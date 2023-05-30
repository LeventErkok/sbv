-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.BitPrecise.Legato
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- An encoding and correctness proof of Legato's multiplier in Haskell. Bill Legato came
-- up with an interesting way to multiply two 8-bit numbers on Mostek, as described here:
--   <http://www.cs.utexas.edu/~moore/acl2/workshop-2004/contrib/legato/Weakest-Preconditions-Report.pdf>
--
-- Here's Legato's algorithm, as coded in Mostek assembly:
--
-- @
--    step1 :       LDX #8         ; load X immediate with the integer 8
--    step2 :       LDA #0         ; load A immediate with the integer 0
--    step3 : LOOP  ROR F1         ; rotate F1 right circular through C
--    step4 :       BCC ZCOEF      ; branch to ZCOEF if C = 0
--    step5 :       CLC            ; set C to 0
--    step6 :       ADC F2         ; set A to A+F2+C and C to the carry
--    step7 : ZCOEF ROR A          ; rotate A right circular through C
--    step8 :       ROR LOW        ; rotate LOW right circular through C
--    step9 :       DEX            ; set X to X-1
--    step10:       BNE LOOP       ; branch to LOOP if Z = 0
-- @
--
-- This program came to be known as the Legato's challenge in the community, where
-- the challenge was to prove that it indeed does perform multiplication. This file
-- formalizes the Mostek architecture in Haskell and proves that Legato's algorithm
-- is indeed correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.BitPrecise.Legato where

import Data.Array (Array, Ix(..), (!), (//), array)

import Data.SBV
import Data.SBV.Tools.CodeGen

import GHC.Generics (Generic)

------------------------------------------------------------------
-- * Mostek architecture
------------------------------------------------------------------

-- | We model only two registers of Mostek that is used in the above algorithm, can add more.
data Register = RegX  | RegA  deriving (Eq, Ord, Ix, Bounded)

-- | The carry flag ('FlagC') and the zero flag ('FlagZ')
data Flag = FlagC | FlagZ deriving (Eq, Ord, Ix, Bounded)

-- | Mostek was an 8-bit machine.
type Value = SWord 8

-- | Convenient synonym for symbolic machine bits.
type Bit = SBool

-- | Register bank
type Registers = Array Register Value

-- | Flag bank
type Flags = Array Flag Bit

-- | We have three memory locations, sufficient to model our problem
data Location = F1   -- ^ multiplicand
              | F2   -- ^ multiplier
              | LO   -- ^ low byte of the result gets stored here
              deriving (Eq, Ord, Ix, Bounded)

-- | Memory is simply an array from locations to values
type Memory = Array Location Value

-- | Abstraction of the machine: The CPU consists of memory, registers, and flags.
-- Unlike traditional hardware, we assume the program is stored in some other memory area that
-- we need not model. (No self modifying programs!)
--
-- 'Mostek' is equipped with an automatically derived 'Mergeable' instance
-- because each field is 'Mergeable'.
data Mostek = Mostek { memory    :: Memory
                     , registers :: Registers
                     , flags     :: Flags
                     } deriving (Generic, Mergeable)

-- | Given a machine state, compute a value out of it
type Extract a = Mostek -> a

-- | Programs are essentially state transformers (on the machine state)
type Program = Mostek -> Mostek

------------------------------------------------------------------
-- * Low-level operations
------------------------------------------------------------------

-- | Get the value of a given register
getReg :: Register -> Extract Value
getReg r m = registers m ! r

-- | Set the value of a given register
setReg :: Register -> Value -> Program
setReg r v m = m {registers = registers m // [(r, v)]}

-- | Get the value of a flag
getFlag :: Flag -> Extract Bit
getFlag f m = flags m ! f

-- | Set the value of a flag
setFlag :: Flag -> Bit -> Program
setFlag f b m = m {flags = flags m // [(f, b)]}

-- | Read memory
peek :: Location -> Extract Value
peek a m = memory m ! a

-- | Write to memory
poke :: Location -> Value -> Program
poke a v m = m {memory = memory m // [(a, v)]}

-- | Checking overflow. In Legato's multiplier the @ADC@ instruction
-- needs to see if the expression x + y + c overflowed, as checked
-- by this function. Note that we verify the correctness of this check
-- separately below in `checkOverflowCorrect`.
checkOverflow :: SWord 8 -> SWord 8 -> SBool -> SBool
checkOverflow x y c = s .< x .|| s .< y .|| s' .< s
  where s  = x + y
        s' = s + ite c 1 0

-- | Correctness theorem for our `checkOverflow` implementation.
--
--   We have:
--
--   >>> checkOverflowCorrect
--   Q.E.D.
checkOverflowCorrect :: IO ThmResult
checkOverflowCorrect = checkOverflow === overflow
  where -- Reference spec for overflow. We do the addition
        -- using 16 bits and check that it's larger than 255
        overflow :: SWord 8 -> SWord 8 -> SBool -> SBool
        overflow x y c = (0 # x) + (0 # y) + ite c 1 0 .> (255 :: SWord 16)
------------------------------------------------------------------
-- * Instruction set
------------------------------------------------------------------

-- | An instruction is modeled as a 'Program' transformer. We model
-- mostek programs in direct continuation passing style.
type Instruction = Program -> Program

-- | LDX: Set register @X@ to value @v@
ldx :: Value -> Instruction
ldx v k = k . setReg RegX v

-- | LDA: Set register @A@ to value @v@
lda :: Value -> Instruction
lda v k = k . setReg RegA v

-- | CLC: Clear the carry flag
clc :: Instruction
clc k = k . setFlag FlagC sFalse

-- | ROR, memory version: Rotate the value at memory location @a@
-- to the right by 1 bit, using the carry flag as a transfer position.
-- That is, the final bit of the memory location becomes the new carry
-- and the carry moves over to the first bit. This very instruction
-- is one of the reasons why Legato's multiplier is quite hard to understand
-- and is typically presented as a verification challenge.
rorM :: Location -> Instruction
rorM a k m = k . setFlag FlagC c' . poke a v' $ m
  where v  = peek a m
        c  = getFlag FlagC m
        v' = setBitTo (v `rotateR` 1) 7 c
        c' = sTestBit v 0

-- | ROR, register version: Same as 'rorM', except through register @r@.
rorR :: Register -> Instruction
rorR r k m = k . setFlag FlagC c' . setReg r v' $ m
  where v  = getReg r m
        c  = getFlag FlagC m
        v' = setBitTo (v `rotateR` 1) 7 c
        c' = sTestBit v 0

-- | BCC: branch to label @l@ if the carry flag is sFalse
bcc :: Program -> Instruction
bcc l k m = ite (c .== sFalse) (l m) (k m)
  where c = getFlag FlagC m

-- | ADC: Increment the value of register @A@ by the value of memory contents
-- at location @a@, using the carry-bit as the carry-in for the addition.
adc :: Location -> Instruction
adc a k m = k . setFlag FlagZ (v' .== 0) . setFlag FlagC c' . setReg RegA v' $ m
  where v  = peek a m
        ra = getReg RegA m
        c  = getFlag FlagC m
        v' = v + ra + ite c 1 0
        c' = checkOverflow v ra c

-- | DEX: Decrement the value of register @X@
dex :: Instruction
dex k m = k . setFlag FlagZ (x .== 0) . setReg RegX x $ m
  where x = getReg RegX m - 1

-- | BNE: Branch if the zero-flag is sFalse
bne :: Program -> Instruction
bne l k m = ite (z .== sFalse) (l m) (k m)
  where z = getFlag FlagZ m

-- | The 'end' combinator "stops" our program, providing the final continuation
-- that does nothing.
end :: Program
end = id

------------------------------------------------------------------
-- * Legato's algorithm in Haskell/SBV
------------------------------------------------------------------

-- | Multiplies the contents of @F1@ and @F2@, storing the low byte of the result
-- in @LO@ and the high byte of it in register @A@. The implementation is a direct
-- transliteration of Legato's algorithm given at the top, using our notation.
legato :: Program
legato = start
  where start   =    ldx 8
                   $ lda 0
                   $ loop
        loop    =    rorM F1
                   $ bcc zeroCoef
                   $ clc
                   $ adc F2
                   $ zeroCoef
        zeroCoef =   rorR RegA
                   $ rorM LO
                   $ dex
                   $ bne loop
                   $ end

------------------------------------------------------------------
-- * Verification interface
------------------------------------------------------------------
-- | Given values for  F1 and F2, @runLegato@ takes an arbitrary machine state @m@ and
-- returns the high and low bytes of the multiplication.
runLegato :: Mostek -> (Value, Value)
runLegato m = (getReg RegA m', peek LO m')
  where m' = legato m

-- | Helper synonym for capturing relevant bits of Mostek
type InitVals = ( Value      -- Contents of mem location F1
                , Value      -- Contents of mem location F2
                , Value      -- Contents of mem location LO
                , Value      -- Content of Register X
                , Value      -- Content of Register A
                , Bit        -- Value of FlagC
                , Bit        -- Value of FlagZ
                )

-- | Create an instance of the Mostek machine, initialized by the memory and the relevant
-- values of the registers and the flags
initMachine :: InitVals -> Mostek
initMachine (f1, f2, lo, rx, ra, fc, fz) = Mostek { memory    = array (minBound, maxBound) [(F1, f1), (F2, f2), (LO, lo)]
                                                  , registers = array (minBound, maxBound) [(RegX, rx),  (RegA, ra)]
                                                  , flags     = array (minBound, maxBound) [(FlagC, fc), (FlagZ, fz)]
                                                  }

-- | The correctness theorem. For all possible memory configurations, the factors (@x@ and @y@ below), the location
-- of the low-byte result and the initial-values of registers and the flags, this function will return True only if
-- running Legato's algorithm does indeed compute the product of @x@ and @y@ correctly.
legatoIsCorrect :: InitVals -> SBool
legatoIsCorrect initVals@(x, y, _, _, _, _, _) = result .== expected
    where (hi, lo) = runLegato (initMachine initVals)
          -- NB. perform the comparison over 16 bit values to avoid overflow!
          -- If Value changes to be something else, modify this accordingly.
          result, expected :: SWord 16
          result   = 256 * (0 # hi) + (0 # lo)
          expected = (0 # x) * (0 # y)

------------------------------------------------------------------
-- * Verification
------------------------------------------------------------------

-- | The correctness theorem.
correctnessTheorem :: IO ThmResult
correctnessTheorem = proveWith defaultSMTCfg{timing = PrintTiming} $ do
        lo <- sWord "lo"

        x <- sWord  "x"
        y <- sWord  "y"

        regX  <- sWord "regX"
        regA  <- sWord "regA"

        flagC <- sBool "flagC"
        flagZ <- sBool "flagZ"

        return $ legatoIsCorrect (x, y, lo, regX, regA, flagC, flagZ)

------------------------------------------------------------------
-- * C Code generation
------------------------------------------------------------------

-- | Generate a C program that implements Legato's algorithm automatically.
legatoInC :: IO ()
legatoInC = compileToC Nothing "runLegato" $ do
                x <- cgInput "x"
                y <- cgInput "y"
                let (hi, lo) = runLegato (initMachine (x, y, 0, 0, 0, sFalse, sFalse))
                cgOutput "hi" hi
                cgOutput "lo" lo

{- HLint ignore legato "Redundant $"        -}
{- HLint ignore module "Reduce duplication" -}
