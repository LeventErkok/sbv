{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

module Data.SBV.Examples.BitPrecise.Legato where

{- An encoding and correctness proof of Legato's multiplier in Haskell
   Inspired by the Cryptol version. Note that the Haskell version is
   a deep(-er) embedding of the interpreter

   For details: 
     http://www.cs.utexas.edu/~moore/acl2/workshop-2004/contrib/legato/Weakest-Preconditions-Report.pdf
-}

{- Here's Legato's algorithm, as coded in Mostek assembly

 step1 :       LDX #8         ; load X immediate with the integer 8 
 step2 :       LDA #0         ; load A immediate with the integer 0 
 step3 :       CLC            ; set C to 0
 step4 : LOOP  ROR F1         ; rotate F1 right circular through C 
 step5 :       BCC ZCOEF      ; branch to ZCOEF if C = 0 
 step6 :       CLC            ; set C to 0 
 step7 :       ADC F2         ; set A to A+F2+C and C to the carry 
 step8 : ZCOEF ROR A          ; rotate A right circular through C 
 step9 :       ROR LOW        ; rotate LOW right circular through C 
 step10:       DEX            ; set X to X-1 
 step11:       BNE LOOP       ; branch to LOOP if Z = 0 

Note that apparently the CLC in step3 was later added by Warren Hunt; the
original spec did not include this statement. However, without this
addition, the algorithm does not work correctly for all starting states,
so we adopt this change as well.
-}

import Data.Array
import Data.SBV

type Address  = SWord32
data Register = RegX  | RegA  deriving (Eq, Ord, Ix, Bounded, Enum)
data Flag     = FlagC | FlagZ deriving (Eq, Ord, Ix, Bounded, Enum)

type Value     = SWord8
type Bit       = SBool

type Registers = Array Register Value
type Flags     = Array Flag     Bit

type Memory = Model Word32 Word8        -- Model defined later

data Mostek = Mostek { memory    :: Memory
                     , registers :: Registers
                     , flags     :: Flags
                     }

type Extract a = Mostek -> a
type Program = Extract Mostek

instance Mergeable Mostek where
  symbolicMerge b m1 m2 = Mostek { memory    = symbolicMerge b (memory m1)    (memory m2)
                                 , registers = symbolicMerge b (registers m1) (registers m2)
                                 , flags     = symbolicMerge b (flags m1)     (flags m2)
                                 }

-- Low-level operations
getReg :: Register -> Extract Value
getReg r m = registers m ! r

setReg :: Register -> Value -> Program
setReg r v m = m {registers = registers m // [(r, v)]}

getFlag :: Flag -> Extract Bit
getFlag f m = flags m ! f

setFlag :: Flag -> Bit -> Program
setFlag f b m = m {flags = flags m // [(f, b)]}

peek :: Address -> Extract Value
peek a m = readArray (memory m) a

poke :: Address -> Value -> Program
poke a v m = m {memory = writeArray (memory m) a v}

-- Programmer instructions
type Instruction = Program -> Program

ldx :: Value -> Instruction
ldx v k = k . setReg RegX v

lda :: Value -> Instruction
lda v k = k . setReg RegA v

clc :: Instruction
clc k = k . setFlag FlagC false

rorM :: Address -> Instruction
rorM a k m = k . setFlag FlagC c' . poke a v' $ m
  where v  = peek a m
        c  = getFlag FlagC m
        v' = setBitTo (v `rotateR` 1) 7 c
        c' = bitValue v 0

rorR :: Register -> Instruction
rorR r k m = k . setFlag FlagC c' . setReg r v' $ m
  where v  = getReg r m
        c  = getFlag FlagC m
        v' = setBitTo (v `rotateR` 1) 7 c
        c' = bitValue v 0

bcc :: Program -> Instruction
bcc l k m = ite (c .== false) (l m) (k m)
  where c = getFlag FlagC m

adc :: Address -> Instruction
adc a k m = k . setFlag FlagZ (v' .== 0) . setFlag FlagC c' . setReg RegA v' $ m
  where v  = peek a m
        ra = getReg RegA m
        c  = getFlag FlagC m
        v' = v + ra + ite (c .== true) 1 0
        c' = bitValue v' 7 -- c is true if the sum overflowed

dex :: Instruction
dex k m = k . setFlag FlagZ (x .== 0) . setReg RegX x $ m
  where x = getReg RegX m - 1

bne :: Program -> Instruction
bne l k m = ite (z .== false) (l m) (k m)
  where z = getFlag FlagZ m

end :: Program
end = id

legato :: Address -> Address -> Address -> Program
legato f1Addr f2Addr lowAddr = start
  where start   =    ldx 8
                   $ lda 0
                   $ clc
                   $ loop
        loop    =    rorM f1Addr
                   $ bcc zeroCoef
                   $ clc
                   $ adc f2Addr
                   $ zeroCoef
        zeroCoef =   rorR RegA
                   $ rorM lowAddr
                   $ dex
                   $ bne loop
                   $ end

runLegato :: (Address, Value) -> (Address, Value) -> Address -> Mostek -> (Value, Value)
runLegato (f1Addr, f1Val) (f2Addr, f2Val) loAddr m = (getReg RegA mFinal, peek loAddr mFinal)
  where m0     = poke f1Addr f1Val $ poke f2Addr f2Val m
        mFinal = legato f1Addr f2Addr loAddr m0

type InitVals = ( Value      -- Content of Register X
                , Value      -- Content of Register A
                , Value      -- Initial contents of memory
                , Bit        -- Value of FlagC
                , Bit        -- Value of FlagZ
                )

initMachine :: Memory -> InitVals -> Mostek
initMachine mem (rx, ra, mc, fc, fz) = Mostek { memory    = resetArray mem mc
                                              , registers = array (minBound, maxBound) [(RegX, rx),  (RegA, ra)]
                                              , flags     = array (minBound, maxBound) [(FlagC, fc), (FlagZ, fz)]
                                              }

legatoIsCorrect :: Memory -> (Address, Value) -> (Address, Value) -> Address -> InitVals -> SBool
legatoIsCorrect mem (addrX, x) (addrY, y) addrLow initVals = allDifferent [addrX, addrY, addrLow] ==> x * y .== 256 * hi + lo
    where (hi, lo) = runLegato (addrX, x) (addrY, y) addrLow (initMachine mem initVals)

-- type Model = SArray
type Model = SFunArray

-- To prove this, Yices takes:
--   About 45 seconds with SFunArray memory model
--   About 30 minutes with SArray memory model
correctnessTheorem :: IO ThmResult
correctnessTheorem = proveWith timingSMTCfg legatoIsCorrect

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "legato" ~: legatoPgm `goldCheck` "legato.gold"
 ]
 where legatoPgm = runSymbolic $ forAll ["mem", "addrX", "x", "addrY", "y", "addrLow", "regX", "regA", "memVals", "flagC", "flagZ"] legatoIsCorrect
