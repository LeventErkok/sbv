-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.AOC_2021_24
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A solution to the advent-of-code problem, 2021, day 24: <http://adventofcode.com/2021/day/24>.
--
-- Here is a high-level summary: We are essentially modeling the ALU of a fictional
-- computer with 4 integer registers (w, x, y, z), and 6 instructions (inp, add, mul, div, mod, eql).
-- You are given a program (hilariously called "monad"), and your goal is to figure out what
-- the maximum and minimum inputs you can provide to this program such that when it runs
-- register z ends up with the value 1. Please refer to the above link for the full description.
--
-- While there are multiple ways to solve this problem in SBV, the solution here demonstrates
-- how to turn programs in this fictional language into actual Haskell/SBV programs, i.e.,
-- developing a little EDSL (embedded domain-specific language) for it. Hopefully this
-- should provide a template for other similar programs.
-----------------------------------------------------------------------------

{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE NegativeLiterals #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.AOC_2021_24 where

import Prelude hiding (read, mod, div)

import Control.Monad (forM_)
import Data.Maybe

import qualified Data.Map.Strict          as M
import qualified Control.Monad.State.Lazy as ST

import Data.SBV

-----------------------------------------------------------------------------------------------
-- * Registers, values, and the ALU
-----------------------------------------------------------------------------------------------

-- | A Register in the machine, identified by its name.
type Register = String

-- | We operate on 64-bit signed integers. It is also possible to use the unbounded integers here
-- as the problem description doesn't mention any size limitations. But performance isn't as good
-- with unbounded integers, and 64-bit signed bit-vectors seem to fit the bill just fine, much
-- like any other modern processor these days.
type Value = SInt64

-- | An item of data to be processed. We can either be referring to a named register, or an immediate value.
data Data = Reg {register :: Register}
          | Imm Int64

-- | 'Num' instance for 'Data'. This is merely there for us to be able to represent programs in a
-- natural way, i.e, lifting integers (positive and negative). Other methods are neither implemented
-- nor needed.
instance Num Data where
  fromInteger    = Imm . fromIntegral
  (+)            = error "+     : unimplemented"
  (*)            = error "*     : unimplemented"
  negate (Imm i) = Imm (-i)
  negate Reg{}   = error "negate: unimplemented"
  abs            = error "abs   : unimplemented"
  signum         = error "signum: unimplemented"

-- | Shorthand for the @w@ register.
w :: Data
w = Reg "w"

-- | Shorthand for the @x@ register.
x :: Data
x = Reg "x"

-- | Shorthand for the @y@ register.
y :: Data
y = Reg "y"

-- | Shorthand for the @z@ register.
z :: Data
z = Reg "z"

-- | The state of the machine. We keep track of the data values, along with the input parameters.
data State = State { env    :: M.Map Register Value  -- ^ Values of registers
                   , inputs :: [Value]               -- ^ Input parameters, stored in reverse.
                   }

-- | The ALU is simply a state transformer, manipulating the state, wrapped around SBV's 'Symbolic' monad.
type ALU = ST.StateT State Symbolic

-----------------------------------------------------------------------------------------------
-- * Operations
-----------------------------------------------------------------------------------------------

-- | Reading a value. For a register, we simply look it up in the environment.
-- For an immediate, we simply return it.
read :: Data -> ALU Value
read (Reg r) = ST.get >>= \st -> pure $ fromJust (r `M.lookup` env st)
read (Imm i) = pure $ literal i

-- | Writing a value. We update the registers.
write :: Data -> Value -> ALU ()
write d v = ST.modify' $ \st -> st{env = M.insert (register d) v (env st)}

-- | Reading an input value. In this version, we simply write a free symbolic value
-- to the specified register, and keep track of the inputs explicitly.
inp :: Data -> ALU ()
inp a = do v <- ST.lift free_
           write a v
           ST.modify' $ \st -> st{inputs = v : inputs st}

-- | Addition.
add :: Data -> Data -> ALU ()
add a b = write a =<< (+) <$> read a <*> read b

-- | Multiplication.
mul :: Data -> Data -> ALU ()
mul a b = write a =<< (*) <$> read a <*> read b

-- | Division.
div :: Data -> Data -> ALU ()
div a b = write a =<< sDiv <$> read a <*> read b

-- | Modulus.
mod :: Data -> Data -> ALU ()
mod a b = write a =<< sMod <$> read a <*> read b

-- | Equality.
eql :: Data -> Data -> ALU ()
eql a b = write a . oneIf =<< (.==) <$> read a <*> read b

-----------------------------------------------------------------------------------------------
-- * Running a program
-----------------------------------------------------------------------------------------------

-- | Run a given program, returning the final state. We simply start with the initial
-- environment mapping all registers to zero, as specified in the problem specification.
run :: ALU () -> Symbolic State
run pgm = ST.execStateT pgm initState
 where initState = State { env    = M.fromList [(register r, 0) | r <- [w, x, y, z]]
                         , inputs = []
                         }

-----------------------------------------------------------------------------------------------
-- * Solving the puzzle
--
-----------------------------------------------------------------------------------------------

-- | We simply run the 'monad' program, and specify the constraints at the end. We take a boolean
-- as a parameter, choosing whether we want to minimize or maximize the model-number. Note that this
-- test takes rather long to run. We get:
--
-- @
-- ghci> puzzle True
-- Optimal model:
--   Maximum model number = 96918996924991 :: Int64
-- ghci> puzzle False
-- Optimal model:
--   Minimum model number = 91811241911641 :: Int64
-- @
puzzle :: Bool -> IO ()
puzzle shouldMaximize = print =<< optimizeWith z3{isNonModelVar = (/= finalVar)}  Lexicographic problem
  where finalVar | shouldMaximize = "Maximum model number"
                 | True           = "Minimum model number"
        problem = do State{env, inputs} <- run monad

                     -- The final z value should be 0
                     constrain $ fromJust (register z `M.lookup` env) .== 0

                     -- Digits of the model number, stored in reverse
                     let digits = reverse inputs

                     -- Each digit is between 1-9
                     forM_ digits $ \d -> constrain $ d `inRange` (1, 9)

                     -- Digits spell out the model number. We minimize/maximize this value as requested:
                     let modelNum = foldl (\sofar d -> 10 * sofar + d) 0 digits

                     -- maximize/minimize the digits as requested
                     if shouldMaximize
                        then maximize "goal" modelNum
                        else minimize "goal" modelNum

                     -- For display purposes, create a variable to assign to modelNum
                     modelNumV <- free finalVar
                     constrain $ modelNumV .== modelNum

-- | The program we need to crack. Note that different users get different programs on the Advent-Of-Code site, so this is simply one example.
-- You can simply cut-and-paste your version instead. (Don't forget the pragma @NegativeLiterals@ to GHC so @add x -1@ parses correctly as @add x (-1)@.)
monad :: ALU ()
monad = do inp w
           mul x 0
           add x z
           mod x 26
           div z 1
           add x 11
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 5
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 1
           add x 13
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 5
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 1
           add x 12
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 1
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 1
           add x 15
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 15
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 1
           add x 10
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 2
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 26
           add x -1
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 2
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 1
           add x 14
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 5
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 26
           add x -8
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 8
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 26
           add x -7
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 14
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 26
           add x -8
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 12
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 1
           add x 11
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 7
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 26
           add x -2
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 14
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 26
           add x -2
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 13
           mul y x
           add z y
           inp w
           mul x 0
           add x z
           mod x 26
           div z 26
           add x -13
           eql x w
           eql x 0
           mul y 0
           add y 25
           mul y x
           add y 1
           mul z y
           mul y 0
           add y w
           add y 6
           mul y x
           add z y

{- HLint ignore module "Reduce duplication" -}
