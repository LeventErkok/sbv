{-# OPTIONS_GHC -Wall            #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.SBV
import Control.Exception as E

-- Node indexes, support upto 2^16 entries (no of inputs + no of AND gates)
type Node = SWord16

-- Values that flow through the AND gates
type V = (Node, SBool)  -- A node, possibly complemented if the boolean is true

-- helpers
node, cmp :: Node -> V
node n = (n, false)
cmp  n = (n, true)

-- An AND gate has two inputs going into it
type AND = (V, V)

-- A circuit is a collection of AND gates. The "output" is the result
-- of the final AND gate, possibly complemented if the boolean is true
type Circuit = ([AND], SBool)

-- For instance, here's how we can model a 2 gate XOR using this paradigm
-- nodes 0 and 1 are the inputs; we refer to them as a and b below in comments
-- This looks pretty ugly, but it's quite straightforward..
xorCircuit :: Circuit
xorCircuit = (gs, o)
 where (a, a') = (node 0, cmp 0)  -- the first input and its complement
       (b, b') = (node 1, cmp 1)  -- the second input and its complement
       gs :: [AND]
       gs = [ (a, b')             -- 2: ab'
            , (a', b)             -- 3: a'b
            , (cmp 2, cmp 3)      -- 4: (ab')' (a'b)'
            ]
       o  = true                  -- ((ab')' (a'b)')' = ab' + a'b, which is the XOR of a and b
                                  -- So we complement the result of the last AND gate

-- Check that a given "circuit" is valid. This means that the indices of all And gates must
-- be less than its own output index; thus ensuring there are no cycles
-- The first parameter is the number of inputs to the circuit
validCircuit :: Int -> Circuit -> SBool
validCircuit nInps (ands, _) = bAll valid (zip [fromIntegral nInps ..] ands)
  where valid (n, ((i, _), (j, _))) = i .< literal n &&& j .< literal n

-- "Run" a circuit. We consult the "environment" for storing the values.
-- Invariant: Environment always have a constant size
-- This is important to make sure that the results are always symbolically mergeable
-- NB. There are faster ways of doing this; the current version is a bit of
-- slow due to indexing and all. But the idea remains the same.
run :: [SBool] -> Circuit -> SBool
run inps (ands, oc) = ite oc (bnot res) res
  where env0 = inps ++ replicate (length ands) false
        envF = foldl upd env0 (zip [length inps..] ands)
        res  = last envF
        upd env (n, ((i, ic), (j, jc))) = let (f, _:r) = splitAt n env in f ++ [v] ++ r
           where vi = select env false i
                 vj = select env false j
                 ni = ite ic (bnot vi) vi
                 nj = ite jc (bnot vj) vj
                 v  = ni &&& nj

-- Synthesis

-- A specification is a Haskell function from
-- symbolic boolean inputs to a symbolic boolean outputs
type Spec = [SBool] -> SBool

-- Synthesize a given spec with 'n' inputs
-- This code looks kind of gnarly, and you need to know some of the
-- details of SBV to make full sense of it. In any case, here it goes..
synthesize :: Int -> Spec -> IO ()
synthesize nInps spec = synth 1 -- Start with just a program with one instruction
  where -- synthesize a program of given number of AND gates
        synth gateCount = do
           putStrLn $ "Trying to find a program with " ++ show gateCount ++ " AND gates.."
           SatResult res <- sat $ do
                    -- generate the gates. For each gate, we need two inputs,
                    -- each of which requires two bits to state whether they are complemented
                    circuit <- do cout <- free_  -- bit for complementing the output
                                  cmps  <- mkFreeVars (2*gateCount)  -- complement bits for each input
                                  wires <- mkFreeVars (2*gateCount)  -- inputs to AND gates
                                  return (chop2 (zip wires cmps), cout)
                    -- assert that spec matches the circuit for all inputs
                    let inps = sequence (replicate nInps [false, true])
                    return $ bAll (\i -> validCircuit nInps circuit &&& run i circuit .== spec i) inps
           -- Display the model, if there's one; otherwise loop
           disp gateCount (getModel res) `E.catch` (\(_ :: SomeException) -> synth (gateCount+1))
        chop2 (a:b:r) = (a, b) : chop2 r
        chop2 _       = []
        disp :: Int -> ([Bool], [Word16]) -> IO ()
        disp gc (bs, is)
         | -- Do some sanity checking..We expect 1+2*gc bools, and 2*gc Word16's
           not (length bs == 1 + 2*gc && length is == 2*gc)
         = do putStrLn "Cannot reconstruct circuit from the counter example"
              putStrLn $ "Received: " ++ show (bs, is)
         | True -- good to go
         = do let cout:cbits     = bs
                  gateDescs      = chop2 (zip is cbits)
                  shN (n, nc)    = (if nc then "~" else "") ++ show n
                  shA i (v1, v2) = "    " ++ show i ++ " <- " ++ shN v1 ++ " & " ++ shN v2
              putStrLn $ "  Inputs are 0 through " ++ show (nInps - 1)
              putStrLn $ "  AND gates:"
              mapM_ putStrLn (zipWith shA [nInps ..] gateDescs)
              putStrLn $ "  OUTPUT: "
              putStrLn $ "    " ++ shN (nInps + gc - 1, cout)

-- Tests

-- Generate the xor circuit
testXOR :: IO ()
testXOR = synthesize 2 specXor
  where specXor :: Spec
        specXor [a, b] = ite a (bnot b) b
        specXor _      = error "specXor: needs two elements"

{- Result:
*Main> testXOR 
Trying to find a program with 1 AND gates..
Trying to find a program with 2 AND gates..
Trying to find a program with 3 AND gates..
  Inputs are 0 through 1
  AND gates:
    2 <- ~0 & 1
    3 <- ~1 & 0
    4 <- ~2 & ~3
  OUTPUT: 
    ~4

So, if we read that as a formula, where 0 is a and 1 is b, where a' denotes a complement, we have:

   And gate number 2: a'b
   And gate number 3: b'a
   And gate number 4: (a'b)' (b'a)'
   Output: ((a'b)' (b'a)')'

By De-morgan's rules, the output is: a'b + b'a; which is precisely our xorCircuit definition above! (Modulo
the commutativity of the and gate.)
-}

-- Generate the majority circuit for 3 inputs
testMajority :: IO ()
testMajority = synthesize 3 specMaj
  where specMaj :: Spec
        specMaj [a, b, c] = (a &&& b) <+> (a &&& c) <+> (b &&& c)
        specMaj _         = error "specMac: needs three elements"

{- Result:
Trying to find a program with 1 AND gates..
Trying to find a program with 2 AND gates..
Trying to find a program with 3 AND gates..
Trying to find a program with 4 AND gates..
  Inputs are 0 through 2
  AND gates:
    3 <- ~2 & ~0
    4 <- 2 & 0
    5 <- ~3 & 1
    6 <- ~5 & ~4
  OUTPUT: 
    ~6

Let's see. This is:
     0: a
     1: b
     2: c
     3: c'a'
     4: ca
     5: (c'a')'b
     6: ((c'a')'b)' (ca)'

So the output is:
      (((c'a')'b)' (ca)')'

Simplification gives:

      (((c'a')'b)' (ca)')' = ((c'a')'b) + ca
                           = ((c+a)b) + ca
                           = cb+ab+ca

This is indeed a correct implementation of the majority function; but note that it
differs from our specification in its implementation. The specification used XOR gates
(<+> in SBV notation), but we derived the equivalent version with just OR gates. It's
easy to show that these two functions are indeed equivalent and they both compute the
majority function.
-}
