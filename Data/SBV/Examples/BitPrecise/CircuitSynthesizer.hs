{-# OPTIONS_GHC -Wall            #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.SBV

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

-- A circuit is a collection of AND gates. The "output" is the results
-- of some of those gates, possibly complemented
type Circuit = ([AND], [V])

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
       o  = [(4, true)]           -- ((ab')' (a'b)')' = ab' + a'b, which is the XOR of a and b
                                  -- So we complement the result of the last AND gate

-- Check that a given "circuit" is valid. This means that the indices of all And gates must
-- be less than its own output index; thus ensuring there are no cycles
-- The first parameter is the number of inputs to the circuit
validCircuit :: Int -> Circuit -> SBool
validCircuit nInps (ands, os) = bAll valid (zip [fromIntegral nInps ..] ands) &&& bAll goodOut os
  where total = nInps + length ands
        valid (n, ((i, _), (j, _))) = i .< literal n &&& j .< literal n
        goodOut (n, _) = n .< literal (fromIntegral total)

-- "Run" a circuit. We consult the "environment" for storing the values.
-- Invariant: Environment always have a constant size
-- This is important to make sure that the results are always symbolically mergeable
-- NB. There are faster ways of doing this; the current version is a bit of
-- slow due to indexing and all. But the idea remains the same.
run :: [SBool] -> Circuit -> [SBool]
run inps (ands, outs) = map extract outs
  where env0 = inps ++ replicate (length ands) false
        envF = foldl upd env0 (zip [length inps..] ands)
        extract (v, c) = ite c (bnot res) res
           where res = select envF false v
        upd env (n, ((i, ic), (j, jc))) = let (f, _:r) = splitAt n env in f ++ [v] ++ r
           where vi = select env false i
                 vj = select env false j
                 ni = ite ic (bnot vi) vi
                 nj = ite jc (bnot vj) vj
                 v  = ni &&& nj

-- Synthesis

-- A specification is a Haskell function from
-- symbolic boolean inputs to a symbolic boolean outputs
type Spec = [SBool] -> [SBool]

-- Synthesize a given spec with 'nInps' inputs and 'nOuts' outputs
-- This code looks kind of gnarly, and you need to know some of the
-- details of SBV to make full sense of it. In any case, here it goes..
synthesize :: (Int, Int) -> Spec -> IO ()
synthesize (nInps, nOuts) spec = synth 1 -- Start with just a program with one instruction
  where inps = sequence (replicate nInps [false, true])
        specOuts = map spec inps
        -- synthesize a program of given number of AND gates
        synth gateCount = do
           putStrLn $ "Trying to find a program with " ++ show gateCount ++ " AND gates.."
           res <- sat $ do
                    -- generate the gates. For each gate, we need two inputs,
                    -- each of which requires two bits to state whether they are complemented
                    circuit <- do couts <- mkFreeVars nOuts          -- complement bits each output
                                  cmps  <- mkFreeVars (2*gateCount)  -- complement bits for each input
                                  wires <- mkFreeVars (2*gateCount)  -- inputs to AND gates
                                  outs  <- mkFreeVars nOuts          -- output lines
                                  return (chop2 (zip wires cmps), zip outs couts)
                    -- assert that spec matches the circuit for all inputs
                    return $     validCircuit nInps circuit
                             &&& map (flip run circuit) inps .== specOuts
           -- Display the model, if there's one; otherwise loop
           case getModel res of
             Right c -> disp gateCount c
             Left _  -> synth (gateCount+1)
        chop2 (a:b:r) = (a, b) : chop2 r
        chop2 _       = []
        disp :: Int -> ([Bool], [Word16]) -> IO ()
        disp gc (bs, ios)
         | -- Do some sanity checking.. We expect nOuts+2*gc bools, and Word16's
           any (/= nOuts + 2*gc) [length bs, length ios]
         = do putStrLn "Cannot reconstruct circuit from the counter example"
              putStrLn $ "Received: " ++ show (bs, ios)
         | True -- good to go
         = do let (obits,cbits)  = splitAt nOuts bs
                  (is,os)        = splitAt (2*gc) ios
                  gateDescs      = chop2 (zip is cbits)
                  outDescs       = zip os obits
                  shN (n, nc)    = (if nc then "~" else "") ++ show n
                  shA i (v1, v2) = "    " ++ show i ++ " <- " ++ shN v1 ++ " & " ++ shN v2
              putStrLn $ "  Inputs are 0 through " ++ show (nInps - 1)
              putStrLn $ "  AND gates:"
              mapM_ putStrLn (zipWith shA [nInps ..] gateDescs)
              putStrLn $ "  OUTPUTS: "
              mapM_ (\od -> putStrLn ("    " ++ shN od)) outDescs

-- Tests

-- Generate the xor circuit
testXOR :: IO ()
testXOR = synthesize (2,1) specXor
  where specXor :: Spec
        specXor [a, b] = [ite a (bnot b) b]
        specXor _      = error "specXor: needs two elements"

{- Result:
*Main> testXOR 
Trying to find a program with 1 AND gates..
Trying to find a program with 2 AND gates..
Trying to find a program with 3 AND gates..
  Inputs are 0 through 1
  AND gates:
    2 <- ~1 & 0
    3 <- ~0 & 1
    4 <- ~2 & ~3
  OUTPUT: 
    ~4

So, if we read that as a formula, where 0 is a and 1 is b, where a' denotes a complement, we have:

   And gate number 2: b'a
   And gate number 3: a'b
   And gate number 4: (b'a)'(a'b)'
   Output: ((b'a)'(a'b)')'

By De-morgan's rules, the output is: b'a+a'b; which is indeed a correct definition for xor
-}

-- Generate the majority circuit for 3 inputs
testMajority :: IO ()
testMajority = synthesize (3,1) specMaj
  where specMaj :: Spec
        specMaj [a, b, c] = [(a &&& b) <+> (a &&& c) <+> (b &&& c)]
        specMaj _         = error "specMac: needs three elements"

{- Result:
Trying to find a program with 1 AND gates..
Trying to find a program with 2 AND gates..
Trying to find a program with 3 AND gates..
Trying to find a program with 4 AND gates..
  Inputs are 0 through 2
  AND gates:
    3 <- 0 & 1
    4 <- ~2 & ~3
    5 <- ~1 & ~0
    6 <- ~5 & ~4
  OUTPUT: 
    6

Let's see. This is:
     0: a
     1: b
     2: c
     3: ab
     4: c'(ab)'
     5: b'a'
     6: (b'a')'(c'(ab)')'

Simplification gives:

     (b'a')'(c'(ab)')' = (b+a)(c+ab)
                       = bc+bab+ac+aab
                       = bc+ab+ac+ab
                       = bc+ab+ac

This is indeed a correct implementation of the majority function.
-}

-- Generate a 2-bit adder; we ignore the carry-out
testAdder :: IO ()
testAdder = synthesize (4,2) specAdd
  where specAdd :: Spec
        specAdd [a0, a1, b0, b1] = blast (mkNum [a0, a1] + mkNum [b0, b1])
        specAdd _ = error "specAdd needs 4 elements"
        -- assume big-endian
        mkNum :: [SBool] -> SWord8
        mkNum = foldl add 0
          where add s b = 2*s + ite b 1 0
        blast = take 2 . blastLE
