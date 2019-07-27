import Data.List

gen :: Int -> String
gen n = unlines $ to ++ from

  where exts i
          | i < 0 = []
          | True  = ("bvExtract (Proxy " ++ sh i ++ ") (Proxy " ++ sh (i-7) ++ ") a") : exts (i-8)
        l = 1 + length (show n)
        sh i = reverse $ take l $ (reverse ("@" ++ show i) ++ repeat ' ')

        n2 = show $ n `div` 2
        req = n `div` 8
        half = show $ req `div` 2

        by4 xs | length xs < 4 = xs
               | True          = intercalate ", " (take 4 xs) : by4 (drop 4 xs)

        to
         | n == 8
         = [ "-- | 'SWord' " ++ show n ++ " instance for 'ByteConverter'"
           , "instance ByteConverter (SWord " ++ show n ++ ") where"
           , "   toBytes a = [a]"
           , ""
           ]
         | True
         = [ "-- | 'SWord' " ++ show n ++ " instance for 'ByteConverter'"
           , "instance ByteConverter (SWord " ++ show n ++ ") where"
           , "   toBytes a = [ " ++ intercalate "\n               , " (by4 (exts (n-1))) ++ "\n               ]"
           , ""
           ]

        from
         | n == 8
         = [ "   fromBytes [x] = x"
           , "   fromBytes as  = error $ \"fromBytes:SWord " ++ show n ++ ": Incorrect number of bytes: \" ++ show (length as)"
           ]
         | True
         = [ "   fromBytes as"
           , "     | l == " ++ show req
           , "     = (fromBytes :: [SWord 8] -> SWord " ++ n2 ++ ") (take " ++ half ++ " as) # fromBytes (drop " ++ half ++ " as)"
           , "     | True"
           , "     = error $ \"fromBytes:SWord " ++ show n ++ ": Incorrect number of bytes: \" ++ show l"
           , "     where l = length as"
           ]

generate :: IO ()
generate = writeFile "generated.hs" $ intercalate "\n" $ map gen insts
  where insts = [8, 16, 32, 64, 128, 256, 512, 1024]
