-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
module Code where
  import Circuit
  import Data.Bifunctor
  import Data.List
  import Optimise
  import Typing
  brack :: String -> Integer -> String
  brack x y = x ++ brackets y
  brack_q :: Integer -> String
  brack_q = brack "q"
  brackets :: Integer -> String
  brackets x = "[" ++ show x ++ "]"
  codefile :: (Circuit, Integer) -> String
  codefile (Circuit _ c q _ g, x) =
    let
      (cr, name_map) = cregs 0 0 (reverse c) x
    in
      newl ("include \"qelib1.inc\"" : create_reg "q" "q" q ++ cr ++ encode_gates 0 name_map (reverse g)) ++ ";"
  cmm :: [String] -> String
  cmm = intercalate ", "
  count_non_empty_regs :: [Integer] -> Integer
  count_non_empty_regs x = case x of
    [] -> 0
    h : t -> (if h == 0 then id else (+ 1)) (count_non_empty_regs t)
  create_reg :: String -> String -> Integer -> [String]
  create_reg t n l = case l of
    0 -> []
    _ -> [t ++ "reg " ++ brack n l]
  creg_help :: String -> Integer -> Integer -> ([String], [(Integer, String)]) -> ([String], [(Integer, String)])
  creg_help a n m = bimap (create_reg "c" a n ++) ((m, a) :)
  cregs :: Integer -> Integer -> [Integer] -> Integer -> ([String], [(Integer, String)])
  cregs m n c r = case c of
    [] -> ice
    h : t ->
      (\(a, x) -> creg_help a h m x)
        (if m == r then ("r", cregs' (m + 1) n t) else (rgmnt_c n, cregs (m + 1) (n + 1) t r))
  cregs' :: Integer -> Integer -> [Integer] -> ([String], [(Integer, String)])
  cregs' m n c = case c of
    [] -> ([], [])
    h : t -> creg_help (rgmnt_c n) h m (cregs' (m + 1) (n + 1) t)
  encode_gate :: Integer -> [(Integer, String)] -> Gate -> (Integer, String)
  encode_gate i c g = case g of
    Unitary g' -> (i, encode_gate' brack_q g')
    If_g x y z w a -> let
      f = " " ++ rgmnt "f" i ++ " " in
        (
          i + 1,
            "gate" ++
            f ++
            cmm ((\j -> rgmnt_a j) <$> [0 .. z - 1]) ++
            " {\n  " ++
            intercalate ";\n  " (encode_gate' rgmnt_a <$> w) ++
            ";}\nif (" ++
            lookup' x c ++
            " == " ++
            show y ++
            f ++
            cmm (brack_q <$> a))
    Mea_g x y z -> (i, "measure " ++ brack_q x ++ " -> " ++ lookup' y c ++ brackets z)
  encode_gates :: Integer -> [(Integer, String)] -> [Gate] -> [String]
  encode_gates i c g = case g of
    [] -> []
    h : t -> let
      (i', s) = encode_gate i c h in
        s : encode_gates i' c t
  encode_gate' :: (Integer -> String) -> Gate' -> String
  encode_gate' a g =
    let
      print_gate (x, y) = x ++ " " ++ cmm (a <$> y)
    in
      print_gate (case g of
        Double_gate f x y -> (f, [x, y])
        Single_gate f x -> (f, [x])
        CCX_gate x y z -> ("ccx", [x, y, z]))
  newl :: [String] -> String
  newl = intercalate ";\n"
  rgmnt :: String -> Integer -> String
  rgmnt x y = x ++ show y
  rgmnt_a :: Integer -> String
  rgmnt_a = rgmnt "a"
  rgmnt_c :: Integer -> String
  rgmnt_c = rgmnt "c"
-----------------------------------------------------------------------------------------------------------------------------