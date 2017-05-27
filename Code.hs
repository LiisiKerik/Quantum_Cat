-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Code where
  import Circuit
  import Data.Bifunctor
  import Data.List
  import Typing
  brackets :: Integer -> String
  brackets x = "[" ++ show x ++ "]"
  codefile :: (Circuit, Val) -> Either String String
  codefile (Circuit _ c q _ g, r) = case r of
    Creg_pointer x -> let
      (cr, name_map) = cregs 0 0 (reverse c) x in
        Right (newl ("include \"qelib1.inc\"" : create_reg 'q' "q" q ++ cr ++ encode_gates 0 name_map (reverse g)) ++ ";")
    _ -> Left "Circuit generation error. Circuit can only be generated for an expression of type Creg{n}."
  cmm :: [String] -> String
  cmm = intercalate ", "
  count_non_empty_regs :: [Integer] -> Integer
  count_non_empty_regs x = case x of
    [] -> 0
    h : t -> (if h == 0 then id else (+ 1)) (count_non_empty_regs t)
  create_reg :: Char -> String -> Integer -> [String]
  create_reg t n l = case l of
    0 -> []
    _ -> [t : "reg " ++ n ++ brackets l]
  creg_help :: String -> Integer -> Integer -> ([String], [(Integer, String)]) -> ([String], [(Integer, String)])
  creg_help a n m x = bimap (create_reg 'c' a n ++) ((m, a) :) x
  creg_lookup :: [(Integer, String)] -> Integer -> String
  creg_lookup x y = unsafe_lookup x y "Internal compiler error. Found an unknown creg when printing circuit."
  cregs :: Integer -> Integer -> [Integer] -> Integer -> ([String], [(Integer, String)])
  cregs m n c r = case c of
    [] -> error ("Internal compiler error. Failed to find the result register.")
    h : t ->
      (\(a, x) -> creg_help a h m x)
        (if m == r then ("r", cregs' (m + 1) n t) else ('c' : show n, cregs (m + 1) (n + 1) t r))
  cregs' :: Integer -> Integer -> [Integer] -> ([String], [(Integer, String)])
  cregs' m n c = case c of
    [] -> ([], [])
    h : t -> creg_help ('c' : show n) h m (cregs' (m + 1) (n + 1) t)
  encode_gate :: Integer -> [(Integer, String)] -> Gate -> (Integer, String)
  encode_gate i c g = case g of
    Cnot_g x y -> (i, "cx q" ++ brackets x ++ ", q" ++ brackets y)
    If_g x y z w a -> let
      f = " f" ++ show i ++ " " in
        (
          i + 1,
            "gate" ++
            f ++
            cmm ((\j -> "a" ++ show j) <$> [0 .. z - 1]) ++
            " {\n  " ++
            intercalate ";\n  " (encode_gate' <$> w) ++
            ";}\nif (" ++
            creg_lookup c x ++
            " == " ++
            show y ++
            f ++
            cmm ((\t -> "q" ++ brackets t) <$> a))
    Mea_g x y z -> (i, "measure q" ++ brackets x ++ " -> " ++ creg_lookup c y ++ brackets z)
    Single_g f x -> (i, f ++ " q" ++ brackets x)
  encode_gates :: Integer -> [(Integer, String)] -> [Gate] -> [String]
  encode_gates i c g = case g of
    [] -> []
    h : t -> let
      (i', s) = encode_gate i c h in
        s : encode_gates i' c t
  encode_gate' :: Gate' -> String
  encode_gate' g = case g of
    Cnot_g' x y -> "cx a" ++ show x ++ ", a" ++ show y
    Single_g' f x -> f ++ " a" ++ show x
  newl :: [String] -> String
  newl = intercalate ";\n"
-----------------------------------------------------------------------------------------------------------------------------