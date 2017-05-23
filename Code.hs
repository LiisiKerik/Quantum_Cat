-----------------------------------------------------------------------------------------------------------------------------
module Code where
  import Circuit
  import Data.Bifunctor
  import Data.List
  import Typing
  brackets :: Integer -> String
  brackets(x) = "[" ++ show(x) ++ "]"
  codefile :: (Circuit, Val) -> String
  codefile(Circuit(_)(c)(q)(g), r) =
    intercalate
      (";\n")
      ("include \"qelib1.inc\"" : create_reg('q')("q")(q) ++ cr ++ (encode_gate(name_map) <$> reverse(g))) ++ ";" where
        (cr, name_map) = case r of
          Creg_pointer(x) -> cregs(0)(0)(reverse(c))(x)
          _ -> error("Internal compiler error. Generated a malformed circuit.")
  count_non_empty_regs :: [Integer] -> Integer
  count_non_empty_regs(x) = case x of
    [] -> 0
    h : t -> (if h == 0 then id else (+ 1))(count_non_empty_regs(t))
  create_reg :: Char -> String -> Integer -> [String]
  create_reg(t)(n)(l) = case l of
    0 -> []
    _ -> [t : "reg " ++ n ++ brackets(l)]
  creg_help :: String -> Integer -> Integer -> ([String], [(Integer, String)]) -> ([String], [(Integer, String)])
  creg_help(a)(n)(m)(x) = bimap(create_reg('c')(a)(n) ++)((m, a) :)(x)
  creg_lookup :: [(Integer, String)] -> Integer -> String
  creg_lookup(x)(y) = unsafe_lookup(x)(y)("Internal compiler error. Found an unknown creg when printing circuit.")
  cregs :: Integer -> Integer -> [Integer] -> Integer -> ([String], [(Integer, String)])
  cregs(m)(n)(c)(r) = case c of
    [] -> error("Internal compiler error. Failed to find the result register.")
    h : t ->
      (\(a, x) -> creg_help(a)(h)(m)(x))
        (if m == r then ("r", cregs'(m + 1)(n)(t)) else ('c' : show(n), cregs(m + 1)(n + 1)(t)(r)))
  cregs' :: Integer -> Integer -> [Integer] -> ([String], [(Integer, String)])
  cregs'(m)(n)(c) = case c of
    [] -> ([], [])
    h : t -> creg_help('c' : show(n))(h)(m)(cregs'(m + 1)(n + 1)(t))
  encode_gate :: [(Integer, String)] -> Gate -> String
  encode_gate(c)(g) = case g of
    Cnot_g(x)(y) -> "cx q" ++ brackets(x) ++ ", q" ++ brackets(y)
    Mea_g(x)(y)(z) -> "measure q" ++ brackets(x) ++ " -> " ++ creg_lookup(c)(y) ++ brackets(z)
    Single_g(f)(x) -> f ++ " q" ++ brackets(x)
-----------------------------------------------------------------------------------------------------------------------------