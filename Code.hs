-----------------------------------------------------------------------------------------------------------------------------
module Code where
  import Circuit
  import Data.List
  brackets :: Integer -> String
  brackets(x) = "[" ++ show(x) ++ "]"
  cbits :: Integer-> Integer  -> Integer -> Integer -> [Integer] -> [String]
  cbits(i)(j)(m)(n)(r) = if m == n then [] else case r of
    [] -> ["c" ++ show(k) | k <- [i .. i + n - m - 1]]
    h : t ->
      (\(a, b, i', j') -> (a : brackets(b)) : cbits(i')(j')(m + 1)(n)(t))
        (if m == h then ('r', j, i, j + 1) else ('c', i, i + 1, j))
  code_gate :: [String] -> Gate -> String
  code_gate(c)(g) = case g of
    Cnot_g(x)(y) -> "cx q" ++ brackets(x) ++ ", q" ++ brackets(y)
    Mea_g(x)(y) -> "measure q" ++ brackets(x) ++ " -> " ++ c !! fromInteger(y)
    Single_g(f)(x) -> f ++ " q" ++ brackets(x)
  codefile :: (Circuit, [Integer]) -> String
  codefile(Circuit(c)(q)(g), r) =
    intercalate
      (";\n")
      (
        "include \"qelib1.inc\"" :
        (
          create_reg('q')('q')(q) ++
          create_reg('c')('c')(c - r') ++
          create_reg('c')('r')(r') ++
          (code_gate(cbits(0)(0)(0)(c)(r)) <$> reverse(g)))) ++
            ";" where
              r' = toInteger(length(r))
  create_reg :: Char -> Char -> Integer -> [String]
  create_reg(t)(n)(l) = case l of
    0 -> []
    _ -> [t : "reg " ++ n : brackets(l)]
-----------------------------------------------------------------------------------------------------------------------------