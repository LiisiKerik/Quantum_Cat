-----------------------------------------------------------------------------------------------------------------------------
module Quantum_Cat' where
  import Circuit
  import Code
  import Optimise
  import Standard
  import Tokenise
  import Tree
  import Typing
  check_file :: String -> Maybe(String)
  check_file(x) = case tokenise(x) of
    Left((l, c), e) -> Just("Tokenisation error" ++ location'(l)(c) ++ "." ++ e)
    Right(y) -> case tree(y) of
      Left(l, c) -> Just("Parse error" ++ location'(l)(c) ++ ".")
      Right(z) -> case typing(init_res)(types)(init_bind)(init_defs)(standard(z)) of
        Left(e) -> Just(e)
        Right(_) -> Nothing
  quantum_Cat :: String -> String -> Either(String)(String)
  quantum_Cat(x)(inp) = case tokenise(x) of
    Left((l, c), e) -> Left("Tokenisation error in library" ++ location'(l)(c) ++ "." ++ e)
    Right(y) -> case tree(y) of
      Left(l, c) -> Left("Parse error in library" ++ location'(l)(c) ++ ".")
      Right(z) -> typing(init_res)(types)(init_bind)(init_defs)(standard(z)) >>= \(r, con, b, w) -> case tokenise(inp) of
        Left((l, c), e) -> Left("Tokenisation error in input" ++ location'(l)(c) ++ "." ++ e)
        Right(inp2) -> case expr_tree(inp2) of
          Left(l, c) -> Left("Parse error in input" ++ location'(l)(c) ++ ".")
          Right(inp3) ->
            type_expr(r)(con)(b)(standard_expr(inp3)) >>= \inp4 -> circuit(w)(inp4) >>= Right <$> codefile <$> cleanup
-----------------------------------------------------------------------------------------------------------------------------