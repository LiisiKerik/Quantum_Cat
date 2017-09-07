-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
module Circuit where
  import Data.Bifunctor
  import Data.Map
  import Naming
  import Tokenise
  import Tree
  import Typing
  data Circuit = Circuit Integer [Integer] Integer Integer [Gate] deriving Show
  data Gate = G' Gate' | If_g Integer Integer Integer [Gate'] [Integer] | Mea_g Integer Integer Integer deriving Show
  data Gate' = Double_g String Integer Integer | Single_g String Integer | Toffoli_g Integer Integer Integer
    deriving Show
  data Expression_3 =
    Add_Finite_expression_3 Integer |
    Add_Finite_expression'_3 Integer Integer |
    Add_Int_expression_3 |
    Add_Int_expression'_3 Integer |
    Algebraic_expression_3 String [Expression_3] |
    Convert_Finite_expression_3 Integer |
    Crash_expression_3 |
    Creg_expression_3 Integer |
    Equal_Finite_expression_3 |
    Equal_Finite_expression'_3 Integer |
    Equal_Int_expression_3 |
    Equal_Int_expression'_3 Integer |
    Field_expression_3 String |
    Finite_expression_3 Integer |
    Function_expression_3 [(String, Expression_3)] Pattern_0 Expression_2 |
    Gate_1_expression_3 String |
    Int_expression_3 Integer |
    Inverse_Finite_expression_3 Integer |
    Multiply_Finite_expression_3 Integer |
    Multiply_Finite_expression'_3 Integer Integer |
    Multiply_Int_expression_3 |
    Multiply_Int_expression'_3 Integer |
    Qbit_expression_3 Integer |
    Struct_expression_3 (Map' Expression_3)
      deriving Show
  circuit :: Defs -> Expression_2 -> Err (Circuit, Integer)
  circuit a b = circuit' (Left <$> a) init_circ b >>= \(c, d) -> case d of
    Creg_expression_3 e -> Right (c, e)
    _ -> Left "Code generation error. The output should be a classical register."
  circuit' :: Map' (Either Expression_2 Expression_3) -> Circuit -> Expression_2 -> Err (Circuit, Expression_3)
  circuit' a b c =
    let
      f = Right <$> (,) b
    in case c of
      Add_Finite_expression_2 d -> f (Add_Finite_expression_3 d)
      Add_Int_expression_2 -> f Add_Int_expression_3
      Algebraic_expression_2 d e -> second (Algebraic_expression_3 d) <$> eval_algebraic a b e
      Application_expression_2 d e -> undefined
      Convert_Finite_expression_2 d -> f (Convert_Finite_expression_3 d)
      Crash_expression_2 -> f Crash_expression_3
      Equal_Finite_expression_2 -> f Equal_Finite_expression_3
      Equal_Int_expression_2 -> f Equal_Int_expression_3
      Field_expression_2 d -> f (Field_expression_3 d)
      Finite_expression_2 d -> f (Finite_expression_3 d)
      Function_expression_2 d e -> f (Function_expression_3 [] d e)
      Gate_1_expression_2 d -> f (Gate_1_expression_3 d)
      Int_expression_2 d -> f (Int_expression_3 d)
      Inverse_Finite_expression_2 d -> f (Inverse_Finite_expression_3 d)
      Match_expression_2 d e -> circuit' a b d >>= \(g, h) -> case h of
        Algebraic_expression_3 i j -> case Data.Map.lookup i e of
          Just (Match k l) -> circuit' (eval_match k j a) g l
          Nothing -> ice
        Crash_expression_3 -> f Crash_expression_3
        _ -> ice
      Multiply_Finite_expression_2 d -> f (Multiply_Finite_expression_3 d)
      Multiply_Int_expression_2 -> f Multiply_Int_expression_3
      Name_expression_2 d -> case Data.Map.lookup d a of
        Just h -> case h of
          Left g -> circuit' a b g
          Right g -> f g
        Nothing -> ice
      Struct_expression_2 d -> second Struct_expression_3 <$> eval_struct a b d
      Take_expression_2 -> eval_take b
  eval_algebraic :: Map' (Either Expression_2 Expression_3) -> Circuit -> [Expression_2] -> Err (Circuit, [Expression_3])
  eval_algebraic a b c = case c of
    [] -> Right (b, [])
    d : e -> circuit' a b d >>= \(f, g) -> second ((:) g) <$> eval_algebraic a f e
  eval_match :: [Pattern_0] -> [Expression_3] -> Map' (Either Expression_2 Expression_3) -> Map' (Either Expression_2 Expression_3)
  eval_match = undefined
  eval_struct :: Map' (Either Expression_2 Expression_3) -> Circuit -> Map' Expression_2 -> Err (Circuit, Map' Expression_3)
  eval_struct a b c = case minViewWithKey c of
    Just ((d, e), f) -> circuit' a b e >>= \(g, h) -> second (insert d h) <$> eval_struct a g f
    Nothing -> Right (b, empty)
  eval_take :: Circuit -> Err (Circuit, Expression_3)
  eval_take (Circuit cc c q cg g) = Right (Circuit cc c (q + 1) cg g, Qbit_expression_3 q)
  init_circ :: Circuit
  init_circ = Circuit 0 [] 0 0 []
-----------------------------------------------------------------------------------------------------------------------------