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
  data Gate = Unitary Gate' | If_g Integer Integer Integer [Gate'] [Integer] | Mea_g Integer Integer Integer deriving Show
  data Gate' = CCX_gate Integer Integer Integer | Double_gate String Integer Integer | Single_gate String Integer
    deriving Show
  data Expression_3 =
    Add_Finite_expression_3 Integer |
    Add_Finite_expression'_3 Integer Integer |
    Add_Int_expression_3 |
    Add_Int_expression'_3 Integer |
    Algebraic_expression_3 String [Expression_3] |
    Array_expression_3 Integer [Expression_3] |
    CCX_expression_3 |
    CCX_expression'_3 Integer |
    CCX_expression''_3 Integer Integer |
    Construct_expression_3 |
    Construct_expression'_3 Integer |
    Convert_Finite_expression_3 Integer |
    Crash_expression_3 |
    Creg_expression_3 Integer |
    Double_expression_3 String |
    Double_expression'_3 String Integer |
    Equal_Finite_expression_3 |
    Equal_Finite_expression'_3 Integer |
    Equal_Int_expression_3 |
    Equal_Int_expression'_3 Integer |
    Field_expression_3 String |
    Finite_expression_3 Integer |
    Function_expression_3 [(String, Expression_3)] Pattern_0 Expression_2 |
    Index_expression_3 |
    Index_expression'_3 Integer [Expression_3] |
    Int_expression_3 Integer |
    Inverse_Finite_expression_3 Integer |
    Length_expression_3 |
    Less_Int_expression_3 |
    Less_Int_expression'_3 Integer |
    Mod_Int_expression_3 |
    Mod_Int_expression'_3 Integer |
    Multiply_Finite_expression_3 Integer |
    Multiply_Finite_expression'_3 Integer Integer |
    Multiply_Int_expression_3 |
    Multiply_Int_expression'_3 Integer |
    Negate_Int_expression_3 |
    Qbit_expression_3 Integer |
    Single_expression_3 String |
    Struct_expression_3 (Map' Expression_3)
      deriving Show
  add_g :: Circuit -> Gate' -> Circuit
  add_g (Circuit cc c q cg t) h = Circuit cc c q (cg + 1) (Unitary h : t)
  circuit :: Defs -> Expression_2 -> Err (Circuit, Integer)
  circuit a b = circuit' (Left <$> a) (Circuit 0 [] 0 0 []) b >>= \(c, d) -> case d of
    Crash_expression_3 -> code_err "Crash."
    Creg_expression_3 e -> Right (c, e)
    _ -> ice
-- TODO: MAYBE HERE IT'S UNNECESSARY TO HAVE ERR IN OUTPUT? CHECK AND REMOVE LATER, WHEN IMPLEMENTATION FINISHED
  circuit' :: Map' (Either Expression_2 Expression_3) -> Circuit -> Expression_2 -> Err (Circuit, Expression_3)
  circuit' a b c =
    let
      f = Right <$> (,) b
      m = f Crash_expression_3
    in case c of
      Add_Finite_expression_2 d -> f (Add_Finite_expression_3 d)
      Add_Int_expression_2 -> f Add_Int_expression_3
      Algebraic_expression_2 d e -> second (Algebraic_expression_3 d) <$> eval_list a b e
      Application_expression_2 d e -> circuit' a b d >>= \(g, h) -> circuit' a g e >>= \(i, j) ->
        let
          r = Right <$> (,) i
        in case h of
        Add_Finite_expression_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Finite_expression_3 l -> Add_Finite_expression'_3 k l
          _ -> ice)
        Add_Finite_expression'_3 k l -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Finite_expression_3 n -> Finite_expression_3 (mod (l + n) k)
          _ -> ice)
        Add_Int_expression_3 -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 l -> Add_Int_expression'_3 l
          _ -> ice)
        Add_Int_expression'_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 n -> Int_expression_3 (k + n)
          _ -> ice)
        CCX_expression_3 -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Qbit_expression_3 k -> CCX_expression'_3 k
          _ -> ice)
        CCX_expression'_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Qbit_expression_3 l -> CCX_expression''_3 k l
          _ -> ice)
        CCX_expression''_3 k l -> Right (case j of
          Crash_expression_3 -> (i, Crash_expression_3)
          Qbit_expression_3 n -> (add_g i (CCX_gate k l n), j)
          _ -> ice)
        Construct_expression_3 -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 k -> Construct_expression'_3 k
          _ -> ice)
        Construct_expression'_3 k ->
          if k < 0 then
            r (Algebraic_expression_3 "Nothing" [])
          else
            second (\l -> Algebraic_expression_3 "Wrap" [Array_expression_3 k l]) <$> construct_array a i 0 k e
        Convert_Finite_expression_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 l -> Finite_expression_3 (mod l k)
          _ -> ice)
        Crash_expression_3 -> m
        Double_expression_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Qbit_expression_3 l -> Double_expression'_3 k l
          _ -> ice)
        Double_expression'_3 k l -> Right (case j of
          Crash_expression_3 -> (i, Crash_expression_3)
          Qbit_expression_3 n -> (add_g i (Double_gate k l n), j)
          _ -> ice)
        Equal_Finite_expression_3 -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Finite_expression_3 k -> Equal_Finite_expression'_3 k
          _ -> ice)
        Equal_Finite_expression'_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Finite_expression_3 l -> Algebraic_expression_3 (show (k == l)) []
          _ -> ice)
        Equal_Int_expression_3 -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 k -> Equal_Int_expression'_3 k
          _ -> ice)
        Equal_Int_expression'_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 l -> Algebraic_expression_3 (show (k == l)) []
          _ -> ice)
        Field_expression_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Struct_expression_3 l -> unsafe_lookup k l
          _ -> ice)
        Function_expression_3 k l n ->
          let
            o = case l of
              Blank_pattern -> k
              Name_pattern p -> (p, j) : k
          in case n of
            Function_expression_2 q s -> r (Function_expression_3 o q s)
            _ -> circuit' (Prelude.foldl (flip (\(v, u) -> insert v (Right u))) a o) i n
        Index_expression_3 -> r (case j of
          Array_expression_3 k l -> Index_expression'_3 k l
          Crash_expression_3 -> Crash_expression_3
          _ -> ice)
        Index_expression'_3 k l -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 n ->
            if n < 0 || n > k then
              Algebraic_expression_3 "Nothing" []
            else
              Algebraic_expression_3 "Wrap" [l !! fromInteger n]
          _ -> ice)
        Inverse_Finite_expression_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Finite_expression_3 l -> case div_finite k 1 l of
            Just n -> Algebraic_expression_3 "Wrap" [Finite_expression_3 n]
            Nothing -> Algebraic_expression_3 "Nothing" []
          _ -> ice)
        Length_expression_3 -> r (case j of
          Array_expression_3 k _ -> Int_expression_3 k
          Crash_expression_3 -> Crash_expression_3
          _ -> ice)
        Less_Int_expression_3 -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 k -> Less_Int_expression'_3 k
          _ -> ice)
        Less_Int_expression'_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 l -> Algebraic_expression_3 (show (k < l)) []
          _ -> ice)
        Mod_Int_expression_3 -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 k -> Mod_Int_expression'_3 k
          _ -> ice)
        Mod_Int_expression'_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 l -> Int_expression_3 (mod k (abs l))
          _ -> ice)
        Multiply_Finite_expression_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Finite_expression_3 l -> Multiply_Finite_expression'_3 k l
          _ -> ice)
        Multiply_Finite_expression'_3 k l -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Finite_expression_3 n -> Finite_expression_3 (mod (l * n) k)
          _ -> ice)
        Multiply_Int_expression_3 -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 l -> Multiply_Int_expression'_3 l
          _ -> ice)
        Multiply_Int_expression'_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 n -> Int_expression_3 (k * n)
          _ -> ice)
        Negate_Int_expression_3 -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 k -> Int_expression_3 (- k)
          _ -> ice)
        Single_expression_3 k -> Right (case j of
          Crash_expression_3 -> (i, Crash_expression_3)
          Qbit_expression_3 l -> (add_g i (Single_gate k l), j)
          _ -> ice)
        _ -> ice
      CCX_expression_2 -> f CCX_expression_3
      Construct_expression_2 -> f Construct_expression_3
      Convert_Finite_expression_2 d -> f (Convert_Finite_expression_3 d)
      Crash_expression_2 -> m
      Double_expression_2 d -> f (Double_expression_3 d)
      Equal_Finite_expression_2 -> f Equal_Finite_expression_3
      Equal_Int_expression_2 -> f Equal_Int_expression_3
      Field_expression_2 d -> f (Field_expression_3 d)
      Finite_expression_2 d -> f (Finite_expression_3 d)
      Function_expression_2 d e -> f (Function_expression_3 [] d e)
      Index_expression_2 -> f Index_expression_3
      Int_expression_2 d -> f (Int_expression_3 d)
      Inverse_Finite_expression_2 d -> f (Inverse_Finite_expression_3 d)
      Length_expression_2 -> f Length_expression_3
      Less_Int_expression_2 -> f Less_Int_expression_3
      Match_expression_2 d e -> circuit' a b d >>= \(g, h) -> case h of
        Algebraic_expression_3 i j ->
            let
              Match k l = unsafe_lookup i e
            in circuit' (eval_match k j a) g l
        Crash_expression_3 -> m
        _ -> ice
      Mod_Int_expression_2 -> f Mod_Int_expression_3
      Multiply_Finite_expression_2 d -> f (Multiply_Finite_expression_3 d)
      Multiply_Int_expression_2 -> f Multiply_Int_expression_3
      Name_expression_2 d -> case unsafe_lookup d a of
        Left g -> circuit' a b g
        Right g -> f g
      Negate_Int_expression_2 -> f Negate_Int_expression_3
      Single_expression_2 d -> f (Single_expression_3 d)
      Struct_expression_2 d -> second Struct_expression_3 <$> eval_struct a b d
      Take_expression_2 -> eval_take b
  code_err :: String -> Err t
  code_err = Left <$> (++) "Code generation error. "
  construct_array ::
    Map' (Either Expression_2 Expression_3) -> Circuit -> Integer -> Integer -> Expression_2 -> Err (Circuit, [Expression_3])
  construct_array d a i i_fin c =
    if i == i_fin then
      Right (a, [])
    else
      (
        circuit' d a (Application_expression_2 c (Int_expression_2 i)) >>=
        \(b, e) -> second ((:) e) <$> construct_array d b (i + 1) i_fin c)
  div_finite :: Integer -> Integer -> Integer -> Maybe Integer
  div_finite a b c = case a of
    1 -> Just 0
    _ -> case c of
      0 -> Nothing
      _ -> (\d -> div (a * d + b) c) <$> div_finite c (mod (- b) c) (mod a c)
  eval_list :: Map' (Either Expression_2 Expression_3) -> Circuit -> [Expression_2] -> Err (Circuit, [Expression_3])
  eval_list a b c = case c of
    [] -> Right (b, [])
    d : e -> circuit' a b d >>= \(f, g) -> second ((:) g) <$> eval_list a f e
  eval_match ::
    [Pattern_0] -> [Expression_3] -> Map' (Either Expression_2 Expression_3) -> Map' (Either Expression_2 Expression_3)
  eval_match a b = case a of
    [] -> case b of
      [] -> id
      _ -> ice
    d : e -> case b of
      [] -> ice
      f : g -> eval_match e g <$> (case d of
        Blank_pattern -> id
        Name_pattern c -> insert c (Right f))
  eval_struct :: Map' (Either Expression_2 Expression_3) -> Circuit -> Map' Expression_2 -> Err (Circuit, Map' Expression_3)
  eval_struct a b c = case minViewWithKey c of
    Just ((d, e), f) -> circuit' a b e >>= \(g, h) -> second (insert d h) <$> eval_struct a g f
    Nothing -> Right (b, empty)
  eval_take :: Circuit -> Err (Circuit, Expression_3)
  eval_take (Circuit cc c q cg g) = Right (Circuit cc c (q + 1) cg g, Qbit_expression_3 q)
-----------------------------------------------------------------------------------------------------------------------------