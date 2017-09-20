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
  data Gate = Unitary Gate' | If_g Integer Integer Integer [Gate'] [Integer] | Measure_gate Integer Integer Integer
    deriving Show
  data Gate' = CCX_gate Integer Integer Integer | Double_gate String Integer Integer | Single_gate String Integer
    deriving Show
  add_creg :: Integer -> Circuit -> (Integer, Circuit)
  add_creg n (Circuit cc c q cg g) = (cc, Circuit (cc + 1) (n : c) q cg g)
  add_g :: Circuit -> Gate' -> Circuit
  add_g (Circuit cc c q cg t) h = Circuit cc c q (cg + 1) (Unitary h : t)
  add_measure :: Integer -> Integer -> Integer -> Circuit -> Circuit
  add_measure x y z (Circuit cc c q cg g) = Circuit cc c q (cg + 1) (Measure_gate x y z : g)
  circuit :: Defs -> Expression_2 -> Err (Circuit, Integer)
  circuit a b = circuit' a (Circuit 0 [] 0 0 []) b >>= \(c, d) -> case d of
    Crash_expression_2 -> code_err "Crash."
    Creg_expression_2 e -> Right (c, e)
    _ -> ice
-- TODO: MAYBE HERE IT'S UNNECESSARY TO HAVE ERR IN OUTPUT? CHECK AND REMOVE LATER, WHEN IMPLEMENTATION FINISHED
  circuit' :: Map' Expression_2 -> Circuit -> Expression_2 -> Err (Circuit, Expression_2)
  circuit' a b c =
    let
      f = Right <$> (,) b
      m = f Crash_expression_2
    in case c of
      Application_expression_2 d e -> circuit' a b d >>= \(g, h) -> circuit' a g e >>= \(i, j) ->
        let
          r = Right <$> (,) i
        in case h of
          Add_Int_expression_2 -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 l -> Add_Int'_expression_2 l
            _ -> ice)
          Add_Int'_expression_2 k -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 n -> Int_expression_2 (k + n)
            _ -> ice)
          CCX_expression_2 -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Qbit_expression_2 k -> CCX'_expression_2 k
            _ -> ice)
          CCX'_expression_2 k -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Qbit_expression_2 l -> CCX''_expression_2 k l
            _ -> ice)
          CCX''_expression_2 k l -> Right (case j of
            Crash_expression_2 -> (i, Crash_expression_2)
            Qbit_expression_2 n -> (add_g i (CCX_gate k l n), j)
            _ -> ice)
          Construct_expression_2 -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 k -> Construct'_expression_2 k
            _ -> ice)
          Construct'_expression_2 k ->
            if k < 0 then
              r nothing_algebraic
            else
              second (\l -> wrap_algebraic (Array_expression_2 k l)) <$> construct_array a i 0 k e
          Crash_expression_2 -> m
          Double_expression_2 k -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Qbit_expression_2 l -> Double'_expression_2 k l
            _ -> ice)
          Double'_expression_2 k l -> Right (case j of
            Crash_expression_2 -> (i, Crash_expression_2)
            Qbit_expression_2 n -> (add_g i (Double_gate k l n), j)
            _ -> ice)
          Equal_Int_expression_2 -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 k -> Equal_Int'_expression_2 k
            _ -> ice)
          Equal_Int'_expression_2 k -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 l -> logical_algebraic (k == l)
            _ -> ice)
          Field_expression_2 k -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Struct_expression_2 l -> unsafe_lookup k l
            _ -> ice)
          Function_expression_2 k l -> circuit' a i (case k of
            Blank_pattern -> l
            Name_pattern n -> subst_expr n l j)
          Index_expression_2 -> r (case j of
            Array_expression_2 k l -> Index'_expression_2 k l
            Crash_expression_2 -> Crash_expression_2
            _ -> ice)
          Index'_expression_2 k l -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 n ->
              if n < 0 || n > k then nothing_algebraic else wrap_algebraic (l !! fromInteger n)
            _ -> ice)
          Length_expression_2 -> r (case j of
            Array_expression_2 k _ -> Int_expression_2 k
            Crash_expression_2 -> Crash_expression_2
            _ -> ice)
          Less_Int_expression_2 -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 k -> Less_Int'_expression_2 k
            _ -> ice)
          Less_Int'_expression_2 k -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 l -> logical_algebraic (k < l)
            _ -> ice)
          Measure_expression_2 -> case j of
            Array_expression_2 k l ->
              let
                (x, y) = add_creg k i
              in case measure x 0 y l of
                Left n -> Right (n, Crash_expression_2)
                Right n -> Right (n, Creg_expression_2 x)
            Crash_expression_2 -> r Crash_expression_2
            _ -> ice
          Mod_Int_expression_2 -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 k -> Mod_Int'_expression_2 k
            _ -> ice)
          Mod_Int'_expression_2 k -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 l -> Int_expression_2 (mod k (abs l))
            _ -> ice)
          Multiply_Int_expression_2 -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 k -> Multiply_Int'_expression_2 k
            _ -> ice)
          Multiply_Int'_expression_2 k -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 l -> Int_expression_2 (k * l)
            _ -> ice)
          Negate_Int_expression_2 -> r (case j of
            Crash_expression_2 -> Crash_expression_2
            Int_expression_2 k -> Int_expression_2 (- k)
            _ -> ice)
          Single_expression_2 k -> Right (case j of
            Crash_expression_2 -> (i, Crash_expression_2)
            Qbit_expression_2 l -> (add_g i (Single_gate k l), j)
            _ -> ice)
          Take_expression_2 -> case j of
            Crash_expression_2 -> r Crash_expression_2
            Struct_expression_2 _ -> eval_take i
            _ -> ice
          _ -> ice
      Match_expression_2 d e -> circuit' a b d >>= \(g, h) ->
        let
          n o = circuit' o g
          s = n a
        in case e of
          Matches_Algebraic_2 i j -> case h of
            Algebraic_expression_2 k l -> case Data.Map.lookup k i of
              Just (Match_Algebraic_2 o p) -> n (eval_match o l a) p
              Nothing -> case j of
                Just o -> s o
                Nothing -> ice
            Crash_expression_2 -> m
            _ -> ice
          Matches_Int_2 i j -> case h of
            Crash_expression_2 -> m
            Int_expression_2 k -> s (case Data.Map.lookup k i of
              Just o -> o
              Nothing -> j)
            _ -> ice
      Name_expression_2 d -> circuit' a b (unsafe_lookup d a)
      _ -> f c
  code_err :: String -> Err t
  code_err = Left <$> (++) "Code generation error. "
  construct_array :: Map' Expression_2 -> Circuit -> Integer -> Integer -> Expression_2 -> Err (Circuit, [Expression_2])
  construct_array d a i i_fin c =
    if i == i_fin then
      Right (a, [])
    else
      (
        circuit' d a (Application_expression_2 c (Int_expression_2 i)) >>=
        \(b, e) -> second ((:) e) <$> construct_array d b (i + 1) i_fin c)
  eval_match :: [Pattern_0] -> [Expression_2] -> Map' Expression_2 -> Map' Expression_2
  eval_match a b = case a of
    [] -> case b of
      [] -> id
      _ -> ice
    d : e -> case b of
      [] -> ice
      f : g -> eval_match e g <$> (case d of
        Blank_pattern -> id
        Name_pattern c -> insert c f)
  eval_take :: Circuit -> Err (Circuit, Expression_2)
  eval_take (Circuit cc c q cg g) = Right (Circuit cc c (q + 1) cg g, Qbit_expression_2 q)
  measure :: Integer -> Integer -> Circuit -> [Expression_2] -> Either Circuit Circuit
  measure f g a b = case b of
    [] -> Right a
    c : d -> case c of
      Crash_expression_2 -> Left a
      Qbit_expression_2 e -> measure f (g + 1) (add_measure e f g a) d
      _ -> ice
  logical_algebraic :: Bool -> Expression_2
  logical_algebraic a = Algebraic_expression_2 (show a) []
  nothing_algebraic :: Expression_2
  nothing_algebraic = Algebraic_expression_2 "Nothing" []
  subst_algebraic :: String -> Expression_2 -> Match_Algebraic_2 -> Match_Algebraic_2
  subst_algebraic a b (Match_Algebraic_2 c d) = Match_Algebraic_2 c (subst_expr a d b)
  subst_expr :: String -> Expression_2 -> Expression_2 -> Expression_2
  subst_expr a b c =
    let
      f x = subst_expr a x c
      f_list = (<$>) f
      f_map = (<$>) f
    in case b of
      Algebraic_expression_2 d e -> Algebraic_expression_2 d (f_list e)
      Application_expression_2 d e -> Application_expression_2 (f d) (f e)
      Array_expression_2 d e -> Array_expression_2 d (f_list e)
      Function_expression_2 d e -> case d of
        Blank_pattern -> c
        Name_pattern g -> if g == a then c else Function_expression_2 d (f e)
      Index'_expression_2 d e -> Index'_expression_2 d (f_list e)
      Match_expression_2 d e -> Match_expression_2 (f d) (case e of
        Matches_Algebraic_2 g h -> Matches_Algebraic_2 (subst_algebraic a c <$> g) (f <$> h)
        Matches_Int_2 g h -> Matches_Int_2 (f <$> g) (f h))
      Name_expression_2 d -> if d == a then c else b
      Struct_expression_2 d -> Struct_expression_2 (f_map d)
      _ -> b
  wrap_algebraic :: Expression_2 -> Expression_2
  wrap_algebraic a = Algebraic_expression_2 "Wrap" [a]
-----------------------------------------------------------------------------------------------------------------------------