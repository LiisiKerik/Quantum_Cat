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
    Array_expression_3 Integer [Expression_3] |
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
    Lift_Array_expression_3 |
    Lift_Array_expression'_3 Integer |
    Multiply_Finite_expression_3 Integer |
    Multiply_Finite_expression'_3 Integer Integer |
    Multiply_Int_expression_3 |
    Multiply_Int_expression'_3 Integer |
    Qbit_expression_3 Integer |
    Struct_expression_3 (Map' Expression_3)
      deriving Show
  add_g :: Circuit -> Gate' -> Circuit
  add_g (Circuit cc c q cg t) h = Circuit cc c q (cg + 1) (G' h : t)
  circuit :: Defs -> Expression_2 -> Err (Circuit, Integer)
  circuit a b = circuit' (Left <$> a) init_circ b >>= \(c, d) -> case d of
    Creg_expression_3 e -> Right (c, e)
    _ -> Left "Code generation error. The output should be a classical register."
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
        Convert_Finite_expression_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Int_expression_3 l -> Finite_expression_3 (mod l k)
          _ -> ice)
        Crash_expression_3 -> m
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
        Gate_1_expression_3 k -> Right (case j of
          Crash_expression_3 -> (i, Crash_expression_3)
          Qbit_expression_3 l -> (add_g i (Single_g k l), j)
          _ -> ice)
        Inverse_Finite_expression_3 k -> r (case j of
          Crash_expression_3 -> Crash_expression_3
          Finite_expression_3 l -> case div_finite k 1 l of
            Just n -> Algebraic_expression_3 "Wrap" [Finite_expression_3 n]
            Nothing -> Algebraic_expression_3 "Nothing" []
          _ -> ice)
        Lift_Array_expression_3 -> case j of
          Crash_expression_3 -> r Crash_expression_3
          Int_expression_3 k ->
            if k < 0 then code_err "Lift_Array applied to a negative Int." else r (Lift_Array_expression'_3 k)
          _ -> ice
        Lift_Array_expression'_3 k -> Right (second (Array_expression_3 k) (uncurry (replicate_circuit i k) (cleanup i j)))
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
        _ -> ice
      Array_expression_2 d e -> second (Array_expression_3 d) <$> eval_list a b e
      Convert_Finite_expression_2 d -> f (Convert_Finite_expression_3 d)
      Crash_expression_2 -> m
      Equal_Finite_expression_2 -> f Equal_Finite_expression_3
      Equal_Int_expression_2 -> f Equal_Int_expression_3
      Field_expression_2 d -> f (Field_expression_3 d)
      Finite_expression_2 d -> f (Finite_expression_3 d)
      Function_expression_2 d e -> f (Function_expression_3 [] d e)
      Gate_1_expression_2 d -> f (Gate_1_expression_3 d)
      Int_expression_2 d -> f (Int_expression_3 d)
      Inverse_Finite_expression_2 d -> f (Inverse_Finite_expression_3 d)
      Lift_Array_expression_2 -> f Lift_Array_expression_3
      Match_expression_2 d e -> circuit' a b d >>= \(g, h) -> case h of
        Algebraic_expression_3 i j ->
            let
              Match k l = unsafe_lookup i e
            in circuit' (eval_match k j a) g l
        Crash_expression_3 -> m
        _ -> ice
      Multiply_Finite_expression_2 d -> f (Multiply_Finite_expression_3 d)
      Multiply_Int_expression_2 -> f Multiply_Int_expression_3
      Name_expression_2 d -> case unsafe_lookup d a of
        Left g -> circuit' a b g
        Right g -> f g
      Struct_expression_2 d -> second Struct_expression_3 <$> eval_struct a b d
      Take_expression_2 -> eval_take b
  clean_gates ::
    Integer -> (([(Integer, Bool)], [Bool]), (Integer, [Gate])) -> (([(Integer, Bool)], [Bool]), (Integer, [Gate]))
-- TODO: THIS FUNCTION CAN BE REFACTORISED FURTHER. USE ZIPWITH MORE!
  clean_gates cc (r @ ((c, q), (cg, g))) = case g of
    [] -> r
    h : t ->
      let
        ifc cond n = if cond then id else update_c cc n
        iff cnd fc fq = if or cnd then (second (bimap ((+) 1) ((:) h)), (comp_all fc, comp_all fq)) else (id, (id, id))
        ifq cond n = if cond then id else update_q n
      in
        (\(f', (gc, gq)) -> f' (clean_gates cc ((gc c, gq q), (cg - 1, t)))) (case h of
          G' g' -> case g' of
            Double_g _ x y ->
              let
                x' = q !! fromInteger x
                y' = q !! fromInteger y
              in
                iff [x', y'] [] [ifq x' x, ifq y' y]
            Single_g _ x -> iff [q !! fromInteger x] [] []
            Toffoli_g x y z ->
              let
                x' = q !! fromInteger x
                y' = q !! fromInteger y
                z' = q !! fromInteger z
              in
                iff [x', y', z'] [] [ifq x' x, ifq y' y, ifq z' z]
          If_g x _ _ _ y ->
            let
              x' = q !! fromInteger (cc - x - 1)
              y' = (!!) q <$> fromInteger <$> y
            in
              iff (x' : y') [ifc x' x] (zipWith ifq y' y)
          Mea_g x y _ ->
            let
              x' = q !! fromInteger x
              y' = snd (c !! fromInteger (cc - y - 1))
            in
              iff [x', y'] [ifc y' y] [ifq x' x])
  clean_cregs :: Integer -> Integer -> [(Integer, Bool)] -> ([Integer], [(Integer, Integer)])
  clean_cregs m n x = case x of
    [] -> ([], [])
    (c, b) : t -> if b then bimap (c :) ((m, n) :) (clean_cregs (m - 1) (n - 1) t) else clean_cregs (m - 1) n t
  clean_qbits :: Integer -> Integer -> [Bool] -> (Integer, [(Integer, Integer)])
  clean_qbits m n x = case x of
    [] -> (n, [])
    h : t -> if h then second ((m, n) :) (clean_qbits (m + 1) (n + 1) t) else clean_qbits (m + 1) n t
  cleanup :: Circuit -> Expression_3 -> (Circuit, Expression_3)
  cleanup (Circuit cc c q cg g) x = let
    ((c'', q''), (cg', g')) = clean_gates cc (tag_circ cc (init' c, replicate (fromInteger q) False) x, (cg, g))
    cc3 = count_cregs c''
    (c', cmap) = clean_cregs (cc - 1) (cc3 - 1) c''
    (qc, qmap) = clean_qbits 0 0 q''
    fc = flip lookup' cmap
    fq = flip lookup' qmap in
      (Circuit cc3 c' qc cg' (transf_gate fc fq <$> g'), transf_val fc fq x)
  code_err :: String -> Err t
  code_err = Left <$> (++) "Code generation error. "
  comp_all :: [t -> t] -> t -> t
  comp_all = Prelude.foldr (<$>) id
  count_cregs :: [(t, Bool)] -> Integer
  count_cregs x = case x of
    [] -> 0
    (_, h) : t -> (if h then (+ 1) else id) (count_cregs t)
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
  init' :: [t] -> [(t, Bool)]
  init' = (<$>) (flip (,) False)
  init_circ :: Circuit
  init_circ = Circuit 0 [] 0 0 []
  lookup' :: Eq t => t -> [(t, u)] -> u
  lookup' a b = case b of
    [] -> ice
    (c, d) : e -> if c == a then d else lookup' a e
  offset' :: Functor f => Integer -> Integer -> f Expression_3 -> f Expression_3
  offset' c q x = fmap (offset_val c q) x
  offset_val :: Integer -> Integer -> Expression_3 -> Expression_3
  offset_val c q v =
    let
      offset_list = offset' c q
    in case v of
      Algebraic_expression_3 x y -> Algebraic_expression_3 x (offset_list y)
      Array_expression_3 n x -> Array_expression_3 n (offset_list x)
      Creg_expression_3 x -> Creg_expression_3 (x + c)
      Qbit_expression_3 x -> Qbit_expression_3 (x + q)
      Struct_expression_3 x -> Struct_expression_3 (offset' c q x)
      _ -> v
  replicate_circuit :: Circuit -> Integer -> Circuit -> Expression_3 -> (Circuit, [Expression_3])
  replicate_circuit(circ @ (Circuit cc c q gc g)) n (circ' @ (Circuit cc' c' q' gc' g')) v =
    if n == 0 then
      (circ, [])
    else
      second
        ((:) (offset_val cc q v))
        (replicate_circuit
          (Circuit (cc + cc') (c' ++ c) (q + q') (gc + gc') ((transf_gate (+ cc) (+ q) <$> g') ++ g))
          (n - 1)
          circ'
          v)
  tag_arr :: Integer -> ([(Integer, Bool)], [Bool]) -> [Expression_3] -> ([(Integer, Bool)], [Bool])
  tag_arr cc t x = case x of
    [] -> t
    y : z -> tag_arr cc (tag_circ cc t y) z
  tag_circ :: Integer -> ([(Integer, Bool)], [Bool]) -> Expression_3 -> ([(Integer, Bool)], [Bool])
  tag_circ cc (t @ (c, q)) x =
    let
      ta = tag_arr cc t
    in case x of
      Algebraic_expression_3 _ a -> ta a
      Array_expression_3 _ a -> ta a
      Creg_expression_3 a -> (update_c cc a c, q)
      Qbit_expression_3 a -> (c, update_q a q)
      Struct_expression_3 a -> tag_map cc t a
      _ -> t
  tag_map :: Integer -> ([(Integer, Bool)], [Bool]) -> Map' Expression_3 -> ([(Integer, Bool)], [Bool])
  tag_map cc t x = case minViewWithKey x of
    Just (y, z) -> tag_map cc (tag_circ cc t (snd y)) z
    Nothing -> t
  transf_gate :: (Integer -> Integer) -> (Integer -> Integer) -> Gate -> Gate
  transf_gate c q g = case g of
    G' g' -> G' (transf_gate' q g')
    If_g x y a f z -> If_g (c x) y a f (q <$> z)
    Mea_g x y z -> Mea_g (q x) (c y) z
  transf_gate' :: (Integer -> Integer) -> Gate' -> Gate'
  transf_gate' q g = case g of
    Double_g f x y -> Double_g f (q x) (q y)
    Single_g f x -> Single_g f (q x)
    Toffoli_g x y z -> Toffoli_g (q x) (q y) (q z)
  transf_val :: (Integer -> Integer) -> (Integer -> Integer) -> Expression_3 -> Expression_3
  transf_val c q x =
    let
      f = transf_val' c q
    in case x of
      Algebraic_expression_3 y z -> Algebraic_expression_3 y (f z)
      Array_expression_3 n y -> Array_expression_3 n (f y)
      Creg_expression_3 y -> Creg_expression_3 (c y)
      Qbit_expression_3 y -> Qbit_expression_3 (q y)
      Struct_expression_3 y -> Struct_expression_3 (transf_val' c q y)
      _ -> x
  transf_val' :: Functor f => (Integer -> Integer) -> (Integer -> Integer) -> f Expression_3 -> f Expression_3
  transf_val' c q = fmap (transf_val c q)
  update_c :: Integer -> Integer -> [(Integer, Bool)] -> [(Integer, Bool)]
  update_c x y = update_c' (x - y - 1)
  update_c' :: Integer -> [(Integer, Bool)] -> [(Integer, Bool)]
  update_c' x y = case y of
    [] -> ice
    z @ (w, _) : a -> if x == 0 then (w, True) : a else z : update_c' (x - 1) a
  update_q :: Integer -> [Bool] -> [Bool]
  update_q x y = case y of
    [] -> ice
    z : w -> if x == 0 then True : w else z : update_q (x - 1) w
-----------------------------------------------------------------------------------------------------------------------------