-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TupleSections #-}
module Circuit where
  import Data.Bifunctor
  import Tree
  import Typing
  data Circuit = Circuit Integer [Integer] Integer Integer [Gate] deriving (Eq, Show)
  data Gate = G' Gate' | If_g Integer Integer Integer [Gate'] [Integer] | Mea_g Integer Integer Integer deriving (Eq, Show)
  data Gate' = Double_g String Integer Integer | Single_g String Integer | Toffoli_g Integer Integer Integer
    deriving (Eq, Show)
  data Val =
    Alg_val String [Val] |
    Arr_val [Val] |
    Creg_pointer Integer |
    Func_val ([(String, Either Def_tree'' Val)] -> Circuit -> Val -> Either String (Circuit, Val)) |
    Int_val Integer |
    Qbit_pointer Integer |
    Struct_val [Val]
      deriving (Eq, Show)
  add_g :: Circuit -> Gate' -> Circuit
  add_g (Circuit cc c q cg t) h = Circuit cc c q (cg + 1) (G' h : t)
  add_to_context :: [(String, Either Def_tree'' Val)] -> [String] -> [Val] -> [(String, Either Def_tree'' Val)]
  add_to_context d [] [] = d
  add_to_context d (x : y) (z : w) = (x, Right z) : add_to_context d y w
  add_to_context _ _ _ = error("Internal compiler error. Failed pattern match due to wrong number of variables.")
  circ_lookup :: [(Integer, Integer)] -> Integer -> Integer
  circ_lookup x y = unsafe_lookup x y "Internal compiler error. Bit or register lookup failure."
  circuit :: [(String, Def_tree'')] -> Expression_tree'' -> Either String (Circuit, Val)
  circuit d = circuit' (second Left <$> d) init_circ
  circuit' :: [(String, Either Def_tree'' Val)] -> Circuit -> Expression_tree'' -> Either String (Circuit, Val)
  circuit' d (circ @ (Circuit cc c q cg g)) (Expression_tree'' _ e _) = case e of
    Alg'' x e' -> eval_struct (Alg_val x) d circ e'
    App'' e1 e2 -> circuit' d circ e1 >>= \(_, fn) -> case fn of
      Func_val f -> circuit' d circ e2 >>= uncurry (f d)
      _ -> error "Internal compiler error. Expected function when generating code, got non-function."
    Double_qbit_def f ->
      func_val
        circ
        (pure_func (\(Qbit_pointer x) -> \circ' -> \(p @ (Qbit_pointer y)) -> Right (add_g circ' (Double_g f x y), p)))
    Field'' n -> func_val circ (\circ' -> \(Struct_val x) -> Right (circ', x !! fromInteger n))
    Foldr''{} ->
      func_val
        circ
        (pure_func
          (\(Func_val f) -> pure_func' (\x -> Func_val (\d' -> \circ' -> \(Arr_val y) -> foldr_circ d' (f d') x circ' y))))
    Fun'' x e' -> Right (circ, Func_val (\d' -> \circ' -> \x' -> circuit' ((x, Right x') : d') circ' e'))
    If_gate'' t _ ->
      if qtype t then
        func_val
          circ
          (pure_func
            (\(Creg_pointer x) ->
              pure_func
                (\(Int_val y) -> -- TODO: CHECK WHETHER VALUE OF Y IS IN A SUITABLE RANGE, RETURN ERROR MSG WITH LEFT OTHERWISE
                  pure_func
                    (\(Func_val f) ->
                    \(circ' @ (Circuit cc' c' q' cg' g')) ->
                    \z ->
                      f d circ' z >>=
                      \(Circuit _ c'' q'' cg'' g'', z') ->
                        if c'' == c' && q'' == q' && z' == z then
                          (\(sub_gates, tagged_qbits) ->
                            let
                              (inps, arg_num) = gate_map tagged_qbits 0 0
                            in
                              (
                                Circuit
                                  cc'
                                  c'
                                  q'
                                  (cg' + 1)
                                  (If_g x y arg_num (transf_gate' (circ_lookup inps) <$> sub_gates) (fst <$> inps) : g'),
                                z)) <$>
                          tag_qbits (take (fromInteger (cg'' - cg')) g'') (replicate (fromInteger q') False)
                        else
                          Left
                            ("Code generation error. The function fed to If_gate is not allowed to " ++
                            "allocate qbits, make measurements, include conditionals, " ++
                            "or change the intermediate result pointer.")))))
      else
        Left "Type error. If_gate can only be applied to quantum types."
    Int_expr'' n -> Right (circ, Int_val n)
    Lift'' _ m -> case m of
      Int_constant n ->
        func_val circ (\circ' -> \x -> Right (second Arr_val (uncurry (replicate_circuit circ' n) (cleanup (circ', x)))))
      _ -> error "Internal compiler error. Found a free integer type variable during code generation."
    Map''{} ->
      func_val
        circ
        (pure_func'
          (\(Func_val f) -> Func_val (\d' -> \circ'' -> \(Arr_val x) -> second Arr_val <$> (map_help (f d') circ'' x))))
    Match'' e' m -> circuit' d circ e' >>= \(circ', v) -> case v of
      Alg_val x y -> let
        (z, e'') = find_case m x in
          circuit' (add_to_context d z y) circ' e''
      _ -> error "Internal compiler error. Match expression got something that is not an algebraic structure as parameter."
    Mes''{} ->
      func_val
        circ
        (
          \(Circuit cc' c' q' cg' g') ->
          \(Arr_val x) ->
            Right
              ((\(c'', (cg'', g'')) -> Circuit (cc' + 1) (c'' : c') q' cg'' g'') (mes_help cc' cg' g' 0 x), Creg_pointer cc'))
    Name'' x t n -> case unsafe_lookup d x "Internal compiler error. Found an undefined variable." of
      Left (Def_tree'' _ (Bind b _) e') -> circuit' d circ ((case b of
        Global v w -> type_application (zip v t) (zip w n)
        Local -> id) e')
      Right v -> Right (circ, v)
-- TODO: GENERALISE THIS AND THE CNOT AND TOFFOLI CASES, AND MAYBE IF AND MEASUREMENT?, WITH SOME HELPER FUNCTION?
    Single_qbit_def f -> func_val circ (\circ' -> \p @ (Qbit_pointer x) -> Right (add_g circ' (Single_g f x), p))
    Str'' e' -> eval_struct Struct_val d circ e'
    Take'' -> Right (Circuit cc c (q + 1) cg g, Qbit_pointer q)
    Toffoli'' ->
      func_val
        circ
        (pure_func
          (\(Qbit_pointer x) ->
            pure_func (\(Qbit_pointer y) -> \circ' -> \(p @ (Qbit_pointer z)) -> Right (add_g circ' (Toffoli_g x y z), p))))
  clean_cregs :: Integer -> Integer -> [(Integer, Bool)] -> ([Integer], [(Integer, Integer)])
  clean_cregs m n x = case x of
    [] -> ([], [])
    (c, b) : t -> if b then bimap (c :) ((m, n) :) (clean_cregs (m - 1) (n - 1) t) else clean_cregs (m - 1) n t
  clean_gates ::
    Integer -> (([(Integer, Bool)], [Bool]), (Integer, [Gate])) -> (([(Integer, Bool)], [Bool]), (Integer, [Gate]))
-- TODO: THIS FUNCTION CAN BE REFACTORISED FURTHER. USE ZIPWITH MORE!
  clean_gates cc (r @ ((c, q), (cg, g))) = case g of
    [] -> r
    h : t ->
      let
        ifc cond n = if cond then id else update_c cc n
        iff cnd fc fq = if or cnd then (second (bimap (+ 1) (h :)), (comp_all fc, comp_all fq)) else (id, (id, id))
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
  clean_qbits :: Integer -> Integer -> [Bool] -> (Integer, [(Integer, Integer)])
  clean_qbits m n x = case x of
    [] -> (n, [])
    h : t -> if h then second ((m, n) :) (clean_qbits (m + 1) (n + 1) t) else clean_qbits (m + 1) n t
  cleanup :: (Circuit, Val) -> (Circuit, Val)
  cleanup (Circuit cc c q cg g, x) = let
    ((c'', q''), (cg', g')) = clean_gates cc (tag_circ cc (init' c, replicate (fromInteger q) False) x, (cg, g))
    cc3 = count_cregs c''
    (c', cmap) = clean_cregs (cc - 1) (cc3 - 1) c''
    (qc, qmap) = clean_qbits 0 0 q''
    fc = circ_lookup cmap
    fq = circ_lookup qmap in
      (Circuit cc3 c' qc cg' (transf_gate fc fq <$> g'), transf_val fc fq x)
  comp_all :: [t -> t] -> t -> t
  comp_all = foldr (<$>) id
  count_cregs :: [(t, Bool)] -> Integer
  count_cregs x = case x of
    [] -> 0
    (_, h) : t -> (if h then (+ 1) else id) (count_cregs t)
  eval_struct ::
    ([Val] -> Val) -> [(String, Either Def_tree'' Val)] -> Circuit -> [Expression_tree''] -> Either String (Circuit, Val)
  eval_struct f d c e = second f <$> eval_struct' d c e
  eval_struct' :: [(String, Either Def_tree'' Val)] -> Circuit -> [Expression_tree''] -> Either String (Circuit, [Val])
  eval_struct' d c e = case e of
    [] -> Right (c, [])
    h : t -> circuit' d c h >>= \(c', h') -> second (h' :) <$> (eval_struct' d c' t)
  find_case :: [Match_case''] -> String -> ([String], Expression_tree'')
  find_case x y = case x of
    [] -> error("Internal compiler error. Failed algebraic data type matching.")
    Match_case'' z w a : b -> if z == y then (w, a) else find_case b y
  foldr_circ ::
    [(String, Either Def_tree'' Val)] ->
    (Circuit -> Val -> Either String (Circuit, Val)) ->
    Val ->
    Circuit ->
    [Val] ->
    Either String (Circuit, Val)
  foldr_circ d f x circ y = case y of
    [] -> Right (circ, x)
    h : t -> foldr_circ d f x circ t >>= \(circ', z) -> f circ' h >>= \(_, Func_val g) -> g d circ' z
  func_val :: Circuit -> (Circuit -> Val -> Either String (Circuit, Val)) -> Either String (Circuit, Val)
  func_val circ f = Right (circ, Func_val (return f))
  func_val' :: Circuit -> Val -> Either String (Circuit, Val)
  func_val' circ x = Right (circ, x)
  gate_map :: [Bool] -> Integer -> Integer -> ([(Integer, Integer)], Integer)
  gate_map b x y = case b of
    [] -> ([], 0)
    h : t -> let
      f = gate_map t (x + 1) in
        if h then bimap ((x, y) :) (+ 1) (f (y + 1)) else f y
  init_circ :: Circuit
  init_circ = Circuit 0 [] 0 0 []
  init' :: [t] -> [(t, Bool)]
  init' = (<$>) (, False)
  map_help :: (Circuit -> Val -> Either String (Circuit, Val)) -> Circuit -> [Val] -> Either String (Circuit, [Val])
  map_help f c v = case v of
    [] -> Right (c, [])
    h : t -> f c h >>= \(c', h') -> second (h' :) <$> (map_help f c' t) 
  mes_help :: Integer -> Integer -> [Gate] -> Integer -> [Val] -> (Integer, (Integer, [Gate]))
  mes_help m gc g n x = case x of
    [] -> (n, (gc, g))
    h : t -> case h of
      Qbit_pointer y -> mes_help m (gc + 1) (Mea_g y m n : g) (n + 1) t
      _ -> error("Internal compiler error. Tried to measure something that is not a qbit.")
  offset_val :: Integer -> Integer -> Val -> Val
  offset_val c q v = let
    offset' = (<$>) (offset_val c q) in
      case v of
        Alg_val x y -> Alg_val x (offset' y)
        Arr_val x -> Arr_val (offset' x)
        Creg_pointer x -> Creg_pointer (x + c)
        Qbit_pointer x -> Qbit_pointer (x + q)
        Struct_val x -> Struct_val (offset' x)
        _ -> v
  pure_func :: (Val -> Circuit -> Val -> Either String (Circuit, Val)) -> Circuit -> Val -> Either String (Circuit, Val)
  pure_func f c x = func_val c (f x)
  pure_func' :: (Val -> Val) -> Circuit -> Val -> Either String (Circuit, Val)
  pure_func' f c x = func_val' c (f x)
  qtype :: Type -> Bool
  qtype t = case t of
    Arr u _ -> qtype u
    Qbit -> True
    Struct_type _ u _ _ -> and (qtype <$> u)
    _ -> False
  replicate_circuit :: Circuit -> Integer -> Circuit -> Val -> (Circuit, [Val])
  replicate_circuit(circ @ (Circuit cc c q gc g)) n (circ' @ (Circuit cc' c' q' gc' g')) v =
    if n == 0 then
      (circ, [])
    else
      second
        (offset_val cc q v :)
        (replicate_circuit
          (Circuit (cc + cc') (c' ++ c) (q + q') (gc + gc') ((transf_gate (+ cc) (+ q) <$> g') ++ g))
          (n - 1)
          circ'
          v)
  tag_arr :: Integer -> ([(Integer, Bool)], [Bool]) -> [Val] -> ([(Integer, Bool)], [Bool])
  tag_arr cc t x = case x of
    [] -> t
    y : z -> tag_arr cc (tag_circ cc t y) z
  tag_circ :: Integer -> ([(Integer, Bool)], [Bool]) -> Val -> ([(Integer, Bool)], [Bool])
  tag_circ cc (t @ (c, q)) x = let
    ta = tag_arr cc t in
      case x of
        Alg_val _ y -> ta y
        Arr_val y -> ta y
        Creg_pointer y -> (update_c cc y c, q)
        Qbit_pointer y -> (c, update_q y q)
        Struct_val y -> ta y
        _ -> t
  tag_qbits :: [Gate] -> [Bool] -> Either String ([Gate'], [Bool]) -- TODO: REFACTORISE, REMOVE REPEATED CODE
  tag_qbits g b = case g of
    [] -> Right ([], b)
    h : t -> let
      t' = tag_qbits t in
        case h of
          G' g' -> first (g' :) <$> (case g' of
            Double_g _ x y -> t' (comp_all (update_q <$> [x, y]) b)
            Single_g _ x -> t' (update_q x b)
            Toffoli_g x y z -> t' (comp_all (update_q <$> [x, y, z]) b))
          _ -> Left "Code generation error. Tried to put a non-unitary gate into a subroutine."
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
  transf_val :: (Integer -> Integer) -> (Integer -> Integer) -> Val -> Val
  transf_val c q x = let
    f = (<$>) (transf_val c q) in
      case x of
        Alg_val y z -> Alg_val y (f z)
        Arr_val y -> Arr_val (f y)
        Creg_pointer y -> Creg_pointer (c y)
        Qbit_pointer y -> Qbit_pointer (q y)
        Struct_val y -> Struct_val (f y)
        _ -> x
  type_application :: [(String, Type)] -> [(String, Int_branch)] -> Expression_tree'' -> Expression_tree''
  type_application t u (Expression_tree'' l e ty) = Expression_tree'' l (type_application' t u e) (type_repl t u ty)
  type_application' :: [(String, Type)] -> [(String, Int_branch)] -> Expression_branch'' -> Expression_branch''
  type_application' t u e = case e of
    App'' e1 e2 -> App'' (type_application t u e1) (type_application t u e2)
    Fun'' x e' -> Fun'' x (type_application t u e')
    Lift'' v n -> Lift'' (type_repl t u v) (type_int_repl u n)
    Map'' v w n -> Map'' (type_repl t u v) (type_repl t u w) (type_int_repl u n)
    Name'' x v n -> Name'' x (type_repl t u <$> v) (type_int_repl u <$> n)
    _ -> e
  type_int_repl :: [(String, Int_branch)] -> Int_branch -> Int_branch
  type_int_repl x y = case y of
    Int_constant _ -> y
    Int_variable z -> unsafe_lookup x z "Internal compiler error. Failed to perform integer type variable replacement."
  type_repl :: [(String, Type)] -> [(String, Int_branch)] -> Type -> Type
  type_repl x y z = case z of
    Arr w a -> Arr (type_repl x y w) (type_int_repl y a)
    Function_type'' w a -> Function_type'' (type_repl x y w) (type_repl x y a)
    Typevar w -> unsafe_lookup x w "Internal compiler error. Failed to perform type variable replacement."
    _ -> z
  update_c :: Integer -> Integer -> [(Integer, Bool)] -> [(Integer, Bool)]
  update_c x y = update_c' (x - y - 1)
  update_c' :: Integer -> [(Integer, Bool)] -> [(Integer, Bool)]
  update_c' x y = case y of
    [] -> error("Internal compiler error. Tried to perform relevancy update on a non-existing creg.")
    z @ (w, _) : a -> if x == 0 then (w, True) : a else z : update_c' (x - 1) a
  update_q :: Integer -> [Bool] -> [Bool]
  update_q x y = case y of
    [] -> error("Internal compiler error. Tried to perform relevancy update on a non-existing qbit.")
    z : w -> if x == 0 then True : w else z : update_q (x - 1) w
-----------------------------------------------------------------------------------------------------------------------------