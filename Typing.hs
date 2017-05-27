-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TupleSections #-}
module Typing where
  import Data.Bifunctor
  import Standard
  import Tree
  data Bind = Bind Typevars Type deriving Show
  data Def_interm = Def_interm Integer Integer String [String] [String] Type Expression_tree' deriving Show
  data Def_tree'' = Def_tree'' Location Bind Expression_tree'' deriving Show
  data Expression_branch'' =
    Alg'' String [Expression_tree''] |
    App'' Expression_tree'' Expression_tree'' |
    Cnot'' |
    Field'' Integer |
    Fun'' String Expression_tree'' |
    If_gate'' Type Int_branch |
    Int_expr'' Integer |
    Lift'' Type Int_branch |
    Map'' Type Type Int_branch |
    Match'' Expression_tree'' [Match_case''] |
    Mes'' Int_branch |
    Name'' String [Type] [Int_branch] |
    Single_qbit_def String |
    Str'' [Expression_tree''] |
    Take''
      deriving Show
  data Expression_tree'' = Expression_tree'' Location Expression_branch'' Type deriving Show
  data Int'' = Const_int Integer | Ext_int String | Int_int String deriving Show
  data Location = Code Integer Integer | Language deriving Show
  data Match_case'' = Match_case'' String [String] Expression_tree'' deriving Show
  data Type =
    Arr Type Int_branch |
    Creg Int_branch |
    Function_type'' Type Type |
    Int_type |
    Qbit |
    Struct_type String [Type] [Int_branch] (Maybe [String]) |
    Typevar String
      deriving (Eq, Show)
  data Type' =
    Arr' Type' Int'' |
    Creg' Int'' |
    External String |
    Function_type_3 Type' Type' |
    Int' |
    Qbit' |
    Struct_type' String [Type'] [Int''] (Maybe [String]) |
    Typevar' String
      deriving Show
  data Type_constr =
    Type_constr {
      get_constr ::
        Integer ->
        Integer ->
        [(String, Type_constr)] ->
        [String] ->
        [String] ->
        [Type_tree] ->
        [Int_tree] ->
        Either String Type}
          deriving Show
  data Typevars = Global [String] [String] | Local deriving Show
  add_to_res :: [(String, Location)] -> String -> Integer -> Integer -> Either String [(String, Location)]
  add_to_res r x l c = case r of
    [] -> Right ([(x, Code l c)])
    h @ (y, loc) : t ->
      if x == y then
        Left ("Naming error. " ++ x ++ " defined both" ++ location'' loc ++ " and" ++ location' l c ++ ".")
      else
        (h :) <$> add_to_res t x l c
  bind_help :: Bind -> (([String], [String]), Type')
  bind_help (Bind x y) = case x of
    Global z w -> ((z, w), type' y)
    Local -> (([], []), type'' y)
  build_arr ::
    Integer ->
    Integer ->
    [(String, Type_constr)] ->
    [String] ->
    [String] ->
    [Type_tree] ->
    [Int_tree] ->
    Either String Type
  build_arr _ _ type_con v w [t] [n] = type_transf type_con v w t >>= \t' -> Arr t' <$> transf_int w n
  build_arr l c _ _ _ _ _ = param_err "Arr" l c 1 1
  build_creg ::
    Integer ->
    Integer ->
    [(String, Type_constr)] ->
    [String] ->
    [String] ->
    [Type_tree] ->
    [Int_tree] ->
    Either String Type
  build_creg _ _ _ _ w [] [n] = Creg <$> transf_int w n
  build_creg l c _ _ _ _ _ = param_err "Creg" l c 1 1
  case_num_err :: Integer -> Integer -> Either String t
  case_num_err l c = Left("Matching error" ++ location' l c ++ ". Wrong number of cases.")
  cmp :: Type -> Type' -> Bool
  cmp (Arr t m) (Arr' u n) = cmp t u && cmp_int m n
  cmp (Creg m) (Creg' n) = cmp_int m n
  cmp (Function_type'' t u) (Function_type_3 v w) = cmp t v && cmp u w
  cmp Int_type Int' = True
  cmp Qbit Qbit' = True
  cmp (Typevar x) (External y) = x == y
  cmp _ Typevar'{} = error "Internal compiler error. Free type variable after type application."
  cmp _ _ = False
  cmp_int :: Int_branch -> Int'' -> Bool
  cmp_int (Int_constant m) (Const_int n) = m == n
  cmp_int (Int_variable m) (Ext_int n) = m == n
  cmp_int _ Int_int{} = error "Internal compiler error. Free integer type variable after type application."
  cmp_int _ _ = False
  constr_struct ::
    ([Expression_tree''] -> Expression_branch'') ->
    [(Integer, Type)] ->
    [(Integer, Integer)] ->
    Integer ->
    Integer ->
    Integer ->
    [Type] ->
    Type ->
    Expression_tree''
  constr_struct h i a j l c t t' = case t of
    [] ->
      Expression_tree''
        (Code l c)
        (h
          ((
            \((p, q), (r, s)) -> Expression_tree'' (Code r s) (Name'' (show p) [] []) q) <$>
            zip (reverse i) a))
        t'
    t'' : ts -> let
      f @ (Expression_tree'' z _ ty) = constr_struct h ((j, t'') : i) a (j + 1) l c ts t' in
        Expression_tree'' z (Fun'' (show j) f) (Function_type'' t'' ty)
  create_type_constr ::
    Maybe([String]) ->
    String ->
    [Name_tree] ->
    [Name_tree] ->
    Integer ->
    Integer ->
    [(String, Type_constr)] ->
    [String] ->
    [String] ->
    [Type_tree] ->
    [Int_tree] ->
    Either String Type
  create_type_constr m n t u l c con a b x y = let
    lt = length t
    lu = length u in
      if length x == lt && length y == lu then
        (\(x', y') -> Struct_type n x' y' m) <$> create_type_constr' con a b x y
      else
        param_err n l c (toInteger lt) (toInteger lu)
  create_type_constr' ::
    [(String, Type_constr)] -> [String] -> [String] -> [Type_tree] -> [Int_tree] -> Either String ([Type], [Int_branch])
  create_type_constr' c x y z w = case z of
    [] -> ([], ) <$> transf_ints y w
    h : t -> type_transf c x y h >>= \h' -> first(h' :) <$> create_type_constr' c x y t w
  drepl ::
    [(String, Type_constr)] ->
    Integer ->
    Integer ->
    String ->
    [String] ->
    [String] ->
    [Type_tree] ->
    [Int_tree] ->
    [String] ->
    [String] ->
    Type' ->
    Either String (([Type], [Int_branch]), Type)
  drepl _ l c n _ y [] w [] w' t = first([], ) <$> drepl2 l c n y w w' t
  drepl con l c n x y (v : vs) w (v' : v's) w' t =
    type_transf con x y v >>= \v'' -> first (first (v'' :)) <$> drepl con l c n x y vs w v's w' (repl3 v' (type'' v'') t)
  drepl _ l c n _ _ _ _ _ _ _ = par_num_err l c n
  drepl2 :: Integer -> Integer -> String -> [String] -> [Int_tree] -> [String] -> Type' -> Either String ([Int_branch], Type)
  drepl2 _ _ _ _ [] [] t = Right ([], type_back t)
  drepl2 l c n y (w : ws) (w' : w's) t =
    transf_int y w >>= \w'' -> first(w'' :) <$> drepl2 l c n y ws w's (repl4 w' (int'' w'') t)
  drepl2 l c n _ _ _ _ = ipar_num_err l c n
  dtype ::
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [String] ->
    [String] ->
    Expression_tree' ->
    Either String (Expression_tree'', Type)
  dtype r con b v w (Expression_tree' l c e) =
    (\(e', t) -> (Expression_tree'' (Code l c) e' t, t)) <$> (case e of
      Expression_application' e1 e2 -> dtype r con b v w e1 >>= \(e1', t1) -> case t1 of
        Function_type'' t2 t3 -> (, t3) <$> App'' e1' <$> typecheck r con b v w t2 e2
        _ -> nonf_err l c
      Expression_function' (x, t1) (e', t2) ->
        add_to_res r x l c >>=
        \r' ->
          type_transf con v w t1 >>=
          \t1' ->
            type_transf con v w t2 >>=
            \t2' ->
              (\e'' -> (Fun'' x e'', Function_type'' t1' t2')) <$>
              typecheck r' con ((x, Bind Local t1') : b) v w t2' e'
      Expression_int' x -> Right(Int_expr'' x, Int_type)
      Expression_match'(x @ (Expression_tree' l' c' _)) y -> dtype r con b v w x >>= \(x', t') -> case t' of
        Struct_type _ _ _ (Just s) ->
          dtype_matches l c r con b v w s y >>= \(m, type_arr) -> (Match'' x' m, ) <$> eqls l c type_arr
        _ -> match_type_err l' c'
      Expression_name' x y z -> case lookup x b of
        Just bind -> first (uncurry (Name'' x)) <$> uncurry (uncurry (drepl con l c x v w y z)) (bind_help bind)
        Nothing -> undef_var_err l c x)
  dtype_match ::
    Integer ->
    Integer ->
    [(String, Location)] ->
    [(String, Bind)] ->
    Type ->
    [Name_tree] ->
    Either String ([(String, Location)], [(String, Bind)], [String])
  dtype_match l c r b t x = let
    err = field_num_err l c in case t of
      Function_type'' t1 t2 -> case x of
        [] -> err
        Name_tree l' c' y : tl ->
          add_to_res r y l' c' >>=
          \r' -> (\(r'', b', s) -> (r'', (y, Bind Local t1) : b', y : s)) <$> dtype_match l c r' b t2 tl
      _ -> case x of
        [] -> Right (r, b, [])
        _ -> err
  dtype_matches ::
    Integer ->
    Integer ->
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [String] ->
    [String] ->
    [String] ->
    [Match_tree'] ->
    Either String ([Match_case''], [Type])
  dtype_matches _ _ _ _ _ _ _ [] [] = Right ([], [])
  dtype_matches line col r c b v w f (Match_tree' (Name_tree l' c' y) vars expr : t) =
    rem_from_list f y (wrong_pattern_err l' c') >>=
    \f' ->
      dtype_match l' c' r b (lookup_alg_constr b y) vars >>=
      \(r', b', v') ->
        dtype r' c b' v w expr >>=
        \(exp', tt) -> bimap (Match_case'' y v' exp' :) (tt :) <$> dtype_matches line col r c b v w f' t
  dtype_matches l c _ _ _ _ _ _ _ = case_num_err l c
  eqls :: Integer -> Integer -> [Type] -> Either String Type
  eqls l c x = case x of
    [] -> error "Internal compiler error. Found a matching expression with zero cases."
    y : z -> eqls' l c y z
  eqls' :: Integer -> Integer -> Type -> [Type] -> Either String Type
  eqls' l c x y = case y of
    [] -> Right x
    z : w ->
      if x == z then
        eqls' l c x w
      else
        Left ("Type error" ++ location' l c ++ ". Branches of matching expression have different types.")
  field_num_err :: Integer -> Integer -> Either String t
  field_num_err l c = Left ("Matching error" ++ location' l c ++ ". Wrong number of fields.")
  fun_type :: [Type] -> Type -> Type
  fun_type t u = case t of
    [] -> u
    v : w -> Function_type'' v (fun_type w u)
  get_cases :: [Algebraic_form_tree] -> Maybe [String]
  get_cases x = Just ((\(Algebraic_form_tree _ _ y _) -> y) <$> x)
  init_bind :: [(String, Bind)]
  init_bind = second (\(Def_tree'' _ b _) -> b) <$> init_defs
  init_defs :: [(String, Def_tree'')]
  init_defs =
    (\(x, y, z, w, a) -> (x, Def_tree'' Language (Bind (Global y z) w) (Expression_tree'' Language a w))) <$>
    (
      [
        ("Cnot", [], [], Function_type'' Qbit (Function_type'' Qbit Qbit), Cnot''),
        (
          "If_gate",
          ["U"],
          ["n"],
          Function_type''
            (Creg (Int_variable "n"))
            (Function_type''
              Int_type
              (Function_type'' (Function_type'' (Typevar "U") (Typevar "U")) (Function_type'' (Typevar "U") (Typevar "U")))),
          If_gate'' (Typevar "U") (Int_variable "n")),
        (
          "Lift",
          ["U"],
          ["n"],
          Function_type'' (Typevar "U") (Arr (Typevar "U") (Int_variable "n")),
          Lift'' (Typevar "U") (Int_variable "n")),
        (
          "Map",
          ["U", "V"],
          ["n"],
          Function_type''
            (Function_type'' (Typevar "U") (Typevar "V"))
            (Function_type'' (Arr (Typevar "U") (Int_variable "n")) (Arr (Typevar "V") (Int_variable "n"))),
          Map'' (Typevar "U") (Typevar "V") (Int_variable "n")),
        (
          "Measure",
          [],
          ["n"],
          Function_type'' (Arr Qbit (Int_variable "n")) (Creg (Int_variable "n")),
          Mes'' (Int_variable "n")),
        ("Take", [], [], Qbit, Take'')] ++
      (
        (\(x, y) -> (x, [], [], Function_type'' Qbit Qbit, Single_qbit_def y)) <$>
        [("H", "h"), ("S", "s"), ("S'", "sdg"), ("T", "t"), ("T'", "tdg"), ("X", "x"), ("Y", "y"), ("Z", "z")]))
  init_res :: [(String, Location)]
  init_res = (, Language) <$> (fst <$> types) ++ (fst <$> init_bind)
  int' :: Int_branch -> Int''
  int' (Int_constant n) = Const_int n
  int' (Int_variable n) = Int_int n
  int'' :: Int_branch -> Int''
  int'' (Int_constant n) = Const_int n
  int'' (Int_variable n) = Ext_int n
  int_back :: Int'' -> Int_branch
  int_back (Const_int n) = Int_constant n
  int_back (Ext_int n) = Int_variable n
  int_back (Int_int _) =
    error("Internal compiler error. Free integer type variable after type application when trying to derive a type.")
  ipar_num_err :: Integer -> Integer -> String -> Either String t
  ipar_num_err l c x = Left("Error. Wrong number of integer type parameters for " ++ x ++ location' l c ++ ".")
  location :: Integer -> Integer -> String
  location l c = " " ++ show l ++ ":" ++ show c
  location' :: Integer -> Integer -> String
  location' l c = " at" ++ location l c
  location'' :: Location -> String
  location'' (Code l c) = location' l c
  location'' Language = " in the language"
  lookup_alg_constr :: [(String, Bind)] -> String -> Type
  lookup_alg_constr b x =
    (\(Bind _ t) -> t) (unsafe_lookup b x "Internal compiler error. Failed to find algebraic data type constructor.")
  match_type_err :: Integer -> Integer -> Either String t
  match_type_err l c =
    Left ("Type error" ++ location' l c ++ ". Match over an expression that is not an algebraic data type.")
  mism_err :: Integer -> Integer -> Either String t
  mism_err l c = Left("Type error. Type mismatch" ++ location' l c ++ ".")
  nonf_err :: Integer -> Integer -> Either String t
  nonf_err l c = Left ("Type error" ++ location' l c ++ ". Application of non-functional type.")
  par_num_err :: Integer -> Integer -> String -> Either String t
  par_num_err l c x = Left ("Error. Wrong number of type parameters for " ++ x ++ location' l c ++ ".")
  param_err :: String -> Integer -> Integer -> Integer -> Integer -> Either String t
  param_err x l c v w =
    Left
      ("Error. Type " ++
      x ++
      location' l c ++
      " has a wrong number of type parameters. Expected " ++
      show v ++
      " standard and " ++
      show w ++
      " numeric type parameters.")
  plain_type ::
    (String, Type) ->
    (
      String,
      (
        Integer ->
        Integer ->
        [(String, Type_constr)] ->
        [String] -> 
        [String] ->
        [Type_tree] ->
        [Int_tree] ->
        Either String Type))
  plain_type (x, y) = (x, plain_type' x y)
  plain_type' ::
    String ->
    Type ->
    Integer ->
    Integer ->
    [(String, Type_constr)] ->
    [String] ->
    [String] ->
    [Type_tree] ->
    [Int_tree] ->
    Either String Type
  plain_type' _ x _ _ _ _ _ [] [] = Right x
  plain_type' x _ l c _ _ _ _ _ = param_err x l c 0 0
  rem_from_list :: Eq t => [t] -> t -> String -> Either String [t]
  rem_from_list x y err = case x of
    [] -> Left err
    z : w -> if z == y then Right w else (z :) <$> rem_from_list w y err
  repl ::
    [(String, Type_constr)] ->
    Integer ->
    Integer -> String ->
    [String] ->
    [String] ->
    [Type_tree] ->
    [Int_tree] ->
    Type ->
    [String] ->
    [String] ->
    Type' ->
    Either String ([Type], [Int_branch])
  repl _ l c n _ y [] w t [] w' t' = ([], ) <$> repl2 l c n y w t w' t'
  repl con l c n x y (v : vs) w t (v' : v's) w' t' =
    type_transf con x y v >>=
    \v'' -> first(v'' :) <$> repl con l c n x y vs w t v's w' (repl3 v' (type'' v'') t')
  repl _ l c n _ _ _ _ _ _ _ _ = par_num_err l c n
  repl2 ::
    Integer -> Integer -> String -> [String] -> [Int_tree] -> Type -> [String] -> Type' -> Either String [Int_branch]
  repl2 l c _ _ [] t [] t' = if cmp t t' then Right [] else mism_err l c
  repl2 l c n y (w : ws) t (w' : w's) t' =
    transf_int y w >>= \w'' -> (w'' :) <$> repl2 l c n y ws t w's (repl4 w' (int'' w'') t')
  repl2 l c n _ _ _ _ _ = ipar_num_err l c n
  repl3 :: String -> Type' -> Type' -> Type'
  repl3 x t u = let
    f = repl3 x t in
      case u of
        Arr' v n -> Arr' (f v) n
        Function_type_3 v w -> Function_type_3 (f v) (f w)
        Struct_type' y v n a -> Struct_type' y (f <$> v) n a
        Typevar' y -> if y == x then t else u
        _ -> u
  repl4 :: String -> Int'' -> Type' -> Type'
  repl4 x n t = let
    f = repl4 x n
    g = repl5 x n in
      case t of
        Arr' u m -> Arr' (f u) (g m)
        Creg' m -> Creg' (g m)
        Function_type_3 u v -> Function_type_3 (f u) (f v)
        Struct_type' y u m a -> Struct_type' y (f <$> u) (g <$> m) a
        _ -> t
  repl5 :: String -> Int'' -> Int'' -> Int''
  repl5 x y (z @ (Int_int w)) = if w == x then y else z
  repl5 _ _ z = z
  transf_int :: [String] -> Int_tree -> Either String Int_branch
  transf_int x (Int_tree l c y) = let
    r = Right y in
      case y of
        Int_constant{} -> r
        Int_variable z ->
          if elem z x then r else Left ("Typing error. Unknown integer type variable " ++ z ++ location' l c ++ ".")
  transf_ints :: [String] -> [Int_tree] -> Either String [Int_branch]
  transf_ints x y = case y of
    [] -> Right []
    z : w -> transf_int x z >>= \a -> (a :) <$> transf_ints x w
  type' :: Type -> Type'
  type' (Arr x y) = Arr' (type' x) (int' y)
  type' (Creg n) = Creg' (int' n)
  type' (Function_type'' x y) = Function_type_3 (type' x) (type' y)
  type' Int_type = Int'
  type' Qbit = Qbit'
  type' (Struct_type x y z w) = Struct_type' x (type' <$> y) (int' <$> z) w
  type' (Typevar x) = Typevar' x
  type'' :: Type -> Type'
  type'' (Arr x y) = Arr' (type'' x) (int'' y)
  type'' (Creg n) = Creg' (int'' n)
  type'' (Function_type'' x y) = Function_type_3 (type'' x) (type'' y)
  type'' Int_type = Int'
  type'' Qbit = Qbit'
  type'' (Struct_type x y z w) = Struct_type' x (type'' <$> y) (int'' <$> z) w
  type'' (Typevar x) = External x
  type_alg ::
    [(String, Location)] ->
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [(String, Def_tree'')] ->
    [String] ->
    [String] ->
    Type ->
    [Algebraic_form_tree] ->
    Either String ([(String, Location)], [(String, Bind)], [(String, Def_tree'')])
  type_alg glob loc c b d t u newt a = case a of
    [] -> Right (glob, b, d)
    Algebraic_form_tree line col n h : tl ->
      add_to_res loc n line col >>= \loc' -> type_alg_fields c 0 newt t u h >>= \t' -> let
        b' = Bind (Global t u) ft
        ft = fun_type t' newt in
          type_alg
            ((n, Code line col) : glob)
            loc'
            c
            ((n, b') : b)
            (
              (
                n,
                Def_tree''
                  (Code line col)
                  b'
                  (constr_struct (Alg'' n) [] ((\(Type_tree ll cc _) -> (ll, cc)) <$> h) 0 line col t' newt)) :
              d)
            t
            u
            newt
            tl
  type_alg_fields ::
    [(String, Type_constr)] ->
    Integer ->
    Type ->
    [String] ->
    [String] ->
    [Type_tree] ->
    Either String [Type]
  type_alg_fields c i st v w a = case a of
    [] -> Right []
    h : t -> type_transf c v w h >>= \ty -> (ty :) <$> type_alg_fields c (i + 1) st v w t
  type_back :: Type' -> Type
  type_back (Arr' t m) = Arr (type_back t) (int_back m)
  type_back (Creg' n) = Creg (int_back n)
  type_back (Function_type_3 t u) = Function_type'' (type_back t) (type_back u)
  type_back Int' = Int_type
  type_back Qbit' = Qbit
  type_back (External x) = Typevar x
  type_back (Struct_type' x y z w) = Struct_type x (type_back <$> y) (int_back <$> z) w
  type_back Typevar'{} =
    error("Internal compiler error. Free type variable after type application when trying to derive type.")
  type_def_1 :: [(String, Location)] -> Def_tree' -> Either String ([(String, Location)])
  type_def_1 r (Def_tree' (Decl_tree l c x _ _) _ _) = add_to_res r x l c
  type_def_2 :: [(String, Location)] -> [(String, Type_constr)] -> Def_tree' -> Either String ((String, Bind), Def_interm)
  type_def_2 r con (Def_tree' (Decl_tree l c x v w) t expr) =
    typevars r v w >>=
    \(_, v', w') ->
      (\t' -> ((x, Bind (Global v' w') t'), Def_interm l c x v' w' t' expr)) <$> type_transf con v' w' t
  type_def_3 ::
    [(String, Location)] -> [(String, Type_constr)] -> [(String, Bind)] -> Def_interm -> Either String (String, Def_tree'')
  type_def_3 r con b (Def_interm l c x v w t expr) =
    (x, ) <$> Def_tree'' (Code l c) (Bind (Global v w) t) <$> typecheck r con b v w t expr
  type_defs_1 :: [(String, Location)] -> [Def_tree'] -> Either String ([(String, Location)])
  type_defs_1 r [] = Right r
  type_defs_1 r (h : t) = type_def_1 r h >>= \r' -> type_defs_1 r' t
  type_defs_2 ::
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [Def_tree'] ->
    Either String ([(String, Bind)], [Def_interm])
  type_defs_2 r con b d = case d of
    [] -> Right (b, [])
    h : t -> type_def_2 r con h >>= \(b', i) -> second (i :) <$> type_defs_2 r con (b' : b) t
  type_defs_3 ::
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [(String, Def_tree'')] ->
    [Def_interm] ->
    Either String ([(String, Def_tree'')])
  type_defs_3 r con c d x = case x of
    [] -> Right d
    h : t -> type_def_3 r con c h >>= \y -> (y :) <$> type_defs_3 r con c d t
  type_expr ::
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    Expression_tree' ->
    Either String Expression_tree''
  type_expr r con c x = fst <$> dtype r con c [] [] x
  type_field ::
    [(String, Location)] ->
    [(String, Location)] ->
    [(String, Type_constr)] ->
    Integer ->
    Type ->
    [String] ->
    [String] ->
    Argument_tree ->
    Either String ([(String, Location)], [(String, Location)], (String, Bind), (String, Def_tree''), Type)
  type_field glob loc c i st v w (Argument_tree line col x t) =
    add_to_res loc x line col >>= \loc' -> type_transf c v w t >>= \t' -> let
      b = Bind (Global v w) (Function_type'' st t')
      lc = Code line col in
        Right ((x, Code line col) : glob, loc', (x, b), (x, Def_tree'' lc b (Expression_tree'' lc (Field'' i) t')), t')
  type_fields ::
    [(String, Location)] ->
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [(String, Def_tree'')] ->
    Integer ->
    Type ->
    [String] ->
    [String] ->
    [Argument_tree] ->
    Either String ([(String, Location)], [(String, Location)], [(String, Bind)], [(String, Def_tree'')], [Type])
  type_fields glob loc c b d i st v w a = case a of
    [] -> Right (glob, loc, b, d, [])
    h : t ->
      type_field glob loc c i st v w h >>=
      \(glob', loc', b', d', ty) ->
        (\(x1, x2, x3, x4, x5) -> (x1, x2, x3, x4, ty : x5)) <$>
        type_fields glob' loc' c (b' : b) (d' : d) (i + 1) st v w t
  type_struct_1 ::
    [(String, Location)] ->
    [(String, Type_constr)] ->
    Data_tree ->
    Either String ([(String, Location)], [(String, Type_constr)])
  type_struct_1 r c (Data_tree (Decl_tree line col x t u) f) = (, (x, Type_constr (create_type_constr (case f of
    Algebraic_tree f' -> get_cases f'
    _ -> Nothing) x t u)) : c) <$> add_to_res r x line col
  type_struct_2 ::
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [(String, Def_tree'')] ->
    Data_tree ->
    Either String ([(String, Location)], [(String, Bind)], [(String, Def_tree'')])
  type_struct_2 r c b d (Data_tree (Decl_tree line col n t u) x) = typevars r t u >>= \(r', t', u') -> let
    newt = Struct_type n (Typevar <$> t') (Int_variable <$> u') in case x of
        Algebraic_tree f -> type_alg r r' c b d t' u' (newt (get_cases f)) f
        Struct_tree f -> let newt' = newt(Nothing) in
          (\(r'', _, b', d', t'') -> let
            b'' = Bind (Global t' u') ft
            ft = fun_type t'' newt' in
              (
                r'',
                (n, b'') : b',
                  (
                    n,
                    Def_tree''
                      (Code line col)
                      b''
                      (constr_struct Str'' [] ((\(Argument_tree ll cc _ _) -> (ll, cc)) <$> f) 0 line col t'' newt')) :
                  d')) <$>
          type_fields r r' c b d 0 newt' t' u' f
  type_structs_1 ::
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [Data_tree] ->
    Either String ([(String, Location)], [(String, Type_constr)])
  type_structs_1 r c s = case s of
    [] -> Right (r, c)
    h : t -> type_struct_1 r c h >>= \(r', c') -> type_structs_1 r' c' t
  type_structs_2 ::
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [(String, Def_tree'')] ->
    [Data_tree] ->
    Either String ([(String, Location)], [(String, Bind)], [(String, Def_tree'')])
  type_structs_2 r c b d s = case s of
    [] -> Right (r, b, d)
    h : tl -> type_struct_2 r c b d h >>= \(r', b', d') -> type_structs_2 r' c b' d' tl
  type_transf :: [(String, Type_constr)] -> [String] -> [String] -> Type_tree -> Either String Type
  type_transf type_con v w (Type_tree l c t) = case t of
    Basic_type x y z -> case lookup x type_con of
      Nothing ->
        if elem x v then
          if y == [] && z == [] then
            Right (Typevar x)
          else
            Left ("Error. Type variable " ++ x ++ location' l c ++ "has type parameters.")
        else
          Left ("Error. Unknown type " ++ x ++ location' l c ++ ".")
      Just f -> get_constr f l c type_con v w y z
    Function_type x y -> type_transf type_con v w x >>= \x' -> Function_type'' x' <$> type_transf type_con v w y
  typecheck ::
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [String] ->
    [String] ->
    Type ->
    Expression_tree' ->
    Either String Expression_tree''
  typecheck r con b v w t (Expression_tree' l c e) = flip (Expression_tree'' (Code l c)) t <$> (case e of
    Expression_application' e1 e2 -> dtype r con b v w e1 >>= \(e1', t1) -> case t1 of
      Function_type'' t2 t3 ->
        if t3 == t then
          App'' e1' <$> typecheck r con b v w t2 e2
        else
          Left ("Typing error" ++ location' l c ++ ". Function result type does not match the expected result type.")
      _ -> nonf_err l c
    Expression_function' (x, t1) (e', t2) ->
      add_to_res r x l c >>=
      \r' ->
        type_transf con v w t1 >>=
        \t1' ->
          type_transf con v w t2 >>=
          \t2' ->
            if Function_type'' t1' t2' == t then
              Fun'' x <$> typecheck r' con ((x, Bind Local t1') : b) v w t2' e'
            else
              mism_err l c
    Expression_int' x -> if t == Int_type then Right (Int_expr'' x) else mism_err l c
    Expression_match' (x @ (Expression_tree' l' c' _)) y -> dtype r con b v w x >>= \(x', t') -> case t' of
      Struct_type _ _ _ (Just s) -> Match'' x' <$> typecheck_matches l c r con b v w t s y
      _ -> match_type_err l' c'
    Expression_name' x y z -> case lookup x b of
      Just bind -> uncurry (Name'' x) <$> uncurry (uncurry (repl con l c x v w y z t)) (bind_help bind)
      Nothing -> undef_var_err l c x)
  typecheck_matches ::
    Integer ->
    Integer ->
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [String] ->
    [String] ->
    Type ->
    [String] ->
    [Match_tree'] ->
    Either String [Match_case'']
  typecheck_matches _ _ _ _ _ _ _ _ [] [] = Right []
  typecheck_matches line col r c b v w ty f (Match_tree' (Name_tree l' c' y) vars expr : t) =
    rem_from_list f y (wrong_pattern_err l' c') >>=
    \f' ->
      dtype_match l' c' r b (lookup_alg_constr b y) vars >>=
      \(r', b', v') ->
        typecheck r' c b' v w ty expr >>=
        \exp' -> (Match_case'' y v' exp' :) <$> typecheck_matches line col r c b v w ty f' t
  typecheck_matches l c _ _ _ _ _ _ _ _ = case_num_err l c
  types :: [(String, Type_constr)]
  types =
    second(Type_constr) <$>
    ([("Arr", build_arr), ("Creg", build_creg)] ++ (plain_type <$> [("Int", Int_type), ("Qbit", Qbit)]))
  typevars :: [(String, Location)] -> [Name_tree] -> [Name_tree] -> Either String ([(String, Location)], [String], [String])
  typevars r x y = vars_to_res r x >>= \(r', x') -> (\(r'', y') -> (r'', x', y')) <$> vars_to_res r' y
  typing ::
    [(String, Location)] ->
    [(String, Type_constr)] ->
    [(String, Bind)] ->
    [(String, Def_tree'')] ->
    Tree' ->
    Either String ([(String, Location)], [(String, Type_constr)], [(String, Bind)], [(String, Def_tree'')])
  typing r c b d (Tree' s x) =
    type_structs_1 r c s >>=
    \(r', c') ->
      type_structs_2 r' c' b d s >>=
      \(r'', b', d') ->
        type_defs_1 r'' x >>=
        \r3 -> type_defs_2 r3 c' b' x >>= \(b'', y) -> (r3, c', b'', ) <$> type_defs_3 r3 c' b'' d' y
  undef_var_err :: Integer -> Integer -> String -> Either String t
  undef_var_err l c x = Left ("Error. Undefined variable " ++ x ++ location' l c ++ ".")
  unsafe_lookup :: Eq t => [(t, u)] -> t -> String -> u
  unsafe_lookup x y e = case lookup y x of
    Just z -> z
    Nothing -> error e
  var_to_res :: [(String, Location)] -> Name_tree -> Either String ([(String, Location)], String)
  var_to_res r (Name_tree l c x) = (, x) <$> add_to_res r x l c
  vars_to_res :: [(String, Location)] -> [Name_tree] -> Either String ([(String, Location)], [String])
  vars_to_res r [] = Right (r, [])
  vars_to_res r (h : t) = var_to_res r h >>= \(r', h') -> second (h' :) <$> vars_to_res r' t
  wrong_pattern_err :: Integer -> Integer -> String
  wrong_pattern_err l c =
    "Matching error" ++
    location' l c ++
    ". Pattern name is not applicable to this algebraic data type or has already been matched."
-----------------------------------------------------------------------------------------------------------------------------