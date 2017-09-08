-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
module Typing where
  import Data.Bifunctor
  import Data.Map
  import Naming
  import Tokenise
  import Tree
  type Algebraics = Map' (([(String, Kind)], Map' [Type_1], Type_1), Status) -- TODO: REM STRINGS FROM FST MAP
  type Constrs = Map' (String, Status)
  data Def_4 = Basic_def_4 Location_0 String [(String, Kind)] Kinds Type_1 Expression_1 deriving Show
  type Defs = Map' Expression_2
  data Expression_2 =
    Add_Finite_expression_2 Integer |
    Add_Int_expression_2 |
    Algebraic_expression_2 String [Expression_2] |
    Application_expression_2 Expression_2 Expression_2 |
    Array_expression_2 Integer [Expression_2] |
    Convert_Finite_expression_2 Integer |
    Crash_expression_2 |
    Equal_Finite_expression_2 |
    Equal_Int_expression_2 |
    Field_expression_2 String |
    Finite_expression_2 Integer |
    Function_expression_2 Pattern_0 Expression_2 |
    Gate_1_expression_2 String |
    Int_expression_2 Integer |
    Inverse_Finite_expression_2 Integer |
    Lift_Array_expression_2 |
    Match_expression_2 Expression_2 Matches |
    Multiply_Finite_expression_2 Integer |
    Multiply_Int_expression_2 |
    Name_expression_2 String |
    Struct_expression_2 (Map' Expression_2) |
    Take_expression_2
      deriving Show
  data File = File Kinds Algebraics Constrs Types deriving Show
  data Form_2 = Form_2 String [Type_1] deriving Show
  type Kinds = Map' (Kind, Status)
  data Match = Match [Pattern_0] Expression_2 deriving Show
  type Matches = Map' Match
  data Status' = Fixed | Flexible deriving Show
  data Type_1 = Application_type_1 Type_1 Type_1 | Int_type_1 Integer | Name_type_1 String deriving (Eq, Show)
  data Type_1' = Basic_type_1 [(String, Kind)] Type_1 | Local_type_1 Type_1 deriving Show
  type Types = Map' (Type_1', Status)
  algebraics :: Map' ([(String, Kind)], Map' [Type_1], Type_1)
  algebraics =
    fromList
      [
        ("Logical", ([], fromList [("False", []), ("True", [])], Name_type_1 "Logical")),
        (
          "Maybe",
          (
            [("U", Star_kind)],
            fromList [("Nothing", []), ("Wrap", [Name_type_1 "U"])],
            Application_type_1 (Name_type_1 "Maybe") (Name_type_1 "U")))]
  check_kind :: String -> String -> Map' ((Kind, Status), Status') -> Type_1 -> Err Kind
  check_kind j c a b = case b of
    Application_type_1 d e -> check_kind j c a d >>= \f -> case f of
      Arrow_kind g h -> check_kind j c a e >>= \i -> if i == g then Right h else Left j
      _ -> Left j
    Name_type_1 d -> if d == c then Left j else Right (fst (fst (unsafe_lookup d a)))
    _ -> Right Hash_kind
  constrs :: Map' String
  constrs = fromList [("False", "Logical"), ("Nothing", "Maybe"), ("True", "Logical"), ("Wrap", "Maybe")]
  defs :: Map' Expression_2
  defs =
    fromList
      [
        ("Add_Int", Add_Int_expression_2),
        ("Crash", Crash_expression_2),
        ("Equal_Int", Equal_Int_expression_2),
        ("False", Algebraic_expression_2 "False" []),
        ("H", Gate_1_expression_2 "h"),
        ("Multiply_Int", Multiply_Int_expression_2),
        ("Nothing", Algebraic_expression_2 "Nothing" []),
        ("S", Gate_1_expression_2 "s"),
        ("S'", Gate_1_expression_2 "sdg"),
        ("T", Gate_1_expression_2 "t"),
        ("T'", Gate_1_expression_2 "tdg"),
        ("Take", Take_expression_2),
        ("True", Algebraic_expression_2 "True" []),
        ("Wrap", Function_expression_2 (Name_pattern "x") (Algebraic_expression_2 "Wrap" [Name_expression_2 "x"])),
        ("X", Gate_1_expression_2 "x"),
        ("Y", Gate_1_expression_2 "y"),
        ("Z", Gate_1_expression_2 "z")]
  finite_type :: Type_1
  finite_type = Application_type_1 (Name_type_1 "Finite") (Name_type_1 "N")
  function_type :: Type_1 -> Type_1 -> Type_1
  function_type = Application_type_1 <$> Application_type_1 (Name_type_1 "Function")
  gate_type_1 :: Type_1'
  gate_type_1 = Basic_type_1 [] (function_type (Name_type_1 "Qbit") (Name_type_1 "Qbit"))
  ice :: t
  ice = error "Internal compiler error."
  init_type_context :: File
  init_type_context = File (old kinds) (old algebraics) (old constrs) (old types)
  ins_new :: String -> t -> Map' (t, Status) -> Map' (t, Status)
  ins_new a b = insert a (b, New)
  int_type :: Type_1
  int_type = Name_type_1 "Int"
  kinds :: Map' Kind
  kinds =
    Data.Map.fromList
      [
        ("Array", Arrow_kind Star_kind Star_kind),
        ("Finite", Arrow_kind Hash_kind Star_kind),
        ("Function", Arrow_kind Star_kind (Arrow_kind Star_kind Star_kind)),
        ("Int", Star_kind),
        ("Logical", Star_kind),
        ("Maybe", Arrow_kind Star_kind Star_kind),
        ("Qbit", Star_kind)]
  repl :: Map' String -> Type_1 -> Type_1
  repl a b = case b of
    Application_type_1 c d -> Application_type_1 (repl a c) (repl a d)
    Name_type_1 c -> Name_type_1 (case Data.Map.lookup c a of
      Just d -> d
      Nothing -> c)
    _ -> b
  solvesys :: String -> Map' ((Kind, Status), Status') -> [(Type_1, Type_1)] -> Err ()
  solvesys m a b = case b of
    [] -> Right ()
    (c, d) : g -> case c of
      Application_type_1 e f -> case d of
        Application_type_1 h i -> solvesys m a ((e, h) : (f, i) : g)
        Name_type_1 h -> solvesys' m a h c g
        _ -> Left m
      Int_type_1 e -> case d of
        Int_type_1 f -> if e == f then solvesys m a g else Left m
        Name_type_1 f -> solvesys' m a f c g
        _ -> Left m
      Name_type_1 e -> case d of
        Name_type_1 f ->
          let
            ((h, _), j) = unsafe_lookup e a
            ((k, _), l) = unsafe_lookup f a
          in if h == k then case j of
            Fixed -> case l of
              Fixed -> if e == f then solvesys m a g else Left m
              Flexible -> solvesys m a (sysrep f c g)
            Flexible -> solvesys m a (sysrep e d g) else Left m
        _ -> solvesys' m a e d g
  solvesys' :: String -> Map' ((Kind, Status), Status') -> String -> Type_1 -> [(Type_1, Type_1)] -> Err ()
  solvesys' h a b c d =
    let
      ((e, _), f) = unsafe_lookup b a
    in case f of
      Fixed -> Left h
      Flexible -> check_kind h b a c >>= \g -> if g == e then solvesys h a (sysrep b c d) else Left h
  sysrep :: String -> Type_1 -> [(Type_1, Type_1)] -> [(Type_1, Type_1)]
  sysrep a b =
    let
      c = sysrep' a b
    in
      (<$>) (bimap c c)
  sysrep' :: String -> Type_1 -> Type_1 -> Type_1
  sysrep' a b c =
    let
      f = sysrep' a b
    in
      case c of
        Application_type_1 d e -> Application_type_1 (f d) (f e)
        Name_type_1 d -> if d == a then b else c
        _ -> c
  type_case ::
    Type_1 ->
    Algebraics ->
    Constrs ->
    Types ->
    (Location_0 -> Location_1) ->
    String ->
    Map' String ->
    Map' [Type_1] ->
    Match_1 ->
    (Matches, Integer, Integer, [(Type_1, Type_1)], Map' ((Kind, Status), Status')) ->
    Err (Matches, Integer, Integer, [(Type_1, Type_1)], Map' ((Kind, Status), Status'))
  type_case y q r k i j a b (Match_1 (m @ (Name d e)) g h) (c, o, p, l, x) = case Data.Map.lookup e b of
    Just f ->
      (
        type_case' i m a g f k >>=
        \n -> (\(s, t, u, v, w) -> (insert e (Match g s) c, v, w, u, t)) <$> type_expression q r i o p x l n h y)
    Nothing -> Left ("Undefined constructor " ++ e ++ " for algebraic data type " ++ j ++ location' (i d))
  type_case' :: (Location_0 -> Location_1) -> Name -> Map' String -> [Pattern_0] -> [Type_1] -> Types -> Err Types
  type_case' j (m @ (Name k l)) a b c d = case b of
    [] -> Right d
    e : f -> case c of
      [] -> Left ("Constructor " ++ l ++ location (j k) ++ " has too many fields.")
      g : h -> type_case' j m a f h (case e of
        Blank_pattern -> d
        Name_pattern i -> ins_new i (Local_type_1 (repl a g)) d)
  type_cases ::
    Type_1 ->
    Algebraics ->
    Constrs ->
    Types ->
    (Location_0 -> Location_1) ->
    String ->
    Map' String ->
    Map' [Type_1] ->
    [Match_1] ->
    (Matches, Integer, Integer, [(Type_1, Type_1)], Map' ((Kind, Status), Status')) ->
    Err (Matches, Integer, Integer, [(Type_1, Type_1)], Map' ((Kind, Status), Status'))
  type_cases n k l j i h a b d c = case d of
    [] -> Right c
    e : f -> type_case n k l j i h a b e c >>= type_cases n k l j i h a b f
  type_data_1 :: Data_2 -> (Kinds, Constrs, Defs) -> (Kinds, Constrs, Defs)
  type_data_1 (Data_2 a b c) (i, j, k) =
    let
      (l, m) = case c of
        Algebraic_data_1 e ->
          (
            Prelude.foldl (\d -> \(Form_1 n _) -> ins_new n a d) j e,
            Prelude.foldl
              (\f -> \(Form_1 g h) ->
                let
                  h' = show <$> [0 .. length h]
                in
                  insert
                    g
                    (Prelude.foldr
                      Function_expression_2
                      (Algebraic_expression_2 g (Name_expression_2 <$> h'))
                      (Name_pattern <$> h'))
                    f)
              k
              e)
        Struct_data_1 e ->
          let
            e' = fst <$> e
          in
            (
              j,
              Prelude.foldl
                (flip (\g -> insert g (Field_expression_2 g)))
                (insert
                  a
                  (Prelude.foldr
                    (\f -> Function_expression_2 (Name_pattern ('!' : f)))
                    (Struct_expression_2 (fromList ((\f -> (f, Name_expression_2 ('!' : f))) <$> e')))
                    e')
                  k)
                e')
    in
      (ins_new a (Prelude.foldr (Arrow_kind <$> snd) Star_kind b) i, l, m)
  type_data_2 :: (Location_0 -> Location_1) -> Data_2 -> Kinds -> (Algebraics, Types) -> Err (Algebraics, Types)
  type_data_2 f (Data_2 a b c) d (p, e) =
    let
      g = type_kinds b d
      x = Prelude.foldl (\n -> Application_type_1 n <$> Name_type_1) (Name_type_1 a) (fst <$> b)
    in case c of
      Algebraic_data_1 h ->
        (
          (\q ->
            (
              ins_new a (b, fromList ((\(Form_2 r s) -> (r, s)) <$> q), x) p,
              Prelude.foldl (flip (\(Form_2 l m) -> ins_new l (Basic_type_1 b (Prelude.foldr function_type x m)))) e q)) <$>
          type_forms f h g)
      Struct_data_1 h ->
        (
          (\i ->
            (
              p,
              Prelude.foldl
                (flip (\(k, l) -> ins_new k (Basic_type_1 b (function_type x l))))
                (ins_new a (Basic_type_1 b (Prelude.foldr (function_type <$> snd) x i)) e)
                i)) <$>
          type_fields f h g)
  type_datas :: (Location_0 -> Location_1) -> [Data_2] -> (File, Defs) -> Err (File, Defs)
  type_datas h a (File b i j d, c) =
    let
      (e, k, f) = type_datas_1 a (b, j, c)
    in (\(l, g) -> (File e l k g, f)) <$> type_datas_2 h a e (i, d)
  type_datas_1 :: [Data_2] -> (Kinds, Constrs, Defs) -> (Kinds, Constrs, Defs)
  type_datas_1 = flip (Prelude.foldl (flip type_data_1))
  type_datas_2 :: (Location_0 -> Location_1) -> [Data_2] -> Kinds -> (Algebraics, Types) -> Err (Algebraics, Types)
  type_datas_2 f a b c = case a of
    [] -> Right c
    d : e -> type_data_2 f d b c >>= type_datas_2 f e b
  type_def_1 :: (Location_0 -> Location_1) -> Def_2 -> Kinds -> Types -> Err (Def_4, Types)
  type_def_1 l a b c = case a of
    Basic_def_2 f d e g i ->
      let
        j = type_kinds e b
      in
        (\h -> (Basic_def_4 f d e j h i, ins_new d (Basic_type_1 e h) c)) <$> type_type l g j Star_kind
  type_def_2 :: (Location_0 -> Location_1) -> Def_4 -> (Algebraics, Constrs, Types) -> Defs -> Err Defs
  type_def_2 j a (d, l, k) c = case a of
    Basic_def_4 r e _ b h i ->
      flip (insert e) c <$> type_expr ("in function " ++ e ++ location' (j r)) h j ((\g -> (g, Fixed)) <$> b, d, l, k) i
  type_defs ::
    (Location_0 -> Location_1) -> [Def_2] -> (Kinds, Algebraics, Constrs) -> (Defs, Types) -> Err (Defs, Types)
  type_defs h a (b, i, j) (c, d) = type_defs_1 h a b d >>= \(g, e) -> (\f -> (f, e)) <$> type_defs_2 h g (i, j, e) c
  type_defs_1 :: (Location_0 -> Location_1) -> [Def_2] -> Kinds -> Types -> Err ([Def_4], Types)
  type_defs_1 h a b c = case a of
    [] -> Right ([], c)
    d : e -> type_def_1 h d b c >>= \(f, g) -> first ((:) f) <$> type_defs_1 h e b g
  type_defs_2 :: (Location_0 -> Location_1) -> [Def_4] -> (Algebraics, Constrs, Types) -> Defs -> Err Defs
  type_defs_2 f a b c = case a of
    [] -> Right c
    d : e -> type_def_2 f d b c >>= type_defs_2 f e b
  type_error :: Location_1 -> Err t
  type_error a = Left ("Type error" ++ location' a)
  type_expr ::
    String ->
    Type_1 ->
    (Location_0 -> Location_1) ->
    (Map' ((Kind, Status), Status'), Algebraics, Constrs, Types) ->
    Expression_1 ->
    Err Expression_2
  type_expr k h a (b, c, d, e) f =
    type_expression c d a 0 0 b [] e f h >>= \(g, i, j, _, _) -> g <$ solvesys ("Type error " ++ k) i j
  type_expr' :: (Location_0 -> Location_1) -> (Kinds, Algebraics, Constrs, Types) -> Expression_1 -> Err Expression_2
  type_expr' a (b, c, d, e) =
    type_expr
      "in expression."
      (Name_type_1 "!")
      a
      (insert "!" ((Star_kind, New), Flexible) ((\g -> (g, Fixed)) <$> b), c, d, e)
  type_expression ::
    Algebraics ->
    Constrs ->
    (Location_0 -> Location_1) ->
    Integer ->
    Integer ->
    Map' ((Kind, Status), Status') ->
    [(Type_1, Type_1)] ->
    Types ->
    Expression_1 ->
    Type_1 ->
    Err (Expression_2, Map' ((Kind, Status), Status'), [(Type_1, Type_1)], Integer, Integer)
  type_expression v w r o s f h d (Expression_1 a b) e = case b of
    Application_expression_1 c g ->
      (
        type_expression
          v
          w
          r
          (o + 1)
          s
          (insert (show o) ((Star_kind, New), Flexible) f)
          h
          d
          c
          (function_type (Name_type_1 (show o)) e) >>=
        \(i, j, k, p, t) ->
          (
            (\(l, m, n, q, u) -> (Application_expression_2 i l, m, n, q, u)) <$>
            type_expression v w r p t j k d g (Name_type_1 (show o))))
    Finite_expression_1 c g ->
      if c > - 1 && c < g then
        Right (Finite_expression_2 c, f, (e, Int_type_1 g) : h, o, s)
      else
        Left ("Invalid Finite" ++ location' (r a))
    Function_expression_1 c g ->
      (
        (\(a', b', c', d', e') -> (Function_expression_2 c a', b', c', d', e')) <$>
        type_expression
          v
          w
          r
          (o + 2)
          s
          (insert (show (o + 1)) ((Star_kind, New), Flexible) (insert (show o) ((Star_kind, New), Flexible) f))
          ((e, function_type (Name_type_1 (show o)) (Name_type_1 (show (o + 1)))) : h)
          (case c of
            Blank_pattern -> d
            Name_pattern i -> ins_new i (Local_type_1 (Name_type_1 (show o))) d)
          g
          (Name_type_1 (show (o + 1))))
    Int_expression_1 c -> Right (Int_expression_2 c, f, (e, int_type) : h, o, s)
    Match_expression_1 c g -> case g of
      [] -> ice
      Match_1 (Name i0 i) _ _ : _ -> case Data.Map.lookup i w of
        Just (x, _) ->
          let
            (y, z, a1) = fst (unsafe_lookup x v)
            (b1, b2) = typevars (flip (++) (show s)) y (empty, f)
          in (
            type_expression v w r o (s + 1) b2 h d c (repl b1 a1) >>=
            \(a0, b0, c0, d0, e0) ->
              (
                (\(f0, g0, h0, i', j') -> (Match_expression_2 a0 f0, j', i', g0, h0)) <$>
                type_cases e v w d r x b1 z g (empty, d0, e0, c0, b0)))
        Nothing -> Left ("Undefined algebraic constructor " ++ i ++ location' (r i0))
    Name_expression_1 c -> case Data.Map.lookup c d of
      Just (g, _) ->
        let
          (k, l, m) = case g of
            Basic_type_1 i j ->
{-
INEFFICIENCY.
ONE COULD CONSTRUCT AN IDENTITY MAP AND PUT IT INTO BASIC_TYPE AND THEN MAP (++ SUFFIX) OVER IT
OR SUFFIX COULD BE GIVEN AS ARGUMENT TO REPL AND ADDED INSIDE REPL
-}
              let
                (n, p) = type_kinds'' i s f
              in
                (n, repl p j, s + 1)
            Local_type_1 i -> (f, i, s)
        in
          Right (Name_expression_2 c, k, (e, l) : h, o, m)
      Nothing -> Left ("Undefined variable " ++ c ++ location' (r a))
  type_field :: (Location_0 -> Location_1) -> (String, Type_0) -> Kinds -> Err (String, Type_1)
  type_field d (a, b) c = (,) a <$> type_type d b c Star_kind
  type_fields :: (Location_0 -> Location_1) -> [(String, Type_0)] -> Kinds -> Err [(String, Type_1)]
  type_fields f a b = case a of
    [] -> Right []
    c : d -> type_field f c b >>= \e -> (:) e <$> type_fields f d b
  type_form :: (Location_0 -> Location_1) -> Form_1 -> Kinds -> Err Form_2
  type_form d (Form_1 a b) c = Form_2 a <$> type_types d b c
  type_forms :: (Location_0 -> Location_1) -> [Form_1] -> Kinds -> Err [Form_2]
  type_forms f a b = case a of
    [] -> Right []
    c : d -> type_form f c b >>= \e -> (:) e <$> type_forms f d b
  type_kind :: (String, Kind) -> Kinds -> Kinds
  type_kind = uncurry ins_new
  type_kinds :: [(String, Kind)] -> Kinds -> Kinds
  type_kinds a b = case a of
    [] -> b
    c : d -> type_kinds d (type_kind c b)
  type_kinds'' ::
    [(String, Kind)] -> Integer -> Map' ((Kind, Status), Status') -> (Map' ((Kind, Status), Status'), Map' String)
  type_kinds'' a b c = type_kinds_3 a (show b) c empty
  type_kinds_3 ::
    [(String, Kind)] ->
    String ->
    Map' ((Kind, Status), Status') ->
    Map' String ->
    (Map' ((Kind, Status), Status'), Map' String)
  type_kinds_3 a b f c = case a of
    [] -> (f, c)
    (d, e) : g ->
      let
        h = d ++ b
      in
        type_kinds_3 g b (insert h ((e, New), Flexible) f) (insert d h c)
  type_type :: (Location_0 -> Location_1) -> Type_0 -> Kinds -> Kind -> Err Type_1
  type_type l (Type_0 a c) d e =
    let
      x = Left ("Kind mismatch" ++ location' (l a))
    in case c of
      Application_type_0 f g -> type_type' l f d >>= \(h, i) -> case i of
        Arrow_kind j k ->
          if k == e then
            Application_type_1 h <$> type_type l g d j
          else
            x
        _ -> x
      Int_type_0 b -> if e == Hash_kind then Right (Int_type_1 b) else x
      Name_type_0 f -> case Data.Map.lookup f d of
        Just (g, _) -> if g == e then Right (Name_type_1 f) else x
        Nothing -> Left ("Undefined type" ++ f ++ location' (l a))
  type_type' :: (Location_0 -> Location_1) -> Type_0 -> Kinds -> Err (Type_1, Kind)
  type_type' l (Type_0 a c) d = case c of
    Application_type_0 e f -> type_type' l e d >>= \(g, h) -> case h of
      Arrow_kind i j -> (\k -> (Application_type_1 g k, j)) <$> type_type l f d i
      _ -> Left ("Kind mismatch" ++ location' (l a))
    Int_type_0 b -> Right (Int_type_1 b, Hash_kind)
    Name_type_0 e -> case Data.Map.lookup e d of
      Just (f, _) -> Right (Name_type_1 e, f)
      Nothing -> Left ("Undefined type " ++ e ++ location' (l a))
  type_types :: (Location_0 -> Location_1) -> [Type_0] -> Kinds -> Err [Type_1]
  type_types f a b = case a of
    [] -> Right []
    c : d -> type_type f c b Star_kind >>= \e -> (:) e <$> type_types f d b
  types :: Map' Type_1'
  types =
    Data.Map.fromList
      [
        ("Add_Finite", Basic_type_1 [("N", Hash_kind)] (function_type finite_type (function_type finite_type finite_type))),
        ("Add_Int", Basic_type_1 [] (function_type int_type (function_type int_type int_type))),
        ("Convert_Finite", Basic_type_1 [("N", Hash_kind)] (function_type int_type finite_type)),
        ("Crash", Basic_type_1 [("U", Star_kind)] (Name_type_1 "U")),
        (
          "Equal_Finite",
          Basic_type_1 [("N", Hash_kind)] (function_type finite_type (function_type finite_type (Name_type_1 "Logical")))),
        ("Equal_Int", Basic_type_1 [] (function_type int_type (function_type int_type (Name_type_1 "Logical")))),
        ("False", Basic_type_1 [] (Name_type_1 "Logical")),
        ("H", gate_type_1),
        (
          "Inverse_Finite",
          Basic_type_1
            [("N", Hash_kind)]
            (function_type finite_type (Application_type_1 (Name_type_1 "Maybe") finite_type))),
        (
          "Lift_Array",
          Basic_type_1
            [("U", Star_kind)]
            (function_type
              int_type
              (function_type (Name_type_1 "U") (Application_type_1 (Name_type_1 "Array") (Name_type_1 "U"))))),
        (
          "Multiply_Finite",
          Basic_type_1 [("N", Hash_kind)] (function_type finite_type (function_type finite_type finite_type))),
        (
          "Multiply_Int",
          Basic_type_1
            []
            (function_type int_type (function_type int_type int_type))),
        ("Nothing", Basic_type_1 [("U", Star_kind)] (Application_type_1 (Name_type_1 "Maybe") (Name_type_1 "U"))),
        ("S", gate_type_1),
        ("S'", gate_type_1),
        ("T", gate_type_1),
        ("T'", gate_type_1),
        ("Take", Basic_type_1 [] (Name_type_1 "Qbit")),
        ("True", Basic_type_1 [] (Name_type_1 "Logical")),
        (
          "Wrap",
          Basic_type_1
            [("U", Star_kind)]
            (function_type (Name_type_1 "U") (Application_type_1 (Name_type_1 "Maybe") (Name_type_1 "U")))),
        ("X", gate_type_1),
        ("Y", gate_type_1),
        ("Z", gate_type_1)]
  typevar ::
    (String -> String) ->
    (String, Kind) ->
    (Map' String, Map' ((Kind, Status), Status')) ->
    (Map' String, Map' ((Kind, Status), Status'))
  typevar e (a, b) =
    let
      d = e a
    in
      bimap (insert a d) (insert d ((b, New), Flexible))
  typevars ::
    (String -> String) ->
    [(String, Kind)] ->
    (Map' String, Map' ((Kind, Status), Status')) ->
    (Map' String, Map' ((Kind, Status), Status'))
  typevars e a b = case a of
    [] -> b
    c : d -> typevars e d (typevar e c b)
  typing :: (Location_0 -> Location_1) -> Tree_5 -> (File, Defs) -> Err (File, Defs)
  typing k (Tree_5 a c) d =
    (
      type_datas k a d >>=
      \(File e b h g, f) ->
        (\(i, j) -> (File (rem_old e) (rem_old b) (rem_old h) (rem_old j), i)) <$> type_defs k c (e, b, h) (f, g))
  unsafe_lookup :: String -> Map' t -> t
  unsafe_lookup a b = case Data.Map.lookup a b of
    Just c -> c
    Nothing -> ice
-----------------------------------------------------------------------------------------------------------------------------