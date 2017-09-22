{-
HIGHEST PRIORITY
if gate
let expression
constructor for arrays [x0, x1, x2, ...] in addition to existing length-and-index constructor
make match work with negative ints (modify parser)
check whether kinds of everything are ok (ending with a star) - potential failure to catch very stupid bugs
addition of qnums. test it
protection against duplicate file loading - what happens now? if crashes - fix, give a nice error/warning. if nothing - warn?
implement all necessary operations for ints and bools (both classical and quantum)
graph examples
foldm for log-depth array aggregation - probably necessary for more efficient circuits
tests
NICE-TO-HAVE
type synonyms
operators
type operators
abstract methods
optimisations in generated circuit. wipe and re-use of qbits and cregs to reduce the required amount of memory
internal: attach scope tags to kinds once instead of doing it in type_kinds
if-elif-else
eta reduction warnings
unused type variable warnings
unused local variable warnings
add something for easily changing fields of structs
internal: do something with old/new status tags. check where exactly they're necessary. get rid of them where they're useless
internal: with new matching error system, do we need to keep locations for each match? if not, modify parser/namer to remove
change semantics of missing pattern-match variables from blank to lambda? (Left -> e is not Left _ -> e but Left x -> e x)
internal: make the system of specifying built-in algebraic data types and things better and safer
"Algebraic List[A : *](Cons(A, List A), Empty)" -> "Algebraic List[A : *](Cons A (List A), Empty)"
Allow hiding things to functions outside module - so that helper functions are not exported from the module
OF QUESTIONABLE USEFULNESS
internal: do something with the internal representation of arrays to reduce lookup complexity?
allow more than 1-dimensional cbit arrays (and also single cbits) as outputs?
linked lists?
gather naming and type errors and give a list instead of giving only the first one?
internal: remove locations from expressions except from lowest-level things where some checks are necessary (name)?
switch expression that is less strict and more flexible than match?
generalise if gate to work on different kinds of structs, not only on cregs?
change how crash works? wrap expr_3 in maybe, make constructors give crash as a result when they get crash as argument?
prettier result code by letting user define composite gates which will be printed as subroutine in end code?
there's too much safety now? wrapping all array operations in maybe seems silly. make wrong indexation etc crash instead?
rename bool type into "Bit" for nice symmetry between classical and quantum types?
-}
-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
module Typing where
  import Data.Bifunctor
  import Data.Map
  import Naming
  import Standard
  import Tokenise
  import Tree
  type Algebraics = Map' (([(String, Kind)], Map' [Type_1], Type_1), Status) -- TODO: REM STRINGS FROM FST MAP
  type Constrs = Map' (String, Status)
  data Def_4 = Basic_def_4 Location_0 String [(String, Kind)] Kinds Type_1 Expression_1 deriving Show
  type Defs = Map' Expression_2
  data Expression_2 =
    Add_Int_expression_2 |
    Add_Int'_expression_2 Integer |
    Algebraic_expression_2 String [Expression_2] |
    Application_expression_2 Expression_2 Expression_2 |
    Array_expression_2 Integer [Expression_2] |
    CCX_expression_2 |
    CCX'_expression_2 Integer |
    CCX''_expression_2 Integer Integer |
    Construct_expression_2 |
    Construct'_expression_2 Integer |
    Crash_expression_2 |
    Creg_expression_2 Integer |
    Double_expression_2 String |
    Double'_expression_2 String Integer |
    Equal_Int_expression_2 |
    Equal_Int'_expression_2 Integer |
    Field_expression_2 String |
    Function_expression_2 Pattern_0 Expression_2 |
    Index_expression_2 |
    Index'_expression_2 Integer [Expression_2] |
    Int_expression_2 Integer |
    Length_expression_2 |
    Less_Int_expression_2 |
    Less_Int'_expression_2 Integer |
    Match_expression_2 Expression_2 Matches_2 |
    Measure_expression_2 |
    Mod_Int_expression_2 |
    Mod_Int'_expression_2 Integer |
    Multiply_Int_expression_2 |
    Multiply_Int'_expression_2 Integer |
    Name_expression_2 String |
    Negate_Int_expression_2 |
    Qbit_expression_2 Integer |
    Single_expression_2 String |
    Struct_expression_2 (Map' Expression_2) |
    Take_expression_2
      deriving Show
  data File = File Kinds Algebraics Constrs Types deriving Show
  data Form_2 = Form_2 String [Type_1] deriving Show
  type Kinds = Map' (Kind, Status)
  data Match_Algebraic_2 = Match_Algebraic_2 [Pattern_0] Expression_2 deriving Show
  data Matches_2 =
    Matches_Algebraic_2 (Map' Match_Algebraic_2) (Maybe Expression_2) | Matches_Int_2 (Map Integer Expression_2) Expression_2
      deriving Show
  data Status' = Fixed | Flexible deriving Show
  data Type_1 = Application_type_1 Type_1 Type_1 | Name_type_1 String deriving (Eq, Show)
  data Type_1' = Basic_type_1 [(String, Kind)] Type_1 | Local_type_1 Type_1 deriving Show
  type Types = Map' (Type_1', Status)
  algebraics :: Map' ([(String, Kind)], Map' [Type_1], Type_1)
  algebraics =
    fromList
      [
        ("Logical", ([], fromList [("False", []), ("True", [])], logical_type)),
        (
          "Maybe",
          (
            [("A", Star_kind)],
            fromList [("Nothing", []), ("Wrap", [Name_type_1 "A"])],
            maybe_type (Name_type_1 "A")))]
  array_type :: Type_1 -> Type_1
  array_type = Application_type_1 (Name_type_1 "Array")
  check_kind :: String -> String -> Map' ((Kind, Status), Status') -> Type_1 -> Err Kind
  check_kind j c a b = case b of
    Application_type_1 d e -> check_kind j c a d >>= \f -> case f of
      Arrow_kind g h -> check_kind j c a e >>= \i -> if i == g then Right h else Left j
      _ -> Left j
    Name_type_1 d -> if d == c then Left j else Right (fst (fst (unsafe_lookup d a)))
  constrs :: Map' String
  constrs = fromList [("False", "Logical"), ("Nothing", "Maybe"), ("True", "Logical"), ("Wrap", "Maybe")]
  context_union :: File -> File -> File
  context_union (File b i j d) (File f k l h) =
    File (Data.Map.union b f) (Data.Map.union i k) (Data.Map.union j l) (Data.Map.union d h)
  creg_type :: Type_1
  creg_type = Name_type_1 "Creg"
  defs :: Map' Expression_2
  defs = fst <$> defs_and_types
  defs_and_types :: Map' (Expression_2, Type_1')
  defs_and_types =
    fromList
      [
        ("Add_Int", (Add_Int_expression_2, Basic_type_1 [] (function_type int_type (function_type int_type int_type)))),
        (
          "Array",
          (
            Construct_expression_2,
            Basic_type_1
              [("A", Star_kind)]
              (function_type
                int_type
                (function_type (function_type int_type (Name_type_1 "A")) (maybe_type (array_type (Name_type_1 "A"))))))),
        (
          "CCX",
          (
            CCX_expression_2,
            Basic_type_1 [] (function_type qbit_type (function_type qbit_type (function_type qbit_type qbit_type))))),
        ("CH", (Double_expression_2 "ch", gate_type_2)),
        ("CX", (Double_expression_2 "cx", gate_type_2)),
        ("CY", (Double_expression_2 "cy", gate_type_2)),
        ("CZ", (Double_expression_2 "cz", gate_type_2)),
        ("Crash", (Crash_expression_2, Basic_type_1 [("A", Star_kind)] (Name_type_1 "A"))),
        (
          "Equal_Int",
          (Equal_Int_expression_2, Basic_type_1 [] (function_type int_type (function_type int_type logical_type)))),
        ("False", (Algebraic_expression_2 "False" [], Basic_type_1 [] logical_type)),
        ("H", (Single_expression_2 "h", gate_type_1)),
        (
          "Index",
          (
            Index_expression_2,
            Basic_type_1
              [("A", Star_kind)]
              (function_type (array_type (Name_type_1 "A")) (function_type int_type (maybe_type (Name_type_1 "A")))))),
        (
          "Length",
          (Length_expression_2, Basic_type_1 [("A", Star_kind)] (function_type (array_type (Name_type_1 "A")) int_type))),
        (
          "Less_Int",
          (Less_Int_expression_2, Basic_type_1 [] (function_type int_type (function_type int_type logical_type)))),
        ("Measure", (Measure_expression_2, Basic_type_1 [] (function_type (array_type qbit_type) creg_type))),
        ("Mod_Int", (Mod_Int_expression_2, Basic_type_1 [] (function_type int_type (function_type int_type int_type)))),
        (
          "Multiply_Int",
          (Multiply_Int_expression_2, Basic_type_1 [] (function_type int_type (function_type int_type int_type)))),
        ("Negate_Int", (Negate_Int_expression_2, Basic_type_1 [] (function_type int_type int_type))),
        ("Nothing", (Algebraic_expression_2 "Nothing" [], Basic_type_1 [("A", Star_kind)] (maybe_type (Name_type_1 "A")))),
        ("S", (Single_expression_2 "s", gate_type_1)),
        ("S'", (Single_expression_2 "sdg", gate_type_1)),
        ("T", (Single_expression_2 "t", gate_type_1)),
        ("T'", (Single_expression_2 "tdg", gate_type_1)),
        ("Take", (Take_expression_2, Basic_type_1 [] (function_type unit_type qbit_type))),
        ("True", (Algebraic_expression_2 "True" [], Basic_type_1 [] logical_type)),
        ("Unit", (Struct_expression_2 empty, Basic_type_1 [] unit_type)),
        (
          "Wrap",
          (Function_expression_2 (Name_pattern "x") (Algebraic_expression_2 "Wrap" [Name_expression_2 "x"]),
          Basic_type_1
            [("A", Star_kind)]
            (function_type (Name_type_1 "A") (Application_type_1 (Name_type_1 "Maybe") (Name_type_1 "A"))))),
        ("X", (Single_expression_2 "x", gate_type_1)),
        ("Y", (Single_expression_2 "y", gate_type_1)),
        ("Z", (Single_expression_2 "z", gate_type_1))]
  find_and_delete :: Ord t => Map t u -> t -> Maybe (u, Map t u)
  find_and_delete a b = (\c -> (c, Data.Map.delete b a)) <$> Data.Map.lookup b a
  function_type :: Type_1 -> Type_1 -> Type_1
  function_type = Application_type_1 <$> Application_type_1 (Name_type_1 "Function")
  gate_type_1 :: Type_1'
  gate_type_1 = Basic_type_1 [] (function_type qbit_type qbit_type)
  gate_type_2 :: Type_1'
  gate_type_2 = Basic_type_1 [] (function_type qbit_type (function_type qbit_type qbit_type))
  ice :: t
  ice = error "Internal compiler error."
  init_type_context :: File
  init_type_context = File (old kinds) (old algebraics) (old constrs) (old (snd <$> defs_and_types))
  ins_new :: String -> t -> Map' (t, Status) -> Map' (t, Status)
  ins_new a b = insert a (b, New)
  int_type :: Type_1
  int_type = Name_type_1 "Int"
  kinds :: Map' Kind
  kinds =
    fromList
      [
        ("Array", Arrow_kind Star_kind Star_kind),
        ("Creg", Star_kind),
        ("Function", Arrow_kind Star_kind (Arrow_kind Star_kind Star_kind)),
        ("Int", Star_kind),
        ("Logical", Star_kind),
        ("Maybe", Arrow_kind Star_kind Star_kind),
        ("Qbit", Star_kind),
        ("Unit", Star_kind)]
  location_err' :: String -> Location_1 -> Location_1 -> String
  location_err' a b = location_err a (Library b)
  logical_type :: Type_1
  logical_type = Name_type_1 "Logical"
  maybe_type :: Type_1 -> Type_1
  maybe_type = Application_type_1 (Name_type_1 "Maybe")
  qbit_type :: Type_1
  qbit_type = Name_type_1 "Qbit"
  naming_typing :: String -> Tree_2 -> (Locations, File, Defs) -> Err (Locations, File, Defs)
  naming_typing f a (b, c, g) = naming f a b >>= \(d, e) -> (\(h, i) -> (d, h, i)) <$> typing (Location_1 f) e (c, g)
  repl :: Map' String -> Type_1 -> Type_1
  repl a b = case b of
    Application_type_1 c d -> Application_type_1 (repl a c) (repl a d)
    Name_type_1 c -> Name_type_1 (case Data.Map.lookup c a of
      Just d -> d
      Nothing -> c)
  solvesys :: String -> Map' ((Kind, Status), Status') -> [(Type_1, Type_1)] -> Err ()
  solvesys m a b = case b of
    [] -> Right ()
    (c, d) : g -> case c of
      Application_type_1 e f -> case d of
        Application_type_1 h i -> solvesys m a ((e, h) : (f, i) : g)
        Name_type_1 h -> solvesys' m a h c g
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
  type_case :: (Location_0 -> Location_1) -> Name -> Map' String -> [Pattern_0] -> [Type_1] -> Types -> Err Types
  type_case j (m @ (Name k l)) a b c d = case b of
    [] -> Right d
    e : f -> case c of
      [] -> Left ("Constructor " ++ l ++ location (j k) ++ " has too many fields.")
      g : h -> type_case j m a f h (case e of
        Blank_pattern -> d
        Name_pattern i -> ins_new i (Local_type_1 (repl a g)) d)
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
      flip (insert e) c <$> type_expr ("function " ++ e ++ location (j r)) h j ((\g -> (g, Fixed)) <$> b, d, l, k) i
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
    type_expression c d a 0 0 b [] e f h >>= \(g, i, j, _, _) -> g <$ solvesys ("Type error in " ++ k ++ ".") i j
  type_expr' :: (Location_0 -> Location_1) -> (Kinds, Algebraics, Constrs, Types) -> Expression_1 -> Err Expression_2
  type_expr' a (b, c, d, e) = type_expr "input" (Name_type_1 "Creg") a (flip (,) Fixed <$> b, c, d, e)
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
  type_expression v w r o s f h d (Expression_1 a b) e =
    let
      x' = location' (r a)
    in case b of
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
        Matches_Algebraic_1 i j -> case i of
          [] -> ice
          Match_Algebraic_1 (Name _ l) _ _ : _ ->
            let
              y0 = "Match error" ++ x' ++ " Undefined algebraic constructors, incompatible constructors or conflicting cases"
            in case Data.Map.lookup l w of
              Just (m, _) ->
                let
                  (n, p, q) = fst (unsafe_lookup m v)
                  (t, u) = typevars (flip (++) (show s)) n (empty, f)
                  l0 = repl t q
                in (
                  type_expression v w r o (s + 1) u h d c l0 >>=
                  \(x, y, a0, b0, c0) ->
                    type_matches_algebraic v w r b0 c0 y a0 d empty i e p y0 t >>= \(d0, e0, f0, g0, h0, i0) ->
                      let
                        k0 = Match_expression_2 x <$> Matches_Algebraic_2 d0
                      in if Data.Map.null i0 then case j of
                        Just _ -> Left ("Unnecessary default case " ++ x')
                        Nothing -> Right (k0 Nothing, e0, f0, g0, h0) else case j of
                          Just j0 ->
                            (
                              (\(a', b', c', d', e') -> (k0 (Just a'), b', c', d', e')) <$>
                              type_expression v w r g0 h0 e0 f0 d j0 l0)
                          Nothing -> Left ("Incomplete match" ++ x'))
              Nothing -> Left y0
        Matches_Int_1 i j ->
          (
            type_expression v w r o s f h d c (Name_type_1 "Int") >>=
            \(k, l, m, n, p) ->
              (
                type_matches_int v w r n p l m d empty i e >>=
                \(q, t, u, x, y) ->
                  (
                    (\(a0, b0, c0, d0, e0) -> (Match_expression_2 k (Matches_Int_2 q a0), b0, c0, d0, e0)) <$>
                    type_expression v w r x y t u d j e)))
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
                in (n, repl p j, s + 1)
              Local_type_1 i -> (f, i, s)
          in Right (Name_expression_2 c, k, (e, l) : h, o, m)
        Nothing -> Left ("Undefined variable " ++ c ++ x')
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
  type_match_algebraic ::
    Algebraics ->
    Constrs ->
    (Location_0 -> Location_1) ->
    Integer ->
    Integer ->
    Map' ((Kind, Status), Status') ->
    [(Type_1, Type_1)] ->
    Types ->
    Map' Match_Algebraic_2 ->
    Match_Algebraic_1 ->
    Type_1 ->
    Map' [Type_1] ->
    String ->
    Map' String ->
    Err (Map' Match_Algebraic_2, Map' ((Kind, Status), Status'), [(Type_1, Type_1)], Integer, Integer, Map' [Type_1])
  type_match_algebraic a b c d e f g h i (Match_Algebraic_1 (Name j k) l m) n o q r = case find_and_delete o k of
    Just (p, y) ->
      (
        type_case c (Name j k) r l p h >>=
        \s ->
          (\(t, u, v, w, x) -> (insert k (Match_Algebraic_2 l t) i, u, v, w, x, y)) <$> type_expression a b c d e f g s m n)
    Nothing -> Left q
  type_match_int ::
    Algebraics ->
    Constrs ->
    (Location_0 -> Location_1) ->
    Integer ->
    Integer ->
    Map' ((Kind, Status), Status') ->
    [(Type_1, Type_1)] ->
    Types ->
    Map Integer Expression_2 ->
    Match_Int_1 ->
    Type_1 ->
    Err (Map Integer Expression_2, Map' ((Kind, Status), Status'), [(Type_1, Type_1)], Integer, Integer)
  type_match_int a b c d e f g h i (Match_Int_1 j k) l =
-- TODO: PUT A GOOD ERROR MESSAGE HERE. LOCATIONS AND STUFF.
    (
      type_expression a b c d e f g h k l >>=
      \(m, n, o, p, q) ->
        bimap (\_ -> location_err' ("cases for " ++ show j) undefined undefined) (\r -> (r, n, o, p, q)) (add i j m))
  type_matches_algebraic ::
    Algebraics ->
    Constrs ->
    (Location_0 -> Location_1) ->
    Integer ->
    Integer ->
    Map' ((Kind, Status), Status') ->
    [(Type_1, Type_1)] ->
    Types ->
    Map' Match_Algebraic_2 ->
    [Match_Algebraic_1] ->
    Type_1 ->
    Map' [Type_1] ->
    String ->
    Map' String ->
    Err (Map' Match_Algebraic_2, Map' ((Kind, Status), Status'), [(Type_1, Type_1)], Integer, Integer, Map' [Type_1])
  type_matches_algebraic a b c d e f g h i j k s u v = case j of
    [] -> Right (i, f, g, d, e, s)
    l : m ->
      (
        type_match_algebraic a b c d e f g h i l k s u v >>=
        \(n, o, p, q, r, t) -> type_matches_algebraic a b c q r o p h n m k t u v)
  type_matches_int ::
    Algebraics ->
    Constrs ->
    (Location_0 -> Location_1) ->
    Integer ->
    Integer ->
    Map' ((Kind, Status), Status') ->
    [(Type_1, Type_1)] ->
    Types ->
    Map Integer Expression_2 ->
    [Match_Int_1] ->
    Type_1 ->
    Err (Map Integer Expression_2, Map' ((Kind, Status), Status'), [(Type_1, Type_1)], Integer, Integer)
  type_matches_int a b c d e f g h i j k = case j of
    [] -> Right (i, f, g, d, e)
    l : m -> type_match_int a b c d e f g h i l k >>= \(n, o, p, q, r) -> type_matches_int a b c q r o p h n m k
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
      Name_type_0 f -> case Data.Map.lookup f d of
        Just (g, _) -> if g == e then Right (Name_type_1 f) else x
        Nothing -> Left ("Undefined type " ++ f ++ location' (l a))
  type_type' :: (Location_0 -> Location_1) -> Type_0 -> Kinds -> Err (Type_1, Kind)
  type_type' l (Type_0 a c) d = case c of
    Application_type_0 e f -> type_type' l e d >>= \(g, h) -> case h of
      Arrow_kind i j -> (\k -> (Application_type_1 g k, j)) <$> type_type l f d i
      _ -> Left ("Kind mismatch" ++ location' (l a))
    Name_type_0 e -> case Data.Map.lookup e d of
      Just (f, _) -> Right (Name_type_1 e, f)
      Nothing -> Left ("Undefined type " ++ e ++ location' (l a))
  type_types :: (Location_0 -> Location_1) -> [Type_0] -> Kinds -> Err [Type_1]
  type_types f a b = case a of
    [] -> Right []
    c : d -> type_type f c b Star_kind >>= \e -> (:) e <$> type_types f d b
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
  unit_type :: Type_1
  unit_type = Name_type_1 "Unit"
  unsafe_lookup :: String -> Map' t -> t
  unsafe_lookup a b = case Data.Map.lookup a b of
    Just c -> c
    Nothing -> ice
-----------------------------------------------------------------------------------------------------------------------------