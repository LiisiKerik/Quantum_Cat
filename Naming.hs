-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
module Naming where
  import Data.Bifunctor
  import Data.Map
  import Standard
  import Tokenise
  import Tree
  data Data_branch_1 = Algebraic_data_1 [Form_1] | Struct_data_1 [(String, Type_0)] deriving Show
  data Data_1 = Data_1 String [(Name, Kind)] Data_branch_1 deriving Show
  data Data_2 = Data_2 String [(String, Kind)] Data_branch_1 deriving Show
  data Def_2 = Basic_def_2 Location_0 String [(String, Kind)] Type_0 Expression_1 deriving Show
  data Expression_branch_1 =
    Application_expression_1 Expression_1 Expression_1 |
    Finite_expression_1 Integer Integer |
    Function_expression_1 Pattern_0 Expression_1 |
    Int_expression_1 Integer |
    Match_expression_1 Expression_1 [Match_1] |
    Name_expression_1 String
      deriving Show
  data Expression_1 = Expression_1 Location_0 Expression_branch_1 deriving Show
  data Form_1 = Form_1 String [Type_0] deriving Show
  data Location' = Language | Library Location_1 deriving Show
  type Locations = Map' Location'
  type Map' t = Map String t
  data Match_1 = Match_1 Name [Pattern_0] Expression_1 deriving Show
  data Status = New | Old deriving (Eq, Show)
  data Tree_4 = Tree_4 [Data_1] [Def_1] deriving Show
  data Tree_5 = Tree_5 [Data_2] [Def_2] deriving Show
  add :: Ord t => Map t u -> t -> u -> Either u (Map t u)
  add x y z = (case w of
    Just z' -> Left z'
    Nothing -> Right x') where
      (w, x') = insertLookupWithKey (return return) y z x
  location_err :: String -> Location' -> Location_1 -> String
  location_err a c d = "Conflicting " ++ a ++ (case c of
    Language -> " in the language"
    Library e -> location e) ++ " and" ++ location' d
  locations :: Locations
  locations =
    Data.Map.fromList
      (
        flip (,) (Language) <$>
        [
          "Add_Finite",
          "Add_Int",
          "Array",
          "CH",
          "CX",
          "CY",
          "CZ",
          "Convert_Finite",
          "Crash",
          "Equal_Finite",
          "Equal_Int",
          "False",
          "Finite",
          "Function",
          "H",
          "Int",
          "Inverse_Finite",
          "Lift_Array",
          "Logical",
          "Maybe",
          "Multiply_Finite",
          "Multiply_Int",
          "Nothing",
          "Qbit",
          "S",
          "S'",
          "T",
          "T'",
          "Take",
          "True",
          "Wrap",
          "X",
          "Y",
          "Z"])
  naming :: String -> Tree_2 -> Locations -> Err (Locations, Tree_5)
  naming f a b = naming_1 f a b >>= \(c, d) -> ((,) c) <$> naming_2 f d c
  naming_argument ::
    (String -> t -> Locations -> Err (Locations, u)) -> String -> (t, v) -> Locations -> Err (Locations, (u, v))
  naming_argument a e (b, c) d = second (flip (,) c) <$> a e b d
  naming_arguments ::
    (String -> t -> Locations -> Err (Locations, u)) -> String -> [(t, v)] -> Locations -> Err (Locations, [(u, v)])
  naming_arguments = naming_list <$> naming_argument
  naming_arguments' :: String -> (String -> t -> Locations -> Err (Locations, u)) -> [(t, v)] -> Locations -> Err [(u, v)]
  naming_arguments' c a b = (<$>) snd <$> naming_arguments a c b
  naming_1 :: String -> Tree_2 -> Locations -> Err (Locations, Tree_4)
  naming_1 f (Tree_2 a b) c = naming_datas_1 f a c >>= \(d, e) -> flip (,) (Tree_4 e b) <$> naming_defs_1 f b d
  naming_2 :: String -> Tree_4 -> Locations -> Err Tree_5
  naming_2 e (Tree_4 a b) c = naming_datas_2 e a c >>= \d -> Tree_5 d <$> naming_defs_2 e b c
  naming_data_1 :: String -> Data_0 -> Locations -> Err (Locations, Data_1)
  naming_data_1 g (Data_0 a b c) d =
    naming_name g a d >>= \(e, f) -> second (Data_1 f b) <$> naming_data_branches g c e
  naming_data_2 :: String -> Data_1 -> Locations -> Err Data_2
  naming_data_2 f (Data_1 a b c) d = (\e -> Data_2 a e c) <$> naming_arguments' f naming_name b d
  naming_data_branches :: String -> Data_branch_0 -> Locations -> Err (Locations, Data_branch_1)
  naming_data_branches c a = case a of
    Algebraic_data_0 b -> naming_forms c b
    Struct_data_0 b -> naming_fields c b
  naming_datas_1 :: String -> [Data_0] -> Locations -> Err (Locations, [Data_1])
  naming_datas_1 = naming_list naming_data_1
  naming_datas_2 :: String -> [Data_1] -> Locations -> Err [Data_2]
  naming_datas_2 f a b = case a of
    [] -> Right []
    c : d -> naming_data_2 f c b >>= \e -> (:) e <$> naming_datas_2 f d b
  naming_def_1 :: String -> Def_1 -> Locations -> Err Locations
  naming_def_1 i a = case a of
    Basic_def_1 c _ _ _ -> (<$>) fst <$> naming_name i c
  naming_def_2 :: String -> Def_1 -> Locations -> Err Def_2
  naming_def_2 j a b = case a of
    Basic_def_1 (Name k c) d f g ->
      naming_arguments naming_name j d b >>= \(h, i) -> Basic_def_2 k c i f <$> naming_expression j g h
  naming_defs_1 :: String -> [Def_1] -> Locations -> Err Locations
  naming_defs_1 a b c = case b of
    [] -> Right c
    d : e -> naming_def_1 a d c >>= naming_defs_1 a e
  naming_defs_2 :: String -> [Def_1] -> Locations -> Err [Def_2]
  naming_defs_2 = naming_list' naming_def_2
  naming_expression :: String -> Expression_0 -> Locations -> Err Expression_1
  naming_expression e (Expression_0 a c) d = Expression_1 a <$> naming_expression_branch e c d
  naming_expression_branch :: String -> Expression_branch_0 -> Locations -> Err Expression_branch_1
  naming_expression_branch g a b = case a of
    Application_expression_0 c d -> naming_expression g c b >>= \e -> Application_expression_1 e <$> naming_expression g d b
    Finite_expression_0 c d -> Right (Finite_expression_1 c d)
    Function_expression_0 c d -> naming_pattern g c b >>= \(e, f) -> Function_expression_1 f <$> naming_expression g d e
    Int_expression_0 c -> Right (Int_expression_1 c)
    Match_expression_0 c d -> naming_expression g c b >>= \e -> Match_expression_1 e <$> naming_matches g d b
    Name_expression_0 c -> Right (Name_expression_1 c)
  naming_fields :: String -> [(Name, Type_0)] -> Locations -> Err (Locations, Data_branch_1)
  naming_fields b a c = second Struct_data_1 <$> naming_arguments naming_name b a c
  naming_form :: String -> Form_0 -> Locations -> Err (Locations, Form_1)
  naming_form d (Form_0 a b) c = second (flip Form_1 b) <$> naming_name d a c
  naming_forms :: String -> [Form_0] -> Locations -> Err (Locations, Data_branch_1)
  naming_forms c a b = second Algebraic_data_1 <$> naming_list naming_form c a b
  naming_list :: (String -> t -> u -> Err (u, v)) -> String -> [t] -> u -> Err (u, [v])
  naming_list a h b c = case b of
    [] -> Right (c, [])
    d : e -> a h d c >>= \(f, g) -> second ((:) g) <$> naming_list a h e f
  naming_list' :: (String -> t -> u -> Err v) -> String -> [t] -> u -> Err [v]
  naming_list' a g b c = case b of
    [] -> Right []
    d : e -> a g d c >>= \f -> (:) f <$> naming_list' a g e c
  naming_match :: String -> Match_0 -> Locations -> Err Match_1
  naming_match g (Match_0 a b c) d = naming_patterns g b d >>= \(e, f) -> Match_1 a f <$> naming_expression g c e
  naming_matches :: String -> [Match_0] -> Locations -> Err [Match_1]
  naming_matches = naming_list' naming_match
  naming_name :: String -> Name -> Locations -> Err (Locations, String)
  naming_name f (Name a c) d =
    bimap (flip (location_err ("definitions of " ++ c)) (Location_1 f a)) (flip (,) c) (add d c (Library (Location_1 f a)))
  naming_pattern :: String -> Pattern_1 -> Locations -> Err (Locations, Pattern_0)
  naming_pattern f (Pattern_1 a c) d = case c of
    Blank_pattern -> Right (d, Blank_pattern)
    Name_pattern e -> second Name_pattern <$> naming_name f (Name a e) d
  naming_patterns :: String -> [Pattern_1] -> Locations -> Err (Locations, [Pattern_0])
  naming_patterns = naming_list naming_pattern
  old :: Map' t -> Map' (t, Status)
  old = (<$>) (flip (,) Old)
  rem_old :: Map' (t, Status) -> Map' (t, Status)
  rem_old = (<$>) (second (return Old)) <$> Data.Map.filter ((==) New <$> snd)
-----------------------------------------------------------------------------------------------------------------------------