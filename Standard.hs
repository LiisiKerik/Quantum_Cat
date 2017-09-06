-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
module Standard where
  import Data.Bifunctor
  import Tokenise
  import Tree
  data Def_1 = Basic_def_1 Name [(Name, Kind)] Type_0 Expression_0 deriving Show
  data Tree_2 = Tree_2 [Data_0] [Def_1] deriving Show
  data Tree_3 = Tree_3 [Name] Tree_2 deriving Show
  standard' :: (Location_0 -> Location_1) -> String -> Err Tree_3
  standard' a b = standard_0 <$> parse_tree a b
  standard_0 :: Tree_1 -> Tree_3
  standard_0 (Tree_1 a b) = Tree_3 a (standard_1 b)
  standard_1 :: Tree_0 -> Tree_2
  standard_1 (Tree_0 a b) = Tree_2 a (standard_defs b)
  standard_argument :: (Pattern_1, Type_0) -> (Type_0, Expression_0) -> (Type_0, Expression_0)
  standard_argument (a, b) = bimap (standard_type b) (standard_pattern a)
  standard_arguments :: (Type_0, Expression_0) -> [(Pattern_1, Type_0)] -> (Type_0, Expression_0)
  standard_arguments = foldr standard_argument
  standard_def :: Def_0 -> Def_1
  standard_def a = case a of
    Basic_def_0 b c d e f -> uncurry (Basic_def_1 b c) (standard_arguments (e, f) d)
  standard_defs :: [Def_0] -> [Def_1]
  standard_defs = (<$>) standard_def
  standard_pattern :: Pattern_1 -> Expression_0 -> Expression_0
  standard_pattern a = Expression_0 (get_location a) <$> Function_expression_0 a
  standard_type :: Type_0 -> Type_0 -> Type_0
  standard_type a b =
    let
      c = get_location a
    in Type_0 c (Application_type_0 (Type_0 c (Application_type_0 (Type_0 c (Name_type_0 "Function")) a)) b)
-----------------------------------------------------------------------------------------------------------------------------