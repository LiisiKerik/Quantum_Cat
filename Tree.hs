-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
module Tree where
  import Control.Applicative
  import Control.Monad
  import Data.Bifunctor
  import Tokenise
  data Data_0 = Data_0 Name [(Name, Kind)] Data_branch_0 deriving Show
  data Data_branch_0 = Algebraic_data_0 [Form_0] | Struct_data_0 [(Name, Type_0)] deriving Show
  data Def_0 = Basic_def_0 Name [(Name, Kind)] [(Pattern_1, Type_0)] Type_0 Expression_0 deriving Show
  data Expression_0 = Expression_0 Location_0 Expression_branch_0 deriving Show
  data Expression_branch_0 =
    Application_expression_0 Expression_0 Expression_0 |
    Finite_expression_0 Integer Integer |
    Function_expression_0 Pattern_1 Expression_0 |
    Int_expression_0 Integer |
    Match_expression_0 Expression_0 [Match_0] |
    Name_expression_0 String
      deriving Show
  data Form_0 = Form_0 Name [Type_0] deriving Show
  data Kind = Arrow_kind Kind Kind | Hash_kind | Star_kind deriving (Eq, Show)
  data Match_0 = Match_0 Name [Pattern_1] Expression_0 deriving Show
  data Name = Name Location_0 String deriving Show
  data Pattern_1 = Pattern_1 Location_0 Pattern_0 deriving Show
  data Pattern_0 = Blank_pattern | Name_pattern String deriving Show
  newtype Parser t = Parser {parser :: State -> Either Location_0 (t, State)}
  data State = State Tokens Location_0
  data Tree_0 = Tree_0 [Data_0] [Def_0] deriving Show
  data Tree_1 = Tree_1 [Name] Tree_0 deriving Show
  data Type_branch_0 = Application_type_0 Type_0 Type_0 | Int_type_0 Integer | Name_type_0 String deriving Show
  data Type_0 = Type_0 Location_0 Type_branch_0 deriving Show
  class Get_location t where
    get_location :: t -> Location_0
  infixl 4 <&
  (<&) :: (Location_0 -> t) -> Parser () -> Parser t
  f <& p = f <$> parse_location <* p
  infixl 4 <&>
  (<&>) :: (Location_0 -> t -> u) -> Parser t -> Parser u
  f <&> p = f <$> parse_location <*> p
  instance Alternative Parser where
    Parser a <|> Parser b = Parser (\c -> left_bind (b <$> update_location c) (a c))
    empty = Parser (return (Left init_location))
  instance Applicative Parser where
    Parser a <*> Parser b = Parser (a >=> \(c, d) -> first c <$> b d)
    pure = lift_parser
  instance Functor Parser where
    fmap a (Parser b) = Parser (\c -> first a <$> b c)
  instance Get_location Pattern_1 where
    get_location (Pattern_1 a _) = a
  instance Get_location Type_0 where
    get_location (Type_0 a _) = a
  instance Monad Parser where
    Parser a >>= b = Parser (a >=> \(c, d) -> parser (b c) d)
    return = lift_parser
  init_location :: Location_0
  init_location = Location_0 0 0
  left_bind :: (t -> Either u v) -> Either t v -> Either u v
  left_bind a b = case b of
    Left c -> a c
    Right c -> Right c
  lift_parser :: t -> Parser t
  lift_parser x = Parser (\y -> Right (x, y))
  parse :: Parser t -> (Location_0 -> Location_1) -> String -> Err t
  parse a b c =
    let
       d = parse_error b
    in tokenise b c >>= \e -> case parser a (State e init_location) of
      Left f -> d f
      Right (f, State (Tokens g _) _) -> case g of
        [] -> Right f
        Token_1 h _ : _ -> d h
  parse_algebraic :: Parser Data_0
  parse_algebraic = parse_data' Algebraic_token (Algebraic_data_0 <$> parse_round (parse_list 2 parse_form))
  parse_application_expression :: Parser Expression_branch_0
  parse_application_expression =
    (
      (\x -> foldl (Application_expression_0 <$> Expression_0 x)) <&>
      (Application_expression_0 <$> parse_bracketed_expression <*> parse_bracketed_expression) <*>
      many parse_bracketed_expression)
  parse_application_type :: Parser Type_branch_0
  parse_application_type =
    (
      (\x -> foldl (Application_type_0 <$> Type_0 x)) <&>
      (Application_type_0 <$> parse_bracketed_type <*> parse_bracketed_type) <*>
      many parse_bracketed_type)
  parse_arguments :: (Parser [(t, u)] -> Parser [(t, u)]) -> Parser t -> Parser u -> Parser [(t, u)]
  parse_arguments a b c = parse_optional a ((,) <$> b <* parse_colon <*> c)
  parse_arguments' :: Parser t -> Parser [(t, Type_0)]
  parse_arguments' a = parse_arguments parse_round a parse_type
  parse_arrow :: Parser ()
  parse_arrow = parse_operator "->"
  parse_arrow_kind :: Parser Kind
  parse_arrow_kind = Arrow_kind <$> parse_bracketed_kind <* parse_arrow <*> parse_kind
  parse_basic :: Parser Def_0
  parse_basic =
    (
      Basic_def_0 <$>
      parse_name'' Def_token <*>
      parse_kinds <*>
      parse_arguments' parse_pattern_1 <*
      parse_colon <*>
      parse_type <*
      parse_operator "=" <*>
      parse_expression')
  parse_blank :: Parser Pattern_0
  parse_blank = Blank_pattern <$ parse_name_4 "_"
  parse_bracketed_expression :: Parser Expression_0
  parse_bracketed_expression = Expression_0 <&> (parse_elementary_expression <|> parse_round parse_composite_expression)
  parse_bracketed_type :: Parser Type_0
  parse_bracketed_type = Type_0 <&> (parse_name_type <|> parse_round parse_application_type)
  parse_bracketed_kind :: Parser Kind
  parse_bracketed_kind = parse_round parse_arrow_kind <|> parse_hash_kind <|> parse_star_kind
  parse_brackets :: Token_0 -> Parser t -> Token_0 -> Parser t
  parse_brackets a b c = parse_token a *> b <* parse_token c
  parse_colon :: Parser ()
  parse_colon = parse_operator ":"
  parse_comma :: Parser ()
  parse_comma = parse_token Comma_token
  parse_composite_expression :: Parser Expression_branch_0
  parse_composite_expression = parse_application_expression <|> parse_function <|> parse_match_expression
  parse_data :: Parser Data_0
  parse_data = parse_algebraic <|> parse_struct
  parse_data' :: Token_0 -> Parser Data_branch_0 -> Parser Data_0
  parse_data' a b = Data_0 <$> parse_name'' a <*> parse_kinds <*> b
  parse_def :: Parser Def_0
  parse_def = parse_basic
  parse_elementary :: (Token_0 -> Maybe t) -> Parser t
  parse_elementary a = Parser (\(State (Tokens b c) d) -> case b of
    [] -> Left c
    Token_1 e f : g ->
      let
        h = max d e
      in case a f of
        Just i -> Right (i, (State (Tokens g c) h))
        Nothing -> Left h)
  parse_elementary_expression :: Parser Expression_branch_0
  parse_elementary_expression = parse_finite <|> parse_int_expression <|> parse_name_expression
  parse_error :: (Location_0 -> Location_1) -> Location_0 -> Err t
  parse_error a b = Left ("Parse error" ++ location' (a b))
  parse_expression :: String -> Err Expression_0
  parse_expression = parse parse_expression' (Location_1 "expression")
  parse_expression' :: Parser Expression_0
  parse_expression' = Expression_0 <&> parse_expression_branch
  parse_expression_branch :: Parser Expression_branch_0
  parse_expression_branch = parse_composite_expression <|> parse_elementary_expression
  parse_finite :: Parser Expression_branch_0
  parse_finite =
    (
      parse_int >>=
      \x -> parse_token Hash_token *> parse_int >>= \y -> if x < y then return (Finite_expression_0 x y) else empty)
  parse_form :: Parser Form_0
  parse_form = Form_0 <$> parse_name' <*> parse_optional parse_round parse_type
  parse_function :: Parser Expression_branch_0
  parse_function = Function_expression_0 <$> parse_pattern_1 <* parse_arrow <*> parse_expression'
  parse_hash_kind :: Parser Kind
  parse_hash_kind = Hash_kind <$ parse_token Hash_token
  parse_int :: Parser Integer
  parse_int = parse_elementary (\a -> case a of
    Int_token b -> Just b
    _ -> Nothing)
  parse_int_expression :: Parser Expression_branch_0
  parse_int_expression = Int_expression_0 <$> parse_int
  parse_int_type :: Parser Type_branch_0
  parse_int_type = Int_type_0 <$> parse_int
  parse_kind :: Parser Kind
  parse_kind = parse_arrow_kind <|> parse_hash_kind <|> parse_star_kind
  parse_kinds :: Parser [(Name, Kind)]
  parse_kinds = parse_arguments (\a -> parse_brackets Left_square_token a Right_square_token) parse_name' parse_kind
  parse_list :: Integer -> Parser t -> Parser [t]
  parse_list a b = case a of
    0 -> parse_optional' (parse_list 1 b)
    _ -> parse_list' a b
  parse_list' :: Integer -> Parser t -> Parser [t]
  parse_list' a b = (:) <$> b <*> case a of
    1 -> many (parse_comma *> b)
    _ -> parse_comma *> parse_list (a - 1) b
  parse_load :: Parser Name
  parse_load = parse_name_3 Load_token ((flip (++) ".awf" <$> parse_name) <* parse_operator "." <* parse_name_4 "awf")
  parse_location :: Parser Location_0
  parse_location = Parser (\a -> Right (state_location a, a))
  parse_match :: Parser Match_0
  parse_match = Match_0 <$> parse_name' <*> many parse_pattern_1 <* parse_arrow <*> parse_expression'
  parse_match_expression :: Parser Expression_branch_0
  parse_match_expression =
    Match_expression_0 <$
    parse_token Match_token <*>
    parse_expression' <*
    parse_token Left_curly_token <*>
    parse_list 2 parse_match <*
    parse_token Right_curly_token
  parse_name :: Parser String
  parse_name = parse_elementary (\a -> case a of
    Name_token b -> Just b
    _ -> Nothing)
  parse_name' :: Parser Name
  parse_name' = Name <&> parse_name
  parse_name'' :: Token_0 -> Parser Name
  parse_name'' = flip parse_name_3 parse_name
  parse_name_3 :: Token_0 -> Parser String -> Parser Name
  parse_name_3 a b = Name <& parse_token a <*> b
  parse_name_4 :: String -> Parser ()
  parse_name_4 = parse_token <$> Name_token
  parse_name_expression :: Parser Expression_branch_0
  parse_name_expression = Name_expression_0 <$> parse_name
  parse_name_pattern :: Parser Pattern_0
  parse_name_pattern = Name_pattern <$> parse_name
  parse_name_type :: Parser Type_branch_0
  parse_name_type = Name_type_0 <$> parse_name
  parse_nothing :: Parser ()
  parse_nothing = Parser (\a -> Right ((), a))
  parse_operator :: String -> Parser ()
  parse_operator = parse_token <$> Operator_token
  parse_optional :: (Parser [t] -> Parser [t]) -> Parser t -> Parser [t]
  parse_optional a b = parse_optional' (a (parse_list 1 b))
  parse_optional' :: Parser [t] -> Parser [t]
  parse_optional' a = a <|> return []
  parse_pattern_0 :: Parser Pattern_0
  parse_pattern_0 = parse_blank <|> parse_name_pattern
  parse_pattern_1 :: Parser Pattern_1
  parse_pattern_1 = Pattern_1 <&> parse_pattern_0
  parse_round :: Parser t -> Parser t
  parse_round a = parse_brackets Left_round_token a Right_round_token
  parse_star_kind :: Parser Kind
  parse_star_kind = Star_kind <$ parse_operator "*"
  parse_struct :: Parser Data_0
  parse_struct = parse_data' Struct_token (Struct_data_0 <$> parse_arguments' parse_name')
  parse_token :: Token_0 -> Parser ()
  parse_token a = parse_elementary (\b -> if b == a then Just () else Nothing)
  parse_tree :: (Location_0 -> Location_1) -> String -> Err Tree_1
  parse_tree = parse parse_tree'
  parse_tree' :: Parser Tree_1
  parse_tree' = Tree_1 <$> many parse_load <*> (Tree_0 <$> many parse_data <*> many parse_def)
  parse_type :: Parser Type_0
  parse_type = Type_0 <&> parse_type_branch
  parse_type_branch :: Parser Type_branch_0
  parse_type_branch = parse_application_type <|> parse_int_type <|> parse_name_type
  state_location :: State -> Location_0
  state_location (State (Tokens a b) _) = case a of
    [] -> b
    Token_1 c _ : _ -> c
  update_location :: State -> Location_0 -> State
  update_location (State a b) c = State a (max b c)
-----------------------------------------------------------------------------------------------------------------------------