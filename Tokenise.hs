-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
module Tokenise where
  import Data.Bifunctor
  import Data.Char
  data Char' =
    Delimiter_char Token_0 |
    Int_char Char |
    Name_char Char |
    Newline_char |
    Operator_char Char |
    Slash_char |
    Space_char |
    Tick_char |
    Tilde_char
      deriving Show
  type Err t = Either String t
  data Location_0 = Location_0 Integer Integer deriving (Eq, Ord, Show)
  data Location_1 = Location_1 String Location_0 deriving Show
  data Token_0 =
    Algebraic_token |
    Case_token |
    Comma_token |
    Def_token |
    Default_token |
    Int_token Integer |
    Left_curly_token |
    Left_round_token |
    Left_square_token |
    Load_token |
    Match_token |
    Name_token String |
    Operator_token String |
    Right_curly_token |
    Right_round_token |
    Right_square_token |
    Struct_token
      deriving (Eq, Show)
  data Token_1 = Token_1 Location_0 Token_0 deriving Show
  data Tokens = Tokens [Token_1] Location_0 deriving Show
  accumulate :: (String -> Token_0) -> (Char' -> Maybe Char) -> Location_1 -> [Char'] -> Err Tokens
  accumulate a b c d = (\(e, f) -> add_token c (a e) f) <$> accumulate' b c d
  accumulate' :: (Char' -> Maybe Char) -> Location_1 -> [Char'] -> Err (String, Tokens)
  accumulate' a b c =
    let
      d = (,) "" <$> tokenise' b c
    in case c of
      [] -> d
      e : f -> case a e of
        Just g -> first ((:) g) <$> accumulate' a (next_char b) f
        Nothing -> d
  add_token :: Location_1 -> Token_0 -> Tokens -> Tokens
  add_token (Location_1 _ a) b (Tokens c d) = Tokens (Token_1 a b : c) d
  char :: Char -> Char'
  char a = case a of
    '\n' -> Newline_char
    ' ' -> Space_char
    '(' -> Delimiter_char Left_round_token
    ')' -> Delimiter_char Right_round_token
    ',' -> Delimiter_char Comma_token
    '/' -> Slash_char
    '[' -> Delimiter_char Left_square_token
    ']' -> Delimiter_char Right_square_token
    '`' -> Tick_char
    '{' -> Delimiter_char Left_curly_token
    '}' -> Delimiter_char Right_curly_token
    '~' -> Tilde_char
    _ ->
      (if_sequence
        a
        [
          (flip
            elem
            ['!', '#', '$', '%', '&', '*', '+', '-', '.', ':', ';', '|', '<', '=', '>', '?', '@', '\\', '^'], Operator_char),
          (isDigit, Int_char)]
        Name_char)
          a
  end_tokens :: Location_1 -> Err Tokens
  end_tokens (Location_1 _ a) = Right (Tokens [] a)
  file_location :: Location_1 -> String
  file_location (Location_1 a _) = a
  if_sequence :: t -> [(t -> Bool, u)] -> u -> u
  if_sequence a b c = case b of
    [] -> c
    (d, e) : f -> if d a then e else if_sequence a f c
  int_char :: Char' -> Maybe Char
  int_char a = case a of
    Int_char b -> Just b
    _ -> Nothing
  location :: Location_1 -> String
  location (Location_1 a (Location_0 b c)) = " at " ++ a ++ ":" ++ show b ++ ":" ++ show c
  location' :: Location_1 -> String
  location' a = location a ++ "."
  name_char :: Char' -> Maybe Char
  name_char a = case a of
    Name_char b -> Just b
    _ -> Nothing
  next_char :: Location_1 -> Location_1
  next_char (Location_1 a (Location_0 b c)) = Location_1 a (Location_0 b (c + 1))
  next_line :: Location_1 -> Location_1
  next_line (Location_1 a (Location_0 b _)) = Location_1 a (Location_0 (b + 1) 1)
  operator_char :: Char' -> Maybe Char
  operator_char a = case a of
    Operator_char b -> Just b
    Slash_char -> Just '/'
    Tilde_char -> Just '~'
    _ -> Nothing
  tokenise :: (Location_0 -> Location_1) -> String -> Err Tokens
  tokenise a b = tokenise' (a (Location_0 1 1)) (char <$> b)
  tokenise' :: Location_1 -> [Char'] -> Err Tokens
  tokenise' a b = case b of
    [] -> end_tokens a
    c : d ->
      let
        e = next_char a
        f = tokenise_operator a b
      in case c of
        Delimiter_char g -> add_token a g <$> tokenise' e d
        Int_char _ -> accumulate (Int_token <$> read) int_char a b
        Name_char _ -> accumulate word_token name_char a b
        Newline_char -> tokenise' (next_line a) d
        Operator_char _ -> f
        Slash_char -> f
        Space_char -> tokenise' e d
        Tick_char -> tokenise_single e d
        Tilde_char -> tokenise_tilde a b e d
  tokenise_multiline :: Integer -> Location_1 -> [Char'] -> Err Tokens
  tokenise_multiline a b c = case c of
    [] -> Left ("Missing end comment in " ++ file_location b ++ ".")
    d : e ->
      let
        f = tokenise_multiline a
        g = next_char b
      in case d of
        Newline_char -> f (next_line b) e
        Slash_char -> tokenise_slash a g e
        Tilde_char -> tokenise_multiline_tilde a g e
        _ -> f g e
  tokenise_multiline_tilde :: Integer -> Location_1 -> [Char'] -> Err Tokens
  tokenise_multiline_tilde a b c = case c of
    Slash_char : d -> tokenise_multiline (a + 1) (next_char b) d
    _ -> tokenise_multiline a b c
  tokenise_operator :: Location_1 -> [Char'] -> Err Tokens
  tokenise_operator = accumulate Operator_token operator_char
  tokenise_single :: Location_1 -> [Char'] -> Err Tokens
  tokenise_single a b = case b of
    [] -> end_tokens a
    c : d -> (case c of
      Newline_char -> tokenise' (next_line a)
      _ -> tokenise_single (next_char a)) d
  tokenise_slash :: Integer -> Location_1 -> [Char'] -> Err Tokens
  tokenise_slash a b c = case c of
    Tilde_char : d -> (case a of
      1 -> tokenise'
      _ -> tokenise_multiline (a - 1)) (next_char b) d
    _ -> tokenise_multiline a b c
  tokenise_tilde :: Location_1 -> [Char'] -> Location_1 -> [Char'] -> Err Tokens
  tokenise_tilde a b c d = case d of
    Slash_char : e -> tokenise_multiline 1 (next_char c) e
    _ -> tokenise_operator a b
  word_token :: String -> Token_0
  word_token a = case a of
    "Algebraic" -> Algebraic_token
    "Case" -> Case_token
    "Def" -> Def_token
    "Default" -> Default_token
    "Load" -> Load_token
    "Match" -> Match_token
    "Struct" -> Struct_token
    _ -> Name_token a
-----------------------------------------------------------------------------------------------------------------------------