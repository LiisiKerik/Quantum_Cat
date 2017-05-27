-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TupleSections #-}
module Tokenise where
  import Data.Bifunctor
  import Data.Char
  instance Eq (t -> u) where
    _ == _ = error "Internal type error. Tried to compare functions."
  instance Show (t -> u) where
    show = return "FUNCTION"
  data Char_type =
    Dash_char |
    Delimiter_char(Token_type) |
    Greater_char |
    Int_char(Char) |
    Invalid_char |
    Name_char(Char) |
    Newline_char |
    Slash_char |
    Space_char |
    Tick_char |
    Tilde_char
      deriving (Eq, Show)
  data Token = Token(Integer)(Integer)(Token_type) deriving (Eq, Show)
  data Token_type =
    Algebraic_token |
    Arrow_token |
    Colon_token |
    Comma_token |
    Def_token |
    End_token |
    Equality_token |
    Int_token(Integer) |
    Left_curly_token |
    Left_round_token |
    Left_square_token |
    Match_token |
    Name_token(String) |
    Right_curly_token |
    Right_round_token |
    Right_square_token |
    Semicolon_token |
    Struct_token
      deriving (Eq, Show)
  char_type :: Char -> Char_type
  char_type c = case c of
    '\n' -> Newline_char
    ' ' -> Space_char
    '\'' -> Name_char '\''
    '(' -> Delimiter_char Left_round_token
    ')' -> Delimiter_char Right_round_token
    ',' -> Delimiter_char Comma_token
    '-' -> Dash_char
    '/' -> Slash_char
    ':' -> Delimiter_char Colon_token
    ';' -> Delimiter_char Semicolon_token
    '=' -> Delimiter_char Equality_token
    '>' -> Greater_char
    '[' -> Delimiter_char Left_square_token
    ']' -> Delimiter_char Right_square_token
    '_' -> Name_char '_'
    '`' -> Tick_char
    '{' -> Delimiter_char Left_curly_token
    '}' -> Delimiter_char Right_curly_token
    '~' -> Tilde_char
    _ -> if isDigit c then Int_char c else if isLetter c then Name_char c else Invalid_char
  name_token :: String -> Token_type
  name_token s = case s of
    "Algebraic" -> Algebraic_token
    "Def" -> Def_token
    "Match" -> Match_token
    "Struct" -> Struct_token
    _ -> Name_token s
  tokenise :: String -> Either((Integer, Integer), String) [Token]
  tokenise = tokenise' 1 1 . (<$>) char_type
  tokenise' :: Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise' l c x = case x of
    [] -> Right([Token l c End_token])
    h : t -> case h of
      Dash_char -> tokenise_dash l c (c + 1) t
      Delimiter_char y -> (Token l c y :) <$> tokenise' l (c + 1) t
      Greater_char -> Left ((l, c), "Arrowhead without the stem.")
      Int_char{} -> uncurry (:) . first (Token l c <$> Int_token <$> read) <$> tokenise_int l c x
      Invalid_char -> Left ((l, c), "Invalid character.")
      Name_char{} -> uncurry (:) . first (Token l c <$> name_token) <$> tokenise_name l c x
      Newline_char -> tokenise' (l + 1) 1 t
      Slash_char -> Left ((l, c), "Misplaced comment marker.")
      Space_char -> tokenise' l (c + 1) t
      Tick_char -> tokenise_single l (c + 1) t
      Tilde_char -> tokenise_tilde l (c + 1) t
  tokenise_dash :: Integer -> Integer -> Integer -> [Char_type] -> Either ((Integer, Integer), String) [Token]
  tokenise_dash l c' c x = case x of
    Greater_char : y -> (Token l c' Arrow_token :) <$> tokenise' l (c + 1) y
    _ -> Left ((l, c'), "Arrow stem without the head.")
  tokenise_int :: Integer -> Integer -> [Char_type] -> Either ((Integer, Integer), String) (String, [Token])
  tokenise_int l c (Int_char x : y) = first(x :) <$> tokenise_int l (c + 1) y
  tokenise_int l c x = ("", ) <$> tokenise' l c x
  tokenise_multi :: Integer -> Integer -> Integer -> [Char_type] -> Either ((Integer, Integer), String) [Token]
  tokenise_multi l c _ [] = Left ((l, c), "Missing end comment.")
  tokenise_multi l _ n (Newline_char : x) = tokenise_multi (l + 1) 1 n x
  tokenise_multi(l)(c)(n)(Slash_char : x) = tokenise_slash l (c + 1) n x
  tokenise_multi(l)(c)(n)(Tilde_char : x) = tokenise_multi_tilde l (c + 1) n x
  tokenise_multi(l)(c)(n)(_ : x) = tokenise_multi l (c + 1) n x
  tokenise_multi_tilde :: Integer -> Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise_multi_tilde(l)(c)(n)(Slash_char : x) = tokenise_multi(l)(c + 1)(n + 1)(x)
  tokenise_multi_tilde(l)(c)(n)(x) = tokenise_multi(l)(c)(n)(x)
  tokenise_name :: Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)(String, [Token])
  tokenise_name l c (Int_char(x) : y) = first(x :) <$> tokenise_name(l)(c + 1)(y)
  tokenise_name l c (Name_char(x) : y) = first(x :) <$> tokenise_name(l)(c + 1)(y)
  tokenise_name l c x = ("", ) <$> tokenise'(l)(c)(x)
  tokenise_single :: Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise_single l c [] = Right([Token(l)(c)(End_token)])
  tokenise_single l _ (Newline_char : x) = tokenise'(l + 1)(1)(x)
  tokenise_single l c (_ : x) = tokenise_single l (c + 1) x
  tokenise_slash :: Integer -> Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise_slash(l)(c)(n)(Tilde_char : x) = if n == 1 then tokenise'(l)(c + 1)(x) else tokenise_multi(l)(c + 1)(n - 1)(x)
  tokenise_slash(l)(c)(n)(x) = tokenise_multi(l)(c)(n)(x)
  tokenise_tilde :: Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise_tilde(l)(c)(Slash_char : x) = tokenise_multi(l)(c + 1)(1)(x)
  tokenise_tilde(l)(c)(_) = Left((l, c), "Misplaced comment marker.")
-----------------------------------------------------------------------------------------------------------------------------