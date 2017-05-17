-----------------------------------------------------------------------------------------------------------------------------
{-# LANGUAGE TupleSections #-}
module Tokenise where
  import Data.Bifunctor
  import Data.Char
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
      deriving(Show)
  data Token = Token(Integer)(Integer)(Token_type) deriving(Show)
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
      deriving(Eq, Show)
  char_type :: Char -> Char_type
  char_type('\n') = Newline_char
  char_type(' ') = Space_char
  char_type('\'') = Name_char('\'')
  char_type('(') = Delimiter_char(Left_round_token)
  char_type(')') = Delimiter_char(Right_round_token)
  char_type(',') = Delimiter_char(Comma_token)
  char_type('-') = Dash_char
  char_type('/') = Slash_char
  char_type(':') = Delimiter_char(Colon_token)
  char_type(';') = Delimiter_char(Semicolon_token)
  char_type('=') = Delimiter_char(Equality_token)
  char_type('>') = Greater_char
  char_type('[') = Delimiter_char(Left_square_token)
  char_type(']') = Delimiter_char(Right_square_token)
  char_type('_') = Name_char('_')
  char_type('`') = Tick_char
  char_type('{') = Delimiter_char(Left_curly_token)
  char_type('}') = Delimiter_char(Right_curly_token)
  char_type('~') = Tilde_char
  char_type(x) = if isDigit(x) then Int_char(x) else if isLetter(x) then Name_char(x) else Invalid_char
  name_token :: String -> Token_type
  name_token("Algebraic") = Algebraic_token
  name_token("Def") = Def_token
  name_token("Match") = Match_token
  name_token("Struct") = Struct_token
  name_token(x) = Name_token(x)
  tokenise :: String -> Either((Integer, Integer), String)([Token])
  tokenise = tokenise'(1)(1) . (<$>)(char_type)
  tokenise' :: Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise'(l)(c)([]) = Right([Token(l)(c)(End_token)])
  tokenise'(l)(c)(Dash_char : x) = tokenise_dash(l)(c)(c + 1)(x)
  tokenise'(l)(c)(Delimiter_char(x) : y) = (Token(l)(c)(x) :) <$> tokenise'(l)(c + 1)(y)
  tokenise'(l)(c)(Greater_char : _) = Left((l, c), "Arrowhead without the stem.")
  tokenise'(l)(c)(x @ (Int_char(_) : _)) = uncurry(:) . first(Token(l)(c) . Int_token . read) <$> tokenise_int(l)(c)(x)
  tokenise'(l)(c)(Invalid_char : _) = Left((l, c), "Invalid character.")
  tokenise'(l)(c)(x @ (Name_char(_) : _)) = uncurry(:) . first(Token(l)(c) . name_token) <$> tokenise_name(l)(c)(x)
  tokenise'(l)(_)(Newline_char : x) = tokenise'(l + 1)(1)(x)
  tokenise'(l)(c)(Slash_char : _) = Left((l, c), "Misplaced comment marker.")
  tokenise'(l)(c)(Space_char : x) = tokenise'(l)(c + 1)(x)
  tokenise'(l)(c)(Tick_char : x) = tokenise_single(l)(c + 1)(x)
  tokenise'(l)(c)(Tilde_char : x) = tokenise_tilde(l)(c + 1)(x)
  tokenise_dash :: Integer -> Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise_dash(l)(c')(c)(x) = case x of
    Greater_char : y -> (Token(l)(c')(Arrow_token) :) <$> tokenise'(l)(c + 1)(y)
    _ -> Left((l, c'), "Arrow stem without the head.")
  tokenise_int :: Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)(String, [Token])
  tokenise_int(l)(c)(Int_char(x) : y) = first(x :) <$> tokenise_int(l)(c + 1)(y)
  tokenise_int(l)(c)(x) = ("", ) <$> tokenise'(l)(c)(x)
  tokenise_multi :: Integer -> Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise_multi(l)(c)(_)([]) = Left((l, c), "Missing end comment.")
  tokenise_multi(l)(_)(n)(Newline_char : x) = tokenise_multi(l + 1)(1)(n)(x)
  tokenise_multi(l)(c)(n)(Slash_char : x) = tokenise_slash(l)(c + 1)(n)(x)
  tokenise_multi(l)(c)(n)(Tilde_char : x) = tokenise_multi_tilde(l)(c + 1)(n)(x)
  tokenise_multi(l)(c)(n)(_ : x) = tokenise_multi(l)(c + 1)(n)(x)
  tokenise_multi_tilde :: Integer -> Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise_multi_tilde(l)(c)(n)(Slash_char : x) = tokenise_multi(l)(c + 1)(n + 1)(x)
  tokenise_multi_tilde(l)(c)(n)(x) = tokenise_multi(l)(c)(n)(x)
  tokenise_name :: Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)(String, [Token])
  tokenise_name(l)(c)(Int_char(x) : y) = first(x :) <$> tokenise_name(l)(c + 1)(y)
  tokenise_name(l)(c)(Name_char(x) : y) = first(x :) <$> tokenise_name(l)(c + 1)(y)
  tokenise_name(l)(c)(x) = ("", ) <$> tokenise'(l)(c)(x)
  tokenise_single :: Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise_single(l)(c)([]) = Right([Token(l)(c)(End_token)])
  tokenise_single(l)(_)(Newline_char : x) = tokenise'(l + 1)(1)(x)
  tokenise_single(l)(c)(_ : x) = tokenise_single(l)(c + 1)(x)
  tokenise_slash :: Integer -> Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise_slash(l)(c)(n)(Tilde_char : x) = if n == 1 then tokenise'(l)(c + 1)(x) else tokenise_multi(l)(c + 1)(n - 1)(x)
  tokenise_slash(l)(c)(n)(x) = tokenise_multi(l)(c)(n)(x)
  tokenise_tilde :: Integer -> Integer -> [Char_type] -> Either((Integer, Integer), String)([Token])
  tokenise_tilde(l)(c)(Slash_char : x) = tokenise_multi(l)(c + 1)(1)(x)
  tokenise_tilde(l)(c)(_) = Left((l, c), "Misplaced comment marker.")
-----------------------------------------------------------------------------------------------------------------------------