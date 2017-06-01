-- TODO: LAMBDAS
-- TODO: TYPE SYNONYMS
-- TODO: ADD GATES (SEE QASM DOCUMENTATION ON GITHUB)
-- TODO: NESTED DEFINITIONS
-- TODO: IMPROVE PERFORMANCE BY REPLACING LISTS WITH MAPS
-- TODO: INTEGRATION WITH PYTHON/HASKELL?
-- TODO: <*> OPERATOR FOR ARRAYS
-- TODO: TYPE INFERENCE
-- TODO: CONSTRUCTOR FOR ARRAYS
-- TODO: HEAD AND TAIL
-- TODO: MORE DETAILED LOCATIONS FOR TYPE MISMATCH ERROR?
-- TODO: OPERATORS?
-- TODO: SIMULATOR FOR TRYING OUT THE RESULTING QASM CODE?
-- TODO: PRETTIER QASM CODE BY DEFINING COMPOSITE GATES IN THE CODE?
-- TODO: OPTIMISATIONS IN GENERATED CIRCUIT. WIPE AND RE-USE OF BITS TO REDUCE THE REQUIRED AMOUNT OF MEMORY?
-- TODO: SOME OPERATIONS ON TYPE-LEVEL NUMBERS?
-- TODO: STATIC CHECKING OF ARRAY INDEXATION?
-- TODO: ARRAY INDEXATION
-- TODO: ALLOW MORE THAN 1-DIMENSIONAL CBIT ARRAYS (AND ALSO SINGLE CBITS) AS OUTPUTS?
-- TODO: NON-GATE, ORDINARY IF BASED ON ALGEBRAIC DATA TYPES AND CASE MATCHING
-- TODO: CLEAN UP REPEATED CODE IN QUANTUM_CAT' FILE
-- TODO: NECESSARY OPERATIONS FOR INTS, BOOLS
-- TODO: BOOLS
-- TODO: TYPING ERROR WITH BETTER PLACEMENT (DO THEY OCCUR IN LIBRARY OR INPUT)
-- TODO: IS TAGGING STRUCTS AND FIELD ACCESSORS WITH STRUCT NAMES NECESSARY FOR SAFETY OR NOT? IF NOT, REMOVE NAMES.
-- TODO: IMPROVE PARSER AND REMOVE UGLY CODE FROM TYPECHECKING BY SEPARATING PRIMITIVE TYPES FROM USER-DEFINED TYPES DURING PARSING?
-- TODO: MATCHING EXPRESSIONS FOR VALUES
-- TODO: UNUSED PARAMETER WARNINGS?
-- TODO: TRY, CATCH, CRASH
-- TODO: BLANKS IN PATTERNS IN ALGEBRAIC DATA TYPE MATCHING
-- TODO: A DEFAULT CASE IN ALGEBRAIC DATA TYPE MATCHING
-- TODO: POSSIBILITY OF MATCHING THE GENERAL SHAPE WITHOUT BINDING ANY VARIABLES, LIKE {} IN HASKELL?
-- TODO: BLANKS IN FUNCTION ARGUMENTS
-- TODO: REPLACE PATTERN (INTEGER, INTEGER, STRING) IN DATA STRUCTURES IN PARSER WITH NAME_TREE WHERE APPROPRIATE
-- TODO: ADD FUNCTION COMPOSITION, S-COMBINATOR, IDENTITY, CONST, ETC...
-- TODO: IMPROVE EFFICIENCY BY REPLACING INTEGER WITH INT IN SOME PLACES
-- TODO: MAKE CASE LISTING [MATCH_TREE] A LOOKUP TABLE / MAP INSTEAD?
-- TODO: TYPE PARAMETERS OF KIND * -> * AND SO ON. FUNCTORS, APPLICATIVE FUNCTORS, MONADS
-- TODO: BUILD UP SOME STANDARD LIBRARY
-- TODO: ADDITION EXAMPLE (BOTH WITH BUILT-IN AND HOME-MADE TOFFOLI GATES)
-- TODO: GRAPH EXAMPLES
-- TODO: CHARS, STRINGS?
-- TODO: KEEP LIST OF ALGEBRAIC DATA TYPE BRANCHES MAYBE([STRING]) SEPARATE FROM TYPE AND TYPE' STRUCTURES?
-- TODO: THERE'S MAYBE A BUG IN NAME CHECKING. TYPE VARIABLES OF STRUCTS MIGHT CLASH WITH GLOBAL NAME DEFS. FIX BY MAKING GATHERING ALL GLOBAL NAMES FROM THE FILE THE FIRST STEP IN TYPECHECKING.
-- TODO: REARRANGE THE ORDER OF [] AND {} PARAMETERS
-- TODO: TEST SEVERAL VERSIONS OF RANDOM NUMBER GENERATION, WITH MORE AND LESS THINGS INLINED
-- TODO: ADD GADT-S TO THE LANGUAGE?
-- TODO: USE GADT-S TO MAKE THE COMPILER SAFER AND TO REMOVE THE NECESSITY FOR SOME OF ERROR MESSAGES?
-- TODO: ADD SOMETHING FOR EASILY UPDATING FIELDS OF STRUCTS
-- TODO: IMPLEMENT ADDITIONAL TYPE RESTRICTIONS FOR THINGS THAT CAN'T BE USED ON EVERYTHING (LIKE IF_GATE' WHERE TYPE VARIABLE U SHOULD ACTUALLY BE RESTRICTED TO QUANTUM STRUCTURES)?
-- TODO: GENERALISE IF GATE TO WORK ON DIFFERENT KINDS OF STRUCTS, NOT ONLY ON CREGS?
-- TODO: AD HOC POLYMORPHISM?
-- TODO: LOOK INTO TYPE ERROR WITH LINE "Def Main'(x : Arr[Qbit]{9}) : Arr[Qbit]{9} = Measure{9}(Map[Qbit, Qbit]{9}(H, x))"
-- TODO: CAN THERE BE DEAD CODE INSIDE SUBROUTINES? IF YES, CAN WE REMOVE IT?
-- TODO: (CIRCUIT, VAL) -> (CIRCUIT, VAL) INSTEAD OF CIRCUIT -> VAL -> (CIRCUIT, VAL) IN FUNC_VAL?
-- TODO: LIST AND VECTOR AGGREGATION
-- TODO: REPLACE LET WITH WHERE
-- TODO: REMOVE EXCESSIVE PARENTHESES
-- TODO: REPLACE LAMBDAS CONTAINING PATTERN MATCHES OF ADT-S WITH CASE STATEMENTS FOR SAFETY?
-- TODO: CHANGE LIFT SO THAT THE ORIGINAL THING THAT WE COPY IS REMOVED?
-- TODO: CHANGE APPLICATION PARSING; DO NOT REQUIRE BRACKETS?
-- TODO: DIFFERENT WAYS OF ARRAY AGGREGATION
-- TODO: ARRAY REVERSAL
-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TupleSections #-}
module Tree where
  import Data.Bifunctor
  import Tokenise
  data Algebraic_form_tree = Algebraic_form_tree Integer Integer String [Type_tree] deriving Show
  data Argument_tree = Argument_tree Integer Integer String Type_tree deriving Show
  data Data_branch = Algebraic_tree [Algebraic_form_tree] | Struct_tree([Argument_tree]) deriving Show
  data Data_tree = Data_tree Decl_tree Data_branch deriving Show
  data Decl_tree = Decl_tree Integer Integer String [Name_tree] [Name_tree] deriving Show
  data Def_tree = Def_tree Decl_tree [Argument_tree] Type_tree Expression_tree deriving Show
  data Expression_branch =
    Expression_application Expression_tree [Expression_tree] |
    Expression_int Integer |
    Expression_match Expression_tree [Match_tree] |
    Expression_name String [Type_tree] [Int_tree]
      deriving Show
  data Expression_tree = Expression_tree Integer Integer Expression_branch deriving Show
  data Int_branch = Int_constant Integer | Int_variable String deriving (Eq, Show)
  data Int_tree = Int_tree Integer Integer Int_branch deriving (Eq, Show)
  data Match_tree = Match_tree Name_tree [Name_tree] Expression_tree deriving Show
  data Name_tree = Name_tree Integer Integer String deriving Show
  newtype Parser t = Parser {parser :: [Token] -> Either (Integer, Integer) (t, [Token])}
  instance Applicative Parser where
    Parser p <*> Parser q = Parser (\x -> p x >>= \(f, y) -> first f <$> q y)
    pure x = Parser (Right <$> (x, ))
  instance Functor Parser where
    fmap f (Parser p) = Parser ((<$>) (first f) <$> p)
  data Tree = Tree [Data_tree] [Def_tree] deriving Show
  data Type_branch = Basic_type String [Type_tree] [Int_tree] | Function_type Type_tree Type_tree deriving (Eq, Show)
  data Type_tree = Type_tree Integer Integer Type_branch deriving (Eq, Show)
  (<&) :: (Integer -> Integer -> t) -> Parser () -> Parser t
  infixl 4 <&
  f <& p = f <$> line_tree <*> column_tree <* p
  (<&>) :: (Integer -> Integer -> t -> u) -> Parser t -> Parser u
  infixl 4 <&>
  f <&> p = f <$> line_tree <*> column_tree <*> p
  (<+>) :: Parser t -> Parser t -> Parser t
  infixl 3 <+>
  Parser p <+> Parser q = Parser (\x -> left_bind (\l -> first (max l) (q x)) (p x))
  algebraic_form_tree :: Parser(Algebraic_form_tree)
  algebraic_form_tree = Algebraic_form_tree <&> name_tree <*> optional_round_tree(type_tree)
  algebraic_tree :: Parser Data_branch
  algebraic_tree = Algebraic_tree <$> at_least_2_tree(algebraic_form_tree)
  at_least_2_sep_tree :: Parser t -> Parser () -> Parser [t]
  at_least_2_sep_tree p q = (\x -> \y -> \z -> x : y : z) <$> p <* q <*> p <*> list_tree(q *> p)
  at_least_2_tree :: Parser t -> Parser [t]
  at_least_2_tree p = round_tree ((\x -> \y -> \z -> x : y : z) <$> p <*> p <*> list_tree(comma_tree *> p))
  application_suffix_tree :: Parser (Expression_tree -> Expression_branch)
  application_suffix_tree =
    (
      (\x -> \y -> \z @ (Expression_tree l c _) -> y (Expression_tree l c (Expression_application z x))) <$>
      round_comma_list_tree expression_tree <*>
      application_suffix_tree) <+>
    flip Expression_application <$> round_comma_list_tree expression_tree
  application_tree :: Parser(Expression_branch)
  application_tree = flip ($) <$> (Expression_tree <&> name_expression_tree) <*> application_suffix_tree
  args_tree :: Parser [Argument_tree]
  args_tree = optional_round_tree argument_tree
  argument_tree :: Parser(Argument_tree)
  argument_tree = Argument_tree <&> name_tree <* discard_tree Colon_token <*> type_tree
  arrow_tree :: Parser ()
  arrow_tree = discard_tree Arrow_token
  basic_type_tree :: Parser Type_branch
  basic_type_tree = Basic_type <$> name_tree <*> square_tree type_tree <*> curly_tree int_tree'
  between_tree :: Parser () -> Parser t -> Parser () -> Parser t
  between_tree p q r = p *> q <* r
  column_tree :: Parser(Integer)
  column_tree = Parser(\x @ (Token _ c _ : _) -> Right(c, x))
  curly_tree :: Parser t -> Parser [t]
  curly_tree p = optional_tree (discard_tree Left_curly_token) p (discard_tree Right_curly_token)
  comma_tree :: Parser ()
  comma_tree = discard_tree Comma_token
  data_tree :: Parser Data_tree
  data_tree =
    Data_tree <$> decl_tree(Algebraic_token) <*> algebraic_tree <+> Data_tree <$> decl_tree Struct_token <*> struct_tree
  decl_tree :: Token_type -> Parser Decl_tree
  decl_tree x = Decl_tree <& discard_tree x <*> name_tree <*> type_param_tree <*> int_param_tree
  def_tree :: Parser Def_tree
  def_tree =
    Def_tree <$>
    decl_tree Def_token <*>
    args_tree <*
    discard_tree Colon_token <*>
    type_tree <*
    discard_tree Equality_token <*>
    expression_tree
  discard_tree :: Token_type -> Parser ()
  discard_tree x = Parser (\(Token l c y : z) -> if y == x then Right ((), z) else Left (l, c))
  end_tree :: Parser t -> Parser t
  end_tree t = t <* discard_tree End_token
  expr_tree :: [Token] -> Either (Integer, Integer) Expression_tree
  expr_tree = (<$>) fst . parser expr_tree'
  expr_tree' :: Parser Expression_tree
  expr_tree' = end_tree expression_tree
  expression_branch :: Parser Expression_branch
  expression_branch =
    application_tree <+>
    Expression_int <$> int_tree <+>
    (
      Expression_match <$
      discard_tree Match_token <*>
      round_tree expression_tree <*>
      at_least_2_sep_tree match_tree semicolon_tree) <+>
    name_expression_tree
  expression_tree :: Parser Expression_tree
  expression_tree = Expression_tree <&> expression_branch
  function_type_tree :: Parser Type_branch
  function_type_tree =
    Function_type <$>
    (Type_tree <&> (basic_type_tree <+> round_tree function_type_tree)) <*
    arrow_tree <*>
    type_tree
  int_branch :: Parser Int_branch
  int_branch = Int_constant <$> int_tree <+> Int_variable <$> name_tree
  int_param_tree :: Parser [Name_tree]
  int_param_tree = curly_tree name_tree'
  int_tree :: Parser Integer
  int_tree = Parser (\(Token l c x : y) -> case x of
    Int_token z -> Right (z, y)
    _ -> Left (l, c))
  int_tree' :: Parser Int_tree
  int_tree' = Int_tree <&> int_branch
  left_bind :: (t -> Either u v) -> Either t v -> Either u v
  left_bind f x = case x of
    Left y -> f y
    Right y -> Right y
  left_round_tree :: Parser ()
  left_round_tree = discard_tree Left_round_token
  left_square_tree :: Parser ()
  left_square_tree = discard_tree(Left_square_token)
  line_tree :: Parser(Integer)
  line_tree = Parser (\x @ (Token l _ _ : _) -> Right (l, x))
  list_tree :: Parser t -> Parser [t]
  list_tree p = (:) <$> p <*> list_tree p <+> pure []
  match_tree :: Parser Match_tree
  match_tree = Match_tree <$> name_tree' <*> optional_round_tree name_tree' <* arrow_tree <*> expression_tree
  name_expression_tree :: Parser Expression_branch
  name_expression_tree = Expression_name <$> name_tree <*> square_tree type_tree <*> curly_tree int_tree'
  name_tree :: Parser String
  name_tree = Parser (\(Token l c x : y) -> case x of
    Name_token z -> Right (z, y)
    _ -> Left (l, c))
  name_tree' :: Parser Name_tree
  name_tree' = Name_tree <&> name_tree
  non_empty_comma_list_tree :: Parser t -> Parser [t]
  non_empty_comma_list_tree p = (:) <$> p <*> list_tree (comma_tree *> p)
  optional_round_tree :: Parser t -> Parser [t]
  optional_round_tree p = optional_tree left_round_tree p right_round_tree
  optional_tree :: Parser () -> Parser t -> Parser () -> Parser [t]
  optional_tree p q r = between_tree p (non_empty_comma_list_tree q) r <+> pure []
  right_round_tree :: Parser ()
  right_round_tree = discard_tree Right_round_token
  right_square_tree :: Parser ()
  right_square_tree = discard_tree Right_square_token
  round_comma_list_tree :: Parser t -> Parser [t]
  round_comma_list_tree = round_tree . non_empty_comma_list_tree
  round_tree :: Parser t -> Parser t
  round_tree p = between_tree left_round_tree p right_round_tree
  semicolon_tree :: Parser ()
  semicolon_tree = discard_tree(Semicolon_token)
  sep_tree :: Parser t -> Parser () -> Parser [t]
  sep_tree p q = (:) <$> p <*> list_tree (q *> p) <+> pure []
  square_tree :: Parser t -> Parser [t]
  square_tree p = optional_tree left_square_tree p right_square_tree
  struct_tree :: Parser Data_branch
  struct_tree = Struct_tree <$> args_tree
  tree :: [Token] -> Either (Integer, Integer) Tree
  tree = (<$>) fst . parser tree'
  tree' :: Parser Tree
  tree' = end_tree (Tree <$> list_tree data_tree <*> list_tree def_tree)
  type_branch :: Parser Type_branch
  type_branch = function_type_tree <+> basic_type_tree
  type_param_tree :: Parser [Name_tree]
  type_param_tree = square_tree name_tree'
  type_tree :: Parser Type_tree
  type_tree = Type_tree <&> type_branch
-----------------------------------------------------------------------------------------------------------------------------