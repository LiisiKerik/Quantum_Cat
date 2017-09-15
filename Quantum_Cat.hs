-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
import Circuit
import Code
import Data.List
import Data.Map
import Naming
import Optimise
import Standard
import System.Directory
import System.Environment
import System.FilePath
import Tokenise
import Tree
import Typing
type Files = Map' File
check :: [String] -> (Files, Locations, Defs) -> Location' -> String -> IO (Err (Files, Locations, Defs, File))
check b (f, x, y) j name_qc = case Data.Map.lookup name_qc f of
  Just a -> return (Right (f, x, y, a))
  Nothing -> case check' name_qc b of
    Just a -> return (Left ("Circular dependency between files " ++ intercalate ", " a ++ "."))
    Nothing -> do
      find_file <- findFile [""] name_qc
      case find_file of
        Just file -> do
          a <- readFile file
          case standard (Location_1 name_qc) a of
            Left c -> return (Left c)
            Right (Tree_3 c d) -> do
              g <-
                check_imports
                  (name_qc : b)
                  (f, x, y, init_type_context)
                  ((\(Name h i) -> (Library (Location_1 name_qc h), i)) <$> c)
              return
                (
                  g >>=
                  \(h, i, l, m) ->
                    (\(k, n, o) -> (Data.Map.insert name_qc n h, k, o, n)) <$> naming_typing name_qc d (i, m, l))
        Nothing -> err ("Failed to find file " ++ name_qc ++ " requested" ++ case j of
          Language -> " in the command."
          Library k -> location' k)
check' :: String -> [String] -> Maybe [String]
check' a b = case b of
  [] -> Nothing
  c : d -> if c == a then Just [a] else (:) c <$> check' a d
check_extension :: String -> Err ()
check_extension a = case takeExtension a of
  ".qc" -> Right ()
  _ -> Left ("File " ++ a ++ " has an invalid extension. You can only load a .qc file.")
check_extension' :: String -> Err ()
check_extension' a = case takeExtension a of
  ".qasm" -> Right ()
  _ -> Left ("File " ++ a ++ " has an invalid extension. You can only write the results to a .qasm file.")
check_extensions :: String -> String -> [String] -> Err ([String], String, String)
check_extensions a b c = case c of
  [] -> ([], a, b) <$ check_extension' b
  d : e -> check_extension a >> (\(f, g, h) -> (a : f, g, h)) <$> check_extensions b d e
check_imports ::
  [String] -> (Files, Locations, Defs, File) -> [(Location', String)] -> IO (Err (Files, Locations, Defs, File))
check_imports a b @ (f, h, l, k) c = case c of
  [] -> return (Right b)
  (d, g) : e -> do
    x <- check a (f, h, l) d g
    case x of
      Left i -> err i
      Right (i, j, m, n) -> check_imports a (i, j, m, context_union k n) e
context_union :: File -> File -> File
context_union (File b i j d) (File f k l h) =
  File (Data.Map.union b f) (Data.Map.union i k) (Data.Map.union j l) (Data.Map.union d h)
defs :: Map' Expression_2
defs = fst <$> defs_and_types
err :: String -> IO (Err t)
err = return <$> Left
eval' :: [String] -> String -> IO (Err String)
eval' a b= do
  c <- check_imports [] (empty, locations, defs, init_type_context) ((,) Language <$> a)
  return (c >>= \(_, e, f, g) -> tokenise_parse_naming_typing_eval e g f b)
main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> putStrLn "Missing command."
    command : arguments -> case command of
      "check" -> case arguments of
        [f] -> case check_extension f of
          Left a -> putStrLn a
          _ -> do
            res <- check [] (empty, locations, defs) Language f
            putStrLn (case res of
              Left e -> e
              _ -> "Library check successful!")
        _ -> putStrLn "Command check expects 1 argument."
      "compile" -> case arguments of
        a : b : g -> case check_extensions a b g of
          Left e -> putStrLn e
          Right (c, d, outp) -> do
            e <- eval' c d
            case e of
              Left f -> putStrLn f
              Right f -> do
                writeFile outp f
                putStrLn "Code generation successful!"
        _ -> putStrLn "Command compile expects at least 2 arguments."
      _ -> putStrLn ("Invalid command " ++ command ++ ".")
naming_typing :: String -> Tree_2 -> (Locations, File, Defs) -> Err (Locations, File, Defs)
naming_typing f a (b, c, g) = naming f a b >>= \(d, e) -> (\(h, i) -> (d, h, i)) <$> typing (Location_1 f) e (c, g)
tokenise_parse_naming_typing_eval :: Locations -> File -> Defs -> String -> Err String
tokenise_parse_naming_typing_eval c (File f g h i) l b =
  (
    parse_expression b >>=
    \e ->
      (
        naming_expression "input" e c >>=
        \j -> type_expr' (Location_1 "input") (f, g, h, i) j >>= \a -> codefile <$> optimise <$> circuit l a))
-----------------------------------------------------------------------------------------------------------------------------