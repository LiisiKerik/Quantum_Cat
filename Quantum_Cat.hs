-----------------------------------------------------------------------------------------------------------------------------
import Quantum_Cat'
import System.Directory
import System.Environment
import System.FilePath
inp_file :: String -> IO(Either(String)(String))
inp_file(name_qc) = case splitExtension(name_qc) of
  (_, ".qc") -> do
    try_file <- findFile([""])(name_qc)
    case try_file of
      Just(file) -> Right <$> readFile(file)
      Nothing -> return(Left("File error. Failed to find the library."))
  _ -> return(Left("File error. You can only use a .qc file as a library."))
main :: IO()
main = do
  args <- getArgs
  case args of
    [name_qc] -> do
      find_file <- inp_file(name_qc)
      putStrLn(case find_file of
        Left(err) -> err
        Right(code) -> case check_file(code) of
          Just(err) -> err
          Nothing -> "Library parses and typechecks successfully!")
    [name_qc, inp, name_qasm] -> do
      find_file <- inp_file(name_qc)
      case find_file of
        Left(err) -> putStrLn(err)
        Right(code) -> case quantum_Cat(code)(inp) of
          Left(err) -> putStrLn(err)
          Right(res) -> case splitExtension(name_qasm) of
            (_, ".qasm") -> do
              putStrLn("Code generation successful!")
              writeFile(name_qasm)(res)
            _ -> putStrLn("File error. You can only write the circuit to a .qasm file.")
    _ ->
      putStrLn(
        "Input error." ++
        "Wrong number of command line arguments." ++
        "If you want to check a library input the name of the library." ++
        "If you want to generate code, input the name of the library, the expression, and the name of the output file.")
-----------------------------------------------------------------------------------------------------------------------------