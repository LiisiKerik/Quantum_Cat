-----------------------------------------------------------------------------------------------------------------------------
{-# LANGUAGE TupleSections #-}
module Circuit where
  import Data.Bifunctor
  import Tree
  import Typing
  data Circuit = Circuit(Integer)([Integer])(Integer)([Gate]) deriving(Show)
  data Gate = Cnot_g(Integer)(Integer) | Mea_g(Integer)(Integer)(Integer) | Single_g(String)(Integer) deriving(Show)
  data Val =
    Alg_val(String)([Val]) |
    Arr_val([Val]) |
    Creg_pointer(Integer) |
    Func_val([(String, Either(Def_tree'')(Val))] -> Circuit -> Val -> (Circuit, Val)) |
    Int_val(Integer) |
    Qbit_pointer(Integer) |
    Struct_val([Val])
  instance Show Val where
    show x = case x of
      Alg_val(y)(z) -> "Alg_val " ++ show y ++ show z
      Arr_val(y) -> "Arr_val " ++ show y
      Creg_pointer(y) -> "Creg_pointer " ++ show y
      Func_val(_) -> "Func_val FUNCTION"
      Int_val(y) -> "Int_val " ++ show y
      Qbit_pointer(y) -> "Qbit_pointer " ++ show y
      Struct_val(y) -> "Struct_val " ++ show y
  add_to_context :: [(String, Either(Def_tree'')(Val))] -> [String] -> [Val] -> [(String, Either(Def_tree'')(Val))]
  add_to_context(d)([])([]) = d
  add_to_context(d)(x : y)(z : w) = (x, Right(z)) : add_to_context(d)(y)(w)
  add_to_context(_)(_)(_) = error("Internal compiler error. Failed pattern match due to wrong number of variables.")
  circ_lookup :: [(Integer, Integer)] -> Integer -> Integer
  circ_lookup(x)(y) = unsafe_lookup(x)(y)("Internal compiler error. Bit or register lookup failure.")
  circuit :: [(String, Def_tree'')] -> Expression_tree'' -> Either(String)(Circuit, Val)
  circuit(d)(e) = return(circuit'(second(Left) <$> d)(Circuit(0)([])(0)([]))(e)) <$> res_bits(e)
  circuit' :: [(String, Either(Def_tree'')(Val))] -> Circuit -> Expression_tree'' -> (Circuit, Val)
  circuit'(d)(circ @ (Circuit(cc)(c)(q)(g)))(Expression_tree''(_)(e)(_)) = case e of
    Alg''(x)(e') -> eval_struct(Alg_val(x))(d)(circ)(e')
    App''(e1)(e2) -> f(d)(circ')(x) where
      (_, Func_val(f)) = circuit'(d)(circ)(e1)
      (circ', x) = circuit'(d)(circ)(e2)
    Cnot'' ->
      func_val
        (circ)
        (pure_func
          (\(Qbit_pointer(x)) ->
          \(Circuit(cc')(c')(q')(g')) ->
          \(p @ (Qbit_pointer(y))) ->
            (Circuit(cc')(c')(q')(Cnot_g(x)(y) : g'), p)))
    Field''(n) -> func_val(circ)(\circ' -> \(Struct_val(x)) -> (circ', x !! fromInteger(n)))
    Fun''(x)(e') -> (circ, Func_val(\d' -> \circ' -> \x' -> circuit'((x, Right(x')) : d')(circ')(e')))
    Int_expr''(n) -> (circ, Int_val(n))
    Lift''(_)(m) -> case m of
      Int_constant(n) ->
        func_val(circ)(\circ' -> \x -> second(Arr_val)(uncurry(replicate_circuit(circ')(n))(cleanup(circ', x))))
      _ -> error("Internal compiler error. Found a free integer type variable during code generation.")
    Map''{} ->
      func_val
        (circ)
        (
          \circ' ->
          \(Func_val(f)) ->
            (circ', Func_val(\d' -> \circ'' -> \(Arr_val(x)) -> second(Arr_val)(map_help(f)(d')(circ'')(x)))))
    Match''(e')(m) -> case circuit'(d)(circ)(e') of
      (circ', Alg_val(x)(y)) -> let
        (z, e'') = find_case(m)(x) in
          circuit'(add_to_context(d)(z)(y))(circ')(e'')
      _ -> error("Internal compiler error. Match expression got something that is not an algebraic structure as parameter.")
    Mes''{} ->
      func_val
        (circ)
        (
          \(Circuit(cc')(c')(q')(g')) ->
          \(Arr_val(x)) ->
            ((\(g'', c'') -> Circuit(cc' + 1)(c'' : c')(q')(g''))(mes_help(cc')(g')(0)(x)), Creg_pointer(cc')))
    Name''(x)(t)(n) -> case unsafe_lookup(d)(x)("Internal compiler error. Found an undefined variable.") of
      Left(Def_tree''(_)(Bind(b)(_))(e')) -> circuit'(d)(circ)((case b of
        Global(v)(w) -> type_application(zip(v)(t))(zip(w)(n))
        Local -> id)(e'))
      Right(v) -> (circ, v)
    Single_qbit_def(f) -> single_gate(circ)(f)
    Str''(e') -> eval_struct(Struct_val)(d)(circ)(e')
    Take'' -> (Circuit(cc)(c)(q + 1)(g), Qbit_pointer(q))
  clean_cregs :: Integer -> Integer -> [(Integer, Bool)] -> ([Integer], [(Integer, Integer)])
  clean_cregs(m)(n)(x) = case x of
    [] -> ([], [])
    (c, b) : t -> if b then bimap(c :)((m, n) :)(clean_cregs(m - 1)(n - 1)(t)) else clean_cregs(m - 1)(n)(t)
  clean_gates :: Integer -> (([(Integer, Bool)], [Bool]), [Gate]) -> (([(Integer, Bool)], [Bool]), [Gate])
  clean_gates(cc)(r @ ((c, q), g)) = case g of
    [] -> r
    h : t -> let
      f(f', (gc, gq)) = f'(clean_gates(cc)((gc(c), gq(q)), t))
      add_gate = second(h :) in
        case h of
          Cnot_g(x)(y) -> let
            y' = q !! fromInteger(y) in
              f
                (if q !! fromInteger(x) then
                  (add_gate, (id, if y' then id else update_q(y)))
                else
                  second(id, )(if y' then (add_gate, update_q(x)) else (id, id)))
          Mea_g(x)(y)(_) -> let
            y' = snd(c !! fromInteger(cc - y - 1)) in
              f
                (if q !! fromInteger(x) then
                  (add_gate, (if y' then id else update_c(cc)(y), id))
                else
                  second(id, )(if y' then (add_gate, update_q(x)) else (id, id)))
          Single_g(_)(x) -> f(if q !! fromInteger(x) then add_gate else id, (id, id))
  clean_qbits :: Integer -> Integer -> [Bool] -> (Integer, [(Integer, Integer)])
  clean_qbits(m)(n)(x) = case x of
    [] -> (n, [])
    h : t -> if h then second((m, n) :)(clean_qbits(m + 1)(n + 1)(t)) else clean_qbits(m + 1)(n)(t)
  cleanup' :: Integer -> [(Integer, Bool)] -> [Bool] -> [Gate] -> Val -> (Circuit, Val)
  cleanup'(cc)(c)(q)(g)(x) =
    (Circuit(cc')(c')(qc)(transf_gates(fc)(fq)(g)), transf_val(fc)(fq)(x)) where
      cc' = count_cregs(c)
      (c', cmap) = clean_cregs(cc - 1)(cc' - 1)(c)
      (qc, qmap) = clean_qbits(0)(0)(q)
      fc = circ_lookup(cmap)
      fq = circ_lookup(qmap)
  cleanup :: (Circuit, Val) -> (Circuit, Val)
  cleanup(Circuit(cc)(c)(q)(g), x) = cleanup'(cc)(c'')(q'')(g')(x) where
    ((c'', q''), g') = clean_gates(cc)(tag_circ(cc)(init'(c), replicate(fromInteger(q))(False))(x), g)
  count_cregs :: [(t, Bool)] -> Integer
  count_cregs(x) = case x of
    [] -> 0
    (_, h) : t -> (if h then (+ 1) else id)(count_cregs(t))
  eval_struct :: ([Val] -> Val) -> [(String, Either(Def_tree'')(Val))] -> Circuit -> [Expression_tree''] -> (Circuit, Val)
  eval_struct(f)(d)(c)(e) = second(f)(eval_struct'(d)(c)(e))
  eval_struct' :: [(String, Either(Def_tree'')(Val))] -> Circuit -> [Expression_tree''] -> (Circuit, [Val])
  eval_struct'(d)(c)(e) = case e of
    [] -> (c, [])
    h : t -> second(h' :)(eval_struct'(d)(c')(t)) where
      (c', h') = circuit'(d)(c)(h)
  find_case :: [Match_case''] -> String -> ([String], Expression_tree'')
  find_case(x)(y) = case x of
    [] -> error("Internal compiler error. Failed algebraic data type matching.")
    Match_case''(z)(w)(a) : b -> if z == y then (w, a) else find_case(b)(y)
  func_val :: Circuit -> (Circuit -> Val -> (Circuit, Val)) -> (Circuit, Val)
  func_val(circ)(f) = (circ, Func_val(return(f)))
  init' :: [t] -> [(t, Bool)]
  init' = (<$>)(, False)
  map_help ::
    ([(String, Either(Def_tree'')(Val))] -> Circuit -> Val -> (Circuit, Val)) ->
    [(String, Either(Def_tree'')(Val))] ->
    Circuit ->
    [Val] ->
    (Circuit, [Val])
  map_help(f)(d)(c)(v) = case v of
    [] -> (c, [])
    h : t -> second(h' :)(map_help(f)(d)(c')(t)) where
      (c', h') = f(d)(c)(h)
  mes_help :: Integer -> [Gate] -> Integer -> [Val] -> ([Gate], Integer)
  mes_help(m)(g)(n)(x) = case x of
    [] -> (g, n)
    h : t -> case h of
      Qbit_pointer(y) -> mes_help(m)(Mea_g(y)(m)(n) : g)(n + 1)(t)
      _ -> error("Internal compiler error. Tried to measure something that is not a qbit.")
  offset_gate :: Integer -> Integer -> Gate -> Gate
  offset_gate(c)(q)(g) = case g of
    Cnot_g(x)(y) -> Cnot_g(x + q)(y + q)
    Mea_g(x)(y)(z) -> Mea_g(x + q)(y + c)(z)
    Single_g(f)(x) -> Single_g(f)(x + q)
  offset_val :: Integer -> Integer -> Val -> Val
  offset_val(c)(q)(v) = let
    offset' = (<$>)(offset_val(c)(q)) in
      case v of
        Alg_val(x)(y) -> Alg_val(x)(offset'(y))
        Arr_val(x) -> Arr_val(offset'(x))
        Creg_pointer(x) -> Creg_pointer(x + c)
        Qbit_pointer(x) -> Qbit_pointer(x + q)
        Struct_val(x) -> Struct_val(offset'(x))
        _ -> v
  pure_func :: (Val -> Circuit -> Val -> (Circuit, Val)) -> Circuit -> Val -> (Circuit, Val)
  pure_func(f)(c)(x) = func_val(c)(f x)
  replicate_circuit :: Circuit -> Integer -> Circuit -> Val -> (Circuit, [Val])
  replicate_circuit(circ @ (Circuit(cc)(c)(q)(g)))(n)(circ' @ (Circuit(cc')(c')(q')(g')))(v) =
    if n == 0 then
      (circ, [])
    else
      second
        (offset_val(cc)(q)(v) :)
        (replicate_circuit(Circuit(cc + cc')(c' ++ c)(q + q')((offset_gate(cc)(q) <$> g') ++ g))(n - 1)(circ')(v))
  res_bits :: Expression_tree'' -> Either(String)(Integer)
  res_bits(Expression_tree''(_)(_)(Creg(Int_constant(n)))) = Right(n)
  res_bits(_) = Left("Circuit generation error. Circuit can only be generated for an expression of type Creg{n}.")
  single_gate :: Circuit -> String -> (Circuit, Val)
  single_gate(circ)(f) =
    func_val(circ)(\(Circuit(n)(c)(q)(g)) -> \p @ (Qbit_pointer(x)) -> (Circuit(n)(c)(q)(Single_g(f)(x) : g), p))
  tag_arr :: Integer -> ([(Integer, Bool)], [Bool]) -> [Val] -> ([(Integer, Bool)], [Bool])
  tag_arr(cc)(t)(x) = case x of
    [] -> t
    y : z -> tag_arr(cc)(tag_circ(cc)(t)(y))(z)
  tag_circ :: Integer -> ([(Integer, Bool)], [Bool]) -> Val -> ([(Integer, Bool)], [Bool])
  tag_circ(cc)(t @ (c, q))(x) = let
    ta = tag_arr(cc)(t) in
      case x of
        Alg_val(_)(y) -> ta(y)
        Arr_val(y) -> ta(y)
        Creg_pointer(y) -> (update_c(cc)(y)(c), q)
        Qbit_pointer(y) -> (c, update_q(y)(q))
        Struct_val(y) -> ta(y)
        _ -> t
  transf_gates :: (Integer -> Integer) -> (Integer -> Integer) -> [Gate] -> [Gate]
  transf_gates(c)(q)(g) = case g of
    [] -> []
    h : t -> ((case h of
      Cnot_g(x)(y) -> Cnot_g(q(x))(q(y))
      Mea_g(x)(y)(z) -> Mea_g(q(x))(c(y))(z)
      Single_g(f)(x) -> Single_g(f)(q(x))) :)(transf_gates(c)(q)(t))
  transf_val :: (Integer -> Integer) -> (Integer -> Integer) -> Val -> Val
  transf_val(c)(q)(x) = let
    f = (<$>)(transf_val(c)(q)) in
      case x of
        Alg_val(y)(z) -> Alg_val(y)(f(z))
        Arr_val(y) -> Arr_val(f(y))
        Creg_pointer(y) -> Creg_pointer(c(y))
        Qbit_pointer(y) -> Qbit_pointer(q(y))
        Struct_val(y) -> Struct_val(f(y))
        _ -> x
  type_application :: [(String, Type)] -> [(String, Int_branch)] -> Expression_tree'' -> Expression_tree''
  type_application(t)(u)(Expression_tree''(l)(e)(ty)) = Expression_tree''(l)(type_application'(t)(u)(e))(type_repl(t)(u)(ty))
  type_application' :: [(String, Type)] -> [(String, Int_branch)] -> Expression_branch'' -> Expression_branch''
  type_application'(t)(u)(e) = case e of
    App''(e1)(e2) -> App''(type_application(t)(u)(e1))(type_application(t)(u)(e2))
    Fun''(x)(e') -> Fun''(x)(type_application(t)(u)(e'))
    Lift''(v)(n) -> Lift''(type_repl(t)(u)(v))(type_int_repl(u)(n))
    Map''(v)(w)(n) -> Map''(type_repl(t)(u)(v))(type_repl(t)(u)(w))(type_int_repl(u)(n))
    Name''(x)(v)(n) -> Name''(x)(type_repl(t)(u) <$> v)(type_int_repl(u) <$> n)
    _ -> e
  type_int_repl :: [(String, Int_branch)] -> Int_branch -> Int_branch
  type_int_repl(x)(y) = case y of
    Int_constant(z) -> Int_constant(z)
    Int_variable(z) -> unsafe_lookup(x)(z)("Internal compiler error. Failed to perform integer type variable replacement.")
  type_repl :: [(String, Type)] -> [(String, Int_branch)] -> Type -> Type
  type_repl(x)(y)(z) = case z of
    Arr(w)(a) -> Arr(type_repl(x)(y)(w))(type_int_repl(y)(a))
    Function_type''(w)(a) -> Function_type''(type_repl(x)(y)(w))(type_repl(x)(y)(a))
    Typevar(w) -> unsafe_lookup(x)(w)("Internal compiler error. Failed to perform type variable replacement.")
    _ -> z
  update_c :: Integer -> Integer -> [(Integer, Bool)] -> [(Integer, Bool)]
  update_c(x)(y) = update_c'(x - y - 1)
  update_c' :: Integer -> [(Integer, Bool)] -> [(Integer, Bool)]
  update_c'(x)(y) = case y of
    [] -> error("Internal compiler error. Tried to perform relevancy update on a non-existing creg.")
    z @ (w, _) : a -> if x == 0 then (w, True) : a else z : update_c'(x - 1)(a)
  update_q :: Integer -> [Bool] -> [Bool]
  update_q(x)(y) = case y of
    [] -> error("Internal compiler error. Tried to perform relevancy update on a non-existing qbit.")
    z : w -> if x == 0 then True : w else z : update_q(x - 1)(w)
-----------------------------------------------------------------------------------------------------------------------------