-----------------------------------------------------------------------------------------------------------------------------
{-# LANGUAGE TupleSections #-}
module Circuit where
  import Data.Bifunctor
  import Tree
  import Typing
  data Circuit = Circuit(Integer)(Integer)([Gate])
  data Gate = Cnot_g(Integer)(Integer) | Mea_g(Integer)(Integer) | Single_g(String)(Integer) deriving(Show)
  data Tagged_circuit = Tagged_circuit([(Integer, Bool)])([(Integer, Bool)])([(Gate, Bool)])
  data Val =
    Alg_val(String)([Val]) |
    Arr_val([Val]) |
    Cbit_pointer(Integer) |
    Func_val([(String, Either(Def_tree'')(Val))] -> Circuit -> Val -> (Circuit, Val)) |
    Int_val(Integer) |
    Qbit_pointer(Integer) |
    Struct_val([Val])
  add_gate :: (Gate, Bool) -> Tagged_circuit -> Tagged_circuit
  add_gate(g)(Tagged_circuit(c)(q)(g')) = Tagged_circuit(c)(q)(g : g')
  add_to_context :: [(String, Either(Def_tree'')(Val))] -> [String] -> [Val] -> [(String, Either(Def_tree'')(Val))]
  add_to_context(d)([])([]) = d
  add_to_context(d)(x : y)(z : w) = (x, Right(z)) : add_to_context(d)(y)(w)
  add_to_context(_)(_)(_) = error("Internal compiler error. Failed pattern match due to wrong number of variables.")
  bit_lookup :: [(Integer, t)] -> Integer -> t
  bit_lookup(m)(i) = unsafe_lookup(m)(i)("Internal compiler error. Found an undefined bit.")
  circuit :: [(String, Def_tree'')] -> Expression_tree'' -> Either(String)(Circuit, Val)
  circuit(d)(e) = case res_bits(e) of
    Just(_) -> Right(circuit'(second(Left) <$> d)(Circuit(0)(0)([]))(e))
    Nothing -> Left("Circuit generation error. Circuit can only be generated for an expression of type Arr[Cbit]{n}.")
  circuit' :: [(String, Either(Def_tree'')(Val))] -> Circuit -> Expression_tree'' -> (Circuit, Val)
  circuit'(d)(circ @ (Circuit(c)(q)(g)))(Expression_tree''(_)(e)(_)) = case e of
    Alg''(x)(e') -> eval_struct(Alg_val(x))(d)(circ)(e')
    App''(e1)(e2) -> f(d)(circ')(x) where
      (_, Func_val(f)) = circuit'(d)(circ)(e1)
      (circ', x) = circuit'(d)(circ)(e2)
    Cnot'' ->
      func_val(
        circ)(
        pure_func(
          \(Qbit_pointer(x)) ->
          \(Circuit(c')(q')(g')) ->
          \(p @ (Qbit_pointer(y))) ->
          (Circuit(c')(q')(Cnot_g(x)(y) : g'), p)))
    Field''(i) -> func_val(circ)(\circ' -> \(Struct_val(x)) -> (circ', x !! fromInteger(i)))
    Fun''(x)(e') -> (circ, Func_val(\d' -> \circ' -> \x' -> circuit'((x, Right(x')) : d')(circ')(e')))
    Int_expr''(n) -> (circ, Int_val(n))
    Lift''(_)(v) -> case v of
      Int_constant(n) ->
        func_val(circ)(\circ' -> \x -> second(Arr_val)(replicate_circuit(n)(replicate_f(tag_circ(circ')(x)))(circ')(x)))
      _ -> error("Internal compiler error. Found a free integer type variable during code generation.")
    Map''(_)(_)(_) ->
      func_val(
        circ)
        (
          \circ' ->
          \(Func_val(f)) ->
          (circ', Func_val(\d' -> \circ'' -> \(Arr_val(x)) -> second(Arr_val)(map_help(f)(d')(circ'')(x)))))
    Match''(e')(cases) -> case circuit'(d)(circ)(e') of
      (circ', Alg_val(x)(y)) -> let
        (z, e'') = find_case(cases)(x) in
          circuit'(add_to_context(d)(z)(y))(circ')(e'')
      _ -> error("Internal compiler error. Match expression got something that is not an algebraic structure as parameter.")
    Mes'' ->
      func_val(
        circ)(
        \(Circuit(c')(q')(g')) -> \(Qbit_pointer(x)) -> (Circuit(c' + 1)(q')(Mea_g(x)(c') : g'), Cbit_pointer(c')))
    Name''(x)(t)(n) -> case unsafe_lookup(d)(x)("Internal compiler error. Found an undefined variable.") of
      Left(Def_tree''(_)(Bind(b)(_))(e')) -> circuit'(d)(circ)((case b of
        Global(v)(w) -> type_application(zip(v)(t))(zip(w)(n))
        Local -> id)(e'))
      Right(v) -> (circ, v)
    Single_qbit_def(f) -> single_gate(circ)(f)
    Str''(e') -> eval_struct(Struct_val)(d)(circ)(e')
    Take'' -> (Circuit(c)(q + 1)(g), Qbit_pointer(q))
  eval_struct :: ([Val] -> Val) -> [(String, Either(Def_tree'')(Val))] -> Circuit -> [Expression_tree''] -> (Circuit, Val)
  eval_struct(f)(d)(c)(e) = second(f)(eval_struct'(d)(c)(e))
  eval_struct' :: [(String, Either(Def_tree'')(Val))] -> Circuit -> [Expression_tree''] -> (Circuit, [Val])
  eval_struct'(d)(c)(e) = case e of
    [] -> (c, [])
    h : t -> second(h' :)(eval_struct'(d)(c')(t)) where
      (c', h') = circuit'(d)(c)(h)
  find_case :: [Match_case''] -> String -> ([String], Expression_tree'')
  find_case(x)(y) = case x of
    [] -> error("Internal type error. Failed algebraic data type matching.")
    Match_case''(z)(w)(a) : b -> if z == y then (w, a) else find_case(b)(y)
  find_relevant :: Tagged_circuit -> Tagged_circuit
  find_relevant(Tagged_circuit(c)(q)(g)) = case g of
    [] -> Tagged_circuit(c)(q)([])
    h' @ (h, _) : t -> case h of
      Cnot_g(x)(y) -> case (bit_lookup(q)(x), bit_lookup(q)(y)) of
        (False, False) -> add_gate(h')(find_relevant(Tagged_circuit(c)(q)(t)))
        (False, True) -> add_gate(h, True)(find_relevant(Tagged_circuit(c)(upd(q)(x))(t)))
        (True, False) -> add_gate(h, True)(find_relevant(Tagged_circuit(upd(q)(y))(q)(t)))
        (True, True) -> add_gate(h, True)(find_relevant(Tagged_circuit(c)(q)(t)))
      Mea_g(x)(y) -> case (bit_lookup(q)(x), bit_lookup(c)(y)) of
        (False, False) -> add_gate(h')(find_relevant(Tagged_circuit(c)(q)(t)))
        (False, True) -> add_gate(h, True)(find_relevant(Tagged_circuit(c)(upd(q)(x))(t)))
        (True, False) -> add_gate(h, True)(find_relevant(Tagged_circuit(upd(c)(y))(q)(t)))
        (True, True) -> add_gate(h, True)(find_relevant(Tagged_circuit(c)(q)(t)))
      Single_g(_)(x) -> add_gate(h, bit_lookup(q)(x))(find_relevant(Tagged_circuit(c)(q)(t)))
  func_val :: Circuit -> (Circuit -> Val -> (Circuit, Val)) -> (Circuit, Val)
  func_val(circ)(f) = (circ, Func_val(return(f)))
  init_circ :: Circuit -> Tagged_circuit
  init_circ(Circuit(c)(q)(g)) = Tagged_circuit(init_int(c))(init_int(q))((, False) <$> g)
  init_int :: Integer -> [(Integer, Bool)]
  init_int(x) = [(i, False) | i <- [0 .. x - 1]]
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
  offset_map :: Integer -> [(Integer, Bool)] -> ([(Integer, Integer)], Integer)
  offset_map(n)(m) = case m of
    [] -> ([], n)
    (i, b) : t -> if b then first((i, n) :)(offset_map(n + 1)(t)) else offset_map(n)(t)
  offset_value :: [(Integer, Integer)] -> [(Integer, Integer)] -> Val -> Val
  offset_value(c)(q)(x) = case x of
    Arr_val(y) -> Arr_val(offset_value(c)(q) <$> y)
    Cbit_pointer(y) -> Cbit_pointer(bit_lookup(c)(y))
    Qbit_pointer(y) -> Qbit_pointer(bit_lookup(q)(y))
    Struct_val(y) -> Arr_val(offset_value(c)(q) <$> y)
    _ -> x
  pure_func :: (Val -> Circuit -> Val -> (Circuit, Val)) -> Circuit -> Val -> (Circuit, Val)
  pure_func(f)(c)(x) = func_val(c)(f x)
  replicate_circuit :: Integer -> (Circuit -> Val -> (Circuit, Val)) -> Circuit -> Val -> (Circuit, [Val])
  replicate_circuit(n)(f)(c)(v) = if n == 0 then (c, []) else second(v' :)(replicate_circuit(n - 1)(f)(c')(v)) where
    (c', v') = f(c)(v)
  replicate_f :: Tagged_circuit -> Circuit -> Val -> (Circuit, Val)
  replicate_f(Tagged_circuit(c')(q')(g'))(Circuit(c)(q)(g))(v) =
    (Circuit(c3)(q3)(transf_gates(g)(c'')(q'')(g')), offset_value(c'')(q'')(v)) where
      (c'', c3) = offset_map(c)(c')
      (q'', q3) = offset_map(q)(q')
  res_bits :: Expression_tree'' -> Maybe(Integer)
  res_bits(Expression_tree''(_)(_)(Arr(Cbit)(Int_constant(n)))) = Just(n)
  res_bits(_) = Nothing
  single_gate :: Circuit -> String -> (Circuit, Val)
  single_gate(circ)(f) =
    func_val(circ)(\(Circuit(c)(q)(g)) -> \p @ (Qbit_pointer(x)) -> (Circuit(c)(q)(Single_g(f)(x) : g), p))
  tag_arr :: Tagged_circuit -> [Val] -> Tagged_circuit
  tag_arr(c)(v) = case v of
    [] -> c
    h : t -> tag_arr(tagged_circ(c)(h))(t)
  tag_circ :: Circuit -> Val -> Tagged_circuit
  tag_circ(c) = tagged_circ(init_circ(c))
  tagged_circ :: Tagged_circuit -> Val -> Tagged_circuit
  tagged_circ(circ @ (Tagged_circuit(c)(q)(g)))(x) = case x of
    Arr_val(y) -> tag_arr(circ)(y)
    Cbit_pointer(y) -> find_relevant(Tagged_circuit(upd(c)(y))(q)(g))
    Qbit_pointer(y) -> find_relevant(Tagged_circuit(c)(upd(q)(y))(g))
    Struct_val(y) -> tag_arr(circ)(y)
    _ -> circ
  transf_gate :: [(Integer, Integer)] -> [(Integer, Integer)] -> Gate -> Gate
  transf_gate(c)(q)(g) = case g of
    Cnot_g(x)(y) -> Cnot_g(bit_lookup(q)(x))(bit_lookup(q)(y))
    Mea_g(x)(y) -> Mea_g(bit_lookup(q)(x))(bit_lookup(c)(y))
    Single_g(f)(x) -> Single_g(f)(bit_lookup(q)(x))
  transf_gates :: [Gate] -> [(Integer, Integer)] -> [(Integer, Integer)] -> [(Gate, Bool)] -> [Gate]
  transf_gates(g)(c)(q)(g') = case g' of
    [] -> g
    (h, b) : t -> if b then transf_gate(c)(q)(h) : transf_gates(g)(c)(q)(t) else transf_gates(g)(c)(q)(t)
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
  upd :: [(Integer, Bool)] -> Integer -> [(Integer, Bool)]
  upd([])(_) = error("Internal compiler error. Tried to perform relevancy update on a non-existing bit.")
  upd(p @ (i, _) : t)(y) = if i == y then (i, True) : t else p : upd(t)(y)
-----------------------------------------------------------------------------------------------------------------------------