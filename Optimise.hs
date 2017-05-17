-----------------------------------------------------------------------------------------------------------------------------
module Optimise where
  import Circuit
  cleanup :: (Circuit, Val) -> (Circuit, [Integer])
  cleanup(circ, x @ (Arr_val(y))) =
    (Circuit(c_count)(q_count)(rem_gates(c_map)(q_map)(g)), transf_output(c_map)((\(Cbit_pointer(n)) -> n) <$> y)) where
      Tagged_circuit(c)(q)(g) = tag_circ(circ)(x)
      (c_map, c_count) = offset_map(0)(c)
      (q_map, q_count) = offset_map(0)(q)
  cleanup(_) = error("Internal compiler error. Generated a malformed circuit.")
  rem_gates :: [(Integer, Integer)] -> [(Integer, Integer)] -> [(Gate, Bool)] -> [Gate]
  rem_gates(c)(q)(g) = case g of
    [] -> []
    (h, b) : t -> (if b then ((case h of
      Cnot_g(x)(y) -> Cnot_g(bit_lookup(q)(x))(bit_lookup(q)(y))
      Mea_g(x)(y) -> Mea_g(bit_lookup(q)(x))(bit_lookup(c)(y))
      Single_g(f)(x) -> Single_g(f)(bit_lookup(q)(x))) :) else id)(rem_gates(c)(q)(t))
  transf_output :: [(Integer, Integer)] -> [Integer] -> [Integer]
  transf_output = (<$>) <$> bit_lookup
-----------------------------------------------------------------------------------------------------------------------------