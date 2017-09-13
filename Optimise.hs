-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
module Optimise where
  import Circuit
  import Data.Bifunctor
  import Typing
  clean_gates ::
    Integer -> (([(Integer, Bool)], [Bool]), (Integer, [Gate])) -> (([(Integer, Bool)], [Bool]), (Integer, [Gate]))
-- TODO: THIS FUNCTION CAN BE REFACTORISED FURTHER. USE ZIPWITH MORE!
  clean_gates cc (r @ ((c, q), (cg, g))) = case g of
    [] -> r
    h : t ->
      let
        ifc cond n = if cond then id else update_c cc n
        iff cnd fc fq = if or cnd then (second (bimap ((+) 1) ((:) h)), (comp_all fc, comp_all fq)) else (id, (id, id))
        ifq cond n = if cond then id else update_q n
      in
        (\(f', (gc, gq)) -> f' (clean_gates cc ((gc c, gq q), (cg - 1, t)))) (case h of
          Unitary g' -> case g' of
            CCX_gate x y z ->
              let
                x' = q !! fromInteger x
                y' = q !! fromInteger y
                z' = q !! fromInteger z
              in
                iff [x', y', z'] [] [ifq x' x, ifq y' y, ifq z' z]
            Double_gate _ x y ->
              let
                x' = q !! fromInteger x
                y' = q !! fromInteger y
              in
                iff [x', y'] [] [ifq x' x, ifq y' y]
            Single_gate _ x -> iff [q !! fromInteger x] [] []
          If_g x _ _ _ y ->
            let
              x' = q !! fromInteger (cc - x - 1)
              y' = (!!) q <$> fromInteger <$> y
            in
              iff (x' : y') [ifc x' x] (zipWith ifq y' y)
          Mea_g x y _ ->
            let
              x' = q !! fromInteger x
              y' = snd (c !! fromInteger (cc - y - 1))
            in
              iff [x', y'] [ifc y' y] [ifq x' x])
  clean_cregs :: Integer -> Integer -> [(Integer, Bool)] -> ([Integer], [(Integer, Integer)])
  clean_cregs m n x = case x of
    [] -> ([], [])
    (c, b) : t -> if b then bimap (c :) ((m, n) :) (clean_cregs (m - 1) (n - 1) t) else clean_cregs (m - 1) n t
  clean_qbits :: Integer -> Integer -> [Bool] -> (Integer, [(Integer, Integer)])
  clean_qbits m n x = case x of
    [] -> (n, [])
    h : t -> if h then second ((m, n) :) (clean_qbits (m + 1) (n + 1) t) else clean_qbits (m + 1) n t
  cleanup :: (Circuit, Integer) -> (Circuit, Integer)
  cleanup (Circuit cc c q cg g, x) = let
    ((c'', q''), (cg', g')) = clean_gates cc (tag_circ cc x (init' c, replicate (fromInteger q) False), (cg, g))
    cc3 = count_cregs c''
    (c', cmap) = clean_cregs (cc - 1) (cc3 - 1) c''
    (qc, qmap) = clean_qbits 0 0 q''
    fc = flip lookup' cmap
    fq = flip lookup' qmap in
      (Circuit cc3 c' qc cg' (transf_gate fc fq <$> g'), fc x)
  comp_all :: [t -> t] -> t -> t
  comp_all = Prelude.foldr (<$>) id
  count_cregs :: [(t, Bool)] -> Integer
  count_cregs x = case x of
    [] -> 0
    (_, h) : t -> (if h then (+ 1) else id) (count_cregs t)
  init' :: [t] -> [(t, Bool)]
  init' = (<$>) (flip (,) False)
  lookup' :: Eq t => t -> [(t, u)] -> u
  lookup' a b = case b of
    [] -> ice
    (c, d) : e -> if c == a then d else lookup' a e
  tag_circ :: Integer -> Integer -> ([(Integer, Bool)], [Bool]) -> ([(Integer, Bool)], [Bool])
  tag_circ cc x = first (update_c cc x)
  optimise :: (Circuit, Integer) -> (Circuit, Integer)
  optimise = cleanup
  transf_gate :: (Integer -> Integer) -> (Integer -> Integer) -> Gate -> Gate
  transf_gate c q g = case g of
    Unitary g' -> Unitary (case g' of
      CCX_gate x y z -> CCX_gate (q x) (q y) (q z)
      Double_gate f x y -> Double_gate f (q x) (q y)
      Single_gate f x -> Single_gate f (q x))
    If_g x y a f z -> If_g (c x) y a f (q <$> z)
    Mea_g x y z -> Mea_g (q x) (c y) z
  update_c :: Integer -> Integer -> [(Integer, Bool)] -> [(Integer, Bool)]
  update_c x y = update_c' (x - y - 1)
  update_c' :: Integer -> [(Integer, Bool)] -> [(Integer, Bool)]
  update_c' x y = case y of
    [] -> ice
    z @ (w, _) : a -> if x == 0 then (w, True) : a else z : update_c' (x - 1) a
  update_q :: Integer -> [Bool] -> [Bool]
  update_q x y = case y of
    [] -> ice
    z : w -> if x == 0 then True : w else z : update_q (x - 1) w
-----------------------------------------------------------------------------------------------------------------------------