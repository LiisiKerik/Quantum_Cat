-----------------------------------------------------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Optimise where
  import Circuit
  optimise :: (Circuit, Val) -> (Circuit, Val)
  optimise = cleanup
-----------------------------------------------------------------------------------------------------------------------------