module NatRec where

import Numeric.Natural (Natural)

recNat :: a -> (Natural -> a -> a) -> Natural -> a
recNat z s n = if n == 0 then z else \ m -> s m (recNat z s m)

