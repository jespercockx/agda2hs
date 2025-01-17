

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
open import Haskell.Law.Eq
open import Haskell.Prim.Natural

case0_of_ : a → (a → b) → b
case0 x of f = f x

{-# COMPILE AGDA2HS case0_of_ inline #-}

recNat : (a : @0 Nat → Set)
       → (z : a 0)
       → (s : (m : Nat) → a m → a (suc m))
       → (n : Nat) → a n
recNat a z s n = ifDec (n ≟ 0)
  (λ where {{refl}} → z)
  (λ {{n≠0}} →
    case0 predNat n n≠0 of λ where
      (m ⟨ refl ⟩) → s m (recNat a z s m))

{-# COMPILE AGDA2HS recNat #-}
