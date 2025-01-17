
module Haskell.Prim.Natural where

open import Haskell.Prim

open import Haskell.Extra.Refinement

predNat : (n : Nat) → @0 (n ≡ 0 → ⊥) → ∃ Nat λ m → n ≡ suc m
predNat zero    p = magic (p refl)
predNat (suc n) p = n ⟨ refl ⟩