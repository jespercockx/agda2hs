{-# OPTIONS --guardedness #-}

module Haskell.Extra.Delay where


open import Haskell.Prelude
open import Haskell.Extra.Refinement

private variable
  x y z : a
  
data Delay (a : Set) : Set
record Delay′ (a : Set) : Set

data Delay a where
  now : a → Delay a
  later : Delay′ a → Delay a

record Delay′ a where
  coinductive
  field
    force : Delay a
open Delay′ public

bindDelay : Delay a → (a → Delay b) → Delay b
bindDelay (now x)   f = f x
bindDelay (later x) f = later (λ where .force → bindDelay (x .force) f)

{-# COMPILE AGDA2HS bindDelay inline #-}

instance
  iFunctorDelay : Functor (λ a → Delay a)
  iFunctorDelay = record { DefaultFunctor iDefaultFunctorDelay }
    where
      iDefaultFunctorDelay : DefaultFunctor (λ a → Delay a)
      iDefaultFunctorDelay = λ where
        .DefaultFunctor.fmap → λ f mx → bindDelay mx (λ x → now (f x))

  iApplicativeDelay : Applicative (λ a → Delay a)
  iApplicativeDelay = record { DefaultApplicative iDefaultApplicativeDelay }
    where
      iDefaultApplicativeDelay : DefaultApplicative (λ a → Delay a)
      iDefaultApplicativeDelay = λ where
        .DefaultApplicative.pure → now
        .DefaultApplicative._<*>_ → 
          λ mf mx → bindDelay mf (λ f → bindDelay mx (λ x → now (f x)))

  iMonadDelay : Monad (λ a → Delay a)
  iMonadDelay = record { DefaultMonad iDefaultMonadDelay }
    where
      iDefaultMonadDelay : DefaultMonad (λ a → Delay a)
      iDefaultMonadDelay = λ where
        .DefaultMonad._>>=_ → bindDelay

-- tryDelay and unDelay cannot and should not be compiled to Haskell,
-- so they are marked as erased.
@0 tryDelay : (y : Delay a) → Nat → Maybe a
tryDelay (now x)   _       = Just x
tryDelay (later y) zero    = Nothing
tryDelay (later y) (suc n) = tryDelay (y .force) n

@0 unDelay : (y : Delay a) (n : Nat) → @0 {IsJust (tryDelay y n)} → a
unDelay y n {p} = fromJust _ {p}

data @0 HasResult (x : a) : Delay a → Set where
  now   : HasResult x (now x)
  later : HasResult x (y .force) → HasResult x (later y)

runDelay : (y : Delay a) → @0 HasResult x y → a
runDelay (now x) now = x
runDelay (later y) (later p) = runDelay (y .force) p

-- `bindHasResult y f` should compile to `f y`
bindHasResult : (y : Delay a) → ((∃ a λ x → HasResult x y) → Delay b) → Delay b
bindHasResult (now x)   f = f (x ⟨ now ⟩)
bindHasResult (later x) f = later λ where 
  .force → bindHasResult (x .force) (f ∘ mapRefine later)

-- `delayHasResult y` should compile to `y`
delayHasResult : (y : Delay a) → Delay (∃ a λ x → HasResult x y)
delayHasResult y = bindHasResult y return
