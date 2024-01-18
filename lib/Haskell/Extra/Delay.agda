{-# OPTIONS --sized-types #-}

module Haskell.Extra.Delay where

open import Agda.Builtin.Size public

open import Haskell.Prelude
open import Haskell.Extra.Refinement

private variable
  @0 i : Size
  x y z : a
  
data Delay (a : Set) (@0 i : Size) : Set
record Delay′ (a : Set) (@0 i : Size) : Set

data Delay a i where
  now : a → Delay a i
  later : Delay′ a i → Delay a i

record Delay′ a i where
  coinductive
  field
    force : {j : Size< i} → Delay a j
open Delay′ public

bindDelay : Delay a i → (a → Delay b i) → Delay b i
bindDelay (now x)   f = f x
bindDelay (later x) f = later (λ where .force → bindDelay (x .force) f)

{-# COMPILE AGDA2HS bindDelay inline #-}

instance
  iFunctorDelay : Functor (λ a → Delay a i)
  iFunctorDelay = record { DefaultFunctor iDefaultFunctorDelay }
    where
      iDefaultFunctorDelay : DefaultFunctor (λ a → Delay a i)
      iDefaultFunctorDelay = λ where
        .DefaultFunctor.fmap → λ f mx → bindDelay mx (λ x → now (f x))

  iApplicativeDelay : Applicative (λ a → Delay a i)
  iApplicativeDelay = record { DefaultApplicative iDefaultApplicativeDelay }
    where
      iDefaultApplicativeDelay : DefaultApplicative (λ a → Delay a i)
      iDefaultApplicativeDelay = λ where
        .DefaultApplicative.pure → now
        .DefaultApplicative._<*>_ → 
          λ mf mx → bindDelay mf (λ f → bindDelay mx (λ x → now (f x)))

  iMonadDelay : Monad (λ a → Delay a i)
  iMonadDelay = record { DefaultMonad iDefaultMonadDelay }
    where
      iDefaultMonadDelay : DefaultMonad (λ a → Delay a i)
      iDefaultMonadDelay = λ where
        .DefaultMonad._>>=_ → bindDelay

-- tryDelay and unDelay cannot and should not be compiled to Haskell,
-- so they are marked as erased.
@0 tryDelay : (y : Delay a ∞) → Nat → Maybe a
tryDelay (now x)   _       = Just x
tryDelay (later y) zero    = Nothing
tryDelay (later y) (suc n) = tryDelay (y .force) n

@0 unDelay : (y : Delay a ∞) (n : Nat) → @0 {IsJust (tryDelay y n)} → a
unDelay y n {p} = fromJust _ {p}

data @0 HasResult (x : a) (@0 i : Size) : Delay a i → Set where
  now   : HasResult x i (now x)
  later : ∀ {@0 j : Size< i} {y : Delay′ a i} → HasResult x j (y .force) → HasResult x i (later y)

runDelay : (y : Delay a i) → @0 HasResult x i y → a
runDelay (now x) now = x
runDelay (later y) (later p) = runDelay (y .force) p

-- `bindHasResult y f` should compile to `f y`
bindHasResult : (y : Delay a i) → ((∃ a λ x → HasResult x i y) → Delay b i) → Delay b i
bindHasResult (now x)   f = f (x ⟨ now ⟩)
bindHasResult (later x) f = later λ where 
  .force → bindHasResult (x .force) (f ∘ mapRefine later)

-- `delayHasResult y` should compile to `y`
delayHasResult : (y : Delay a i) → Delay (∃ a λ x → HasResult x i y) i
delayHasResult y = bindHasResult y return
