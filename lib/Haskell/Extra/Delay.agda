{-# OPTIONS --sized-types #-}

module Haskell.Extra.Delay where

open import Agda.Builtin.Size public

open import Haskell.Prelude
open import Haskell.Prim.Thunk
open import Haskell.Extra.Refinement

private variable
  x y z : a
  @0 i : Size

data Delay (a : Set) (@0 i : Size) : Set where
  now : a → Delay a i
  later : Thunk (Delay a) i → Delay a i

bindDelay : Delay a i → (a → Delay b i) → Delay b i
bindDelay (now x)   f = f x
bindDelay (later x) f = later (λ where .force → bindDelay (x .force) f)

{-# COMPILE AGDA2HS bindDelay inline #-}

instance
  iFunctorDelay : ∀ {i} → Functor (λ a → Delay a i)
  iFunctorDelay {i} = record { DefaultFunctor iDefaultFunctorDelay }
    where
      iDefaultFunctorDelay : DefaultFunctor (λ a → Delay a i)
      iDefaultFunctorDelay = λ where
        .DefaultFunctor.fmap → λ f mx → bindDelay mx (λ x → now (f x))

  iApplicativeDelay : ∀ {i} → Applicative (λ a → Delay a i)
  iApplicativeDelay {i} = record { DefaultApplicative iDefaultApplicativeDelay }
    where
      iDefaultApplicativeDelay : DefaultApplicative (λ a → Delay a i)
      iDefaultApplicativeDelay = λ where
        .DefaultApplicative.pure → now
        .DefaultApplicative._<*>_ → 
          λ mf mx → bindDelay mf (λ f → bindDelay mx (λ x → now (f x)))

  iMonadDelay : ∀ {i} → Monad (λ a → Delay a i)
  iMonadDelay {i} = record { DefaultMonad iDefaultMonadDelay }
    where
      iDefaultMonadDelay : DefaultMonad (λ a → Delay a i)
      iDefaultMonadDelay = λ where
        .DefaultMonad._>>=_ → bindDelay

data HasResult (x : a) : Delay a i → Set where
  now   : HasResult x (now x)
  later : HasResult x (y .force) → HasResult x (later y)

runDelay : {@0 x : a} (y : Delay a ∞) → @0 HasResult x y → a
runDelay (now x) now = x
runDelay (later y) (later p) = runDelay (y .force) p

runDelaySound : {@0 x : a} (y : Delay a ∞) → (@0 hr : HasResult x y) → runDelay y hr ≡ x
runDelaySound (now x) now = refl
runDelaySound (later y) (later hr) = runDelaySound (y .force) hr

-- tryDelay and unDelay cannot and should not be compiled to Haskell,
-- so they are marked as erased.
@0 tryDelay : (y : Delay a ∞) → Nat → Maybe (∃ a (λ x → HasResult x y))
tryDelay (now x)   _       = Just (x ⟨ now ⟩)
tryDelay (later y) zero    = Nothing
tryDelay (later y) (suc n) = fmap (mapRefine later) (tryDelay (y .force) n)

@0 unDelay : (y : Delay a ∞) (n : Nat) → @0 {IsJust (tryDelay y n)} → a
unDelay y n {p} = fromJust (tryDelay y n) {p} .value
