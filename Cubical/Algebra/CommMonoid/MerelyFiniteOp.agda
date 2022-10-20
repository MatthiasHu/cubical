{-# OPTIONS --safe #-}
module Cubical.Algebra.CommMonoid.InfiniteOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Data.Sum as ⊎ using ()

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid.BigOp

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' : Level

module InfiniteOp (M : CommMonoid ℓ) where
  open CommMonoidStr (snd M)

  data HasSum : {I : Type ℓ'} → (I → ⟨ M ⟩ ) → ⟨ M ⟩ → Type {!!} where

    zeroHasSum :
      {I : _} →
      HasSum (const {B = I} ε) ε

    singletonHasSum :
      (x : ⟨ M ⟩) →
      HasSum (const {B = Unit} x) x

    emptyHasSum :
      HasSum ⊥.rec ε

    splitHasSum :
      {I₁ I₂ : Type ℓ'} →
      {f₁ : I₁ → ⟨ M ⟩} →
      {x₁ : ⟨ M ⟩} →
      HasSum f₁ x₁ →
      {f₂ : I₂ → ⟨ M ⟩} →
      {x₂ : ⟨ M ⟩} →
      HasSum f₂ x₂ →
      HasSum (⊎.rec f₁ f₂) (x₁ · x₂)

  finiteSplitHasSum : {!!}
  finiteSplitHasSum = {!!}

  sumUnique : {!!}
  sumUnique = {!!}

  open MonoidBigOp (CommMonoid→Monoid M)

