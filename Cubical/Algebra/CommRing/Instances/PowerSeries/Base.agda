
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.PowerSeries.Base where

{-
The ring of power series over a commutative ring
================================================
-}

-- TODO: clean up imports
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty.Base
open import Cubical.Data.Bool
open import Cubical.Data.FinData

open import Cubical.Algebra.Group
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps using (module Sum)

private
  variable
    ℓ : Level

module Preliminaries where

  partitionsIntoTwo : (n : ℕ) → FinVec (ℕ × ℕ) (suc n)
  partitionsIntoTwo zero = replicateFinVec 1 (zero , zero)
  partitionsIntoTwo (suc n) =
    λ{ zero → (zero , suc n)
     ; (suc i) →
         let (k , l) = partitionsIntoTwo n i
         in (suc k , l) }

module _
  (R : CommRing ℓ)
  where

  open CommRingStr (snd R)
  open Sum (CommRing→Ring R)
  open Preliminaries

  powerSeriesCommRingStr : CommRingStr (ℕ → ⟨ R ⟩)
  CommRingStr.0r powerSeriesCommRingStr = const 0r
  CommRingStr.1r powerSeriesCommRingStr = λ{ zero → 1r ; (suc _) → 0r }
  CommRingStr._+_ powerSeriesCommRingStr f g = λ n → f n + g n
  CommRingStr._·_ powerSeriesCommRingStr f g = λ n → ∑ ((λ{ (k , l) → f k · g l }) ∘ partitionsIntoTwo n)
  CommRingStr.-_ powerSeriesCommRingStr f = -_ ∘ f
  CommRingStr.isCommRing powerSeriesCommRingStr = {!!}
