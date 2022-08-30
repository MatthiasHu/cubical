
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
open import Cubical.Data.Nat using (ℕ; zero; suc; caseNat)
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

  private
    partitionSum : ℕ → (ℕ → ℕ → ⟨ R ⟩) → ⟨ R ⟩
    partitionSum n f = ∑ (uncurry f ∘ partitionsIntoTwo n)

    partitionSumFlip : (n : ℕ) (f : ℕ → ℕ → ⟨ R ⟩) → partitionSum n f ≡ partitionSum n (flip f)
    partitionSumFlip zero f = refl
    partitionSumFlip (suc n) f =
      partitionSum (suc n) f  ≡⟨⟩
      ∑ (λ{ zero → uncurry f (partitionsIntoTwo (suc n) zero)
          ; suc i → uncurry f (partitionsIntoTwo (suc n) (suc i))})  ≡⟨ {!!} ⟩
      partitionSum (suc n) (flip f)  ∎

--  private
--    ∑[+=]-syntax : ℕ → (ℕ → ℕ → ⟨ R ⟩) → ⟨ R ⟩
--    ∑[+=]-syntax n v = ∑ ((λ(k , l) → v k l) ∘ partitionsIntoTwo n)
--    syntax ∑[+=]-syntax n (λ k → λ l → v) = ∑[ k + l == n ] v
--    syntax ∑ (λ i → v) = ∑[ i ] v
--    syntax ∑ ((λ p → v ) ∘ partitionsIntoTwo n) = ∑[ p == n ] v

  powerSeriesCommRingStr : CommRingStr (ℕ → ⟨ R ⟩)
  module ps = CommRingStr powerSeriesCommRingStr
  CommRingStr.0r powerSeriesCommRingStr = const 0r
  CommRingStr.1r powerSeriesCommRingStr = caseNat 1r 0r
  CommRingStr._+_ powerSeriesCommRingStr f g = λ n → f n + g n
  CommRingStr._·_ powerSeriesCommRingStr f g = λ n → ∑ ((λ(k , l) → f k · g l) ∘ partitionsIntoTwo n)
  CommRingStr.-_ powerSeriesCommRingStr f = -_ ∘ f
  CommRingStr.isCommRing powerSeriesCommRingStr = makeIsCommRing
    (isSet→ is-set)
    (λ f g h → funExt (λ n → +Assoc (f n) (g n) (h n)))
    (λ f → funExt (λ n → +IdR (f n)))
    (λ f → funExt λ n → +InvR (f n))
    (λ f g → funExt (λ n → +Comm (f n) (g n)))
    (λ f g h → funExt (λ n → {!!}))
    (λ f → funExt λ n → {!
      (f ps.· ps.1r) n ≡⟨⟩
      (ps.1r ps.· f) n ≡⟨⟩
--      (∑ λ i → (λ{ (k , l) → f k · ps.1r l }) (partitionsIntoTwo n i)) ≡⟨ {!funExt (λ{ zero → ?; (suc i) → ? })!}⟩
      {!!}  ≡⟨ {!!} ⟩
      {!!} ≡⟨ {!!} ⟩
      f n ∎  !} )
    (λ f g h → funExt (λ n → {!!}))
    (λ f g → funExt (λ n → {!!}))
