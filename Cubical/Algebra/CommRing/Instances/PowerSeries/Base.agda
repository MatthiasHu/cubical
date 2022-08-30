
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

open import Cubical.Tactics.CommRingSolver.Reflection

private
  variable
    ℓ : Level

module _
  (R : CommRing ℓ)
  where

  open CommRingStr (snd R)
  open Sum (CommRing→Ring R)

  private
    ·ps : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → ℕ → ⟨ R ⟩
    -- (a + X * as) * (b + X * bs)  =  a * b  +  X * (a * bs + as * (b + X * bs))
    ·ps f g zero = f zero · g zero
    ·ps f g (suc n) = f zero · g (suc n) + ·ps (f ∘ suc) g n

    ·psComm : (f g : ℕ → ⟨ R ⟩) → (n : ℕ) → ·ps f g n ≡ ·ps g f n
    ·psComm f g zero = ·Comm _ _
    ·psComm f g one = calculation (f 0) (f 1) (g 0) (g 1)
      where
      calculation : (f0 f1 g0 g1 : ⟨ R ⟩) → f0 · g1 + f1 · g0 ≡ g0 · f1 + g1 · f0
      calculation = solve R
    ·psComm f g (suc m@(suc n)) =
      (·ps f g (suc m))                      ≡⟨⟩
      (f 0 · g (suc m) + ·ps (f ∘ suc) g m)  ≡⟨ cong (_ +_) (·psComm (f ∘ suc) g m) ⟩
      (f 0 · g (suc m) + ·ps g (f ∘ suc) m)  ≡⟨⟩
      (f 0 · g (suc m) + (g 0 · f (suc m) + ·ps (g ∘ suc) (f ∘ suc) n))  ≡⟨ {!!} ⟩
      {!!}  ∎

  powerSeriesCommRingStr : CommRingStr (ℕ → ⟨ R ⟩)
  module ps = CommRingStr powerSeriesCommRingStr
  CommRingStr.0r powerSeriesCommRingStr = const 0r
  CommRingStr.1r powerSeriesCommRingStr = caseNat 1r 0r
  CommRingStr._+_ powerSeriesCommRingStr f g = λ n → f n + g n
  CommRingStr._·_ powerSeriesCommRingStr = ·ps
  CommRingStr.-_ powerSeriesCommRingStr f = -_ ∘ f
  CommRingStr.isCommRing powerSeriesCommRingStr = makeIsCommRing
    (isSet→ is-set)
    (λ f g h → funExt (λ n → +Assoc (f n) (g n) (h n)))
    (λ f → funExt (λ n → +IdR (f n)))
    (λ f → funExt λ n → +InvR (f n))
    (λ f g → funExt (λ n → +Comm (f n) (g n)))
    (λ f g h → funExt λ{ zero → ·Assoc (f zero) (g zero) (h zero)
                       ; (suc n) → {!!}})
    (λ f → funExt λ{ zero → ·IdR (f zero)
                   ; (suc n) → {!!} })
    (λ f g h → funExt (λ n → {!!}))
    (λ f g → funExt λ{ zero → ·Comm (f zero) (g zero)
                     ; (suc n) → {!!}})
