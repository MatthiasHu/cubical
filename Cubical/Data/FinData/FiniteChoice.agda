{-
  There is also a finite choice principle for Data.SumFin in Data.FinSet.FiniteChoice.  
-}
{-# OPTIONS --safe #-}
module Cubical.Data.FinData.FiniteChoice where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.Nat renaming (zero to ℕzero ; suc to ℕsuc)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.FinData

private variable
  ℓ ℓ' : Level

finiteChoice : (n : ℕ) (A : Fin n → Type ℓ')
             → ((i : Fin n) → ∥ A i ∥₁ )
             → ∥ ((i : Fin n) → A i) ∥₁
finiteChoice ℕzero    A c = ∣ (λ ()) ∣₁
finiteChoice (ℕsuc k) A c =
  PT.map2 (λ c₀ c' → λ {zero    → c₀;
                        (suc l) → c' l})
          (c zero)
          (finiteChoice k (A ∘ suc) (c ∘ suc))
