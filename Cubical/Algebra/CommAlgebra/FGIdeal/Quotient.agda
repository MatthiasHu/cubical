{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FGIdeal.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.FGIdeal
import Cubical.Algebra.CommAlgebra.Quotient as Q

private
  variable
    ℓ ℓ' : Level
    R : CommRing ℓ

_/_ : {R : CommRing ℓ} → (A : CommAlgebra R ℓ') → {n : ℕ} → FinVec ⟨ A ⟩ n → CommAlgebra R _
A / r = A Q./ generatedIdeal A r
