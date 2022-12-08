{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FGIdeal.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.HITs.SetQuotients hiding (_/_)

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.FGIdeal
import Cubical.Algebra.CommAlgebra.Quotient as Q

private
  variable
    ℓ ℓ' : Level
    R : CommRing ℓ

module _
  {R : CommRing ℓ}
  (A : CommAlgebra R ℓ')
  {n : ℕ}
  (r : FinVec ⟨ A ⟩ n)
  where

  _/_ : CommAlgebra R _
  _/_ = A Q./ generatedIdeal A r

  quotientHom : CommAlgebraHom A _/_
  quotientHom = Q.quotientHom A (generatedIdeal A r)

  quotientHomSurjective = []surjective
