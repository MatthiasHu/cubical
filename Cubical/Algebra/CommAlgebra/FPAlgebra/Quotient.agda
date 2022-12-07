{-
  This module shows, that a an FP-R-algebra A,
  modulo relations ⟨r₁,...,rₙ⟩ is again an FP-R-algebra.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FPAlgebra.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal using (inclOfFGIdeal)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
  renaming (inducedHom to freeInducedHom)
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
  renaming (inducedHom to quotientInducedHom)
open import Cubical.Algebra.CommAlgebra.Ideal using (IdealsIn)
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.Instances.Unit
  renaming (UnitCommAlgebra to TerminalCAlg)
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.Algebra

open import Cubical.Algebra.CommAlgebra.FPAlgebra.Base

private
  variable
    ℓ ℓ' : Level


module _ (R : CommRing ℓ) (A : FPAlgebra R ℓ') (n : ℕ) (r : Vec ⟨ A ⟩ n) where
  open FinitePresentation

  
  
