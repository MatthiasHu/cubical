{-
  This module shows, that an FP-R-algebra A,
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
open import Cubical.Data.FinData.FiniteChoice
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal using (inclOfFGIdeal)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
  renaming (inducedHom to freeInducedHom)
open import Cubical.Algebra.CommAlgebra.Ideal using (IdealsIn)
open import Cubical.Algebra.CommAlgebra.FGIdeal
import Cubical.Algebra.CommAlgebra.FGIdeal.Quotient as FGQ
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.Instances.Unit
  renaming (UnitCommAlgebra to TerminalCAlg)
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.Algebra

open import Cubical.Algebra.CommAlgebra.FPAlgebra.Base

private
  variable
    ℓ ℓ' : Level

private
  module Proof
    {R : CommRing ℓ}
    (n : ℕ)
    {m : ℕ}
    (r : FinVec ⟨ Polynomials R n ⟩ m)
    {k : ℕ}
    (r' : FinVec ⟨ Polynomials R n FGQ./ r ⟩ k)
    where

    π = FGQ.quotientHom (Polynomials R n) r

    _ : ∃[ r'lift ∈ FinVec ⟨ Polynomials R n ⟩ k ] ((i : _) → π $a (r'lift i) ≡ r' i)
    _ = PT.map {!!} (finiteChoice _ (λ i → ∃[ r'i-lift ∈ (⟨ Polynomials R n ⟩) ] π  $a r'i-lift  ≡ r' i) {!!})

    _ : isFPAlgebra ((Polynomials R n FGQ./ r) FGQ./ r')
    _ = {!!}


module _ {R : CommRing ℓ} (A : FPAlgebra R ℓ) {k : ℕ} (r' : FinVec ⟨ A ⟩ k) where
  open FinitePresentation

  A-CAlg : CommAlgebra R ℓ
  A-CAlg = FPAlgebra→CommAlgebra A

  isFPAlgQuotient : isFPAlgebra (A-CAlg FGQ./ r')
  isFPAlgQuotient = PT.rec isPropPropTrunc (λ{ ((n , m) , r , equiv) → {!!}}) (FPAlgebra→∃ A)

  _/_ = FPAlgebraFromCommAlgebra (A-CAlg FGQ./ r') isFPAlgQuotient
