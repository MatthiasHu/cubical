
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.AlgebraicGeometry.Functorial.ZFunctors.PuncturedPlane where

-- TODO: cleanup imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure


open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-notationZ
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.BigOps

open import Cubical.AlgebraicGeometry.ZariskiLattice.Base
open import Cubical.AlgebraicGeometry.ZariskiLattice.UniversalProperty
open import Cubical.AlgebraicGeometry.ZariskiLattice.Properties
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.Base
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.CompactOpen
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.QcQsScheme
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.OpenSubscheme

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.DistLattices
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf
open import Cubical.Categories.Site.Instances.ZariskiCommRing
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Yoneda

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ

private
  𝔸² : ℤFunctor
  𝔸² = Sp ⟅ ℤ[X,Y] ⟆

  open DistLatticeStr (snd (CompOpenDistLattice ⟅ 𝔸² ⟆))
  open StandardOpens ℤ[X,Y]

  X : ⟨ ℤ[X,Y] ⟩
  X = <X1,···,Xn> ℤCommRing 2 zero

  Y : ⟨ ℤ[X,Y] ⟩
  Y = <X1,···,Xn> ℤCommRing 2 one

  DX∨DY : CompactOpen 𝔸²
  DX∨DY = D X ∨l D Y

𝔸²-0 : ℤFunctor {ℓ = ℓ-zero}
𝔸²-0 = ⟦ DX∨DY ⟧ᶜᵒ

𝔸²-0-is-scheme : isQcQsScheme 𝔸²-0
𝔸²-0-is-scheme = isQcQsSchemeCompOpenOfAffine ℤ[X,Y] DX∨DY

-- TODO: Prove that 𝔸²-0 is not affine.
