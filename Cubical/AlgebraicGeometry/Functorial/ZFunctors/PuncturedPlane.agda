{-

  We construct the punctured plane 𝔸²-0
  as an open subscheme of the affine scheme 𝔸².

  Note:
  It would be nice to show that 𝔸²-0 is not an affine scheme.

-}

{-# OPTIONS --safe --lossy-unification #-}
module Cubical.AlgebraicGeometry.Functorial.ZFunctors.PuncturedPlane where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData

open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-notationZ
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.DistLattice

open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.Base
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.CompactOpen
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.QcQsScheme
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.OpenSubscheme

open import Cubical.Categories.Functor


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
