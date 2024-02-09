{-

  If U is a compact open of X then any compact open of U
  can be regarded as a compact open of X too.

-}

{-# OPTIONS --safe #-}
module Cubical.AlgebraicGeometry.Functorial.ZFunctors.CompactOpen.Composition where

open import Cubical.Foundations.Prelude

open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.Base
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.CompactOpen


module _
  {ℓ : Level}
  (X : ℤFunctor {ℓ = ℓ})
  (U : CompactOpen X)
  where
