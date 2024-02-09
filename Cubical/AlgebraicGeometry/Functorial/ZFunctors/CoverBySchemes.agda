{-

  A cover by schemes yields (merely) a cover by affine schemes.
  Therefore, a local ℤ-functor that has a cover by schemes is itself a scheme.

-}

module Cubical.AlgebraicGeometry.Functorial.ZFunctors.CoverBySchemes where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.FinSet.FiniteChoice

import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.Base
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.CompactOpen
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.QcQsScheme


module _
  {ℓ : Level}
  (X : ℤFunctor {ℓ = ℓ})
  {n : ℕ}
  (U : FinVec (CompactOpen X) n)
  where

  module _
    (affineCoverU : (i : _) → AffineCover ⟦ U i ⟧ᶜᵒ)
    where

    affineCoverCover→affineCover : AffineCover X
    affineCoverCover→affineCover = {!!}

  module _
    (isSchemeU : (i : _) → isQcQsScheme ⟦ U i ⟧ᶜᵒ)
    where

    schemeCover→hasAffineCover : hasAffineCover X
    schemeCover→hasAffineCover =
      PT.rec
        PT.isPropPropTrunc
        (λ affineCoverU → PT.∣ affineCoverCover→affineCover affineCoverU ∣₁)
        (choice
          (Fin n , n , {!!})
          (λ i → AffineCover (⟦ U i ⟧ᶜᵒ))
          (λ i → snd (isSchemeU i)))

isLocal×schemeCover→isScheme :
  {ℓ : Level} →
  (X : ℤFunctor {ℓ = ℓ}) →
  (isLocalX : isLocal X) →
  {n : ℕ} →
  (U : FinVec (CompactOpen X) n) →
  (isSchemeU : (i : _) → isQcQsScheme ⟦ U i ⟧ᶜᵒ) →
  isQcQsScheme X
isLocal×schemeCover→isScheme X isLocalX U isSchemeU =
  isLocalX , schemeCover→hasAffineCover X U isSchemeU
