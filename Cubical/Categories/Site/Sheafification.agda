{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Sheafification where

-- Construction of the sheafification of a presheaf on a site
-- using a quotient inductive type.

-- TODO: clean up imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Cubical.Data.Sigma

open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.Categories.Category
open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Sieve
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

module Sheafification
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  {ℓP : Level}
  (P : Presheaf C ℓP)
  where

  open Category C hiding (_∘_)
  open Coverage J

  data ⟨F⟅_⟆⟩ : ob → Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓcov (ℓ-max ℓpat ℓP)))) where

    trunc : {c : ob} → isSet ⟨F⟅ c ⟆⟩

    restrict : {c d : ob} → Hom[ d , c ] → ⟨F⟅ c ⟆⟩ → ⟨F⟅ d ⟆⟩

    restrictId :
      {c : ob} →
      (x : ⟨F⟅ c ⟆⟩) →
      restrict id x ≡ x
    restrictRestrict :
      {c d e : ob} →
      (f : Hom[ d , c ]) →
      (g : Hom[ e , d ]) →
      (x : ⟨F⟅ c ⟆⟩) →
      restrict (g ⋆ f) x ≡ restrict g (restrict f x)

    η⟦_⟧ : {c : ob} → ⟨ P ⟅ c ⟆ ⟩ → ⟨F⟅ c ⟆⟩

    ηNatural :
      {c d : ob} →
      (f : Hom[ d , c ]) →
      (x : ⟨ P ⟅ c ⟆ ⟩) →
      restrict f (η⟦ x ⟧) ≡ η⟦ (P ⟪ f ⟫) x ⟧

    sep :
      {c : ob} →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      (x y : ⟨F⟅ c ⟆⟩) →
      ((i : ⟨ cov ⟩) → restrict (patchArr cov i) x ≡ restrict (patchArr cov i) y) →
      x ≡ y

    amalgamate :
      let
      F : Presheaf C _
      F = record
        { F-ob = λ c → ⟨F⟅ c ⟆⟩ , trunc
        ; F-hom = restrict
        ; F-id = funExt restrictId
        ; F-seq = λ f g → funExt (restrictRestrict f g)
        }
      in
      {c : ob} →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      CompatibleFamily F cov →
      ⟨F⟅ c ⟆⟩
    restrictAmalgamate :
      let
      F : Presheaf C _
      F = record
        { F-ob = λ c → ⟨F⟅ c ⟆⟩ , trunc
        ; F-hom = restrict
        ; F-id = funExt restrictId
        ; F-seq = λ f g → funExt (restrictRestrict f g)
        }
      in
      {c : ob} →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      (fam : CompatibleFamily F cov) →
      (i : ⟨ cov ⟩) →
      restrict (patchArr cov i) (amalgamate cover fam) ≡ fst fam i

  F : Presheaf C (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) ℓP)
  Functor.F-ob F c = ⟨F⟅ c ⟆⟩ , trunc
  Functor.F-hom F = restrict
  Functor.F-id F = funExt restrictId
  Functor.F-seq F f g = funExt (restrictRestrict f g)

  isSheafF : ⟨ amalgamationProperty J F ⟩
  isSheafF c cover = isEmbedding×isSurjection→isEquiv
    ( injEmbedding
        (isSetCompatibleFamily F cov)
        (λ {x} {y} x~y → sep cover x y (funExt⁻ (cong fst x~y)))
    , λ fam →
        ∣ amalgamate cover fam
        , Σ≡Prop
            (str ∘ isCompatibleFamily F cov)
            (funExt (restrictAmalgamate cover fam)) ∣₁ )
    where
    cov = str (covers c) cover


module UniversalProperty
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  where

  -- We now assume P to have this level to ensure that F has the same level as P.
  ℓP = ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓcov ℓpat))

  module _
    (P : Presheaf C ℓP)
    where

    open Sheafification J P
    open NatTrans

    η : P ⇒ F
    N-ob η c = η⟦_⟧
    N-hom η f = funExt (λ x → sym (ηNatural f x))

    module _
      ((G , isSheafG) : Sheaf J ℓP)
      (f : P ⇒ G)
      where

      inducedMap : F ⇒ G
      NatTrans.N-ob inducedMap c x = {!!}
      NatTrans.N-hom inducedMap = {!!}
