{-# OPTIONS --safe #-}
module Cubical.Algebra.Torsor.SIP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.Group
open import Cubical.Algebra.Torsor
open import Cubical.Algebra.Torsor.Morphism

private
  variable
    ℓ ℓ' ℓ'' : Level
    G : Group ℓ

IsTorsorEquiv : {T : Type ℓ'} {T' : Type ℓ''}
              → TorsorStr G T → (T ≃ T') → TorsorStr G T'
              → Type _
IsTorsorEquiv Tstr e Tstr' = IsTorsorHom Tstr (e .fst) Tstr'

module _ (T : Torsor G ℓ') (T' : Torsor G ℓ'') where

  TorsorEquiv : Type _
  TorsorEquiv = Σ[ e ∈ _ ] IsTorsorEquiv (snd T) e (snd T')

isPropIsTorsor : (G : Group ℓ) {T : Type ℓ'}
                 (_⋆_ : ⟨ G ⟩ → T → T)
                 → isProp (IsTorsor G _⋆_)
isPropIsTorsor G _⋆_ =
  isOfHLevelRetractFromIso 1 IsTorsorIsoΣ
    (isPropΣ isPropIsSet λ isSetT →
    (isProp× (isPropΠ3 λ _ _ _ → isSetT _ _)
    (isProp× (isPropΠ λ _ → isSetT _ _)
    (isProp× (isPropΠ3 λ _ _ _ → is-set _ _)
    (isProp× (isPropΠ2 (λ _ _ → isPropPropTrunc))
    isPropPropTrunc)))))
    where
    open GroupStr (snd G)

𝒮ᴰ-Torsor : (G : Group ℓ) → DUARel (𝒮-Univ ℓ') (TorsorStr G) (ℓ-max ℓ ℓ')
𝒮ᴰ-Torsor G =
  𝒮ᴰ-Record (𝒮-Univ _) (IsTorsorEquiv {G = G})
    (fields:
      data[ _⋆_ ∣ autoDUARel _ _ ∣ pres⋆ ]
      prop[ isTorsor ∣ (λ _ _ → isPropIsTorsor _ _) ])
  where
  open TorsorStr
  open IsTorsorHom

TorsorPath : {G : Group ℓ} (T T' : Torsor G ℓ') → TorsorEquiv T T' ≃ (T ≡ T')
TorsorPath {G = G} = ∫ (𝒮ᴰ-Torsor G) .UARel.ua

TorsorHomPath : {G : Group ℓ} (T T' : Torsor G ℓ') → TorsorHom T T' ≃ (T ≡ T')
TorsorHomPath T T' =
  TorsorHom T T'    ≃⟨ invEquiv (Σ-contractSnd (λ f → isEquivTorsorHom f , (λ _ → isPropIsEquiv (fst f) _ _))) ⟩
  Σ[ f ∈ TorsorHom T T' ] isEquiv (fst f)                                 ≃⟨ Σ-assoc-≃ ⟩
  Σ[ f ∈ (⟨ T ⟩ → ⟨ T' ⟩) ] (IsTorsorHom (snd T) f (snd T') × isEquiv f)  ≃⟨ Σ-cong-equiv-snd (λ f → Σ-swap-≃) ⟩
  Σ[ f ∈ (⟨ T ⟩ → ⟨ T' ⟩) ] (isEquiv f × IsTorsorHom (snd T) f (snd T'))  ≃⟨ invEquiv Σ-assoc-≃ ⟩
  TorsorEquiv T T'                                                        ≃⟨ (TorsorPath T T') ⟩
  T ≡ T'                                                                  ■

