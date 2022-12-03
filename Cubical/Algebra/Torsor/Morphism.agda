{-# OPTIONS --safe #-}
module Cubical.Algebra.Torsor.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group
open import Cubical.Algebra.Torsor


private
  variable
    ℓ ℓ' ℓ'' : Level
    G : Group ℓ
    T T' : Torsor G ℓ'

record IsTorsorHom {G : Group ℓ} {T : Type ℓ'} {T' : Type ℓ''}
                   (Tstr : TorsorStr G T) (f : T → T') (Tstr' : TorsorStr G T')
                   : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
                 where

  open TorsorStr ⦃...⦄
  private instance
    _ = Tstr
    _ = Tstr'

  field
    pres⋆ : (g : ⟨ G ⟩) (x : T) → f (g ⋆ x) ≡ g ⋆ f x

TorsorHom : (T : Torsor G ℓ') (T' : Torsor G ℓ'') → Type _
TorsorHom T T' =  Σ[ f ∈ (⟨ T ⟩ → ⟨ T' ⟩) ] IsTorsorHom (snd T) f (snd T')

infixr 10 _$t_
_$t_ : (f : TorsorHom T T') → ⟨ T ⟩ → ⟨ T' ⟩
f $t x = fst f x


module _ {T : Torsor G ℓ'} {T' : Torsor G ℓ''} (f : TorsorHom T T') where
  open TorsorTheory ⦃...⦄
  open TorsorStr ⦃...⦄
  open GroupStr (snd G)
  open IsTorsorHom (snd f)
  private instance
    _ = T
    _ = T'
    _ = snd T
    _ = snd T'
  private module _ (t₀ : ⟨ T ⟩) where
    equiv : isEquiv (fst f)
    equiv = isEmbedding×isSurjection→isEquiv
      (injEmbedding
        (isSetTorsor T')
        (λ {w = x} {x = y} p →
         let
           q : Δ y x ⋆ f $t y ≡ f $t y
           q =
             (Δ y x ⋆ f $t y) ≡⟨ sym (pres⋆ (Δ y x) y) ⟩
             f $t (Δ y x ⋆ y) ≡⟨ cong (fst f) (Δxy⋆x≡y y x) ⟩
             f $t x           ≡⟨ p ⟩
             f $t y           ∎
         in x         ≡⟨ sym (Δxy⋆x≡y y x) ⟩
            Δ y x ⋆ y ≡⟨ cong (_⋆ y) (free (Δ y x) (f $t y) q) ⟩
            1g ⋆ y    ≡⟨ ⋆Id y ⟩
            y ∎) ,
      λ t' → ∣ (Δ (f $t t₀) t' ⋆ t₀) ,
        (f $t (Δ (f $t t₀) t' ⋆ t₀) ≡⟨ pres⋆ (Δ (f $t t₀) t') t₀ ⟩
         Δ (f $t t₀) t' ⋆ f $t t₀   ≡⟨ Δxy⋆x≡y (f $t t₀) t' ⟩
         t' ∎) ∣₁)

  isEquivTorsorHom : isEquiv (fst f)
  isEquivTorsorHom =
    PT.rec
      (isPropIsEquiv (fst f))
      (λ t₀ → equiv t₀)
      inhab
