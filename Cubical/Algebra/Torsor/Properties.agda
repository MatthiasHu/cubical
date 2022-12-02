{-# OPTIONS --safe #-}
module Cubical.Algebra.Torsor.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group
open import Cubical.Algebra.Torsor.Base


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    G : Group ℓ


module TorsorTheory (G : Group ℓ) (T : Torsor G ℓ')
  where
  open TorsorStr (snd T)

  module _ (x y : ⟨ T ⟩) where

    open GroupTheory G

    isPropDiffΣ : isProp (Σ[ g ∈ _ ] g ⋆ x ≡ y)
    isPropDiffΣ (g , eq) (g' , eq') = Σ≡Prop (λ _ → isSetT _ _)
      (g           ≡⟨ sym (invInv g) ⟩
      inv (inv g)  ≡⟨ sym (invUniqueR {g = inv g} {h = g'} g⁻¹g'≡1) ⟩
      g'           ∎)
      where
      g⁻¹g'≡1 : _
      g⁻¹g'≡1 = free (inv g · g') x
        ((inv g · g') ⋆ x    ≡⟨ ⋆Assoc (inv g) g' x ⟩
        inv g ⋆ (g' ⋆ x)     ≡⟨ cong (inv g ⋆_) eq' ⟩
        inv g ⋆ y            ≡⟨ cong (inv g ⋆_) (sym eq) ⟩
        inv g ⋆ (g ⋆ x)      ≡⟨ sym (⋆Assoc (inv g) g x) ⟩
        (inv g · g) ⋆ x      ≡⟨ cong (_⋆ x) (·InvL g) ⟩
        1g ⋆ x               ≡⟨ ⋆Id x ⟩
        x                    ∎)

    private
      ⟨Δ,Δxy⋆x≡y⟩ : Σ[ g ∈ _ ] g ⋆ x ≡ y
      ⟨Δ,Δxy⋆x≡y⟩ = PT.rec isPropDiffΣ (idfun (Σ ⟨ G ⟩ (λ g → (g ⋆ x) ≡ y))) (trans x y)

    Δ : ⟨ G ⟩
    Δ = fst ⟨Δ,Δxy⋆x≡y⟩

    Δxy⋆x≡y : Δ ⋆ x ≡ y
    Δxy⋆x≡y = snd ⟨Δ,Δxy⋆x≡y⟩
