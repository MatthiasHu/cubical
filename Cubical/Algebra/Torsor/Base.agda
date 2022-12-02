{-# OPTIONS --safe #-}
module Cubical.Algebra.Torsor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.Group


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    G : Group ℓ

record IsTorsor (G : Group ℓ) {T : Type ℓ'}
                (_⋆_ : ⟨ G ⟩ → T → T)
                : Type (ℓ-max ℓ ℓ') where

  no-eta-equality

  open GroupStr (snd G) public

  field
    isSetT        : isSet T
    ⋆Assoc        : ∀ g h x → (g · h) ⋆ x ≡ g ⋆ (h ⋆ x)
    ⋆Id           : ∀ x → 1g ⋆ x ≡ x
    free          : ∀ g x → g ⋆ x ≡ x → g ≡ 1g
    trans         : ∀ x y → ∃[ g ∈ _ ] g ⋆ x ≡ y
    inhab         : ∥ T ∥₁

unquoteDecl IsTorsorIsoΣ = declareRecordIsoΣ IsTorsorIsoΣ (quote IsTorsor)

record TorsorStr (G : Group ℓ) (T : Type ℓ') : Type (ℓ-max ℓ ℓ') where

  field
    _⋆_            : ⟨ G ⟩ → T → T
    isTorsor       : IsTorsor G _⋆_

  open IsTorsor isTorsor public

Torsor : (G : Group ℓ) → ∀ ℓ' → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Torsor G ℓ' = Σ[ T ∈ Type ℓ' ] TorsorStr G T

isSetTorsor : (T : Torsor G ℓ') → isSet ⟨ T ⟩
isSetTorsor T = isSetT
  where
  open TorsorStr (snd T)
