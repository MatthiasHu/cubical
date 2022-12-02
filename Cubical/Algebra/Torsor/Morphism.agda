{-# OPTIONS --safe #-}
module Cubical.Algebra.Torsor.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Group
open import Cubical.Algebra.Torsor


private
  variable
    ℓ ℓ' : Level
    G : Group ℓ

record IsTorsorHom {G : Group ℓ} {T T' : Type ℓ'}
                   (Tstr : TorsorStr G T) (f : T → T') (Tstr' : TorsorStr G T')
                   : Type (ℓ-max ℓ ℓ')
                 where

  open TorsorStr ⦃...⦄
  private instance
    _ = Tstr
    _ = Tstr'

  field
    pres⋆ : (g : ⟨ G ⟩) (x : T) → f (g ⋆ x) ≡ g ⋆ f x
