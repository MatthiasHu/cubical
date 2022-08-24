module Cubical.Experiments.UInU where


open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

private variable
  ℓ : Level

Goal : Type (ℓ-suc ℓ-zero)
Goal = (Σ[ X ∈ Type ℓ-zero ] X ≃ Type ℓ-zero) → ⊥


module SimpleTrees
  where

  -- Trees as models of sets.
  data Tree (ℓ : Level) : Type (ℓ-suc ℓ) where
    fork : (I : Type ℓ) → (I → Tree ℓ) → Tree ℓ

  leaf : Tree ℓ-zero
  leaf = fork ⊥ λ{()}

  oneTree : Tree ℓ-zero
  oneTree = fork Unit λ x → leaf

  -- Mutually recursive definition of set relations.
  _∈_ : Tree ℓ → Tree ℓ → Type ℓ
  _⊆_ : Tree ℓ → Tree ℓ → Type ℓ
  _==_ : Tree ℓ → Tree ℓ → Type ℓ
  a ∈ (fork J g) = Σ[ j ∈ J ] a == g j
  (fork I f) ⊆ b = (i : I) → f i ∈ b
  a == b = (a ⊆ b) × (b ⊆ a)

  -- (Tree ℓ-zero) is not equivalent to a type in (Type ℓ-zero).
  module _
    (X : Type ℓ-zero)
    (X-eq : X ≃ Tree ℓ-zero)
    where

    tree : X → Tree ℓ-zero
    tree = equivFun X-eq

    RussellTree : Tree ℓ-zero
    RussellTree = fork (Σ[ x ∈ X ] (tree x ∈ tree x → ⊥)) λ{ (x , _) → tree x}

    crux : Type ℓ-zero
    crux = RussellTree ∈ RussellTree

    _ : ⊥
    _ = {!!}
      where
      h : crux → (crux → ⊥)
      h R∈R = {!!}
      h' : (crux → ⊥) → crux
      h' R∉R = ({!equivInv X-eq RussellTree!} , {!!}) , {!!}


module CodeTrees
  where

  module _
    (X : Type ℓ-zero)
    (X-eq : X ≃ Type ℓ-zero)
    where

    -- ??
