module Cubical.Experiments.UInU where


open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

private variable
  ℓ ℓ' : Level

Goal : Type (ℓ-suc ℓ-zero)
Goal = (Σ[ X ∈ Type ℓ-zero ] X ≃ Type ℓ-zero) → ⊥


module Trees
  (TypeCodes : Type ℓ)
  (decodeType : TypeCodes → Type ℓ')
  where

  -- Trees as models of sets.
  data Tree  : Type (ℓ-max ℓ ℓ') where
    fork : (c : TypeCodes) → (decodeType c → Tree) → Tree
  --  fork : (I : Type ℓ) → (I → Tree ℓ) → Tree ℓ

  {-
  leaf : Tree ℓ-zero
  leaf = fork ⊥ λ{()}

  oneTree : Tree ℓ-zero
  oneTree = fork Unit λ x → leaf
  -}

  -- Mutually recursive definition of set relations.
  _∈_ : Tree → Tree → Type (ℓ-max ℓ ℓ')
  _⊆_ : Tree → Tree → Type (ℓ-max ℓ ℓ')
  _==_ : Tree → Tree → Type (ℓ-max ℓ ℓ')
  a ∈ (fork c g) = Σ[ i ∈ decodeType c ] a == g i
  (fork c f) ⊆ b = (i : decodeType c) → f i ∈ b
  a == b = (a ⊆ b) × (b ⊆ a)

  evil : Tree → Type (ℓ-max ℓ ℓ')
  evil t = t ∈ t

module _
  (X : Type ℓ-zero)
  (X-eq : X ≃ Type ℓ-zero)
  where

  open Trees X (equivFun X-eq)

  codeType : Type ℓ-zero → X
  codeType = equivFun (invEquiv X-eq)

  nonEvilTrees : Type ℓ-zero
  nonEvilTrees = Σ[ t ∈ Tree ] (evil t → ⊥)

  RussellTree : Tree
  RussellTree = fork (codeType nonEvilTrees) λ x → {!retEq X-eq x!}

{-
  crux : Type ℓ-zero
  crux = RussellTree ∈ RussellTree

  _ : ⊥
  _ = {!!}
    where
    h : crux → (crux → ⊥)
    h R∈R = {!!}
    h' : (crux → ⊥) → crux
    h' R∉R = ({!equivInv X-eq RussellTree!} , {!!}) , {!!}
-}
