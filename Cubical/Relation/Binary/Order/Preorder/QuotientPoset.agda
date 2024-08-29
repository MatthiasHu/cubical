{-# OPTIONS --safe #-}

{-
  In this file we construct the quotient poset of a preorder.

  See:
  * https://ncatlab.org/nlab/show/preorder#relation_to_partial_orders
-}


module Cubical.Relation.Binary.Order.Preorder.QuotientPoset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Functions.Embedding
open import Cubical.Functions.Logic using (⇒∶_⇐∶_)

open import Cubical.HITs.SetQuotients as SQ
  using (_/_)

open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open BinaryRelation using (SymKernel)
open import Cubical.Relation.Binary.Order.Preorder.Base
open import Cubical.Relation.Binary.Order.Poset.Base

private
  variable
    ℓ ℓ' : Level


QuotientPoset : Preorder ℓ ℓ' → Poset (ℓ-max ℓ ℓ') ℓ'
QuotientPoset {ℓ' = ℓ'} A =
  (⟨ A ⟩ / _≈_) ,
  posetstr
    _≤_
    (isposet
      SQ.squash/
      isProp≤
      (SQ.elimProp
        (λ x → isProp≤ x x)
        is-refl)
      (SQ.elimProp3
        (λ x y z → isPropΠ2 (λ _ _ → isProp≤ x z))
        is-trans)
      (SQ.elimProp2
        (λ x y → isPropΠ2 (λ _ _ → SQ.squash/ x y))
        λ a b a≲b b≲a → _/_.eq/ a b (a≲b , b≲a)))
  where
  open PreorderStr (str A)

  _≈_ : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ'
  _≈_ = SymKernel _≲_

  _≤ₚ_ : ⟨ A ⟩ / _≈_ → ⟨ A ⟩ / _≈_ → hProp ℓ'
  _≤ₚ_ =
    SQ.rec2
      isSetHProp
      (λ a b → (a ≲ b) , is-prop-valued a b)
      (λ a b c a≈b →
        ⇒∶ (λ a≲c → is-trans b a c (snd a≈b) a≲c)
        ⇐∶ (λ b≲c → is-trans a b c (fst a≈b) b≲c))
      (λ a b c b≈c →
        ⇒∶ (λ a≲b → is-trans a b c a≲b (fst b≈c))
        ⇐∶ (λ a≲c → is-trans a c b a≲c (snd b≈c)))

  _≤_ : ⟨ A ⟩ / _≈_ → ⟨ A ⟩ / _≈_ → Type ℓ'
  x ≤ y = ⟨ x ≤ₚ y ⟩

  isProp≤ : (x y : ⟨ A ⟩ / _≈_) → isProp (x ≤ y)
  isProp≤ x y = str (x ≤ₚ y)
