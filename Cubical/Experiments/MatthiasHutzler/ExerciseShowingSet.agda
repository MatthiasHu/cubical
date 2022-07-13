module Cubical.Experiments.MatthiasHutzler.ExerciseShowingSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure


module test
  (X : Type)
  (x y z : X)
  (p : x ≡ y)
  (q : y ≡ z)
  where private

  test : subst (λ y' → x ≡ y') q p ≡ p ∙ q
  test = {!refl!} -- no.

-- HoTT book, Theorem 7.2.2

module _
  {ℓ-X ℓ-R : _}
  (X : Type ℓ-X)
  (R : X → X → hProp ℓ-R)
  (reflexive : (x : X) → ⟨ R x x ⟩)
  (implication : {x y : X} → ⟨ R x y ⟩ → x ≡ y)
  where

  module _ (x : X) where
    select-refl : x ≡ x
    select-refl = implication (reflexive x)

  module _ {x y : X} (p : x ≡ y) where
    select : x ≡ y
    select i = (select-refl (p i)) i

    project : ⟨ R x y ⟩
    project = subst (λ y' → ⟨ R x y' ⟩) p (reflexive x)

    description : select ≡ implication project
    description = {!!}

  module _ (x : X) where
    private
      r = refl {x = x}

    select-idempotent : select (select r) ≡ select r
    select-idempotent = {!!}

  module _ (x y z : X) (p : x ≡ y) (q : y ≡ z) where
    shift-select : p ∙ select q ≡ select p ∙ q
    shift-select = λ i → triangle-1 i ∙ triangle-2 i
      where
        triangle-1 : (i : I) → x ≡ select-refl y i
        triangle-1 i j = select-refl (p j) (i ∧ j)
        triangle-2 : (i : I) → select-refl y i ≡ z
        triangle-2 i j = select-refl (q j) (i ∨ j)

  module _ (x y : X) (p : x ≡ y) where
--    test : p ≡ implication x y (reflexiv

  conclusion : isSet X
  conclusion x y = {!!}
