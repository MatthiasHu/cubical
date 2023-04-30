module Cubical.Experiments.MatthiasHutzler.InductiveIdentityTypesResizing where

open import Cubical.Foundations.Prelude


-- The following fails because of the flag --cubical.
--
-- "when checking that the type {a : A} → a == a of the constructor
-- refl-== fits in the sort Type of the datatype."
--
-- Actually, why is this allowed in vanilla Agda? Hm...

data _==_ {ℓA : Level} {A : Type ℓA} : A → A → Type where
  refl-== : {a : A} → a == a
