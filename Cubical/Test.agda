{-# OPTIONS --experimental-lossy-unification #-}
module Cubical.Test where

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function

module _
  (A : Type)
  (a : A)
  (B : Type)
  (b b' : B)
  where

  const : A → B → A
  const x = λ _ → x

  const-a : B → A
  const-a = λ _ → a

  _ : const-a _ ≡ const-a b
  _ = refl
