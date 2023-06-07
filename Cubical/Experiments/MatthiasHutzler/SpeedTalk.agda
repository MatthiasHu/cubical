module Cubical.Experiments.MatthiasHutzler.SpeedTalk where
open import Cubical.Foundations.Prelude


data Bool : Type where
  true : Bool
  false : Bool


data Nat : Type where
  zero : Nat
  suc  : Nat → Nat


data Circle : Type where
  base : Circle
  loop : base ≡ base


data Torus : Type₀ where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : line1 ∙ line2 ≡ line2 ∙ line1

