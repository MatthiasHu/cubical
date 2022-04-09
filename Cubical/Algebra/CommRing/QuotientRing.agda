{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.QuotientRing where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.FinData

open import Cubical.HITs.SetQuotients renaming (rec to rec-sq) hiding (_/_)
open import Cubical.HITs.PropositionalTruncation renaming (rec to rec-prop)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.QuotientRing renaming (_/_ to _/Ring_) hiding (asRing)

private
  variable
    ℓ ℓ' : Level

_/_ : (R : CommRing ℓ) → (I : IdealsIn R) → CommRing ℓ
R / I =
  fst asRing , commringstr _ _ _ _ _
                 (iscommring (RingStr.isRing (snd asRing))
                             (elimProp2 (λ _ _ → squash/ _ _)
                                        commEq))
   where
       asRing = (CommRing→Ring R) /Ring (CommIdeal→Ideal I)
       _·/_ : fst asRing → fst asRing → fst asRing
       _·/_ = RingStr._·_ (snd asRing)
       commEq : (x y : fst R) → ([ x ] ·/ [ y ]) ≡ ([ y ] ·/ [ x ])
       commEq x y i = [ CommRingStr.·Comm (snd R) x y i ]

[_]/ : {R : CommRing ℓ} {I : IdealsIn R} → (a : fst R) → fst (R / I)
[ a ]/ = [ a ]


--

module Rec-Quotient-FGideal
  (A'@(A , Ar) : CommRing ℓ)
  (B'@(B , Br) : CommRing ℓ')
  (g'@(g , gr) : CommRingHom A' B')
  where
  
  open CommRingStr Ar using ()
    renaming
    ( 0r        to 0A
    ; 1r        to 1A
    ; _+_       to _+A_
    ; -_        to -A_
    ; _·_       to _·A_ )
    
  open CommRingStr Br using ()
    renaming
    ( 0r        to 0B
    ; 1r        to 1B
    ; _+_       to _+B_
    ; -_        to -B_
    ; _·_       to _·B_ )

  open CommRingStr
  open IsRingHom


  module _
    {n : ℕ}
    (v : FinVec A n)
    (gnull : (k : Fin n) → g ( v k) ≡ 0B)
    where
        
    f : CommRingHom (A' / (generatedIdeal _ v)) B'
    fst f = rec-sq (is-set Br)
            g
            λ a b → rec-prop (is-set Br _ _)
                     λ x → g a                                   ≡⟨ cong g (sym (+Rid Ar a)) ⟩
                     g (a +A 0A)                                  ≡⟨ cong (λ X → g (a +A X)) (sym (snd (+Inv Ar b))) ⟩
                     g (a +A ((-A b) +A b))                       ≡⟨ cong g (+Assoc Ar a (-A b) b) ⟩
                     g ((a +A -A b) +A b)                         ≡⟨ pres+ gr (a +A -A b) b ⟩
                     (g(a +A -A b) +B g b)                        ≡⟨ cong (λ X → g X +B g b) (snd x) ⟩
                     (g (linearCombination A' (fst x) v) +B g b)  ≡⟨ cong (λ X → X +B g b) (cancel-linear-combinaison A' B' g' n (fst x) v gnull) ⟩
                     0B +B g b                                    ≡⟨ +Lid Br (g b) ⟩
                     g b ∎
    snd f = makeIsRingHom
            (pres1 gr)
            (elimProp (λ x p q i y j → is-set Br _ _ (p y) (q y) i j)
                      λ a → elimProp (λ _ → is-set Br _ _)
                             λ a' → pres+ gr a a')
            (elimProp (λ x p q i y j → is-set Br _ _ (p y) (q y) i j)
                      λ a → elimProp (λ _ → is-set Br _ _)
                             λ a' → pres· gr a a')
