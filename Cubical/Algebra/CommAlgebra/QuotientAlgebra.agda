{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.QuotientAlgebra where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset using (_∈_; _⊆_)
open import Cubical.Foundations.Structure

open import Cubical.HITs.SetQuotients hiding (_/_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
import Cubical.Algebra.CommRing.QuotientRing as CommRing
import Cubical.Algebra.Ring.QuotientRing as Ring
open import Cubical.Algebra.CommRing.Ideal hiding (IdealsIn)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.CommAlgebra.Instances.Unit
open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom; isPropIsAlgebraHom)
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal using (isIdeal)
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Algebra.Algebra.Properties
open AlgebraHoms using (compAlgebraHom)

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  open CommRingStr {{...}} hiding (_-_; -_; ·IdL ; ·DistR+) renaming (_·_ to _·R_; _+_ to _+R_)
  open CommAlgebraStr {{...}}
  open RingTheory (CommRing→Ring (CommAlgebra→CommRing A)) using (-DistR·)
  instance
    _ : CommRingStr _
    _ = snd R
    _ : CommAlgebraStr _ _
    _ = snd A

  _/_ : lockUnit {ℓ = ℓ} → CommAlgebra R ℓ
  _/_ unlock = commAlgebraFromCommRing
           ((CommAlgebra→CommRing A) CommRing./ I)
           (λ r → elim (λ _ → squash/) (λ x → [ r ⋆ x ]) (eq r))
           (λ r s → elimProp (λ _ → squash/ _ _)
                             λ x i → [ ((r ·R s) ⋆ x ≡⟨ ⋆Assoc r s x ⟩
                                         r ⋆ (s ⋆ x) ∎) i ])
           (λ r → elimProp2 (λ _ _ → squash/ _ _)
                            λ x y i → [ (r ⋆ (x + y)  ≡⟨ ⋆DistR+ r x y ⟩
                                        r ⋆ x + r ⋆ y ∎) i ])
           (λ r s → elimProp (λ _ → squash/ _ _)
                             λ x i → [ ((r +R s) ⋆ x ≡⟨ ⋆DistL+ r s x ⟩
                                       r ⋆ x + s ⋆ x ∎) i ])
           (elimProp (λ _ → squash/ _ _)
                     (λ x i →  [ (1r ⋆ x ≡⟨ ⋆IdL x ⟩ x ∎) i ]))
           λ r → elimProp2 (λ _ _ → squash/ _ _)
                           λ x y i → [ ((r ⋆ x) · y ≡⟨ ⋆AssocL r x y ⟩
                                       r ⋆ (x · y) ∎) i ]

          where
                open CommIdeal using (isCommIdeal)
                eq : (r : fst R) (x y : fst A) → x - y ∈ (fst I) →  [ r ⋆ x ] ≡ [ r ⋆ y ]
                eq r x y x-y∈I = eq/ _ _
                  (subst (λ u → u ∈ fst I)
                  ((r ⋆ 1a) · (x - y)               ≡⟨ ·DistR+ (r ⋆ 1a) x (- y) ⟩
                    (r ⋆ 1a) · x + (r ⋆ 1a) · (- y) ≡[ i ]⟨ (r ⋆ 1a) · x + -DistR· (r ⋆ 1a) y i ⟩
                    (r ⋆ 1a) · x - (r ⋆ 1a) · y     ≡[ i ]⟨ ⋆AssocL r 1a x i
                                                            - ⋆AssocL r 1a y i ⟩
                    r ⋆ (1a · x) - r ⋆ (1a · y)     ≡[ i ]⟨ r ⋆ (·IdL x i) - r ⋆ (·IdL y i) ⟩
                    r ⋆ x - r ⋆ y ∎ )
                  (isCommIdeal.·Closed (snd I) _ x-y∈I))

  quotientHom : (key : lockUnit) → CommAlgebraHom A (_/_ key)
  fst (quotientHom unlock) x = [ x ]
  IsAlgebraHom.pres0 (snd (quotientHom unlock)) = refl
  IsAlgebraHom.pres1 (snd (quotientHom unlock)) = refl
  IsAlgebraHom.pres+ (snd (quotientHom unlock)) _ _ = refl
  IsAlgebraHom.pres· (snd (quotientHom unlock)) _ _ = refl
  IsAlgebraHom.pres- (snd (quotientHom unlock)) _ = refl
  IsAlgebraHom.pres⋆ (snd (quotientHom unlock)) _ _ = refl

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  open CommRingStr {{...}} hiding (_-_; -_; ·IdL; ·DistR+) renaming (_·_ to _·R_; _+_ to _+R_)
  open CommAlgebraStr ⦃...⦄

  instance
    _ : CommRingStr _
    _ = snd R
    _ : CommAlgebraStr _ _
    _ = snd A

  private
    LRing : lockUnit → Ring _
    LRing key = CommAlgebra→Ring ((A / I) key)
    RRing = (CommAlgebra→Ring A) Ring./ (CommIdeal→Ideal I)

  -- sanity check / maybe a helper function some day
  CommForget/ : (key : lockUnit) →
    RingEquiv (CommAlgebra→Ring ((A / I) key)) ((CommAlgebra→Ring A) Ring./ (CommIdeal→Ideal I))
  fst (CommForget/ unlock) =
    isoToEquiv
      (iso
        (rec (isSetRing (LRing unlock)) (λ a → [ a ]) λ a b a-b∈I → eq/ a b a-b∈I)
        (rec (isSetRing RRing) (λ a → [ a ]) (λ a b a-b∈I → eq/ a b a-b∈I))
        (elimProp (λ _ → isSetRing (LRing unlock) _ _) λ _ → refl)
        (elimProp (λ _ → isSetRing RRing _ _) (λ _ → refl)))
  IsRingHom.pres0 (snd (CommForget/ unlock)) = refl
  IsRingHom.pres1 (snd (CommForget/ unlock)) = refl
  IsRingHom.pres+ (snd (CommForget/ unlock)) = elimProp2 (λ _ _ → isSetRing RRing _ _) (λ _ _ → refl)
  IsRingHom.pres· (snd (CommForget/ unlock)) = elimProp2 (λ _ _ → isSetRing RRing _ _) (λ _ _ → refl)
  IsRingHom.pres- (snd (CommForget/ unlock)) = elimProp (λ _ → isSetRing RRing _ _) (λ _ → refl)

  open IsAlgebraHom
  inducedHom : (key : lockUnit {ℓ = ℓ})
               → (B : CommAlgebra R ℓ) (ϕ : CommAlgebraHom A B)
               → (fst I) ⊆ (fst (kernel A B ϕ))
               → CommAlgebraHom ((A / I) key) B
  fst (inducedHom unlock B ϕ I⊆kernel) =
    let open RingTheory (CommRing→Ring (CommAlgebra→CommRing B))
        instance
          _ : CommAlgebraStr R _
          _ = snd B
          _ : CommRingStr _
          _ = snd (CommAlgebra→CommRing B)
    in rec (isSetCommAlgebra B) (λ x → fst ϕ x)
        λ a b a-b∈I →
          equalByDifference
            (fst ϕ a) (fst ϕ b)
            ((fst ϕ a) - (fst ϕ b)     ≡⟨ cong (λ u → (fst ϕ a) + u) (sym (IsAlgebraHom.pres- (snd ϕ) _)) ⟩
             (fst ϕ a) + (fst ϕ (- b)) ≡⟨ sym (IsAlgebraHom.pres+ (snd ϕ) _ _) ⟩
             fst ϕ (a - b)             ≡⟨ I⊆kernel (a - b) a-b∈I ⟩
             0r ∎)
  pres0 (snd (inducedHom unlock B ϕ kernel⊆I)) = pres0 (snd ϕ)
  pres1 (snd (inducedHom unlock B ϕ kernel⊆I)) = pres1 (snd ϕ)
  pres+ (snd (inducedHom unlock B ϕ kernel⊆I)) = elimProp2 (λ _ _ → isSetCommAlgebra B _ _) (pres+ (snd ϕ))
  pres· (snd (inducedHom unlock B ϕ kernel⊆I)) = elimProp2 (λ _ _ → isSetCommAlgebra B _ _) (pres· (snd ϕ))
  pres- (snd (inducedHom unlock B ϕ kernel⊆I)) = elimProp (λ _ → isSetCommAlgebra B _ _) (pres- (snd ϕ))
  pres⋆ (snd (inducedHom unlock B ϕ kernel⊆I)) = λ r → elimProp (λ _ → isSetCommAlgebra B _ _) (pres⋆ (snd ϕ) r)

  injectivePrecomp : (key : lockUnit)
                     → (B : CommAlgebra R ℓ) (f g : CommAlgebraHom ((A / I) key) B)
                     → f ∘a (quotientHom A I key) ≡ g ∘a (quotientHom A I key)
                     → f ≡ g
  injectivePrecomp unlock B f g p =
    Σ≡Prop
      (λ h → isPropIsAlgebraHom (CommRing→Ring R) (snd (CommAlgebra→Algebra ((A / I) unlock))) h (snd (CommAlgebra→Algebra B)))
      (descendMapPath (fst f) (fst g) (isSetCommAlgebra B)
                      λ x → λ i → fst (p i) x)


{- trivial quotient -}
module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) where
  open CommAlgebraStr (snd A)

  oneIdealQuotient : (key : lockUnit) →
    CommAlgebraEquiv ((A / (1Ideal A)) key) (UnitCommAlgebra R {ℓ' = ℓ})
  fst (oneIdealQuotient unlock) =
    isoToEquiv (iso (fst (terminalMap R ((A / (1Ideal A)) unlock)))
                    (λ _ → [ 0a ])
                    (λ _ → isPropUnit* _ _)
                    (elimProp (λ _ → squash/ _ _)
                              λ a → eq/ 0a a tt*))
  snd (oneIdealQuotient key@unlock) = snd (terminalMap R ((A / (1Ideal A)) key))

  zeroIdealQuotient : (key : lockUnit) →
    CommAlgebraEquiv A ((A / (0Ideal A)) key)
  fst (zeroIdealQuotient unlock) =
    let open RingTheory (CommRing→Ring (CommAlgebra→CommRing A))
    in isoToEquiv (iso (fst (quotientHom A (0Ideal A) unlock))
                    (rec (isSetCommAlgebra A) (λ x → x) λ x y x-y≡0 → equalByDifference x y x-y≡0)
                    (elimProp (λ _ → squash/ _ _) λ _ → refl)
                    λ _ → refl)
  snd (zeroIdealQuotient unlock) = snd (quotientHom A (0Ideal A) unlock)

[_]/ : {R : CommRing ℓ} {A : CommAlgebra R ℓ} {I : IdealsIn A}
       → (a : fst A) → (key : lockUnit) → fst ((A / I) key)
[ a ]/ unlock = [ a ]



module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  open CommIdeal using (isPropIsCommIdeal)

  private
    π : (key : lockUnit) → CommAlgebraHom A ((A / I) key)
    π = quotientHom A I

  kernel≡I : (key : lockUnit) → kernel A ((A / I) key) (π key) ≡ I
  kernel≡I key@unlock =
    kernel A ((A / I) key) (π key) ≡⟨ Σ≡Prop
                                        (isPropIsCommIdeal (CommAlgebra→CommRing A))
                                        refl ⟩
    _                              ≡⟨  CommRing.kernel≡I {R = CommAlgebra→CommRing A} I ⟩
    I ∎


private
  module _ (R : CommRing ℓ) where
    open CommRingStr (snd R)
    lemma : (y : (fst R)) → y ≡ y - 0r
    lemma = solve R

isZeroFromIdeal : (key : lockUnit)
                  → {R : CommRing ℓ} {A : CommAlgebra R ℓ} {I : IdealsIn A}
                  → (x : ⟨ A ⟩) → x ∈ (fst I) → fst (quotientHom A I key) x ≡ CommAlgebraStr.0a (snd ((A / I) key))
isZeroFromIdeal unlock {A = A} {I = I} x x∈I = eq/ x 0a (subst (λ y → y ∈ (fst I)) step x∈I )
  where
    open CommAlgebraStr (snd A)
    step : x ≡ x - 0a
    step = lemma (CommAlgebra→CommRing A) x
    0' : ⟨ (A / I) unlock ⟩
    0' = fst (quotientHom A I unlock) 0a
