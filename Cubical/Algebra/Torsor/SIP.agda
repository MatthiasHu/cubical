{-# OPTIONS --safe #-}
module Cubical.Algebra.Torsor.SIP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.Group
open import Cubical.Algebra.Torsor
open import Cubical.Algebra.Torsor.Morphism

private
  variable
    ℓ ℓ' ℓ'' : Level
    G : Group ℓ

IsTorsorEquiv : {T : Type ℓ'} {T' : Type ℓ''}
              → TorsorStr G T → (T ≃ T') → TorsorStr G T'
              → Type _
IsTorsorEquiv Tstr e Tstr' = IsTorsorHom Tstr (e .fst) Tstr'

module _ (T : Torsor G ℓ') (T' : Torsor G ℓ'') where

  TorsorEquiv : Type _
  TorsorEquiv = Σ[ e ∈ _ ] IsTorsorEquiv (snd T) e (snd T')

isPropIsTorsor : (G : Group ℓ) {T : Type ℓ'}
                 (_⋆_ : ⟨ G ⟩ → T → T)
                 → isProp (IsTorsor G _⋆_)
isPropIsTorsor G _⋆_ =
  isOfHLevelRetractFromIso 1 IsTorsorIsoΣ
    (isPropΣ isPropIsSet λ isSetT →
    (isProp× (isPropΠ3 λ _ _ _ → isSetT _ _)
    (isProp× (isPropΠ λ _ → isSetT _ _)
    (isProp× (isPropΠ3 λ _ _ _ → is-set _ _)
    (isProp× (isPropΠ2 (λ _ _ → isPropPropTrunc))
    isPropPropTrunc)))))
    where
    open GroupStr (snd G)

𝒮ᴰ-Torsor : (G : Group ℓ) → DUARel (𝒮-Univ ℓ') (TorsorStr G) (ℓ-max ℓ ℓ')
𝒮ᴰ-Torsor G =
  𝒮ᴰ-Record (𝒮-Univ _) (IsTorsorEquiv {G = G})
    (fields:
      data[ _⋆_ ∣ autoDUARel _ _ ∣ pres⋆ ]
      prop[ isTorsor ∣ (λ _ _ → isPropIsTorsor _ _) ])
  where
  open TorsorStr
  open IsTorsorHom

TorsorPath : {G : Group ℓ} (T T' : Torsor G ℓ') → TorsorEquiv T T' ≃ (T ≡ T')
TorsorPath {G = G} = ∫ (𝒮ᴰ-Torsor G) .UARel.ua

TorsorHomPath : {G : Group ℓ} (T T' : Torsor G ℓ') → TorsorHom T T' ≃ (T ≡ T')
TorsorHomPath T T' =
  TorsorHom T T'    ≃⟨ invEquiv (Σ-contractSnd (λ f → isEquivTorsorHom f , (λ _ → isPropIsEquiv (fst f) _ _))) ⟩
  Σ[ f ∈ TorsorHom T T' ] isEquiv (fst f)                                 ≃⟨ Σ-assoc-≃ ⟩
  Σ[ f ∈ (⟨ T ⟩ → ⟨ T' ⟩) ] (IsTorsorHom (snd T) f (snd T') × isEquiv f)  ≃⟨ Σ-cong-equiv-snd (λ f → Σ-swap-≃) ⟩
  Σ[ f ∈ (⟨ T ⟩ → ⟨ T' ⟩) ] (isEquiv f × IsTorsorHom (snd T) f (snd T'))  ≃⟨ invEquiv Σ-assoc-≃ ⟩
  TorsorEquiv T T'                                                        ≃⟨ (TorsorPath T T') ⟩
  T ≡ T'                                                                  ■


{-

  open RingStr (snd R) using (1r; ·DistL+) renaming (_+_ to _+r_; _·_ to _·s_)


record IsAlgebraHom {R : Ring ℓ} {A : Type ℓ'} {B : Type ℓ''}
  (M : AlgebraStr R A) (f : A → B) (N : AlgebraStr R B)
  : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  where

  -- Shorter qualified names
  private
    module M = AlgebraStr M
    module N = AlgebraStr N

  field
    pres0 : f M.0a ≡ N.0a
    pres1 : f M.1a ≡ N.1a
    pres+ : (x y : A) → f (x M.+ y) ≡ f x N.+ f y
    pres· : (x y : A) → f (x M.· y) ≡ f x N.· f y
    pres- : (x : A) → f (M.- x) ≡ N.- (f x)
    pres⋆ : (r : ⟨ R ⟩) (y : A) → f (r M.⋆ y) ≡ r N.⋆ f y

unquoteDecl IsAlgebraHomIsoΣ = declareRecordIsoΣ IsAlgebraHomIsoΣ (quote IsAlgebraHom)
open IsAlgebraHom

private
  variable
    R : Ring ℓ
    A B : Algebra R ℓ

AlgebraHom : (M : Algebra R ℓ') (N : Algebra R ℓ'') → Type _
AlgebraHom M N = Σ[ f ∈ (⟨ M ⟩ → ⟨ N ⟩) ] IsAlgebraHom (M .snd) f (N .snd)

IsAlgebraEquiv : {A : Type ℓ'} {B : Type ℓ''}
  (M : AlgebraStr R A) (e : A ≃ B) (N : AlgebraStr R B)
  → Type _
IsAlgebraEquiv M e N = IsAlgebraHom M (e .fst) N

AlgebraEquiv : (M : Algebra R ℓ') (N : Algebra R ℓ'') → Type _
AlgebraEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsAlgebraEquiv (M .snd) e (N .snd)

_$a_ : AlgebraHom A B → ⟨ A ⟩ → ⟨ B ⟩
f $a x = fst f x

AlgebraEquiv→AlgebraHom : AlgebraEquiv A B → AlgebraHom A B
AlgebraEquiv→AlgebraHom (e , eIsHom) = e .fst , eIsHom

isPropIsAlgebra : (R : Ring ℓ) {A : Type ℓ'}
  (0a 1a : A)
  (_+_ _·_ : A → A → A)
  (-_ : A → A)
  (_⋆_ : ⟨ R ⟩ → A → A)
  → isProp (IsAlgebra R 0a 1a _+_ _·_ -_ _⋆_)
isPropIsAlgebra R _ _ _ _ _ _ = let open IsLeftModule in
  isOfHLevelRetractFromIso 1 IsAlgebraIsoΣ
    (isPropΣ
      (isPropIsLeftModule _ _ _ _ _)
      (λ mo → isProp×4 (isPropIsMonoid _ _)
                       (isPropΠ3 λ _ _ _ → mo .is-set _ _)
                       (isPropΠ3 λ _ _ _ → mo .is-set _ _)
                       (isPropΠ3 λ _ _ _ → mo .is-set _ _)
                       (isPropΠ3 λ _ _ _ → mo .is-set _ _) ))


isPropIsAlgebraHom : (R : Ring ℓ) {A : Type ℓ'} {B : Type ℓ''}
                     (AS : AlgebraStr R A) (f : A → B) (BS : AlgebraStr R B)
                   → isProp (IsAlgebraHom AS f BS)
isPropIsAlgebraHom R AS f BS = isOfHLevelRetractFromIso 1 IsAlgebraHomIsoΣ
                               (isProp×5 (isSetAlgebra (_ , BS) _ _)
                                         (isSetAlgebra (_ , BS) _ _)
                                         (isPropΠ2 λ _ _ → isSetAlgebra (_ , BS) _ _)
                                         (isPropΠ2 λ _ _ → isSetAlgebra (_ , BS) _ _)
                                         (isPropΠ λ _ → isSetAlgebra (_ , BS) _ _)
                                         (isPropΠ2 λ _ _ → isSetAlgebra (_ , BS) _ _))

isSetAlgebraHom : (M : Algebra R ℓ') (N : Algebra R ℓ'')
                → isSet (AlgebraHom M N)
isSetAlgebraHom _ N = isSetΣ (isSetΠ (λ _ → isSetAlgebra N))
                        λ _ → isProp→isSet (isPropIsAlgebraHom _ _ _ _)


isSetAlgebraEquiv : (M : Algebra R ℓ') (N : Algebra R ℓ'')
                  → isSet (AlgebraEquiv M N)
isSetAlgebraEquiv M N = isSetΣ (isOfHLevel≃ 2 (isSetAlgebra M) (isSetAlgebra N))
                          λ _ → isProp→isSet (isPropIsAlgebraHom _ _ _ _)

AlgebraHom≡ : {φ ψ : AlgebraHom A B} → fst φ ≡ fst ψ → φ ≡ ψ
AlgebraHom≡ = Σ≡Prop λ f → isPropIsAlgebraHom _ _ f _

𝒮ᴰ-Algebra : (R : Ring ℓ) → DUARel (𝒮-Univ ℓ') (AlgebraStr R) (ℓ-max ℓ ℓ')
𝒮ᴰ-Algebra R =
  𝒮ᴰ-Record (𝒮-Univ _) (IsAlgebraEquiv {R = R})
    (fields:
      data[ 0a ∣ nul ∣ pres0 ]
      data[ 1a ∣ nul ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
      data[ _⋆_ ∣ autoDUARel _ _ ∣ pres⋆ ]
      prop[ isAlgebra ∣ (λ _ _ → isPropIsAlgebra _ _ _ _ _ _ _) ])
  where
  open AlgebraStr

  -- faster with some sharing
  nul = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

AlgebraPath : (A B : Algebra R ℓ') → (AlgebraEquiv A B) ≃ (A ≡ B)
AlgebraPath {R = R} = ∫ (𝒮ᴰ-Algebra R) .UARel.ua

uaAlgebra : AlgebraEquiv A B → A ≡ B
uaAlgebra {A = A} {B = B} = equivFun (AlgebraPath A B)

isGroupoidAlgebra : isGroupoid (Algebra R ℓ')
isGroupoidAlgebra _ _ = isOfHLevelRespectEquiv 2 (AlgebraPath _ _) (isSetAlgebraEquiv _ _)

-- Smart constructor for algebra homomorphisms
-- that infers the other equations from pres1, pres+, pres·, and pres⋆

module _
  -- Variable generalization would fail below without the module parameters A and B.
  {A : Algebra R ℓ}
  {B : Algebra R ℓ'}
  {f : ⟨ A ⟩ → ⟨ B ⟩}
  where

  private
    module A = AlgebraStr (A .snd)
    module B = AlgebraStr (B .snd)

  module _
    (p1 : f A.1a ≡ B.1a)
    (p+ : (x y : ⟨ A ⟩) → f (x A.+ y) ≡ f x B.+ f y)
    (p· : (x y : ⟨ A ⟩) → f (x A.· y) ≡ f x B.· f y)
    (p⋆ : (r : ⟨ R ⟩) (x : ⟨ A ⟩) → f (r A.⋆ x) ≡ r B.⋆ f x)
    where

    open IsAlgebraHom
    private
      isGHom : IsGroupHom (Algebra→Group A .snd) f (Algebra→Group B .snd)
      isGHom = makeIsGroupHom p+

    makeIsAlgebraHom : IsAlgebraHom (A .snd) f (B .snd)
    makeIsAlgebraHom .pres0 = isGHom .IsGroupHom.pres1
    makeIsAlgebraHom .pres1 = p1
    makeIsAlgebraHom .pres+ = p+
    makeIsAlgebraHom .pres· = p·
    makeIsAlgebraHom .pres- = isGHom .IsGroupHom.presinv
    makeIsAlgebraHom .pres⋆ = p⋆

-- -}
