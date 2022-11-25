-- Category of Agda types and functions

open import Category
open import CategoryRecord
open import Agda.Primitive

open import Level

open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
open import Data.List.Relation.Unary.Any
-- open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Algebra.Definitions
-- open import Function.Equality hiding

-- open Setoid

-- open ≡-Reasoning

-- Congruent : {A : Set} -> Rel A -> Set
-- Congruent {A} _R_ = (f : A -> A)(x y : A) -> x R y -> f x R f y

module Agda
  {ℓ : Level}
  where

-- Congruence : ∀ {m} {A} → (A → A → Set m) → Set (lsuc m)
-- Congruence {m} _R_ =
--   ∀ {A B : Set m} → (f : A → B) →
--                {x x′ : A} →
--                x R x′ →
--                f x R f x′

-- Congruence₂ : ∀ {m} → (∀ {A : Set m} → A → A → Set m) → Set (lsuc m)
  -- Congruence₂ {m} _R_ =
  --   ∀ {A B C : Set m} → (f : A → B → C) →
  --                {x x′ : A} → {y y′ : B} →
--                x R x′ →
--                y R y′ →
--                f x y R f x′ y′

-- open IsEquivalence ≈-equiv
-- _Agda-≈_ : ∀ {A B : Set} → (f g : Lift (lsuc ℓ) (A → B)) → Set (lsuc ℓ)
-- _Agda-≈_ = λ f g → (∀ x → Lift (lsuc ℓ) (lower f x ≈ lower g x))

-- Agda : Set (suc o) → Category (suc o) o (o ⊔ e)
Agda : Category (suc ℓ) ℓ
Agda = record
  { Obj = Set ℓ
  ; _⇒_ = λ A B → (A → B)
  ; _∘_ = λ f g → λ z → f (g z)
  ; id = λ x → x
  ; left-id = refl
  ; right-id = refl
  ; ∘-assoc = refl
  }


-- Hom-Initial : {ℂ : Category e (suc ℓ) e} →
--   {𝟘 : Category.Obj ℂ} → CategoryProperties.IsInitial ℂ 𝟘 →
--   ∀ {A B} →
--   (f : Hom {ℂ} A 𝟘) →
--   (g : Hom {ℂ} A B)


-- ¬Hom𝟘 : ∀ {ℂ : Category e (suc ℓ) e} →
--   {𝟘 : Category.Obj ℂ} → CategoryProperties.IsInitial ℂ 𝟘 →
--   ∀ {A} →
--   ¬ (Hom {ℂ} A 𝟘)
-- ¬Hom𝟘 {ℂ} {𝟘} 𝟘-initial {A} prf = {!!}



open Category.Category Agda
open CategoryProperties Agda

-- open import Axiom.Extensionality.Propositional

-- postulate fun-ext : ∀ {m n} → Extensionality m n

⊤-lift-canon : ∀ {A : Set ℓ} → (x : A → Lift ℓ ⊤) → x ≡ λ _ → lift tt
⊤-lift-canon f = fun-ext λ x → refl
-- ⊤-lift-canon (lift tt) = refl

⊤-IsTerminal : IsTerminal (Lift ℓ ⊤)
⊤-IsTerminal = λ A → (λ _ → lift tt) , (tt , (λ n x → (⊤-lift-canon n)))

⊥-IsInitial : IsInitial (Lift ℓ ⊥)
⊥-IsInitial = λ B → (λ x → ⊥-elim (lower x)) , tt , λ n x → (fun-ext λ x₁ → ⊥-elim (lower x₁))

⊤-IsSeparator : IsSeparator (Lift ℓ ⊤)
⊤-IsSeparator {A} {B} {f₁} {f₂} = λ g → (fun-ext (λ x →
  let
    z a = (g (λ _ → a))

    w0 : ∀ a b → (λ z₁ → f₁ a) b ≡ (λ z₁ → f₂ a) b
    w0 a b = cong (λ x₁ → x₁ b) (z a)

    w1 : ∀ a → f₁ a ≡ f₂ a
    w1 a = w0 a (lift tt)
  in
  w1 x))
-- ⊤-IsSeparator = λ f x → (f (λ _ → x) (lift tt))

nondegen : Nondegenerate ⊤-IsTerminal ⊥-IsInitial
nondegen = λ z → lower (proj₁ z (lift tt)) -- lift λ z → lower (proj₁ z (lift tt))

-- ×-canon : ∀  {A B : Set (suc ℓ)} {a×b : A × B} → a×b ≈ₒ (proj₁ a×b , proj₂ a×b)
-- ×-canon {_} {_} {_} {fst , snd} = IsEquivalence.refl ≈ₒ-equiv

×-IsProduct : ∀ A B → IsProduct A B (A × B)
×-IsProduct A B =
  proj₁ , proj₂ , λ f g → (λ x → f x , g x) , (refl ,
    refl) , λ n (s , t) →
      (cong₂ (λ f g x → f x , g x) (sym s) (sym t))

⊎-match : ∀ {m} {A B X : Set m} (a+b : A ⊎ B) (f : A → X) (g : B → X) → X
⊎-match (inj₁ x) f g = f x
⊎-match (inj₂ y) f g = g y

⊎-canon : ∀ {A B : Set o} (X : Set o) (a+b : A ⊎ B) {f : A → X} {g : B → X} {h : A ⊎ B → X} →
  (∀ a → f a ≡ h (inj₁ a)) →
  (∀ b → g b ≡ h (inj₂ b)) →
  h a+b ≡ ⊎-match a+b f g
⊎-canon _ (inj₁ x) prf-1 prf-2 = sym (prf-1 x)
⊎-canon _ (inj₂ y) prf-1 prf-2 = sym (prf-2 y)

⊎-canon-ext : ∀ {A B : Set o} (X : Set o) {f : A → X} {g : B → X} {h : A ⊎ B → X} →
  (f ≡ λ a → h (inj₁ a)) →
  (g ≡ λ b → h (inj₂ b)) →
  h ≡ λ x → ⊎-match x f g
⊎-canon-ext {A} {B} X {f} {g} {h} refl refl = fun-ext λ x → ⊎-canon {A} {B} X x {f} {g} {h} (λ a → refl) λ b → refl

⊎-IsCoproduct : ∀ {A B} → IsCoproduct A B (A ⊎ B)
⊎-IsCoproduct {A} {B} =
  inj₁ , inj₂ , λ {X} f g → (λ x → ⊎-match x (f) (g)) , (refl , refl) ,
    λ n (p , q) → (⊎-canon-ext X p q)

→true : Lift ℓ ⊤ ⇒ Lift ℓ Bool
→true = λ tt → lift true

→false : Lift ℓ ⊤ ⇒ Lift ℓ Bool
→false = λ tt → lift false

Agda-nondegen : Nondegenerate ⊤-IsTerminal ⊥-IsInitial
Agda-nondegen = λ z → lower (proj₁ z (lift tt)) -- lift (λ x → lower (proj₁ x (lift tt)))

-- Bool-IsCoseparator : IsCoseparator Bool
-- Bool-IsCoseparator {T} {A} {a₀} {a₁} f x =
--   let
--     z = ⊤-IsSeparator (λ x₁ x₂ → {!!}) A
--   in
--   {!!}

