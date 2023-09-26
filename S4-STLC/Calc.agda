-- Based partly on "Naive logical relations in synthetic Tait computability" by Sterling

-- {-# OPTIONS --cumulativity #-}

{-# OPTIONS --cubical #-}

-- open import Relation.Binary.PropositionalEquality hiding (Extensionality)
-- open import Axiom.Extensionality.Propositional

-- open import cubical-prelude hiding
open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation


open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Function hiding (_↔_ ; Bijective)

open import Agda.Primitive
open import Level

open import Relation.Binary

module Calc
  (ϕ : Set)
  (ϕ-prop : ∀ {a b : ϕ} → a ≡ b)
  where

funext : ∀ {ℓ} {A B : Set ℓ} {f g : A → B} → (p : (x : A) → f x ≡ g x) → f ≡ g
funext p i x = p x i

record LC {ℓ : Level} : Set (lsuc ℓ) where
  field
    Type : Set ℓ
    El : Type → Set ℓ

    _:→_ : Type → Type → Type

    lam : ∀ {σ τ} → (El σ → El τ) → El (σ :→ τ)
    _·_ : ∀ {σ τ} → El (σ :→ τ) → El σ → El τ

    arrβ : ∀ {σ τ} {u : El σ → El τ} {v} →
      ((lam u) · v) ≡ u v

    arrη : ∀ {σ τ} {u : El (σ :→ τ)} →
      u ≡ lam (λ x → u · x)

    _⊗_ : Type → Type → Type
    pair : ∀ {σ τ} → El σ → El τ → El (σ ⊗ τ)
    fst : ∀ {σ τ} → El (σ ⊗ τ) → El σ
    snd : ∀ {σ τ} → El (σ ⊗ τ) → El τ

    prodβ1 : ∀ {σ τ} {u v} → fst (pair {σ} {τ} u v) ≡ u
    prodβ2 : ∀ {σ τ} {u v} → snd (pair {σ} {τ} u v) ≡ v

    prodη : ∀ {σ τ} {u} →
      u ≡ pair {σ} {τ} (fst u) (snd u)

    bool : Type
    true : El bool
    false : El bool
    ite : ∀ {σ} → El bool → El σ → El σ → El σ
    boolβ1 : ∀ {σ} {u v} → ite {σ} true u v ≡ u
    boolβ2 : ∀ {σ} {u v} → ite {σ} false u v ≡ v

    boolη : ∀ {σ} {u : El bool → El σ} →
      u ≡ λ x → ite x (u true) (u false)

Σ! : ∀ {ℓ} → {A : Set ℓ} → (A → Set ℓ) → Set ℓ
Σ! P = ∃[ a ] (P a × ∀ b → P b → (b ≡ a))

_↔_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
_↔_ A B = (A → B) × (B → A)

Bijective : ∀ {ℓ} {A B : Set ℓ} → (A → B) → Set ℓ
Bijective f = ∀ x y → (f x ≡ f y) ↔ (x ≡ y)

Bijective-Inv : ∀ {ℓ} {A B : Set ℓ} → (A → B) → Set ℓ
Bijective-Inv {_} {A} {B} f = Σ (B → A) λ g → (∀ x → f (g x) ≡ x) × (∀ y → g (f y) ≡ y)

-- These next two things seem related to some
-- of the topics discussed in Escardo's synthetic topology of data types book:

-- Object-space
ϕ-transparent : ∀ {ℓ} → Set ℓ → Set ℓ
ϕ-transparent A = ∀ (u : ϕ → A) → Σ! λ a → u ≡ λ z → a

-- Meta-space
ϕ-sealed : ∀ {ℓ} → Set ℓ → Set (suc zero ⊔ ℓ)
ϕ-sealed A = (ϕ ≡ ⊤) → ∀ (a b : A) → a ≡ b

-- const≡ : ∀ {ℓ m} {A : Set ℓ} {X : Set m} {a b : A} → (λ (x : X) → a) ≡ (λ y → b) → a ≡ b
-- const≡ eq = {!!}

ap : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f p = λ i → f (p i)

ϕ-transparent-unique : ∀ {ℓ} {A : Set ℓ} →
  (u : ϕ → A) →
  ∀ a b → u a ≡ u b
ϕ-transparent-unique u a b = ap u ϕ-prop

-- ϕ-transparent-const : ∀ {ℓ} {A : Set ℓ} →
--   (A-obj : ϕ-transparent A) →
--   (u : ϕ → A) →
--   ∀ a →
--   u ≡ λ _ → u a
-- ϕ-transparent-const A-obj u a = {!!}

-- ϕ-transparent-lemma : ∀ {ℓ} {A B : Set ℓ} →
--   (A-obj : ϕ-transparent A) →
--   (f : (ϕ → A) → A) →
--   (g : ϕ → A) →
--   (a : ϕ) →
--   f g ≡ f (λ _ → g a)
-- ϕ-transparent-lemma A-obj f g a = {!!}

-- ϕ-transparent≡ : ∀ {ℓ} {A : Set ℓ} →
--   ϕ-transparent A →
--   ∀ {x y : ϕ → A} →
--   ((a : ϕ) → x a ≡ y a) →
--   ϕ-transparent (x ≡ y)
-- ϕ-transparent≡ A-obj eq u = {!!} , {!!} , {!!}

-- const≡ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} →
--   ∀ {x y : A} →
--   x ≡ y →
--   (λ (_ : B) → x) ≡ (λ _ → y)
-- const≡ = {!!}

-- ϕ-transparent-lift : ∀ {ℓ} {A B : Set ℓ} →
--   (A-obj : ϕ-transparent A) →
--   (f : (ϕ → A) → A) →
--   (g : ϕ → A) →
--   ((a : ϕ) → f g ≡ f (λ _ → g a)) →
--   proj₁ (A-obj (λ z → f (λ _ → g z))) ≡ f g
-- ϕ-transparent-lift A-obj f g eq =
--   let
--     p = ϕ-transparent≡ {{!!}} {{!!}} A-obj {{!!}} {{!!}} eq {!!}
--   in
--   {!!}



-- -- Lemma 7 in the Sterling paper
-- object-space-universal : ∀ {ℓ} {A B : Set ℓ} →
--   ϕ-transparent B →
--   Bijective-Inv
--     {ℓ}
--     {(ϕ → A) → B}
--     {A → B}
--     (λ f a → f (λ _ → a))
-- object-space-universal {ℓ} {A} {B} B-obj =
--   (λ z z₁ → pr₁ (B-obj (λ z₂ → z (z₁ z₂)))) ,
--   (λ x → funext λ x₁ → λ i → {!transp!}) ,
--   {!!}



--   (λ g h → proj₁ (B-obj (λ z → g (h z)))) , left , λ g → funext (right g)
--   where
--     left : (g : A → B) → (λ a → proj₁ (B-obj (λ z → g a))) ≡ g
--     left g =
--       funext λ a →
--       let z , w = proj₂ (B-obj (λ z → g a))
--       in
--       sym (w (g a) refl)

--     right : (g : (ϕ → A) → B) → ∀ h → proj₁ (B-obj (λ z → g (λ _ → h z))) ≡ g h
--     right g h rewrite (proj₁ (proj₂ (B-obj λ _ → g h))) = {!!}
--     -- right g h rewrite (ϕ-transparent-const B-obj (λ _ → g h) {!!}) = {!!}
--     -- right g h rewrite (sym (proj₂ (proj₂ (B-obj (λ z → g (λ _ → h z)))) (g h) {!!})) = {!!}
--       -- funext λ h →
--       -- let z , w = proj₂ (B-obj (λ z → g (λ _ → h z)))
--       --     q s = w (g (λ _ → h s))
--       --     u₁ , u₂ , u₃ = B-obj λ _ → g h
--       --     prf r = ϕ-transparent-const B-obj λ _ → g r
--       -- in
--       -- sym {!u₂!}

--     -- left : (λ a → x (λ _ → a)) ≡ (λ a → y (λ _ → a)) → x ≡ y
--     -- left eq = funext λ x₁ → let z = (λ a → x (λ _ → a)) {!!} in {!!}

--     -- right : x ≡ y → (λ a → x (λ _ → a)) ≡ (λ a → y (λ _ → a))
--     -- right refl = refl

-- data _/_ {ℓ} (A : Set ℓ) (R : A → A → Set) : Set ℓ where
--   [_] : A → A / R
--   eq/ : (a b : A) → R a b → [ a ] ≡ [ b ]
--   trunc : isSet (A / R) -- (a b : A / R) (p q : a ≡ b) → p ≡ q

ϕ∙ : ∀ (A : Set) → Set
ϕ∙ A = (ϕ ⊎ A) / R
  where
    R : ϕ ⊎ A → ϕ ⊎ A → Set
    R u v = ϕ ⊎ (u ≡ v)

ηϕ : ∀ {A : Set} → A → ϕ∙ A
ηϕ x = [ inj₂ x ]

ϕ[] : ∀ {A : Set} → ϕ ⊎ A → ϕ∙ A
ϕ[] x = [ x ]

ϕ∙is-sealed : ∀ {A : Set} →
  ϕ-sealed (ϕ∙ A)
-- ϕ∙is-sealed p [ x ] [ y ] = eq/ x y (inj₁ (transport (sym p) tt))
ϕ∙is-sealed p x y = elimProp (squash/ x) (λ { (inj₁ q) → {!!} }) y
-- ϕ∙is-sealed p (eq/ a b x j) (eq/ a₁ b₁ x₁ j₁) i = elimProp (squash/ (eq/ a b x j)) (λ z → {!!}) (eq/ a₁ b₁ x₁ j₁) {!!}
  --trunc (ϕ∙is-sealed p [ a ] [ b ] (~ j)) {!!} {!!} {!!} {!!} -- eq/ x x₁ (inj₁ (transport (sym p) tt))
-- ϕ∙-is-sealed p [ inj₁ x ] [ inj₁ x₁ ] = let z = ϕ-prop {x} {x₁} in ap (λ z → [ inj₁ z ]) z
-- ϕ∙-is-sealed p [ inj₁ x ] [ inj₂ y ] i = eq/ {!!} {!!} (inj₁ x) {!!}
-- ϕ∙-is-sealed p [ inj₂ y ] [ inj₁ x ] i = {!!}
-- ϕ∙-is-sealed p [ inj₂ y ] [ inj₂ y₁ ] i = {!!}
-- ϕ∙-is-sealed p [ x ] (eq/ a b x₁ i₁) i = {!!}
-- ϕ∙-is-sealed p [ x ] (trunc b b₁ x₁ y i₁ i₂) i = {!!}
-- ϕ∙-is-sealed p (eq/ a b x i₁) [ x₁ ] i = {!!}
-- ϕ∙-is-sealed p (eq/ a b x i₁) (eq/ a₁ b₁ x₁ i₂) i = {!!}
-- ϕ∙-is-sealed p (eq/ a b x i₁) (trunc b₁ b₂ x₁ y i₂ i₃) i = {!!}
-- ϕ∙-is-sealed p (trunc a a₁ x y i₁ i₂) [ x₁ ] i = {!!}
-- ϕ∙-is-sealed p (trunc a a₁ x y i₁ i₂) (eq/ a₂ b x₁ i₃) i = {!!}
-- ϕ∙-is-sealed p (trunc a a₁ x y i₁ i₂) (trunc b b₁ x₁ y₁ i₃ i₄) i = {!!}


-- data ϕ∙ {ℓ} (A : Set ℓ) : Set ℓ where
--   mk-ϕ∙ : ϕ ⊎ A → ϕ∙ A
--   ϕ∙≡ : ()

-- -- Meta-space component
-- ϕ∙ : ∀ {ℓ} → (A : Set ℓ) → Setoid ℓ ℓ
-- ϕ∙ A =
--   record
--     { Carrier = ϕ ⊎ A
--     ; _≈_ = λ u v → ϕ ⊎ (u ≡ v)
--     ; isEquivalence = record
--                         { refl = inj₂ refl
--                         ; sym = λ { (inj₁ p) → inj₁ p
--                                   ; (inj₂ q) → inj₂ (sym q) }
--                         ; trans = λ { (inj₁ p) _ → inj₁ p
--                                     ; _ (inj₁ q) → inj₁ q
--                                     ; (inj₂ p) (inj₂ q) → inj₂ (trans p q)
--                                     }

--     }

-- ϕ∙-simple : ∀ {ℓ} (A : Set ℓ) → ϕ∙ A → ϕ ⊎ A
-- ϕ∙-simple = ?

-- ϕ∙-is-sealed : ∀ {ℓ} {A : Set ℓ} →
--   ϕ-sealed (ϕ∙ A)
-- ϕ∙-is-sealed = ?

