-- Based on https://plfa.github.io/DeBruijn/

open import Data.Nat
open import Data.Product
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)

module Cont
  where

Name : Set
Name = ℕ

data Type : Set where
  Unit : Type
  _⇒_ : Type → Type → Type
  □_ : Type → Type

data Context : Set where
  ∅ : Context
  _,,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  V-here : ∀ {Γ a} →
    (Γ ,, a) ∋ a
  V-there : ∀ {Γ a b} →
    Γ ∋ a →
    (Γ ,, b) ∋ a

data Expr : Context → Type → Set where
  V : ∀ {Γ a} →
    Γ ∋ a →
    Expr Γ a

  _·_ : ∀ {Γ a b} →
    Expr Γ (a ⇒ b) →
    Expr Γ a →
    Expr Γ b

  ƛ_ : ∀ {Γ a b} →
    Expr (Γ ,, a) b →
    Expr Γ (a ⇒ b)

  unit : ∀ {Γ} → Expr Γ Unit

  box : ∀ {Γ a} → (e : Expr ∅ a) → Expr Γ (□ a)

---- Adapted from https://plfa.github.io/DeBruijn/
ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → (Γ ,, B) ∋ A → (Δ ,, B) ∋ A)
ext ρ V-here       =  V-here
ext ρ (V-there x)  =  V-there (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Expr Γ A → Expr Δ A)
rename ρ (V x)          =  V (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (box e)        = box e
rename ρ unit           = unit

exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Expr Δ A)
    ---------------------------------
  → (∀ {A B} → (Γ ,, B) ∋ A → Expr (Δ ,, B) A)
exts σ V-here      =  V V-here
exts σ (V-there x)  =  rename V-there (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Expr Δ A)
    -----------------------
  → (∀ {A} → Expr Γ A → Expr Δ A)
subst σ (V k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (box e)        = box e
subst σ unit           = unit

_[_] : ∀ {Γ A B}
  → Expr (Γ ,, B) A
  → Expr Γ B
    ---------
  → Expr Γ A
_[_] {Γ} {A} {B} N M =  subst {Γ ,, B} {Γ} σ {A} N
  where
  σ : ∀ {A} → (Γ ,, B) ∋ A → Expr Γ A
  σ V-here       =  M
  σ (V-there x)  =  V x

length : Context → ℕ
length ∅         =  zero
length (Γ ,, _)  =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ ,, A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ ,, _)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ ,, _} {zero}    (s≤s z≤n)  =  V-here
count {Γ ,, _} {(suc n)} (s≤s p)    =  V-there (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Expr Γ (lookup (toWitness n∈Γ))
#_ n {n∈Γ}  =  V (count (toWitness n∈Γ))

----

data Is-Value : ∀ {Γ a} → Expr Γ a → Set where
  Is-Value-ƛ : ∀ {Γ a b} →
    (e : Expr (Γ ,, a) b) →
    Is-Value (ƛ e)

  Is-Value-unit : ∀ {Γ} →
    Is-Value {Γ} unit


data _⟶_ : ∀ {Γ a} → Expr Γ a → Expr Γ a → Set where
  ⟶β : ∀ {Γ a b} →
    (e₁ : Expr (Γ ,, a) b) →
    (e₂ : Expr Γ a) →
    ((ƛ e₁) · e₂) ⟶ (e₁ [ e₂ ])

  -- ⟶K : ∀ {Γ a b} →
  --   Expr Γ (□ (a ⇒ b)) →
  --   Expr Γ ((□ a) ⇒ (□ b))

  -- ⟶app-left : ∀ {Γ a b} →
  --   (e₁ e₁′ : Expr Γ (a ⇒ b)) →
  --   (e₂ : Expr Γ a) →
  --   e₁ ⟶ e₁′ →
  --   (e₁ · e₂) ⟶ (e₁′ · e₂)

  -- ⟶app-right : ∀ {Γ a b} →
  --   (e₁ : Expr Γ (a ⇒ b)) →
  --   (e₂ e₂′ : Expr Γ a) →
  --   Is-Value e₁ →
  --   e₂ ⟶ e₂′ →
  --   (e₁ · e₂) ⟶ (e₁ · e₂′)


-- One-hole evaluation context (call-by-name)
data 𝓔 : (Γ Δ : Context) → (h a : Type) → Set where
  𝓔[] : ∀ {Δ h} → 𝓔 Δ Δ h h

  𝓔-app-left : ∀ {Γ Δ h a b} →
    (e₁ : 𝓔 Γ Δ h (a ⇒ b)) →
    (e₂ : Expr Γ a) →
    𝓔 Γ Δ h b

  𝓔-app-right : ∀ {Γ Δ h a b} →
    (e₁ : Expr Γ (a ⇒ b)) →
    (e₂ : 𝓔 Γ Δ h a) →
    Is-Value e₁ →
    𝓔 Γ Δ h b

  𝓔ƛ : ∀ {Γ Δ h a b} →
    (e : 𝓔 (Γ ,, a) (Δ ,, a) h b) →
    𝓔 Γ Δ h (a ⇒ b)

  𝓔□ : ∀ {Γ h a} →
    (e : 𝓔 ∅ ∅ h a) →
    𝓔 Γ ∅ (□ h) (□ a)

fill-𝓔 : ∀ {Γ Δ h a} → 𝓔 Γ Δ h a → Expr Δ h → Expr Γ a
fill-𝓔 𝓔[] e = e
fill-𝓔 (𝓔-app-left E e₂) e = (fill-𝓔 E e) · e₂
fill-𝓔 (𝓔-app-right e₁ E x) e = e₁ · (fill-𝓔 E e)
fill-𝓔 (𝓔ƛ E) e = ƛ (fill-𝓔 E (rename V-there e))
fill-𝓔 (𝓔□ E) e = box {!!}
-- fill-𝓔 (𝓔□ E) (V x) = box {!!}
-- fill-𝓔 (𝓔□ E) (e · e₁) = box {!!}
-- fill-𝓔 (𝓔□ E) (box e) = box (fill-𝓔 {!!} {!!})

-- _[[_]] : ∀ {Γ h a} → 𝓔 Γ h a → Expr Γ h → Expr Γ a
-- _[[_]] = fill-𝓔

-- data _⟶𝓔_ : ∀ {Γ a} → Expr Γ a → Expr Γ a → Set where
--   ⟶𝓔step : ∀ {Γ h a} →
--     (E : 𝓔 Γ h a) →
--     (e e′ : Expr Γ h) →
--     e ⟶ e′ →
--     (E [[ e ]]) ⟶𝓔 (E [[ e′ ]])

-- data _⟶𝓔*_ : ∀ {Γ a} → Expr Γ a → Expr Γ a → Set where
--   ⟶𝓔*refl : ∀ {Γ a} →
--     (e : Expr Γ a) →
--     e ⟶𝓔* e

--   ⟶𝓔*trans : ∀ {Γ a} →
--     (e e′ e′′ : Expr Γ a) →
--     e ⟶𝓔 e′ →
--     e′ ⟶𝓔* e′′ →
--     e ⟶𝓔* e′′

-- SN : ∀ {a} →
--   (e : Expr ∅ a) →
--   ∃[ e′ ] (e ⟶𝓔* e′ × Is-Value e′)
-- SN (e · e₁) = {!!}
-- SN (ƛ e) = (ƛ e) , ⟶𝓔*refl (ƛ e) , Is-Value-ƛ e
-- SN unit = unit , ⟶𝓔*refl unit , Is-Value-unit
-- SN (box e) = {!!}
