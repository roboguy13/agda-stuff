-- {-# OPTIONS --cumulativity #-}

open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to Eq-subst)
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Level renaming (zero to lzero; suc to lsuc)

module Syntax
  where

infixr 4 _⇒_

-- data Kind : Set where
--   ⋆ : Kind

-- data Ty-Context : Set where
--   ∅ : Ty-Context
--   _,,_ : Ty-Context → Kind → Ty-Context

-- data _T∋_ : Ty-Context → Kind → Set where
--   T-Here : ∀ {Δ k} → (Δ ,, k) T∋ k
--   T-There : ∀ {Δ k k′} →
--     Δ T∋ k →
--     (Δ ,, k′) T∋ k

data Type {ℓ} (V : Set ℓ) : Set ℓ where
  Ty-Var : V → Type V
  Unit : Type V
  Pair : Type V → Type V → Type V
  Sum : Type V → Type V → Type V
  _⇒_ : Type V → Type V → Type V
  Forall : (V → Type V) → Type V

Type′ : ∀ {ℓ} → Set (lsuc ℓ)
Type′ {ℓ} = ∀ {V : Set ℓ} → Type V

Closed-Type : Set
Closed-Type = Type ⊥

-- Ty-Context→ℕ : ∀ {Δ} →
--   ∀ {k} → Δ T∋ k →
--   ℕ
-- Ty-Context→ℕ T-Here = zero
-- Ty-Context→ℕ (T-There x) = suc (Ty-Context→ℕ x)

-- data _⊢_type : Ty-Context → Type → Set where
--   Ty-V-type : ∀ {∁} {k i} →
--     (prf : ∁ T∋ k) →
--     Ty-Context→ℕ prf ≡ i →
--     ∁ ⊢ Ty-V i type
--   Unit-type : ∀ {∁} → ∁ ⊢ Unit type
--   Pair-type : ∀ {∁ A B} →
--     ∁ ⊢ A type →
--     ∁ ⊢ B type →
--     ∁ ⊢ Pair A B type
--   Sum-type : ∀ {∁ A B} →
--     ∁ ⊢ A type →
--     ∁ ⊢ B type →
--     ∁ ⊢ Sum A B type
--   ⇒-type : ∀ {∁ A B} →
--     ∁ ⊢ A type →
--     ∁ ⊢ B type →
--     ∁ ⊢ A ⇒ B type
--   Forall-type : ∀ {∁ k A} →
--     (∁ ,, k) ⊢ A type →
--     ∁ ⊢ Forall A type

data Context {ℓ} (V : Set ℓ) : Set ℓ where
  ∅ : Context V
  _,,_ : Context V → Type V → Context V

Context′ : Set₁
Context′ = ∀ {V} → Context V

-- data _⊢_ctx : Ty-Context → Context → Set where
--   ∅-ctx : ∀ {∁} →
--     ∁ ⊢ ∅ ctx

--   ,,-ctx : ∀ {∁} {Γ} {A} →
--     ∁ ⊢ A type →
--     ∁ ⊢ Γ ctx →
--     ∁ ⊢ (Γ ,, A) ctx

data _∋_ {ℓ} {V : Set ℓ} : Context V → Type V → Set ℓ where
  ∋-here : ∀ {Γ A} → (Γ ,, A) ∋ A
  ∋-there : ∀ {Γ A B} →
    Γ ∋ A →
    (Γ ,, B) ∋ A

_∋′_ : Context′ → Type′ → Set
_∋′_ Γ A = _∋_ {V = ⊤} Γ A

_,,′_ : Context′ → Type′ → Context′
_,,′_ Γ A = _,,_ Γ A

data Term {ℓ} (V : Set ℓ) : Set ℓ where
  unit : Term V
  var : ℕ → Term V
  ƛ : Term V → Term V
  _∙_ : Term V → Term V → Term V
  Λ : (V → Term V) → Term V -- Type abstraction
  _＠_ : Term V → V → Term V -- Type application
  pair : Term V → Term V → Term V
  fst : Term V → Term V
  snd : Term V → Term V
  inl : Term V → Term V
  inr : Term V → Term V
  match : Term V → Term V → Term V → Term V

Term′ : Set₁
Term′ = ∀ {V} → Term V

Context→ℕ : ∀ {ℓ} {V : Set ℓ} {Γ : Context V} →
  ∀ {A} → Γ ∋ A →
  ℕ
Context→ℕ ∋-here = zero
Context→ℕ (∋-there x) = suc (Context→ℕ x)


-- infix 3 [_]_⊢_⦂_
infix 3 _⊢_⦂_
data _⊢_⦂_ {ℓ} {V : Set ℓ} : Context V → Term V → Type V → Set (lsuc ℓ) where
  T-unit : ∀ {Γ : Context V} →
     Γ ⊢ unit ⦂ Unit

  T-var : ∀ {Γ : Context V} {A : Type V} {i} →
    (prf : Γ ∋ A) →
    Context→ℕ prf ≡ i →
    Γ ⊢ var i ⦂ A

  T-ƛ : ∀ {Γ : Context V} {A B : Type V} {t} →
    (Γ ,, A) ⊢ t ⦂ B →
    Γ ⊢ ƛ t ⦂ A ⇒ B

  T-∙ : ∀ {Γ : Context V} {A B : Type V} {s t} →
    Γ ⊢ s ⦂ A ⇒ B →
    Γ ⊢ t ⦂ A →
    Γ ⊢ s ∙ t ⦂ B

  T-Λ : ∀ {Γ : Context V} {F : V → Type V} {t : V → Term V} →
    (∀ A → Γ ⊢ t A ⦂ F A) →
    Γ ⊢ Λ t ⦂ Forall F

  T-＠ : ∀ {Γ : Context V} {F : V → Type V} {A} {t : Term V} →
    Γ ⊢ t ⦂ Forall F →
    Γ ⊢ t ＠ A ⦂ F A

  T-pair : ∀ {Γ : Context V} {A B s t} →
    Γ ⊢ s ⦂ A →
    Γ ⊢ t ⦂ B →
    Γ ⊢ pair s t ⦂ Pair A B

  T-fst : ∀ {Γ : Context V} {A B t} →
    Γ ⊢ t ⦂ Pair A B →
    Γ ⊢ fst t ⦂ A

  T-snd : ∀ {Γ : Context V} {A B t} →
    Γ ⊢ t ⦂ Pair A B →
    Γ ⊢ snd t ⦂ B

  T-inl : ∀ {Γ : Context V} {A B t} →
    Γ ⊢ t ⦂ A →
    Γ ⊢ inl t ⦂ Sum A B

  T-inr : ∀ {Γ : Context V} {A B t} →
    Γ ⊢ t ⦂ B →
    Γ ⊢ inr t ⦂ Sum A B

  T-match : ∀ {Γ : Context V} {A B C s t₁ t₂} →
    Γ ⊢ s ⦂ Sum A B →
    (Γ ,, A) ⊢ t₁ ⦂ C →
    (Γ ,, B) ⊢ t₂ ⦂ C →
    Γ ⊢ match s t₁ t₂ ⦂ C

-- -- _⊢_⦂_ : Context → Term → Type → Set
-- -- _⊢_⦂_ Γ t A = ∃[ ∁ ] ([ ∁ ] Γ ⊢ t ⦂ A)

-- -- typed-ctx : ∀ {∁} {Γ} {t A} →
-- --   [ ∁ ] Γ ⊢ t ⦂ A →
-- --   ∁ ⊢ Γ ctx
-- -- typed-ctx (T-unit x) = x
-- -- typed-ctx (T-V x prf x₁) = x
-- -- typed-ctx (T-ƛ (,,-ctx x x₁) t-typed) = x₁
-- -- typed-ctx (T-∙ x t-typed t-typed₁) = x
-- -- typed-ctx (T-Λ x y t-typed) = x
-- -- typed-ctx (T-＠ x x₁ t-typed) = x
-- -- typed-ctx (T-pair x t-typed t-typed₁) = x
-- -- typed-ctx (T-fst x t-typed) = x
-- -- typed-ctx (T-snd x t-typed) = x
-- -- typed-ctx (T-inl x t-typed) = x
-- -- typed-ctx (T-inr x t-typed) = x
-- -- typed-ctx (T-match x x₁ x₂ t-typed t-typed₁ t-typed₂) = x

ext : (ℕ → ℕ) → (ℕ → ℕ)
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : ∀ {ℓ} {V : Set ℓ} →
  (ℕ → ℕ) →
  Term V →
  Term V
rename ρ unit = unit
rename ρ (var x) = var (ρ x)
rename ρ (ƛ t) = ƛ (rename (ext ρ) t)
rename ρ (t₁ ∙ t₂) = rename ρ t₁ ∙ rename ρ t₂
rename ρ (Λ t) = Λ (λ v → rename ρ (t v))
rename ρ (t ＠ i) = rename ρ t ＠ i
rename ρ (pair t₁ t₂) = pair (rename ρ t₁) (rename ρ t₂)
rename ρ (fst t) = fst (rename ρ t)
rename ρ (snd t) = snd (rename ρ t)
rename ρ (inl t) = inl (rename ρ t)
rename ρ (inr t) = inr (rename ρ t)
rename ρ (match s t₁ t₂) =
  match (rename ρ s) (rename (ext ρ) t₁) (rename (ext ρ) t₂)

exts : ∀ {ℓ} {V : Set ℓ} →
  (ℕ → Term V) →
  (ℕ → Term V)
exts σ zero = var zero
exts σ (suc x) = rename suc (σ x)

subst : ∀ {ℓ} {V : Set ℓ} →
  (ℕ → Term V) →
  Term V →
  Term V
subst σ unit = unit
subst σ (var x) = σ x
subst σ (ƛ t) = ƛ (subst (exts σ) t)
subst σ (t₁ ∙ t₂) = subst σ t₁ ∙ subst σ t₂
subst σ (Λ t) = Λ (λ v → subst σ (t v))
subst σ (t ＠ x) = subst σ t ＠ x
subst σ (pair t₁ t₂) = pair (subst σ t₁) (subst σ t₂)
subst σ (fst t) = fst (subst σ t)
subst σ (snd t) = snd (subst σ t)
subst σ (inl t) = inl (subst σ t)
subst σ (inr t) = inr (subst σ t)
subst σ (match s t₁ t₂) =
  match (subst σ s) (subst (exts σ) t₁) (subst (exts σ) t₂)

subst1-σ : ∀ {ℓ} {V : Set ℓ} → Term V → ℕ → Term V
subst1-σ t zero = t
subst1-σ t (suc x) = var x

_[_] : ∀ {ℓ} {V : Set ℓ} →
  Term V →
  Term V →
  Term V
_[_] s t = subst (subst1-σ t) s

data _∋′_⦂_ {V} : Context V → ℕ → Type V → Set where
  ∋′-here : ∀ {Γ : Context V} {A} →
    (Γ ,, A) ∋′ 0 ⦂ A

  ∋′-there : ∀ {Γ : Context V} {A B} {x} →
    Γ ∋′ x ⦂ A →
    (Γ ,, B) ∋′ suc x ⦂ A

from-raw : ∀ {V} {Γ : Context V} {A x} →
  Γ ∋′ x ⦂ A →
  Γ ∋ A
from-raw ∋′-here = ∋-here
from-raw (∋′-there p) = ∋-there (from-raw p)

to-raw : ∀ {V} {Γ : Context V} {A} →
  Γ ∋ A →
  ∃[ x ] Γ ∋′ x ⦂ A
to-raw ∋-here = zero , ∋′-here
to-raw (∋-there p) =
  let x , q = to-raw p
  in
  suc x , ∋′-there q

to-raw-id : ∀ {V} {Γ : Context V} {A} {x} →
  Context→ℕ {Γ = Γ} {A = A} x ≡ proj₁ (to-raw x)
to-raw-id {_} {.(_ ,, A)} {A} {∋-here} = refl
to-raw-id {_} {.(_ ,, _)} {A} {∋-there x} rewrite to-raw-id {x = x} = refl

to-from-raw-id₁ : ∀ {V} {Γ : Context V} {A} {x : ℕ} {p} →
  proj₁ (to-raw {Γ = Γ} {A = A} (from-raw {x = x} p)) ≡ x
to-from-raw-id₁ {x = .0} {p = ∋′-here} = refl
to-from-raw-id₁ {x = .(suc _)} {p = ∋′-there p} rewrite to-from-raw-id₁ {p = p} = refl

Is-Renaming : ∀ {V} → Context V → Context V → (ℕ → ℕ) → Set
Is-Renaming Γ Δ ρ =
  -- Has-Retract ρ ×
  Σ (∀ {A} {x} →
      Γ ∋′ x ⦂ A →
      Δ ∋′ ρ x ⦂ A)
  λ ρ-renaming →
  ∀ {A} {z : Γ ∋ A} →
  ρ (Context→ℕ z) ≡ Context→ℕ (from-raw (ρ-renaming (proj₂ (to-raw z))))

Is-Subst : ∀ {V} → Context V → Context V → (ℕ → Term V) → Set₁
Is-Subst Γ Δ σ =
  ∀ {A} {x} →
    Γ ∋′ x ⦂ A →
    Δ ⊢ σ x ⦂ A

ext-Is-Renaming : ∀ {V} {Γ Δ : Context V} {A} {ρ} →
  Is-Renaming Γ Δ ρ →
  Is-Renaming (Γ ,, A) (Δ ,, A) (ext ρ)
ext-Is-Renaming {_} {Γ} {Δ} {ρ = ρ} (renames , eq) =
  (λ { {x = zero} ∋′-here → ∋′-here
     ; {x = suc x} (∋′-there z) → ∋′-there (renames z) })
  ,
  λ { {A} {∋-here} → refl
    ; {A} {∋-there x} → cong suc eq
    }

from-to-raw : ∀ {V} {Γ : Context V} {A} {x} →
  from-raw {Γ = Γ} {A = A} (proj₂ (to-raw x)) ≡ x
from-to-raw {x = ∋-here} = refl
from-to-raw {x = ∋-there x} rewrite from-to-raw {x = x} = refl

to-from-raw : ∀ {V} {Γ : Context V} {A} {x} p →
  proj₁ (to-raw {Γ = Γ} {A = A} (from-raw {x = x} p)) ≡ x
to-from-raw ∋′-here = refl
to-from-raw (∋′-there p) rewrite to-from-raw p = refl

suc-Is-Renaming : ∀ {V} {Γ : Context V} {A} →
  Is-Renaming Γ (Γ ,, A) suc
suc-Is-Renaming =
  ∋′-there , cong suc (cong Context→ℕ (sym from-to-raw))

rename-preserves-type : ∀ {V} {Γ Δ : Context V} →
  (ρ : ℕ → ℕ) →
  Is-Renaming Γ Δ ρ →
  ∀ {B} {t} →
  Γ ⊢ t ⦂ B →
  Δ ⊢ rename ρ t ⦂ B
rename-preserves-type ρ ρ-renaming T-unit = T-unit
rename-preserves-type ρ ρ-renaming (T-var prf refl) =
  T-var
    (from-raw (proj₁ ρ-renaming (proj₂ (to-raw prf))))
    (sym (proj₂ ρ-renaming))
rename-preserves-type ρ ρ-renaming (T-ƛ x₁) =
  T-ƛ (rename-preserves-type (ext ρ) (ext-Is-Renaming ρ-renaming) x₁)
rename-preserves-type ρ ρ-renaming (T-∙ x₁ x₂) = T-∙ (rename-preserves-type ρ ρ-renaming x₁)
                                                          (rename-preserves-type ρ ρ-renaming x₂)
rename-preserves-type ρ ρ-renaming (T-Λ x) = T-Λ (λ v → rename-preserves-type ρ ρ-renaming (x v))
rename-preserves-type ρ ρ-renaming (T-＠ x₂) = T-＠ (rename-preserves-type  ρ ρ-renaming x₂)
rename-preserves-type ρ ρ-renaming (T-pair x₁ x₂) = T-pair  (rename-preserves-type  ρ ρ-renaming x₁)
                                                             (rename-preserves-type  ρ ρ-renaming x₂)
rename-preserves-type ρ ρ-renaming (T-fst x₁) = T-fst  (rename-preserves-type  ρ ρ-renaming x₁)
rename-preserves-type ρ ρ-renaming (T-snd x₁) = T-snd  (rename-preserves-type  ρ ρ-renaming x₁)
rename-preserves-type ρ ρ-renaming (T-inl x₁) = T-inl  (rename-preserves-type  ρ ρ-renaming x₁)
rename-preserves-type ρ ρ-renaming (T-inr x₁) = T-inr  (rename-preserves-type  ρ ρ-renaming x₁)
rename-preserves-type ρ ρ-renaming (T-match x₁ x₂ x₃) =
  T-match
    (rename-preserves-type  ρ ρ-renaming x₁)
    (rename-preserves-type  (ext ρ) (ext-Is-Renaming ρ-renaming) x₂)
    (rename-preserves-type  (ext ρ) (ext-Is-Renaming ρ-renaming) x₃)

exts-preserves-type : ∀ {V} {Γ Δ : Context V} {A B} {σ x} →
  Is-Subst Γ Δ σ →
  (Γ ,, B) ∋′ x ⦂ A →
  (Δ ,, B) ⊢ exts σ x ⦂ A
exts-preserves-type σ-subst ∋′-here = T-var ∋-here refl
exts-preserves-type σ-subst (∋′-there p) = rename-preserves-type suc suc-Is-Renaming (σ-subst p)

subst-preserves-type : ∀ {V} {Γ Δ : Context V} {A} {σ} {t} →
  Is-Subst Γ Δ σ →
  Γ ⊢ t ⦂ A →
  Δ ⊢ subst σ t ⦂ A
subst-preserves-type σ-subst T-unit = T-unit
subst-preserves-type σ-subst (T-var prf refl) rewrite to-raw-id {x = prf} = σ-subst (proj₂ (to-raw prf))
subst-preserves-type σ-subst (T-∙ t-typed t-typed₁) = T-∙ (subst-preserves-type σ-subst t-typed)
                                                               (subst-preserves-type σ-subst t-typed₁)
subst-preserves-type σ-subst (T-ƛ t-typed) =
  T-ƛ
    (subst-preserves-type (exts-preserves-type σ-subst) t-typed)
-- subst-preserves-type Δ-ctx σ-subst (T-Λ x t-typed) = T-Λ Δ-ctx (subst-preserves-type Δ-ctx σ-subst t-typed)
subst-preserves-type σ-subst (T-Λ t-typed) = T-Λ (λ v → subst-preserves-type σ-subst (t-typed v))
subst-preserves-type σ-subst (T-＠ t-typed) = T-＠ (subst-preserves-type σ-subst t-typed)
subst-preserves-type σ-subst (T-pair t-typed t-typed₁) = T-pair (subst-preserves-type σ-subst t-typed)
                                                                  (subst-preserves-type σ-subst t-typed₁)
subst-preserves-type σ-subst (T-fst t-typed) = T-fst (subst-preserves-type σ-subst t-typed)
subst-preserves-type σ-subst (T-snd t-typed) = T-snd (subst-preserves-type σ-subst t-typed)
subst-preserves-type σ-subst (T-inl t-typed) = T-inl (subst-preserves-type σ-subst t-typed)
subst-preserves-type σ-subst (T-inr t-typed) = T-inr (subst-preserves-type σ-subst t-typed)
subst-preserves-type σ-subst (T-match t-typed t-typed₁ t-typed₂) =
  T-match
    (subst-preserves-type σ-subst t-typed)
    (subst-preserves-type (exts-preserves-type σ-subst) t-typed₁)
    (subst-preserves-type (exts-preserves-type σ-subst) t-typed₂)

subst1-σ-Is-Subst : ∀ {V} {Γ : Context V} {A} {t} →
  Γ ⊢ t ⦂ A →
  Is-Subst (Γ ,, A) Γ (subst1-σ t)
subst1-σ-Is-Subst t-typed ∋′-here = t-typed
subst1-σ-Is-Subst t-typed (∋′-there p) =
  T-var (from-raw p) (trans to-raw-id (to-from-raw p))

subst1-preserves-type : ∀ {V} {Γ : Context V} {A B t u} →
  (Γ ,, B) ⊢ t ⦂ A →
  Γ ⊢ u ⦂ B →
  Γ ⊢ (t [ u ]) ⦂ A
subst1-preserves-type t-typed u-typed =
  subst-preserves-type (subst1-σ-Is-Subst u-typed) t-typed

data Value {ℓ} {V : Set ℓ} : Term V → Set ℓ where
  Val-unit : Value unit
  Val-ƛ : ∀ {t} → Value (ƛ t)
  Val-pair : ∀ {t u} →
    Value t →
    Value u →
    Value (pair t u)
  Val-inl : ∀ {t} →
    Value (inl t)
  Val-inr : ∀ {t} →
    Value (inr t)

infix 2 _⟶_
data _⟶_ {V} : Term V → Term V → Set where
  ξ-∙₁ : ∀ {t t′ u} →
    t ⟶ t′ →
    t ∙ u ⟶ t′ ∙ u

  ξ-∙₂ : ∀ {t u u′} →
    u ⟶ u′ →
    t ∙ u ⟶ t ∙ u′

  ξ-pair₁ : ∀ {t t′ u} →
    t ⟶ t′ →
    pair t u ⟶ pair t′ u

  ξ-pair₂ : ∀ {t u u′} →
    u ⟶ u′ →
    pair t u ⟶ pair t u′

  ξ-fst : ∀ {t t′} →
    t ⟶ t′ →
    fst t ⟶ fst t′

  ξ-snd : ∀ {t t′} →
    t ⟶ t′ →
    snd t ⟶ snd t′

  ξ-inl : ∀ {t t′} →
    t ⟶ t′ →
    inl t ⟶ inl t′

  ξ-inr : ∀ {t t′} →
    t ⟶ t′ →
    inr t ⟶ inr t′

  match-ξ : ∀ {t t′ u v} →
    t ⟶ t′ →
    match t u v ⟶ match t′ u v

  β-ƛ : ∀ {t u} →
    (ƛ t) ∙ u ⟶ t [ u ]

  β-pair₁ : ∀ {t u} →
    fst (pair t u) ⟶ t

  β-pair₂ : ∀ {t u} →
    snd (pair t u) ⟶ u

  β-inl : ∀ {t u v} →
    match (inl t) u v ⟶ u [ t ]

  β-inr : ∀ {t u v} →
    match (inr t) u v ⟶ v [ t ]

data _⟶*_ {V} : Term V → Term V → Set where
  _∎ : ∀ {t} → t ⟶* t
  _⟶⟨_⟩_ : (t : Term V) → ∀ {t′ t′′} →
    t ⟶ t′ →
    t′ ⟶* t′′ →
    t ⟶* t′′

infix 2 _⇓_
infix 2 _⇓

_⇓_ : ∀ {V} → Term V → Term V → Set
_⇓_ t u = Value u × (t ⟶* u)

_⇓ : ∀ {V} → Term V → Set
_⇓ t = ∃[ u ] (t ⇓ u)

⟶-typed : ∀ {V Γ A} {t u : Term V} →
  Γ ⊢ t ⦂ A →
  t ⟶ u →
  Γ ⊢ u ⦂ A
⟶-typed (T-∙ t-typed t-typed₁) (ξ-∙₁ t⟶u) = T-∙ (⟶-typed t-typed t⟶u) t-typed₁
⟶-typed (T-∙ t-typed t-typed₁) (ξ-∙₂ t⟶u) = T-∙ t-typed (⟶-typed t-typed₁ t⟶u)
⟶-typed (T-pair t-typed t-typed₁) (ξ-pair₁ t⟶u) = T-pair (⟶-typed t-typed t⟶u) t-typed₁
⟶-typed (T-pair t-typed t-typed₁) (ξ-pair₂ t⟶u) = T-pair t-typed (⟶-typed t-typed₁ t⟶u)
⟶-typed (T-fst t-typed) (ξ-fst t⟶u) = T-fst (⟶-typed t-typed t⟶u)
⟶-typed (T-snd t-typed) (ξ-snd t⟶u) = T-snd (⟶-typed t-typed t⟶u)
⟶-typed (T-inl t-typed) (ξ-inl t⟶u) = T-inl (⟶-typed t-typed t⟶u)
⟶-typed (T-inr t-typed) (ξ-inr t⟶u) = T-inr (⟶-typed t-typed t⟶u)
⟶-typed (T-match t-typed t-typed₁ t-typed₂) (match-ξ t⟶u) = T-match (⟶-typed t-typed t⟶u) t-typed₁ t-typed₂
⟶-typed (T-∙ (T-ƛ t-typed) t-typed₁) β-ƛ = subst1-preserves-type t-typed t-typed₁
⟶-typed (T-fst (T-pair t-typed t-typed₁)) β-pair₁ = t-typed
⟶-typed (T-snd (T-pair t-typed t-typed₁)) β-pair₂ = t-typed₁
⟶-typed (T-match (T-inl t-typed) t-typed₁ t-typed₂) β-inl = subst1-preserves-type t-typed₁ t-typed
⟶-typed (T-match (T-inr t-typed) t-typed₁ t-typed₂) β-inr = subst1-preserves-type t-typed₂ t-typed

⟶*-typed : ∀ {V Γ A} {t u : Term V} →
  Γ ⊢ t ⦂ A →
  t ⟶* u →
  Γ ⊢ u ⦂ A
⟶*-typed t-typed _∎ = t-typed
⟶*-typed t-typed (_ ⟶⟨ p ⟩ t⟶*u) =
  ⟶*-typed (⟶-typed t-typed p) t⟶*u

⇓-typed : ∀ {V Γ A} {t u : Term V} →
  Γ ⊢ t ⦂ A →
  t ⇓ u →
  Γ ⊢ u ⦂ A
⇓-typed t-typed (_ , t⟶*u) = ⟶*-typed t-typed t⟶*u

Simulation : ∀ {ℓ m n} {A B : Set} →
  (A → B → Set ℓ) →
  (A → A → Set m) →
  (B → B → Set n) →
  Set (ℓ Level.⊔ m Level.⊔ n)
Simulation _~_ _⊚_ _⊚′_ =
  ∀ {M M† N} →
  M ~ M† →
  M ⊚ N →
  ∃[ N† ]
  ((M† ⊚′ N†)
    ×
   (N ~ N†))

Bisimulation : ∀ {A B : Set} →
  (A → B → Set) →
  (A → A → Set) →
  (B → B → Set) →
  Set
Bisimulation _~_ _⊚_ _⊚′_ =
  Simulation _~_ _⊚_ _⊚′_
    ×
  Simulation (λ x y → y ~ x) _⊚′_ _⊚_

-- _<->_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set (lsuc ℓ)
-- _<->_ {ℓ} A B = A → B → Set ℓ

Type-join : ∀ {ℓ} {V : Set ℓ} → Type (Type V) → Type V
Type-join (Ty-Var A) = A
Type-join Unit = Unit
Type-join (Pair A B) = Pair (Type-join A) (Type-join B)
Type-join (Sum A B) = Sum (Type-join A) (Type-join B)
Type-join (A ⇒ B) = Type-join A ⇒ Type-join B
Type-join (Forall F) =
  Forall λ x →
    Type-join (F (Ty-Var x))


Rel-On : ∀ {ℓ} (V : Set ℓ) → Type V → Type V → Set (lsuc ℓ)
Rel-On V A B =
  ∀ {Γ} {x x′ : Term V} →
  Value x →
  Value x′ →
  Γ ⊢ x ⦂ A →
  Γ ⊢ x′ ⦂ B →
  Set

record Rel {ℓ} (V : Set ℓ) : Set (lsuc ℓ) where
  constructor mk-Rel
  field
    unpack : ∃[ A ] ∃[ B ] Rel-On V A B

open import Data.Sum

Agda-type : Type Set → Set₁
Agda-type Unit = Lift (lsuc lzero) ⊤
Agda-type (Pair A B) = Agda-type A × Agda-type B
Agda-type (Sum A B) = Agda-type A ⊎ Agda-type B
Agda-type (A ⇒ B) = Agda-type A → Agda-type B
Agda-type (Forall F) = ∀ (S : Set) → Agda-type (F S)
Agda-type (Ty-Var S) = Lift (lsuc lzero) S

data Env : Context Set → Set₁ where
  ∅ : Env ∅
  _,,_ : ∀ {Γ A} →
    Env Γ →
    Agda-type A →
    Env (Γ ,, A)

env-lookup : ∀ {Γ} {A} →
  Γ ∋ A →
  Env Γ →
  Agda-type A
env-lookup ∋-here (γ ,, x) = x
env-lookup (∋-there x) (γ ,, x₁) = env-lookup x γ

⟦_⟧ : ∀ {Γ} {t} {A} →
  Γ ⊢ t ⦂ A →
  Env Γ →
  Agda-type A
⟦ T-unit ⟧ γ = lift tt
⟦ T-var x refl ⟧ γ = env-lookup x γ
⟦ T-ƛ t-typed ⟧ γ = λ x → ⟦ t-typed ⟧ (γ ,, x)
⟦ T-∙ t-typed t-typed₁ ⟧ γ = ⟦ t-typed ⟧ γ (⟦ t-typed₁ ⟧ γ)
⟦ T-Λ x ⟧ γ = λ S → ⟦ x S ⟧ γ
⟦ T-＠ {A = A} t-typed ⟧ γ = ⟦ t-typed ⟧ γ A
⟦ T-pair t-typed t-typed₁ ⟧ γ = ⟦ t-typed ⟧ γ , ⟦ t-typed₁ ⟧ γ
⟦ T-fst t-typed ⟧ γ = proj₁ (⟦ t-typed ⟧ γ)
⟦ T-snd t-typed ⟧ γ = proj₂ (⟦ t-typed ⟧ γ)
⟦ T-inl t-typed ⟧ γ = inj₁ (⟦ t-typed ⟧ γ)
⟦ T-inr t-typed ⟧ γ = inj₂ (⟦ t-typed ⟧ γ)
⟦ T-match t-typed t-typed₁ t-typed₂ ⟧ γ with ⟦ t-typed ⟧ γ
... | inj₁ a = ⟦ t-typed₁ ⟧ (γ ,, a)
... | inj₂ b = ⟦ t-typed₂ ⟧ (γ ,, b)

-- Agda-type : ∀ {ℓ} → Type′ {{!!}} → Set {!!}
-- Agda-type {ℓ} T with T {∀ {V : Set {!!}} → Type {{!!}} V}
-- ... | Ty-Var A = let x = Agda-type {ℓ} (λ {V : Set {!!}} → A {V}) in x
-- ... | Unit = {!!}
-- ... | Pair A A₁ = {!!}
-- ... | Sum A A₁ = {!!}
-- ... | A ⇒ A₁ = {!!}
-- ... | Forall x = {!!}

-- typing-simulation : ∀ {V} →
--   Simulation
--     {A = Term V} {B = Term V}
--     _≡_
--     (_⟶_ {V = V})
--     (λ t u → ∃[ Γ ] ∃[ A ] (Γ ⊢ t ⦂ A → Γ ⊢ u ⦂ A))
-- typing-simulation {M = M} {N = N} refl x₁ =
--   N , {!!}

-- typing-unique : ∀ {V} {Γ : Context V} {A t} →
--   (p q : Γ ⊢ t ⦂ A) →
--   p ≡ q
-- typing-unique {Γ = Γ} T-unit T-unit = refl
-- typing-unique {Γ = Γ} (T-var prf refl) (T-var prf₁ x₁) = {!!}
-- typing-unique {Γ = Γ} (T-ƛ p) q = {!!}
-- typing-unique {Γ = Γ} (T-∙ p p₁) q = {!!}
-- typing-unique {Γ = Γ} (T-Λ x) q = {!!}
-- typing-unique {Γ = Γ} (T-＠ p) q = {!!}
-- typing-unique {Γ = Γ} (T-pair p p₁) q = {!!}
-- typing-unique {Γ = Γ} (T-fst p) q = {!!}
-- typing-unique {Γ = Γ} (T-snd p) q = {!!}
-- typing-unique {Γ = Γ} (T-inl p) q = {!!}
-- typing-unique {Γ = Γ} (T-inr p) q = {!!}
-- typing-unique {Γ = Γ} (T-match p p₁ p₂) q = {!!}

-- pair-lemma : ∀ {V} {Γ : Context V} {A B t u v} →
--   (t-typed : Γ ⊢ t ⦂ Pair A B) →
--   fst t ⇓ u →
--   snd t ⇓ v →
--   (u-typed : Γ ⊢ u ⦂ A) →
--   (v-typed : Γ ⊢ v ⦂ B) →
--   t-typed ≡ T-pair u-typed v-typed
-- pair-lemma = ?

-- TODO:
--  - Head expansion (?)
--  - Progress
--  - Confluence
--  - Canonical forms lemma
--  - Weak normalization



-- -- NbE
-- mutual
--   Env : ∀ {V} → Context V → Set₁
--   Env {V} Γ = ∀ {A} → Γ ∋ A → ∃[ t ] Value {V} t
--   -- ClosureEnv {V} Γ = V → ∃[ t ] Closure {V} t
--   -- ClosureEnv {V} Γ = V → ∃[ t ] Closure {V} t

--   data Closure {V : Set} (t : Term V) : Set₁ where
--     closure : ∀ {Γ : Context V} {A B} →
--       (Γ ,, A) ⊢ t ⦂ B →
--       Env Γ →
--       Closure t

--   data Value {V} : Term V → Set₁ where
--     Val-Ne : ∀ {t} → Neutral t → Value t
--     Val-unit : Value unit
--     Val-ƛ : ∀ {t} →
--       Closure t →
--       Value (ƛ t)
--     Val-pair : ∀ {t u} →
--       Value t →
--       Value u →
--       Value (pair t u)
--     Val-inl : ∀ {t} →
--       Value (inl t)
--     Val-inr : ∀ {t} →
--       Value (inr t)

--   data Neutral {V} : Term V → Set₁ where
--     Ne-var : ∀ {n} → Neutral (var n)
--     Ne-app : ∀ {t u} →
--       Neutral t →
--       Value u →
--       Neutral (t ∙ u)
--     Ne-fst : ∀ {t} →
--       Neutral t →
--       Neutral (fst t)
--     Ne-snd : ∀ {t} →
--       Neutral t →
--       Neutral (snd t)
--     Ne-match : ∀ {t u v} →
--       Neutral t →
--       Value u →
--       Value v →
--       Neutral (match t u v)
--     Ne-＠ : ∀ {t A} →
--       Neutral t →
--       Neutral (t ＠ A)

-- extend-Env : ∀ {V} {Γ : Context V} → Env Γ → ∀ {t A} →
--   Γ ⊢ t ⦂ A →
--   Value t →
--   Env (Γ ,, A)
-- extend-Env env {t} t-typed t-value ∋-here = t , t-value
-- extend-Env env t-typed t-value (∋-there x) = env x

-- eval-var : ∀ {V} {Γ : Context V} {A} → Env Γ → Γ ∋ A → ∃[ t ] Value {V} t
-- eval-var = {!!}

-- do-apply : ∀ {V} {Γ : Context V} {A B} {t u} →
--   (Γ ,, A) ⊢ t ⦂ B →
--   Γ ⊢ u ⦂ A →
--   Value t →
--   Value u →
--   ∃[ v ] Value {V = V} v
-- do-apply = {!!}

-- eval : ∀ {V} {Γ : Context V} {A} → Env Γ → {t : Term V} → Γ ⊢ t ⦂ A → ∃[ t′ ] Value {V = V} t′
-- eval env T-unit = unit , Val-unit
-- eval env (T-var prf x) = eval-var env prf
-- eval env {t = t} (T-ƛ t-typed) =
--   let
--     -- u , u-val = eval env t-typed
--     cl = closure t-typed env
--   in
--   t
--   ,
--   Val-ƛ cl
-- eval env (T-∙ t-typed t-typed₁) = {!!} --do-apply t-typed t-typed₁
-- eval env (T-Λ x) = {!!}
-- eval env (T-＠ t-typed) = {!!}
-- eval env (T-pair t-typed t-typed₁) = {!!}
-- eval env (T-fst t-typed) = {!!}
-- eval env (T-snd t-typed) = {!!}
-- eval env (T-inl t-typed) = {!!}
-- eval env (T-inr t-typed) = {!!}
-- eval env (T-match t-typed t-typed₁ t-typed₂) = {!!}
