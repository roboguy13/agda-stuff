open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to Eq-subst)
open import Data.Product
open import Data.Unit

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

data Type (V : Set) : Set where
  Ty-Var : V → Type V
  Unit : Type V
  Pair : Type V → Type V → Type V
  Sum : Type V → Type V → Type V
  _⇒_ : Type V → Type V → Type V
  Forall : (V → Type V) → Type V

Type′ : Set₁
Type′ = ∀ {V} → Type V

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

data Context (V : Set) : Set where
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

data _∋_ {V : Set} : Context V → Type V → Set where
  ∋-here : ∀ {Γ A} → (Γ ,, A) ∋ A
  ∋-there : ∀ {Γ A B} →
    Γ ∋ A →
    (Γ ,, B) ∋ A

_∋′_ : Context′ → Type′ → Set
_∋′_ Γ A = _∋_ {V = ⊤} Γ A

_,,′_ : Context′ → Type′ → Context′
_,,′_ Γ A = _,,_ Γ A

data Term (V : Set) : Set where
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

Context→ℕ : ∀ {V} {Γ : Context V} →
  ∀ {A} → Γ ∋ A →
  ℕ
Context→ℕ ∋-here = zero
Context→ℕ (∋-there x) = suc (Context→ℕ x)


-- infix 3 [_]_⊢_⦂_
infix 3 _⊢_⦂_
data _⊢_⦂_ {V} : Context V → Term V → Type V → Set₁ where
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

rename : ∀ {V} →
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

exts : ∀ {V} →
  (ℕ → Term V) →
  (ℕ → Term V)
exts σ zero = var zero
exts σ (suc x) = rename suc (σ x)

subst : ∀ {V} →
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

subst1-σ : ∀ {V} → Term V → ℕ → Term V
subst1-σ t zero = t
subst1-σ t (suc x) = var x

_[_] : ∀ {V} →
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
