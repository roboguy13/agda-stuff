open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to Eq-subst)
open import Data.Product

module Syntax
  where

infixr 4 _⇒_

data Kind : Set where
  ⋆ : Kind

data Ty-Context : Set where
  ∅ : Ty-Context
  _,,_ : Ty-Context → Kind → Ty-Context

data _T∋_ : Ty-Context → Kind → Set where
  T-Here : ∀ {Δ k} → (Δ ,, k) T∋ k
  T-There : ∀ {Δ k k′} →
    Δ T∋ k →
    (Δ ,, k′) T∋ k

data Type : Set where
  Ty-V : ℕ → Type
  Unit : Type
  Pair : Type → Type → Type
  Sum : Type → Type → Type
  _⇒_ : Type → Type → Type
  Forall : Type → Type

Ty-Context→ℕ : ∀ {Δ} →
  ∀ {k} → Δ T∋ k →
  ℕ
Ty-Context→ℕ T-Here = zero
Ty-Context→ℕ (T-There x) = suc (Ty-Context→ℕ x)

data _⊢_type : Ty-Context → Type → Set where
  Ty-V-type : ∀ {∁} {k i} →
    (prf : ∁ T∋ k) →
    Ty-Context→ℕ prf ≡ i →
    ∁ ⊢ Ty-V i type
  Unit-type : ∀ {∁} → ∁ ⊢ Unit type
  Pair-type : ∀ {∁ A B} →
    ∁ ⊢ A type →
    ∁ ⊢ B type →
    ∁ ⊢ Pair A B type
  Sum-type : ∀ {∁ A B} →
    ∁ ⊢ A type →
    ∁ ⊢ B type →
    ∁ ⊢ Sum A B type
  ⇒-type : ∀ {∁ A B} →
    ∁ ⊢ A type →
    ∁ ⊢ B type →
    ∁ ⊢ A ⇒ B type
  Forall-type : ∀ {∁ k A} →
    (∁ ,, k) ⊢ A type →
    ∁ ⊢ Forall A type

-- data Type : Ty-Context → Set where
--   Ty-V : ∀ {Δ k} → Δ T∋ k → Type Δ
--   Unit : ∀ {Δ} → Type Δ
--   Pair : ∀ {Δ} → Type Δ → Type Δ → Type Δ
--   Sum : ∀ {Δ} → Type Δ → Type Δ → Type Δ
--   _⇒_ : ∀ {Δ} → Type Δ → Type Δ → Type Δ
--   Forall : ∀ {Δ k} → Type (Δ ,, k) → Type Δ

-- data Context (Δ : Ty-Context) : Set where
--   ∅ : Context Δ
--   _,,_ : Context Δ → Type Δ → Context Δ

-- data _∋_ {Δ : Ty-Context} : Context Δ → Type Δ → Set where
--   ∋-here : ∀ {Γ A} → (Γ ,, A) ∋ A
--   ∋-there : ∀ {Γ A B} →
--     Γ ∋ A →
--     (Γ ,, B) ∋ A

-- data Term : Set where
--   unit : Term
--   V : ℕ → Term
--   -- Ty-V : ℕ → Term
--   ƛ : Term → Term
--   _∙_ : Term → Term → Term
--   Λ : Term → Term -- Type abstraction
--   _＠_ : Term → ℕ → Term -- Type application
--   pair : Term → Term → Term
--   fst : Term → Term
--   snd : Term → Term
--   inl : Term → Term
--   inr : Term → Term
--   match : Term → Term → Term → Term

-- Context→ℕ : ∀ {Δ} {Γ : Context Δ} →
--   ∀ {A} → Γ ∋ A →
--   ℕ
-- Context→ℕ ∋-here = zero
-- Context→ℕ (∋-there x) = suc (Context→ℕ x)


-- infix 3 [_]_⊢_⦂_
-- infix 3 _⊢_⦂_
-- data [_]_⊢_⦂_ : ∀ Δ {Δ′} → Context Δ′ → Term → Type Δ → Set where
--   T-unit : ∀ {Δ} {Γ : Context Δ} → [ Δ ] Γ ⊢ unit ⦂ Unit

--   T-V : ∀ {Δ Γ A i} →
--     (prf : Γ ∋ A) →
--     Context→ℕ prf ≡ i →
--     [ Δ ] Γ ⊢ V i ⦂ A

--   T-ƛ : ∀ {Δ Γ A B t} →
--     [ Δ ] (Γ ,, A) ⊢ t ⦂ B →
--     [ Δ ] Γ ⊢ ƛ t ⦂ A ⇒ B

--   T-∙ : ∀ {Δ} {Γ : Context Δ} {A B s t} →
--     [ Δ ] Γ ⊢ s ⦂ A ⇒ B →
--     [ Δ ] Γ ⊢ t ⦂ A →
--     [ Δ ] Γ ⊢ s ∙ t ⦂ B

--   T-Λ : ∀ {Δ k} {Γ : Context Δ} {A t} →
--     [ Δ ,, k ] Γ ⊢ t ⦂ A →
--     [ Δ ] Γ ⊢ Λ t ⦂ Forall A

--   T-＠ : ∀ {Δ k} {Γ : Context Δ} {A i t} {prf : Δ T∋ k} →
--     Ty-Context→ℕ prf ≡ i →
--     [ Δ ] Γ ⊢ t ⦂ Forall A →
--     [ Δ ,, k ] Γ ⊢ t ＠ i ⦂ A -- TODO: Does this make sense?

--   T-pair : ∀ {Δ} {Γ : Context Δ} {A B s t} →
--     [ Δ ] Γ ⊢ s ⦂ A →
--     [ Δ ] Γ ⊢ t ⦂ B →
--     [ Δ ] Γ ⊢ pair s t ⦂ Pair A B

--   T-fst : ∀ {Δ} {Γ : Context Δ} {A B t} →
--     [ Δ ] Γ ⊢ t ⦂ Pair A B →
--     [ Δ ] Γ ⊢ fst t ⦂ A

--   T-snd : ∀ {Δ} {Γ : Context Δ} {A B t} →
--     [ Δ ] Γ ⊢ t ⦂ Pair A B →
--     [ Δ ] Γ ⊢ snd t ⦂ B

--   T-inl : ∀ {Δ} {Γ : Context Δ} {A B t} →
--     [ Δ ] Γ ⊢ t ⦂ A →
--     [ Δ ] Γ ⊢ inl t ⦂ Sum A B

--   T-inr : ∀ {Δ} {Γ : Context Δ} {A B t} →
--     [ Δ ] Γ ⊢ t ⦂ B →
--     [ Δ ] Γ ⊢ inr t ⦂ Sum A B

--   T-match : ∀ {Δ} {Γ : Context Δ} {A B C s t₁ t₂} →
--     [ Δ ] Γ ⊢ s ⦂ Sum A B →
--     [ Δ ] (Γ ,, A) ⊢ t₁ ⦂ C →
--     [ Δ ] (Γ ,, B) ⊢ t₂ ⦂ C →
--     [ Δ ] Γ ⊢ match s t₁ t₂ ⦂ C

-- _⊢_⦂_ : ∀ {Δ} → Context Δ → Term → Type Δ → Set
-- _⊢_⦂_ {Δ} Γ M A = [ Δ ] Γ ⊢ M ⦂ A

-- ext : (ℕ → ℕ) → (ℕ → ℕ)
-- ext ρ zero = zero
-- ext ρ (suc x) = suc (ρ x)

-- rename :
--   (ℕ → ℕ) →
--   Term →
--   Term
-- rename ρ unit = unit
-- rename ρ (V x) = V (ρ x)
-- rename ρ (ƛ t) = ƛ (rename (ext ρ) t)
-- rename ρ (t₁ ∙ t₂) = rename ρ t₁ ∙ rename ρ t₂
-- rename ρ (Λ t) = Λ (rename ρ t)
-- rename ρ (t ＠ i) = rename ρ t ＠ i
-- rename ρ (pair t₁ t₂) = pair (rename ρ t₁) (rename ρ t₂)
-- rename ρ (fst t) = fst (rename ρ t)
-- rename ρ (snd t) = snd (rename ρ t)
-- rename ρ (inl t) = inl (rename ρ t)
-- rename ρ (inr t) = inr (rename ρ t)
-- rename ρ (match s t₁ t₂) =
--   match (rename ρ s) (rename (ext ρ) t₁) (rename (ext ρ) t₂)

-- exts :
--   (ℕ → Term) →
--   (ℕ → Term)
-- exts σ zero = V zero
-- exts σ (suc x) = rename suc (σ x)

-- subst :
--   (ℕ → Term) →
--   Term →
--   Term
-- subst σ unit = unit
-- subst σ (V x) = σ x
-- subst σ (ƛ t) = ƛ (subst (exts σ) t)
-- subst σ (t₁ ∙ t₂) = subst σ t₁ ∙ subst σ t₂
-- subst σ (Λ t) = Λ (subst σ t)
-- subst σ (t ＠ x) = subst σ t ＠ x
-- subst σ (pair t₁ t₂) = pair (subst σ t₁) (subst σ t₂)
-- subst σ (fst t) = fst (subst σ t)
-- subst σ (snd t) = snd (subst σ t)
-- subst σ (inl t) = inl (subst σ t)
-- subst σ (inr t) = inr (subst σ t)
-- subst σ (match s t₁ t₂) =
--   match (subst σ s) (subst σ t₁) (subst σ t₂)

-- subst1-σ : Term → ℕ → Term
-- subst1-σ t zero = t
-- subst1-σ t (suc x) = V x

-- _[_] :
--   Term →
--   Term →
--   Term
-- _[_] s t = subst (subst1-σ t) s

-- data _∋′_⦂_ : ∀ {Δ} → Context Δ → ℕ → Type Δ → Set where
--   ∋′-here : ∀ {Δ} {Γ : Context Δ} {A} →
--     (Γ ,, A) ∋′ 0 ⦂ A

--   ∋′-there : ∀ {Δ} {Γ : Context Δ} {A B} {x} →
--     Γ ∋′ x ⦂ A →
--     (Γ ,, B) ∋′ suc x ⦂ A

-- from-raw : ∀ {Δ} {Γ : Context Δ} {A x} →
--   Γ ∋′ x ⦂ A →
--   Γ ∋ A
-- from-raw ∋′-here = ∋-here
-- from-raw (∋′-there p) = ∋-there (from-raw p)

-- to-raw : ∀ {Δ} {Γ : Context Δ} {A} →
--   Γ ∋ A →
--   ∃[ x ] Γ ∋′ x ⦂ A
-- to-raw ∋-here = zero , ∋′-here
-- to-raw (∋-there p) =
--   let x , q = to-raw p
--   in
--   suc x , ∋′-there q

-- Is-Renaming : ∀ {Δ} → Context Δ → Context Δ → (ℕ → ℕ) → Set
-- Is-Renaming Γ Γ′ ρ =
--   Σ (∀ {A} {x} →
--       Γ ∋′ x ⦂ A →
--       Γ′ ∋′ ρ x ⦂ A)
--   λ ρ-renaming →
--   ∀ {A} {z : Γ ∋ A} →
--   ρ (Context→ℕ z) ≡ Context→ℕ (from-raw (ρ-renaming (proj₂ (to-raw z))))

-- -- TODO: Raw contexts?
-- -- generalize-Is-Renaming : ∀ {Δ Δ′} 

-- Is-Subst : ∀ {Δ} → Context Δ → Context Δ → (ℕ → Term) → Set
-- Is-Subst Γ Γ′ σ =
--   ∀ {A} {x} →
--     Γ ∋′ x ⦂ A →
--     Γ′ ⊢ σ x ⦂ A

-- ext-Is-Renaming : ∀ {Δ} {Γ Γ′ : Context Δ} {A} {ρ} →
--   Is-Renaming Γ Γ′ ρ →
--   Is-Renaming (Γ ,, A) (Γ′ ,, A) (ext ρ)
-- ext-Is-Renaming {_} {Γ} {Γ′} {ρ = ρ} (renames , eq) =
--   (λ { {x = zero} ∋′-here → ∋′-here
--      ; {x = suc x} (∋′-there z) → ∋′-there (renames z) })
--   ,
--   λ { {A} {∋-here} → refl
--     ; {A} {∋-there x} → cong suc eq
--     }

-- from-to-raw : ∀ {Δ} {Γ : Context Δ} {A} {x} →
--   from-raw {Γ = Γ} {A = A} (proj₂ (to-raw x)) ≡ x
-- from-to-raw {x = ∋-here} = refl
-- from-to-raw {x = ∋-there x} rewrite from-to-raw {x = x} = refl

-- suc-Is-Renaming : ∀ {Δ} {Γ : Context Δ} {A} →
--   Is-Renaming Γ (Γ ,, A) suc
-- suc-Is-Renaming = ∋′-there , cong suc (cong Context→ℕ (sym from-to-raw))

-- rename-preserves-type : ∀ {Δ} {Γ Γ′ : Context Δ} →
--   (ρ : ℕ → ℕ) →
--   Is-Renaming Γ Γ′ ρ →
--   ∀ {B} {t} →
--   [ Δ ] Γ ⊢ t ⦂ B →
--   [ Δ ] Γ′ ⊢ rename ρ t ⦂ B
-- rename-preserves-type ρ ρ-renaming T-unit = T-unit
-- rename-preserves-type ρ ρ-renaming (T-V x refl) = T-V (from-raw (proj₁ ρ-renaming (proj₂ (to-raw x)))) (sym (proj₂ ρ-renaming))
-- rename-preserves-type ρ ρ-renaming (T-ƛ x) =
--   T-ƛ (rename-preserves-type (ext ρ) (ext-Is-Renaming ρ-renaming) x)
-- rename-preserves-type ρ ρ-renaming (T-∙ x x₁) =
--   T-∙ (rename-preserves-type ρ ρ-renaming x)
--       (rename-preserves-type ρ ρ-renaming x₁)
-- rename-preserves-type ρ ρ-renaming (T-Λ x) =
--   -- let x′ = rename-preserves-type ρ ρ-renaming x
--   -- in
--   T-Λ {!!}
-- rename-preserves-type ρ ρ-renaming (T-pair x y) =
--   T-pair (rename-preserves-type ρ ρ-renaming x)
--          (rename-preserves-type ρ ρ-renaming y)
-- rename-preserves-type ρ ρ-renaming (T-fst x) = T-fst (rename-preserves-type ρ ρ-renaming x)
-- rename-preserves-type ρ ρ-renaming (T-snd x) = T-snd (rename-preserves-type ρ ρ-renaming x)
-- rename-preserves-type ρ ρ-renaming (T-inl x) = T-inl (rename-preserves-type ρ ρ-renaming x)
-- rename-preserves-type ρ ρ-renaming (T-inr x) = T-inr (rename-preserves-type ρ ρ-renaming x)
-- rename-preserves-type ρ ρ-renaming (T-match x y z) =
--   T-match (rename-preserves-type ρ ρ-renaming x)
--     (rename-preserves-type (ext ρ) (ext-Is-Renaming ρ-renaming) y)
--     (rename-preserves-type (ext ρ) (ext-Is-Renaming ρ-renaming) z)

-- -- data Expr : Context → Type → Set where
-- --   unit : ∀ {Γ} → Expr Γ Unit

-- --   V : ∀ {Γ A} → Γ ∋ A → Expr Γ A

-- --   _∙_ : ∀ {Γ A B} → Expr Γ (A ⇒ B) → Expr Γ A → Expr Γ B

-- --   ƛ : ∀ {Γ A B} →
-- --     Expr (Γ ,, A) B →
-- --     Expr Γ (A ⇒ B)

-- --   pair : ∀ {Γ A B} →
-- --     Expr Γ A →
-- --     Expr Γ B →
-- --     Expr Γ (Pair A B)

-- --   fst : ∀ {Γ A B} →
-- --     Expr Γ (Pair A B) →
-- --     Expr Γ A

-- --   snd : ∀ {Γ A B} →
-- --     Expr Γ (Pair A B) →
-- --     Expr Γ B

-- --   inl : ∀ {Γ A B} →
-- --     Expr Γ A →
-- --     Expr Γ (Sum A B)

-- --   inr : ∀ {Γ A B} →
-- --     Expr Γ B →
-- --     Expr Γ (Sum A B)

-- --   match : ∀ {Γ A B C} →
-- --     Expr Γ (Sum A B) →
-- --     Expr (Γ ,, A) C →
-- --     Expr (Γ ,, B) C →
-- --     Expr Γ C



