-- See https://well-typed.com/blog/2015/05/parametricity/

open import Syntax

open import Data.Unit
open import Data.Empty

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.Sum
open import Level renaming (zero to lzero; suc to lsuc)

module Parametricity {V : Set}
  (Var-rel : V → Rel V)
  -- (F : Type V → Type V)
  -- (𝓕 : ∀ {A A′} {F : Type V → Type V} →
  --   (∀ {t u : Term V} → ∅ ⊢ t ⦂ A → ∅ ⊢ u ⦂ A′ → Set) →
  --   (∀ {t u : Term V} → ∅ ⊢ t ⦂ F A → ∅ ⊢ u ⦂ F A′ → Set)
  --   )
  -- (Var-rel : V → (A B : Type V) → ∀ {Γ} {t u} →
  --   Γ ⊢ t ⦂ A →
  --   Γ ⊢ u ⦂ B →
  --   Set₁)
  where

data Is-Const-Type : Type V → Set where
  Unit-Const : Is-Const-Type Unit
  Pair-Const : ∀ {A B} →
    Is-Const-Type A →
    Is-Const-Type B →
    Is-Const-Type (Pair A B)
  Sum-Const : ∀ {A B} →
    Is-Const-Type A →
    Is-Const-Type B →
    Is-Const-Type (Sum A B)
  -- ⇒-Const : ∀ {A B} →
  --   Is-Const-Type A →
  --   Is-Const-Type B →
  --   Is-Const-Type (A ⇒ B)

data _≡₁_ {A : Set} : A → A → Set₁ where
  refl₁ : ∀ {x} → x ≡₁ x

-- Rel-left : ∀ {ℓ} {V : Set ℓ} → Rel V → Type {!!}
-- Rel-left (mk-Rel R) = {!!}

𝓡 : (T : Type Set) →
  Agda-type T → Agda-type T → Set₁
𝓡 (Ty-Var x) A B = Lift (lsuc lzero) x
𝓡 Unit A B = Lift (lsuc lzero) ⊤
𝓡 (Pair T T₁) (fst₁ , snd₁) (fst₂ , snd₂) =
  𝓡 T fst₁ fst₂
    ×
  𝓡 T₁ snd₁ snd₂
𝓡 (Sum T T₁) (inj₁ x) (inj₁ y) = 𝓡 T x y
𝓡 (Sum T T₁) (inj₁ x) (inj₂ y) = Lift (lsuc lzero) ⊥
𝓡 (Sum T T₁) (inj₂ y) (inj₁ x) = Lift (lsuc lzero) ⊥
𝓡 (Sum T T₁) (inj₂ x) (inj₂ y) = 𝓡 T₁ x y
𝓡 (T ⇒ T₁) f g =
  ∀ a b →
  𝓡 T a b →
  𝓡 T₁ (f a) (g b)
𝓡 (Forall x) f g =
  ∀ S →
  𝓡 (x S) (f S) (g S)

parametricity : ∀ {t A} →
  (t-typed : ∅ ⊢ t ⦂ A) →
  𝓡 A (⟦ t-typed ⟧ ∅) (⟦ t-typed ⟧ ∅)
parametricity T-unit = lift tt
parametricity (T-ƛ t-typed) = {!!}
parametricity (T-∙ t-typed t-typed₁) = {!!}
parametricity (T-Λ x) = {!!}
parametricity (T-＠ t-typed) = {!!}
parametricity (T-pair t-typed t-typed₁) = parametricity t-typed , parametricity t-typed₁
parametricity (T-fst t-typed) = {!!}
parametricity (T-snd t-typed) = {!!}
parametricity (T-inl t-typed) = parametricity t-typed
parametricity (T-inr t-typed) = parametricity t-typed
parametricity (T-match t-typed t-typed₁ t-typed₂) = {!!}

-- 𝓡 :
--   (T : Type (∀ A B → Rel V A B)) →
--   Rel ((x x₁ : Type V) {x = x₂ : Context V}
--         {x = x₃ : Term V} {x = x₄ : Term V} (x₅ : Value x₃) (x₆ : Value x₄)
--         (x₇ : x₂ ⊢ x₃ ⦂ x) (x₈ : x₂ ⊢ x₄ ⦂ x₁) →
--         Set) T T
-- 𝓡 (Ty-Var R) = λ x₁ x₂ x₃ x₄ → ∀ A B → R A B {!!} {!!} {!!} {!!}
-- 𝓡 Unit = {!!}
-- 𝓡 (Pair T T₁) = {!!}
-- 𝓡 (Sum T T₁) = {!!}
-- 𝓡 (T ⇒ T₁) = {!!}
-- 𝓡 (Forall x) = {!!}
-- -- 𝓡 (Ty-Var R) = R
-- -- 𝓡 Unit {x = x} {x′ = x′} x-value x′-value x-typed x′-typed = x ≡ x′
-- -- 𝓡 (Pair A B) {x = x} {x′ = x′} x-value x′-value x-typed x′-typed = {!!}
-- -- 𝓡 (Sum A B) = {!!}
-- -- 𝓡 (A ⇒ B) = {!!}
-- -- 𝓡 (Forall x) = {!!}

-- _𝓡[_]_ : ∀ {x x′ : Term (Type V)} {A B Γ} →
--   Γ ⊢ x ⦂ A →
--   -- Type V →
--   -- Type′ →
--   Type (Type V) →
--   Γ ⊢ x′ ⦂ B →
--   Set₁
-- -- _𝓡[_]_ {x = x} {x′ = x′} _ Unit _ = x ≡₁ x′
-- -- _𝓡[_]_ {x = f} {x′ = f′} {Γ = Γ} f-typed (A ⇒ B) f′-typed =
-- --   ∀ x x′ (x-typed : Γ ⊢ x ⦂ A) (x′-typed : Γ ⊢ x′ ⦂ A) fx fx′ (fx-typed : Γ ⊢ fx ⦂ B) (fx′-typed : Γ ⊢ fx ⦂ B) →
-- --       x-typed 𝓡[ A ] x′-typed →
-- --       f ∙ x ⇓ fx →
-- --       f ∙ x′ ⇓ fx′ →
-- --       fx-typed 𝓡[ B ] fx′-typed
-- -- _𝓡[_]_ {x = x} {x′ = x′} {Γ = Γ} x-typed (Pair A B) x′-typed =
-- --   ∀ fst-x fst-x′ (fst-x-typed : Γ ⊢ fst-x ⦂ A) (fst-x′-typed : Γ ⊢ fst-x′ ⦂ A) snd-x snd-x′ (snd-x-typed : Γ ⊢ snd-x ⦂ B) (snd-x′-typed : Γ ⊢ snd-x′ ⦂ B) →
-- --   fst x ⇓ fst-x →
-- --   fst x′ ⇓ fst-x′ →
-- --   snd x ⇓ snd-x →
-- --   snd x′ ⇓ snd-x′ →
-- --   (fst-x-typed 𝓡[ A ] fst-x′-typed)
-- --     ×
-- --   (snd-x-typed 𝓡[ B ] snd-x′-typed)
-- -- _𝓡[_]_ {x = x} {x′ = x′} {Γ = Γ} x-typed (Sum A B) x′-typed =
-- --   (∀ y y′ (y-typed : Γ ⊢ y ⦂ A) (y′-typed : Γ ⊢ y′ ⦂ A) →
-- --     x ⇓ inl y →
-- --     x′ ⇓ inl y′ →
-- --     y-typed 𝓡[ A ] y′-typed)
-- --   ×
-- --   (∀ y y′ (y-typed : Γ ⊢ y ⦂ B) (y′-typed : Γ ⊢ y′ ⦂ B) →
-- --     x ⇓ inr y →
-- --     x′ ⇓ inr y′ →
-- --     y-typed 𝓡[ A ] y′-typed)
-- -- _𝓡[_]_ {x = f} {x′ = f′} {Γ = Γ} f-typed (Forall F) f′-typed =
-- --   ∀ A f＠A f′＠A (f＠A-typed : Γ ⊢ f＠A ⦂ F A) (f′＠A-typed : Γ ⊢ f′＠A ⦂ F A) →
-- --   {!!}
-- --   -- ∀ A f＠A f′＠A (f＠A-typed : Γ ⊢ f＠A ⦂ F A) (f′＠A-typed : Γ ⊢ f′＠A ⦂ F A) →
-- --   --   f ＠ A ⇓ f＠A →
-- --   --   f′ ＠ A ⇓ f′＠A →
-- --   --   f＠A-typed 𝓡[ F A ] f′＠A-typed -- TODO: Is this right?
-- -- _𝓡[_]_ x-typed (Ty-Var v) x′-typed =
-- --   {!!}
-- --   -- Var-rel v _ _ x-typed x′-typed

-- 𝓡-lemma : ∀ {Γ} {t : Term V} {A} →
--   (t-typed : Γ ⊢ t ⦂ A) →
--   ∃[ u ] Σ (Γ ⊢ u ⦂ A) λ u-typed →
--     t-typed 𝓡[ A ] u-typed
-- 𝓡-lemma T-unit = unit , T-unit , refl₁
-- 𝓡-lemma (T-var prf x) = {!!}
-- 𝓡-lemma (T-ƛ t-typed) = {!!}
-- 𝓡-lemma (T-∙ t-typed t-typed₁) = {!!}
-- 𝓡-lemma (T-Λ x) = {!!}
-- 𝓡-lemma (T-＠ t-typed) = {!!}
-- 𝓡-lemma (T-pair t-typed t-typed₁) =
--   let a , a-typed , a-rel = 𝓡-lemma t-typed
--       b , b-typed , b-rel = 𝓡-lemma t-typed₁
--   in
--   pair a b , T-pair a-typed b-typed ,
--   λ fst-x fst-x′ fst-x-typed fst-x′-typed snd-x snd-x′ snd-x-typed
--      snd-x′-typed x x₁ x₂ x₃ →
--      {!!} , {!!}
-- 𝓡-lemma (T-fst t-typed) = {!!}
-- 𝓡-lemma (T-snd t-typed) = {!!}
-- 𝓡-lemma (T-inl t-typed) = {!!}
-- 𝓡-lemma (T-inr t-typed) = {!!}
-- 𝓡-lemma (T-match t-typed t-typed₁ t-typed₂) = {!!}


-- fundamental-thm : ∀ {t : Term V} {A} →
--   (t-typed : ∅ ⊢ t ⦂ A) →
--   t-typed 𝓡[ A ] t-typed
-- fundamental-thm T-unit = refl₁
-- fundamental-thm (T-ƛ t-typed) = {!!}
-- fundamental-thm (T-∙ t-typed t-typed₁) = {!!}
-- fundamental-thm (T-Λ x) = {!!}
-- fundamental-thm (T-＠ t-typed) = {!!}
-- fundamental-thm (T-pair t-typed t-typed₁) =
--   λ fst-x fst-x′ fst-x-typed fst-x′-typed snd-x snd-x′ snd-x-typed
--      snd-x′-typed x x₁ x₂ x₃ →
--      {!!} , {!!}
-- fundamental-thm (T-fst t-typed) = {!!}
-- fundamental-thm (T-snd t-typed) = {!!}
-- fundamental-thm (T-inl t-typed) = {!!}
-- fundamental-thm (T-inr t-typed) = {!!}
-- fundamental-thm (T-match t-typed t-typed₁ t-typed₂) = {!!}

-- data _𝓡[_]_ {V} : Term V → Type V → Term V → Set where
--   𝓡-const : ∀ {x x′ A} →
--     Is-Const-Type A →
--     x ≡ x′ →
--     x 𝓡[ A ] x′

--   𝓡-⇒ : ∀ {f f′ A B} →
--     (∀ x x′ →
--       x 𝓡[ A ] x′ →
--       (f ∙ x) 𝓡[ B ] (f ∙ x′)) →
--     f 𝓡[ A ⇒ B ] f′
