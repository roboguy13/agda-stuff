open import Category
open import FunctorDefs
open import FunctorProperties
import ElementaryProperties
open import Yoneda
open import Agda
open import AgdaHom

open import Level renaming (suc to lsuc)

open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Empty
open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.HeterogeneousEquality hiding (trans; sym; cong; subst) renaming (_≅_ to _H≅_)

open import Axiom.UniquenessOfIdentityProofs.WithK

module Limits
  where

Cone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  (c : Category.Obj 𝔻) →
  Set (Level.suc o₁ Level.⊔ Level.suc ℓ₁ Level.⊔ Level.suc o₂ Level.⊔ Level.suc ℓ₂)
Cone F c =
  NatTrans (Const-Functor c) F

Cone-∘ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} {𝔼 : Category o₁ ℓ₁} →
  (F : Functor ℂ 𝔻) →
  (c : Category.Obj 𝔻) →
  (G : Functor 𝔻 𝔼) →
  Cone F c →
  Cone (G ∘F F) (actf G c)
Cone-∘ {o₁} {ℓ₁} {o₂} {ℓ₂} {ℂ} {𝔻} {𝔼} F c G cone =
  ((G ∘WL cone)
    ∘NT
   subst (λ x → NatTrans x (G ∘F Const-Functor c))
     (sym (Const-Functor-commutes {o₂} {ℓ₂} {o₁} {ℓ₁} {ℓ₂} {ℓ₂} {𝔻} {𝔼} {ℂ} {G}))
     NT-id
   )

ACone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  Set (Level.suc o₁ Level.⊔ Level.suc ℓ₁ Level.⊔ Level.suc o₂ Level.⊔
         Level.suc ℓ₂)
ACone F = ∃[ c ] (Cone F c)

Is-Universal-Cone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  (c : Category.Obj 𝔻) →
  Cone F c →
  Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc o₂ Level.⊔ lsuc ℓ₂)
Is-Universal-Cone {_} {_} {_} {_} {ℂ} {𝔻} F c cone =
  ∀ c′ (cone′ : Cone F c′) →
  Σ (c′ ⇒[ 𝔻 ] c) λ m →
  ∀ (A : Category.Obj 𝔻) (f : c ⇒[ 𝔻 ] A) (g : c′ ⇒[ 𝔻 ] A) →
  g ≡ (f ∘[ 𝔻 ] m)

Lim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc o₂ Level.⊔ lsuc ℓ₂)
Lim F = ∃[ c ] ∃[ cone ] (Is-Universal-Cone F c cone)



Fin-Cat : (n : ℕ) → Category Level.zero Level.zero
Fin-Cat n =
  record
    { Obj = Fin n
    ; _⇒_ = λ A B → A ≡ B
    ; _∘_ = λ f g → trans g f
    ; id = refl
    ; left-id = λ {A} {B} {f} → uip (trans f refl) f
    ; right-id = refl -- TODO: Why the asymmetry here?
    ; ∘-assoc = λ {A} {B} {C} {D} {f} {g} {h} → uip (trans h (trans g f)) (trans (trans h g) f)
    }

private
  eq-apply : ∀ {m} {A B : Set m} →
    A ≡ B →
    A →
    B
  eq-apply refl x = x

  elim-eq-apply : ∀ {m} {A B : Set m} {x} →
    (prf : A ≡ B) →
    eq-apply prf x H≅ x
  elim-eq-apply {_} {_} {_} {_} refl = refl
    -- x H≅ y
  -- elim-eq-apply {_} {_} {_} {_} {_} {refl} refl = refl

Fin-Cat-Functor : ∀ {o ℓ} {ℂ : Category o ℓ} →
  {n : ℕ} →
  (Fin n → Category.Obj ℂ) →
  Functor (Fin-Cat n) ℂ
Fin-Cat-Functor {_} {_} {ℂ} {n} fn =
  record
    { act = fn
    ; fmap′ = fmap-def
    ; fmap-id′ = λ A → refl
    ; fmap-∘′ = fmap-∘-def
    }
    where
      fmap-def : (A B : Fin n) → Arr (Fin-Cat n) A B → Arr ℂ (fn A) (fn B)
      fmap-def A B refl = Category.id ℂ

      fmap-∘-def : (A B C : Fin n) (f : Arr (Fin-Cat n) B C)
                    (g : Arr (Fin-Cat n) A B) →
                    comp ℂ (fmap-def B C f) (fmap-def A B g) ≡
                    fmap-def A C (comp (Fin-Cat n) f g)
      fmap-∘-def A B C refl refl = Category.left-id ℂ

×-Limit : ∀ {o ℓ} {ℂ : Category o ℓ} → (A B : Category.Obj ℂ) → Set (lsuc o Level.⊔ lsuc ℓ)
×-Limit {o} {ℓ} {ℂ} A B =
  Lim {Level.zero} {Level.zero} {o} {ℓ} {Fin-Cat 2} {ℂ} (Fin-Cat-Functor go)
  where
    go : Fin 2 → Category.Obj ℂ
    go Fin.zero = A
    go (suc Fin.zero) = B

Is-Continuous : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  ∀ {o₃ ℓ₃} →
  Functor ℂ 𝔻 →
  Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc o₂ Level.⊔ lsuc ℓ₂ Level.⊔
         lsuc o₃
         Level.⊔ lsuc ℓ₃
         Level.⊔ ℓ₂)
Is-Continuous {_} {_} {_} {_} {ℂ} {𝔻} {o₃} {ℓ₃} F =
  (𝔼 : Category o₃ ℓ₃) →
  (A : Functor 𝔼 ℂ) →
  (lim-A : Lim A) →
  (lim-FA : Lim (F ∘F A)) →
  let
    lim-A-apex = proj₁ lim-A
    lim-FA-apex = proj₁ lim-FA
    m = proj₂ (proj₂ lim-FA)

    m′ = m (actf F lim-A-apex) {!!}

    p : actf F lim-A-apex ⇒[ 𝔻 ] lim-FA-apex
    p = {!!}
  in
  Category.Obj 𝔼

-- Point : ∀ {o ℓ o₂ ℓ₂} {𝔻 : Category o ℓ} →
--   Functor 𝔻 (Agda {o₂} {ℓ₂})
-- Point {_} {_} {o₂} = Const-Functor (Lift o₂ ⊤)

-- -- Hom_C(c, F(-))
-- Hom-left : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
--   (A : Category.Obj (Op ℂ)) →
--   (F : Functor (Op 𝔻) ℂ) →
--   Functor (Op 𝔻) (Agda {ℓ₁} {ℓ₂})
-- Hom-left {_} {_} {_} {_} {ℂ} {𝔻} c F =
--   record
--     { act = λ x → (c ⇒[ ℂ ] (actf F x))
--     ; fmap′ = λ A B f → lift λ t → Functor.fmap F f ∘[ ℂ ] t
--     ; fmap-id′ = λ A → {!!}
--     ; fmap-∘′ = λ A B C f g → {!!}
--     }

-- -- Called "lîm" on nlab
-- PreLim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {I : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
--   (F : Functor (Op I) ℂ) →
--   Category.Obj ℂ →
--   Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc (lsuc ℓ₂))
-- PreLim {_} {_} {_} {_} {I} {ℂ} F c =
--   Hom [ Op I ,, Agda ] Point (Hom-left c F)

-- PreLim-Functor : ∀ {o₁ ℓ₁ o₂ ℓ₂} {I : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
--   (F : Functor (Op I) ℂ) →
--   Functor ℂ Agda
-- PreLim-Functor = {!!}

-- Is-Lim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {I : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
--   {F : Functor (Op I) ℂ} →
--   {c : Category.Obj ℂ} →
--   (limF : PreLim F c) →
--   Set {!!}
-- Is-Lim {_} {_} {_} {_} {I} {ℂ} {F} {c} limF =
--   {!!}
--   -- Σ (NatIso (Hom ? c ?) ?) ?

-- -- Lim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
-- --   Functor ℂ 𝔻 →
-- --   Set {!!}
-- -- Lim {_} {_} {_} {_} {ℂ} {𝔻} F =
-- --   ∃[ c ]
-- --   Σ (Cone F c) λ cone →
-- --   ∀ c′ (cone′ : Cone F c′) →
-- --   Σ![ c′ ⇒[ 𝔻 ] c ] (Is-NatIso ? ? cone)

-- -- HasLimit : ∀ {o₁ ℓ₁ o₂ ℓ₂} {J : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
-- --   (Lim-D : Cone F )

-- -- Cone-Cat : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
-- --   Functor (Op ℂ) 𝔻 →
-- --   Category.Obj 𝔻 →
-- --   Category {!!} {!!}
-- -- Cone-Cat {_} {_} {_} {_} {ℂ} {𝔻} F c =
-- --   record
-- --     { Obj = Cone F c
-- --     ; _⇒_ = λ A B → {!!}
-- --     ; _∘_ = {!!}
-- --     ; id = {!!}
-- --     ; left-id = {!!}
-- --     ; right-id = {!!}
-- --     ; ∘-assoc = {!!}
-- --     }

