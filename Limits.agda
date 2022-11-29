open import Category
open import FunctorDefs
open import FunctorProperties
import ElementaryProperties
open import Yoneda
open import Agda
open import AgdaHom

open import Level renaming (suc to lsuc; zero to lzero)

open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (lift)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Product.Properties
open import Relation.Binary.Definitions using (Substitutive)

open import Function hiding (case_of_) -- using (Inverse)

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.HeterogeneousEquality hiding (cong; cong₂) renaming (_≅_ to _H≅_; trans to H-trans; sym to H-sym; subst to H-subst)

open import Axiom.UniquenessOfIdentityProofs.WithK

open import ArrowCat

module Limits
  where


Cone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  (c : Category.Obj 𝔻) →
  Set (Level.suc o₁ Level.⊔ Level.suc ℓ₁ Level.⊔ Level.suc o₂ Level.⊔ Level.suc ℓ₂)
Cone F c =
  NatTrans (Const-Functor c) F

Cone-∘ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} {𝔼 : Category o₁ ℓ₁} →
  {F : Functor ℂ 𝔻} →
  {c : Category.Obj 𝔻} →
  (G : Functor 𝔻 𝔼) →
  Cone F c →
  Cone (G ∘F F) (actf G c)
Cone-∘ {o₁} {ℓ₁} {o₂} {ℓ₂} {ℂ} {𝔻} {𝔼} {F} {c} G cone =
  ((G ∘WL cone)
    ∘NT
   subst (λ x → NatTrans x (G ∘F Const-Functor c))
     (sym (Const-Functor-commutes {o₂} {ℓ₂} {o₁} {ℓ₁} {ℓ₂} {ℓ₂} {𝔻} {𝔼} {ℂ} {G}))
     NT-id
   )

map-Cone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  {F : Functor ℂ 𝔻} →
  {c c′ : Category.Obj 𝔻} →
  (c′ ⇒[ 𝔻 ] c) →
  Cone F c →
  Cone F c′
map-Cone {_} {_} {_} {_} {ℂ} {𝔻}  {F} {c} {c′} f cone =
  cone ∘NT lift-to-NT f

-- lift-Cone : ∀ {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
--   {F : Functor ℂ 𝔻} →
--   {c : Category.Obj 𝔻} →

-- Cone-lift : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
--   (F : Functor ℂ 𝔻) →
--   (c : Category.Obj 𝔻) →
--   Cone F c
-- Cone-lift F c =
--   record
--     { component = λ x → {!!}
--     ; natural = {!!}
--     }

Cone-cat : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  (c : Category.Obj 𝔻) →
  Category (o₁ ⊔ o₁ ⊔ ℓ₂) ℓ₂
Cone-cat {o₁} {ℓ₁} {o₂} {ℓ₂} {ℂ} {𝔻} F c =
  (Const-Functor {o₁} {ℓ₁} {o₂} {ℓ₂} {ℂ} {𝔻} c)
    ↓
  F

Cone-cat-2 : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  Category (lsuc o₁ ⊔ lsuc ℓ₁ ⊔ lsuc o₂ ⊔ lsuc ℓ₂) ℓ₂
Cone-cat-2 {o₁} {ℓ₁} {o₂} {ℓ₂} {ℂ} {𝔻} F =
  record
    { Obj = ∃[ c ](Cone F c)
    ; _⇒_ = λ (c , x) (c′ , y) → (c ⇒[ Op 𝔻 ] c′)
    -- ; _⇒_ = λ (x , (c , f)) (y , (c′ , g)) → (x ⇒[ Op 𝔻 ] y) -- × {!!}
    ; _∘_ = λ f g → f ∘[ Op 𝔻 ] g
    ; id = λ {A} → Category.id (Op 𝔻)
    ; left-id = Category.left-id (Op 𝔻)
    ; right-id = Category.right-id (Op 𝔻)
    ; ∘-assoc = Category.∘-assoc (Op 𝔻)
    }

-- Cone-F : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
--   (F : Functor ℂ 𝔻) →
--   Functor (Op ℂ) (Cone-cat-2 F)
-- Cone-F {_} {_} {_} {_} {ℂ} {𝔻} F =
--   record
--     { act = λ x → actf F x , {!!}
--     ; fmap′ = λ A B f → Functor.fmap F f
--     ; fmap-id′ = Functor.fmap-id′ F
--     ; fmap-∘′ = λ A B C f g → Functor.fmap-∘′ F C B A g f
--     }

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
  Functor ℂ 𝔻 →
  Set (lsuc o₁ ⊔ lsuc ℓ₁ ⊔ lsuc o₂ ⊔ lsuc ℓ₂)
Is-Continuous {_} {_} {o₂} {ℓ₂} {ℂ} {𝔻} F =
  (𝔼 : Category o₂ ℓ₂) →
  (A : Functor 𝔼 ℂ) →
  (lim-A : Lim A) →
  (lim-FA : Lim (F ∘F A)) →
  let
    lim-A-apex = proj₁ lim-A
    lim-FA-apex = proj₁ lim-FA
    m = proj₂ (proj₂ lim-FA)

    cone : Cone A lim-A-apex
    cone = proj₁ (proj₂ lim-A)

    c-f-0 : Cone (F ∘F A) (actf F (proj₁ lim-A))
    c-f-0 = Cone-∘ F cone

    x , y = m (actf F lim-A-apex) c-f-0

    p : actf F lim-A-apex ⇒[ 𝔻 ] lim-FA-apex
    p = x
  in
  ∃[ p⁻¹ ]
    (ElementaryProperties.Iso 𝔻 p p⁻¹)

よ-Is-Continuous : ∀ {ℓ} {ℂ : Category (lsuc ℓ) ℓ} → Is-Continuous (よ ℂ)
よ-Is-Continuous {ℓ} {ℂ} 𝔼 A lim-A lim-よA =
  let
    lim-A-apex : Category.Obj ℂ
    lim-A-apex = proj₁ lim-A

    lim-よA-apex : Category.Obj [ Op ℂ ,, Agda ]
    lim-よA-apex = proj₁ lim-よA

    lim-A-cone , lim-A-universal = proj₂ lim-A
    lim-よA-cone , lim-よA-universal = proj₂ lim-よA

    m = proj₂ (proj₂ lim-よA)
    m′ = proj₂ (proj₂ lim-A)

    cone : Cone A lim-A-apex
    cone = proj₁ (proj₂ lim-A)

    x , y = m (actf (よ ℂ) lim-A-apex) (Cone-∘ (よ ℂ) cone)

    -- p : actf (よ ℂ) lim-A-apex ⇒[ ([ Op ℂ ,, Agda ]) ] lim-よA-apex
    p : NatTrans (actf (よ ℂ) lim-A-apex) lim-よA-apex
    p = x

    よ-A : Functor 𝔼 [ Op ℂ ,, Agda ]
    よ-A = (よ ℂ ∘F A)

    -- cone-よ : Cone よ-A lim-よA-apex
    cone-よ : NatTrans (Const-Functor lim-よA-apex) (よ ℂ ∘F A)
    cone-よ = proj₁ (proj₂ lim-よA)

    -- x₀′ , _ = m′ {!!} {!!}

    -- x′ : NatTrans lim-よA-apex lim-よA-apex
    -- x′ = x₀′

    Tgt : Category.Obj [ Op ℂ ,, Agda ]
    Tgt = actf (よ ℂ) lim-A-apex

    -- p⁻¹ : NatTrans lim-よA-apex (actf (よ ℂ) lim-A-apex)
    -- p⁻¹ = {!!}

    q₀ , _ = proj₂ (proj₂ lim-A) lim-A-apex cone

    -- h : Functor (Op ℂ) Agda → Category.Obj ℂ
    -- h = lower (Functor.fmap lim-よA-apex q₀) {!!}
    h = (Functor.fmap lim-よA-apex q₀)

    -- x2 , y2 = m′ {!!} {!!}
    -- p⁻¹ : lim-よA-apex ⇒[ ([ Op ℂ ,, Agda ]) ] actf (よ ℂ) lim-A-apex
    p⁻¹ : NatTrans lim-よA-apex (actf (よ ℂ) lim-A-apex)
    p⁻¹ = -- _∘WL_ {lsuc ℓ} {ℓ} {lsuc ℓ} {ℓ} {{!!}} {{!!}} {Op ℂ} {Op ℂ} {Agda} {Id-Functor} (H {?}) NT-id
      {!!}
      -- record
      --   { component = λ x₁ → lift (λ x₂ →
      --               let
      --                 ty = lim-よA-apex
      --                 x₂′ : actf lim-よA-apex x₁
      --                 x₂′ = x₂

      --                 p′ = NatTrans.component p x₁
      --                 -- z = Functor.fmap (よ ℂ) {!!}

      --                 cone′ : Cone A x₁
      --                 cone′ =
      --                   record
      --                     { component = -- λ x₃ → (lower (Functor.fmap {_} {_} {_} {_} {{!!}} {Agda} (Const-Functor {!!}) {{!!}} {{!!}} (actf {{!!}} A x₃)) {!!})
      --                           λ z → {!!}
      --                     ; natural = {!!}
      --                     }

      --                 -- w = Functor.fmap lim-よA-apex {!!}

      --                 m-A , _ = proj₂ (proj₂ lim-A) x₁ {!!}

      --                 cone′′ : Cone (よ ℂ ∘F A) (actf (よ ℂ) x₁)
      --                 cone′′ = Cone-∘ (よ ℂ) cone′

      --                 m1 = m (actf (よ ℂ) x₁) cone′′ -- (Cone-∘ (よ ℂ) {!!}) --x₂

      --                 test : Lift ℓ (Arr (ℂop ℂ) (proj₁ lim-A) x₁)
      --                 test = lift {!!}

      --                 w′ : Functor.act (actf (よ ℂ) (proj₁ lim-A)) x₁
      --                 w′ = test

      --                 w = lower (Functor.fmap (actf (よ ℂ) (proj₁ lim-A)) (Category.id (Op ℂ))) {!!} -- (Functor.fmap (actf (よ ℂ) (proj₁ lim-A)) {!!})
      --               in
      --               w)
      --   ; natural = λ x₁ y₁ f → {!!}
      --   }
  in
  {!!}
  -- p⁻¹ , {!!} , {!!}
  -- p⁻¹ , p
  -- {!!} , {!!}
