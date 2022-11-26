-- Based on "Formalizing Category Theory in Agda" (Hu and Carette, 2020)

{-# OPTIONS --with-K #-}

open import Relation.Binary.Structures
open import Agda.Primitive
open import Relation.Nullary using (¬_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty


open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Axiom.Extensionality.Propositional
open import Relation.Binary.HeterogeneousEquality using (refl) renaming (_≅_ to _H≅_)
open import Axiom.UniquenessOfIdentityProofs.WithK

open import Level

open import Category

module FunctorDefs
  where

postulate fun-ext : ∀ {m n} → Extensionality m n

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

record Functor {o₁ ℓ₁ o₂ ℓ₂ : Level}
  (Src : Category o₁ ℓ₁) (Tgt : Category o₂ ℓ₂) : Set (lsuc (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂)) where
  field
    act : Category.Obj Src → Category.Obj Tgt
    fmap′ : ∀ A B →
      (A ⇒[ Src ] B) →
      (act A ⇒[ Tgt ] act B)

    fmap-id′ : ∀ A →
      (fmap′ A A (Category.id Src {A})) ≡ (Category.id Tgt)

    fmap-∘′ : ∀ A B C (f : B ⇒[ Src ] C) (g : A ⇒[ Src ] B) →
      (fmap′ B C f ∘[ Tgt ] fmap′ A B g)
        ≡
      (fmap′ A C (f ∘[ Src ] g))

  fmap : ∀ {A B} →
    (A ⇒[ Src ] B) →
    (act A ⇒[ Tgt ] act B)
  fmap {A} {B} = fmap′ A B

  fmap-id : ∀ {A} →
    (fmap′ A A (Category.id Src {A})) ≡ (Category.id Tgt)
  fmap-id {A} = fmap-id′ A

  fmap-∘ :
    ∀ {A B C} {f : B ⇒[ Src ] C} {g : A ⇒[ Src ] B} →
    (fmap′ B C f ∘[ Tgt ] fmap′ A B g)
      ≡
    (fmap′ A C (f ∘[ Src ] g))
  fmap-∘ {A} {B} {C} {f} {g} = fmap-∘′ A B C f g

cong₃ : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ}
          {x y v w s t}
      → (f : A → B → C → D)
      → x ≡ y → v ≡ w → s ≡ t → f x v s ≡ f y w t
cong₃ f refl refl refl = refl

Functor-η : ∀ {o ℓ} {Src : Category o ℓ} {Tgt : Category o ℓ} →
  ∀ {F G : Functor Src Tgt} →
  (act-eq : Functor.act F ≡ Functor.act G) →
  (Functor.fmap′ F H≅ Functor.fmap′ G) →
  F ≡ G
Functor-η {_} {_} {_} {_} {F} {G} refl refl
  with fun-ext (λ A → uip (Functor.fmap-id′ F A) (Functor.fmap-id′ G A))
     | fun-ext (λ A → fun-ext λ B → fun-ext λ C → fun-ext λ f → fun-ext λ g → uip (Functor.fmap-∘′ F A B C f g) (Functor.fmap-∘′ G A B C f g))
... | refl | refl = refl

actf = Functor.act

syntax actf F x = F · x

_∘F_ : ∀ {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level} {𝔸 : Category o₁ ℓ₁} {𝔹 : Category o₂ ℓ₂} {ℂ : Category o₃ ℓ₃} →
  (F : Functor 𝔹 ℂ) →
  (G : Functor 𝔸 𝔹) →
  Functor 𝔸 ℂ
_∘F_ {_} {_} {_} {_} {_} {_} {𝔸} {𝔹} {ℂ} F G =
  let record { act = act₁ ; fmap′ = fmap₁ ; fmap-id′ = fmap-id₁ ; fmap-∘′ = fmap-∘₁ } = F
      record { act = act ; fmap′ = fmap ; fmap-id′ = fmap-id ; fmap-∘′ = fmap-∘ } = G
  in
  record
    { act = λ x → F · (G · x)
    ; fmap′ = λ _ _ x → Functor.fmap F (Functor.fmap G x)
    ; fmap-id′ = λ A →
              let
                p : Functor.fmap F (Functor.fmap G {A} (Category.id 𝔸)) ≡ Functor.fmap F (Category.id 𝔹)
                p = cong (Functor.fmap F) (Functor.fmap-id G)
              in
              trans p (Functor.fmap-id F)
    ; fmap-∘′  = λ A B C f g →
             let
               p = Functor.fmap-∘ G {_} {_} {_} {f} {g}
             in
             trans (Functor.fmap-∘ F) (cong (Functor.fmap F) p)
    }

Id-Functor : {o ℓ : Level} →
  {ℂ : Category o ℓ} →
  Functor ℂ ℂ
Id-Functor {_} {_} {ℂ} =
  record
    { act = λ A → A
    ; fmap′ = λ A B f → f
    ; fmap-id′ = λ A → refl
    ; fmap-∘′ = λ A B C f g → refl
    }

Const-Functor : {o₁ ℓ₁ o₂ ℓ₂ : Level}
  {Src : Category o₁ ℓ₁} {Tgt : Category o₂ ℓ₂}
  (A : Category.Obj Tgt) → Functor Src Tgt
Const-Functor {_} {_} {_} {_} {Src} {Tgt} A =
  record
    { act = λ _ → A
    ; fmap′ = λ A₁ B x → Category.id Tgt
    ; fmap-id′ = λ A₁ → refl
    ; fmap-∘′ = λ A₁ B C f g → Category.left-id Tgt
    }

unfold-∘F : {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level} (A : Category o₁ ℓ₁) (B : Category o₂ ℓ₂) (C : Category o₃ ℓ₃) →
  (F : Functor B C) →
  (G : Functor A B) →
  ∀ {X Y} {f : X ⇒[ A ] Y} →
  Functor.fmap (F ∘F G) f ≡ Functor.fmap F (Functor.fmap G f)
unfold-∘F _ _ _ _ _ = refl


record NatTrans {o₁ ℓ₁ o₂ ℓ₂ : Level} {Src : Category o₁ ℓ₁} {Tgt : Category o₂ ℓ₂}
      (F G : Functor Src Tgt) : Set (lsuc (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂)) where
  field
    component : ∀ (x : Category.Obj Src) →
      (F · x) ⇒[ Tgt ] (G · x)

    natural : ∀ x y (f : x ⇒[ Src ] y) →
      (component y ∘[ Tgt ] Functor.fmap F f)
        ≡
      (Functor.fmap G f ∘[ Tgt ] component x)

NatTrans-η : ∀ {o₁ ℓ₁ o₂ ℓ₂ : Level} {Src : Category o₁ ℓ₁} {Tgt : Category o₂ ℓ₂}
  {F G : Functor Src Tgt}
  {α β : NatTrans F G} →
  NatTrans.component α ≡ NatTrans.component β →
  α ≡ β
NatTrans-η {_} {_} {_} {_} {_} {_} {_} {_} {α} {β} refl with fun-ext (λ x → fun-ext λ y → fun-ext λ f → uip (NatTrans.natural α x y f) (NatTrans.natural β x y f))
... | refl = refl

-- Whisker left
_∘WL_ : {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level} {A : Category o₁ ℓ₁} {B : Category o₂ ℓ₂} {C : Category o₃ ℓ₃} →
  {F G : Functor A B} →
  (H : Functor B C) →
  (α : NatTrans F G) →
  NatTrans (H ∘F F) (H ∘F G)
_∘WL_ {_} {_} {_} {_} {_} {_} {A} {B} {C} {F} {G} H α =
  record
    { component = λ x → Functor.fmap H (NatTrans.component α x)
    ; natural = λ x y f →
              let
                p : ((Functor.fmap H (NatTrans.component α y)) ∘[ C ] (Functor.fmap (H ∘F F) f))
                      ≡
                    ((Functor.fmap H (NatTrans.component α y)) ∘[ C ] (Functor.fmap H (Functor.fmap F f)))
                p = rewrite-right-∘ C (unfold-∘F A B C H F {x} {y} {f}) refl

                q : ((Functor.fmap H (NatTrans.component α y)) ∘[ C ] (Functor.fmap H (Functor.fmap F f)))
                      ≡
                    ((Functor.fmap H (NatTrans.component α y ∘[ B ] Functor.fmap F f)))
                q = Functor.fmap-∘ H

                s : ((Functor.fmap H (NatTrans.component α y ∘[ B ] Functor.fmap F f)))
                      ≡
                    ((Functor.fmap H (Functor.fmap G f ∘[ B ] NatTrans.component α x)))
                s = cong (λ z → Functor.fmap H z) (NatTrans.natural α x y f)

                s2 : ((Functor.fmap H (Functor.fmap G f ∘[ B ] NatTrans.component α x)))
                       ≡
                     ((Functor.fmap H (Functor.fmap G f)) ∘[ C ] Functor.fmap H (NatTrans.component α x))
                s2 = sym (Functor.fmap-∘ H)

                s3 : ((Functor.fmap H (Functor.fmap G f)) ∘[ C ] Functor.fmap H (NatTrans.component α x))
                       ≡
                     ((Functor.fmap (H ∘F G) f ∘[ C ] Functor.fmap H (NatTrans.component α x)))
                s3 = rewrite-left-∘ C (unfold-∘F A B C H G) refl
              in
              trans p (trans q (trans s (trans s2 s3)))
    }
  where
    open CatBasics


-- -- Whisker right
-- _∘WR_ : {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level} {A : Category o₁ ℓ₁} {B : Category o₂ ℓ₂} {C : Category o₃ ℓ₃} →
--   {F G : Functor B C} →
--   (α : NatTrans F G) →
--   (H : Functor A B) →
--   NatTrans (F ∘F H) (G ∘F H)
-- _∘WR_ α H =
--   record
--     { component = λ x → NatTrans.component α (Functor.act H x)
--     ; natural = {!!}
--     }

Op : ∀ {o ℓ} → Category o ℓ → Category o ℓ
Op record { Obj = Obj ; _⇒_ = _⇒_ ; _∘_ = _∘_ ; id = id ; left-id = left-id ; right-id = right-id ; ∘-assoc = ∘-assoc } =
  record
    { Obj = Obj
    ; _⇒_ = λ x y → y ⇒ x
    ; _∘_ = λ f g → g ∘ f
    ; id = id
    ; left-id = λ {A} {B} {f} → right-id
    ; right-id = λ {A} {B} {f} → left-id
    ; ∘-assoc = sym ∘-assoc
    }

-- Op-Functor : ∀ {o ℓ} {ℂ : Category o ℓ} →
--   Functor ℂ (Op ℂ)
-- Op-Functor {_} {_} {ℂ} =
--   record
--     { act = λ x → x
--     ; fmap′ = λ A B x → {!!}
--     ; fmap-id′ = {!!}
--     ; fmap-∘′ = {!!}
--     }

NT-id : {o₁ ℓ₁ o₂ ℓ₂ : Level} {Src : Category o₁ ℓ₁} {Tgt : Category o₂ ℓ₂}
  {F : Functor Src Tgt} →
  NatTrans F F
NT-id {_} {_} {_} {_} {Src} {Tgt} {F} =
  record
    { component = λ x → Functor.fmap′ F x x (Category.id Src)
    ; natural = λ x y f →
        trans (CatBasics.rewrite-left-∘ Tgt (sym (Functor.fmap-id F)) refl)
          (trans (Category.left-id Tgt)
            (sym (CatBasics.rewrite-right-∘ Tgt (sym (Functor.fmap-id F)) (Category.right-id Tgt))))
    }

_∘NT_ : {o₁ ℓ₁ o₂ ℓ₂ : Level} {Src : Category o₁ ℓ₁} {Tgt : Category o₂ ℓ₂}
  {F G H : Functor Src Tgt} →
  (α : NatTrans G H) →
  (β : NatTrans F G) →
  NatTrans F H
_∘NT_ {_} {_} {_} {_} {Src} {Tgt} {F} {G} {H} α β =
  let
    record { component = component-α ; natural = natural-α } = α
    record { component = component-β ; natural = natural-β } = β
  in
  record
    { component = λ x → component-α x ∘[ Tgt ] component-β x
    ; natural = λ x y f →
              let
                α-x : actf G x ⇒ actf H x
                α-x = component-α x

                α-y : actf G y ⇒ actf H y
                α-y = component-α y

                β-x : actf F x ⇒ actf G x
                β-x = component-β x

                β-y : actf F y ⇒ actf G y
                β-y = component-β y

                x-∘ : actf F x ⇒ actf H x
                x-∘ = α-x ∘ β-x

                y-∘ : actf F y ⇒ actf H y
                y-∘ = α-y ∘ β-y

                n1 : (α-y ∘ Functor.fmap G f) ≡ (Functor.fmap H f ∘ α-x)
                n1 = NatTrans.natural α x y f

                n2 : (β-y ∘ Functor.fmap F f) ≡ (Functor.fmap G f ∘ β-x)
                n2 = NatTrans.natural β x y f

                m1 : ∀ z → (component-α z ∘ Functor.fmap G (Category.id Src)) ≡ (Functor.fmap H (Category.id Src) ∘ component-α z)
                m1 z = NatTrans.natural α z z (Category.id Src)

                prf0 : ((α-y ∘ β-y) ∘ Functor.fmap F f) ≡ (α-y ∘ (β-y ∘ Functor.fmap F f))
                prf0 = ∘-assoc

                prf1 : ((α-y ∘ β-y) ∘ Functor.fmap F f) ≡ (α-y ∘ (Functor.fmap G f ∘ β-x))
                prf1 = trans prf0 (rewrite-right-∘ (sym n2) refl)

                prf2 : (α-y ∘ (Functor.fmap G f ∘ β-x)) ≡ ((α-y ∘ Functor.fmap G f) ∘ β-x)
                prf2 = sym ∘-assoc

                prf3 : ((α-y ∘ Functor.fmap G f) ∘ β-x) ≡ ((Functor.fmap H f ∘ α-x) ∘ β-x)
                prf3 = rewrite-left-∘ (sym n1) refl

                prf4 : ((Functor.fmap H f ∘ α-x) ∘ β-x) ≡ (Functor.fmap H f ∘ (α-x ∘ β-x))
                prf4 = ∘-assoc

                prf : ((α-y ∘ β-y) ∘ Functor.fmap F f) ≡ (Functor.fmap H f ∘ (α-x ∘ β-x))
                prf = trans prf1 (trans prf2 (trans prf3 prf4))
              in
              prf
    }
  where
  open Category.Category Tgt
  open CatBasics Tgt


_×cat_ : ∀ {o₁ ℓ₁ o₂ ℓ₂} →
  Category o₁ ℓ₁ → Category o₂ ℓ₂ → Category (o₁ ⊔ o₂) (ℓ₁ ⊔ ℓ₂)
_×cat_ record { Obj = Obj₁ ; _⇒_ = _⇒₁_ ; _∘_ = _∘₁_ ; id = id₁ ; left-id = left-id₁ ; right-id = right-id₁ ; ∘-assoc = ∘-assoc₁ } record { Obj = Obj ; _⇒_ = _⇒_ ; _∘_ = _∘_ ; id = id ; left-id = left-id ; right-id = right-id ; ∘-assoc = ∘-assoc } =
  record
    { Obj = Obj₁ × Obj
    ; _⇒_ = λ (x₁ , x₂) (y₁ , y₂) → (x₁ ⇒₁ y₁) × (x₂ ⇒ y₂)
    ; _∘_ = λ (f₁ , f₂) (g₁ , g₂) → (f₁ ∘₁ g₁) , (f₂ ∘ g₂)
    ; id = id₁ , id
    ; left-id = λ {A} {B} {f} → cong₂ _,_ left-id₁ left-id
    ; right-id = cong₂ _,_ right-id₁ right-id
    ; ∘-assoc = cong₂ _,_ ∘-assoc₁ ∘-assoc
    }

×cat-proj₁ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} → Functor (ℂ ×cat 𝔻) ℂ
×cat-proj₁ {_} {_} {_} {_} {ℂ} {𝔻} =
  record
    { act = proj₁
    ; fmap′ = λ _ _ (f , g) → f
    ; fmap-id′ = λ A → refl
    ; fmap-∘′ = λ A B C f g → refl
    }

×cat-proj₂ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} → Functor (ℂ ×cat 𝔻) 𝔻
×cat-proj₂ {_} {_} {_} {_} {ℂ} {𝔻} =
  record
    { act = proj₂
    ; fmap′ = λ _ _ (f , g) → g
    ; fmap-id′ = λ A → refl
    ; fmap-∘′ = λ A B C f g → refl
    }

Functor-⊗ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {o₃ ℓ₃ o₄ ℓ₄} →
  {ℂ₁ : Category o₁ ℓ₁} → {ℂ₂ : Category o₂ ℓ₂} →
  {𝔻₁ : Category o₃ ℓ₃} → {𝔻₂ : Category o₄ ℓ₄} →
  (F : Functor ℂ₁ 𝔻₁) →
  (G : Functor ℂ₂ 𝔻₂) →
  Functor (ℂ₁ ×cat ℂ₂) (𝔻₁ ×cat 𝔻₂)
Functor-⊗ {_} {_} {_} {_} {_} {_} {_} {_} {ℂ₁} {ℂ₂} {𝔻₁} {𝔻₂} F G =
  record
    { act = λ (x , y) → (actf F x , actf G y)
    ; fmap′ = λ A B (f , g) → Functor.fmap′ F (proj₁ A) (proj₁ B) f , Functor.fmap′ G (proj₂ A) (proj₂ B) g
    ; fmap-id′ = λ A → cong₂ _,_ (Functor.fmap-id F) (Functor.fmap-id G)
    ; fmap-∘′ = λ A B C f g → cong₂ _,_ (Functor.fmap-∘ F) (Functor.fmap-∘ G)
    }

FΔ : ∀ {o ℓ} {ℂ : Category o ℓ} → Functor ℂ (ℂ ×cat ℂ)
FΔ {_} {_} {ℂ} =
  record
    { act = λ x → x , x
    ; fmap′ = λ A B f → f , f
    ; fmap-id′ = λ _ → refl
    ; fmap-∘′ = λ A B C f g → refl
    }


[_,,_] : ∀ {o₁ ℓ₁ o₂ ℓ₂} (ℂ : Category o₁ ℓ₁) (𝔻 : Category o₂ ℓ₂) →
  Category (suc o₁ ⊔ suc ℓ₁ ⊔ suc o₂ ⊔ suc ℓ₂) (suc o₁ ⊔ suc ℓ₁ ⊔ suc o₂ ⊔ suc ℓ₂)
[ ℂ ,, 𝔻 ] =
  record
    { Obj = Functor ℂ 𝔻
    ; _⇒_ = λ F G → NatTrans F G
    ; _∘_ = λ {F} {G} {H} α β → α ∘NT β
    ; id = record { component = λ x → Category.id 𝔻 ; natural = λ _ _ f → trans left-id (sym right-id) }
    ; left-id = NatTrans-η (fun-ext λ x → left-id)
    ; right-id = NatTrans-η (fun-ext λ x → right-id)
    ; ∘-assoc = λ {A} {B} {C} {D} {α} {β} {γ} → NatTrans-η (fun-ext λ x → ∘-assoc)
    }
    where
    open Category.Category 𝔻
    open CatBasics 𝔻

Iso′ : ∀ {o ℓ} (ℂ : Category o ℓ) →
  (A B : Category.Obj ℂ) →
  Set ℓ
Iso′ {_} {_}  ℂ A B =
  Σ (A ⇒[ ℂ ] B) λ f →
  Σ (B ⇒[ ℂ ] A) λ g →
      ((f ∘[ ℂ ] g) ≡ Category.id ℂ)
        ×
      ((g ∘[ ℂ ] f) ≡ Category.id ℂ)



syntax Iso′ ℂ A B = A ≅[ ℂ ] B

exists-unique : ∀ {o ℓ} (ℂ : Category o ℓ) {m : Level} → ∀ A B → (k : (A ⇒[ ℂ ] B) → Set m) → Set (ℓ ⊔ m)
exists-unique ℂ A B P =
  Σ (A ⇒[ ℂ ] B) λ m →
    P m ×
      ∀ (n : A ⇒[ ℂ ] B) → P n → n ≡ m

Σ![_⇒_] : ∀ {o ℓ} {ℂ : Category o ℓ} {m : Level} → ∀ A B → (k : (A ⇒[ ℂ ] B) → Set m) → Set (ℓ ⊔ m)
Σ![_⇒_] {_} {_} {ℂ} A B P =
  Σ (A ⇒[ ℂ ] B) λ m →
    P m ×
      ∀ (n : A ⇒[ ℂ ] B) → P n → n ≡ m


syntax exists-unique ℂ A B = Σ![ A ⇒[ ℂ ] B ]

-- Σ![_⇒[_]_] : ∀ {o ℓ} {ℂ : Category o ℓ} {m : Level} → ∀ A B → (k : (A ⇒[ ℂ ] B) → Set m) → Set (ℓ ⊔ m)
-- Σ![_⇒[_]_] {_} {_} {ℂ} A B P =
--   Σ (A ⇒[ ℂ ] B) λ m →
--     P m ×
--       ∀ (n : A ⇒[ ℂ ] B) → P n → n ≡ m


