-- Based on "Formalizing Category Theory in Agda" (Hu and Carette, 2020)

open import Relation.Binary.Structures
open import Agda.Primitive
open import Relation.Nullary using (¬_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty


open import Relation.Binary.PropositionalEquality hiding (refl; trans; sym)

open import Level

open import Category

module CategoryRecord
  where

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

record Functor {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ : Level}
  (Src : Category o₁ ℓ₁ e₁) (Tgt : Category o₂ ℓ₂ e₂) : Set (lsuc (o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂)) where
  field
    act : Category.Obj Src → Category.Obj Tgt
    fmap : ∀ {A B} →
      (A ⇒[ Src ] B) →
      (act A ⇒[ Tgt ] act B)

    fmap-id : ∀ {A} →
      (fmap (Category.id Src {A})) ≈[ Tgt ] (Category.id Tgt)

    fmap-∘ : ∀ {A B C} {f : B ⇒[ Src ] C} {g : A ⇒[ Src ] B} →
      (fmap f ∘[ Tgt ] fmap g)
        ≈[ Tgt ]
      (fmap (f ∘[ Src ] g))

    fmap-cong : ∀ {A B} {f g : A ⇒[ Src ] B} →
      f ≈[ Src ] g →
      fmap f ≈[ Tgt ] fmap g

actf = Functor.act

syntax actf F x = F · x

_F∘_ : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃ : Level} {𝔸 : Category o₁ ℓ₁ e₁} {𝔹 : Category o₂ ℓ₂ e₂} {ℂ : Category o₃ ℓ₃ e₃} →
  (F : Functor 𝔹 ℂ) →
  (G : Functor 𝔸 𝔹) →
  Functor 𝔸 ℂ
_F∘_ {_} {_} {_} {_} {_} {_} {_} {_} {_} {𝔸} {𝔹} {ℂ} F G =
  let record { act = act₁ ; fmap = fmap₁ ; fmap-id = fmap-id₁ ; fmap-∘ = fmap-∘₁ } = F
      record { act = act ; fmap = fmap ; fmap-id = fmap-id ; fmap-∘ = fmap-∘ } = G
  in
  record
    { act = λ x → F · (G · x)
    ; fmap = λ x → Functor.fmap F (Functor.fmap G x)
    ; fmap-id = λ {A} →
              let
                p : Functor.fmap F (Functor.fmap G {A} (Category.id 𝔸)) ≈[ ℂ ] Functor.fmap F (Category.id 𝔹)
                p = Functor.fmap-cong F (Functor.fmap-id G)
              in
              IsEquivalence.trans (Category.equiv ℂ) p (Functor.fmap-id F)
    ; fmap-∘ = λ {A} {B} {C} {f} {g} →
             let
               p = Functor.fmap-∘ G {_} {_} {_} {f} {g}
             in
             IsEquivalence.trans (Category.equiv ℂ) (Functor.fmap-∘ F) (Functor.fmap-cong F p)
    ; fmap-cong = λ x → Functor.fmap-cong F (Functor.fmap-cong G x)
    }

record NatTrans {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ : Level} {Src : Category o₁ ℓ₁ e₁} {Tgt : Category o₂ ℓ₂ e₂}
      (F G : Functor Src Tgt) : Set (lsuc (o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂)) where
  field
    component : ∀ (x : Category.Obj Src) →
      (F · x) ⇒[ Tgt ] (G · x)

    natural : ∀ {x y} (f : x ⇒[ Src ] y) →
      (component y ∘[ Tgt ] Functor.fmap F f)
        ≈[ Tgt ]
      (Functor.fmap G f ∘[ Tgt ] component x)

_∘NT_ : {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ : Level} {Src : Category o₁ ℓ₁ e₁} {Tgt : Category o₂ ℓ₂ e₂}
  {F G H : Functor Src Tgt} →
  (α : NatTrans G H) →
  (β : NatTrans F G) →
  NatTrans F H
_∘NT_ {_} {_} {_} {_} {_} {_} {Src} {Tgt} {F} {G} {H} α β =
  let
    record { component = component-α ; natural = natural-α } = α
    record { component = component-β ; natural = natural-β } = β
  in
  record
    { component = λ x → component-α x ∘[ Tgt ] component-β x
    ; natural = λ {x} {y} f →
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

                n1 : (α-y ∘ Functor.fmap G f) ≈ (Functor.fmap H f ∘ α-x)
                n1 = NatTrans.natural α f

                n2 : (β-y ∘ Functor.fmap F f) ≈ (Functor.fmap G f ∘ β-x)
                n2 = NatTrans.natural β f

                m1 : ∀ z → (component-α z ∘ Functor.fmap G (Category.id Src)) ≈ (Functor.fmap H (Category.id Src) ∘ component-α z)
                m1 _ = NatTrans.natural α (Category.id Src)

                prf0 : ((α-y ∘ β-y) ∘ Functor.fmap F f) ≈ (α-y ∘ (β-y ∘ Functor.fmap F f))
                prf0 = ∘-assoc

                prf1 : ((α-y ∘ β-y) ∘ Functor.fmap F f) ≈ (α-y ∘ (Functor.fmap G f ∘ β-x))
                prf1 = trans prf0 (rewrite-right-∘ (sym n2) refl)

                prf2 : (α-y ∘ (Functor.fmap G f ∘ β-x)) ≈ ((α-y ∘ Functor.fmap G f) ∘ β-x)
                prf2 = sym ∘-assoc

                prf3 : ((α-y ∘ Functor.fmap G f) ∘ β-x) ≈ ((Functor.fmap H f ∘ α-x) ∘ β-x)
                prf3 = rewrite-left-∘ (sym n1) refl

                prf4 : ((Functor.fmap H f ∘ α-x) ∘ β-x) ≈ (Functor.fmap H f ∘ (α-x ∘ β-x))
                prf4 = ∘-assoc

                prf : ((α-y ∘ β-y) ∘ Functor.fmap F f) ≈ (Functor.fmap H f ∘ (α-x ∘ β-x))
                prf = trans prf1 (trans prf2 (trans prf3 prf4))
              in
              prf
    }
  where
  open Category.Category Tgt
  open CatBasics Tgt


-- (((NatTrans.component α y) ∘[ Tgt ] (NatTrans.component β y))
--    ∘[ Tgt ]
--  (Functor.fmap F f))
--   ≈
-- ((Functor.fmap H f)
--    ∘[ Tgt ]
--  ((NatTrans.component α x) ∘[ Tgt ] (NatTrans.component β x)))



              -- IsEquivalence.trans (Category.equiv Tgt) {!!} {!!}
    -- }

_×cat_ : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} →
  Category o₁ ℓ₁ e₁ → Category o₂ ℓ₂ e₂ → Category (o₁ ⊔ o₂) (ℓ₁ ⊔ ℓ₂) (e₁ ⊔ e₂)
_×cat_ record { Obj = Obj₁ ; _⇒_ = _⇒₁_ ; _∘_ = _∘₁_ ; _≈_ = _≈₁_ ; equiv = equiv₁ ; ∘-resp-≈ = ∘-resp-≈₁ ; id = id₁ ; left-id = left-id₁ ; right-id = right-id₁ ; ∘-assoc = ∘-assoc₁ } record { Obj = Obj ; _⇒_ = _⇒_ ; _∘_ = _∘_ ; _≈_ = _≈_ ; equiv = equiv ; ∘-resp-≈ = ∘-resp-≈ ; id = id ; left-id = left-id ; right-id = right-id ; ∘-assoc = ∘-assoc } =
  record
    { Obj = Obj₁ × Obj
    ; _⇒_ = λ (x₁ , x₂) (y₁ , y₂) → (x₁ ⇒₁ y₁) × (x₂ ⇒ y₂)
    ; _∘_ = λ (f₁ , f₂) (g₁ , g₂) → (f₁ ∘₁ g₁) , (f₂ ∘ g₂)
    ; _≈_ = λ (f₁ , f₂) (g₁ , g₂) → (f₁ ≈₁ g₁) × (f₂ ≈ g₂)
    ; equiv = record
                { refl = IsEquivalence.refl equiv₁ , IsEquivalence.refl equiv
                ; sym = λ (x , y) → IsEquivalence.sym equiv₁ x , IsEquivalence.sym equiv y
                ; trans = λ (x₁ , x₂) (y₁ , y₂) → IsEquivalence.trans equiv₁ x₁ y₁ , IsEquivalence.trans equiv x₂ y₂
                }
    ; ∘-resp-≈ = λ (x₁ , x₂) (y₁ , y₂) → ∘-resp-≈₁ x₁ y₁ , ∘-resp-≈ x₂ y₂
    ; id = id₁ , id
    ; left-id = left-id₁ , left-id
    ; right-id = right-id₁ , right-id
    ; ∘-assoc = ∘-assoc₁ , ∘-assoc
    }

×cat-proj₁ : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} {ℂ : Category o₁ ℓ₁ e₁} {𝔻 : Category o₂ ℓ₂ e₂} → Functor (ℂ ×cat 𝔻) ℂ
×cat-proj₁ {_} {_} {_} {_} {_} {_} {ℂ} {𝔻} =
  record
    { act = proj₁
    ; fmap = λ (f , g) → f
    ; fmap-id = λ {A} → IsEquivalence.refl (Category.equiv ℂ)
    ; fmap-∘ = λ {A} {B} {C} {f} {g} → IsEquivalence.refl (Category.equiv ℂ)
    ; fmap-cong = λ (x , y) → x
    }

×cat-proj₂ : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} {ℂ : Category o₁ ℓ₁ e₁} {𝔻 : Category o₂ ℓ₂ e₂} → Functor (ℂ ×cat 𝔻) 𝔻
×cat-proj₂ {_} {_} {_} {_} {_} {_} {ℂ} {𝔻} =
  record
    { act = proj₂
    ; fmap = λ (f , g) → g
    ; fmap-id = λ {A} → IsEquivalence.refl (Category.equiv 𝔻)
    ; fmap-∘ = λ {A} {B} {C} {f} {g} → IsEquivalence.refl (Category.equiv 𝔻)
    ; fmap-cong = λ (x , y) → y
    }

[_,,_] : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} (ℂ : Category o₁ ℓ₁ e₁) (𝔻 : Category o₂ ℓ₂ e₂) →
  Category (suc o₁ ⊔ suc ℓ₁ ⊔ suc e₁ ⊔ suc o₂ ⊔ suc ℓ₂ ⊔ suc e₂) (suc o₁ ⊔ suc ℓ₁ ⊔ suc e₁ ⊔ suc o₂ ⊔ suc ℓ₂ ⊔ suc e₂) (o₁ ⊔ e₂)
[ ℂ ,, 𝔻 ] =
  record
    { Obj = Functor ℂ 𝔻
    ; _⇒_ = λ F G → NatTrans F G
    ; _∘_ = λ {F} {G} {H} α β → α ∘NT β
    ; _≈_ = λ α β →
      ∀ x → NatTrans.component α x ≈ NatTrans.component β x
    ; equiv =
            record
            { refl = λ x → refl
            ; sym = λ f x → sym (f x)
            ; trans = λ f g x → trans (f x) (g x)
            }
    ; ∘-resp-≈ = λ f g x → ∘-resp-≈ (f x) (g x)
    ; id = record { component = λ x → Category.id 𝔻 ; natural = λ f → trans left-id (sym right-id) }
    ; left-id = λ x → left-id
    ; right-id = λ x → right-id
    ; ∘-assoc = λ x → ∘-assoc
    }
    where
    open Category.Category 𝔻
    open CatBasics 𝔻

Iso′ : ∀ {o ℓ e} (ℂ : Category o ℓ e) →
  (A B : Category.Obj ℂ) →
  Set (ℓ ⊔ e)
Iso′ {_} {_} {_} ℂ A B =
  Σ (A ⇒[ ℂ ] B) λ f →
  Σ (B ⇒[ ℂ ] A) λ g →
      ((f ∘[ ℂ ] g) ≈[ ℂ ] Category.id ℂ)
        ×
      ((g ∘[ ℂ ] f) ≈[ ℂ ] Category.id ℂ)


syntax Iso′ ℂ A B = A ≅[ ℂ ] B



variable o : Level
variable ℓ : Level
variable e : Level

module CategoryProperties
  (ℂ : Category o ℓ e)
  where

  open Category.Category ℂ
  open CatBasics ℂ


  Σ![_⇒_] : ∀ {m : Level} → ∀ A B → (k : (A ⇒ B) → Set m) → Set (ℓ ⊔ m ⊔ e)
  Σ![ A ⇒ B ] P =
    Σ (A ⇒ B) λ m →
      P m ×
        ∀ (n : A ⇒ B) → P n → n ≈ m

  -- Σ![[_]] : 

  IsTerminal : ∀ (T : Obj) → Set (o ⊔ ℓ ⊔ e)
  IsTerminal T = ∀ A → Σ![ A ⇒ T ] λ _ → Lift ℓ ⊤
  -- IsTerminal T = ∀ {A} {f g : A ⇒ T} → f ≈ g

  IsInitial : ∀ (I : Obj) → Set (o ⊔ ℓ ⊔ e)
  IsInitial I = ∀ B → Σ![ I ⇒ B ] λ _ → Lift ℓ ⊤
  -- IsInitial I = ∀ {B} {f g : I ⇒ B} → f ≈ g

  𝟙-map : ∀ {𝟙} → IsTerminal 𝟙 → ∀ {A} → (A ⇒ 𝟙)
  𝟙-map prf {A} = proj₁ (prf A)

  𝟘-map : ∀ {𝟘} → IsInitial 𝟘 → ∀ {A} → (𝟘 ⇒ A)
  𝟘-map prf {A} = proj₁ (prf A)

  IsProduct : ∀ A B A×B → Set (o ⊔ ℓ ⊔ e)
  IsProduct A B A×B =
    ∃[ p ] ∃[ q ] (∀ {X} (f : X ⇒ A) (g : X ⇒ B) →
                Σ![ X ⇒ A×B ] λ m → Lift e (f ≈ (p ∘ m)) × (g ≈ (q ∘ m)))

  product-proj₁ : ∀ {A B A×B} →
    IsProduct A B A×B →
    (A×B) ⇒ A
  product-proj₁ (p , _) = p

  product-proj₂ : ∀ {A B A×B} →
    IsProduct A B A×B →
    (A×B) ⇒ B
  product-proj₂ (_ , q , _) = q


  IsCoproduct : ∀ A B A+B → Set (o ⊔ ℓ ⊔ e)
  IsCoproduct A B A+B =
    ∃[ i ] ∃[ j ] (∀ {X} (f : A ⇒ X) (g : B ⇒ X) →
                Σ![ A+B ⇒ X ] λ m → Lift e (f ≈ (m ∘ i)) × (g ≈ (m ∘ j)))

  coproduct-inj₁ : ∀ {A B A+B} →
    IsCoproduct A B A+B →
    A ⇒ (A+B)
  coproduct-inj₁ (i , _) = i

  coproduct-inj₂ : ∀ {A B A+B} →
    IsCoproduct A B A+B →
    B ⇒ (A+B)
  coproduct-inj₂ (_ , j , _) = j

  IsSeparator : ∀ (S : Obj) → Set (o ⊔ ℓ ⊔ e)
  IsSeparator S = ∀ {X Y} {f₁ f₂ : X ⇒ Y} →
    ((∀ (x : S ⇒ X) → (f₁ ∘ x) ≈ (f₂ ∘ x))) → f₁ ≈ f₂

  IsCoseparator : ∀ (V : Obj) → Set (o ⊔ ℓ ⊔ e)
  IsCoseparator V = ∀ {T A} {a₀ a₁ : T ⇒ A} →
    ((∀ (φ : A ⇒ V) → (φ ∘ a₀) ≈ (φ ∘ a₁))) → a₀ ≈ a₁

  Coseparate-contra : ∀ {V : Obj} → IsCoseparator V →
    ∀ {T} {A} {a₀ a₁ : T ⇒ A} →
    ¬ (a₀ ≈ a₁) → ¬ (∀ (φ : A ⇒ V) → (φ ∘ a₀) ≈ (φ ∘ a₁))
  Coseparate-contra cosep {T} {A} {a₀} {a₁} ref prf = ref (cosep prf)

  Monic : ∀ {A B} → (A ⇒ B) → Set (o ⊔ ℓ ⊔ e)
  Monic {A} {B} f =
    ∀ X (g₁ g₂ : X ⇒ A) →
      ((f ∘ g₁) ≈ (f ∘ g₂)) → (g₁ ≈ g₂)

  Epic : ∀ {A B} → (A ⇒ B) → Set (o ⊔ ℓ ⊔ e)
  Epic {A} {B} f =
    ∀ Y (g₁ g₂ : B ⇒ Y) →
      ((g₁ ∘ f) ≈ (g₂ ∘ f)) → (g₁ ≈ g₂)

  _↣_ : ∀ (A B : Obj) → Set (o ⊔ ℓ ⊔ e)
  A ↣ B = Σ (A ⇒ B) Monic

  _↠_ : ∀ (A B : Obj) → Set (o ⊔ ℓ ⊔ e)
  A ↠ B = Σ (A ⇒ B) Epic

  Retraction : ∀ {A B} (i : A ⇒ B) (r : B ⇒ A) → Set e
  Retraction {A} {B} i r = (r ∘ i) ≈ id {A}

  Retract : ∀ (A B : Obj) → Set (ℓ ⊔ e)
  Retract A B = ∃[ i ] ∃[ r ] (Retraction {A} {B} i r)

  !Retract : ∀ (A B : Obj) → Set (ℓ ⊔ e)
  !Retract A B =
    ∃[ i ] ∃[ r ]
      (Retraction {A} {B} i r
        ×
        ((i′ : A ⇒ B) → (r′ : B ⇒ A) → (Retraction i′ r′) →
          (i′ ≈ i) × (r′ ≈ r)))


  ∃_[_,,_]_ : ∀ {m} (R : ∀ X Y → Set m) (A B : Obj) →
    (P : R A B → Set m) → Set m
  ∃ R [ A ,, B ] P =
    Σ (R A B) P

  𝟙⇒𝟙-is-id : ∀ {𝟙} → IsTerminal 𝟙 → (f : 𝟙 ⇒ 𝟙) → f ≈ id
  𝟙⇒𝟙-is-id {𝟙} 𝟙-terminal f with 𝟙-terminal 𝟙
  ... | fst , fst₁ , snd =
          let eq1 = snd f (lift tt)
              eq2 = snd id (lift tt)
          in
          trans eq1 (sym eq2)

  𝟘⇒𝟘-is-id : ∀ {𝟘} → IsInitial 𝟘 → (f : 𝟘 ⇒ 𝟘) → f ≈ id
  𝟘⇒𝟘-is-id {𝟘} 𝟘-initial f with 𝟘-initial 𝟘
  ... | fst , fst₁ , snd =
          let eq1 = snd f (lift tt)
              eq2 = snd id (lift tt)
          in
          trans eq1 (sym eq2)

  𝟙-map-unique : ∀ {𝟙} → (𝟙-terminal : IsTerminal 𝟙) →
    ∀ {A} →
    {f g : A ⇒ 𝟙} →
    f ≈ 𝟙-map 𝟙-terminal {A}
  𝟙-map-unique 𝟙-terminal {A} {f} with 𝟙-terminal A
  ... | x , y , z = z f (lift tt)

  𝟘-map-unique : ∀ {𝟘} → (𝟘-initial : IsInitial 𝟘) →
    ∀ {A} →
    {f : 𝟘 ⇒ A} →
    f ≈ 𝟘-map 𝟘-initial {A}
  𝟘-map-unique 𝟘-initial {A} {f} with 𝟘-initial A
  ... | x , y , z = z f (lift tt)

  𝟙-maps-same : ∀ {𝟙} → (𝟙-terminal : IsTerminal 𝟙) →
    ∀ {A} →
    {f g : A ⇒ 𝟙} →
    f ≈ g
  𝟙-maps-same {𝟙} 𝟙-terminal {A} {f} {g} with 𝟙-terminal A
  ... | x , y , z =
    let
      p = z f (lift tt)
      q = z g (lift tt)
    in
    trans p (sym q)
    -- let -- TODO: Why is this yellow?
    --   p = 𝟙-map-unique {𝟙}  𝟙-terminal {A} {f}
    --   -- q : g ≈ 𝟙-map 𝟙-terminal {A}
    --   q = 𝟙-map-unique {𝟙} 𝟙-terminal {A} {g}
    -- in
    -- trans p (sym q)

  𝟘-maps-same : ∀ {𝟘} → (𝟘-initial : IsInitial 𝟘) →
    ∀ {A} →
    {f g : 𝟘 ⇒ A} →
    f ≈ g
  𝟘-maps-same {𝟘} 𝟘-initial {A} {f} {g} with 𝟘-initial A
  ... | x , y , z =
    let
      p = z f (lift tt)
      q = z g (lift tt)
    in
    trans p (sym q)

  Iso : ∀ {A B} (f : A ⇒ B) (g : B ⇒ A) → Set e
  Iso f g = Retraction f g × Retraction g f

  !Iso : ∀ {A B} (f : A ⇒ B) (g : B ⇒ A) → Set (ℓ ⊔ e)
  !Iso {A} {B} f g =
    Iso f g × ((f′ : A ⇒ B) → (g′ : B ⇒ A) → (Iso {A} {B} f′ g′) →
      ((f′ ≈ f) × (g′ ≈ g)))

  _≅_ : ∀ (A B : Obj) → Set (ℓ ⊔ e)
  A ≅ B = ∃[ f ] ∃[ g ] (Iso {A} {B} f g)

  Is-Iso : ∀ (A B : Obj) → Set (ℓ ⊔ e)
  Is-Iso A B = A ≅ B

  Is-!Iso : ∀ (A B : Obj) → Set (ℓ ⊔ e)
  Is-!Iso A B = ∃[ f ] ∃[ g ] !Iso {A} {B} f g

  ΣIso[_⇒_]_ : ∀ A B → (∀ f g → Iso {A} {B} f g → Set (ℓ ⊔ e)) → Set (ℓ ⊔ e)
  ΣIso[ A ⇒ B ] P =
    ∃[ f ] ∃[ g ] (Σ (Iso f g) (P f g))

  Σ!Iso[_⇒_] : ∀ A B → (∀ f g → Iso {A} {B} f g → Set (ℓ ⊔ e)) → Set (ℓ ⊔ e)
  Σ!Iso[ A ⇒ B ] P =
    ΣIso[ A ⇒ B ] λ f g i →
      ∀ f′ g′ →
      Iso f′ g′ →
      (f′ ≈ f) × (g′ ≈ g)

  Strict-Initial : ∀ {𝟘 : Obj} →
    IsInitial 𝟘 →
    Set (o ⊔ ℓ ⊔ e)
  Strict-Initial {𝟘} 𝟘-initial =
    ∀ {A} (f : A ⇒ 𝟘) →
    Iso f (𝟘-map 𝟘-initial)

  Nondegenerate : ∀ {𝟙 𝟘 : Obj} → IsTerminal 𝟙 → IsInitial 𝟘 → Set (ℓ ⊔ e)
  Nondegenerate {𝟙} {𝟘} _ _ = ¬ (𝟙 ≅ 𝟘)

  Nondegenerate′ : ∀ {𝟙 : Obj} → IsTerminal 𝟙 → Set (o ⊔ ℓ ⊔ e)
  Nondegenerate′ {𝟙} _ = ¬ IsInitial 𝟙

  Nondegenerate→no-𝟙⇒𝟘 : ∀ {𝟙 𝟘 : Obj} →
    (𝟙-terminal : IsTerminal 𝟙) →
    (𝟘-initial : IsInitial 𝟘) →
    Nondegenerate 𝟙-terminal 𝟘-initial →
    ¬ (𝟙 ⇒ 𝟘)
  Nondegenerate→no-𝟙⇒𝟘 {𝟙} {𝟘} 𝟙-terminal 𝟘-initial nondegen 𝟙⇒𝟘 =
    let
      p : 𝟙 ⇒ 𝟙
      p = 𝟙-map 𝟙-terminal ∘ 𝟙⇒𝟘

      q : 𝟘 ⇒ 𝟘
      q = 𝟙⇒𝟘 ∘ 𝟙-map 𝟙-terminal

      eq1 : p ≈ id
      eq1 = 𝟙⇒𝟙-is-id 𝟙-terminal p

      eq2 : q ≈ id
      eq2 = 𝟘⇒𝟘-is-id 𝟘-initial q
    in
    nondegen (𝟙⇒𝟘 , (𝟙-map 𝟙-terminal , (eq1 , eq2)))

  -- unique-retract→iso : ∀ {A B} →
  --   !Retract A B →
  --   A ≅ B
  -- unique-retract→iso {A} {B} !retract =
  --   let
  --     retract , unique = !retract
  --   in
  --   {!!}

  retract-retract→iso : ∀ {A} {B} {f g h} →
    Retraction {A} {B} f g →
    Retraction {B} {A} g h →
    A ≅ B
  retract-retract→iso {A} {B} {f} {g} {h} retract-f-g retract-g-h =
    let
      z : (g ∘ f) ≈ id
      z = retract-f-g

      w : (h ∘ g) ≈ id
      w = retract-g-h

      r1 : (f ∘ g) ≈ ((h ∘ g) ∘ (f ∘ g))
      r1 = trans (sym left-id) (postcomp-≈ (sym retract-g-h))

      r2′ : ((h ∘ g) ∘ f) ≈ (h ∘ (g ∘ f))
      r2′ = ∘-assoc

      r2′′ : ((h ∘ g) ∘ (f ∘ g)) ≈ (h ∘ ((g ∘ f) ∘ g))
      r2′′ = trans ∘-assoc4 (∘-resp-≈ refl (sym ∘-assoc))

      r2 : (f ∘ g) ≈ (h ∘ ((g ∘ f) ∘ g))
      r2 = trans r1 r2′′

      r3′ : (h ∘ ((g ∘ f) ∘ g)) ≈ ((h ∘ (g ∘ f)) ∘ g)
      r3′ = sym ∘-assoc

      r3′′ : (f ∘ g) ≈ ((h ∘ (g ∘ f)) ∘ g)
      r3′′ = trans r2 r3′

      hgfg≈g : ((h ∘ (g ∘ f)) ∘ g) ≈ (h ∘ g)
      hgfg≈g = rewrite-left-∘ (rewrite-right-∘ retract-f-g refl) (rewrite-left-∘ (sym right-id) refl)

      r3 : (f ∘ g) ≈ (h ∘ g)
      r3 = trans r3′′ (rewrite-right-∘ refl hgfg≈g)

      r : (f ∘ g) ≈ id
      r = trans r3 retract-g-h
    in
    f , g , retract-f-g , r

  --      p2
  --    P -> B
  -- p1 |    | g
  --    v    v
  --    A -> X
  --      f

  CSquare : ∀ {A B X P} (f : A ⇒ X) (g : B ⇒ X)
    (p₁ : P ⇒ A) (p₂ : P ⇒ B) → Set e
  CSquare f g p₁ p₂ =
    (f ∘ p₁) ≈ (g ∘ p₂)

  IsPullback : ∀ A B X (f : A ⇒ X) (g : B ⇒ X) →
    (P : Obj) → (P ⇒ A) → (P ⇒ B) → Set (o ⊔ ℓ ⊔ e)
  IsPullback A B X f g P p₁ p₂ =
    CSquare f g p₁ p₂ ×
      ∀ Z f′ g′ p₁′ p₂′ →
      CSquare {A} {B} {X} {Z} f′ g′ p₁′ p₂′ →
      (Σ![ Z ⇒ P ] λ m →
        ((p₁ ∘ m) ≈ p₁′)
          ×
        ((p₂ ∘ m) ≈ p₂′))


  --      !
  --   A --> 𝟙
  --   v     |
  -- f |     | true
  --   v     v
  --   B --> Ω
  --      χ

  Subobj-Classify : ∀ {𝟙 Ω} → (𝟙-term : IsTerminal 𝟙) →
    (tr : 𝟙 ⇒ Ω) → Set (o ⊔ ℓ ⊔ e)
  Subobj-Classify {𝟙} {Ω} 𝟙-term tr =
    ∀ {A B} {f : A ⇒ B} → Monic f →
    Σ![ B ⇒ Ω ] λ χ →
      IsPullback B 𝟙 Ω χ tr A f (𝟙-map 𝟙-term {A})
  


  Boolean : ∀ {𝟙} → (𝟙-term : IsTerminal 𝟙) →
    ∀ {Ω} → (tr : 𝟙 ⇒ Ω) → Subobj-Classify 𝟙-term tr →
    ∀ {𝟙+𝟙 : Obj} → IsCoproduct 𝟙 𝟙 𝟙+𝟙 →
    Set (ℓ ⊔ e)
  Boolean {_} _ {Ω} _ _ {𝟙+𝟙} _ = Ω ≅ 𝟙+𝟙

  Terminal-unique-Iso : ∀ {A} →
    IsTerminal A →
    ∀ {X} → IsTerminal X →
    Σ!Iso[ X ⇒ A ] (λ _ _ _ → Lift (ℓ ⊔ e) ⊤)
  Terminal-unique-Iso {A} A-term {X} X-term with A-term X in eq₁ | X-term A in eq₂
  ... | fst , fst₂ , snd | fst₁ , fst₃ , snd₁ =
    let
      s₁ , s₂ , s₃ = A-term A
      t₁ , t₂ , t₃ = X-term X

      m = t₃ (proj₁ (X-term A) ∘ proj₁ (A-term X)) (lift tt)
      m′ = t₃ id (lift tt)

      n = s₃ (proj₁ (A-term X) ∘ proj₁ (X-term A)) (lift tt)
      n′ = s₃ id (lift tt)

      z : (proj₁ (X-term A) ∘ proj₁ (A-term X)) ≈ id {X}
      z = trans m (sym m′)

      w : (proj₁ (A-term X) ∘ proj₁ (X-term A) ) ≈ id {A}
      w = trans n (sym n′)
    in
    proj₁ (A-term X) ,
    proj₁ (X-term A) ,
    (z , w) ,
    λ f′ g′ x → proj₂ (proj₂ (A-term X)) f′ (lift tt) ,
    proj₂ (proj₂ (X-term A)) g′ (lift tt)

  point-monic : ∀ {𝟙} → IsTerminal 𝟙 →
    ∀ {A} →
    (f : 𝟙 ⇒ A) →
    Monic f
  point-monic prf {A} f X g h eq with prf X
  ... | fst , fst₁ , snd =
    let p = snd g (lift tt)
        q = snd h (lift tt)
    in
    trans p (sym q)

  bimap :
    (_⊗_ : Obj → Obj → Obj) →
    (∀ X Y → IsProduct X Y (X ⊗ Y)) →
    ∀ {A A′ B B′} (f : A ⇒ A′) (g : B ⇒ B′) →
    (A ⊗ B) ⇒ (A′ ⊗ B′)
  bimap _⊗_ product {A} {A′} {B} {B′} f g =
    let
      p₁ : (A ⊗ B) ⇒ A
      p₁ = product-proj₁ (product A B)

      p₂ : (A ⊗ B) ⇒ B
      p₂ = product-proj₂ (product A B)

      s : (A ⊗ B) ⇒ A′
      s = f ∘ p₁

      t : (A ⊗ B) ⇒ B′
      t = g ∘ p₂

      _ , _ , pair-map = product A′ B′

      m , _ , _ = pair-map {A ⊗ B} s t
    in
    m

  diagonal :
    (_⊗_ : Obj → Obj → Obj) →
    (∀ X Y → IsProduct X Y (X ⊗ Y)) →
    ∀ {A} →
    A ⇒ (A ⊗ A)
  diagonal _⊗_ product {A} with product A A
  ... | x , y , z =
    let t1 , t2 = z {A} id id
    in
    t1

  joined-bimap :
    (_⊗_ : Obj → Obj → Obj) →
    (∀ X Y → IsProduct X Y (X ⊗ Y)) →
    ∀ {Z A B} (f : Z ⇒ A) (g : Z ⇒ B) →
    Z ⇒ (A ⊗ B)
  joined-bimap _⊗_ product f g =
    bimap _⊗_ product f g ∘ diagonal _⊗_ product

  IsExponential : ∀ {A B : Obj} →
    (_⊗_ : Obj → Obj → Obj) →
    (∀ X Y → IsProduct X Y (X ⊗ Y)) →
    (A⟶B : Obj) →
    (ev : (A⟶B ⊗ A) ⇒ B) →
    Set (o ⊔ ℓ ⊔ e)
  IsExponential {A} {B} _⊗_ product A⟶B ev =
    ∀ Z (e : (Z ⊗ A) ⇒ B) →
      Σ![ Z ⇒ A⟶B ] λ u →
        (ev ∘ bimap _⊗_ product u (id {A}))
          ≈
        e

  -- Natural numbers object
  IsNNO : ∀ {𝟙 ℕ} →
    (𝟙-terminal : IsTerminal 𝟙)
    (z : 𝟙 ⇒ ℕ) →
    (s : ℕ ⇒ ℕ) →
    Set (o ⊔ ℓ ⊔ e)
  IsNNO {𝟙} {ℕ} 𝟙-terminal z s =
    ∀ {A} →
      (q : 𝟙 ⇒ A) →
      (f : A ⇒ A) →
      Σ![ ℕ ⇒ A ] λ u →
        ((u ∘ (s ∘ z)) ≈ (f ∘ q))
          ×
        ((u ∘ z) ≈ q)

  -- 𝟘⇒-Monic : ∀ {𝟘 𝟙 : Obj} →
  --   (𝟘-initial : IsInitial 𝟘) →
  --   (𝟙-terminal : IsTerminal 𝟙) →
  --   ∀ {A} →
  --   (f : 𝟘 ⇒ A) →
  --   Nondegenerate 𝟙-terminal 𝟘-initial →
  --   Monic f
  -- 𝟘⇒-Monic {𝟘} 𝟘-initial 𝟙-terminal {A} f nondegen X g₁ g₂ x =
  --   {!!}

  -- A⇒𝟘-is-𝟘 : ∀ {𝟘 : Obj} → (𝟘-initial : IsInitial 𝟘) →
  --   ∀ {A : Obj} →
  --   (A ⇒ 𝟘) →
  --   A ≅ 𝟘
  -- A⇒𝟘-is-𝟘 {𝟘} 𝟘-initial {A} A⇒𝟘 =
  --   let
  --     r , s , t = 𝟘-initial 𝟘


  --     𝟘⇒A = 𝟘-map 𝟘-initial {A}
  --     -- p = 𝟘⇒A ∘ A⇒𝟘
  --     p = A⇒𝟘 ∘ 𝟘⇒A

  --     t′ : (A⇒𝟘 ∘ 𝟘-map 𝟘-initial) ≈ proj₁ (𝟘-initial 𝟘)
  --     t′ = t p (lift tt)

  --     w : proj₁ (𝟘-initial 𝟘) ≈ id
  --     w = sym (t id (lift tt))

  --     q : p ≈ id
  --     q = trans t′ w


  --     p′ : A ⇒ A
  --     p′ = 𝟘⇒A ∘ A⇒𝟘
  --     p2 = A⇒𝟘 ∘ ((𝟘⇒A ∘ A⇒𝟘) ∘ 𝟘⇒A)

  --     --     f
  --     --   A -> 0
  --     -- f |    | !
  --     --   v    v
  --     --   0 -> A
  --     --     !

  --     sq : CSquare 𝟘⇒A 𝟘⇒A A⇒𝟘 A⇒𝟘
  --     sq = refl

  --     -- 0
  --     --  ↘
  --     --   A -> 0
  --     --   |    | !
  --     --   v    v
  --     --   0 -> A
  --     --     !

  --     r′ , s′ , t-A = 𝟘-initial A

  --     -- t-A′ = t-A 𝟘⇒A (lift tt)

  --     -- t′′ : (𝟘-map 𝟘-initial ∘ A⇒𝟘) ≈ id
  --     -- t′′ = {!t-A!}

  --     -- t′′ : 

  --     q′ : p′ ≈ id
  --     q′ = {!!}

  --     w' : A ⇒ 𝟘
  --     w' = (A⇒𝟘 ∘ 𝟘⇒A) ∘ A⇒𝟘

  --     composite = (((A⇒𝟘 ∘ 𝟘⇒A) ∘ A⇒𝟘) ∘ ((𝟘⇒A ∘ A⇒𝟘) ∘ 𝟘⇒A))


  --     eq' : (((A⇒𝟘 ∘ 𝟘⇒A) ∘ A⇒𝟘) ∘ ((𝟘⇒A ∘ A⇒𝟘) ∘ 𝟘⇒A)) ≈ id
  --     eq' = trans (t composite (lift tt)) w

  --     -- eq'' : (((𝟘⇒A ∘ A⇒𝟘) ∘ 𝟘⇒A) ∘ ((A⇒𝟘 ∘ 𝟘⇒A) ∘ A⇒𝟘)) ≈ id
  --     -- eq'' = trans {!t′!} {!!}
  --   in
  --   (A⇒𝟘 ∘ 𝟘⇒A) ∘ A⇒𝟘 ,
  --   (𝟘⇒A ∘ A⇒𝟘) ∘ 𝟘⇒A ,
  --   {!!} ,
  --   {!!}
  --   -- A⇒𝟘 , 𝟘⇒A , q′ , q

  -- 𝟘⇒𝟘-monic : ∀ {𝟘} → (𝟘-initial : IsInitial 𝟘) →
  --   Monic (𝟘-map 𝟘-initial {𝟘})
  -- 𝟘⇒𝟘-monic 𝟘-initial X g₁ g₂ x = {!!}


  -- -- initial-monic :
