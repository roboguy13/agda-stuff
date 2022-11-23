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

module CategoryRecord
  where

record Category (o ℓ e : Level) : Set (lsuc (o ⊔ ℓ ⊔ e)) where
  field
    Obj : Set o
    _⇒_ : Obj → Obj → Set ℓ
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
    _≈_ : ∀ {A B} → (f g : A ⇒ B) → Set e
    equiv : ∀ {A B} → IsEquivalence (λ x y → (_≈_ {A} {B} x y))
    ∘-resp-≈ : ∀ {A B C} → {f h : B ⇒ C} {g i : A ⇒ B} →
                    (f ≈ h) → (g ≈ i) → ((f ∘ g) ≈ (h ∘ i))

    id : ∀ {A} → (A ⇒ A)
    left-id : ∀ {A B} → ∀ {f : A ⇒ B} → (id ∘ f) ≈ f
    right-id : ∀ {A B} → ∀ {f : A ⇒ B} → (f ∘ id) ≈ f
    ∘-assoc : ∀ {A B C D} → ∀ {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
                    ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))

≡-IsEquivalence : ∀ {m} {A : Set m} → IsEquivalence {_} {m} {A} _≡_
≡-IsEquivalence = record { refl = _≡_.refl ; sym = Relation.Binary.PropositionalEquality.sym ; trans = Relation.Binary.PropositionalEquality.trans }

record Eq-Category (o ℓ : Level) : Set (suc (o ⊔ ℓ)) where
  field
    Obj : Set o
    _⇒_ : Obj → Obj → Set ℓ
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

    id : ∀ {A} → (A ⇒ A)
    left-id : ∀ {A B} → ∀ {f : A ⇒ B} → (id ∘ f) ≡ f
    right-id : ∀ {A B} → ∀ {f : A ⇒ B} → (f ∘ id) ≡ f
    ∘-assoc : ∀ {A B C D} → ∀ {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
                    ((f ∘ g) ∘ h) ≡ (f ∘ (g ∘ h))

Cat : ∀ {o ℓ} → Eq-Category o ℓ → Category o ℓ ℓ
Cat record { Obj = Obj ; _⇒_ = _⇒_ ; _∘_ = _∘_ ; id = id ; left-id = left-id ; right-id = right-id ; ∘-assoc = ∘-assoc } =
  record
    { Obj = Obj
    ; _⇒_ = _⇒_
    ; _∘_ = _∘_
    ; _≈_ = _≡_
    ; equiv = ≡-IsEquivalence
    ; ∘-resp-≈ = λ {_} {_} {_} {f} {h} {g} {i} prf-1 prf-2 →
        subst (λ z → (f ∘ z) ≡ (h ∘ i)) (Relation.Binary.PropositionalEquality.sym prf-2)
          (subst (λ z → (z ∘ i) ≡ (h ∘ i)) (Relation.Binary.PropositionalEquality.sym prf-1) _≡_.refl)
    ; id = id
    ; left-id = left-id
    ; right-id = right-id
    ; ∘-assoc = ∘-assoc
    }

-- Mk-Eq-Category : ∀ {o ℓ} →
--   (Obj : Set o) →
--   (_⇒_ : Obj → Obj → Set ℓ) →
--   (_∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)) →
--   (id : ∀ {A} → (A ⇒ A)) →
--   (left-id : ∀ {A B} → ∀ (f : A ⇒ B) → (id ∘ f) ≡ f) →
--   (right-id : ∀ {A B} → ∀ {f : A ⇒ B} → (f ∘ id) ≡ f) →
--   (∘-assoc : ∀ {A B C D} → ∀ {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
--                     ((f ∘ g) ∘ h) ≡ (f ∘ (g ∘ h))) →
--   Category o ℓ ℓ
-- Mk-Eq-Category Obj _⇒_ _∘_ id left-id right-id ∘-assoc =
--   record
--     { Obj = Obj
--     ; _⇒_ = _⇒_
--     ; _∘_ = _∘_
--     ; _≈_ = _≡_
--     ; equiv = ≡-IsEquivalence
--     ; ∘-resp-≈ = λ {_} {_} {_} {f} {h} {g} {i} prf-1 prf-2 →
--         subst (λ z → (f ∘ z) ≡ (h ∘ i)) (sym prf-2)
--           (subst (λ z → (z ∘ i) ≡ (h ∘ i)) (sym prf-1) refl)
--     ; id = id
--     ; left-id = left-id
--     ; right-id = right-id
--     ; ∘-assoc = ∘-assoc
--     }

-- Eq-Category : 

Arr : ∀ {o ℓ e} (ℂ : Category o ℓ e) → Category.Obj ℂ → Category.Obj ℂ → Set ℓ
Arr = Category._⇒_

Arr' : ∀ {o ℓ e} {ℂ : Category o ℓ e} → Category.Obj ℂ → Category.Obj ℂ → Set ℓ
Arr' {_} {_} {_} {ℂ} = Category._⇒_ ℂ

syntax Arr C x y = x ⇒[ C ] y
syntax Arr' x y = x ⇒' y

comp : ∀ {o ℓ e} (ℂ : Category o ℓ e) → ∀ {A B C} → (B ⇒[ ℂ ] C) → (A ⇒[ ℂ ] B) → (A ⇒[ ℂ ] C)
comp = Category._∘_

comp' : ∀ {o ℓ e} {ℂ : Category o ℓ e} → ∀ {A B C} → (B ⇒[ ℂ ] C) → (A ⇒[ ℂ ] B) → (A ⇒[ ℂ ] C)
comp' {_} {_} {_} {ℂ} = Category._∘_ ℂ

syntax comp ℂ f g = f ∘[ ℂ ] g
syntax comp' f g = f ∘' g

Equiv : ∀ {o ℓ e} (ℂ : Category o ℓ e) → ∀ {A B} → (f g : A ⇒[ ℂ ] B) → Set e
Equiv = Category._≈_

Equiv' : ∀ {o ℓ e} {ℂ : Category o ℓ e} → ∀ {A B} → (f g : A ⇒[ ℂ ] B) → Set e
Equiv' {_} {_} {_} {ℂ} = Category._≈_ ℂ

syntax Equiv ℂ f g = f ≈[ ℂ ] g
syntax Equiv' f g = f ≈' g

-- Cat-Congruence : ∀ {o ℓ e} → (ℂ : Category o ℓ e) → Set e
-- Cat-Congruence ℂ =
--   ∀ {A B : Category.Obj ℂ} → (f : A ⇒[ ℂ ] B) →
--                {x x′ : A} →
--                x ≈[ ℂ ] x′ →
--                f x ≈[ ℂ ] f x′

Op : ∀ {o ℓ e} → Category o ℓ e → Category o ℓ e
Op record { Obj = Obj ; _⇒_ = _⇒_ ; _∘_ = _∘_ ; _≈_ = _≈_ ; equiv = equiv ; ∘-resp-≈ = ∘-resp-≈ ; id = id ; left-id = left-id ; right-id = right-id ; ∘-assoc = ∘-assoc } =
  record
    { Obj = Obj
    ; _⇒_ = λ x y → y ⇒ x
    ; _∘_ = λ f g → g ∘ f
    ; _≈_ = _≈_
    ; equiv = equiv
    ; ∘-resp-≈ = λ z z₁ → ∘-resp-≈ z₁ z
    ; id = id
    ; left-id = λ {A} {B} {f} → right-id
    ; right-id = λ {A} {B} {f} → left-id
    ; ∘-assoc = IsEquivalence.sym equiv ∘-assoc
    }

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

actf = Functor.act

syntax actf F x = F · x

record NatTrans {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ : Level} {Src : Category o₁ ℓ₁ e₁} {Tgt : Category o₂ ℓ₂ e₂}
      (F G : Functor Src Tgt) : Set (lsuc (o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂)) where
  field
    component : ∀ {x : Category.Obj Src} →
      (F · x) ⇒[ Tgt ] (G · x)

    natural : ∀ {x y} {f : x ⇒[ Src ] y} →
      (component ∘[ Tgt ] Functor.fmap F f)
        ≈[ Tgt ]
      (Functor.fmap G f ∘[ Tgt ] component)

variable o : Level
variable ℓ : Level
variable e : Level

module CategoryProperties
  (ℂ : Category o ℓ e)
  where


  open Category ℂ

  sym : ∀ {A B : Obj} {f g : A ⇒ B} → f ≈ g → g ≈ f
  sym {A} {B} = IsEquivalence.sym (equiv {A} {B})

  trans : ∀ {A B : Obj} {f g h : A ⇒ B} →
    f ≈ g →
    g ≈ h →
    f ≈ h
  trans {A} {B} = IsEquivalence.trans (equiv {A} {B})

  refl : ∀ {A B : Obj} {f : A ⇒ B} → f ≈ f

  refl {A} {B} {f} = IsEquivalence.refl (equiv {A} {B})

  postcomp-≈ : ∀ {A B C : Obj}
    {f g : B ⇒ C} →
    {h : A ⇒ B} →
    f ≈ g →
    (f ∘ h) ≈ (g ∘ h)
  postcomp-≈ {_} {_} {_} {ℂ} prf =
    ∘-resp-≈ prf refl

  precomp-≈ : ∀ {A B C : Obj}
    {f g : A ⇒ B} →
    {h : B ⇒ C} →
    f ≈ g →
    (h ∘ f) ≈ (h ∘ g)
  precomp-≈ {_} {_} {_} {ℂ} prf =
    ∘-resp-≈ refl prf

  ≈left-id-intro : ∀ {A B : Obj} →
    {f g : A ⇒ B} →
    {h : B ⇒ B} →
    h ≈ id →
    f ≈ g →
    (h ∘ f) ≈ g
  ≈left-id-intro prf1 prf2 = trans (∘-resp-≈ prf1 prf2) left-id

  ≈left-id-elim : ∀ {A B : Obj} →
    {f g : A ⇒ B} →
    {h : B ⇒ B} →
    h ≈ id →
    (h ∘ f) ≈ g →
    f ≈ g
  ≈left-id-elim prf1 prf2 = trans (sym left-id) (trans (∘-resp-≈ (sym prf1) refl) prf2)

  ≈right-id-elim : ∀ {A B : Obj} →
    {f g : A ⇒ B} →
    {h : A ⇒ A} →
    h ≈ id →
    (f ∘ h) ≈ g →
    f ≈ g
  ≈right-id-elim prf1 prf2 = trans (sym right-id) (trans (∘-resp-≈ refl (sym prf1)) prf2)

  rewrite-right-∘ : ∀ {A B C : Obj}
    {f : B ⇒ C}
    {g g′ : A ⇒ B}
    {h : A ⇒ C} →
    g ≈ g′ →
    (f ∘ g) ≈ h →
    (f ∘ g′) ≈ h
  rewrite-right-∘ prf1 prf2 = trans (∘-resp-≈ refl (sym prf1)) prf2

  rewrite-left-∘ : ∀ {A B C : Obj}
    {f : A ⇒ B}
    {g g′ : B ⇒ C}
    {h : A ⇒ C} →
    g ≈ g′ →
    (g ∘ f) ≈ h →
    (g′ ∘ f) ≈ h
  rewrite-left-∘ prf1 prf2 = trans (∘-resp-≈ (sym prf1) refl) prf2


  ∘-assoc4 : ∀ {A B C D E : Obj}
    {f : A ⇒ B}
    {g : B ⇒ C}
    {h : C ⇒ D}
    {i : D ⇒ E} →
    ((i ∘ h) ∘ (g ∘ f)) ≈ (i ∘ (h ∘ (g ∘ f)))
  ∘-assoc4 {_} {_} {_} {_} {_} {f} {g} {h} {i} =
    let
      p : ((i ∘ h) ∘ (g ∘ f)) ≈ ((i ∘ h) ∘ (id ∘ (g ∘ f)))
      p = ∘-resp-≈ refl (sym left-id)

      q : ((i ∘ h) ∘ (id ∘ (g ∘ f))) ≈ (i ∘ (h ∘ (id ∘ (g ∘ f))))
      q = ∘-assoc

      w : (i ∘ (h ∘ (id ∘ (g ∘ f)))) ≈ (i ∘ (h ∘ (g ∘ f)))
      w = ∘-resp-≈ refl (∘-resp-≈ refl left-id)
    in
    trans p (trans q w)

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

  -- -- 0 -> A
  -- -- |    | id
  -- -- v    v
  -- -- A -> A
  -- --   id
  -- 𝟘-id-pullback : ∀ {𝟘 : Obj}
  --   (𝟘-initial : IsInitial 𝟘) →
  --   ∀ {A} →
  --   IsPullback A A A id id 𝟘 (𝟘-map 𝟘-initial) (𝟘-map 𝟘-initial)
  -- 𝟘-id-pullback 𝟘-initial {A} =
  --   ∘-resp-≈ refl refl ,
  --   λ Z f′ g′ p₁′ p₂′ x →
  --     {!!} ,
  --     ({!!} , {!!}) ,
  --     λ n x₁ → {!!}

  -- --      id
  -- --    A -> A
  -- -- id |    | f
  -- --    v    v
  -- --    A -> 0
  -- --      f
  -- 𝟘-id-pullback : ∀ {𝟘 : Obj}
  --   (𝟘-initial : IsInitial 𝟘) →
  --   ∀ {A} →
  --   (f : A ⇒ 𝟘) →
  --   IsPullback A A 𝟘 f f A id id
  -- 𝟘-id-pullback 𝟘-initial {A} f =
  --   let
  --     e : A ⇒ A
  --     e = 𝟘-map 𝟘-initial ∘ f

  --     idem : (e ∘ e) ≈ e
  --     idem = {!!}
  --   in
  --   {!!} ,
  --   λ Z f′ g′ p₁′ p₂′ x →
  --     let
  --       p1≈p2 : p₁′ ≈ p₂′
  --       p1≈p2 = {!!}
  --     in
  --     p₂′ ∘ (𝟘-map 𝟘-initial ∘ (f ∘ p₁′)) ,
  --     ({!!} , {!!}) ,
  --     λ n x₁ → {!!}


  -- --      f
  -- --    A -> B
  -- -- id |    | id
  -- --    v    v
  -- --    A -> B
  -- --      f
  -- id-pullback : ∀ {A B} →
  --   (f : A ⇒ B) →
  --   IsPullback A B B f id A id f
  -- id-pullback {A} f =
  --   trans right-id (sym left-id) ,
  --   λ Z f′ g′ p₁′ p₂′ x →
  --     {!!} , ({!!} , {!!}) , λ n x₁ → {!!}

  -- --     !
  -- --  A --> 1
  -- -- f|    !|
  -- --  v  !  v
  -- --  0 --> 1
  -- 𝟘-𝟙-pullback : ∀ {𝟙 𝟘 : Obj} →
  --   (𝟙-terminal : IsTerminal 𝟙) →
  --   (𝟘-initial : IsInitial 𝟘) →
  --   ∀ {A} →
  --   (f : A ⇒ 𝟘) →
  --   IsPullback 𝟘 𝟙 𝟙 (𝟘-map 𝟘-initial) id A f (𝟙-map 𝟙-terminal)
  -- 𝟘-𝟙-pullback {𝟙} {𝟘} 𝟙-terminal 𝟘-initial f =
  --   let
  --     g = (f ∘ 𝟘-map 𝟘-initial)
  --     eq : g ≈ id
  --     eq = 𝟘⇒𝟘-is-id 𝟘-initial g

  --   in
  --   𝟙-maps-same 𝟙-terminal ,
  --   λ Z f′ g′ p₁′ p₂′ x →
  --     -- let
  --     --   m = 𝟙-map 𝟙-terminal ∘ (𝟘-map 𝟘-initial ∘ p₁′)
  --     -- in
  --     𝟘-map 𝟘-initial ∘ p₁′ , (trans (sym ∘-assoc) (trans (rewrite-left-∘ (sym eq) left-id) refl) , 𝟙-maps-same 𝟙-terminal) , λ n x₁ → {!!}

  -- 𝟘 ∘ f ≈ id ∘ 𝟙


  -- 𝟘-𝟙-pullback : ∀ {𝟙 𝟘 : Obj} →
  --   (𝟙-terminal : IsTerminal 𝟙) →
  --   (𝟘-initial : IsInitial 𝟘) →
  --   IsPullback 𝟘 𝟘 𝟙 (𝟘-map 𝟘-initial) (𝟘-map 𝟘-initial) 𝟘 (𝟘-map 𝟘-initial) (𝟘-map 𝟘-initial)
  -- 𝟘-𝟙-pullback {𝟙} {𝟘} 𝟙-terminal 𝟘-initial =
  --   refl ,
  --   λ Z f′ g′ p₁′ p₂′ x →
  --     let
  --       -- s : 𝟘 ⇒ Z
  --       -- s = {!!}
  --       e : Z ⇒ Z
  --       e = 𝟘-map 𝟘-initial ∘ p₁′

  --       w = (f′ ∘ p₁′)

  --       eq : (f′ ∘ p₁′) ≈ (g′ ∘ p₂′)
  --       eq = x
  --     in
  --     p₁′ ∘ e , ({!!} , {!!}) , λ n x₁ → {!!}

  


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
