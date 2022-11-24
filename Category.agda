-- Based on "Formalizing Category Theory in Agda" (Hu and Carette, 2020)

open import Relation.Binary.Structures
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality hiding (refl; trans; sym)

open import Level

module Category
  where

record Category (o ℓ e : Level) : Set (lsuc (o ⊔ ℓ ⊔ e)) where
  infixr 9 _∘_
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

module CatBasics
  {e ℓ o : Level}
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

  ∘-resp-≡ : ∀ {A B C} → {f h : B ⇒ C} {g i : A ⇒ B} →
                  (f ≡ h) → (g ≡ i) → ((f ∘ g) ≡ (h ∘ i))
  ∘-resp-≡ _≡_.refl _≡_.refl = _≡_.refl

  -- rewrite-left : ∀ {A B C : Obj}
  --   {f : A ⇒ B}
  --   {g : B ⇒ C}
  --   f ≈ f′ →
  --   (g ∘ f) ≈ h →
  --   (g′ ∘ f) ≈ h


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

  ∘-assoc4-mid : ∀ {A B C D E : Obj}
    {f : A ⇒ B}
    {g : B ⇒ C}
    {h : C ⇒ D}
    {i : D ⇒ E} →
    (i ∘ (h ∘ g) ∘ f) ≈ ((i ∘ h) ∘ (g ∘ f))
  ∘-assoc4-mid {_} {_} {_} {_} {_} {f} {g} {h} {i} =
    trans (∘-resp-≈ refl (Category.∘-assoc ℂ)) (sym ∘-assoc4)

  ∘-assoc5-mid : ∀ {A B C D E U : Obj}
    {f : A ⇒ B}
    {g : B ⇒ C}
    {h : C ⇒ D}
    {i : D ⇒ E} →
    {j : E ⇒ U} →
    (j ∘ (i ∘ h ∘ g) ∘ f) ≈ ((j ∘ i) ∘ h ∘ (g ∘ f))
  ∘-assoc5-mid {_} {_} {_} {_} {_} {_} {f} {g} {h} {i} {j} =
    let
      p : (j ∘ ((i ∘ h) ∘ g) ∘ f) ≈ ((j ∘ i) ∘ h ∘ (g ∘ f))
      p = trans
            (∘-resp-≈ refl (Category.∘-assoc ℂ))
            (rewrite-left-∘ refl ∘-assoc4-mid)

      q : (j ∘ (i ∘ h ∘ g) ∘ f) ≈ (j ∘ ((i ∘ h) ∘ g) ∘ f)
      q = (rewrite-right-∘ (rewrite-left-∘ (sym ∘-assoc) refl) refl)
    in
    trans q p
