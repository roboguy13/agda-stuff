-- Based on "Formalizing Category Theory in Agda" (Hu and Carette, 2020)

open import Relation.Binary.Structures
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality

open import Level

module Category
  where

record Category (o ℓ : Level) : Set (lsuc (o ⊔ ℓ)) where
  infixr 9 _∘_
  field
    Obj : Set o
    _⇒_ : Obj → Obj → Set ℓ
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

    id : ∀ {A} → (A ⇒ A)
    left-id : ∀ {A B} → ∀ {f : A ⇒ B} → (id ∘ f) ≡ f
    right-id : ∀ {A B} → ∀ {f : A ⇒ B} → (f ∘ id) ≡ f
    ∘-assoc : ∀ {A B C D} → ∀ {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
                    ((f ∘ g) ∘ h) ≡ (f ∘ (g ∘ h))

Arr : ∀ {o ℓ} (ℂ : Category o ℓ) → Category.Obj ℂ → Category.Obj ℂ → Set ℓ
Arr = Category._⇒_

Arr' : ∀ {o ℓ} {ℂ : Category o ℓ} → Category.Obj ℂ → Category.Obj ℂ → Set ℓ
Arr' {_} {_}  {ℂ} = Category._⇒_ ℂ

syntax Arr C x y = x ⇒[ C ] y
syntax Arr' x y = x ⇒' y

comp : ∀ {o ℓ} (ℂ : Category o ℓ) → ∀ {A B C} → (B ⇒[ ℂ ] C) → (A ⇒[ ℂ ] B) → (A ⇒[ ℂ ] C)
comp = Category._∘_

comp' : ∀ {o ℓ} {ℂ : Category o ℓ} → ∀ {A B C} → (B ⇒[ ℂ ] C) → (A ⇒[ ℂ ] B) → (A ⇒[ ℂ ] C)
comp' {_} {_}  {ℂ} = Category._∘_ ℂ

syntax comp ℂ f g = f ∘[ ℂ ] g
syntax comp' f g = f ∘' g

-- Cat-Congruence : ∀ {o ℓ e} → (ℂ : Category o ℓ e) → Set e
-- Cat-Congruence ℂ =
--   ∀ {A B : Category.Obj ℂ} → (f : A ⇒[ ℂ ] B) →
--                {x x′ : A} →
--                x ≈[ ℂ ] x′ →
--                f x ≈[ ℂ ] f x′

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

module CatBasics
  {o ℓ : Level}
  (ℂ : Category o ℓ)
  where

  open Category ℂ

  postcomp-≡ : ∀ {A B C : Obj}
    {f g : B ⇒ C} →
    {h : A ⇒ B} →
    f ≡ g →
    (f ∘ h) ≡ (g ∘ h)
  postcomp-≡ {_} {_} {_} {ℂ} refl = refl

  precomp-≡ : ∀ {A B C : Obj}
    {f g : A ⇒ B} →
    {h : B ⇒ C} →
    f ≡ g →
    (h ∘ f) ≡ (h ∘ g)
  precomp-≡ {_} {_} {_} {ℂ} refl = refl

  ≡left-id-intro : ∀ {A B : Obj} →
    {f g : A ⇒ B} →
    {h : B ⇒ B} →
    h ≡ id →
    f ≡ g →
    (h ∘ f) ≡ g
  ≡left-id-intro refl refl = left-id

  ≡left-id-elim : ∀ {A B : Obj} →
    {f g : A ⇒ B} →
    {h : B ⇒ B} →
    h ≡ id →
    (h ∘ f) ≡ g →
    f ≡ g
  ≡left-id-elim refl refl = sym left-id

  ≡right-id-elim : ∀ {A B : Obj} →
    {f g : A ⇒ B} →
    {h : A ⇒ A} →
    h ≡ id →
    (f ∘ h) ≡ g →
    f ≡ g
  ≡right-id-elim refl refl = sym right-id

  rewrite-right-∘ : ∀ {A B C : Obj}
    {f : B ⇒ C}
    {g g′ : A ⇒ B}
    {h : A ⇒ C} →
    g ≡ g′ →
    (f ∘ g) ≡ h →
    (f ∘ g′) ≡ h
  rewrite-right-∘ refl refl = refl

  rewrite-left-∘ : ∀ {A B C : Obj}
    {f : A ⇒ B}
    {g g′ : B ⇒ C}
    {h : A ⇒ C} →
    g ≡ g′ →
    (g ∘ f) ≡ h →
    (g′ ∘ f) ≡ h
  rewrite-left-∘ refl refl = refl

  ∘-assoc4 : ∀ {A B C D E : Obj}
    {f : A ⇒ B}
    {g : B ⇒ C}
    {h : C ⇒ D}
    {i : D ⇒ E} →
    ((i ∘ h) ∘ (g ∘ f)) ≡ (i ∘ (h ∘ (g ∘ f)))
  ∘-assoc4 {_} {_} {_} {_} {_} {f} {g} {h} {i} =
    let
      p : ((i ∘ h) ∘ (g ∘ f)) ≡ ((i ∘ h) ∘ (id ∘ (g ∘ f)))
      p = sym (rewrite-right-∘ (sym left-id) refl)

      q : ((i ∘ h) ∘ (id ∘ (g ∘ f))) ≡ (i ∘ (h ∘ (id ∘ (g ∘ f))))
      q = ∘-assoc

      w : (i ∘ (h ∘ (id ∘ (g ∘ f)))) ≡ (i ∘ (h ∘ (g ∘ f)))
      w = rewrite-right-∘ (sym (rewrite-right-∘ (sym left-id) refl)) refl
    in
    trans p (trans q w)

  ∘-assoc4-mid : ∀ {A B C D E : Obj}
    {f : A ⇒ B}
    {g : B ⇒ C}
    {h : C ⇒ D}
    {i : D ⇒ E} →
    (i ∘ (h ∘ g) ∘ f) ≡ ((i ∘ h) ∘ (g ∘ f))
  ∘-assoc4-mid {_} {_} {_} {_} {_} {f} {g} {h} {i} =
    trans (rewrite-right-∘ (sym ∘-assoc) refl) (sym ∘-assoc4)

  ∘-assoc5-mid : ∀ {A B C D E U : Obj}
    {f : A ⇒ B}
    {g : B ⇒ C}
    {h : C ⇒ D}
    {i : D ⇒ E} →
    {j : E ⇒ U} →
    (j ∘ (i ∘ h ∘ g) ∘ f) ≡ ((j ∘ i) ∘ h ∘ (g ∘ f))
  ∘-assoc5-mid {_} {_} {_} {_} {_} {_} {f} {g} {h} {i} {j} =
    let
      p : (j ∘ ((i ∘ h) ∘ g) ∘ f) ≡ ((j ∘ i) ∘ h ∘ (g ∘ f))
      p = trans
            (rewrite-right-∘ (sym ∘-assoc) refl)
            (rewrite-left-∘ refl ∘-assoc4-mid)

            -- (∘-resp-≡ refl (Category.∘-assoc ℂ))
            -- (rewrite-left-∘ refl ∘-assoc4-mid)

      q : (j ∘ (i ∘ h ∘ g) ∘ f) ≡ (j ∘ ((i ∘ h) ∘ g) ∘ f)
      q = (rewrite-right-∘ (rewrite-left-∘ (sym ∘-assoc) refl) refl)
    in
    trans q p
