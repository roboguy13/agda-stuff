-- Partially based on "Formalizing Category Theory in Agda" (Hu and Carette, 2020)

open import Relation.Binary.Structures
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.HeterogeneousEquality hiding (cong; cong₂) renaming (_≅_ to _H≅_; trans to H-trans; sym to H-sym; subst to H-subst; Extensionality to H-Extensionality)
open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs.WithK

open import Level

module Category
  where

private postulate fun-ext : ∀ {m n} → Extensionality m n

record Category (o ℓ : Level) : Set (lsuc (o ⊔ ℓ)) where
  infixr 9 _∘_
  field
    Obj : Set o
    _⇒_ : Obj → Obj → Set ℓ
    _∘′_ : ∀ A B C → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)


    id′ : ∀ A → (A ⇒ A)

  id : ∀ {A} → (A ⇒ A)
  id = id′ _
  _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
  _∘_ = _∘′_ _ _ _

  field
    left-id : ∀ {A B} → ∀ {f : A ⇒ B} → (id ∘ f) ≡ f
    right-id : ∀ {A B} → ∀ {f : A ⇒ B} → (f ∘ id) ≡ f
    ∘-assoc : ∀ {A B C D} → ∀ {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
                    ((f ∘ g) ∘ h) ≡ (f ∘ (g ∘ h))

-- Category-η : ∀ {o ℓ} {ℂ 𝔻 : Category o ℓ} →
--   Category.Obj ℂ ≡ Category.Obj 𝔻 →
--   Category._⇒_ ℂ H≅ Category._⇒_ 𝔻 →
--   Category._∘′_ ℂ H≅ Category._∘′_ 𝔻 →
--   Category.id′ ℂ H≅ Category.id′ 𝔻 →
--   ℂ ≡ 𝔻
-- Category-η {o} {ℓ} {ℂ} {𝔻} refl refl refl refl
--   with fun-ext (λ x → fun-ext λ y → uip (Category.left-id ℂ {x} {y}) (Category.left-id 𝔻 {x} {y}))
-- ... | p = {!!}

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
