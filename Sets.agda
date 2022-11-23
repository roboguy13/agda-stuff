-- Elementary theory of the category of sets

open import CategoryRecord

open import Agda.Primitive
open import Data.Product hiding (_×_)
open import Data.Empty
open import Data.Unit

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Level

module Sets
  -- (ℂ : Category lzero (lsuc lzero) (lsuc lzero))
  (Eq-ℂ : Eq-Category lzero (lsuc lzero))
  where

ℂ : Category lzero (lsuc lzero) (lsuc lzero)
ℂ = Cat Eq-ℂ

open Category ℂ
open CategoryProperties ℂ
  renaming (𝟙-map to 𝟙-map′; 𝟘-map to 𝟘-map′)

record Sets : Set₁ where
  field
    𝟘 : Obj
    𝟙 : Obj
    𝟚 : Obj

    𝟘-initial : IsInitial 𝟘
    𝟙-terminal : IsTerminal 𝟙

    𝟙-separator : IsSeparator 𝟙
    𝟚-coseparator : IsCoseparator 𝟚

    nondegen : Nondegenerate 𝟙-terminal 𝟘-initial

    _×_ : Obj → Obj → Obj
    products : ∀ A B → IsProduct A B (A × B)

    _⊎_ : Obj → Obj → Obj
    coproducts : ∀ A B → IsCoproduct A B (A ⊎ B)

    Pullback : ∀ A B X (f : A ⇒ X) (g : B ⇒ X) →
      ∃[ P ] ∃[ p₁ ] ∃[ p₂ ] (IsPullback A B X f g P p₁ p₂)

      -- Internal hom
    _⟶_ : Obj → Obj → Obj
    ev : ∀ {A B} → (((A ⟶ B) × A) ⇒ B)
    exponentials : ∀ A B →
      IsExponential _×_ products (A ⟶ B) ev

      -- Subobject classifier
    true : 𝟙 ⇒ 𝟚
    subobj-classify : Subobj-Classify 𝟙-terminal true


      -- It's a Boolean topos
    boolean : Boolean 𝟙-terminal true subobj-classify (coproducts 𝟙 𝟙)

      -- Natural numbers object
    ℕ : Obj
    z : 𝟙 ⇒ ℕ
    s : ℕ ⇒ ℕ
    ℤ-NNO : IsNNO 𝟙-terminal z s


module SetsProperties
  (𝕍 : Sets)
  where

  open Sets 𝕍

  neg : (A : Obj) → Set₁
  neg A = A ⇒ 𝟘

  𝟙+𝟙 : Obj
  𝟙+𝟙 = 𝟙 ⊎ 𝟙

  𝟙-map : ∀ {A} → (A ⇒ 𝟙)
  𝟙-map = 𝟙-map′ 𝟙-terminal

  𝟙-map-unique : ∀ {A} → (f : A ⇒ 𝟙) → f ≈ 𝟙-map
  𝟙-map-unique {A} f with 𝟙-terminal A
  ... | fst , fst₁ , snd = snd f (lift tt)

  𝟘-map : ∀ {A} → (𝟘 ⇒ A)
  𝟘-map = 𝟘-map′ 𝟘-initial

  𝟘-map-unique : ∀ {A} → (f : 𝟘 ⇒ A) → f ≈ 𝟘-map
  𝟘-map-unique {A} f with 𝟘-initial A
  ... | fst , fst₁ , snd = snd f (lift tt)

  -- 𝟚↪𝟙+𝟙 : Σ (𝟚 ⇒ (𝟙 ⊎ 𝟙)) Monic
  -- 𝟚↪𝟙+𝟙 with coproducts 𝟙 𝟙
  -- ... | fst , fst₁ , snd =
  --   {!!} , λ g₁ g₂ x → {!!}

  -- 𝟚≅𝟙+𝟙 : 𝟚 ≅ (𝟙 ⊎ 𝟙)
  -- 𝟚≅𝟙+𝟙 =
  --   {!!} ,
  --   {!!} ,
  --   {!!} ,
  --   {!!}

  left-𝟙+𝟙 : 𝟙 ⇒ 𝟙+𝟙
  left-𝟙+𝟙 with coproducts 𝟙 𝟙
  ... | fst , z = fst

  right-𝟙+𝟙 : 𝟙 ⇒ 𝟙+𝟙
  right-𝟙+𝟙 with coproducts 𝟙 𝟙
  ... | fst , fst₁ , snd = fst₁

  left≠right : ¬ (left-𝟙+𝟙 ≈ right-𝟙+𝟙)
  left≠right prf = {!!}


  swap-𝟙+𝟙 : 𝟙+𝟙 ⇒ 𝟙+𝟙
  swap-𝟙+𝟙 with coproducts 𝟙 𝟙
  ... | fst , fst₁ , snd with snd fst₁ fst
  swap-𝟙+𝟙 | fst , fst₁ , snd | fst₂ , z = fst₂

  swap-𝟙+𝟙-not-id : ¬ (swap-𝟙+𝟙 ≈ id)
  swap-𝟙+𝟙-not-id = {!!}

  false : 𝟙 ⇒ 𝟚
  false = {!!}

  false≠true : ¬ (false ≈ true)
  false≠true = {!!}

  𝟙+𝟙-maps-not-all-same :
    ¬ (∀ (f g : 𝟙 ⇒ 𝟙+𝟙) → f ≈ g)
  𝟙+𝟙-maps-not-all-same prf with subobj-classify (point-monic 𝟙-terminal true) | subobj-classify (point-monic 𝟙-terminal false)
  ... | fst , (fst₂ , snd₂) , snd | fst₁ , (fst₃ , snd₃) , snd₁ =
    nondegen ({!!} , 𝟙-map , ({!!} , {!!}))

  has-point→non-𝟘 : ∀ {A} → (𝟙 ⇒ A) → ¬ (A ≅ 𝟘)
  has-point→non-𝟘 f (fst , fst₁ , fst₂ , snd) =
    Nondegenerate→no-𝟙⇒𝟘 𝟙-terminal 𝟘-initial nondegen (fst ∘ f)

  𝟚-maps-not-all-same :
    ¬ (∀ (f g : 𝟙 ⇒ 𝟚) → f ≈ g)
  𝟚-maps-not-all-same prf =
    nondegen ({!!} , 𝟙-map , ({!!} , {!!}))
    -- nondegen
    --   (λ B →
    --     let p = {!!}
    --     in
    --     {!!} ,
    --   {!!} ,
    --   λ n x → {!!})

  distinct-𝟚-maps :
    Σ (𝟙 ⇒ 𝟚) λ t →
    Σ (𝟙 ⇒ 𝟚) λ f →
    ¬ (t ≡ f)
  distinct-𝟚-maps =
    -- let
    --   sep = 𝟙-separator λ x → {!!}
    --   cosep = 𝟚-coseparator
    --   n = lower nondegen
    -- in
    {!!} , {!!} ,
    λ x → {!!}
