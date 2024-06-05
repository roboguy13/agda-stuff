-- Elementary theory of the category of sets

-- open import CategoryRecord
open import Category
import ElementaryProperties renaming (𝟙-map to 𝟙-map′; 𝟘-map to 𝟘-map′)
open import NiceEquiv

open import Agda.Primitive
open import Data.Product renaming (_×_ to _×₀_ )
open import Data.Empty
open import Data.Unit

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Level

open import Agda hiding (nondegen)
  -- renaming (Hom to Hom′; _∘[Hom]_ to _∘[Hom]′_; Hom-Initial to Hom-Initial′)

import AgdaHom

module Sets
  (ℂ : Category lzero (lsuc lzero))
  -- (Eq-ℂ : Eq-Category (lsuc lzero) (lsuc lzero))
  where

-- ℂ : Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
-- ℂ = Cat Eq-ℂ

open Category.Category ℂ
open ElementaryProperties ℂ
--   renaming (𝟙-map to 𝟙-map′; 𝟘-map to 𝟘-map′)

infixr 2 _×_
infixr 1 _⊎_

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
  open AgdaHom ℂ

  neg : (A : Obj) → Set₁
  neg A = A ⇒ 𝟘

  𝟙+𝟙 : Obj
  𝟙+𝟙 = 𝟙 ⊎ 𝟙

  𝟙-map : ∀ {A} → (A ⇒ 𝟙)
  𝟙-map = 𝟙-map′ 𝟙-terminal

  -- 𝟙-map-unique : ∀ {A} → (f : A ⇒ 𝟙) → f ≈ 𝟙-map
  -- 𝟙-map-unique {A} f with 𝟙-terminal A
  -- ... | fst , fst₁ , snd = snd f (lift tt)

  𝟘-map : ∀ {A} → (𝟘 ⇒ A)
  𝟘-map = 𝟘-map′ 𝟘-initial

  -- product-proj₁ : ∀ {A B} →
  --   (A × B) ⇒ A
  -- product-proj₁ = ?

  -- Hom : ∀ (A B : Obj) → Category.Obj Agda'
  -- Hom =
  --   Hom′ zero (suc zero) _≡_ (λ {m} {A} → ≡-IsEquivalence {m} {A}) cong cong₂ {ℂ}

  -- Hom-Initial : 

  Hom×𝟘 : ∀ {A X : Obj} →
    ElementaryProperties._≅_ Agda′ (Hom A X ×₀ Hom A 𝟘) (Hom A 𝟘)
  Hom×𝟘 {A} {X} =
    lift (λ x → {!!}) , {!!} , {!!}
    --(λ x → {!!}) , (λ x → {!!}) , (λ x → {!!}) , λ x → {!!}
    -- -- (λ x → proj₂ x) , (λ x → ({!!} ∘[Hom] Hom-Initial 𝟘-initial ∘[Hom] x) , {!!}) ,
    -- (λ x → proj₂ x) , (λ x → Hom-𝟘 𝟘-initial x , x) ,
    -- (λ p →
    --   let x , y = p

    --       I = Hom-Initial 𝟘-initial
    --       w : Hom A X
    --       w = (Hom-Initial 𝟘-initial ∘[Hom] proj₂ p)

    --       eq : (w , proj₂ p) ≡ p
    --       eq = {!!}
    --   in
    --   lift {!!}) ,
    -- (λ x → lift _≡_.refl)



  -- ×𝟘≅𝟘 : ∀ {A} → (A × 𝟘) ≅ 𝟘
  -- ×𝟘≅𝟘 {A} =
  --   let
  --     p : (A × 𝟘) ⇒ 𝟘
  --     p = product-proj₂ (products A 𝟘)

  --     u = p ∘ 𝟘-map
  --     v = 𝟘-map ∘ p

  --     eq1 : u ≈ id
  --     eq1 = 𝟘-maps-same 𝟘-initial

  --     -- canon : (A × 𝟘) ⇒ (A × 𝟘)
  --     -- canon = products ()

  --     eq2 : v ≈ id
  --     eq2 = {!!}
  --   in
  --   p , 𝟘-map , eq2 , eq1

  -- 𝟘-strict-initial : Strict-Initial 𝟘-initial
  -- 𝟘-strict-initial {A} f =
  --   let
  --     m : A ⇒ A
  --     m = 𝟘-map {A} ∘ f

  --     n : 𝟘 ⇒ 𝟘
  --     n = f ∘ 𝟘-map {A}

  --     eq1 : n ≈ id
  --     eq1 = 𝟘⇒𝟘-is-id 𝟘-initial n

  --     p : (A × 𝟘) ≅ 𝟘
  --     p = {!!}
  --   in
  --   {!!} , eq1

  -- -- 𝟘-map-unique : ∀ {A} → (f : 𝟘 ⇒ A) → f ≈ 𝟘-map
  -- -- 𝟘-map-unique {A} f with 𝟘-initial A
  -- -- ... | fst , fst₁ , snd = snd f (lift tt)

  -- --
  -- -- 𝟘 --> B
  -- -- |     |
  -- -- |     | j
  -- -- v     v
  -- -- A --> A+B
  -- --    i
  -- coproduct-pullback : ∀ {A B} →
  --   ∃[ f ] ∃[ g ]
  --   (IsPullback
  --     A B
  --     (A ⊎ B)
  --     (coproduct-inj₁ (coproducts A B))
  --     (coproduct-inj₂ (coproducts A B))
  --     𝟘
  --     f
  --     g)
  -- coproduct-pullback {A} {B}
  --   with Pullback A B (A ⊎ B) (coproduct-inj₁ (coproducts A B))(coproduct-inj₂ (coproducts A B))
  -- ... | fst , fst₁ , fst₂ , fst₃ , snd =
  --   𝟘-map , 𝟘-map , 𝟘-maps-same 𝟘-initial ,
  --   (λ Z f′ g′ p₁′ p₂′ x →
  --     let
  --       m , q1 , q2 = (snd Z f′ g′ p₁′ p₂′ x)
  --       -- w1 , w2 , w3 = snd Z f′ g′ p₁′ p₂′ x
  --       -- w1 , w2 , w3 = snd Z f′ g′ (fst₁ ∘ proj₁ (snd Z f′ g′ p₁′ p₂′ x))  (proj₁ (snd Z f′ g′ p₁′ p₂′ x)) {!!}
  --       w1 , w2 , w3 = snd Z f′ g′ (fst₁ ∘ m) p₂′ {!!}


  --       -- eq : (Eq-ℂ Eq-Category.∘ fst₁) (proj₁ (snd Z f′ g′ p₁′ p₂′ x)) ≡ p₁′
  --       -- eq = {!!}

  --       w = w3 {!!} ({!!} , {!!})
  --     in
  --     {!!} , ({!!} , {!!}) , (λ n x₁ →
  --       let q2′ = q2 (𝟘-map ∘ n) ({!!} , {!!})
  --       in {!!}))

  --   -- Pullback : ∀ A B X (f : A ⇒ X) (g : B ⇒ X) →
  -- -- inj₁-monic : ∀ {A B} →
  -- --   Monic (coproduct-inj₁ (coproducts A B))
  -- -- inj₁-monic X g₁ g₂ x =
  -- --   {!!}
  -- --   -- 𝟚-coseparator λ φ → {!!}

  -- -- ⊎-disjoint : 

  -- -- distribute : 

  -- -- 𝟚↪𝟙+𝟙 : Σ (𝟚 ⇒ (𝟙 ⊎ 𝟙)) Monic
  -- -- 𝟚↪𝟙+𝟙 with coproducts 𝟙 𝟙
  -- -- ... | fst , fst₁ , snd =
  -- --   {!!} , λ g₁ g₂ x → {!!}

  -- -- 𝟚≅𝟙+𝟙 : 𝟚 ≅ (𝟙 ⊎ 𝟙)
  -- -- 𝟚≅𝟙+𝟙 =
  -- --   {!!} ,
  -- --   {!!} ,
  -- --   {!!} ,
  -- --   {!!}

  -- left-𝟙+𝟙 : 𝟙 ⇒ 𝟙+𝟙
  -- left-𝟙+𝟙 with coproducts 𝟙 𝟙
  -- ... | fst , z = fst

  -- right-𝟙+𝟙 : 𝟙 ⇒ 𝟙+𝟙
  -- right-𝟙+𝟙 with coproducts 𝟙 𝟙
  -- ... | fst , fst₁ , snd = fst₁

  -- left≠right : ¬ (left-𝟙+𝟙 ≈ right-𝟙+𝟙)
  -- left≠right prf = {!!}


  -- swap-𝟙+𝟙 : 𝟙+𝟙 ⇒ 𝟙+𝟙
  -- swap-𝟙+𝟙 with coproducts 𝟙 𝟙
  -- ... | fst , fst₁ , snd with snd fst₁ fst
  -- swap-𝟙+𝟙 | fst , fst₁ , snd | fst₂ , z = fst₂

  -- swap-𝟙+𝟙-not-id : ¬ (swap-𝟙+𝟙 ≈ id)
  -- swap-𝟙+𝟙-not-id = {!!}

  -- false : 𝟙 ⇒ 𝟚
  -- false = {!!}

  -- false≠true : ¬ (false ≈ true)
  -- false≠true = {!!}

  -- 𝟙+𝟙-maps-not-all-same :
  --   ¬ (∀ (f g : 𝟙 ⇒ 𝟙+𝟙) → f ≈ g)
  -- 𝟙+𝟙-maps-not-all-same prf with subobj-classify (point-monic 𝟙-terminal true) | subobj-classify (point-monic 𝟙-terminal false)
  -- ... | fst , (fst₂ , snd₂) , snd | fst₁ , (fst₃ , snd₃) , snd₁ =
  --   nondegen ({!!} , 𝟙-map , ({!!} , {!!}))

  -- has-point→non-𝟘 : ∀ {A} → (𝟙 ⇒ A) → ¬ (A ≅ 𝟘)
  -- has-point→non-𝟘 f (fst , fst₁ , fst₂ , snd) =
  --   Nondegenerate→no-𝟙⇒𝟘 𝟙-terminal 𝟘-initial nondegen (fst ∘ f)

  -- 𝟚-maps-not-all-same :
  --   ¬ (∀ (f g : 𝟙 ⇒ 𝟚) → f ≈ g)
  -- 𝟚-maps-not-all-same prf =
  --   nondegen ({!!} , 𝟙-map , ({!!} , {!!}))
  --   -- nondegen
  --   --   (λ B →
  --   --     let p = {!!}
  --   --     in
  --   --     {!!} ,
  --   --   {!!} ,
  --   --   λ n x → {!!})

  -- distinct-𝟚-maps :
  --   Σ (𝟙 ⇒ 𝟚) λ t →
  --   Σ (𝟙 ⇒ 𝟚) λ f →
  --   ¬ (t ≡ f)
  -- distinct-𝟚-maps =
  --   -- let
  --   --   sep = 𝟙-separator λ x → {!!}
  --   --   cosep = 𝟚-coseparator
  --   --   n = lower nondegen
  --   -- in
  --   {!!} , {!!} ,
  --   λ x → {!!}
