open import Data.Product
open import Data.Sum
open import Data.Nat
open import Relation.Binary.PropositionalEquality

module Subset
  where

_∘_ : ∀ {A B C : Set} (f : B → C) (g : A → B) → A → C
f ∘ g = λ x → f (g x)

_F≡_ : ∀ {A B : Set} (f g : A → B) → Set
_F≡_ f g = ∀ x → f x ≡ g x

id : ∀ {A : Set} → A → A
id x = x

Injective : {A B : Set} → (A → B) → Set
Injective f = ∀ x y → f x ≡ f y → x ≡ y

Surjective : {A B : Set} → (A → B) → Set
Surjective f = ∀ y → ∃[ x ] (f x ≡ y)

Retraction : {A B : Set} → (A → B) → (B → A) → Set
Retraction f r = (r ∘ f) F≡ id

Retract : {A B : Set} → (A → B) → Set
Retract f = ∃[ r ] (Retraction f r)

-- Inj-Surj : {A B : Set} (f : A → B) → Injective f → Σ (B → A) λ g → Surjective g
-- Inj-Surj f x = {!!} , {!!}

-- Surj-Inj : {A B : Set} (f : A → B) → Surjective f → Σ (B → A) λ g → Injective g
-- Surj-Inj f prf = (λ x → proj₁ (prf x)) , λ x y eq → {!!}

Subset : Set → Set → Set
Subset A B =
  Σ (A → B) λ f → Injective f
  -- Σ (A → B) λ f → Injective f × (Σ (B → A) (Retraction f))

-- Subset : Set → Set → Set
-- Subset A B = Σ (A → B) Injective

_⊆_ : Set → Set → Set
_⊆_ = Subset

inject : ∀ {A B} → A ⊆ B → (A → B)
inject (f , _) = f

inject′ : ∀ {A B} → (A⊆B : A ⊆ B) → Injective (inject A⊆B)
inject′ (_ , prf) = prf

-- surject′ : ∀ {A B} → (A⊆B : A ⊆ B) → Surjective (surject A⊆B)
-- surject′ (A⊆B , A⊆B₁) = proj₂ A⊆B₁

_∈_ : {A B : Set} → B → A ⊆ B → Set
_∈_ {A} {B} b A⊆B = Σ A λ a → (inject A⊆B a ≡ b)

∈-elem : ∀ {A B : Set} {b : B} → (A⊆B : A ⊆ B) → b ∈ A⊆B → A
∈-elem _ (fst , snd) = fst

⊆fiber-eq : ∀ {A B : Set} {b : B} (a : A) → (A⊆B : A ⊆ B) → b ∈ A⊆B → Set
⊆fiber-eq {A} {B} {b} a A⊆B (fst , snd) = a ≡ fst

⊆fiber-eq-2 : ∀ {V A B : Set} {v1 v2 : V} → (A⊆V : A ⊆ V) → (B⊆V : B ⊆ V) → v1 ∈ A⊆V → v2 ∈ B⊆V → Set
⊆fiber-eq-2 {V} {A} {B} {v1} {v2} A⊆V B⊆V (fst , snd) (fst₁ , snd₁) = v1 ≡ v2

-- elem-∈ : ∀ {A B : Set} {b : B} → (A⊆B : A ⊆ B) → b ∈ A⊆B

data Even : ℕ → Set where
  Even-0 : Even 0
  Even-ss : ∀ n → Even n → Even (suc (suc n))

Evens : Set
Evens = ∃[ n ] Even n

Evens-inj : Injective {Evens} {ℕ} proj₁
Evens-inj (.0 , Even-0) (.0 , Even-0) eq = refl
Evens-inj (.(suc (suc n)) , Even-ss n y) (.(suc (suc n)) , Even-ss .n y′) refl
  with Evens-inj (n , y) (n , y′) refl
... | refl = refl

ℕ→Evens : ℕ → Evens
ℕ→Evens zero = zero , Even-0
ℕ→Evens (suc (suc n)) with ℕ→Evens n
... | m , prf = suc (suc m) , Even-ss m prf
ℕ→Evens (suc n) = ℕ→Evens n

Evens-retract : Retraction proj₁ ℕ→Evens
Evens-retract (zero , Even-0) = refl
Evens-retract (suc (suc fst) , Even-ss .fst snd) with Evens-retract (fst , snd)
... | eq rewrite eq = refl

Evens⊆ℕ : Evens ⊆ ℕ
Evens⊆ℕ = proj₁ , Evens-inj

data Single (A : Set) : A → Set where
  mk-Single : (a : A) → Single A a

singleton⊆ : ∀ {A} → (a : A) → Single A a ⊆ A
singleton⊆ a =
  (λ _ → a) ,
  (λ { (mk-Single x) (mk-Single .x) _ → refl })

⊆-refl : ∀ {A} → A ⊆ A
⊆-refl = (λ x → x) , (λ x x₁ x₂ → x₂)

∈-trivial : {A : Set} → (x : A) → x ∈ (⊆-refl {A})
∈-trivial = λ x → x , refl

_I∘_ : ∀ {A B C} {f : B → C} {g : A → B} → Injective f → Injective g → Injective (f ∘ g)
_I∘_ {A} {B} {C} {f} {g} f-prf g-prf = λ x y z → g-prf x y (f-prf (g x) (g y) z)

_R∘_ : ∀ {A B C} {f : B → C} {g : A → B} {r : C → B} {r′ : B → A} →
  Retraction f r →
  Retraction g r′ →
  Retraction (f ∘ g) (r′ ∘ r)
_R∘_ {_} {_} {_} {f} {g} {r} {r′} f-prf g-prf x rewrite g-prf x | f-prf (g x) | g-prf x = refl

-- -- I∘-assoc : ∀ {A B C D : Set} {f : C → D} {g : B → C} {h : A → B} →
-- --   (f-prf : Injective f) → (g-prf : Injective g) → (h-prf : Injective h) →
-- --   (f-prf I∘ g-prf) I∘ h-prf ≡ f-prf I∘ (g-prf I∘ h-prf)
-- -- I∘-assoc f-prf g-prf h-prf = refl

inj₁-injective : ∀ {A B : Set} → Injective (inj₁ {_} {_} {A} {B})
inj₁-injective x .x refl = refl

inj₂-injective : ∀ {A B : Set} → Injective (inj₂ {_} {_} {A} {B})
inj₂-injective x .x refl = refl

-- data _∪_ (A B : Set) 

_F+_ : ∀ {A B X : Set} (f : A → X) (g : B → X) → (A ⊎ B → X)
(f F+ g) (inj₁ x) = f x
(f F+ g) (inj₂ y) = g y

-- inject-pullback : 

inj₁-retract : ∀ {A B : Set} → (f : B → A) → Retraction (inj₁ {_} {_} {A} {B}) (id F+ f)
inj₁-retract f x = refl

⊆-proj₁-inject : ∀ {A B} → (A⊆B : A ⊆ B) → Injective (proj₁ A⊆B)
⊆-proj₁-inject = proj₂

⊆-trans : ∀ {A B C : Set} → A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans {A} {B} {C} A⊆B B⊆C =
  inject B⊆C ∘ inject A⊆B ,
  inject′ B⊆C I∘ inject′ A⊆B

union-fst : ∀ {A B} → A ⊆ (A ⊎ B)
union-fst {A} {B} =
  inj₁ , inj₁-injective

union-snd : ∀ {A B} → B ⊆ (A ⊎ B)
union-snd {A} {B} =
  inj₂ , inj₂-injective

⊆union-1 : ∀ {A B B′} → A ⊆ B → A ⊆ (B ⊎ B′)
⊆union-1 (fst , snd) =
  (λ z → inj₁ (fst z)) ,
  inj₁-injective I∘ snd

⊆union-2 : ∀ {A B B′} → A ⊆ B′ → A ⊆ (B ⊎ B′)
⊆union-2 (fst , snd) =
  (λ z → inj₂ (fst z)) ,
  inj₂-injective I∘ snd

-- data Intersect {A V B : Set} (A⊆V : A ⊆ V) (B⊆V : B ⊆ V) : Set where
--   in-intersect : ∀ x y → (x-prf : x ∈ A⊆V) → (y-prf : y ∈ B⊆V) → ⊆fiber-eq-2 A⊆V B⊆V x-prf y-prf → Intersect A⊆V B⊆V

intersection : ∀ {V A B} →
  A ⊆ V →
  B ⊆ V →
  Set
intersection A⊆V B⊆V = ∃[ a ] ∃[ b ] (inject A⊆V a ≡ inject B⊆V b)

_∩_ : {A V B : Set} (A⊆V : A ⊆ V) (B⊆V : B ⊆ V) → Set
_∩_ = intersection

intersection-⊆ : {A V B : Set} (A⊆V : A ⊆ V) (B⊆V : B ⊆ V) →
  (A⊆V ∩ B⊆V) ⊆ V
intersection-⊆ {A} {V} {B} A⊆V B⊆V =
  -- (λ { (a , b , prf) →  subst (λ _ → V) prf (inject A⊆V a) }) ,
  (λ { (a , b , prf) →  inject A⊆V a }) ,
  {!!}
  where
    go : Injective {A⊆V ∩ B⊆V} {V} (λ { (a , b , prf) → inject A⊆V a })
    go (x₁ , x₂ , p) (y₁ , y₂ , q) eq rewrite (sym p) | sym q = {!!}

∈⊆ : ∀ {V A B} {x : V} →
  (B⊆V : B ⊆ V) →
  (A⊆B : A ⊆ B) →
  let A⊆V = ⊆-trans A⊆B B⊆V
  in
  x ∈ A⊆V →
  x ∈ B⊆V
∈⊆ {V} {A} {B} B⊆V A⊆B (f , refl) = inject A⊆B f , refl

-- ⊆-pullback : {A B V : Set} → V ⊆ A → (A → B) → 

-- intersect-extract : ∀ {V A B} → (A⊆V : A ⊆ V) → (B⊆V : B ⊆ V) → Intersect A⊆V B⊆V → V
-- intersect-extract A⊆V B⊆V (in-intersect x y x-prf y-prf x₁) = x

-- intersect-extract-inj : ∀ {V A B} → (A⊆V : A ⊆ V) → (B⊆V : B ⊆ V) → Intersect A⊆V B⊆V → Injective (intersect-extract A⊆V B⊆V)
-- intersect-extract-inj A⊆V B⊆V (in-intersect .(inject A⊆V fst) .(inject A⊆V fst) (fst , refl) y-prf refl) (in-intersect x₁ y x-prf₁ y-prf₁ x₂) (in-intersect .(intersect-extract A⊆V B⊆V (in-intersect x₁ y x-prf₁ y-prf₁ x₂)) y₁ x-prf₂ y-prf₂ x₄) refl = {!!}

disjoint : ∀ {V A B} →
  A ⊆ V →
  B ⊆ V →
  Set
disjoint A⊆V B⊆V = ∀ a b → inject A⊆V a ≢ inject B⊆V b

-- intersect : ∀ {V A B} →
--   (A⊆V : A ⊆ V) →
--   (B⊆V : B ⊆ V) →
--   Σ (A⊆V ∩ B⊆V) λ A∩B →
--   -- Σ (A∩B ⊆ V) λ A∩B⊆V →
--   ∀ x → x ∈ A∩B → (x ∈ A⊆V) × (x ∈ B⊆V)
-- intersect {V} {A} {B} A⊆V B⊆V =
--   A⊆V ∩ B⊆V ,
--   ((λ { (a , b) → inject A⊆V a }) , λ { x y x₁ → {!!} }) ,
--   {!!}
--   -- Intersect A⊆V B⊆V ,
--   -- (intersect-extract A⊆V B⊆V , λ x y x₁ → {!!}) , -- λ { (in-intersect x x-1 x-2) (in-intersect y y-1 y-2) refl → {!!} }) ,
--   -- λ x x₁ → {!!}

-- -- ⊆-intersect-⊎ : ∀ {V A B} →
-- --   (A-prf : A ⊆ V) →
-- --   (B-prf : B ⊆ V) →
-- --   (A∩B : A ∩ B) →
-- --   ∀ x →
-- --   x ∈ A
-- -- ⊆-intersect-⊎ = ?


-- -- ⊆-intersect : ∀ {V A B B′} →
-- --   (B-prf : B ⊆ V) →
-- --   (B′-prf : B′ ⊆ V) →
-- --   (A ⊆ B) →
-- --   (A ⊆ B′) →
-- --   Σ (B ⊆ V) λ B⊆V →
-- --     Σ (B′ ⊆ V) λ B′⊆V →
-- --       A ⊆ (B⊆V ∩ B′⊆V)
-- -- ⊆-intersect {V} {A} {B} {B′} B-prf B′-prf A⊆B A⊆B′ =
-- --   let A⊆V : A ⊆ V
-- --       A⊆V = ⊆-trans A⊆B B-prf
-- --   in
-- --   ⊆-trans {!!} B′-prf ,
-- --   {!!} ,
-- --   (λ x →
-- --     let b = inject A⊆B x
-- --         b′ = inject A⊆B′ x

-- --         v-1 = inject B-prf b
-- --         v-2 = inject B′-prf b′
-- --     in in-intersect (b , refl) (b′ , {!!})
-- --   ) ,
-- --   {!!}
-- --   -- (λ x → in-intersect {!!} {!!}) , {!!}
-- --   -- (λ x →
-- --   --   let b = inject A⊆B x
-- --   --       b′ = inject A⊆B′ x

-- --   --       v-1 = inject B-prf b
-- --   --       v-2 = inject B′-prf b′
-- --   --   in in-intersect (b , {!!}) (b′ , refl)
-- --   -- ) ,
-- --   -- {!!}

-- -- -- -- join : ∀ {A} → ∀ {U} → U ⊆ A → A
-- -- -- -- join = {!!}

