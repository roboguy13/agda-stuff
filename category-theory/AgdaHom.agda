open import Category
open import FunctorDefs
import ElementaryProperties
open import Agda
open import Relation.Binary using (IsEquivalence)

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Level

module AgdaHom
  {o : Level}
  {ℓ : Level}
  (ℂ : Category o ℓ )
  -- (let _≈_ = Category._≈_ Eq-ℂ)

  -- (_≈ₒ_ : ∀ {m} {A : Set m} → A → A → Set m)
  -- (≈ₒ-equiv : ∀ {m} {A : Set m} → IsEquivalence {_} {m} {A} _≈ₒ_)
  -- (≈-cong : ∀ {m} {A B : Set m} → (f : A → B) →
  --              {x x′ : A} →
  --              x ≈ x′ →
  --              f x ≈ f x′)
  -- (≈-cong₂ : ∀ {m} {A B C : Set m} → (f : A → B → C) →
  --              {x x′ : A} → {y y′ : B} →
  --              x ≈ x′ →
  --              y ≈ y′ →
  --              f x y ≈ f x′ y′)
  where


open Category.Category ℂ
open ElementaryProperties ℂ
-- open import Yoneda e ℓ ℂ

-- open IsEquivalence (Category.equiv ℂ {{!!}} {{!!}})

Agda′ : Category (suc ℓ) ℓ
Agda′ = Agda {ℓ} {ℓ}
-- Agda′ = Agda ? ? (Category._≈_ ℂ) ? ? ? --≈-cong ≈-cong₂

-- reflₒ : ∀ {A B} {f : A ⇒[ Agda′ ] B} → f ≈ₒ f
-- reflₒ = IsEquivalence.refl ≈ₒ-equiv
-- symₒ : ∀ {A B} {f g : A ⇒[ Agda′ ] B} → f ≈ₒ g → g ≈ₒ f
-- symₒ = IsEquivalence.sym ≈ₒ-equiv
-- transₒ : ∀ {A B} {f g h : A ⇒[ Agda′ ] B} → f ≈ₒ g → g ≈ₒ h → f ≈ₒ h
-- transₒ = IsEquivalence.trans ≈ₒ-equiv

Hom :
  (A : Category.Obj ℂ) → (B : Category.Obj ℂ) →
  Category.Obj Agda′
Hom A B = A ⇒[ ℂ ] B

unlift-eq : ∀ {m} {n} {A : Set m} →
  {x y : A} →
  lift {_} {n} x ≡ lift {_} {n} y →
  x ≡ y
unlift-eq refl = refl

infixr 9 _∘[Hom]_
_∘[Hom]_ :
  ∀ {A B C} →
  Hom B C →
  Hom A B →
  Hom A C
_∘[Hom]_ f g = f ∘[ ℂ ] g

Hom-whisker-right : ∀ {A B X} →
  (f : X ⇒[ ℂ ] A) →
  Hom A B →
  Hom X B
Hom-whisker-right f H = H ∘[Hom] f

Hom-whisker-left : ∀ {A B X} →
  (f : B ⇒[ ℂ ] X) →
  Hom A B →
  Hom A X
Hom-whisker-left f H = f ∘[Hom] H

    -- fmap-id : ∀ {A} →
    --   (fmap (Category.id Src {A})) ≈[ Tgt ] (Category.id Tgt)

Hom-F : Functor (Op ℂ ×cat ℂ) Agda′
Hom-F =
  record
  { act = λ (A , B) → Hom A B
  ; fmap′ = λ A B (f₁ , f₂) → lift λ g → f₂ ∘ g ∘ f₁
  ; fmap-id′ = λ T →
            let
              eq1 : (λ g → id {proj₂ T} ∘ g ∘ id {proj₁ T}) ≡ (λ g → id ∘ g)
              eq1 = fun-ext λ x →
                let
                  p = Category.right-id ℂ {_} {_} {id ∘ x}
                in
                trans (sym (Category.∘-assoc ℂ)) p

              eq2 : (λ (g : proj₁ T ⇒ proj₂ T) → id {proj₂ T} ∘ g) ≡ lower (Category.id Agda′)
              eq2 = fun-ext λ x → Category.left-id ℂ {_} {_} {x}
            in
            cong lift (trans eq1 eq2)
  ; fmap-∘′ = λ X A B f g →
           let
             eq1 :   lift (λ h → proj₂ f ∘ h ∘ proj₁ f)
                        ∘[ Agda′ ]
                     lift (λ i → proj₂ g ∘ i ∘ proj₁ g)
                   ≡
                     lift λ z → proj₂ f ∘ (proj₂ g ∘ z ∘ proj₁ g) ∘ proj₁ f
             eq1 = refl

             p z = proj₂ g ∘ z ∘ proj₁ g
             p1 = proj₂ f
             p2 = proj₂ g
             p3 = proj₁ g
             p4 = proj₁ f
             q = (λ (z : proj₁ X ⇒ proj₂ X) → proj₂ f ∘ (proj₂ g ∘ z ∘ proj₁ g) ∘ proj₁ f)

             eq2 :  (λ (z : proj₁ X ⇒ proj₂ X) → proj₂ f ∘ (proj₂ g ∘ z ∘ proj₁ g) ∘ proj₁ f)
                   ≡
                    (λ (z : proj₁ X ⇒ proj₂ X) → (proj₂ f ∘ proj₂ g) ∘ z ∘ (proj₁ g ∘ proj₁ f))
             eq2 = fun-ext λ z → CatBasics.∘-assoc5-mid ℂ
           in
           (trans eq1 (cong lift eq2))
  }

open import FunctorProperties

-- Hom(A, -)
Hom-Left : ∀ (A : Category.Obj (Op ℂ)) → Functor ℂ Agda
Hom-Left = F-Left Hom-F

-- Hom(-, B)
Hom-Right : ∀ (B : Category.Obj ℂ) → Functor (Op ℂ) Agda′
Hom-Right = F-Right Hom-F


Hom-Initial :
  {𝟘 : Category.Obj ℂ} → IsInitial 𝟘 →
  ∀ {A} →
  Hom 𝟘 A
Hom-Initial 𝟘-initial {A} = 𝟘-map 𝟘-initial

Hom-Terminal :
  ∀ {𝟙} → IsTerminal 𝟙 →
  ∀ {A} →
  Hom A 𝟙
Hom-Terminal 𝟙-terminal {A} = 𝟙-map 𝟙-terminal


Hom-Const : ∀ {𝟙} → IsTerminal 𝟙 →
  ∀ {A B} →
  (b : Hom 𝟙 B) →
  Hom A B
Hom-Const {𝟙} 𝟙-terminal {A} {B} b = b ∘[Hom] (Hom-Terminal 𝟙-terminal)

-- Hom-Left : ∀ (A : Category.Obj (Op ℂ)) → Functor ℂ Agda
-- Hom-Left A =
--   record
--     { act = Hom A
--     ; fmap′ = λ B C f → Functor.fmap Hom-F (Category.id ℂ , f)
--     ; fmap-id′ = λ B → Functor.fmap-id Hom-F
--     ; fmap-∘′ = λ B C D f g →
--               let
--                 p {T} = Functor.fmap-∘′ Hom-F (T , _) (_ , _) (_ , _) (Category.id ℂ , f) (Category.id ℂ , g)

--                 p′ : ∀ {T} → (λ z → comp ℂ {T} {_} {_} f ((g ∘ z ∘ id) ∘ id)) ≡
--                      (λ g₁ →
--                          proj₂ (comp (Op ℂ ×cat ℂ) {(B , _)} {_} {_} (id , f) (id , g)) ∘
--                          g₁ ∘ proj₁ (comp (Op ℂ ×cat ℂ) (id , f) (id , g)))
--                 p′ = unlift-eq p

--                 f-eq : Functor.fmap Hom-F (id {A} , f) ≡ lift λ h → f ∘ h ∘ id
--                 f-eq = refl

--                 g-eq : Functor.fmap Hom-F (id {B} , g) ≡ lift λ h → g ∘ h ∘ id
--                 g-eq = refl

--                 w1 : ∀ {T} → (Functor.fmap Hom-F (id {T} , f)) ∘[ Agda′ ] (Functor.fmap Hom-F (id {T} , g)) ≡ lift (λ h → f ∘ (g ∘ h ∘ id) ∘ id)
--                 w1 = refl

--                 w1′ : ∀ {m} {T} → lift {_} {m} (λ h → comp ℂ {T} {_} {_} f ((g ∘ h ∘ id) ∘ id)) ≡ lift (λ h → f ∘ (g ∘ h))
--                 w1′ = cong lift (fun-ext λ z → trans (CatBasics.rewrite-right-∘ ℂ (sym right-id) refl) (CatBasics.rewrite-right-∘ ℂ (CatBasics.rewrite-right-∘ ℂ right-id refl) refl))

--                 w1′′ : ∀ {n} {T} → lift {_} {n} (λ h → f ∘ (comp ℂ g h)) ≡ lift (λ h → (f ∘ g) ∘ (comp ℂ {T} {_} {_} h id)) 
--                 w1′′ = cong lift (fun-ext λ z → trans (sym ∘-assoc) (sym (CatBasics.rewrite-right-∘ ℂ (sym right-id) refl)))

--                 w2 : ∀ {T} → lift (λ h → (f ∘ g) ∘ (comp ℂ {T} {_} {_} h id)) ≡ Functor.fmap Hom-F (id , comp ℂ f g)
--                 w2 = refl
--               in
--               trans w1 (trans w1′ (trans w1′′ w2))
--     }
Hom-𝟘 : ∀ {𝟘} → IsInitial 𝟘 →
  ∀ {A B} →
  Hom A 𝟘 →
  Hom A B
Hom-𝟘 {𝟘} 𝟘-initial H = Hom-Initial 𝟘-initial ∘[Hom] H

Hom-× :
  (_⊗_ : Obj → Obj → Obj) →
  (∀ A B → IsProduct A B (A ⊗ B)) →
  ∀ {X A B} →
  Hom X A × Hom X B →
  Hom X (A ⊗ B)
Hom-× _⊗_ product (f , g) = joined-bimap _⊗_ product f g

-- Hom-Fn : ∀ {𝟙} → IsTerminal 𝟙 →
--   (_⊗_ : Obj → Obj → Obj) →
--   (product : ∀ A B → IsProduct A B (A ⊗ B)) →
--   (_⟶_ : Obj → Obj → Obj) →
--   (ev : ∀ A B → ((A ⟶ B) ⊗ A) ⇒ B) →
--   (∀ A B → IsExponential _⊗_ product (A ⟶ B) (ev A B)) →
--   ∀ {A B} →
--   Hom A B →
--   Hom 𝟙 (A ⟶ B)
-- Hom-Fn 𝟙-terminal _⊗_ product _⟶_ ev exp {A} {B} H with exp A B (A ⟶ B) (ev A B)
-- ... | fst , fst₁ , snd = {!!}

Hom-Ev : ∀ {A B A′ B′} →
  ((Hom A B → Hom A′ B′) × Hom A B)
    →
  Hom A′ B′
Hom-Ev (f , x) = f x

-- to-profunctor : ∀ {A B} →
--   A ⇒ B →
--   A ⇒[ (Op ℂ ×cat ℂ) ] B
-- to-profunctor = ?

-- よ-Exp-1 :
--   (_⊗_ : Obj → Obj → Obj) →
--   (product : ∀ A B → IsProduct A B (A ⊗ B)) →
--   (_⟶_ : Obj → Obj → Obj) →
--   (ev : ∀ A B → ((A ⟶ B) ⊗ A) ⇒ B) →
--   (∀ A B → IsExponential _⊗_ product (A ⟶ B) (ev A B)) →
--   ∀ {A B} →
--   actf よ (A ⟶ B) →
--   (actf よ A → actf よ B)
-- よ-Exp-1 _⊗_ product _⟶_ ev exp {A} {B} H-fn H =
--   Functor.fmap よ {!ev!} {!!}

-- Hom-Exp-1 :
--   (_⊗_ : Obj → Obj → Obj) →
--   (product : ∀ A B → IsProduct A B (A ⊗ B)) →
--   (_⟶_ : Obj → Obj → Obj) →
--   (ev : ∀ A B → ((A ⟶ B) ⊗ A) ⇒ B) →
--   (∀ A B → IsExponential _⊗_ product (A ⟶ B) (ev A B)) →
--   ∀ {A B X} →
--   Hom X (A ⟶ B) →
--   (Hom X A → Hom X B)
-- Hom-Exp-1 _⊗_ product _⟶_ ev exp {A} {B} {X} H-fn H =
--   let
--     -- p = Functor.fmap Hom-F {!!} {!!}
--     p : Hom X A → Hom X (A ⊗ X)
--     p z = Functor.fmap Hom-F {!!} {!!}
--   in
--   {!!}

-- Curry :
--   (_⊗_ : Obj → Obj → Obj) →
--   (product : ∀ A B → IsProduct A B (A ⊗ B)) →
--   (_⟶_ : Obj → Obj → Obj) →
--   (ev : ∀ A B → ((A ⟶ B) ⊗ A) ⇒ B) →
--   (∀ A B → IsExponential _⊗_ product (A ⟶ B) (ev A B)) →
--   ∀ {A B R} →
--   Hom (A ⊗ B) R ⇒[ Agda′ ] Hom A (B ⟶ R)
-- Curry _⊗_ product _⟶_ ev exp {A} {B} {R} with exp B R {!!} {!!}
-- ... | fst , fst₁ , snd = λ x → fst ∘ {!!}

-- Curry-Iso :
--   (_⊗_ : Obj → Obj → Obj) →
--   (product : ∀ A B → IsProduct A B (A ⊗ B)) →
--   (_⟶_ : Obj → Obj → Obj) →
--   (ev : ∀ A B → ((A ⟶ B) ⊗ A) ⇒ B) →
--   (∀ A B → IsExponential _⊗_ product (A ⟶ B) (ev A B)) →
--   ∀ {A B R} →
--   Hom (A ⊗ B) R ≅[ Agda′ ] Hom A (B ⟶ R)
-- Curry-Iso _⊗_ product _⟶_ ev exp {A} {B} {R} with exp B R (B ⟶ R) (ev B R)
-- ... | fst , fst₁ , snd =
--   (λ x → {!!}) , (λ x → {!!}) , (lift {!!}) , (lift {!!})

-- Hom-×-Iso :
--   (_⊗_ : Obj → Obj → Obj) →
--   (∀ A B → IsProduct A B (A ⊗ B)) →
--   ∀ {X A B} →
--   CategoryProperties._≅_ Agda′ (Hom X A × Hom X B) (Hom X (A ⊗ B))
-- Hom-×-Iso _⊗_ product =
--   (λ x → Hom-× _⊗_ product x) , (λ x → Functor.fmap ×cat-proj₁ {!!} {!!} , {!!}) , {!!} , {!!}
