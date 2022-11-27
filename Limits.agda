open import Category
open import FunctorDefs
open import FunctorProperties
import ElementaryProperties
open import Yoneda
open import Agda
open import AgdaHom

open import Level renaming (suc to lsuc; zero to lzero)

open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (lift)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Product.Properties
open import Relation.Binary.Definitions using (Substitutive)

open import Function hiding (case_of_) -- using (Inverse)

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.HeterogeneousEquality hiding (cong; cong₂) renaming (_≅_ to _H≅_; trans to H-trans; sym to H-sym; subst to H-subst)

open import Axiom.UniquenessOfIdentityProofs.WithK

module Limits
  where

-- ×-η : ∀ {m} {A A′ B : Set m} → {x x′ : A} → {y y′ : B} →
--   x ≡ x′ →
--   y ≡ y′ →
--   (x , y′) ≡ (x , y′)
-- ×-η refl refl = refl

-- Σ-≡,≡→≡ : ∀ {m n}  {A : Set m} {B : A → Set n} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ A B} {a₁ a₂ B b₁ b₂ p₁ p₂} → Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂) → p₁ ≡ p₂
-- Σ-≡,≡→≡ (refl , refl) = refl

-- H-compat : ∀ {m} → {A B : Set m} →
--   A ≡ B →
--   ∀ {x : A} {y : B} →
--   x ≅ y →

-- lower-eq : ∀ {m} {A B} →
--   A ≡ B

subst-removable₀ : ∀ {n} {x y : Set n} (eq : x H≅ y) (z : x) →
                  H-subst (λ x → x) eq z H≅ z
subst-removable₀ refl _ = refl

CSquare-≡ : ∀ {o ℓ} {ℂ : Category o ℓ} →
  ∀ {A B X P} →
  ∀ {f : A ⇒[ ℂ ] X} {g : B ⇒[ ℂ ] X}
  {p₁ : P ⇒[ ℂ ] A} {p₂ : P ⇒[ ℂ ] B} →
  ∀ {f′ : A ⇒[ ℂ ] X} {g′ : B ⇒[ ℂ ] X}
  {p₁′ : P ⇒[ ℂ ] A} {p₂′ : P ⇒[ ℂ ] B} →
  (prf1 : ElementaryProperties.CSquare ℂ f g p₁ p₂) →
  (prf2 : ElementaryProperties.CSquare ℂ f′ g′ p₁′ p₂′) →
  prf1 H≅ prf2
CSquare-≡ = {!!}
-- CSquare-≡ prf1 prf2 = uip prf1 prf2

CSquare-≡₂ : ∀ {o ℓ} {ℂ : Category o ℓ} →
  ∀ {A B X P} →
  ∀ {f : A ⇒[ ℂ ] X} {g : B ⇒[ ℂ ] X}
  {p₁ : P ⇒[ ℂ ] A} {p₂ : P ⇒[ ℂ ] B} →
  ∀ {f′ : A ⇒[ ℂ ] X} {g′ : B ⇒[ ℂ ] X}
  {p₁′ : P ⇒[ ℂ ] A} {p₂′ : P ⇒[ ℂ ] B} →
  ∀  {Z : Set ℓ} {z z′ : Z} →
  z ≡ z′ →
  (prf1 : ElementaryProperties.CSquare ℂ f g p₁ p₂) →
  (prf2 : ElementaryProperties.CSquare ℂ f′ g′ p₁′ p₂′) →
  (z , prf1) H≅ (z′ , prf2)
CSquare-≡₂ = {!!}

pair-prf-elim : ∀ {m} {A : Set m} {B B′ : A → Set m} {p₁@(a₁ , b₁) : Σ A B} {p₂@(a₂ , b₂) : Σ A B′} →
  a₁ ≡ a₂ →
  B ≡ B′ → -- Use extensionality to get this argument when we use this?
  b₁ H≅ b₂ →
  p₁ H≅ p₂
pair-prf-elim refl refl refl = refl

pair-prf-elim′ : ∀ {m} {A : Set m} {B B′ : A → Set m} {p₁@(a₁ , b₁) : Σ A B} {p₂@(a₂ , b₂) : Σ A B′} →
  a₁ ≡ a₂ →
  B ≡ B′ → -- Use extensionality to get this argument when we use this?
  b₁ H≅ b₂ →
  p₁ ≡ subst (λ z → z) {!!} p₂
pair-prf-elim′ = {!!}


-- H≅-to-≡ : ∀ {m} {A B : Set m} →


data Interval-Arr : Fin 2 → Fin 2 → Set where
  interval-arr : Interval-Arr zero (suc zero)
  interval-id : ∀ x → Interval-Arr x x

Interval-Cat : Category lzero lzero
Interval-Cat =
  record
    { Obj = Fin 2
    ; _⇒_ = Interval-Arr
    ; _∘_ = comp-def
    ; id = λ {x} → interval-id x
    ; left-id = left-id-def
    ; right-id = right-id-def
    ; ∘-assoc = comp-assoc-def
    }
  where
    comp-def : ∀ {A B C} → Interval-Arr B C → Interval-Arr A B → Interval-Arr A C
    comp-def interval-arr (interval-id .zero) = interval-arr
    comp-def (interval-id .(suc zero)) interval-arr = interval-arr
    comp-def (interval-id A) (interval-id _) = interval-id A

    left-id-def : {A B : Fin 2} {f : Interval-Arr A B} →
                  comp-def (interval-id B) f ≡ f
    left-id-def {_} {_} {interval-arr} = refl
    left-id-def {_} {_} {interval-id _} = refl

    right-id-def : {A B : Fin 2} {f : Interval-Arr A B} →
                  comp-def f (interval-id A) ≡ f
    right-id-def {_} {_} {interval-arr} = refl
    right-id-def {_} {_} {interval-id _} = refl

    comp-assoc-def : ∀ {A B C D : Fin 2} {f : Interval-Arr C D} {g : Interval-Arr B C}
            {h : Interval-Arr A B} →
            comp-def (comp-def f g) h ≡ comp-def f (comp-def g h)
    comp-assoc-def {_} {_} {_} {_} {interval-arr} {interval-id .zero} {interval-id .zero} = refl
    comp-assoc-def {_} {_} {_} {_} {interval-id .(suc zero)} {interval-arr} {interval-id .zero} = refl
    comp-assoc-def {_} {_} {_} {_} {interval-id .(suc zero)} {interval-id .(suc zero)} {interval-arr} = refl
    comp-assoc-def {_} {_} {_} {_} {interval-id _} {interval-id _} {interval-id _} = refl

-- Arrow-Cat : ∀ {o ℓ} → Category o ℓ → Category (lsuc o Level.⊔ lsuc ℓ Level.⊔ lsuc lzero) (lsuc lzero Level.⊔ lsuc lzero Level.⊔ lsuc o Level.⊔ lsuc ℓ)
-- Arrow-Cat ℂ = [ Interval-Cat ,, ℂ ]

Arrow-Cat : ∀ {o ℓ} → Category o ℓ → Category {!!} {!!}
Arrow-Cat {o} {ℓ} ℂ =
  record
    { Obj = Obj₀
    ; _⇒_ = _⇒₀_
    ; _∘_ = ∘-def
    -- ; _∘_ = λ {(A , f-A)} {(B , f-B)} {(C , f-C)} (a₁ , b₁ , f) (a₂ , b₂ , g) →
    --           {!!} , {!!} , {!!} -- ElementaryProperties.CSquare-horiz-comp {!!} {!!} {!!}
    ; id = (Category.id ℂ , Category.id ℂ) , trans (Category.right-id ℂ) (sym (Category.left-id ℂ))
    ; left-id = {!!} -- λ {A} {B} {f} → {!fun-ext!}
    ; right-id = {!!}
    ; ∘-assoc = {!!}
    }
    where
      -- Obj₀ = Σ (Category.Obj ℂ) λ A → Σ (Category.Obj ℂ) λ B → (A ⇒[ ℂ ] B)
      Obj₀ : Set (o Level.⊔ ℓ)
      Obj₀ = Σ (Category.Obj ℂ × Category.Obj ℂ) λ (A , B) →  (A ⇒[ ℂ ] B)

      _⇒₀_ : Obj₀ → Obj₀ → Set ℓ
      _⇒₀_ = λ ((A₁ , B₁) , f) ((A₂ , B₂) , g) → Σ ((B₂ ⇒[ ℂ ] B₁) × (A₂ ⇒[ ℂ ] A₁)) λ (a , b) → (ElementaryProperties.CSquare ℂ f a b g)

      ∘-def : ∀ {A B C} → (B ⇒₀ C) → (A ⇒₀ B) → (A ⇒₀ C)
      ∘-def {(A , A′) , f-A} {(B , B′) , f-B} {(C , C′) , f-C} F G =
        let
          ((p , q) , snd) = F
          ((f , g) , snd₁) = G
          s = g ∘[ ℂ ] q
          t = f ∘[ ℂ ] p
        in
        (t , s) , ElementaryProperties.CSquare-vert-comp ℂ snd snd₁


      left-id-def : {A B : Obj₀} {f : A ⇒₀ B} →
                    ∘-def ((Category.id ℂ , Category.id ℂ),
                      trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
                      f
                    ≡ f
      left-id-def {A} {B} {f} =
        let
            f1 = proj₁ (proj₁ f)
            f2 = proj₂ (proj₁ f)

            ∘-app = ∘-def ((Category.id ℂ , Category.id ℂ) ,
                      trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
                      f

            p : ∘-app ≡ (((f1 ∘[ ℂ ] Category.id ℂ) , (f2 ∘[ ℂ ] Category.id ℂ)) ,
                   ElementaryProperties.CSquare-vert-comp ℂ (trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
                     (proj₂ f)
                  )
            p = refl

            p′ : ∀ {X Y X′ Y′} {h : X ⇒[ ℂ ] Y} {h′ : X′ ⇒[ ℂ ] Y′} → ((h ∘[ ℂ ] Category.id ℂ) , (h′ ∘[ ℂ ] Category.id ℂ)) ≡ (h , h′)
            p′ = Inverse.f ×-≡,≡↔≡ (Category.right-id ℂ , Category.right-id ℂ)

            p1 : proj₁ ∘-app
                  ≡ proj₁ f
            p1 =
               let z , _ = Inverse.f⁻¹ Σ-≡,≡↔≡ p
               in
               trans z (trans p′ refl)

            p-left = subst
                (λ x →
                  ElementaryProperties.CSquare ℂ (proj₂ A) (proj₁ x)
                  (proj₂ x) (proj₂ B))
                (trans
                  (case (Category.right-id ℂ {(proj₂ (proj₁ B))} {(proj₂ (proj₁ A))} {f1} , Category.right-id ℂ {(proj₁ (proj₁ B))} {(proj₁ (proj₁ A))} {f2}) of
                    λ { (p₁ , p₂) → Inverse.f ×-≡,≡↔≡ (p₁ , p₂) })

                -- ((λ { (refl , refl) → refl {{!!}} {{!!}} {{!!}} {{!!}} {{!!}} })
                --   (Category.right-id ℂ , Category.right-id ℂ))
                  refl)
                (ElementaryProperties.CSquare-vert-comp ℂ
                (trans (Category.right-id ℂ) (sym (Category.left-id ℂ))) (proj₂ f))

        in
        -- Inverse.f Σ-≡,≡↔≡ (p1 , ≅-to-≡ (CSquare-≡ {_} {_} {ℂ} (proj₂ ∘-app) (proj₂ f))) --CSquare-≡ {_} {_} {ℂ} (proj₂ ∘-app) (proj₂ f))
        -- Inverse.f Σ-≡,≡↔≡ (p1 , ≅-to-subst-≡ (CSquare-≡ {?} {?} {ℂ} (proj₂ ∘-app) (proj₂ f))) --CSquare-≡ {_} {_} {ℂ} (proj₂ ∘-app) (proj₂ f))

        Inverse.f Σ-≡,≡↔≡ (p1 , (uip p-left (proj₂ f))) -- ≅-to-subst-≡ {{!!}} {?} {?} {pr} {!!})


      -- left-id-eq : ∀ {A B} Z → ∘-def {A} {B} {B} (Category.id ℂ  , Category.id ℂ  , trans (Category.right-id ℂ) (sym (Category.left-id ℂ))) Z
      --               ≡ Z
      -- left-id-eq {A , A′ , f-A} {B , B′ , f-B} Z =
      --   let
      --     x , y , z = ∘-def (Category.id ℂ , Category.id ℂ , trans (Category.right-id ℂ) (sym (Category.left-id ℂ))) Z

      --     p : x ≡ (proj₁ Z) ∘[ ℂ ] Category.id ℂ
      --     p = refl

      --     p′ : x ≡ proj₁ Z
      --     p′ = Category.right-id ℂ

      --     q′ : y ≡ proj₁ (proj₂ Z)
      --     q′ = Category.right-id ℂ

      --     -- w0 : y H≅ proj₂ Z
      --     -- w0 = {!!}


      --     -- w : (subst
      --     --       (λ a → ∃-syntax (λ b → ElementaryProperties.CSquare ℂ f-A a b f-B))
      --     --       (Category.right-id ℂ)
      --     --       (comp ℂ (proj₁ (proj₂ Z)) (Category.id ℂ) ,
      --     --         ElementaryProperties.CSquare-vert-comp ℂ
      --     --         (trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
      --     --         (proj₂ (proj₂ Z))))
      --     --     ≡ proj₂ Z
      --     -- w = ≅-to-subst-≡ w0

      --     -- w′ : ∃-syntax (λ b → ElementaryProperties.CSquare ℂ f-A (Category.right-id ℂ) b f-B)
      --     --      H≅
      --     --      proj₂ Z
      --     -- w′ = ?

      --   in
      --   Inverse.f Σ-≡,≡↔≡ (p′ , Inverse.f Σ-≡,≡↔≡ ({!!} , {!!}))
      --   -- ×-η ? ?
      -- -- left-id-eq {A , A′ , f-A} {B , B′ , f-B} (fst , fst₁ , snd)
      -- --   with ∘-def (Category.id ℂ , Category.id ℂ , trans (Category.right-id ℂ) (sym (Category.left-id ℂ))) (fst , fst₁ , snd)
      -- -- ... | fst₂ , fst₃ , snd₁ = {!!}

      -- left-id-def : {A B : Obj₀} {f : A ⇒₀ B} →
      --               ∘-def (Category.id ℂ ,
      --                 Category.id ℂ ,
      --                 trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
      --                 f
      --               ≡ f
      -- left-id-def {A} {B} {f , g , prf} =
      --   let p : ∘-def (Category.id ℂ ,
      --                 Category.id ℂ ,
      --                 trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
      --                 (f , g , prf)
      --           ≡ ((f ∘[ ℂ ] Category.id ℂ) ,
      --              (g ∘[ ℂ ] Category.id ℂ) ,
      --              ElementaryProperties.CSquare-vert-comp ℂ (trans (Category.right-id ℂ) (sym (Category.left-id ℂ))) prf
      --             )
      --       p = refl

      --       p1 : proj₁ (∘-def (Category.id ℂ ,
      --                 Category.id ℂ ,
      --                 trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
      --                 (f , g , prf))
      --             ≡ f
      --       p1 =
      --          let z , _ = Inverse.f⁻¹ Σ-≡,≡↔≡ p
      --          in
      --          trans z (Category.right-id ℂ)

      --       p2 : proj₁ (proj₂ (∘-def (Category.id ℂ ,
      --                 Category.id ℂ ,
      --                 trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
      --                 (f , g , prf)))
      --             ≡ g
      --       p2 =
      --          let _ , w = Inverse.f⁻¹ Σ-≡,≡↔≡ p
      --              z , _ = Inverse.f⁻¹ Σ-≡,≡↔≡ w
      --          in
      --          trans z (Category.right-id ℂ)

      --       w = ElementaryProperties.CSquare-vert-comp ℂ (trans (Category.right-id ℂ) (sym (Category.left-id ℂ))) prf

      --       w′ :  ElementaryProperties.CSquare ℂ (proj₂ (proj₂ A))
      --               (comp ℂ f (Category.id ℂ)) ((ℂ Category.∘ g) (Category.id ℂ))
      --               (proj₂ (proj₂ B))
      --             ≡  ElementaryProperties.CSquare ℂ (proj₂ (proj₂ A)) f g (proj₂ (proj₂ B))
      --       w′ =
      --         cong₂ (λ x y →
      --               ElementaryProperties.CSquare ℂ (proj₂ (proj₂ A)) x y (proj₂ (proj₂ B)))
      --           (Category.right-id ℂ) (Category.right-id ℂ)

      --       w′′ = H-subst (λ x → x) (≡-to-≅ w′) w

      --       z : w′′ ≡ prf
      --       z = uip w′′ prf

      --       z′ : H-subst (λ x → x) (≡-to-≅ w′) w H≅ w
      --       z′ = subst-removable₀ {!!} {!!}

      --       z′′ : w H≅ prf
      --       z′′ = H-trans (H-sym z′) (≡-to-≅ z)

      --       p3 : proj₂ (proj₂ (∘-def (Category.id ℂ ,
      --                 Category.id ℂ ,
      --                 trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
      --                 (f , g , prf)))
      --             H≅ prf
      --       p3 =
      --          -- let _ , w = Inverse.f⁻¹ Σ-≡,≡↔≡ p
      --          --     _ , y = Inverse.f⁻¹ Σ-≡,≡↔≡ w
      --          -- in
      --          z′′

      --       -- q : ElementaryProperties.CSquare-vert-comp ℂ (trans (Category.right-id ℂ) (sym (Category.left-id ℂ))) prf H≅ prf
      --       -- q = {!!}

      --       m : ∘-def (Category.id ℂ ,
      --                 Category.id ℂ ,
      --                 trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
      --                 (f , g , prf)
      --           ≡ (f ,
      --              g ,
      --              prf
      --             )
      --       m = {!!}
      --   in
      --   {!!}
      --   -- Inverse.f Σ-≡,≡↔≡ (p1 , Inverse.f Σ-≡,≡↔≡ (≅-to-≡ (subst-removable (λ a →
      --   --               ∃-syntax
      --   --               (λ b →
      --   --                 ElementaryProperties.CSquare ℂ (proj₂ (proj₂ A)) a b
      --   --                 (proj₂ (proj₂ B)))) ? ?)
      --   --                 , {!!}))
      -- -- ∘-def : ∀ {A B C} → (B ⇒₀ C) → (A ⇒₀ B) → (A ⇒₀ C)
      -- -- ∘-def {A , A′ , f-A} {B , B′ , f-B} {C , C′ , f-C} F G =
      -- --   let
      -- --     (p , q , snd) = F
      -- --     (f , g , snd₁) = G
      -- --     s = g ∘[ ℂ ] q
      -- --     t = f ∘[ ℂ ] p
      -- --   in
      -- --   t , s , ElementaryProperties.CSquare-vert-comp ℂ snd snd₁

Cone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  (c : Category.Obj 𝔻) →
  Set (Level.suc o₁ Level.⊔ Level.suc ℓ₁ Level.⊔ Level.suc o₂ Level.⊔ Level.suc ℓ₂)
Cone F c =
  NatTrans (Const-Functor c) F

Cone-∘ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} {𝔼 : Category o₁ ℓ₁} →
  {F : Functor ℂ 𝔻} →
  {c : Category.Obj 𝔻} →
  (G : Functor 𝔻 𝔼) →
  Cone F c →
  Cone (G ∘F F) (actf G c)
Cone-∘ {o₁} {ℓ₁} {o₂} {ℓ₂} {ℂ} {𝔻} {𝔼} {F} {c} G cone =
  ((G ∘WL cone)
    ∘NT
   subst (λ x → NatTrans x (G ∘F Const-Functor c))
     (sym (Const-Functor-commutes {o₂} {ℓ₂} {o₁} {ℓ₁} {ℓ₂} {ℓ₂} {𝔻} {𝔼} {ℂ} {G}))
     NT-id
   )

ACone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  Set (Level.suc o₁ Level.⊔ Level.suc ℓ₁ Level.⊔ Level.suc o₂ Level.⊔
         Level.suc ℓ₂)
ACone F = ∃[ c ] (Cone F c)

Is-Universal-Cone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  (c : Category.Obj 𝔻) →
  Cone F c →
  Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc o₂ Level.⊔ lsuc ℓ₂)
Is-Universal-Cone {_} {_} {_} {_} {ℂ} {𝔻} F c cone =
  ∀ c′ (cone′ : Cone F c′) →
  Σ (c′ ⇒[ 𝔻 ] c) λ m →
  ∀ (A : Category.Obj 𝔻) (f : c ⇒[ 𝔻 ] A) (g : c′ ⇒[ 𝔻 ] A) →
  g ≡ (f ∘[ 𝔻 ] m)

Lim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc o₂ Level.⊔ lsuc ℓ₂)
Lim F = ∃[ c ] ∃[ cone ] (Is-Universal-Cone F c cone)



Fin-Cat : (n : ℕ) → Category Level.zero Level.zero
Fin-Cat n =
  record
    { Obj = Fin n
    ; _⇒_ = λ A B → A ≡ B
    ; _∘_ = λ f g → trans g f
    ; id = refl
    ; left-id = λ {A} {B} {f} → uip (trans f refl) f
    ; right-id = refl -- TODO: Why the asymmetry here?
    ; ∘-assoc = λ {A} {B} {C} {D} {f} {g} {h} → uip (trans h (trans g f)) (trans (trans h g) f)
    }

private
  eq-apply : ∀ {m} {A B : Set m} →
    A ≡ B →
    A →
    B
  eq-apply refl x = x

  elim-eq-apply : ∀ {m} {A B : Set m} {x} →
    (prf : A ≡ B) →
    eq-apply prf x H≅ x
  elim-eq-apply {_} {_} {_} {_} refl = refl
    -- x H≅ y
  -- elim-eq-apply {_} {_} {_} {_} {_} {refl} refl = refl

Fin-Cat-Functor : ∀ {o ℓ} {ℂ : Category o ℓ} →
  {n : ℕ} →
  (Fin n → Category.Obj ℂ) →
  Functor (Fin-Cat n) ℂ
Fin-Cat-Functor {_} {_} {ℂ} {n} fn =
  record
    { act = fn
    ; fmap′ = fmap-def
    ; fmap-id′ = λ A → refl
    ; fmap-∘′ = fmap-∘-def
    }
    where
      fmap-def : (A B : Fin n) → Arr (Fin-Cat n) A B → Arr ℂ (fn A) (fn B)
      fmap-def A B refl = Category.id ℂ

      fmap-∘-def : (A B C : Fin n) (f : Arr (Fin-Cat n) B C)
                    (g : Arr (Fin-Cat n) A B) →
                    comp ℂ (fmap-def B C f) (fmap-def A B g) ≡
                    fmap-def A C (comp (Fin-Cat n) f g)
      fmap-∘-def A B C refl refl = Category.left-id ℂ

×-Limit : ∀ {o ℓ} {ℂ : Category o ℓ} → (A B : Category.Obj ℂ) → Set (lsuc o Level.⊔ lsuc ℓ)
×-Limit {o} {ℓ} {ℂ} A B =
  Lim {Level.zero} {Level.zero} {o} {ℓ} {Fin-Cat 2} {ℂ} (Fin-Cat-Functor go)
  where
    go : Fin 2 → Category.Obj ℂ
    go Fin.zero = A
    go (suc Fin.zero) = B

Is-Continuous : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  Functor ℂ 𝔻 →
  Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc o₂ Level.⊔ lsuc ℓ₂)
Is-Continuous {_} {_} {o₂} {ℓ₂} {ℂ} {𝔻} F =
  (𝔼 : Category o₂ ℓ₂) →
  (A : Functor 𝔼 ℂ) →
  (lim-A : Lim A) →
  (lim-FA : Lim (F ∘F A)) →
  let
    lim-A-apex = proj₁ lim-A
    lim-FA-apex = proj₁ lim-FA
    m = proj₂ (proj₂ lim-FA)

    cone : Cone A lim-A-apex
    cone = proj₁ (proj₂ lim-A)

    x , y = m (actf F lim-A-apex) (Cone-∘ F cone)

    p : actf F lim-A-apex ⇒[ 𝔻 ] lim-FA-apex
    p = x
  in
  ⊤
  -- ElementaryProperties.Is-Iso Agda p {!!}

-- Point : ∀ {o ℓ o₂ ℓ₂} {𝔻 : Category o ℓ} →
--   Functor 𝔻 (Agda {o₂} {ℓ₂})
-- Point {_} {_} {o₂} = Const-Functor (Lift o₂ ⊤)

-- -- Hom_C(c, F(-))
-- Hom-left : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
--   (A : Category.Obj (Op ℂ)) →
--   (F : Functor (Op 𝔻) ℂ) →
--   Functor (Op 𝔻) (Agda {ℓ₁} {ℓ₂})
-- Hom-left {_} {_} {_} {_} {ℂ} {𝔻} c F =
--   record
--     { act = λ x → (c ⇒[ ℂ ] (actf F x))
--     ; fmap′ = λ A B f → lift λ t → Functor.fmap F f ∘[ ℂ ] t
--     ; fmap-id′ = λ A → {!!}
--     ; fmap-∘′ = λ A B C f g → {!!}
--     }

-- -- Called "lîm" on nlab
-- PreLim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {I : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
--   (F : Functor (Op I) ℂ) →
--   Category.Obj ℂ →
--   Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc (lsuc ℓ₂))
-- PreLim {_} {_} {_} {_} {I} {ℂ} F c =
--   Hom [ Op I ,, Agda ] Point (Hom-left c F)

-- PreLim-Functor : ∀ {o₁ ℓ₁ o₂ ℓ₂} {I : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
--   (F : Functor (Op I) ℂ) →
--   Functor ℂ Agda
-- PreLim-Functor = {!!}

-- Is-Lim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {I : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
--   {F : Functor (Op I) ℂ} →
--   {c : Category.Obj ℂ} →
--   (limF : PreLim F c) →
--   Set {!!}
-- Is-Lim {_} {_} {_} {_} {I} {ℂ} {F} {c} limF =
--   {!!}
--   -- Σ (NatIso (Hom ? c ?) ?) ?

-- -- Lim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
-- --   Functor ℂ 𝔻 →
-- --   Set {!!}
-- -- Lim {_} {_} {_} {_} {ℂ} {𝔻} F =
-- --   ∃[ c ]
-- --   Σ (Cone F c) λ cone →
-- --   ∀ c′ (cone′ : Cone F c′) →
-- --   Σ![ c′ ⇒[ 𝔻 ] c ] (Is-NatIso ? ? cone)

-- -- HasLimit : ∀ {o₁ ℓ₁ o₂ ℓ₂} {J : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
-- --   (Lim-D : Cone F )

-- -- Cone-Cat : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
-- --   Functor (Op ℂ) 𝔻 →
-- --   Category.Obj 𝔻 →
-- --   Category {!!} {!!}
-- -- Cone-Cat {_} {_} {_} {_} {ℂ} {𝔻} F c =
-- --   record
-- --     { Obj = Cone F c
-- --     ; _⇒_ = λ A B → {!!}
-- --     ; _∘_ = {!!}
-- --     ; id = {!!}
-- --     ; left-id = {!!}
-- --     ; right-id = {!!}
-- --     ; ∘-assoc = {!!}
-- --     }

