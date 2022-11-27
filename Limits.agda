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

Arrow-Cat : ∀ {o ℓ} → Category o ℓ → Category (o ⊔ ℓ) ℓ
Arrow-Cat {o} {ℓ} ℂ =
  record
    { Obj = Obj₀
    ; _⇒_ = _⇒₀_
    ; _∘_ = ∘-def
    ; id = (Category.id ℂ , Category.id ℂ) , trans (Category.right-id ℂ) (sym (Category.left-id ℂ))
    ; left-id = left-id-def
    ; right-id = right-id-def
    ; ∘-assoc = ∘-assoc-def
    }
    where
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

            f-prf = proj₂ f
            ∘-prf = proj₂ ∘-app
            p-left = subst
                (λ x →
                  ElementaryProperties.CSquare ℂ (proj₂ A) (proj₁ x)
                  (proj₂ x) (proj₂ B))
                (trans
                  (case (Category.right-id ℂ {(proj₂ (proj₁ B))} {(proj₂ (proj₁ A))} {f1} , Category.right-id ℂ {(proj₁ (proj₁ B))} {(proj₁ (proj₁ A))} {f2}) of
                    λ { (p₁ , p₂) → Inverse.f ×-≡,≡↔≡ (p₁ , p₂) })
                  refl)
                (ElementaryProperties.CSquare-vert-comp ℂ
                (trans (Category.right-id ℂ) (sym (Category.left-id ℂ))) (proj₂ f))

        in
        Inverse.f Σ-≡,≡↔≡ (p1 , (uip p-left (proj₂ f)))

      right-id-def : ∀ {A B : Obj₀} {f : A ⇒₀ B} →
                    ∘-def f
                    ((Category.id ℂ , Category.id ℂ) ,
                    trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
                    ≡ f
      right-id-def {A} {B} {f} =
        let
            f1 = proj₁ (proj₁ f)
            f2 = proj₂ (proj₁ f)

            ∘-app = ∘-def f ((Category.id ℂ , Category.id ℂ) ,
                      trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
                      -- f

            p : ∘-app ≡ (((Category.id ℂ ∘[ ℂ ] f1) , (Category.id ℂ ∘[ ℂ ] f2)) ,
                   ElementaryProperties.CSquare-vert-comp ℂ
                     (proj₂ f)
                     (trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
                  )
            p = refl

            p′ : ∀ {X Y X′ Y′} {h : X ⇒[ ℂ ] Y} {h′ : X′ ⇒[ ℂ ] Y′} → ((Category.id ℂ ∘[ ℂ ] h) , (Category.id ℂ ∘[ ℂ ] h′)) ≡ (h , h′)
            p′ = Inverse.f ×-≡,≡↔≡ (Category.left-id ℂ , Category.left-id ℂ)

            p1 : proj₁ ∘-app
                  ≡ proj₁ f
            p1 =
               let z , _ = Inverse.f⁻¹ Σ-≡,≡↔≡ p
               in
               trans z (trans p′ refl)
        in
        Inverse.f Σ-≡,≡↔≡ (p1 , (uip _ (proj₂ f)))

      ∘-assoc-def : ∀ {A B C D : Obj₀} {f : C ⇒₀ D} {g : B ⇒₀ C} {h : A ⇒₀ B} →
            ∘-def (∘-def f g) h ≡ ∘-def f (∘-def g h)
      ∘-assoc-def {A} {B} {C} {D} {f} {g} {h} =
        let
          f1 = proj₁ (proj₁ f)
          f2 = proj₂ (proj₁ f)

          g1 = proj₁ (proj₁ g)
          g2 = proj₂ (proj₁ g)

          h1 = proj₁ (proj₁ h)
          h2 = proj₂ (proj₁ h)

          ∘-app-1 = ∘-def (∘-def f g) h
          ∘-app-2 = ∘-def f (∘-def g h)

          ∘-1-fst = proj₁ (proj₁ ∘-app-1)
          ∘-1-snd = proj₂ (proj₁ ∘-app-1)

          ∘-2-fst = proj₁ (proj₁ ∘-app-2)
          ∘-2-snd = proj₂ (proj₁ ∘-app-2)

          fg-1 : proj₁ (proj₁ (∘-def f g)) ≡ (g1 ∘[ ℂ ] f1)
          fg-1 = refl

          fg-2 : proj₂ (proj₁ (∘-def f g)) ≡ (g2 ∘[ ℂ ] f2)
          fg-2 = refl

          gh-1 : proj₁ (proj₁ (∘-def g h)) ≡ (h1 ∘[ ℂ ] g1)
          gh-1 = refl

          gh-2 : proj₂ (proj₁ (∘-def g h)) ≡ (h2 ∘[ ℂ ] g2)
          gh-2 = refl

          p-1 : proj₁ (proj₁ ∘-app-1) ≡ (h1 ∘[ ℂ ] (g1 ∘[ ℂ ] f1) )
          p-1 = refl

          p-2 : proj₂ (proj₁ ∘-app-1) ≡ (h2 ∘[ ℂ ] (g2 ∘[ ℂ ] f2) )
          p-2 = refl

          q-1 : proj₁ (proj₁ ∘-app-2) ≡ (((h1 ∘[ ℂ ] g1) ∘[ ℂ ] f1))
          q-1 = refl

          q-2 : proj₂ (proj₁ ∘-app-2) ≡ (((h2 ∘[ ℂ ] g2) ∘[ ℂ ] f2))
          q-2 = refl


          p-1-eq : proj₁ (proj₁ ∘-app-1) ≡ proj₁ (proj₁ ∘-app-2)
          p-1-eq = trans p-1 (sym (Category.∘-assoc ℂ))

          p-2-eq : proj₂ (proj₁ ∘-app-1) ≡ proj₂ (proj₁ ∘-app-2)
          p-2-eq = trans p-2 (sym (Category.∘-assoc ℂ))

          proj₁-eq : proj₁ ∘-app-1 ≡ proj₁ ∘-app-2
          proj₁-eq = Inverse.f ×-≡,≡↔≡ (p-1-eq , p-2-eq)

          prf-2 = subst
                (λ x →
                  ElementaryProperties.CSquare ℂ (proj₂ A) (proj₁ x)
                  (proj₂ x) (proj₂ D))
                (case (sym (Category.∘-assoc ℂ {_} {_} {_} {_} {h1} {g1} {f1}) , trans refl (sym (Category.∘-assoc ℂ {_} {_} {_} {_} {h2} {g2} {f2}))) of
                  λ { (p₁ , p₂) → Inverse.f ×-≡,≡↔≡ (p₁ , p₂) })
                (ElementaryProperties.CSquare-vert-comp ℂ (proj₂ (∘-def f g))
                (proj₂ h))

        in
        Inverse.f Σ-≡,≡↔≡ (proj₁-eq , uip prf-2 (proj₂ ∘-app-2))


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
  ∃[ p⁻¹ ]
    (ElementaryProperties.Iso 𝔻 p p⁻¹)

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

