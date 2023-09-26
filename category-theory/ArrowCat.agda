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

module ArrowCat
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

-- Comma category
_↓_ : ∀ {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃} →
  {𝔸 : Category o₁ ℓ₁} →
  {𝔹 : Category o₂ ℓ₂} →
  {ℂ : Category o₃ ℓ₃} →
  (S : Functor 𝔸 ℂ)
  (T : Functor 𝔹 ℂ) →
  Category (o₁ ⊔ o₂ ⊔ ℓ₃) ℓ₃
_↓_ {o₁} {ℓ₁} {o₂} {ℓ₂} {o₃} {ℓ₃} {𝔸} {𝔹} {ℂ} S T =
  record
    { Obj = Obj₀
    ; _⇒_ = _⇒₀_
    ; _∘_ = _∘₀_
    ; id = (Category.id ℂ , Category.id ℂ) , trans (Category.right-id ℂ) (sym (Category.left-id ℂ))
    ; left-id = left-id-def
    ; right-id = right-id-def
    ; ∘-assoc = ∘-assoc-def
    }
    where
      Obj₀ : Set (o₁ ⊔ o₂ ⊔ ℓ₃)
      Obj₀ = Σ (Category.Obj 𝔸 × Category.Obj 𝔹) λ (A , B) →  (actf S A ⇒[ ℂ ] actf T B)

      -- _⇒₀_ : {!!} -- Obj₀ → Obj₀ → Set ℓ
      _⇒₀_ = λ ((A₁ , B₁) , f) ((A₂ , B₂) , g) →
        Σ ((actf T B₂ ⇒[ ℂ ] actf T B₁) × (actf S A₂ ⇒[ ℂ ] actf S A₁)) λ (a , b) →
        (ElementaryProperties.CSquare ℂ f a b g)

      _∘₀_ : {A B C : Obj₀} → B ⇒₀ C → A ⇒₀ B → A ⇒₀ C
      _∘₀_ {A} {B} {C} f g =
        let
          (A₁ , A₂) , A-f = A
          (B₁ , B₂) , B-f = B
          (C₁ , C₂) , C-f = C

          (f₁ , f₂) , f₃ = f
          (g₁ , g₂) , g₃ = g

          p = g₁ ∘[ ℂ ] f₁
          q = g₂ ∘[ ℂ ] f₂
        in
        (p , q) , ElementaryProperties.CSquare-vert-comp ℂ f₃ g₃

      left-id-def : {A B : Obj₀} {f : A ⇒₀ B} →
                    (((Category.id ℂ , Category.id ℂ) ,
                      trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
                    ∘₀ f)
                    ≡ f
      left-id-def {A} {B} {f} =
        let
            f1 = proj₁ (proj₁ f)
            f2 = proj₂ (proj₁ f)

            ∘-app = _∘₀_ ((Category.id ℂ , Category.id ℂ) ,
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
        in
        Inverse.f Σ-≡,≡↔≡ (p1 , (uip _ (proj₂ f)))

      right-id-def : ∀ {A B : Obj₀} {f : A ⇒₀ B} →
                    _∘₀_ f
                    ((Category.id ℂ , Category.id ℂ) ,
                    trans (Category.right-id ℂ) (sym (Category.left-id ℂ)))
                    ≡ f
      right-id-def {A} {B} {f} =
        let
            f1 = proj₁ (proj₁ f)
            f2 = proj₂ (proj₁ f)

            ∘-app = _∘₀_ f ((Category.id ℂ , Category.id ℂ) ,
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
            _∘₀_ (_∘₀_ f g) h ≡ _∘₀_ f (_∘₀_ g h)
      ∘-assoc-def {A} {B} {C} {D} {f} {g} {h} =
        let
          f1 = proj₁ (proj₁ f)
          f2 = proj₂ (proj₁ f)

          g1 = proj₁ (proj₁ g)
          g2 = proj₂ (proj₁ g)

          h1 = proj₁ (proj₁ h)
          h2 = proj₂ (proj₁ h)

          ∘-app-1 = _∘₀_ (_∘₀_ f g) h
          ∘-app-2 = _∘₀_ f (_∘₀_ g h)

          ∘-1-fst = proj₁ (proj₁ ∘-app-1)
          ∘-1-snd = proj₂ (proj₁ ∘-app-1)

          ∘-2-fst = proj₁ (proj₁ ∘-app-2)
          ∘-2-snd = proj₂ (proj₁ ∘-app-2)

          fg-1 : proj₁ (proj₁ (_∘₀_ f g)) ≡ (g1 ∘[ ℂ ] f1)
          fg-1 = refl

          fg-2 : proj₂ (proj₁ (_∘₀_ f g)) ≡ (g2 ∘[ ℂ ] f2)
          fg-2 = refl

          gh-1 : proj₁ (proj₁ (_∘₀_ g h)) ≡ (h1 ∘[ ℂ ] g1)
          gh-1 = refl

          gh-2 : proj₂ (proj₁ (_∘₀_ g h)) ≡ (h2 ∘[ ℂ ] g2)
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

        in
        Inverse.f Σ-≡,≡↔≡ (proj₁-eq , uip _ (proj₂ ∘-app-2))

Arrow-Cat : ∀ {o ℓ} → Category o ℓ → Category (o ⊔ ℓ) ℓ
Arrow-Cat {o} {ℓ} ℂ = Id-Functor {_} {_} {ℂ} ↓ Id-Functor

-- Arrow-Cat : ∀ {o ℓ} → Category o ℓ → Category (lsuc o Level.⊔ lsuc ℓ Level.⊔ lsuc lzero) (lsuc lzero Level.⊔ lsuc lzero Level.⊔ lsuc o Level.⊔ lsuc ℓ)
-- Arrow-Cat ℂ = [ Interval-Cat ,, ℂ ]
