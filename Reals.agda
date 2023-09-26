open import Data.Nat
open import Data.Rational hiding (NonZero)
open import Data.Rational.Unnormalised.Base using (_≢0)
open import Data.Integer using (ℤ)
open import Data.Nat.Base using (NonZero)
open import Data.Unit renaming (⊤ to Unit)

open import Data.Product
open import Data.Sum

open import Relation.Nullary

open ℤ using (pos)

module Reals
  where

max : ℕ → ℕ → ℕ
max x y with x Data.Nat.>? y
... | yes p = x
... | no ¬p = y

recip : (x : ℕ) → {{nz : x ≢0}} → ℚ
recip x {{nz}} = _/_ (pos 1) x {nz}

_⁻¹ : (x : ℕ) → {{nz : x ≢0}} → ℚ
_⁻¹ = recip

-- https://stackoverflow.com/questions/28404520/how-to-define-real-number-in-agda
record ℝ : Set where
  constructor Real
  field
    f : ℕ → ℚ
    reg : {n m : ℕ} → {{p : suc m ≢0}} →
      ∣ (f n - f m) ∣ Data.Rational.≤ (recip (suc n) Data.Rational.+ recip (suc m))

abs< : (ε⁻¹ : ℕ) → {{nz : ε⁻¹ ≢0}} → ℝ → ℝ → Set
abs< ε⁻¹ x y = ∃[ p ] (∣ (ℝ.f x p - ℝ.f y p) ∣) Data.Rational.< recip ε⁻¹

-- The numbers are "as close as you want" to each other
_==_ : ℝ → ℝ → Set
_==_ x y = ∀ (ε⁻¹ : ℕ) {{_ : ε⁻¹ ≢0}} → ∃[ n ] ∀ m → m Data.Nat.> n → (∣ (ℝ.f x m - ℝ.f y m) ∣) Data.Rational.< recip ε⁻¹

Seq : Set → Set → Set
Seq X A = X → A

ℝ-Seq : Set → Set
ℝ-Seq X = Seq X ℝ

NonEmpty : Set → Set
NonEmpty A = Unit → A

record Direction (A : Set) : Set₁ where
  field
    point : NonEmpty A
    _≻_ : A → A → Set
    trans : ∀ {x y z} → x ≻ y → y ≻ z → x ≻ z
    upper-bound : ∀ x y → ∃[ z ] ((z ≻ x) × (z ≻ y))


-- Final segment (See Beardon's book on limits)
_∙_ : ∀ {A} → Direction A → A → Set
_∙_ dir w = ∃[ x ] (x ≻ w)
  where
    open Direction dir

NonEmpty∙ : ∀ {A w} → (dir : Direction A) → NonEmpty (dir ∙ w)
NonEmpty∙ {A} {w} dir = λ _ →
  let y , y≻w , _ = upper-bound w w
  in
  y , y≻w
  where
    open Direction dir

Direction∙ : ∀ {A w} → (dir : Direction A) → Direction (dir ∙ w)
Direction∙ dir =
  record
    { point = NonEmpty∙ dir
    ; _≻_ = λ x y → proj₁ x ≻ proj₁ y
    ; trans = trans
    ; upper-bound = λ x y →
        let z , z≻x , z≻y = upper-bound (proj₁ x) (proj₁ y)
            _ , x≻w = x
        in
        (z , trans z≻x x≻w) , (z≻x , z≻y)
    }
  where
    open Direction dir

Subset : Set → Set₁
Subset A = A → Set

_⊆_ : ∀ {A} → Subset A → Subset A → Set
_⊆_ P Q = ∀ a → P a → Q a

_∪_ : ∀ {A} → Subset A → Subset A → Subset A
_∪_ P Q = λ a → P a ⊎ Q a

_∩_ : ∀ {A} → Subset A → Subset A → Subset A
_∩_ P Q = λ a → P a × Q a

_s∙_ : ∀ {A} → Direction A → A → Subset A
_s∙_ dir w = λ x → x ≻ w
  where
    open Direction dir

module _ (A : Set) (dir : Direction A) where
  open Direction dir

  almost-every : (A → Set) → Set
  almost-every P =
    ∃[ x₀ ] ∀ x → x ≻ x₀ → P x

  antitone∙ : ∀ {x y} → x ≻ y → (dir s∙ x) ⊆ (dir s∙ y)
  antitone∙ = λ p a q → trans q p

  ∩∙ : ∀ {x y} →
    ∃[ z ]
      (dir s∙ z)
        ⊆
      ((dir s∙ x) ∩ (dir s∙ y))
  ∩∙ {x} {y} =
    let z , z≻x , z≻y = upper-bound x y
    in
    z , λ a p → trans p z≻x , trans p z≻y

  both : (A → Set) → (A → Set) → A → Set
  both P Q a = P a × Q a

  almost-every∧ : ∀ {P Q} → almost-every P → almost-every Q → almost-every (both P Q)
  almost-every∧ (x-P , p) (x-Q , q) =
    let z , z≻x-P , z≻x-Q = upper-bound x-P x-Q
    in
    z , λ x x₁ → p x (trans x₁ z≻x-P) , q x (trans x₁ z≻x-Q)

  data Lim (f : ℝ-Seq A) : ℝ → Set where
    mk-Lim : ∀ {α ε} {{_ : ε ≢0}} →
      (∃[ x₀ ] ∀ x →
        x ≻ x₀ →
        abs< ε (f x) α) →
      Lim f α

  Lim-unique : ∀ {f} {α β} →
    Lim f α →
    Lim f β →
    α == β
  Lim-unique (mk-Lim {ε = ε₁} (fst , snd)) (mk-Lim {ε = ε₂} (fst₁ , snd₁)) =
    λ ε⁻¹ →
      max ε₁ ε₂ , λ m x → *<* {!!}

