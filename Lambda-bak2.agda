-- Based on "Data Types as Lattices" by Dana Scott

open import Data.Nat
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Data.List hiding (head; tail)
open import Data.Maybe

open import Function

-- open import Data.Nat.Tactic.RingSolver

open import Data.Nat.Solver
open +-*-Solver using (solve; _:*_; _:+_; _:^_; con; _:=_)

open import Data.Nat.Binary renaming (suc to ℕᵇ-suc) hiding (_*_; _+_)

module Lambda where

data Bit : Set where
  O : Bit
  I : Bit

fromBit : Bit → ℕ
fromBit O = zero
fromBit I = 1

infixl 5 _,,_

data Bits : Set where
  B : Bit → Bits
  _,,_ : Bits → Bit → Bits

data Has-One : Bits → Set where
  Has-One-I : Has-One (B I)
  Has-One-Here : ∀ {x} →
    Has-One (x ,, I)
  Has-One-There : ∀ {x} →
    Has-One x →
    Has-One (x ,, O)

-- Turn any representation of 0 into its canonical representation
normalize : Bits → Bits
normalize (B O) = B O
normalize (B I) = B I
normalize (b ,, O) = normalize b ,, O
normalize (b ,, I) = b ,, I

normalize-Has-One : ∀ {x} →
  Has-One x →
  normalize x ≡ x
normalize-Has-One Has-One-I = refl
normalize-Has-One Has-One-Here = refl
normalize-Has-One (Has-One-There prf) rewrite normalize-Has-One prf = refl

Bits-suc : Bits → Bits
Bits-suc (B O) = B I
Bits-suc (B I) = B I ,, O
Bits-suc (b ,, O) = b ,, I
Bits-suc (b ,, I) = Bits-suc b ,, O

Bits-suc-Has-One : ∀ {x} →
  Has-One (Bits-suc x)
Bits-suc-Has-One {B O} = Has-One-I
Bits-suc-Has-One {B I} = Has-One-There Has-One-I
Bits-suc-Has-One {x ,, O} = Has-One-Here
Bits-suc-Has-One {x ,, I} = Has-One-There Bits-suc-Has-One

toBits : ℕᵇ → Bits
toBits zero = B O
toBits 2[1+ n ] = Bits-suc (toBits n) ,, O
toBits 1+[2 n ] = Bits-suc (toBits n ,, O)

fromBits : Bits → ℕᵇ
fromBits (B O) = zero
fromBits (B I) = 1+[2 zero ]
fromBits (b ,, O) = double (fromBits b)
fromBits (b ,, I) = 1+[2 fromBits b ]

ℕ→Bits : ℕ → Bits
ℕ→Bits = toBits ∘ fromℕ

Bits→ℕ : Bits → ℕ
Bits→ℕ = toℕ ∘ fromBits

fromBits-suc : ∀ {x} →
  double (fromBits (Bits-suc x)) ≡ 2[1+ fromBits x ]
fromBits-suc {B O} = refl
fromBits-suc {B I} = refl
fromBits-suc {x ,, O} = refl
fromBits-suc {x ,, I} rewrite (fromBits-suc {x}) = refl

fromBits-toBits : ∀ {x : ℕᵇ} →
  fromBits (toBits x) ≡ x
fromBits-toBits {zero} = refl
fromBits-toBits {2[1+ x ]} rewrite fromBits-suc {toBits x} | fromBits-toBits {x} = refl
fromBits-toBits {1+[2 x ]} rewrite fromBits-toBits {x} = refl

fromBits-normalize : ∀ {x} →
  fromBits x ≡ fromBits (normalize x)
fromBits-normalize {B O} = refl
fromBits-normalize {B I} = refl
fromBits-normalize {x ,, O} rewrite fromBits-normalize {x} = refl
fromBits-normalize {x ,, I} = refl

normalize-Bits-suc : ∀ {x} →
  normalize (Bits-suc x) ≡ Bits-suc x
normalize-Bits-suc {x} rewrite normalize-Has-One (Bits-suc-Has-One {x}) = refl

normalize-idem : ∀ {x} →
  normalize (normalize x) ≡ normalize x
normalize-idem {B O} = refl
normalize-idem {B I} = refl
normalize-idem {x ,, O} rewrite normalize-idem {x} = refl
normalize-idem {x ,, I} = refl

-- Bits-suc-normalize-comm : ∀ {x} →
--   Bits-suc (normalize x) ≡ normalize (Bits-suc x)
-- Bits-suc-normalize-comm {x} rewrite normalize-Bits-suc {x} = {!!}
-- Bits-suc-normalize {B O} = refl
-- Bits-suc-normalize {B I} = refl
-- Bits-suc-normalize {x ,, O} = {!!}
-- Bits-suc-normalize {x ,, I} rewrite normalize-Has-One (Bits-suc-Has-One {x ,, I}) = refl

-- Bits-suc-normalize {B O} = refl
-- Bits-suc-normalize {B I} = refl
-- Bits-suc-normalize {x ,, O} = {!!}
-- Bits-suc-normalize {x ,, I} rewrite sym (Bits-suc-normalize {x}) = {!!}

toBits-normalize : ∀ {x} →
  toBits x ≡ normalize (toBits x)
toBits-normalize {zero} = refl
toBits-normalize {2[1+ x ]} rewrite toBits-normalize {x} | normalize-Bits-suc {normalize (toBits x)} = refl
toBits-normalize {1+[2 x ]} = refl

is-normal : (Bits → Bits) → Set
is-normal f =
  ∀ x → f (normalize x) ≡ normalize (f (normalize x))

Bits-lift : (f : Bits → Bits) → (ℕ → ℕ)
Bits-lift f = Bits→ℕ ∘ f ∘ ℕ→Bits

Bits-lower : (ℕ → ℕ) → (Bits → Bits)
Bits-lower f = ℕ→Bits ∘ f ∘ Bits→ℕ

Bits-transport : ((Bits → Bits) → Set) → ((ℕ → ℕ) → Set)
Bits-transport P = P ∘ Bits-lower

-- toBits-fromBits-normalize : ∀ {x : Bits} →
--   toBits

-- fromBits : Bits → ℕ
-- fromBits (B x) = fromBit x
-- fromBits (b ,, x) = fromBit x + 2 * (fromBits b)

-- toBits : ℕ → Bits
-- toBits zero = B O
-- toBits (suc n) = Bits-suc (toBits n)

-- _ : fromBits (toBits 4) ≡ 4
-- _ = refl

-- _ : fromBits (toBits 11) ≡ 11
-- _ = refl

-- fromBits-suc : ∀ {x m} →
--   fromBits x ≡ m →
--   fromBits (Bits-suc x) ≡ suc m
-- fromBits-suc {B O} {.(fromBits (B O))} refl = refl
-- fromBits-suc {B I} {.(fromBits (B I))} refl = refl
-- fromBits-suc {x ,, O} {.(fromBits (x ,, O))} refl = refl
-- fromBits-suc {x ,, I} {.(fromBits (x ,, I))} refl with fromBits-suc {x} {fromBits x} refl
-- ... | eq rewrite eq =
--   solve 1 (λ z → (con 1 :+ z) :+ ((con 1 :+ z) :+ con 0) := con 1 :+ (con 1 :+ (z :+ (z :+ con 0)))) refl (fromBits x)

-- fromBits-toBits : ∀ {n} →
--   fromBits (toBits n) ≡ n
-- fromBits-toBits {zero} = refl
-- fromBits-toBits {suc n} rewrite fromBits-suc {toBits n} refl = cong suc (fromBits-toBits {n})

-- -- shiftBits : ∀ {m} →
-- --   toBits (m + m) ≡ toBits m ,, O
-- -- shiftBits {zero} = {!!}
-- -- shiftBits {suc m} = {!!}

-- toBits-fromBits : ∀ {x} →
--   toBits (fromBits x) ≡ x
-- toBits-fromBits {B O} = refl
-- toBits-fromBits {B I} = refl
-- toBits-fromBits {x ,, O} rewrite sym (toBits-fromBits {x}) =
--   let eq = toBits-fromBits {x}
--   in {!!}
-- toBits-fromBits {x ,, I} = {!!}

singleton-Bits : ℕ → ℕᵇ
singleton-Bits zero = 1+[2 zero ]
singleton-Bits (ℕ.suc n) = double (singleton-Bits n)

split : ℕᵇ → Maybe Bit × ℕᵇ
split zero     = nothing , zero
split 2[1+ n ] = just O , n
split 1+[2 n ] = just I , n

head : ℕᵇ → Maybe Bit
head = proj₁ ∘ split

tail : ℕᵇ → ℕᵇ
tail = proj₂ ∘ split

-- singleton

-- singleton-Bits : ℕ → Bits
-- singleton-Bits zero = B I
-- singleton-Bits (suc n) = singleton-Bits n ,, O

singleton : ℕ → ℕ
singleton n = toℕ (singleton-Bits n)

_ : singleton 3 ≡ 8
_ = refl

_ : singleton 11 ≡ (2 ^ 11)
_ = refl

singleton-suc : ∀ {n} →
  singleton (suc n) ≡ singleton n + singleton n
singleton-suc {zero} = refl
-- singleton-suc {suc n} rewrite singleton-suc {n} = {!!}
singleton-suc {suc n} = {!!}

-- singleton^ : ∀ {n} →
--   singleton n ≡ 2 ^ n
-- singleton^ {zero} = refl
-- singleton^ {suc n} rewrite singleton-suc {n} | singleton^ {n} = refl

-- data Divides : ℕ → ℕ → Set where
--   mk-Divides : ∀ {m n k} →
--     m ≡ (n * k) →
--     Divides m n

-- _∈_ : ℕ → ℕ → Set
-- _∈_ n x = Divides (2 ^ n) x

-- -- _ : 3 ∈ ((2 ^ 7) )

-- -- -- From https://git8.cs.fau.de/software/duration-monad-agda/-/blob/master/Cantor.agda
-- -- ⟨_,_⟩ : ℕ → ℕ → ℕ
-- -- ⟨_,_⟩ 0 0 = 0
-- -- -- ⟨_,_⟩ 0 (suc m) = ⟨ 0 , m ⟩ + suc m + 1
-- -- ⟨_,_⟩ 0 (suc m) = suc (suc (⟨ 0 , m ⟩ + m))
-- -- ⟨_,_⟩ (suc n) m = suc (⟨ n , m ⟩ + (n + m))

-- -- pair-lemma : ∀ {b} → suc (suc ⟨ 0 , b ⟩ + b) ≡ ⟨ 0 , suc b ⟩
-- -- pair-lemma {zero} = refl
-- -- pair-lemma {suc b} = refl

-- -- -- inverses
-- -- π₂⁻¹ π₁⁻¹ : ℕ → ℕ

-- -- π₂⁻¹ 0 = 0
-- -- π₂⁻¹ (suc n) with (π₁⁻¹ n)
-- -- π₂⁻¹ (suc n) | zero  = 0
-- -- π₂⁻¹ (suc n) | suc _ = suc (π₂⁻¹ n)

-- -- π₁⁻¹ 0 = 0
-- -- π₁⁻¹ (suc n) with (π₁⁻¹ n)
-- -- π₁⁻¹ (suc n) | zero = suc (π₂⁻¹ n)
-- -- π₁⁻¹ (suc n) | suc m = m

-- -- pair-suc : ∀ (n m : ℕ) → ⟨ n , (suc m) ⟩ ≡ suc ⟨ (suc n) , m ⟩
-- -- pair-suc = {!!}


-- -- h₁ : ∀ (n k : ℕ) → (k ≤ n) → π₁⁻¹ ⟨ n + k , 0 ⟩ ≡ n ∸ k
-- -- h₁ = {!!}

-- -- data Proj₁-helper : ℕ → Set where
-- --   Proj₁-helper-0 : ∀ {b} →
-- --     Proj₁-helper ⟨ 0 , b ⟩

-- --   Proj₁-helper-s : ∀ {n} →
-- --     Proj₁-helper n →
-- --     Proj₁-helper (suc n)


-- -- proj₁-lemma : ∀ {b} → Proj₁-helper b → π₁⁻¹ b ≡ 0

-- -- π₁-lemma′ : ∀ {b} → π₁⁻¹ ⟨ 0 , b ⟩ ≡ 0
-- -- π₁-lemma′ {zero} = refl
-- -- π₁-lemma′ {suc b} = {!!} --proj₁-lemma {!!}

-- -- proj₁-lemma {.(⟨ 0 , _ ⟩)} Proj₁-helper-0 = {!!}
-- -- proj₁-lemma {.(suc _)} (Proj₁-helper-s prf) = {!!}

-- -- -- π₁-lemma′ : ∀ {b} → π₁⁻¹ (suc (suc ⟨ 0 , b ⟩ + b)) ≡ 0
-- -- -- π₁-lemma′ {zero} = refl
-- -- -- π₁-lemma′ {suc b} = {!!}

-- -- -- π₁-lemma′ {zero} = refl
-- -- -- π₁-lemma′ {suc b} rewrite (pair-lemma {b}) | π₁-lemma′ {b} =
-- -- --   let p = π₁-lemma′ {b}
-- -- --   in
-- -- --   {!!}

-- -- -- π₁-lemma : ∀ {b} → π₁⁻¹ ⟨ 0 , b ⟩ ≡ 0
-- -- -- π₁-lemma {zero} = refl
-- -- -- π₁-lemma {suc b} = π₁-lemma′ {b}


-- -- -- pair-inv₁ : ∀ {a b} → π₁⁻¹ ⟨ a , b ⟩ ≡ a
-- -- -- pair-inv₁ {zero} {zero} = refl
-- -- -- pair-inv₁ {zero} {suc b} = π₁-lemma {suc b} --π₁-lemma {suc b}
-- -- -- pair-inv₁ {suc a} {b} = {!!}
