-- Based on "Data Types as Lattices" by Dana Scott

open import Data.Nat
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Data.List

-- open import Data.Nat.Tactic.RingSolver

open import Data.Nat.Solver
open +-*-Solver using (solve; _:*_; _:+_; _:^_; con; _:=_)

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

Bits-suc : Bits → Bits
Bits-suc (B O) = B I
Bits-suc (B I) = B I ,, O
Bits-suc (b ,, O) = b ,, I
Bits-suc (b ,, I) = Bits-suc b ,, O

fromBits : Bits → ℕ
fromBits (B x) = fromBit x
fromBits (b ,, x) = fromBit x + 2 * (fromBits b)

toBits : ℕ → Bits
toBits zero = B O
toBits (suc n) = Bits-suc (toBits n)

_ : fromBits (toBits 4) ≡ 4
_ = refl

_ : fromBits (toBits 11) ≡ 11
_ = refl

fromBits-suc : ∀ {x m} →
  fromBits x ≡ m →
  fromBits (Bits-suc x) ≡ suc m
fromBits-suc {B O} {.(fromBits (B O))} refl = refl
fromBits-suc {B I} {.(fromBits (B I))} refl = refl
fromBits-suc {x ,, O} {.(fromBits (x ,, O))} refl = refl
fromBits-suc {x ,, I} {.(fromBits (x ,, I))} refl with fromBits-suc {x} {fromBits x} refl
... | eq rewrite eq =
  solve 1 (λ z → (con 1 :+ z) :+ ((con 1 :+ z) :+ con 0) := con 1 :+ (con 1 :+ (z :+ (z :+ con 0)))) refl (fromBits x)

fromBits-toBits : ∀ {n} →
  fromBits (toBits n) ≡ n
fromBits-toBits {zero} = refl
fromBits-toBits {suc n} rewrite fromBits-suc {toBits n} refl = cong suc (fromBits-toBits {n})

-- shiftBits : ∀ {m} →
--   toBits (m + m) ≡ toBits m ,, O
-- shiftBits {zero} = {!!}
-- shiftBits {suc m} = {!!}

toBits-fromBits : ∀ {x} →
  toBits (fromBits x) ≡ x
toBits-fromBits {B O} = refl
toBits-fromBits {B I} = refl
toBits-fromBits {x ,, O} rewrite sym (toBits-fromBits {x}) =
  let eq = toBits-fromBits {x}
  in {!!}
toBits-fromBits {x ,, I} = {!!}

singleton-Bits : ℕ → Bits
singleton-Bits zero = B I
singleton-Bits (suc n) = singleton-Bits n ,, O

singleton : ℕ → ℕ
singleton n = fromBits (singleton-Bits n)

_ : singleton 3 ≡ 8
_ = refl

_ : singleton 11 ≡ (2 ^ 11)
_ = refl

singleton-suc : ∀ {n} →
  singleton (suc n) ≡ 2 * singleton n
singleton-suc {zero} = refl
singleton-suc {suc n} = refl

singleton^ : ∀ {n} →
  singleton n ≡ 2 ^ n
singleton^ {zero} = refl
singleton^ {suc n} rewrite singleton-suc {n} | singleton^ {n} = refl

data Divides : ℕ → ℕ → Set where
  mk-Divides : ∀ {m n k} →
    m ≡ (n * k) →
    Divides m n

_∈_ : ℕ → ℕ → Set
_∈_ n x = Divides (2 ^ n) x

-- _ : 3 ∈ ((2 ^ 7) )

-- -- From https://git8.cs.fau.de/software/duration-monad-agda/-/blob/master/Cantor.agda
-- ⟨_,_⟩ : ℕ → ℕ → ℕ
-- ⟨_,_⟩ 0 0 = 0
-- -- ⟨_,_⟩ 0 (suc m) = ⟨ 0 , m ⟩ + suc m + 1
-- ⟨_,_⟩ 0 (suc m) = suc (suc (⟨ 0 , m ⟩ + m))
-- ⟨_,_⟩ (suc n) m = suc (⟨ n , m ⟩ + (n + m))

-- pair-lemma : ∀ {b} → suc (suc ⟨ 0 , b ⟩ + b) ≡ ⟨ 0 , suc b ⟩
-- pair-lemma {zero} = refl
-- pair-lemma {suc b} = refl

-- -- inverses
-- π₂⁻¹ π₁⁻¹ : ℕ → ℕ

-- π₂⁻¹ 0 = 0
-- π₂⁻¹ (suc n) with (π₁⁻¹ n)
-- π₂⁻¹ (suc n) | zero  = 0
-- π₂⁻¹ (suc n) | suc _ = suc (π₂⁻¹ n)

-- π₁⁻¹ 0 = 0
-- π₁⁻¹ (suc n) with (π₁⁻¹ n)
-- π₁⁻¹ (suc n) | zero = suc (π₂⁻¹ n)
-- π₁⁻¹ (suc n) | suc m = m

-- pair-suc : ∀ (n m : ℕ) → ⟨ n , (suc m) ⟩ ≡ suc ⟨ (suc n) , m ⟩
-- pair-suc = {!!}


-- h₁ : ∀ (n k : ℕ) → (k ≤ n) → π₁⁻¹ ⟨ n + k , 0 ⟩ ≡ n ∸ k
-- h₁ = {!!}

-- data Proj₁-helper : ℕ → Set where
--   Proj₁-helper-0 : ∀ {b} →
--     Proj₁-helper ⟨ 0 , b ⟩

--   Proj₁-helper-s : ∀ {n} →
--     Proj₁-helper n →
--     Proj₁-helper (suc n)


-- proj₁-lemma : ∀ {b} → Proj₁-helper b → π₁⁻¹ b ≡ 0

-- π₁-lemma′ : ∀ {b} → π₁⁻¹ ⟨ 0 , b ⟩ ≡ 0
-- π₁-lemma′ {zero} = refl
-- π₁-lemma′ {suc b} = {!!} --proj₁-lemma {!!}

-- proj₁-lemma {.(⟨ 0 , _ ⟩)} Proj₁-helper-0 = {!!}
-- proj₁-lemma {.(suc _)} (Proj₁-helper-s prf) = {!!}

-- -- π₁-lemma′ : ∀ {b} → π₁⁻¹ (suc (suc ⟨ 0 , b ⟩ + b)) ≡ 0
-- -- π₁-lemma′ {zero} = refl
-- -- π₁-lemma′ {suc b} = {!!}

-- -- π₁-lemma′ {zero} = refl
-- -- π₁-lemma′ {suc b} rewrite (pair-lemma {b}) | π₁-lemma′ {b} =
-- --   let p = π₁-lemma′ {b}
-- --   in
-- --   {!!}

-- -- π₁-lemma : ∀ {b} → π₁⁻¹ ⟨ 0 , b ⟩ ≡ 0
-- -- π₁-lemma {zero} = refl
-- -- π₁-lemma {suc b} = π₁-lemma′ {b}


-- -- pair-inv₁ : ∀ {a b} → π₁⁻¹ ⟨ a , b ⟩ ≡ a
-- -- pair-inv₁ {zero} {zero} = refl
-- -- pair-inv₁ {zero} {suc b} = π₁-lemma {suc b} --π₁-lemma {suc b}
-- -- pair-inv₁ {suc a} {b} = {!!}
