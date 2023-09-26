-- Based on "Data Types as Lattices" by Dana Scott

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Product

open import Data.Sum

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.List hiding (head; tail)
open import Data.Maybe

open import Function

open import Relation.Nullary

-- open import Data.Nat.Tactic.RingSolver

open import Data.Nat.Solver
open +-*-Solver using (solve; _:*_; _:+_; _:^_; con; _:=_)

open import Data.Nat.Binary using (ℕᵇ; 2[1+_]; 1+[2_]; toℕ; fromℕ'; double; zero) renaming (suc to ℕᵇ-suc)
open import Data.Nat.Binary.Properties using (toℕ-double; toℕ-fromℕ')

open import Data.Empty renaming (⊥ to False; ⊥-elim to False-elim)

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

Bits-apart : ∀ {x y z} →
  ¬ (B x ≡ y ,, z)
Bits-apart = λ ()

dec-Has-One : ∀ x →
  Has-One x ⊎ ¬ Has-One x
dec-Has-One (B O) = inj₂ (λ ())
dec-Has-One (B I) = inj₁ Has-One-I
dec-Has-One (x ,, O) with dec-Has-One x
... | inj₁ p = inj₁ (Has-One-There p)
... | inj₂ ¬p = inj₂ (λ { (Has-One-There q) → ¬p q })
dec-Has-One (x ,, I) = inj₁ Has-One-Here

invert¬Has-One : ∀ {x b} →
  ¬ Has-One (x ,, b) →
  ¬ Has-One x
invert¬Has-One {x} {O} ¬p prf = ¬p (Has-One-There prf)
invert¬Has-One {x} {I} ¬p prf = ¬p Has-One-Here

-- Remove any leading zeros
normalize : Bits → Bits
normalize (B O) = B O
normalize (B I) = B I
normalize (b ,, O) with dec-Has-One b
... | inj₁ p = normalize b ,, O
... | inj₂ ¬p = B O
normalize (b ,, I) with dec-Has-One b
... | inj₁ p = normalize b ,, I
... | inj₂ ¬p = B I

_ : normalize (B O ,, I) ≡ B I
_ = refl

-- normalize-Has-One : ∀ {x} →
--   Has-One x →
--   normalize x ≡ x
-- normalize-Has-One Has-One-I = refl
-- normalize-Has-One Has-One-Here = refl
-- normalize-Has-One {B I ,, O} (Has-One-There prf) = refl
-- normalize-Has-One {w ,, x ,, O} (Has-One-There prf) with dec-Has-One (w ,, x)
-- ... | inj₁ p rewrite normalize-Has-One prf = refl
-- ... | inj₂ ¬p = False-elim (¬p prf)

data Is-Normalized : Bits → Set where
  Is-Normalized-B : ∀ {x} → Is-Normalized (B x)
  Is-Normalized-O : ∀ {x} →
    Has-One x →
    Is-Normalized x →
    Is-Normalized (x ,, O)
  Is-Normalized-I : ∀ {x} →
    Has-One x →
    Is-Normalized x →
    Is-Normalized (x ,, I)

invert-Bits-cons-left : ∀ {x y x′ y′} →
  x ,, y ≡ x′ ,, y′ →
  x ≡ x′
invert-Bits-cons-left refl = refl

Normalized : Bits → Set
Normalized x = normalize x ≡ x

_ : normalize (B O ,, I ,, O ,, I) ≡ B I ,, O ,, I
_ = refl

invert-Normalized : ∀ {x y} →
  Normalized (x ,, y) →
  Normalized x
invert-Normalized {B I} {O} prf = refl
invert-Normalized {B I} {I} prf = refl
invert-Normalized {x ,, O} {O} prf with dec-Has-One x
... | inj₁ Has-One-I = refl
... | inj₁ (Has-One-Here {x = y}) with dec-Has-One y
invert-Normalized {.(_ ,, I) ,, O} {O} prf | inj₁ (Has-One-Here {_}) | inj₁ x rewrite invert-Bits-cons-left prf = refl
invert-Normalized {x ,, O} {O} prf | inj₁ (Has-One-There {x = y} x₁) with dec-Has-One y
invert-Normalized {(w ,, O) ,, O} {O} prf | inj₁ (Has-One-There {_} x₁) | inj₁ x with dec-Has-One w
invert-Normalized {.(w ,, O) ,, O} {O} prf | inj₁ (Has-One-There {w} x₁) | inj₁ x | inj₁ x₂ rewrite invert-Bits-cons-left prf = refl

invert-Normalized {x ,, I} {O} prf with dec-Has-One x
... | inj₁ p rewrite invert-Bits-cons-left prf = refl
invert-Normalized {x ,, I} {O} () | inj₂ ¬p
invert-Normalized {x ,, O} {I} prf with dec-Has-One x
... | inj₁ Has-One-I = refl
... | inj₁ (Has-One-Here {x = y}) with dec-Has-One y
invert-Normalized {.(_ ,, I) ,, O} {I} prf | inj₁ (Has-One-Here {_}) | inj₁ x rewrite invert-Bits-cons-left prf = refl
invert-Normalized {.(B O ,, I) ,, O} {I} () | inj₁ (Has-One-Here {B O}) | inj₂ y
invert-Normalized {.(B I ,, I) ,, O} {I} () | inj₁ (Has-One-Here {B I}) | inj₂ y
invert-Normalized {.(z ,, x ,, I) ,, O} {I} () | inj₁ (Has-One-Here {z ,, x}) | inj₂ y
invert-Normalized {x ,, O} {I} prf | inj₁ (Has-One-There {x = y} p) with dec-Has-One y
... | inj₁ w with dec-Has-One y
invert-Normalized {.(_ ,, O) ,, O} {I} prf | inj₁ (Has-One-There {_} p) | inj₁ w | inj₁ x rewrite invert-Bits-cons-left prf = refl
invert-Normalized {.(_ ,, O) ,, O} {I} () | inj₁ (Has-One-There {_} p) | inj₂ ¬w
invert-Normalized {x ,, O} {I} () | inj₂ ¬p

invert-Normalized {x ,, I} {I} prf with dec-Has-One x
... | inj₁ p rewrite invert-Bits-cons-left prf = refl

Is-Normalized→Normalized : ∀ {x} →
  Is-Normalized x →
  Normalized x
Is-Normalized→Normalized {B O} Is-Normalized-B = refl
Is-Normalized→Normalized {B I} Is-Normalized-B = refl
Is-Normalized→Normalized {w ,, O} (Is-Normalized-O x prf)
  with dec-Has-One w
... | inj₁ p rewrite Is-Normalized→Normalized prf = refl
... | inj₂ ¬p = False-elim (¬p x)
Is-Normalized→Normalized {w ,, I} (Is-Normalized-I x prf)
  with dec-Has-One w
... | inj₁ p rewrite Is-Normalized→Normalized prf = refl
... | inj₂ ¬p = False-elim (¬p x)

Normalized→Is-Normalized : ∀ {x} →
  Normalized x →
  Is-Normalized x
Normalized→Is-Normalized {B O} prf = Is-Normalized-B
Normalized→Is-Normalized {B I} prf = Is-Normalized-B
Normalized→Is-Normalized {x ,, O} prf with dec-Has-One x
... | inj₁ p = Is-Normalized-O p (Normalized→Is-Normalized (invert-Bits-cons-left prf))
Normalized→Is-Normalized {x ,, O} () | inj₂ ¬p
Normalized→Is-Normalized {x ,, I} eq = go (invert-Normalized eq)
  where
    go : (Normalized x) → Is-Normalized (x ,, I)
    go prf with dec-Has-One x
    ... | inj₂ ¬p = False-elim (Bits-apart eq)
    ... | inj₁ p = Is-Normalized-I p (Normalized→Is-Normalized prf)

dec-Is-Normalized : ∀ x →
  Is-Normalized x ⊎ ¬ Is-Normalized x
dec-Is-Normalized (B x) = inj₁ Is-Normalized-B
dec-Is-Normalized (x ,, O) with dec-Has-One x | dec-Is-Normalized x
... | inj₁ x₁ | inj₁ x₂ = inj₁ (Is-Normalized-O x₁ x₂)
... | inj₁ x₁ | inj₂ y = inj₂ (λ { (Is-Normalized-O a b) → y b })
... | inj₂ y | inj₁ x₁ = inj₂ (λ { (Is-Normalized-O a b) → y a })
... | inj₂ y | inj₂ y₁ = inj₂ (λ { (Is-Normalized-O a b) → y a })
dec-Is-Normalized (x ,, I) with dec-Has-One x | dec-Is-Normalized x
... | inj₁ x₁ | inj₁ x₂ = inj₁ (Is-Normalized-I x₁ x₂)
... | inj₁ x₁ | inj₂ y = inj₂ (λ { (Is-Normalized-I a b) → y b })
... | inj₂ y | inj₁ x₁ = inj₂ (λ { (Is-Normalized-I a b) → y a })
... | inj₂ y | inj₂ y₁ = inj₂ (λ { (Is-Normalized-I a b) → y a })

normalize-¬Has-One : ∀ {x} →
  ¬ Has-One x →
  normalize x ≡ B O
normalize-¬Has-One {B O} prf = refl
normalize-¬Has-One {B I} prf = False-elim (prf Has-One-I)
normalize-¬Has-One {x ,, O} prf with dec-Has-One x
... | inj₁ p = False-elim (prf (Has-One-There p))
... | inj₂ ¬p = refl
normalize-¬Has-One {x ,, I} prf = False-elim (prf Has-One-Here)

normalize-preserves-Has-One : ∀ {x} →
  Has-One x →
  Has-One (normalize x)
normalize-preserves-Has-One {.(B I)} Has-One-I = Has-One-I
normalize-preserves-Has-One {x ,, I} Has-One-Here with dec-Has-One x
... | inj₁ p = Has-One-Here
... | inj₂ ¬p = Has-One-I
normalize-preserves-Has-One {x ,, O} (Has-One-There prf) with dec-Has-One x
... | inj₁ p = Has-One-There (normalize-preserves-Has-One {x} prf)
... | inj₂ ¬p = False-elim (¬p prf)

normalize-idem : ∀ {x} →
  normalize (normalize x) ≡ normalize x
normalize-idem {x} with dec-Is-Normalized x
... | inj₁ (Is-Normalized-B {O}) = refl
... | inj₁ (Is-Normalized-B {I}) = refl
... | inj₁ (Is-Normalized-O {x = y} z p) with dec-Has-One y
normalize-idem {.(_ ,, O)} | inj₁ (Is-Normalized-O {x = y} z p) | inj₁ x with dec-Has-One (normalize y)
normalize-idem {.(_ ,, O)} | inj₁ (Is-Normalized-O {x = y} z p) | inj₁ x | inj₁ q rewrite (normalize-idem {y}) = refl
normalize-idem {.(_ ,, O)} | inj₁ (Is-Normalized-O {x = y} z p) | inj₁ x | inj₂ ¬q =
  False-elim (¬q (normalize-preserves-Has-One x))
normalize-idem {.(_ ,, O)} | inj₁ (Is-Normalized-O {_} z p) | inj₂ y = refl
normalize-idem {x} | inj₁ (Is-Normalized-I {x = y} z p) with dec-Has-One y
... | inj₂ ¬q = refl
... | inj₁ q with dec-Has-One y
normalize-idem {.(_ ,, I)} | inj₁ (Is-Normalized-I {y} z p) | inj₁ q | inj₁ x with dec-Has-One (normalize y)
... | inj₁ w rewrite normalize-idem {y} = refl
... | inj₂ ¬w = False-elim (¬w (normalize-preserves-Has-One z))
normalize-idem {.(_ ,, I)} | inj₁ (Is-Normalized-I {_} z p) | inj₁ q | inj₂ y = False-elim (y z)

normalize-idem {B O} | inj₂ ¬p = refl
normalize-idem {B I} | inj₂ ¬p = refl
normalize-idem {x ,, O} | inj₂ ¬p with dec-Has-One x
normalize-idem {x ,, O} | inj₂ ¬p | inj₁ q with dec-Has-One (normalize x)
normalize-idem {x ,, O} | inj₂ ¬p | inj₁ q | inj₁ x₁ rewrite normalize-idem {x} = refl
normalize-idem {x ,, O} | inj₂ ¬p | inj₁ q | inj₂ y = False-elim (y (normalize-preserves-Has-One q))
normalize-idem {x ,, O} | inj₂ ¬p | inj₂ q = refl
normalize-idem {x ,, I} | inj₂ ¬p with dec-Has-One x
... | inj₂ ¬q = refl
... | inj₁ q with dec-Has-One x
normalize-idem {x ,, I} | inj₂ ¬p | inj₁ q | inj₁ r with dec-Has-One (normalize x)
... | inj₁ w rewrite normalize-idem {x} = refl
... | inj₂ ¬w = False-elim (¬w (normalize-preserves-Has-One q))
normalize-idem {x ,, I} | inj₂ ¬p | inj₁ q | inj₂ ¬r = False-elim (¬r q)

Bits-suc : Bits → Bits
Bits-suc (B O) = B I
Bits-suc (B I) = B I ,, O
Bits-suc (b ,, O) = b ,, I
Bits-suc (b ,, I) = Bits-suc b ,, O

data Bits-Suc : Bits → Bits → Set where
  Bits-Suc-O : Bits-Suc (B O) (B I)
  Bits-Suc-I : Bits-Suc (B I) (B I ,, O)
  Bits-Suc-Cons-O : ∀ {b} →
    Bits-Suc (b ,, O) (b ,, I)
  Bits-Suc-Cons-I : ∀ {b x} →
    Bits-Suc b x →
    Bits-Suc (b ,, I) (x ,, O)

lower-Bits-suc : ∀ {b x} →
  Bits-Suc b x →
  Bits-suc b ≡ x
lower-Bits-suc {.(B O)} {.(B I)} Bits-Suc-O = refl
lower-Bits-suc {.(B I)} {.(B I ,, O)} Bits-Suc-I = refl
lower-Bits-suc {.(_ ,, O)} {.(_ ,, I)} Bits-Suc-Cons-O = refl
lower-Bits-suc {.(_ ,, I)} {.(_ ,, O)} (Bits-Suc-Cons-I prf) rewrite lower-Bits-suc prf = refl

lift-Bits-suc : ∀ {b x} →
  Bits-suc b ≡ x →
  Bits-Suc b x
lift-Bits-suc {B O} {.(Bits-suc (B O))} refl = Bits-Suc-O
lift-Bits-suc {B I} {.(Bits-suc (B I))} refl = Bits-Suc-I
lift-Bits-suc {b ,, O} {.(Bits-suc (b ,, O))} refl = Bits-Suc-Cons-O
lift-Bits-suc {b ,, I} {.(Bits-suc (b ,, I))} refl = Bits-Suc-Cons-I (lift-Bits-suc refl)

Bits-Suc-exists : ∀ {b} →
  ∃[ x ] Bits-Suc b x
Bits-Suc-exists {x} = Bits-suc x , lift-Bits-suc {x} refl

Bits-suc-Has-One : ∀ {x} →
  Has-One (Bits-suc x)
Bits-suc-Has-One {B O} = Has-One-I
Bits-suc-Has-One {B I} = Has-One-There Has-One-I
Bits-suc-Has-One {x ,, O} = Has-One-Here
Bits-suc-Has-One {x ,, I} = Has-One-There Bits-suc-Has-One

Bits-suc-preserves-normalized : ∀ {x y} →
  Bits-suc x ≡ y →
  Normalized x →
  Normalized y
Bits-suc-preserves-normalized {B O} {B I} eq prf = refl
Bits-suc-preserves-normalized {B I} {.(B I) ,, O} refl prf = refl
Bits-suc-preserves-normalized {x ,, x₁} {B O} eq prf = refl
Bits-suc-preserves-normalized {x ,, x₁} {B I} eq prf = refl
Bits-suc-preserves-normalized {x ,, O} {.x ,, .I} refl prf rewrite invert-Normalized prf with dec-Has-One x
... | inj₁ p rewrite invert-Bits-cons-left prf = refl
Bits-suc-preserves-normalized {x ,, I} {.(Bits-suc x) ,, .O} refl prf with dec-Has-One x
... | inj₁ p with dec-Has-One (Bits-suc x)
Bits-suc-preserves-normalized {x ,, I} {.(Bits-suc x) ,, .O} refl prf | inj₁ p | inj₁ q
  rewrite Bits-suc-preserves-normalized {x} {Bits-suc x} refl (invert-Bits-cons-left prf) = refl
Bits-suc-preserves-normalized {x ,, I} {.(Bits-suc x) ,, .O} refl prf | inj₁ p | inj₂ ¬q = False-elim (¬q (Bits-suc-Has-One {x}))
Bits-suc-preserves-normalized {x ,, I} {.(Bits-suc x) ,, .O} eq@refl prf | inj₂ ¬p
  with dec-Has-One (Bits-suc x)
Bits-suc-preserves-normalized {x ,, I} {.(Bits-suc x) ,, .O} refl () | inj₂ ¬p | inj₁ q
Bits-suc-preserves-normalized {x ,, I} {.(Bits-suc x) ,, .O} refl () | inj₂ ¬p | inj₂ ¬q

toBits : ℕᵇ → Bits
toBits zero = B O
toBits 2[1+ n ] = Bits-suc (toBits n) ,, O
toBits 1+[2 n ] with toBits n
... | B O = B I
... | x = Bits-suc (x ,, O)

data ToBits : ℕᵇ → Bits → Set where
  ToBits-zero : ToBits zero (B O)

  ToBits-2[1+n] : ∀ {x b b′} →
    ToBits x b →
    Bits-Suc b b′ →
    ToBits 2[1+ x ] (b′ ,, O)

  ToBits-1+[2n]-O : ∀ {x} →
    ToBits x (B O) →
    ToBits 1+[2 x ] (B I)

  ToBits-1+[2n]-I : ∀ {x b′} →
    ToBits x (B I) →
    Bits-Suc (B I ,, O) b′ →
    ToBits 1+[2 x ] b′

  ToBits-1+[2n]-Cons-O : ∀ {x b r′} →
    let r = b ,, O
    in
    ToBits x r →
    Bits-Suc (r ,, O) r′ →
    ToBits 1+[2 x ] r′

  ToBits-1+[2n]-Cons-I : ∀ {x b r′} →
    let r = b ,, I
    in
    ToBits x r →
    Bits-Suc (r ,, O) r′ →
    ToBits 1+[2 x ] r′

lower-ToBits : ∀ {x b} →
  ToBits x b →
  toBits x ≡ b
lower-ToBits {.zero} {.(B O)} ToBits-zero = refl
lower-ToBits {.(2[1+ _ ])} {.(B I ,, O)} (ToBits-2[1+n] prf Bits-Suc-O) rewrite lower-ToBits prf = refl
lower-ToBits {.(2[1+ _ ])} {.(B I ,, O ,, O)} (ToBits-2[1+n] prf Bits-Suc-I) rewrite lower-ToBits prf = refl
lower-ToBits {.(2[1+ _ ])} {.(_ ,, I ,, O)} (ToBits-2[1+n] prf Bits-Suc-Cons-O) rewrite lower-ToBits prf = refl
lower-ToBits {.(2[1+ _ ])} {.(_ ,, O ,, O)} (ToBits-2[1+n] prf (Bits-Suc-Cons-I x)) rewrite lower-ToBits prf | lower-Bits-suc x = refl
lower-ToBits {.(1+[2 _ ])} {.(B I)} (ToBits-1+[2n]-O prf) rewrite lower-ToBits prf = refl
lower-ToBits {1+[2 x ]} {w ,, b} (ToBits-1+[2n]-I prf y) rewrite lower-ToBits prf | lower-Bits-suc y = refl
lower-ToBits {.(1+[2 _ ])} {b} (ToBits-1+[2n]-Cons-O prf x) rewrite lower-ToBits prf | lower-Bits-suc x = refl
lower-ToBits {.(1+[2 _ ])} {b} (ToBits-1+[2n]-Cons-I prf x) rewrite lower-ToBits prf | lower-Bits-suc x = refl

lift-ToBits : ∀ {x b} →
  toBits x ≡ b →
  ToBits x b
lift-ToBits {zero} {B O} prf = ToBits-zero
lift-ToBits {2[1+ x ]} {b ,, O} refl = ToBits-2[1+n] (lift-ToBits refl) (lift-Bits-suc refl)
lift-ToBits {1+[2 x ]} {.(toBits 1+[2 x ])} refl with lift-ToBits {x} {toBits x} refl
lift-ToBits {1+[2 zero ]} {.(toBits 1+[2 zero ])} eq | p = ToBits-1+[2n]-O p
lift-ToBits {1+[2 2[1+ x ] ]} {.(toBits 1+[2 2[1+ x ] ])} eq | p = ToBits-1+[2n]-Cons-O p Bits-Suc-Cons-O
lift-ToBits {1+[2 1+[2 x ] ]} {.(toBits 1+[2 1+[2 x ] ])} eq | p with toBits 1+[2 x ] in eq₂
... | q ,, O = ToBits-1+[2n]-Cons-O p Bits-Suc-Cons-O
... | q ,, I = ToBits-1+[2n]-Cons-I p Bits-Suc-Cons-O
... | B O with toBits x
lift-ToBits {1+[2 1+[2 x ] ]} {.(toBits 1+[2 1+[2 x ] ])} refl | p | B O | B O with () ← eq₂
lift-ToBits {1+[2 1+[2 x ] ]} {.(toBits 1+[2 1+[2 x ] ])} refl | p | B O | B I with () ← eq₂
lift-ToBits {1+[2 1+[2 x ] ]} {.(toBits 1+[2 1+[2 x ] ])} refl | p | B I with toBits x in eq₃
lift-ToBits {1+[2 1+[2 zero ] ]} {.(toBits 1+[2 1+[2 zero ] ])} refl | p | B I | B O = ToBits-1+[2n]-I p Bits-Suc-Cons-O
lift-ToBits {1+[2 1+[2 1+[2 x ] ] ]} {.(toBits 1+[2 1+[2 1+[2 x ] ] ])} refl | p | B I | B O = ToBits-1+[2n]-I p Bits-Suc-Cons-O
lift-ToBits {1+[2 1+[2 x ] ]} {.(toBits 1+[2 1+[2 x ] ])} refl | p | B I | B I with () ← eq₂

ToBits-exists : ∀ {x} →
  ∃[ b ] ToBits x b
ToBits-exists {x} = toBits x , lift-ToBits {x} refl

-- toBits-normalized : ∀ {x y} →
--   toBits x ≡ y →
--   Normalized y
-- toBits-normalized {x} prf = {!!}

fromBits : Bits → ℕᵇ
fromBits (B O) = zero
fromBits (B I) = 1+[2 zero ]
-- fromBits (b ,, O) = double (fromBits b)
fromBits (b ,, O) with fromBits b
... | zero = zero
... | x = double x
fromBits (b ,, I) = 1+[2 fromBits b ]

data FromBits : Bits → ℕᵇ → Set where
  FromBits-O : FromBits (B O) zero
  FromBits-I : FromBits (B I) 1+[2 zero ]

  FromBits-Cons-O-O : ∀ {b} →
    FromBits b zero →
    FromBits (b ,, O) zero

  FromBits-Cons-O-1+[2n] : ∀ {b x y} →
    FromBits b 1+[2 x ] →
    y ≡ double 1+[2 x ] →
    FromBits (b ,, O) y

  FromBits-Cons-O-2[1+n] : ∀ {b x y} →
    FromBits b 2[1+ x ] →
    y ≡ double 2[1+ x ] →
    FromBits (b ,, O) y

  FromBits-Cons-I : ∀ {b x} →
    FromBits b x →
    FromBits (b ,, I) 1+[2 x ]

lower-FromBits : ∀ {b x} →
  FromBits b x →
  fromBits b ≡ x
lower-FromBits {.(B O)} {.zero} FromBits-O = refl
lower-FromBits {.(B I)} {.(1+[2 zero ])} FromBits-I = refl
lower-FromBits {.(_ ,, O)} {.zero} (FromBits-Cons-O-O prf) rewrite lower-FromBits prf = refl
lower-FromBits {.(_ ,, O)} {.(double 1+[2 _ ])} (FromBits-Cons-O-1+[2n] prf refl) rewrite lower-FromBits prf = refl
lower-FromBits {.(_ ,, O)} {.(double 2[1+ _ ])} (FromBits-Cons-O-2[1+n] prf refl) rewrite lower-FromBits prf = refl
lower-FromBits {.(_ ,, I)} {.(1+[2 _ ])} (FromBits-Cons-I prf) rewrite lower-FromBits prf = refl

lift-fromBits : ∀ {b x} →
  fromBits b ≡ x →
  FromBits b x
lift-fromBits {B O} {x} refl = FromBits-O
lift-fromBits {B I} {x} refl = FromBits-I
lift-fromBits {b ,, O} {x} refl with fromBits b in eq
... | zero = FromBits-Cons-O-O (lift-fromBits eq)
... | 2[1+ p ] = FromBits-Cons-O-2[1+n] {b} {p} (lift-fromBits eq) refl
... | 1+[2 p ] = FromBits-Cons-O-1+[2n] (lift-fromBits eq) refl
lift-fromBits {b ,, I} {x} refl = FromBits-Cons-I (lift-fromBits refl)

FromBits-exists : ∀ {b} →
  ∃[ x ] FromBits b x
FromBits-exists {x} = fromBits x , lift-fromBits {x} refl

ℕ→Bits : ℕ → Bits
ℕ→Bits = toBits ∘ fromℕ'

Bits→ℕ : Bits → ℕ
Bits→ℕ = toℕ ∘ fromBits

fromBits-O : ∀ {x} →
  fromBits (x ,, O) ≡ zero →
  fromBits x ≡ zero
fromBits-O {B O} prf = refl
fromBits-O {x ,, O} prf with fromBits x
... | zero = refl

fromBits-Bits-suc-nonzero : ∀ {x} →
  fromBits (Bits-suc x) ≢ zero
fromBits-Bits-suc-nonzero {B O} ()
fromBits-Bits-suc-nonzero {B I} ()
fromBits-Bits-suc-nonzero {x ,, I} eq =
  fromBits-Bits-suc-nonzero {x} (fromBits-O {Bits-suc x} eq)

double-zero : ∀ {x} →
  double x ≡ zero →
  x ≡ zero
double-zero {zero} prf = refl

fromBits-suc-zero : ∀ {x} →
  fromBits (Bits-suc x) ≡ 1+[2 zero ] →
  fromBits x ≡ zero
fromBits-suc-zero {B O} prf = refl
fromBits-suc-zero {x ,, O} prf with fromBits x
... | zero = refl
fromBits-suc-zero {x ,, I} prf with fromBits (Bits-suc x)
fromBits-suc-zero {x ,, I} () | zero
fromBits-suc-zero {x ,, I} () | 2[1+ p ]
fromBits-suc-zero {x ,, I} () | 1+[2 p ]

invert-2[1+] : ∀ {x y} →
  2[1+ x ] ≡ 2[1+ y ] →
  x ≡ y
invert-2[1+] {x} {.x} refl = refl

invert-1+[2] : ∀ {x y} →
  1+[2 x ] ≡ 1+[2 y ] →
  x ≡ y
invert-1+[2] {x} {.x} refl = refl

suc-double : ∀ {x} →
  ℕᵇ-suc (double x) ≡ 1+[2 x ]
suc-double {zero} = refl
suc-double {2[1+ x ]} = refl
suc-double {1+[2 x ]} rewrite suc-double {x} = refl

double-suc : ∀ {x} →
  double (ℕᵇ-suc x) ≡ 2[1+ x ]
double-suc {zero} = refl
double-suc {2[1+ x ]} = cong 2[1+_] double-suc
double-suc {1+[2 x ]} = refl

-- 2x = 2(1 + y)
-- 2x = 2 + 2y
-- x = 1 + y
double-suc-2[1+] : ∀ {x y} →
  double x ≡ 2[1+ y ] →
  x ≡ ℕᵇ-suc y
double-suc-2[1+] {2[1+ x ]} {.(1+[2 x ])} refl = refl
double-suc-2[1+] {1+[2 x ]} {.(double x)} refl with ℕᵇ-suc (double x) in eq
double-suc-2[1+] {1+[2 zero ]} {.(double zero)} refl | zero = eq
double-suc-2[1+] {1+[2 2[1+ x ] ]} {.(double 2[1+ x ])} refl | zero = eq
... | 2[1+ p ] rewrite suc-double {x} = eq
... | 1+[2 p ] with ℕᵇ-suc (double x) in eq₁
double-suc-2[1+] {1+[2 x ]} {.(double x)} refl | 1+[2 p ] | 1+[2 q ]
  rewrite invert-1+[2] (trans (sym (suc-double {x})) eq₁)
  = eq

suc-double-2[1+] : ∀ {x y} →
  x ≡ ℕᵇ-suc y →
  double x ≡ 2[1+ y ]
suc-double-2[1+] {2[1+ x ]} {1+[2 .x ]} refl = refl
suc-double-2[1+] {1+[2 .zero ]} {zero} refl = refl
suc-double-2[1+] {1+[2 .(ℕᵇ-suc y) ]} {2[1+ y ]} refl =
  cong 2[1+_] double-suc



-- 1 + x = 1 + 2(y + 1)
-- x = 2(y + 1)
fromBits-Bits-suc-1+[2] : ∀ {x y} →
  fromBits (Bits-suc x) ≡ 1+[2 ℕᵇ-suc y ] →
  fromBits x ≡ 2[1+ y ]
fromBits-Bits-suc-1+[2] {B O} {zero} ()
fromBits-Bits-suc-1+[2] {B I} {zero} ()
fromBits-Bits-suc-1+[2] {B O} {2[1+ y ]} ()
fromBits-Bits-suc-1+[2] {B I} {2[1+ y ]} ()
fromBits-Bits-suc-1+[2] {B O} {1+[2 y ]} ()
fromBits-Bits-suc-1+[2] {B I} {1+[2 y ]} ()
fromBits-Bits-suc-1+[2] {x ,, O} {zero} prf with fromBits x
fromBits-Bits-suc-1+[2] {x ,, O} {zero} refl | 1+[2 .zero ] = refl
fromBits-Bits-suc-1+[2] {x ,, I} {zero} prf with fromBits x
fromBits-Bits-suc-1+[2] {x ,, I} {zero} prf | 2[1+ p ] with fromBits (Bits-suc x)
fromBits-Bits-suc-1+[2] {x ,, I} {zero} () | 2[1+ p ] | zero
fromBits-Bits-suc-1+[2] {x ,, I} {zero} () | 2[1+ p ] | 2[1+ q ]
fromBits-Bits-suc-1+[2] {x ,, I} {zero} () | 2[1+ p ] | 1+[2 q ]
fromBits-Bits-suc-1+[2] {x ,, I} {zero} prf | 1+[2 p ] with fromBits (Bits-suc x)
fromBits-Bits-suc-1+[2] {x ,, I} {zero} () | 1+[2 p ] | zero
fromBits-Bits-suc-1+[2] {x ,, I} {zero} () | 1+[2 p ] | 2[1+ q ]
fromBits-Bits-suc-1+[2] {x ,, I} {zero} () | 1+[2 p ] | 1+[2 q ]
fromBits-Bits-suc-1+[2] {x ,, I} {zero} prf | zero with fromBits (Bits-suc x)
fromBits-Bits-suc-1+[2] {B x ,, I} {zero} () | zero | zero
fromBits-Bits-suc-1+[2] {B x ,, I} {zero} () | zero | 2[1+ q ]
fromBits-Bits-suc-1+[2] {B x ,, I} {zero} () | zero | 1+[2 q ]
fromBits-Bits-suc-1+[2] {x ,, O} {2[1+ y ]} prf with fromBits x
... | 1+[2 p ] rewrite invert-1+[2] (invert-1+[2] prf) =
  cong 2[1+_] (suc-double-2[1+] refl)
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} prf with fromBits x
... | zero with fromBits (Bits-suc x)
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} () | zero | zero
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} () | zero | 2[1+ q ]
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} () | zero | 1+[2 q ]
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} prf | 2[1+ p ] with fromBits (Bits-suc x)
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} () | 2[1+ p ] | zero
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} () | 2[1+ p ] | 2[1+ q ]
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} () | 2[1+ p ] | 1+[2 q ]
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} prf | 1+[2 p ] with fromBits (Bits-suc x)
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} () | 1+[2 p ] | zero
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} () | 1+[2 p ] | 2[1+ q ]
fromBits-Bits-suc-1+[2] {x ,, I} {2[1+ y ]} () | 1+[2 p ] | 1+[2 q ]
fromBits-Bits-suc-1+[2] {x ,, O} {1+[2 y ]} prf with fromBits x
fromBits-Bits-suc-1+[2] {x ,, O} {1+[2 .q ]} refl | 2[1+ q ] = refl
fromBits-Bits-suc-1+[2] {x ,, I} {1+[2 y ]} prf with fromBits (Bits-suc x)
fromBits-Bits-suc-1+[2] {x ,, I} {1+[2 y ]} () | zero
fromBits-Bits-suc-1+[2] {x ,, I} {1+[2 y ]} () | 2[1+ q ]
fromBits-Bits-suc-1+[2] {x ,, I} {1+[2 y ]} () | 1+[2 q ]

¬double-1+[2] : ∀ {x y} →
  double x ≢ 1+[2 y ]
¬double-1+[2] {zero} {zero} ()
¬double-1+[2] {zero} {2[1+ y ]} ()
¬double-1+[2] {zero} {1+[2 y ]} ()
¬double-1+[2] {2[1+ x ]} {zero} ()
¬double-1+[2] {2[1+ x ]} {2[1+ y ]} ()
¬double-1+[2] {2[1+ x ]} {1+[2 y ]} ()
¬double-1+[2] {1+[2 x ]} {zero} ()
¬double-1+[2] {1+[2 x ]} {2[1+ y ]} ()
¬double-1+[2] {1+[2 x ]} {1+[2 y ]} ()

-- 2(1 + y) = 1 + x
-- 2 + 2y = 1 + x
-- 1 + 2y = x
fromBits-Bits-suc-2[1+] : ∀ {x y} →
  fromBits (Bits-suc x) ≡ 2[1+ y ] →
  fromBits x ≡ 1+[2 y ]
fromBits-Bits-suc-2[1+] {B I} {zero} prf = refl
fromBits-Bits-suc-2[1+] {B O} {2[1+ y ]} ()
fromBits-Bits-suc-2[1+] {B I} {2[1+ y ]} ()
fromBits-Bits-suc-2[1+] {B O} {1+[2 y ]} ()
fromBits-Bits-suc-2[1+] {B I} {1+[2 y ]} ()
fromBits-Bits-suc-2[1+] {x ,, I} {zero} prf with fromBits (Bits-suc x) in eq₀
... | 1+[2 p ] with double p in eq₁
fromBits-Bits-suc-2[1+] {x ,, I} {zero} prf | 1+[2 p ] | zero rewrite double-zero eq₁ | fromBits-suc-zero {x} eq₀ = refl
-- fromBits-Bits-suc-2[1+] {x ,, I} {zero} prf | 1+[2 p ] | zero = refl
-- fromBits-Bits-suc-2[1+] {x ,, I} {zero} prf | 1+[2 zero ] | 2[1+ y ] = {!!}
-- fromBits-Bits-suc-2[1+] {x ,, I} {zero} prf | 1+[2 p ] | 1+[2 y ] = {!!}
fromBits-Bits-suc-2[1+] {x ,, I} {2[1+ y ]} prf with fromBits (Bits-suc x) in eq₀
... | 1+[2 p ] rewrite double-suc-2[1+] (invert-2[1+] prf) =
  let eq₁ = invert-2[1+] prf
      eq₂ = double-suc-2[1+] eq₁
  in
  cong 1+[2_] (fromBits-Bits-suc-1+[2] {x} eq₀)
fromBits-Bits-suc-2[1+] {x ,, I} {1+[2 y ]} prf with fromBits (Bits-suc x) in eq
fromBits-Bits-suc-2[1+] {x ,, I} {1+[2 .p ]} refl | 2[1+ p ]
  rewrite fromBits-Bits-suc-2[1+] {x} eq = refl
... | 1+[2 p ] =
  let q = invert-2[1+] prf
  in
  False-elim (¬double-1+[2] q)

double-fromBits : ∀ {x} →
  double (fromBits x) ≡ fromBits (x ,, O)
double-fromBits {x} with fromBits x
... | zero = refl
... | 2[1+ p ] = refl
... | 1+[2 p ] = refl

-- x = 2(1 + y)
-- 1 + x = 2(1 + y) + 1
-- 1 + x = 2 + 2y + 1
-- 1 + x = 1 + 2(1 + y)
fromBits-suc′ : ∀ {x y} →
  fromBits x ≡ 2[1+ y ] →
  fromBits (Bits-suc x) ≡ 1+[2 ℕᵇ-suc y ]
fromBits-suc′ {B O} {zero} ()
fromBits-suc′ {B I} {zero} ()
fromBits-suc′ {B O} {2[1+ y ]} ()
fromBits-suc′ {B I} {2[1+ y ]} ()
fromBits-suc′ {B O} {1+[2 y ]} ()
fromBits-suc′ {B I} {1+[2 y ]} ()
fromBits-suc′ {x ,, O} {zero} prf with fromBits x
... | 1+[2 p ] rewrite double-zero (invert-2[1+] prf) = refl
fromBits-suc′ {x ,, O} {2[1+ y ]} prf with fromBits x
... | 1+[2 p ] rewrite double-suc-2[1+] (invert-2[1+] prf) = refl
fromBits-suc′ {x ,, O} {1+[2 y ]} prf with fromBits x
... | 2[1+ p ] rewrite (invert-1+[2] (invert-2[1+] prf))= refl
... | 1+[2 p ] = False-elim (¬double-1+[2] (invert-2[1+] prf))

ℕᵇ-suc-nonzero : ∀ {x} →
  ℕᵇ-suc x ≢ zero
ℕᵇ-suc-nonzero {zero} ()
ℕᵇ-suc-nonzero {2[1+ x ]} ()
ℕᵇ-suc-nonzero {1+[2 x ]} ()

-- -- 1 + x = 1 + 2(1 + y)
-- -- x = 2(1 + y)
-- suc-fromBits′ : ∀ {x y} →
--   fromBits (Bits-suc x) ≡ 1+[2 ℕᵇ-suc y ] →
--   fromBits x ≡ 2[1+ y ]
-- suc-fromBits′ {x} {y} prf with fromBits (Bits-suc x) in eq
-- ... | 1+[2 p ] = {!!}

  -- fromBits (Bits-suc x) ≡ 1+[2 ℕᵇ-suc y ] →
  -- fromBits x ≡ 2[1+ y ]

fromBits-suc : ∀ {x} →
  double (fromBits (Bits-suc x)) ≡ 2[1+ fromBits x ]
fromBits-suc {B O} = refl
fromBits-suc {B I} = refl
fromBits-suc {x ,, O} with fromBits x
... | zero = refl
... | 2[1+ p ] = refl
... | 1+[2 p ] = refl
fromBits-suc {B O ,, I} = refl
fromBits-suc {B I ,, I} = refl
fromBits-suc {x ,, x₁ ,, I} with fromBits (Bits-suc (x ,, x₁)) in eq
... | zero = False-elim (fromBits-Bits-suc-nonzero {x ,, x₁} eq)
... | 2[1+ p ] = cong 2[1+_] (cong 1+[2_] (sym (fromBits-Bits-suc-2[1+] {x ,, x₁} {p} eq)))
fromBits-suc {x ,, O ,, I} | 1+[2 p ]
  rewrite sym (double-fromBits {x})
        | invert-1+[2] eq = refl
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] with fromBits x
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | zero with fromBits (Bits-suc x)
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | zero | zero with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | zero | 2[1+ w ] with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | zero | 1+[2 w ] with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | 2[1+ q ] with fromBits (Bits-suc x)
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | 2[1+ q ] | zero with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | 2[1+ q ] | 2[1+ w ] with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | 2[1+ q ] | 1+[2 w ] with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | 1+[2 q ] with fromBits (Bits-suc x)
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | 1+[2 q ] | zero with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | 1+[2 q ] | 2[1+ w ] with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 zero ] | 1+[2 q ] | 1+[2 w ] with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 2[1+ p ] ] with fromBits (Bits-suc x)
fromBits-suc {x ,, I ,, I} | 1+[2 2[1+ p ] ] | zero with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 2[1+ p ] ] | 2[1+ w ] with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 2[1+ p ] ] | 1+[2 w ] with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 1+[2 p ] ] with fromBits (Bits-suc x)
fromBits-suc {x ,, I ,, I} | 1+[2 1+[2 p ] ] | zero with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 1+[2 p ] ] | 2[1+ w ] with () ← eq
fromBits-suc {x ,, I ,, I} | 1+[2 1+[2 p ] ] | 1+[2 w ] with () ← eq

_ : fromBits (toBits 2[1+ 1+[2 zero ] ]) ≡ 2[1+ 1+[2 zero ] ]
_ = refl

_ : toBits 2[1+ zero ] ≡ B I ,, O
_ = refl

-- 1 + x = 2(1 + y)
-- 1 + x = 2 + 2y
-- x = 1 + 2y
suc-2[1+] : ∀ {x y} →
  ℕᵇ-suc x ≡ 2[1+ y ] →
  x ≡ 1+[2 y ]
suc-2[1+] {1+[2 .zero ]} {zero} refl = refl
suc-2[1+] {1+[2 x ]} {2[1+ y ]} refl = refl
suc-2[1+] {1+[2 x ]} {1+[2 y ]} refl = refl

-- 2(1 + x) = 2(1 + 1 + 2y)
-- 2 + 2x = 2(2 + 2y)
-- 1 + x = 2 + 2y
-- 1 + x = 2(1 + y)
suc-double′ : ∀ {x y} →
  ℕᵇ-suc x ≡ 1+[2 y ] →
  x ≡ double y
suc-double′ {zero} {zero} prf = refl
suc-double′ {2[1+ zero ]} {zero} ()
suc-double′ {2[1+ 2[1+ x ] ]} {zero} ()
suc-double′ {2[1+ 1+[2 x ] ]} {zero} ()
suc-double′ {2[1+ x ]} {2[1+ y ]} prf with ℕᵇ-suc x in eq
suc-double′ {2[1+ x ]} {2[1+ y ]} prf | 2[1+ p ]
  rewrite invert-2[1+] (invert-1+[2] prf)
        | suc-2[1+] eq = refl
suc-double′ {2[1+ x ]} {1+[2 y ]} prf rewrite suc-double′ (invert-1+[2] prf) = refl

fromBits-suc-comm : ∀ {x} →
  fromBits (Bits-suc x) ≡ ℕᵇ-suc (fromBits x)
fromBits-suc-comm {B O} = refl
fromBits-suc-comm {B I} = refl
fromBits-suc-comm {x ,, O} with fromBits x in eq₀
fromBits-suc-comm {x ,, O} | zero = refl
fromBits-suc-comm {x ,, O} | 2[1+ p ] = refl
fromBits-suc-comm {x ,, O} | 1+[2 p ] rewrite (suc-double {p}) = refl
fromBits-suc-comm {x ,, I} with fromBits (Bits-suc x) in eq
fromBits-suc-comm {x ,, I} | zero = False-elim (fromBits-Bits-suc-nonzero {x} eq)
fromBits-suc-comm {x ,, I} | 2[1+ p ] rewrite fromBits-Bits-suc-2[1+] {x} eq = refl
fromBits-suc-comm {B O ,, I} | 1+[2 zero ] = refl
fromBits-suc-comm {x ,, O ,, I} | 1+[2 zero ] with fromBits x
fromBits-suc-comm {x ,, O ,, I} | 1+[2 zero ] | zero = refl
fromBits-suc-comm {x ,, I ,, I} | 1+[2 zero ] with fromBits (Bits-suc x)
fromBits-suc-comm {x ,, I ,, I} | 1+[2 zero ] | zero with () ← eq
fromBits-suc-comm {x ,, I ,, I} | 1+[2 zero ] | 2[1+ p ] with () ← eq
fromBits-suc-comm {x ,, I ,, I} | 1+[2 zero ] | 1+[2 p ] with () ← eq
fromBits-suc-comm {x ,, I} | 1+[2 2[1+ p ] ] rewrite fromBits-Bits-suc-1+[2] {x} eq = refl
fromBits-suc-comm {x ,, I} | 1+[2 1+[2 p ] ] rewrite fromBits-suc-comm {x} | suc-double′ eq = refl

-- data FromBits-ToBits : ℕᵇ → Set where
--   FromBits-ToBits-zero : FromBits-ToBits zero
--   FromBits-ToBits-1+[2n] : ∀ {x} →
--     FromBits-ToBits x →
--     fromBits (toBits 1+[2 x ]) ≡ 1+[2 x ] →

-- data FromBits-ToBits : ℕᵇ → ℕᵇ → Set where

bits-suc-helper : ∀ {x b} →
  Bits-Suc x b →
  ¬ FromBits b zero
bits-suc-helper Bits-Suc-O ()
bits-suc-helper Bits-Suc-I (FromBits-Cons-O-O prf-2) = bits-suc-helper Bits-Suc-O prf-2
bits-suc-helper Bits-Suc-I (FromBits-Cons-O-1+[2n] prf-2 ())
bits-suc-helper Bits-Suc-I (FromBits-Cons-O-2[1+n] prf-2 ())
bits-suc-helper Bits-Suc-Cons-O ()
bits-suc-helper (Bits-Suc-Cons-I prf-1) (FromBits-Cons-O-O prf-2) = bits-suc-helper prf-1 prf-2
-- bits-suc-helper {.(_ ,, I)} {B O} (Bits-Suc-Cons-I ()) prf-2
-- bits-suc-helper {.(_ ,, I)} {B I} (Bits-Suc-Cons-I prf) ()
-- bits-suc-helper {b′ ,, I} {b ,, .O} (Bits-Suc-Cons-I prf) (FromBits-Cons-O-O prf-2) =
--   bits-suc-helper {b′} {b} prf prf-2

¬Bits-Suc-zero : ∀ {b x} →
  Bits-Suc b x →
  fromBits x ≢ zero
¬Bits-Suc-zero Bits-Suc-O = λ ()
¬Bits-Suc-zero Bits-Suc-I = λ ()
¬Bits-Suc-zero Bits-Suc-Cons-O = λ ()
¬Bits-Suc-zero {b} {x} (Bits-Suc-Cons-I {x = y} prf) eq with fromBits y in eq₁
... | zero = ¬Bits-Suc-zero prf eq₁

lifted-fromBits-toBits : ∀ {x b} →
  ToBits x b →
  fromBits b ≡ x
lifted-fromBits-toBits {.zero} {.(B O)} ToBits-zero = refl

lifted-fromBits-toBits {.(2[1+ _ ])} {.(B I ,, O)} (ToBits-2[1+n] prf Bits-Suc-O) rewrite lifted-fromBits-toBits prf = refl
lifted-fromBits-toBits {.(2[1+ _ ])} {.(B I ,, O ,, O)} (ToBits-2[1+n] prf Bits-Suc-I) rewrite lifted-fromBits-toBits prf = refl

lifted-fromBits-toBits {.(2[1+ _ ])} {b ,, I ,, O} (ToBits-2[1+n] prf Bits-Suc-Cons-O) with fromBits b in eq
lifted-fromBits-toBits {.(2[1+ _ ])} {b ,, I ,, O} (ToBits-2[1+n] prf Bits-Suc-Cons-O) | zero rewrite sym (lifted-fromBits-toBits prf) | eq = refl
lifted-fromBits-toBits {.(2[1+ _ ])} {b ,, I ,, O} (ToBits-2[1+n] prf Bits-Suc-Cons-O) | 2[1+ z ] rewrite sym (lifted-fromBits-toBits prf) | eq = refl
lifted-fromBits-toBits {.(2[1+ _ ])} {b ,, I ,, O} (ToBits-2[1+n] prf Bits-Suc-Cons-O) | 1+[2 z ] rewrite sym (lifted-fromBits-toBits prf) | eq = refl

lifted-fromBits-toBits {.(2[1+ _ ])} {b ,, O ,, O} (ToBits-2[1+n] prf (Bits-Suc-Cons-I x)) with fromBits b in eq
lifted-fromBits-toBits {.(2[1+ _ ])} {b ,, O ,, O} (ToBits-2[1+n] prf (Bits-Suc-Cons-I x)) | zero = False-elim (¬Bits-Suc-zero x eq)
lifted-fromBits-toBits {.(2[1+ _ ])} {b ,, O ,, O} (ToBits-2[1+n] {b = b₁} prf x0@(Bits-Suc-Cons-I {b = b₂} x)) | 2[1+ p ]
  rewrite sym (lower-Bits-suc x) | sym (fromBits-Bits-suc-2[1+] {b₂} eq)
        | lifted-fromBits-toBits prf = refl
lifted-fromBits-toBits {.(2[1+ _ ])} {b ,, O ,, O} (ToBits-2[1+n] prf (Bits-Suc-Cons-I x)) | 1+[2 p ]
  rewrite (lower-Bits-suc x) | sym (lifted-fromBits-toBits prf) =
    let IH = lifted-fromBits-toBits prf
    in
    {!!}


lifted-fromBits-toBits {.(1+[2 _ ])} {.(B I)} (ToBits-1+[2n]-O prf) = {!!}
lifted-fromBits-toBits {.(1+[2 _ ])} {b} (ToBits-1+[2n]-I prf x) = {!!}
lifted-fromBits-toBits {.(1+[2 _ ])} {b} (ToBits-1+[2n]-Cons-O prf x) = {!!}
lifted-fromBits-toBits {.(1+[2 _ ])} {b} (ToBits-1+[2n]-Cons-I prf x) = {!!}

-- lifted-fromBits-toBits : ∀ {x y y′ z} →
--   y′ ≡ y →
--   ToBits x y →
--   FromBits y′ z →
--   x ≡ z
-- lifted-fromBits-toBits {.zero} {.(B O)} {.(B O)} {.zero} refl ToBits-zero FromBits-O = refl
-- lifted-fromBits-toBits {.(2[1+ _ ])} {.(_ ,, O)} {.(_ ,, O)} {.zero} refl (ToBits-2[1+n] to-prf x) (FromBits-Cons-O-O from-prf) = False-elim (bits-suc-helper x from-prf)

-- lifted-fromBits-toBits {.(2[1+ zero ])} {.(B I ,, O)} {.(B I ,, O)} {z} refl (ToBits-2[1+n] ToBits-zero Bits-Suc-O) (FromBits-Cons-O-1+[2n] FromBits-I x₁) = sym x₁
-- lifted-fromBits-toBits {.(2[1+ 1+[2 _ ] ])} {.(B I ,, O ,, O)} {.(B I ,, O ,, O)} {z} refl (ToBits-2[1+n] (ToBits-1+[2n]-O to-prf) Bits-Suc-I) (FromBits-Cons-O-1+[2n] (FromBits-Cons-O-1+[2n] from-prf ()) x₁)
-- lifted-fromBits-toBits {.(2[1+ 1+[2 _ ] ])} {.(B I ,, O ,, O)} {.(B I ,, O ,, O)} {z} refl (ToBits-2[1+n] (ToBits-1+[2n]-O to-prf) Bits-Suc-I) (FromBits-Cons-O-1+[2n] (FromBits-Cons-O-2[1+n] () x) x₁)
-- lifted-fromBits-toBits {.(2[1+ 2[1+ _ ] ])} {.(_ ,, I ,, O)} {.(_ ,, I ,, O)} {z} refl (ToBits-2[1+n] (ToBits-2[1+n] to-prf x) Bits-Suc-Cons-O) (FromBits-Cons-O-1+[2n] (FromBits-Cons-I from-prf) x₁) = {!!}
-- lifted-fromBits-toBits {.(2[1+ _ ])} {.(_ ,, O ,, O)} {.(_ ,, O ,, O)} {z} refl (ToBits-2[1+n] to-prf (Bits-Suc-Cons-I x)) (FromBits-Cons-O-1+[2n] from-prf x₁) = {!!}

-- lifted-fromBits-toBits {.(2[1+ _ ])} {.(_ ,, O)} {.(_ ,, O)} {z} refl (ToBits-2[1+n] to-prf x) (FromBits-Cons-O-2[1+n] from-prf x₁) = {!!}
-- lifted-fromBits-toBits {.(1+[2 _ ])} {.(B I)} {.(B I)} {.(1+[2 zero ])} refl (ToBits-1+[2n]-O to-prf) FromBits-I = {!!}
-- lifted-fromBits-toBits {.(1+[2 _ ])} {.(_ ,, I)} {.(_ ,, I)} {.(1+[2 _ ])} refl (ToBits-1+[2n]-I to-prf x) (FromBits-Cons-I from-prf) = {!!}
-- lifted-fromBits-toBits {.(1+[2 _ ])} {.(_ ,, I)} {.(_ ,, I)} {.(1+[2 _ ])} refl (ToBits-1+[2n]-Cons-O to-prf x) (FromBits-Cons-I from-prf) = {!!}
-- lifted-fromBits-toBits {.(1+[2 _ ])} {.(_ ,, I)} {.(_ ,, I)} {.(1+[2 _ ])} refl (ToBits-1+[2n]-Cons-I to-prf x) (FromBits-Cons-I from-prf) = {!!}


-- lifted-fromBits-toBits {.zero} {.(B O)} {.zero} ToBits-zero FromBits-O = refl
-- lifted-fromBits-toBits {2[1+ a ]} {B O ,, O} {.zero} (ToBits-2[1+n] {b = b₁} to-prf ()) (FromBits-Cons-O-O from-prf)
-- lifted-fromBits-toBits {2[1+ a ]} {B I ,, O} {.zero} (ToBits-2[1+n] {b = b₁} to-prf x) (FromBits-Cons-O-O ())
-- lifted-fromBits-toBits {2[1+ a ]} {b ,, .O ,, O} {.zero} (ToBits-2[1+n] {b = b₁} to-prf x) (FromBits-Cons-O-O (FromBits-Cons-O-O from-prf)) =
--   False-elim (bits-suc-helper x from-prf)
-- lifted-fromBits-toBits {.(2[1+ _ ])} {.(_ ,, O)} {z} (ToBits-2[1+n] to-prf x) (FromBits-Cons-O-1+[2n] from-prf x₁)
--   rewrite lifted-fromBits-toBits to-prf {!!} = {!!}
-- lifted-fromBits-toBits {.(2[1+ _ ])} {.(_ ,, O)} {z} (ToBits-2[1+n] to-prf x) (FromBits-Cons-O-2[1+n] from-prf x₁) = {!!}
-- lifted-fromBits-toBits {.(1+[2 _ ])} {.(B I)} {.(1+[2 zero ])} (ToBits-1+[2n]-O to-prf) FromBits-I = {!!}
-- lifted-fromBits-toBits {.(1+[2 _ ])} {.(_ ,, I)} {.(1+[2 _ ])} (ToBits-1+[2n]-I to-prf x) (FromBits-Cons-I from-prf) = {!!}
-- lifted-fromBits-toBits {.(1+[2 _ ])} {.(_ ,, I)} {.(1+[2 _ ])} (ToBits-1+[2n]-Cons-O to-prf x) (FromBits-Cons-I from-prf) = {!!}
-- lifted-fromBits-toBits {.(1+[2 _ ])} {.(_ ,, I)} {.(1+[2 _ ])} (ToBits-1+[2n]-Cons-I to-prf x) (FromBits-Cons-I from-prf) = {!!}

fromBits-toBits : ∀ {x : ℕᵇ} →
  fromBits (toBits x) ≡ x
fromBits-toBits {x} with ToBits-exists {x}
... | .(B O) , ToBits-zero = refl
... | .(_ ,, O) , ToBits-2[1+n] snd x = {!!}
... | .(B I) , ToBits-1+[2n]-O snd = {!!}
... | fst , ToBits-1+[2n]-I snd x = {!!}
... | fst , ToBits-1+[2n]-Cons-O snd x = {!!}
... | fst , ToBits-1+[2n]-Cons-I snd x = {!!}

-- fromBits-toBits {zero} = refl
-- fromBits-toBits {2[1+ x ]} with fromBits (Bits-suc (toBits x)) in eq
-- ... | zero rewrite fromBits-suc-comm {toBits x} | fromBits-toBits {x} = False-elim (ℕᵇ-suc-nonzero eq)
-- ... | 2[1+ p ] rewrite fromBits-suc-comm {toBits x} | fromBits-toBits {x} | suc-2[1+] eq = refl
-- ... | 1+[2 p ] rewrite fromBits-suc-comm {toBits x} | fromBits-toBits {x} | suc-double′ eq = refl
-- -- fromBits-toBits {2[1+ x ]} rewrite fromBits-suc-comm {toBits x} | fromBits-toBits {x} with ℕᵇ-suc x in eq
-- -- ... | zero = {!!}
-- -- ... | 2[1+ p ] = {!!}
-- -- ... | 1+[2 p ] = {!!}

-- -- Goal: fromBits (toBits 1+[2 x ] | toBits x) ≡ 1+[2 x ]
-- fromBits-toBits {1+[2 zero ]} = refl
-- fromBits-toBits {1+[2 2[1+ zero ] ]} = refl
-- fromBits-toBits {1+[2 2[1+ 2[1+ zero ] ] ]} = refl
-- fromBits-toBits {1+[2 2[1+ 2[1+ 2[1+ x ] ] ] ]} rewrite fromBits-suc-comm {toBits x} = {!!}
-- fromBits-toBits {1+[2 2[1+ 2[1+ 1+[2 x ] ] ] ]} = {!!}
-- fromBits-toBits {1+[2 2[1+ 1+[2 x ] ] ]} with toBits x in eq
-- ... | B O = {!!}
-- ... | B I = {!!}
-- ... | p ,, O = {!!}
-- ... | p ,, I = {!!}
-- fromBits-toBits {1+[2 1+[2 x ] ]} = {!!}



-- fromBits-toBits {1+[2 zero ]} | B O = refl
-- ... | p ,, I = {!!}
-- ... | p ,, O with fromBits p in eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, O | zero = {!!}
-- fromBits-toBits {1+[2 x ]} | p ,, O | 2[1+ q ] = {!!}
-- fromBits-toBits {1+[2 x ]} | p ,, O | 1+[2 q ] = {!!}

-- fromBits-toBits {1+[2 1+[2 zero ] ]} | B I = refl
-- fromBits-toBits {1+[2 1+[2 1+[2 x ] ] ]} | B I with toBits x
-- fromBits-toBits {1+[2 1+[2 1+[2 x ] ] ]} | B I | B O with () ← eq
-- fromBits-toBits {1+[2 1+[2 1+[2 x ] ] ]} | B I | B I with () ← eq

-- fromBits-toBits {1+[2 1+[2 x ] ]} | B O with toBits x
-- fromBits-toBits {1+[2 1+[2 x ] ]} | B O | B O with () ← eq
-- fromBits-toBits {1+[2 1+[2 x ] ]} | B O | B I with () ← eq




-- fromBits-toBits {x} with x in eq₁
-- fromBits-toBits {x} | zero = refl
-- fromBits-toBits {x} | 2[1+ p ] with fromBits (Bits-suc (toBits p)) in eq₂
-- fromBits-toBits {x} | 2[1+ p ] | zero = False-elim (fromBits-Bits-suc-nonzero {toBits p} eq₂)
-- fromBits-toBits {x} | 2[1+ p ] | 2[1+ q ]
--   rewrite sym (fromBits-Bits-suc-2[1+] {toBits p} eq₂)
--         | fromBits-toBits {p} = refl
-- fromBits-toBits {x} | 2[1+ p ] | 1+[2 q ]
--   rewrite fromBits-suc-comm {toBits p}
--         | fromBits-toBits {p}
--         | suc-double′ {p} {q} eq₂ = refl
--   -- rewrite sym (fromBits-Bits-suc-1+[2] eq₂) = ?
-- fromBits-toBits {1+[2 x ]} | 1+[2 p ] with toBits p in eq₂
-- fromBits-toBits {1+[2 x ]} | 1+[2 zero ] | B O = refl
-- fromBits-toBits {1+[2 x ]} | 1+[2 1+[2 p ] ] | B O with refl ← eq₁ | toBits p
-- ... | B O with () ← eq₂
-- ... | B I with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | 1+[2 p ] | B I with refl ← eq₁ | p in eq₃
-- ... | 1+[2 q ] with toBits q in eq₄
-- fromBits-toBits {1+[2 p ]} | 1+[2 p ] | B I | 1+[2 zero ] | B O = refl
-- fromBits-toBits {1+[2 p ]} | 1+[2 p ] | B I | 1+[2 1+[2 q ] ] | B O with toBits q
-- fromBits-toBits {1+[2 p ]} | 1+[2 p ] | B I | 1+[2 1+[2 q ] ] | B O | B O with () ← eq₄
-- fromBits-toBits {1+[2 p ]} | 1+[2 p ] | B I | 1+[2 1+[2 q ] ] | B O | B I with () ← eq₄
-- -- fromBits-toBits {1+[2 p ]} | 1+[2 p ] B I | refl | 1+[2 zero ] | B O = ?
-- -- fromBits-toBits {1+[2 p ]} | 1+[2 p ] B I | refl | 1+[2 1+[2 q ] ] | B O = ?
-- fromBits-toBits {1+[2 x ]} | 1+[2 p ] | q ,, O = {!!}
-- fromBits-toBits {1+[2 x ]} | 1+[2 p ] | q ,, I = {!!}

-- fromBits-toBits {x} with toBits x in eq
-- fromBits-toBits {zero} | B O = refl
-- fromBits-toBits {1+[2 x ]} | B O with toBits x
-- fromBits-toBits {1+[2 x ]} | B O | B O with () ← eq
-- fromBits-toBits {1+[2 x ]} | B O | B I with () ← eq
-- fromBits-toBits {1+[2 x ]} | B I with fromBits (toBits x) in eq₂
-- fromBits-toBits {1+[2 x ]} | B I | zero rewrite sym eq₂ | fromBits-toBits {x} = refl
-- fromBits-toBits {1+[2 x ]} | B I | 2[1+ p ] with toBits x
-- fromBits-toBits {1+[2 x ]} | B I | 2[1+ p ] | B O with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | B I | 2[1+ p ] | B I with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | B I | 1+[2 p ] with toBits x
-- fromBits-toBits {1+[2 x ]} | B I | 1+[2 p ] | B O with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | B I | 1+[2 p ] | B I with () ← eq
-- fromBits-toBits {1+[2 x ]} | p ,, O with fromBits p
-- fromBits-toBits {1+[2 x ]} | p ,, O | zero with toBits x
-- fromBits-toBits {1+[2 x ]} | p ,, O | zero | B O with () ← eq
-- fromBits-toBits {1+[2 x ]} | p ,, O | zero | B I with () ← eq
-- fromBits-toBits {1+[2 x ]} | p ,, O | 2[1+ q ] with toBits x
-- fromBits-toBits {1+[2 x ]} | p ,, O | 2[1+ q ] | B O with () ← eq
-- fromBits-toBits {1+[2 x ]} | p ,, O | 2[1+ q ] | B I with () ← eq
-- fromBits-toBits {1+[2 x ]} | p ,, O | 1+[2 q ] with toBits x
-- fromBits-toBits {1+[2 x ]} | p ,, O | 1+[2 q ] | B O with () ← eq
-- fromBits-toBits {1+[2 x ]} | p ,, O | 1+[2 q ] | B I with () ← eq
-- fromBits-toBits {1+[2 x ]} | p ,, I with x in eq₁
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ q ] rewrite sym (invert-Bits-cons-left eq)
--   with fromBits (Bits-suc (toBits q)) in eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ q ] | zero = False-elim (fromBits-Bits-suc-nonzero {toBits q} eq₂)
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ q ] | 2[1+ r ] =
--   let a = fromBits-Bits-suc-2[1+] {toBits q} eq₂
--       b = fromBits-toBits {q}
--   in
--   cong 1+[2_] (cong 2[1+_] (trans (sym a) b))
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ zero ] | 1+[2 zero ] = refl
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 2[1+ q ] ] | 1+[2 zero ] =
--   let
--     a = invert-1+[2] eq₂
--   in
--   False-elim (fromBits-Bits-suc-nonzero {toBits q} a)
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] with toBits q
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] | B O with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] | B I with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] | B O ,, O with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] | B I ,, O with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] | w ,, O ,, O with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] | w ,, I ,, O with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] | w ,, I with fromBits (Bits-suc w)
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] | w ,, I | zero with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] | w ,, I | 2[1+ r ] with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ 1+[2 q ] ] | 1+[2 zero ] | w ,, I | 1+[2 r ] with () ← eq₂
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ q ] | 1+[2 2[1+ r ] ] = {!!}
-- fromBits-toBits {1+[2 x ]} | p ,, I | 2[1+ q ] | 1+[2 1+[2 r ] ] = {!!}
-- fromBits-toBits {1+[2 x ]} | p ,, I | 1+[2 q ] = {!!}
-- fromBits-toBits {2[1+ x ]} | p ,, O with fromBits p in eq₁
-- fromBits-toBits {2[1+ x ]} | p ,, O | zero = {!!}
-- fromBits-toBits {2[1+ x ]} | p ,, O | 2[1+ q ] = {!!}
-- fromBits-toBits {2[1+ x ]} | p ,, O | 1+[2 q ] = {!!}
  -- let IH = fromBits-toBits {x}
  --     w = invert-Bits-cons-left eq
  -- in
  -- {!!}
-- fromBits-toBits {zero} = refl
-- fromBits-toBits {2[1+ x ]} rewrite fromBits-suc {toBits x} | fromBits-toBits {x} = {!!}
-- fromBits-toBits {1+[2 x ]} rewrite fromBits-toBits {x} with toBits x in eq
-- fromBits-toBits {1+[2 zero ]} | B O = refl
-- fromBits-toBits {1+[2 1+[2 x ] ]} | B O with toBits x
-- fromBits-toBits {1+[2 1+[2 x ] ]} | B O | B O with () ← eq
-- fromBits-toBits {1+[2 1+[2 x ] ]} | B O | B I with () ← eq
-- fromBits-toBits {1+[2 2[1+ x ] ]} | B O with () ← eq
-- fromBits-toBits {1+[2 x ]} | B I with 1+[2 zero ] ← x = refl
-- fromBits-toBits {1+[2 x ]} | y ,, O with fromBits y in eq₂
-- fromBits-toBits {1+[2 x ]} | y ,, O | zero = {!!}
-- fromBits-toBits {1+[2 x ]} | y ,, O | 2[1+ q ] = {!!}
-- fromBits-toBits {1+[2 x ]} | y ,, O | 1+[2 q ] = {!!}
-- fromBits-toBits {1+[2 x ]} | y ,, I = {!!}

fromBits-zero : ∀ {x} →
  ¬ Has-One x →
  fromBits x ≡ zero
fromBits-zero {B O} prf = refl
fromBits-zero {B I} prf = False-elim (prf Has-One-I)
fromBits-zero {x ,, O} prf rewrite fromBits-zero {x} (invert¬Has-One prf) = refl
fromBits-zero {x ,, I} prf = False-elim (prf Has-One-Here)

fromBits-normalize : ∀ {x} →
  fromBits x ≡ fromBits (normalize x)
fromBits-normalize {x} with dec-Has-One x
... | inj₂ ¬p rewrite normalize-¬Has-One ¬p = fromBits-zero ¬p
fromBits-normalize {B I} | inj₁ p = refl
fromBits-normalize {x ,, O} | inj₁ p with dec-Has-One x
... | inj₁ q rewrite fromBits-normalize {x} = refl
fromBits-normalize {x ,, O} | inj₁ (Has-One-There p) | inj₂ ¬q = False-elim (¬q p)
fromBits-normalize {x ,, I} | inj₁ p with dec-Has-One x
... | inj₁ q rewrite fromBits-normalize {x} = refl
... | inj₂ ¬q rewrite fromBits-zero ¬q = refl

normalize-Bits-suc : ∀ {x} →
  normalize (Bits-suc x) ≡ Bits-suc x
normalize-Bits-suc {x} = {!!}

_ : normalize (B O ,, O) ≡ B O
_ = refl

-- -- Normalized-unique-O : ∀ {x} →
-- --   Normalized x →
-- --   fromBits x ≡ zero →
-- --   x ≡ B O
-- -- Normalized-unique-O {B O} eq₁ eq₂ = refl
-- -- Normalized-unique-O {x ,, O} eq₁ eq₂ with Normalized-unique-O {x} {!!} {!!}
-- -- ... | refl = {!!}

_ : toBits (fromBits (B I)) ≡ B I
_ = refl

_ : fromBits (B I) ≡ 1+[2 zero ]
_ = refl

toBits-fromBits : ∀ {x : Bits} →
  Normalized x →
  toBits (fromBits x) ≡ x
toBits-fromBits {B O} prf = refl
toBits-fromBits {B I} prf = {!!}
toBits-fromBits {x ,, x₁} prf = {!!}

-- ℕ→Bits→ℕ : ∀ {x : ℕ} →
--   Bits→ℕ (ℕ→Bits x) ≡ x
-- ℕ→Bits→ℕ {x} rewrite fromBits-toBits {fromℕ' x} | toℕ-fromℕ' x = refl

-- -- Bits→ℕ→Bits : ∀ {x : Bits} →
-- --   ℕ→Bits (Bits→ℕ x) ≡ x


-- -- Bits-suc-normalize-comm : ∀ {x} →
-- --   Bits-suc (normalize x) ≡ normalize (Bits-suc x)
-- -- Bits-suc-normalize-comm {x} rewrite normalize-Bits-suc {x} = {!!}
-- -- Bits-suc-normalize {B O} = refl
-- -- Bits-suc-normalize {B I} = refl
-- -- Bits-suc-normalize {x ,, O} = {!!}
-- -- Bits-suc-normalize {x ,, I} rewrite normalize-Has-One (Bits-suc-Has-One {x ,, I}) = refl

-- -- Bits-suc-normalize {B O} = refl
-- -- Bits-suc-normalize {B I} = refl
-- -- Bits-suc-normalize {x ,, O} = {!!}
-- -- Bits-suc-normalize {x ,, I} rewrite sym (Bits-suc-normalize {x}) = {!!}

-- toBits-normalize : ∀ {x} →
--   toBits x ≡ normalize (toBits x)
-- toBits-normalize {zero} = refl
-- toBits-normalize {2[1+ x ]} rewrite toBits-normalize {x} | normalize-Bits-suc {normalize (toBits x)} = {!!}
-- toBits-normalize {1+[2 x ]} = refl

-- is-normal : (Bits → Bits) → Set
-- is-normal f =
--   ∀ x → f (normalize x) ≡ normalize (f (normalize x))

-- Bits-lift : (f : Bits → Bits) → (ℕ → ℕ)
-- Bits-lift f = Bits→ℕ ∘ f ∘ ℕ→Bits

-- Bits-lower : (ℕ → ℕ) → (Bits → Bits)
-- Bits-lower f = ℕ→Bits ∘ f ∘ Bits→ℕ

-- Bits-transport : ((Bits → Bits) → Set) → ((ℕ → ℕ) → Set)
-- Bits-transport P = P ∘ Bits-lower

-- -- toBits-fromBits-normalize : ∀ {x : Bits} →
-- --   toBits

-- -- fromBits : Bits → ℕ
-- -- fromBits (B x) = fromBit x
-- -- fromBits (b ,, x) = fromBit x + 2 * (fromBits b)

-- -- toBits : ℕ → Bits
-- -- toBits zero = B O
-- -- toBits (suc n) = Bits-suc (toBits n)

-- -- _ : fromBits (toBits 4) ≡ 4
-- -- _ = refl

-- -- _ : fromBits (toBits 11) ≡ 11
-- -- _ = refl

-- -- fromBits-suc : ∀ {x m} →
-- --   fromBits x ≡ m →
-- --   fromBits (Bits-suc x) ≡ suc m
-- -- fromBits-suc {B O} {.(fromBits (B O))} refl = refl
-- -- fromBits-suc {B I} {.(fromBits (B I))} refl = refl
-- -- fromBits-suc {x ,, O} {.(fromBits (x ,, O))} refl = refl
-- -- fromBits-suc {x ,, I} {.(fromBits (x ,, I))} refl with fromBits-suc {x} {fromBits x} refl
-- -- ... | eq rewrite eq =
-- --   solve 1 (λ z → (con 1 :+ z) :+ ((con 1 :+ z) :+ con 0) := con 1 :+ (con 1 :+ (z :+ (z :+ con 0)))) refl (fromBits x)

-- -- fromBits-toBits : ∀ {n} →
-- --   fromBits (toBits n) ≡ n
-- -- fromBits-toBits {zero} = refl
-- -- fromBits-toBits {suc n} rewrite fromBits-suc {toBits n} refl = cong suc (fromBits-toBits {n})

-- -- -- shiftBits : ∀ {m} →
-- -- --   toBits (m + m) ≡ toBits m ,, O
-- -- -- shiftBits {zero} = {!!}
-- -- -- shiftBits {suc m} = {!!}

-- -- toBits-fromBits : ∀ {x} →
-- --   toBits (fromBits x) ≡ x
-- -- toBits-fromBits {B O} = refl
-- -- toBits-fromBits {B I} = refl
-- -- toBits-fromBits {x ,, O} rewrite sym (toBits-fromBits {x}) =
-- --   let eq = toBits-fromBits {x}
-- --   in {!!}
-- -- toBits-fromBits {x ,, I} = {!!}

-- split : ℕᵇ → Maybe Bit × ℕᵇ
-- split zero     = nothing , zero
-- split 2[1+ n ] = just O , n
-- split 1+[2 n ] = just I , n

-- head : ℕᵇ → Maybe Bit
-- head = proj₁ ∘ split

-- tail : ℕᵇ → ℕᵇ
-- tail = proj₂ ∘ split

-- -- singleton

-- singleton-Bits : ℕ → Bits
-- singleton-Bits zero = B I
-- singleton-Bits (suc n) = singleton-Bits n ,, O

-- singleton : ℕ → ℕ
-- singleton = Bits→ℕ ∘ singleton-Bits

-- Bits→ℕ-suc : ∀ {x} →
--   Bits→ℕ (x ,, O) ≡ 2 * Bits→ℕ x
-- Bits→ℕ-suc {B O} = refl
-- Bits→ℕ-suc {B I} = refl
-- Bits→ℕ-suc {x ,, O} rewrite Bits→ℕ-suc {x} | toℕ-double (double (fromBits x)) | toℕ-double (fromBits x) = refl
-- Bits→ℕ-suc {x ,, I} rewrite Bits→ℕ-suc {x} = refl

-- _ : singleton 3 ≡ 8
-- _ = refl

-- _ : singleton 11 ≡ (2 ^ 11)
-- _ = refl

-- singleton-Bits-suc : ∀ {n} →
--   singleton-Bits (suc n) ≡ singleton-Bits n ,, O
-- singleton-Bits-suc {zero} = refl
-- singleton-Bits-suc {suc n} = refl

-- singleton-suc : ∀ {n} →
--   singleton (suc n) ≡ 2 * singleton n
-- singleton-suc {zero} = refl
-- singleton-suc {suc n}
--   rewrite toℕ-double (fromBits (singleton-Bits n))
--         | toℕ-double (double (fromBits (singleton-Bits n)))
--         | toℕ-double (fromBits (singleton-Bits n)) = refl

-- singleton^ : ∀ {n} →
--   singleton n ≡ 2 ^ n
-- singleton^ {zero} = refl
-- singleton^ {suc n} rewrite singleton-suc {n} | singleton^ {n} = refl

-- -- data Divides : ℕ → ℕ → Set where
-- --   mk-Divides : ∀ {m n k} →
-- --     m ≡ (n * k) →
-- --     Divides m n

-- data _Bits∈_ : ℕ → Bits → Set where
--   Bits∈-zero-base : zero Bits∈ B I
--   Bits∈-zero : ∀ {x} → zero Bits∈ (x ,, I)
--   Bits∈-suc : ∀ {n b y} →
--     n Bits∈ b →
--     suc n Bits∈ (b ,, y)

-- Bits∈shift : ∀ {x n b} →
--   n Bits∈ x →
--   (suc n) Bits∈ (x ,, b)
-- Bits∈shift {.(B I)} {.zero} {O} Bits∈-zero-base = Bits∈-suc Bits∈-zero-base
-- Bits∈shift {.(B I)} {.zero} {I} Bits∈-zero-base = Bits∈-suc Bits∈-zero-base
-- Bits∈shift {.(_ ,, I)} {.zero} {b} Bits∈-zero = Bits∈-suc Bits∈-zero
-- Bits∈shift {.(_ ,, _)} {.(suc _)} {b} (Bits∈-suc prf) = Bits∈-suc (Bits∈shift prf)

-- Has-One-inhabited : ∀ {x} →
--   Has-One x →
--   ∃[ n ] n Bits∈ x
-- Has-One-inhabited {.(B I)} Has-One-I = zero , Bits∈-zero-base
-- Has-One-inhabited {.(_ ,, I)} Has-One-Here = zero , Bits∈-zero
-- Has-One-inhabited {.(_ ,, O)} (Has-One-There prf) =
--   let n , p = Has-One-inhabited prf
--   in
--   suc n , Bits∈shift p


-- _∈_ : ℕ → ℕ → Set
-- _∈_ n x = n Bits∈ (ℕ→Bits x)

-- Bit-and : Bit → Bit → Bit
-- Bit-and O O = O
-- Bit-and O I = O
-- Bit-and I O = O
-- Bit-and I I = I

-- Bit-or : Bit → Bit → Bit
-- Bit-or O O = O
-- Bit-or O I = I
-- Bit-or I O = I
-- Bit-or I I = I

-- _Bits∪_ : Bits → Bits → Bits
-- B x Bits∪ B x₁ = B (Bit-or x x₁)
-- B x Bits∪ (y ,, x₁) = y ,, Bit-or x x₁
-- (x ,, x₁) Bits∪ B x₂ = x ,, Bit-or x₁ x₂
-- (x ,, x₁) Bits∪ (y ,, x₂) = (x Bits∪ y) ,, Bit-or x₁ x₂
-- -- B x Bits∪ B y = B (Bit-or x y)
-- -- B x Bits∪ (y ,, b) = (B x Bits∪ y) ,, b
-- -- (x ,, y) Bits∪ B b = (B b Bits∪ x) ,, y
-- -- (x ,, x₁) Bits∪ (y ,, x₂) = (x Bits∪ y) ,, Bit-or x₁ x₂

-- _∪_ : ℕ → ℕ → ℕ
-- _∪_ x y = Bits→ℕ ((ℕ→Bits x) Bits∪ (ℕ→Bits y))

-- Bits∪-inj₁ : ∀ {x y n} →
--   n Bits∈ x →
--   n Bits∈ (x Bits∪ y)
-- Bits∪-inj₁ {B .I} {B O} {.zero} Bits∈-zero-base = Bits∈-zero-base
-- Bits∪-inj₁ {B .I} {B I} {.zero} Bits∈-zero-base = Bits∈-zero-base
-- Bits∪-inj₁ {B .I} {y ,, O} {.zero} Bits∈-zero-base = Bits∈-zero
-- Bits∪-inj₁ {B .I} {y ,, I} {.zero} Bits∈-zero-base = Bits∈-zero
-- Bits∪-inj₁ {x ,, .I} {B O} {.zero} Bits∈-zero = Bits∈-zero
-- Bits∪-inj₁ {x ,, .I} {B I} {.zero} Bits∈-zero = Bits∈-zero
-- Bits∪-inj₁ {x ,, x₁} {B O} {.(suc _)} (Bits∈-suc prf) = Bits∈-suc prf
-- Bits∪-inj₁ {x ,, x₁} {B I} {.(suc _)} (Bits∈-suc prf) = Bits∈-suc prf
-- Bits∪-inj₁ {x ,, .I} {y ,, O} {.zero} Bits∈-zero = Bits∈-zero
-- Bits∪-inj₁ {x ,, .I} {y ,, I} {.zero} Bits∈-zero = Bits∈-zero
-- Bits∪-inj₁ {x ,, x₁} {y ,, x₂} {.(suc _)} (Bits∈-suc prf) = Bits∈-suc (Bits∪-inj₁ prf)

-- -- lift-binary-prop :
-- --   (P : Bits → Bits → Set) →
-- --   (∀ x y → P x y) →
-- --   Σ (ℕ → ℕ → Set) λ Q →
-- --   (∀ a b → Q a b)
-- -- lift-binary-prop P prf =
-- --   (λ a b → P (ℕ→Bits a) (ℕ→Bits b))
-- --   ,
-- --   λ a b → {!!}
-- --       -- prf (toBits (fromℕ.helper a a a)) (toBits (fromℕ.helper b b b))

-- Bits∪-inj₁-prop : Bits → Bits → Set
-- Bits∪-inj₁-prop x y = ∀ n → n Bits∈ x → n Bits∈ (x Bits∪ y)

-- Bits-zero : ∀ {b} →
--   Bits→ℕ (b ,, O) ≡ 0 →
--   Bits→ℕ b ≡ 0
-- Bits-zero {b} prf with Bits→ℕ (b ,, O) in eq
-- Bits-zero {B O} prf | zero = refl
-- Bits-zero {b ,, O} refl | zero with fromBits b
-- ... | zero = refl

-- Bits∈-nonzero : ∀ {n b} →
--   n Bits∈ b →
--   Bits→ℕ b ≢ 0
-- Bits∈-nonzero {n} {B O} () eq
-- Bits∈-nonzero {.zero} {B I} Bits∈-zero-base ()
-- Bits∈-nonzero {.(suc _)} {b ,, O} (Bits∈-suc prf) eq with Bits∈-nonzero prf (Bits-zero {b} eq)
-- ... | ()

-- -- suc-∪-nonempty : ∀ {x y z} →
-- --   z ≡ (suc x ∪ y) →
-- --   ∃[ n ] n ∈ z
-- -- suc-∪-nonempty {zero} {zero} {.(1 ∪ zero)} refl = zero , Bits∈-zero
-- -- suc-∪-nonempty {zero} {suc y} {.(1 ∪ suc y)} refl = zero , {!!}
-- -- suc-∪-nonempty {suc x} {y} {z} eq = {!!}

-- ℕᵇ-suc-not-0 : ∀ {x} →
--   toℕ (ℕᵇ-suc x) ≢ 0
-- ℕᵇ-suc-not-0 {zero} = λ ()
-- ℕᵇ-suc-not-0 {2[1+ x ]} = λ ()
-- ℕᵇ-suc-not-0 {1+[2 x ]} = λ ()

-- toℕ-nonzero : ∀ {x} →
--   toℕ x ≢ 0 →
--   toBits x ≢ B O
-- toℕ-nonzero {zero} prf = λ _ → prf refl
-- toℕ-nonzero {2[1+ x ]} prf = λ ()
-- toℕ-nonzero {1+[2 x ]} prf = λ ()

-- toℕ-zero : ∀ {x} →
--   toBits x ≡ B O →
--   toℕ x ≡ 0
-- toℕ-zero {zero} prf = refl


-- nonzero-not-O : ∀ {x} →
--   toBits (ℕᵇ-suc (fromℕ' x)) ≢ B O
-- nonzero-not-O {x} prf = ℕᵇ-suc-not-0 {fromℕ' x} (toℕ-zero {ℕᵇ-suc (fromℕ' x)} prf)

-- -- Has-One-exists : ∀ {x} →
-- --   normalize

-- -- nonzero-suc : ∀ {x} →
-- --   normalize x ≢ B O →
-- --   ∃[ y ] x ≡ Bits-suc y
-- -- nonzero-suc {B O} prf = False-elim (prf refl)
-- -- nonzero-suc {B I} prf = (B O) , refl
-- -- nonzero-suc {x ,, O} prf =
-- --   let y , p = nonzero-suc {x} {!!}
-- --   in
-- --   Bits-suc (y) , {!!}
-- -- nonzero-suc {x ,, I} prf = {!!}

-- shiftO : ∀ {x} →
--   Bits→ℕ x ≡ 0 →
--   Bits→ℕ (x ,, O) ≡ 0
-- shiftO {B O} prf = refl
-- shiftO {x ,, O} prf with fromBits x
-- ... | zero = refl

-- nonzero→Has-One′ : ∀ {x} →
--   Bits→ℕ x ≢ 0 →
--   Has-One x
-- nonzero→Has-One′ {B O} prf = False-elim (prf refl)
-- nonzero→Has-One′ {B I} prf = Has-One-I
-- nonzero→Has-One′ {x ,, O} prf =
--   let p = nonzero→Has-One′ {x} (λ eq → prf (shiftO {x} eq))
--   in
--   Has-One-There p
-- nonzero→Has-One′ {x ,, I} prf = Has-One-Here

-- nonzero→Has-One : ∀ {x} →
--   x ≢ 0 →
--   Has-One (ℕ→Bits x)
-- nonzero→Has-One = {!!}

-- nonempty→nonzero : ∀ {x n} →
--   n ∈ x →
--   x ≢ 0
-- nonempty→nonzero {suc x} {n} prf = λ ()

-- nonzero→nonempty : ∀ {x} →
--   x ≢ 0 →
--   ∃[ n ] n ∈ x
-- nonzero→nonempty {zero} prf = False-elim (prf refl)
-- nonzero→nonempty {suc x} prf = {!!}

-- Bits∪-inj₁-transport : ∀ {x y x∪y n b} →
--   b ≡ ℕ→Bits x →
--   x∪y ≡ (x ∪ y) →
--   n Bits∈ b →
--   n ∈ x∪y
-- Bits∪-inj₁-transport {zero} {y} {x∪y} {n} {b} eq₁ eq₂ prf rewrite eq₁ = False-elim (Bits∈-nonzero prf refl)
-- Bits∪-inj₁-transport {suc x} {y} {x∪y} {.zero} {.(B I)} eq₁ eq₂ prf@Bits∈-zero-base rewrite (sym eq₂) = {!!} --with ℕ→Bits x∪y in eq
-- -- Bits∪-inj₁-transport {suc x} {y} {.(toℕ (fromBits (toBits (ℕᵇ-suc (fromℕ' x)) Bits∪ toBits (fromℕ' y))))} {.zero} {.(B I)} eq₁ refl Bits∈-zero-base | B O = {!!}
-- -- ... | B I = Bits∈-zero-base
-- -- ... | z ,, x₁ = {!!}
-- Bits∪-inj₁-transport {suc x} {y} {x∪y} {.zero} {.(_ ,, I)} eq₁ eq₂ Bits∈-zero = {!!}
-- Bits∪-inj₁-transport {suc x} {y} {x∪y} {.(suc _)} {.(_ ,, _)} eq₁ eq₂ (Bits∈-suc prf) = {!!}
-- -- ... | zero = False-elim (Bits∈-nonzero {!!} {!!})
-- -- ... | suc z = {!!}
-- -- -- Bits∪-inj₁-transport {zero} {suc y} {zero} {.zero} {.(B I)} eq₁ eq₂ prf | B I with zero ∪ suc y
-- -- -- ... | z = {!!}
-- -- -- Bits∪-inj₁-transport {x} {y} {suc x∪y} {.zero} {.(B I)} eq₁ eq₂ Bits∈-zero-base | B I = {!!}
-- -- -- Bits∪-inj₁-transport {x} {y} {x∪y} {.zero} {.(_ ,, I)} eq₁ eq₂ Bits∈-zero = {!!}
-- -- -- Bits∪-inj₁-transport {x} {y} {x∪y} {.(suc _)} {.(_ ,, _)} eq₁ eq₂ (Bits∈-suc prf) = {!!}

-- -- Bits∪∈ : ∀ {x y n b} →
-- --   b ≡ (ℕ→Bits x Bits∪ ℕ→Bits y) →
-- --   n Bits∈ b →
-- --   n ∈ (x ∪ y)
-- -- Bits∪∈ {zero} {suc y} {.zero} {.(B I)} eq Bits∈-zero-base with ℕ→Bits (suc y)
-- -- ... | B I = Bits∈-zero
-- -- Bits∪∈ {suc x} {zero} {.zero} {.(B I)} eq Bits∈-zero-base with ℕ→Bits (suc x)
-- -- ... | B I = Bits∈-zero
-- -- Bits∪∈ {suc x} {suc y} {.zero} {.(B I)} eq Bits∈-zero-base with ℕ→Bits (suc x) | ℕ→Bits (suc y)
-- -- ... | B O | B I = Bits∈-zero
-- -- ... | B I | B O = Bits∈-zero
-- -- ... | B I | B I = Bits∈-zero
-- -- ... | B O | w₁ ,, O = False-elim (Bits-ttttt eq)
-- -- ... | B O | w₁ ,, I = False-elim (Bits-apart eq)
-- -- ... | B I | w₁ ,, O = False-elim (Bits-apart eq)
-- -- ... | B I | w₁ ,, I = False-elim (Bits-apart eq)
-- -- ... | w ,, O | w₁ ,, O = False-elim (Bits-apart eq)
-- -- ... | w ,, I | w₁ ,, O = False-elim (Bits-apart eq)
-- -- ... | w ,, O | w₁ ,, I = False-elim (Bits-apart eq)
-- -- ... | w ,, I | w₁ ,, I = False-elim (Bits-apart eq)
-- -- Bits∪∈ {zero} {suc y} {.zero} {.(_ ,, I)} eq Bits∈-zero with ℕ→Bits (suc y)
-- -- Bits∪∈ {zero} {suc y} {.zero} {.(_ ,, I)} eq Bits∈-zero | p ,, I with Bits∪∈ {_} {_} {_} {p} {!!} {!!}
-- -- ... | z = {!!}
-- -- Bits∪∈ {suc x} {zero} {.zero} {.(_ ,, I)} eq Bits∈-zero = {!!}
-- -- Bits∪∈ {suc x} {suc y} {.zero} {.(_ ,, I)} eq Bits∈-zero = {!!}
-- -- Bits∪∈ {x} {y} {.(suc _)} {.(_ ,, _)} eq (Bits∈-suc prf) = {!!}

-- -- Bits∈-transport : ∀ {n x} →
-- --   n Bits∈ (ℕ→Bits x) →
-- --   n ∈ x
-- -- Bits∈-transport {n} {x} prf with ℕ→Bits x
-- -- Bits∈-transport {n} {zero} prf | B x = prf
-- -- Bits∈-transport {n} {zero} prf | z ,, x = prf
-- -- Bits∈-transport {n} {suc x} prf | z = prf

-- ∪-inj₁ : ∀ {x y n} →
--   n ∈ x →
--   n ∈ (x ∪ y)
-- ∪-inj₁ {x} {y} {n} prf =
--   let
--     p = Bits∪-inj₁ {ℕ→Bits x} {ℕ→Bits y} {n} prf
--   in
--   {!!}
--   -- let
--   --   Q , f = lift-binary-prop Bits∪-inj₁-prop (λ a b n prf → Bits∪-inj₁ prf)
--   -- in
--   -- f ? ? ? ?

-- -- _Bits∈_ : ℕ → Bits → Set
-- -- zero Bits∈ x = {!!}
-- -- suc n Bits∈ x = {!!}

-- _ : 3 ∈ ((2 ^ 1) + (2 ^ 3) + (2 ^ 7))
-- _ = Bits∈-suc (Bits∈-suc (Bits∈-suc Bits∈-zero))

-- ex1 : ¬ 3 ∈ ((2 ^ 1) + (2 ^ 5))
-- ex1 (Bits∈-suc (Bits∈-suc (Bits∈-suc ())))

-- -- -- From https://git8.cs.fau.de/software/duration-monad-agda/-/blob/master/Cantor.agda
-- -- ⟨_,_⟩ : ℕ → ℕ → ℕ
-- -- ⟨_,_⟩ 0 0 = 0
-- -- -- ⟨_,_⟩ 0 (suc m) = ⟨ 0 , m ⟩ + suc m + 1
-- -- ⟨_,_⟩ 0 (suc m) = suc (suc (⟨ 0 , m ⟩ + m))
-- -- ⟨_,_⟩ (suc n) m = suc (⟨ n , m ⟩ + (n + m))

-- iterate : ∀ {A : Set} → ℕ → (ℕ → A → A) → A → A
-- iterate zero f x = x
-- iterate (suc n) f x = f n (iterate n f x)

-- iterate-suc : ∀ {A : Set} {f} {x : A} {n} →
--   iterate (suc n) f x ≡ f n (iterate n f x)
-- iterate-suc = refl

-- -- monotone-base : ∀ {f : ℕ → ℕ} {n} →
-- --   (∀ a b → a ≤ b → f a ≤ f b) →
-- --   n ≤ f n
-- -- monotone-base {f} {zero} f-mono = z≤n
-- -- monotone-base {f} {suc n} f-mono =
-- --   let IH = monotone-base {f} {n} f-mono
-- --       p = ≤-trans IH (f-mono {!!} {!!} (n≤1+n n))
-- --   in
-- --   {!!}

-- iterate-monotone : ∀ {n n′ f x} →
--   (∀ {a b s t} → a ≤ b → s ≤ t → f a s ≤ f b t) →
--   (∀ a → x ≤ f a x) →
--   n ≤ n′ →
--   iterate n f x ≤ iterate n′ f x
-- iterate-monotone {.zero} {zero} {f} {x} f-mono prf z≤n = ≤-refl
-- iterate-monotone {.zero} {suc n′} {f} {x} f-mono prf z≤n = ≤-trans (prf n′) (f-mono ≤-refl (iterate-monotone {zero} {n′} {f} {x} f-mono prf z≤n))
-- iterate-monotone {.(suc _)} {.(suc _)} {f} {x} f-mono prf (s≤s p) = f-mono p (iterate-monotone f-mono prf p)

-- -- Based on https://coq.inria.fr/stdlib/Coq.Arith.Cantor.html
-- pair-go : ℕ → ℕ → ℕ
-- pair-go i m = suc i + m

-- ⟨_,_⟩ : ℕ → ℕ → ℕ
-- ⟨_,_⟩ x y = y + iterate (y + x) pair-go 0

-- _ : ⟨ 3 , 4 ⟩ ≡ 32
-- _ = refl

-- _ : ⟨ 4 , 3 ⟩ ≡ 31
-- _ = refl

-- -- Based on of_nat from https://coq.inria.fr/stdlib/Coq.Arith.Cantor.html
-- →Pair-go : ℕ × ℕ → ℕ × ℕ
-- →Pair-go (suc x , y) = (x , suc y)
-- →Pair-go (zero , y) = (suc y , 0)

-- →Pair : ℕ → ℕ × ℕ
-- →Pair zero = (0 , 0)
-- →Pair (suc n) = →Pair-go (→Pair n)

-- fst snd : ℕ → ℕ
-- fst = proj₁ ∘ →Pair
-- snd = proj₂ ∘ →Pair

-- pair-go-suc₁ : ∀ {x y} →
--   pair-go x y ≤ pair-go (suc x) y
-- pair-go-suc₁ {zero} {zero} = s≤s z≤n
-- pair-go-suc₁ {suc x} {zero} = s≤s (pair-go-suc₁ {x})
-- pair-go-suc₁ {zero} {suc y} = s≤s (pair-go-suc₁ {_} {y})
-- pair-go-suc₁ {suc x} {suc y} = s≤s (pair-go-suc₁ {x} {suc y})

-- pair-go-suc₂ : ∀ {x y} →
--   pair-go x y ≤ pair-go x (suc y)
-- pair-go-suc₂ {zero} {zero} = s≤s z≤n
-- pair-go-suc₂ {zero} {suc y} = s≤s (pair-go-suc₂ {zero} {y})
-- pair-go-suc₂ {suc x} {zero} = s≤s (pair-go-suc₂)
-- pair-go-suc₂ {suc x} {suc y} = s≤s (pair-go-suc₂)

-- pair-go-monotone₁ : ∀ {x x′ y} →
--   x ≤ x′ →
--   pair-go x y ≤ pair-go x′ y
-- pair-go-monotone₁ {.zero} {x′} {zero} z≤n = s≤s z≤n
-- pair-go-monotone₁ {.zero} {x′} {suc y} z≤n = s≤s (+-mono-≤ {0} {x′} {suc y} z≤n ≤-refl)
-- pair-go-monotone₁ {.(suc _)} {.(suc _)} {y} (s≤s p) = s≤s (pair-go-monotone₁ p)

-- pair-go-monotone : ∀ {x x′ y y′} →
--   x ≤ x′ →
--   y ≤ y′ →
--   pair-go x y ≤ pair-go x′ y′
-- pair-go-monotone {.zero} {x′} {.zero} {y′} z≤n z≤n = s≤s z≤n
-- pair-go-monotone {.zero} {x′} {suc m} {suc n} z≤n (s≤s q) = s≤s (+-mono-≤ {0} {x′} {suc m} {suc n} z≤n (s≤s q))
-- pair-go-monotone {.(suc _)} {.(suc _)} {.zero} {y′} (s≤s p) z≤n = s≤s (pair-go-monotone p z≤n)
-- pair-go-monotone {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (s≤s p) (s≤s q) = s≤s (pair-go-monotone p (s≤s q))

-- pair-suc₁ : ∀ {x y} →
--   ⟨ x , y ⟩ ≤ ⟨ suc x , y ⟩
-- pair-suc₁ {zero} {zero} = z≤n
-- pair-suc₁ {suc x} {zero} =
--   let prf = pair-suc₁ {x} {zero}
--       prf′ = s≤s prf

--       p : suc (suc (x + iterate x (λ i → _+_ (suc i)) 0)) ≤ suc (suc (x + suc (x + iterate x (λ z z₁ → suc z + z₁) zero)))
--       p =
--         s≤s (s≤s
--           (+-mono-≤ {x} {x} {iterate x (λ i → _+_ (suc i)) 0} {suc (x + iterate x (λ z z₁ → suc (z + z₁)) zero)}
--             ≤-refl
--             (≤-trans (+-mono-≤ {0} {x} z≤n ≤-refl)
--               (n≤1+n (x + iterate x (λ z z₁ → suc (z + z₁)) zero)))))
--   in
--   (≤-trans (pair-go-monotone₁ (n≤1+n x)) p)
-- pair-suc₁ {x} {suc y} =
--   let prf = pair-suc₁ {x} {y}

--       p : y + x ≤ y + suc x
--       p = +-mono-≤ {y} {y} {x} {suc x} ≤-refl (n≤1+n x)

--       q : iterate (y + x) pair-go 0 ≤ iterate (y + suc x) pair-go 0
--       q = iterate-monotone (λ prf-1 prf-2 → pair-go-monotone prf-1 prf-2) (λ a → z≤n) p
--   in
--   s≤s (+-mono-≤ {y} {y} ≤-refl (pair-go-monotone p q))

-- Pair-monotone-lift₂ : ∀ {x x′ y y′} {f : ℕ → ℕ} →
--   (∀ {a b} → a ≤ b → f a ≤ f b) →
--   x ≤ x′ →
--   y ≤ y′ →
--   ⟨ x , f y ⟩ ≤ ⟨ x′ , f y′ ⟩
-- Pair-monotone-lift₂ {x} {x′} {y} {y′} {f} f-mono prf-1 prf-2 =
--   let
--     p : f y + x ≤ f y′ + x′
--     p = +-mono-≤ {f y} {f y′} {x} {x′} (f-mono prf-2) prf-1
--   in
--   +-mono-≤
--     {f y}
--     {f y′}
--     {iterate (f y + x) pair-go zero}
--     {iterate (f y′ + x′) pair-go zero}
--     (f-mono prf-2)
--     (iterate-monotone (λ prf-1 prf-2 → pair-go-monotone prf-1 prf-2) (λ a → z≤n) p)

-- Pair-monotone : ∀ {x x′ y y′} →
--   x ≤ x′ →
--   y ≤ y′ →
--   ⟨ x , y ⟩ ≤ ⟨ x′ , y′ ⟩
-- Pair-monotone {x} {x′} {y} {y′} x≤x′ y≤y′ =
--   Pair-monotone-lift₂ {x} {x′} {y} {y′} {λ a → a} (λ p → p) x≤x′ y≤y′

-- -- Pair-suc : ∀ {x y} →
-- --   ⟨ suc x , y ⟩ ≤ ⟨ x , suc y ⟩
-- -- Pair-suc {zero} {zero} = s≤s z≤n
-- -- Pair-suc {zero} {suc y} =
-- --   let IH = Pair-suc {zero} {y}
-- --   in
-- --   {!!}
-- --   -- s≤s (≤-trans (n≤1+n (y + suc (y + 1 + iterate (y + 1) pair-go zero)))
-- --   --   (s≤s (+-mono-≤ {y} {y} {suc (y + 1 + iterate (y + 1) pair-go zero)} {suc
-- --   --                                                                          (suc (y + zero + suc (y + zero + iterate (y + zero) pair-go zero)))}
-- --   --           ≤-refl
-- --   --           (s≤s (≤-trans (n≤1+n (y + 1 + iterate (y + 1) pair-go zero)) (s≤s p))))))
-- --   -- where
-- --   --   p : y + 1 + iterate (y + 1) pair-go zero ≤ y + zero + suc (y + zero + iterate (y + zero) pair-go zero)
-- --   --   p rewrite solve 1 (λ y → y :+ con 0 := y) refl y
-- --   --           | solve 2 (λ y z → y :+ con 1 :+ z := y :+ (con 1 :+ z)) refl y (iterate (y + 1) (λ i m → suc (i + m)) 0) =
-- --   --     +-mono-≤
-- --   --       {y}
-- --   --       {y}
-- --   --       {suc (iterate (y + 1) (λ z z₁ → suc (z + z₁)) zero)}
-- --   --       {suc (y + iterate y (λ z z₁ → suc (z + z₁)) zero)}
-- --   --       ≤-refl
-- --   --       (s≤s {!!})
-- -- Pair-suc {suc x} {zero} = {!!}
-- -- Pair-suc {suc x} {suc y} = {!!}

-- _ : ⟨ 0 , 2 ⟩ ≡ 5
-- _ = refl

-- _ : ⟨ 2 , 0 ⟩ ≡ 3
-- _ = refl

-- _ : fst ⟨ 0 , 2 ⟩ ≡ 0
-- _ = refl

-- _ : snd ⟨ 0 , 2 ⟩ ≡ 2
-- _ = refl

-- _ : fst ⟨ 7 , 11 ⟩ ≡ 7
-- _ = refl

-- _ : snd ⟨ 7 , 11 ⟩ ≡ 11
-- _ = refl

-- fst-monotone : ∀ {n n′} →
--   n ≤ n′ →
--   fst n ≤ fst n′
-- fst-monotone {.zero} {zero} z≤n = z≤n
-- fst-monotone {.zero} {suc n′} z≤n = z≤n
-- fst-monotone {suc n} {suc n′} (s≤s prf) =
--   let IH = fst-monotone {n} {n′} prf
--   in
--   {!!}
--   -- +-mono-≤ {{!!}} {?} {?} {?} {!!} {!!}

-- -- pair-suc : ∀ {x} →
-- --   suc ⟨ zero , x ⟩ ≡ ⟨ x , zero ⟩
-- -- pair-suc {zero} = {!!}
-- -- pair-suc {suc x} = {!!}

-- pair-lemma1 : ∀ {x} → ⟨ zero , x ⟩ ≡ x + iterate x (λ i m → suc (i + m)) 0
-- pair-lemma1 {zero} = refl
-- pair-lemma1 {suc x}
--   rewrite pair-lemma1 {x}
--         | solve 1 (λ x → x :+ con 0 := x) refl x = refl

-- _ : ⟨ 1 , 3 ⟩ ≡ 13
-- _ = refl

-- _ : ⟨ 1 , 7 ⟩ ≡ 7 + pair-go 7 (iterate 7 pair-go 0)
-- _ = refl

-- _ : ⟨ 1 , suc 7 ⟩ ≡ suc 7 + pair-go (suc 7) (pair-go 7 (iterate 7 pair-go 0))
-- _ = refl

-- pair-lemma2 : ∀ {y} →
--   ⟨ 1 , y ⟩ ≡ y + pair-go (y + zero) (iterate (y + zero) pair-go 0)
-- pair-lemma2 {zero} = refl
-- pair-lemma2 {suc y}
--   rewrite solve 1 (λ x → x :+ con 1 := con 1 :+ x) refl y
--         | solve 1 (λ x → x :+ con 0 := x) refl y = refl

-- -- suc ⟨ suc x , y ⟩ ≡ ⟨ suc x , suc y ⟩
-- _ :
--   let x = 2
--       y = 9
--   in
--   1 + suc x + suc y + ⟨ suc x , y ⟩ ≡ ⟨ suc x , suc y ⟩
-- _ = refl


-- -- _ :
-- --   let x = 2
-- --       y = 9
-- --   in
-- --   ⟨ suc x , y ⟩ ≡
-- --       y + pair-go (y + suc x) (iterate (y + suc x) pair-go 0)
-- -- _ = refl


-- -- Based on https://github.com/coq/coq/blob/110921a449fcb830ec2a1cd07e3acc32319feae6/theories/Arith/Cantor.v

-- data Pair-Lemma : ℕ → ℕ → ℕ → Set where
--   Pair-Lemma-z : Pair-Lemma zero zero zero

--   Pair-Lemma-s-z : ∀ {n x} →
--     Pair-Lemma n zero x →
--     Pair-Lemma (suc n) (suc x) zero

--   Pair-Lemma-z-s : ∀ {n y} →
--     Pair-Lemma n (suc zero) y →
--     Pair-Lemma (suc n) zero (suc y)

--   Pair-Lemma-s-s : ∀ {n x y} →
--     Pair-Lemma n (suc (suc x)) y →
--     Pair-Lemma (suc n) (suc x) (suc y)

-- pair-lemma : ∀ {n x y} →
--   Pair-Lemma n x y →
--   →Pair n ≡ (x , y)
-- pair-lemma Pair-Lemma-z = refl
-- pair-lemma (Pair-Lemma-s-z prf) rewrite pair-lemma prf = refl
-- pair-lemma (Pair-Lemma-z-s prf) rewrite pair-lemma prf = refl
-- pair-lemma (Pair-Lemma-s-s prf) rewrite pair-lemma prf = refl

-- -- nonzero-Pair-go₁ : ∀ {p} →
-- --   ¬ (proj₁ (→Pair-go p) ≡ 0)
-- -- nonzero-Pair-go₁ {p} x with →Pair-go p in eq
-- -- ... | a , b rewrite x = {!!}
-- -- -- nonzero-Pair-go₁ {zero} = λ ()
-- -- -- nonzero-Pair-go₁ {suc n} x = nonzero-Pair-go₁ {n} {!!}

-- -- pair-canon : ∀ {x y} →
-- --   ⟨ x , y ⟩ ≡ ⟨ fst ⟨ x , y ⟩ , snd ⟨ x , y ⟩ ⟩
-- -- pair-canon {zero} {zero} = refl
-- -- pair-canon {zero} {suc y} with fst ⟨ zero , suc y ⟩ in eq₁ | snd ⟨ zero , suc y ⟩ in eq₂
-- -- ... | p | q = {!!}
-- -- pair-canon {suc x} {zero} = {!!}
-- -- pair-canon {suc x} {suc y} = {!!}

-- data Pair-Nonzero : ℕ → ℕ → Set where
--   Mk-Pair-Nonzero : ∀ {x y} →
--     fst (suc x) ≡ 0 →
--     snd (suc y) ≡ 0 →
--     Pair-Nonzero (suc x) (suc y)

-- fst≤ : ∀ {p} →
--   fst p ≤ fst (suc p)
-- fst≤ {zero} = z≤n
-- fst≤ {suc p} =
--   let IH = fst≤ {p}
--   in
--   {!!} --s≤s ?

-- pair-0′ : ⟨ 0 , 0 ⟩ ≡ 0
-- pair-0′ = refl

-- pair-0′′ : ∀ {p} →
--   ⟨ fst p , snd p ⟩ ≡ 0 →
--   p ≡ 0
-- pair-0′′ {zero} eq = refl
-- pair-0′′ {suc p} eq = {!!}

-- Pair-Nonzero-empty : ∀ {x y} →
--   ¬ Pair-Nonzero x y
-- Pair-Nonzero-empty {zero} {zero} = λ ()
-- Pair-Nonzero-empty {zero} {suc y} = λ ()
-- Pair-Nonzero-empty {suc x} {zero} = λ ()
-- Pair-Nonzero-empty {suc x} {suc y} (Mk-Pair-Nonzero a b) = {!!}

-- pair-0 : ∀ {p} →
--   fst p ≡ 0 →
--   snd p ≡ 0 →
--   p ≡ ⟨ 0 , 0 ⟩
-- pair-0 {zero} x y = refl
-- pair-0 {suc p} x y = {!!}

-- -- pair-0 : ∀ {p} →
-- --   fst p ≡ 0 →
-- --   snd p ≡ 0 →
-- --   p ≡ 0
-- -- pair-0 {zero} eq₁ eq₂ = refl
-- -- pair-0 {suc p} eq₁ eq₂ with fst (suc p) in eq₁ | snd (suc p) in eq₂
-- -- ... | zero | zero with eq₁ | eq₂
-- -- pair-0 {suc p} eq₁ eq₂ | zero | zero | refl | refl =
-- --   let IH = pair-0 {p} {!!} {!!}
-- --   in
-- --   {!!}

-- pair-nonzero : ∀ {n} →
--   ¬ (fst (suc n) ≡ 0 × snd (suc n) ≡ 0)
-- pair-nonzero {suc n} (eq₁ , eq₂)
--   with pair-nonzero {n} {!!}
-- ... | z = z

-- Pair-Lemma-exists₀ : ∀ {n} →
--   ∃[ x ]
--   ∃[ y ]
--   Pair-Lemma n x y
-- Pair-Lemma-exists₀ {zero} = zero , zero , Pair-Lemma-z
-- Pair-Lemma-exists₀ {suc n} with fst (suc n) in eq₁ | snd (suc n) in eq₂
-- ... | zero | zero = {!!}
-- ... | zero | suc b = {!!}
-- ... | suc a | zero = {!!}
-- ... | suc a | suc b = {!!}
-- -- Pair-Lemma-exists₀ {n} with fst n in eq₁ | snd n in eq₂
-- -- ... | zero | suc q = {!!} , {!!} , {!!}
-- -- ... | suc p | zero = {!!}
-- -- ... | suc p | suc q = {!!}
-- -- ... | zero | zero with n
-- -- Pair-Lemma-exists₀ {n} | zero | zero | zero = zero , zero , Pair-Lemma-z
-- -- Pair-Lemma-exists₀ {n} | zero | zero | suc m = zero , zero , {!!}

-- -- Pair-Lemma-exists : ∀ {x y} →
-- --   ∃[ n ] Pair-Lemma n x y
-- -- Pair-Lemma-exists {zero} {zero} = zero , Pair-Lemma-z
-- -- Pair-Lemma-exists {zero} {suc y} =
-- --   let n , prf = Pair-Lemma-exists {suc zero} {y}
-- --   in
-- --   suc n , Pair-Lemma-z-s prf
-- -- Pair-Lemma-exists {suc x} {zero} =
-- --   let n , prf = Pair-Lemma-exists {zero} {x}
-- --   in
-- --   suc n , Pair-Lemma-s-z {!!}
-- -- Pair-Lemma-exists {suc x} {suc y} = {!!}

-- -- pair-lemma Pair-Lemma-z = refl
-- -- pair-lemma (Pair-Lemma-s-z x) = {!!}
-- --   -- let IHn = pair-lemma
-- -- pair-lemma (Pair-Lemma-z-s x) = {!!}
-- -- pair-lemma (Pair-Lemma-s-s x) = {!!}

-- -- pair-lemma : ∀ {n x y} →
-- --   ⟨ x , y ⟩ ≡ n →
-- --   →Pair n ≡ (x , y)
-- -- pair-lemma {zero} {zero} {zero} = λ _ → refl
-- -- pair-lemma {zero} {zero} {suc y} = λ ()
-- -- pair-lemma {zero} {suc x} {zero} = λ ()
-- -- pair-lemma {zero} {suc x} {suc y} = λ ()
-- -- pair-lemma {suc n} {zero} {zero} = λ ()
-- -- pair-lemma {suc n} {suc x} {zero} refl =
-- --     let IHn = pair-lemma {n} {zero} {x} (pair-lemma1 {x})
-- --     in
-- --     begin
-- --       →Pair-go (→Pair (x + iterate x (λ z z₁ → suc (z + z₁)) zero)) ≡⟨ cong →Pair-go IHn ⟩
-- --       →Pair-go (zero , x) ≡⟨⟩
-- --       suc x , zero
-- --     ∎
-- -- pair-lemma {suc n} {zero} {suc y} refl =
-- --   let IHn = pair-lemma {n} {suc zero} {y} pair-lemma2
-- --   in
-- --   begin
-- --     →Pair-go (→Pair (y + suc (y + zero + iterate (y + zero) pair-go zero))) ≡⟨ cong →Pair-go IHn ⟩
-- --     zero , suc y
-- --   ∎
-- -- pair-lemma {suc n} {suc x} {suc y} refl =
-- --   let IHn = pair-lemma {n} {suc (suc x)} {suc y} {!!}
-- --   in
-- --   begin
-- --     →Pair-go (→Pair n) ≡⟨ cong →Pair-go IHn ⟩
-- --     {!!} ≡⟨ {!!} ⟩
-- --     {!!}
-- --   ∎

-- -- pair-thm : ∀ {x y} →
-- --   →Pair ⟨ x , y ⟩ ≡ (x , y)
-- -- pair-thm = pair-lemma refl

-- -- fst-thm : ∀ {x y} →
-- --   fst ⟨ x , y ⟩ ≡ x
-- -- fst-thm {zero} {zero} = refl
-- -- fst-thm {zero} {suc y} rewrite fst-thm {zero} {y} = {!!}
-- -- fst-thm {suc x} {y} = {!!}

-- -- -- pair-lemma : ∀ {b} → suc (suc ⟨ 0 , b ⟩ + b) ≡ ⟨ 0 , suc b ⟩
-- -- -- pair-lemma {zero} = refl
-- -- -- pair-lemma {suc b} = refl

-- -- -- -- inverses
-- -- -- π₂⁻¹ π₁⁻¹ : ℕ → ℕ

-- -- -- π₂⁻¹ 0 = 0
-- -- -- π₂⁻¹ (suc n) with (π₁⁻¹ n)
-- -- -- π₂⁻¹ (suc n) | zero  = 0
-- -- -- π₂⁻¹ (suc n) | suc _ = suc (π₂⁻¹ n)

-- -- -- π₁⁻¹ 0 = 0
-- -- -- π₁⁻¹ (suc n) with (π₁⁻¹ n)
-- -- -- π₁⁻¹ (suc n) | zero = suc (π₂⁻¹ n)
-- -- -- π₁⁻¹ (suc n) | suc m = m

-- -- -- pair-suc : ∀ (n m : ℕ) → ⟨ n , (suc m) ⟩ ≡ suc ⟨ (suc n) , m ⟩
-- -- -- pair-suc = {!!}


-- -- -- h₁ : ∀ (n k : ℕ) → (k ≤ n) → π₁⁻¹ ⟨ n + k , 0 ⟩ ≡ n ∸ k
-- -- -- h₁ = {!!}

-- -- -- data Proj₁-helper : ℕ → Set where
-- -- --   Proj₁-helper-0 : ∀ {b} →
-- -- --     Proj₁-helper ⟨ 0 , b ⟩

-- -- --   Proj₁-helper-s : ∀ {n} →
-- -- --     Proj₁-helper n →
-- -- --     Proj₁-helper (suc n)


-- -- -- proj₁-lemma : ∀ {b} → Proj₁-helper b → π₁⁻¹ b ≡ 0

-- -- -- π₁-lemma′ : ∀ {b} → π₁⁻¹ ⟨ 0 , b ⟩ ≡ 0
-- -- -- π₁-lemma′ {zero} = refl
-- -- -- π₁-lemma′ {suc b} = {!!} --proj₁-lemma {!!}

-- -- -- proj₁-lemma {.(⟨ 0 , _ ⟩)} Proj₁-helper-0 = {!!}
-- -- -- proj₁-lemma {.(suc _)} (Proj₁-helper-s prf) = {!!}

-- -- -- -- π₁-lemma′ : ∀ {b} → π₁⁻¹ (suc (suc ⟨ 0 , b ⟩ + b)) ≡ 0
-- -- -- -- π₁-lemma′ {zero} = refl
-- -- -- -- π₁-lemma′ {suc b} = {!!}

-- -- -- -- π₁-lemma′ {zero} = refl
-- -- -- -- π₁-lemma′ {suc b} rewrite (pair-lemma {b}) | π₁-lemma′ {b} =
-- -- -- --   let p = π₁-lemma′ {b}
-- -- -- --   in
-- -- -- --   {!!}

-- -- -- -- π₁-lemma : ∀ {b} → π₁⁻¹ ⟨ 0 , b ⟩ ≡ 0
-- -- -- -- π₁-lemma {zero} = refl
-- -- -- -- π₁-lemma {suc b} = π₁-lemma′ {b}


-- -- -- -- pair-inv₁ : ∀ {a b} → π₁⁻¹ ⟨ a , b ⟩ ≡ a
-- -- -- -- pair-inv₁ {zero} {zero} = refl
-- -- -- -- pair-inv₁ {zero} {suc b} = π₁-lemma {suc b} --π₁-lemma {suc b}
-- -- -- -- pair-inv₁ {suc a} {b} = {!!}

