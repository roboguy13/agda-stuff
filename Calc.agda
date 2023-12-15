module Calc where

open import Data.Integer
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit

data Expr : Set where
  Lit : ℤ → Expr
  Add : Expr → Expr → Expr

  Print : Expr → Expr
  Seq : Expr → Expr → Expr

data Output : Set where
  ∅ : Output                -- Empty output
  _∷_ : ℤ → Output → Output -- Put another item in an existing output

-- First one-step relation
data ⟨_,_⟩⟶⟨_,_⟩ : Expr → Output → Expr → Output → Set where
  E-Add-1 : ∀ {a a′ b ω ω′} →
    ⟨ a , ω ⟩⟶⟨ a′ , ω′ ⟩ →
    -------------
    ⟨ Add a b , ω ⟩⟶⟨ Add a′ b , ω′ ⟩

  E-Add-2 : ∀ {i b b′ ω ω′} →
    ⟨ b , ω ⟩⟶⟨ b′ , ω′ ⟩ →
    -------------
    ⟨ Add (Lit i) b , ω ⟩⟶⟨ Add (Lit i) b′ , ω′ ⟩

  E-Add : ∀ {i j k ω} →
    k ≡ i + j →
    -------------
    ⟨ Add (Lit i) (Lit j) , ω ⟩⟶⟨ Lit k , ω ⟩

  E-Print-1 : ∀ {a a′ ω ω′} →
    ⟨ a , ω ⟩⟶⟨ a′ , ω′ ⟩ →
    -------------
    ⟨ Print a , ω ⟩⟶⟨ Print a′ , ω′ ⟩

  E-Print : ∀ {i ω} →
    -------------
    ⟨ Print (Lit i) , ω ⟩⟶⟨ Lit i , (i ∷ ω) ⟩

  E-Seq-1 : ∀ {a a′ b ω ω′} →
    ⟨ a , ω ⟩⟶⟨ a′ , ω′ ⟩ →
    -------------
    ⟨ Seq a b , ω ⟩⟶⟨ Seq a′ b , ω′ ⟩

  E-Seq-2 : ∀ {i b b′ ω ω′} →
    ⟨ b , ω ⟩⟶⟨ b′ , ω′ ⟩ →
    -------------
    ⟨ Seq (Lit i) b , ω ⟩⟶⟨ Seq (Lit i) b′ , ω′ ⟩

  E-Seq : ∀ {i j ω} →
    -------------
    ⟨ Seq (Lit i) (Lit j) , ω ⟩⟶⟨ Lit j , ω ⟩

data ⟨_,_⟩⟶*⟨_,_⟩ : Expr → Output → Expr → Output → Set where
  E-Done : ∀ {a ω} →
    -------------
    ⟨ a , ω ⟩⟶*⟨ a , ω ⟩

  E-Step : ∀ {a a′ a′′ ω ω′ ω′′} →
    ⟨ a , ω ⟩⟶⟨ a′ , ω′ ⟩ →
    ⟨ a′ , ω′ ⟩⟶*⟨ a′′ , ω′′ ⟩ →
    -------------
    ⟨ a , ω ⟩⟶*⟨ a′′ , ω′′ ⟩
--

-- The new one-step relation
data ⟨_,_⟩⟶′⟨_,_⟩ : Expr → Output → Expr → Output → Set where
  E-Add-1′ : ∀ {a a′ b ω ω′} →
    ⟨ a , ω ⟩⟶′⟨ a′ , ω′ ⟩ →
    -------------
    ⟨ Add a b , ω ⟩⟶′⟨ Add a′ b , ω′ ⟩

  E-Add-2′ : ∀ {i b b′ ω ω′} →
    ⟨ b , ω ⟩⟶′⟨ b′ , ω′ ⟩ →
    -------------
    ⟨ Add (Lit i) b , ω ⟩⟶′⟨ Add (Lit i) b′ , ω′ ⟩

  E-Add′ : ∀ {i j k ω} →
    k ≡ i + j →
    -------------
    ⟨ Add (Lit i) (Lit j) , ω ⟩⟶′⟨ Lit k , ω ⟩

  E-Print-1′ : ∀ {a a′ ω ω′} →
    ⟨ a , ω ⟩⟶′⟨ a′ , ω′ ⟩ →
    -------------
    ⟨ Print a , ω ⟩⟶′⟨ Print a′ , ω′ ⟩

  E-Print′ : ∀ {i ω} →
    -------------
    ⟨ Print (Lit i) , ω ⟩⟶′⟨ Lit i , (i ∷ ω) ⟩

  E-Seq-1′ : ∀ {a a′ b ω ω′} →
    ⟨ a , ω ⟩⟶′⟨ a′ , ω′ ⟩ →
    -------------
    ⟨ Seq a b , ω ⟩⟶′⟨ b , ω′ ⟩

  E-Seq′ : ∀ {i b ω} →
    ⟨ Seq (Lit i) b , ω ⟩⟶′⟨ b , ω ⟩

data ⟨_,_⟩⟶′*⟨_,_⟩ : Expr → Output → Expr → Output → Set where
  E-Done′ : ∀ {a ω} →
    -------------
    ⟨ a , ω ⟩⟶′*⟨ a , ω ⟩

  E-Step′ : ∀ {a a′ a′′ ω ω′ ω′′} →
    ⟨ a , ω ⟩⟶′⟨ a′ , ω′ ⟩ →
    ⟨ a′ , ω′ ⟩⟶′*⟨ a′′ , ω′′ ⟩ →
    -------------
    ⟨ a , ω ⟩⟶′*⟨ a′′ , ω′′ ⟩
--

one-step′ : ∀ {a a′ ω ω′} →
  ⟨ a , ω ⟩⟶′⟨ a′ , ω′ ⟩ →
  ⟨ a , ω ⟩⟶′*⟨ a′ , ω′ ⟩
one-step′ p = E-Step′ p E-Done′

one-step : ∀ {a a′ ω ω′} →
  ⟨ a , ω ⟩⟶⟨ a′ , ω′ ⟩ →
  ⟨ a , ω ⟩⟶*⟨ a′ , ω′ ⟩
one-step p = E-Step p E-Done

lift′* : ∀ {a a′ ω ω′} {f : Expr → Expr} →
  (∀ {a c ω ω′′} → ⟨ a , ω ⟩⟶′⟨ c , ω′′ ⟩ →
   ⟨ f a , ω ⟩⟶′⟨ f c , ω′′ ⟩
  ) →
  ⟨ a , ω ⟩⟶′*⟨ a′ , ω′ ⟩ →
  ⟨ f a , ω ⟩⟶′*⟨ f a′ , ω′ ⟩
lift′* _ E-Done′ = E-Done′
lift′* op (E-Step′ x p) =
  let z = op {_} x
  in
  E-Step′ z (lift′* op p)

data Is-Value : Expr → Set where
  Is-Value-Lit : ∀ {i} →
    -------------
    Is-Value (Lit i)

value-not-step : ∀ {a b ω ω′} →
  Is-Value a →
  ¬ (⟨ a , ω ⟩⟶⟨ b , ω′ ⟩)
value-not-step Is-Value-Lit ()

value-or-can-step : ∀ {a ω} →
  (Is-Value a) ⊎ (∃[ a′ ] ∃[ ω′ ] ⟨ a , ω ⟩⟶⟨ a′ , ω′ ⟩)
value-or-can-step {Lit x} = inj₁ Is-Value-Lit
value-or-can-step {Add a b} {ω} with value-or-can-step {a} {ω}
value-or-can-step {Add .(Lit _) b} {ω} | inj₁ Is-Value-Lit with value-or-can-step {b} {ω}
value-or-can-step {Add .(Lit _) .(Lit _)} {ω} | inj₁ Is-Value-Lit | inj₁ Is-Value-Lit = inj₂ (Lit _ , ω , E-Add refl)
value-or-can-step {Add .(Lit _) b} {ω} | inj₁ Is-Value-Lit | inj₂ (fst , fst₁ , snd) = inj₂ (Add _ fst , fst₁ , E-Add-2 snd)
value-or-can-step {Add a b} {ω} | inj₂ (fst , fst₁ , snd) = inj₂ (Add fst b , fst₁ , E-Add-1 snd)
value-or-can-step {Print a} {ω} with value-or-can-step {a} {ω}
... | inj₁ Is-Value-Lit = inj₂ (Lit _ , _ , E-Print)
... | inj₂ (fst , fst₁ , snd) = inj₂ (Print fst , fst₁ , E-Print-1 snd)
value-or-can-step {Seq a b} {ω} with value-or-can-step {a} {ω}
value-or-can-step {Seq .(Lit _) b} {ω} | inj₁ Is-Value-Lit with value-or-can-step {b} {ω}
value-or-can-step {Seq .(Lit _) .(Lit _)} {ω} | inj₁ Is-Value-Lit | inj₁ Is-Value-Lit = inj₂ (Lit _ , ω , E-Seq)
value-or-can-step {Seq .(Lit _) b} {ω} | inj₁ Is-Value-Lit | inj₂ (fst , fst₁ , snd) = inj₂ (Seq (Lit _) fst , fst₁ , E-Seq-2 snd)
value-or-can-step {Seq a b} {ω} | inj₂ (fst , fst₁ , snd) = inj₂ (Seq fst b , fst₁ , E-Seq-1 snd)

open import Data.Nat

---- {
-- Numeric literals as integers
record Number {a} (A : Set a) : Set a where
  field fromNat : ℕ → A

open Number {{...}} public

{-# BUILTIN FROMNAT fromNat #-}

instance
  NumInt : Number ℤ
  NumInt .Number.fromNat zero    = +0
  NumInt .Number.fromNat (suc n) = Data.Integer.suc (fromNat n)
---- }

counterexample : ∃[ a ] ∃[ v ] ∃[ ω′ ]
  Is-Value v ×
  ⟨ a , ∅ ⟩⟶*⟨ v , ω′ ⟩ ×
  ¬ (⟨ a , ∅ ⟩⟶′*⟨ v , ω′ ⟩)
counterexample =
  a , Lit 3 ,
  ω′ , Is-Value-Lit ,
  E-Step (E-Seq-1 (E-Add-1 E-Print))
    (E-Step (E-Seq-1 (E-Add-2 E-Print))
      (E-Step (E-Seq-1 (E-Add refl))
        (E-Step (E-Seq-2 E-Print) (E-Step E-Seq E-Done)))) ,
  no-derivation
  where
    a = Seq (Add (Print (Lit 1)) (Print (Lit 2))) (Print (Lit 3))
    ω′ = 3 ∷ (2 ∷ (1 ∷ ∅))

    no-derivation :
      ¬ (⟨ a , ∅ ⟩⟶′*⟨ Lit 3 , ω′ ⟩)
    no-derivation (E-Step′ (E-Seq-1′ (E-Add-1′ E-Print′)) (E-Step′ E-Print′ (E-Step′ () p)))
