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

  E-Seq′ : ∀ {a a′ b ω ω′} →
    ⟨ a , ω ⟩⟶′⟨ a′ , ω′ ⟩ →
    -------------
    ⟨ Seq a b , ω ⟩⟶′⟨ b , ω′ ⟩

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

data _~_ : Expr → Expr → Set where
  Sim-Lit : ∀ {i} →
    -------------

    Lit i ~ Lit i

  Sim-Add : ∀ {a b a† b†} →
    a ~ a† →
    b ~ b† →
    Add a b ~ Add a† b†

  Sim-Print : ∀ {a a†} →
    a ~ a† →
    Print a ~ Print a†

  Sim-Seq : ∀ {a b a† b†} →
    a ~ a† →
    b ~ b† →
    Seq a b ~ b†

data _[_]O~_ : Output → Expr → Output → Set where
  O-Sim-Lit : ∀ {i ω} →
    ω [ Lit i ]O~ ω

  O-Sim-Add : ∀ {a b ω} →
    ω [ Add a b ]O~ ω

  O-Sim-Print : ∀ {a ω} →
    ω [ Print a ]O~ ω

  O-Sim-Seq-1 : ∀ {a a′ b ω ω†} →
    ⟨ a , ω ⟩⟶⟨ a′ , ω† ⟩ →
    ω [ Seq a b ]O~ ω†

  O-Sim-Seq : ∀ {i b ω} →
    ω [ Seq (Lit i) b ]O~ ω

O-Sim-exists : ∀ a ω →
  ∃[ ω† ]
  ω [ a ]O~ ω†
O-Sim-exists (Lit x) ω = ω , O-Sim-Lit
O-Sim-exists (Add a a₁) ω = ω , O-Sim-Add
O-Sim-exists (Print a) ω = ω , O-Sim-Print
O-Sim-exists (Seq a a₁) ω with value-or-can-step {a} {ω}
... | inj₁ Is-Value-Lit = ω , O-Sim-Seq
... | inj₂ (fst , fst₁ , snd) = fst₁ , O-Sim-Seq-1 snd

⟶deterministic : ∀ {a b₁ b₂ ω ω₁ ω₂} →
  ⟨ a , ω ⟩⟶⟨ b₁ , ω₁ ⟩ →
  ⟨ a , ω ⟩⟶⟨ b₂ , ω₂ ⟩ →
  b₁ ≡ b₂
⟶deterministic (E-Add-1 p) (E-Add-1 q) rewrite ⟶deterministic p q = refl
⟶deterministic (E-Add-2 p) (E-Add-2 q) rewrite ⟶deterministic p q = refl
⟶deterministic (E-Add refl) (E-Add refl) = refl
⟶deterministic (E-Print-1 p) (E-Print-1 q) rewrite ⟶deterministic p q = refl
⟶deterministic E-Print E-Print = refl
⟶deterministic (E-Seq-1 p) (E-Seq-1 q) rewrite ⟶deterministic p q = refl
⟶deterministic (E-Seq-2 p) (E-Seq-2 q) rewrite ⟶deterministic p q = refl
⟶deterministic E-Seq E-Seq = refl

⟶deterministic-state : ∀ {a b₁ b₂ ω ω₁ ω₂} →
  ⟨ a , ω ⟩⟶⟨ b₁ , ω₁ ⟩ →
  ⟨ a , ω ⟩⟶⟨ b₂ , ω₂ ⟩ →
  ω₁ ≡ ω₂
⟶deterministic-state (E-Add-1 p) (E-Add-1 q) rewrite ⟶deterministic-state p q = refl
⟶deterministic-state (E-Add-2 p) (E-Add-2 q) rewrite ⟶deterministic-state p q = refl
⟶deterministic-state (E-Add refl) (E-Add refl) = refl
⟶deterministic-state (E-Print-1 p) (E-Print-1 q) rewrite ⟶deterministic-state p q = refl
⟶deterministic-state E-Print E-Print = refl
⟶deterministic-state (E-Seq-1 p) (E-Seq-1 q) rewrite ⟶deterministic-state p q = refl
⟶deterministic-state (E-Seq-2 p) (E-Seq-2 q) rewrite ⟶deterministic-state p q = refl
⟶deterministic-state E-Seq E-Seq = refl

O-Sim-unique : ∀ {a ω ω†₁ ω†₂} →
  ω [ a ]O~ ω†₁ →
  ω [ a ]O~ ω†₂ →
  ω†₁ ≡ ω†₂
O-Sim-unique O-Sim-Lit O-Sim-Lit = refl
O-Sim-unique O-Sim-Add O-Sim-Add = refl
O-Sim-unique O-Sim-Print O-Sim-Print = refl
O-Sim-unique O-Sim-Seq O-Sim-Seq = refl
O-Sim-unique (O-Sim-Seq-1 x) (O-Sim-Seq-1 x₂) rewrite ⟶deterministic-state x x₂ = refl

sim : ∀ {a a† b ω ω′} →
  a ~ a† →
  ⟨ a , ω ⟩⟶⟨ b , ω′ ⟩ →
  ∃[ b† ]
  ∃[ ω† ]
  ∃[ ω′† ]
  (b ~ b†)
    ×
  (ω [ a ]O~ ω†)
    ×
  ⟨ a† , ω† ⟩⟶′*⟨ b† , ω′† ⟩
sim Sim-Lit ()
sim (Sim-Add {b† = b†} p p₁) (E-Add-1 q) with sim p q
... | fst , fst₁ , fst₂ , fst₃ , fst₀ , snd = Add fst b† , fst₁ , fst₂ , Sim-Add fst₃ p₁ , {!O-Sim-Add!} , lift′* E-Add-1′ snd
sim (Sim-Add p p₁) (E-Add-2 q) = {!!}
sim (Sim-Add p p₁) (E-Add x) = {!!}
sim (Sim-Print p) (E-Print-1 q) = {!!}
sim (Sim-Print p) E-Print = {!!}
sim (Sim-Seq p p₁) (E-Seq-1 q) = {!!}
sim (Sim-Seq p p₁) (E-Seq-2 q) = {!!}
sim (Sim-Seq p p₁) E-Seq = {!!}
-- sim {ω = ω} (Sim-Lit {i = i}) O-Sim-Lit ()
-- sim {ω = ω} {ω′ = ω′} (Sim-Add {a = a} p p₁) prf@O-Sim-Add (E-Add-1 r) with sim p (proj₂ (O-Sim-exists a ω′)) r
-- ... | fst , fst₁ , fst₂ , snd = {!!} , {!!} , {!!} , lift′* E-Add-1′ {!!}
-- sim (Sim-Add p p₁) O-Sim-Add (E-Add-2 r) = {!!}
-- sim (Sim-Add p p₁) O-Sim-Add (E-Add x) = {!!}
-- sim (Sim-Print p) O-Sim-Print r = {!!}
-- sim (Sim-Seq p p₁) (O-Sim-Seq-1 x) r = {!!}
-- sim (Sim-Seq p p₁) O-Sim-Seq r = {!!}
