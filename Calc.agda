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

E-Add-1′* : ∀ {a a′ b ω ω′} →
  ⟨ a , ω ⟩⟶′*⟨ a′ , ω′ ⟩ →
  ⟨ Add a b , ω ⟩⟶′*⟨ Add a′ b , ω′ ⟩
E-Add-1′* = lift′* E-Add-1′
-- E-Add-1′* E-Done′ = E-Done′
-- E-Add-1′* (E-Step′ x p) = E-Step′ (E-Add-1′ x) (E-Add-1′* p)

data Is-Value : Expr → Set where
  Is-Value-Lit : ∀ {i} →
    -------------
    Is-Value (Lit i)

value-not-step : ∀ {i a ω ω′} →
  ¬ (⟨ Lit i , ω ⟩⟶⟨ a , ω′ ⟩)
value-not-step ()

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

-- _[_]O~_ : Output → Expr → Output → Set
-- ω [ a ]O~ ω′ = ∃[ a′ ] ⟨ a , ω ⟩⟶*⟨ a′ , ω′ ⟩

-- -- Relating outputs
-- data _[_]O~_ : Output → Expr → Output → Set where
--   O-Sim-Lit : ∀ {i ω} →
--     -------------
--     ω [ Lit i ]O~ ω

--   O-Sim-Add : ∀ {a b ω ω′ ω′†} →
--     ω [ a ]O~ ω′ →
--     ω′ [ b ]O~ ω′† →
--     -------------
--     ω [ Add a b ]O~ ω′†

--   O-Sim-Print : ∀ {a c ω ω′ ω†} →
--     ¬ Is-Value a →
--     ω [ a ]O~ ω† →
--     ⟨ Print a , ω ⟩⟶⟨ c , ω′ ⟩ →
--     -------------
--     ω [ Print a ]O~ ω′

--   O-Sim-Seq : ∀ {a b ω ω′ ω′†} →
--     ω [ a ]O~ ω′ →
--     ω′ [ b ]O~ ω′† →
--     -------------
--     ω [ Seq a b ]O~ ω′†

data Value-Choice : Expr → Output → Output → Output → Set where
  Value-Choice-yes : ∀ {a ω₁ ω₂} →
    Is-Value a →
    Value-Choice a ω₁ ω₁ ω₂

  Value-Choice-no : ∀ {a ω₁ ω₂} →
    ¬ Is-Value a →
    Value-Choice a ω₂ ω₁ ω₂

dec-value : ∀ a →
  Is-Value a ⊎ ¬ Is-Value a
dec-value (Lit x) = inj₁ Is-Value-Lit
dec-value (Add a a₁) = inj₂ (λ ())
dec-value (Print a) = inj₂ (λ ())
dec-value (Seq a a₁) = inj₂ (λ ())

mk-Value-Choice : ∀ {a ω₁ ω₂} →
  ∃[ ω ] Value-Choice a ω ω₁ ω₂
mk-Value-Choice {a} {ω₁} {ω₂} with dec-value a
... | inj₁ x = ω₁ , Value-Choice-yes x
... | inj₂ y = ω₂ , Value-Choice-no y

data _[_]O~_ : Output → Expr → Output → Set where
  O-Sim-Lit : ∀ {i ω} →
    ω [ Lit i ]O~ ω

  O-Sim-Add : ∀ {a b ω} →
    ω [ Add a b ]O~ ω

  O-Sim-Print : ∀ {a ω} →
    ω [ Print a ]O~ ω

  O-Sim-Seq-1 : ∀ {a b ω ω′} →
    ¬ Is-Value a →
    ⟨ a , ω ⟩⟶⟨ b , ω′ ⟩ →
    ω [ a ]O~ ω′

  O-Sim-Seq : ∀ {i b ω} →
    ω [ Seq (Lit i) b ]O~ ω

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

dec-O-rel : ∀ a ω →
  (ω [ a ]O~ ω)
    ⊎
  (∃[ a′ ] ∃[ b′ ] (¬ Is-Value a) × a ≡ Seq a′ b′)
dec-O-rel (Lit x) ω = inj₁ O-Sim-Lit
dec-O-rel (Add a a₁) ω = inj₁ O-Sim-Add
dec-O-rel (Print a) ω = inj₁ O-Sim-Print
dec-O-rel (Seq (Lit x) a₁) ω = inj₁ O-Sim-Seq
dec-O-rel (Seq (Add a a₂) a₁) ω = inj₂ (Add a a₂ , a₁ , (λ ()) , refl)
dec-O-rel (Seq (Print a) a₁) ω = inj₂ (Print a , a₁ , (λ ()) , refl)
dec-O-rel (Seq (Seq a a₂) a₁) ω = inj₂ (Seq a a₂ , a₁ , (λ ()) , refl)

O-rel-unique-1 : ∀ {a ω₁ ω₂ ω₁′ ω₂′} →
  ω₁ [ a ]O~ ω₂ →
  ω₁′ [ a ]O~ ω₂′ →
  ω₁′ ≡ ω₁
O-rel-unique-1 O-Sim-Lit O-Sim-Lit = {!!}
O-rel-unique-1 O-Sim-Add O-Sim-Add = {!!}
O-rel-unique-1 O-Sim-Add (O-Sim-Seq-1 x x₁) = {!!}
O-rel-unique-1 O-Sim-Print O-Sim-Print = {!!}
O-rel-unique-1 O-Sim-Print (O-Sim-Seq-1 x x₁) = {!!}
O-rel-unique-1 (O-Sim-Seq-1 x x₁) O-Sim-Add = {!!}
O-rel-unique-1 (O-Sim-Seq-1 x x₁) O-Sim-Print = {!!}
O-rel-unique-1 (O-Sim-Seq-1 x x₁) (O-Sim-Seq-1 x₂ x₃) = {!!}
O-rel-unique-1 (O-Sim-Seq-1 x x₁) O-Sim-Seq = {!!}
O-rel-unique-1 O-Sim-Seq (O-Sim-Seq-1 x x₁) = {!!}
O-rel-unique-1 O-Sim-Seq O-Sim-Seq = {!!}

-- data _~~_

-- rel-lemma : ∀ {a b a† b† ω ω′ ω† ω′†} →
--   a ~ a† →
--   b ~ b† →
--   ⟨ a , ω ⟩⟶⟨ b , ω′ ⟩ →
--   ⟨ a† , ω† ⟩⟶′⟨ b† , ω′† ⟩ →
--   ω [ a ]O~ ω† →
--   ω′ [ b ]O~ ω′†
-- rel-lemma (Sim-Add p p₁) Sim-Lit (E-Add x) (E-Add′ refl) z = {!!}
-- rel-lemma {ω = ω} (Sim-Add {a = a} p p₁) (Sim-Add q q₁) (E-Add-1 r) (E-Add-1′ s) O-Sim-Add with dec-O-rel a ω
-- ... | inj₂ y = {!!}
-- ... | inj₁ x =
--   let w = rel-lemma p q r s x
--   in
--   {!O-Sim-Add!}
-- rel-lemma (Sim-Add p p₁) (Sim-Add q q₁) (E-Add-1 r) (E-Add-1′ s) (O-Sim-Seq-1 x x₁) = {!!}
-- rel-lemma (Sim-Add p p₁) (Sim-Add q q₁) (E-Add-1 r) (E-Add-2′ s) z = {!!}
-- rel-lemma (Sim-Add p p₁) (Sim-Add q q₁) (E-Add-2 r) (E-Add-1′ s) z = {!!}
-- rel-lemma (Sim-Add p p₁) (Sim-Add q q₁) (E-Add-2 r) (E-Add-2′ s) z = {!!}
-- rel-lemma (Sim-Print p) Sim-Lit E-Print E-Print′ = {!!}
-- rel-lemma (Sim-Print p) (Sim-Print q) (E-Print-1 r) (E-Print-1′ s) = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-1 r) (E-Add-1′ s) = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-1 r) (E-Add-2′ s) = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-1 r) (E-Add′ x) = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-1 r) (E-Print-1′ s) = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-1 r) E-Print′ = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-1 r) (E-Seq′ s) = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-2 r) (E-Add-1′ s) = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-2 r) (E-Add-2′ s) = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-2 r) (E-Add′ x) = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-2 r) (E-Print-1′ s) = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-2 r) E-Print′ = {!!}
-- rel-lemma (Sim-Seq p p₁) (Sim-Seq q q₁) (E-Seq-2 r) (E-Seq′ s) = {!!}

-- transform-output : Expr → Output → Output → Set
-- transform-output (Seq a b) ω ω† = ∃[ c ] ((Is-Value a × ω ≡ ω†) ⊎ ⟨ a , ω ⟩⟶⟨ c , ω† ⟩)
-- transform-output a ω ω† = ω ≡ ω†

-- transform-output-fn : ∀ {a ω} → ∃[ ω† ] transform-output a ω ω†
-- transform-output-fn {Lit x} {ω} = ω , refl
-- transform-output-fn {Add a a₁} {ω} = ω , refl
-- transform-output-fn {Print a} {ω} = ω , refl
-- transform-output-fn {Seq a a₁} {ω} with value-or-can-step {a} {ω}
-- ... | inj₁ x = ω , a₁ , inj₁ (x , refl)
-- ... | inj₂ (fst , ω† , snd) = ω† , fst , inj₂ snd

transform-output : Expr → Output → Output
transform-output (Seq a b) ω with value-or-can-step {a} {ω}
... | inj₁ Is-Value-Lit = ω
... | inj₂ (fst , ω† , snd) = ω†
transform-output a ω = ω


sim : ∀ {a b a† ω ω′ ω† ω′†} →
  a ~ a† →
  -- b† ~ b →
  ⟨ a , ω ⟩⟶⟨ b , ω′ ⟩ →
  ω† [ a ]O~ ω →
  ∃[ b† ]
  ∃[ ω′† ]
  (b ~ b†)
    ×
  ω′† [ b ]O~ ω′ ×
  (⟨ a† , ω† ⟩⟶′*⟨ b† , ω′† ⟩)
sim Sim-Lit () r
sim (Sim-Add p p₁) (E-Add-1 q) O-Sim-Add = let z = sim p q {!!} in {!!}
sim (Sim-Add p p₁) (E-Add-1 q) (O-Sim-Seq-1 x x₁) = {!!}
-- with sim p q {!!}
-- sim (Sim-Add p p₁) (E-Add-1 q) r | u = {!!}
sim (Sim-Add p p₁) (E-Add-2 q) r = {!!}
sim (Sim-Add p p₁) (E-Add x) r = {!!}
sim (Sim-Print p) (E-Print-1 q) r = {!!}
sim (Sim-Print p) E-Print r = {!!}
sim (Sim-Seq p p₁) (E-Seq-1 q) r = {!!}
sim (Sim-Seq p p₁) (E-Seq-2 q) r = {!!}
sim (Sim-Seq p p₁) E-Seq r = {!!}

-- transform-lemma : ∀ {a b a† ω ω′ ω† ω′†} →
--   a ~ a† →
--   -- b† ~ b →
--   ⟨ a , ω ⟩⟶⟨ b , ω′ ⟩ →
--   ω† ≡ transform-output a ω →
--   ∃[ b† ]
--   ∃[ ω′† ]
--   (b ~ b†)
--     ×
--   ω′† ≡ transform-output b ω′ ×
--   (⟨ a† , ω† ⟩⟶′*⟨ b† , ω′† ⟩)
-- transform-lemma Sim-Lit () r
-- transform-lemma (Sim-Add p p₁) (E-Add-1 q) refl with transform-lemma p q {!!}
-- ... | fst , fst₁ , fst₂ , fst₃ , snd = {!!} , {!!} , Sim-Add fst₂ p₁ , {!!} , lift′* E-Add-1′ snd
-- transform-lemma (Sim-Add p p₁) (E-Add-2 q) r = {!!}
-- transform-lemma (Sim-Add p p₁) (E-Add x) r = {!!}
-- transform-lemma (Sim-Print p) (E-Print-1 q) r = {!!}
-- transform-lemma (Sim-Print p) E-Print r = {!!}
-- transform-lemma (Sim-Seq p p₁) (E-Seq-1 q) r = {!!}
-- transform-lemma (Sim-Seq p p₁) (E-Seq-2 q) r = {!!}
-- transform-lemma (Sim-Seq p p₁) E-Seq r = {!!}
-- -- transform-lemma Sim-Lit ()
-- -- transform-lemma (Sim-Add p p₁) (E-Add-1 q) with transform-lemma p q
-- -- ... | fst , snd , snd₁ = {!!} , Sim-Add {!!} {!!} , lift′* E-Add-1′ {!!}
-- -- transform-lemma (Sim-Add p p₁) (E-Add-2 q) r s = {!!}
-- -- transform-lemma (Sim-Add p p₁) (E-Add x) r s = {!!}
-- -- transform-lemma (Sim-Print p) (E-Print-1 q) r s = {!!}
-- -- transform-lemma (Sim-Print p) E-Print r s = {!!}
-- -- transform-lemma (Sim-Seq p p₁) (E-Seq-1 q) r s = {!!}
-- -- transform-lemma (Sim-Seq p p₁) (E-Seq-2 q) r s = {!!}
-- -- transform-lemma (Sim-Seq p p₁) E-Seq r s = {!!}

data Leg a† b ω† : Set where
  leg : ∀ {b† ω′†} →
    -- ⟨ b , ω′ ⟩~⟨ b† , ω′† ⟩ →
    b ~ b† →
    ⟨ a† , ω† ⟩⟶′*⟨ b† , ω′† ⟩ →
    -------------
    Leg a† b ω†

-- sim : ∀ {a a† b ω ω′ ω†} →
--   a ~ a† →
--   ⟨ a , ω ⟩⟶⟨ b , ω′ ⟩ →
--   ω† ≡ transform-output a ω →
--   Leg a† b ω†
-- sim Sim-Lit () r
-- sim (Sim-Add {a = a}  p p₁) (E-Add-1 {ω = ω} q) refl with transform-output a ω in E
-- ... | u with sim p q (sym E)
-- sim (Sim-Add {_} p p₁) (E-Add-1 {ω = _} q) refl | u | leg x x₁ = leg (Sim-Add x p₁) (lift′* E-Add-1′ {!!})

-- sim (Sim-Add p p₁) (E-Add-2 q) r = {!!}
-- sim (Sim-Add p p₁) (E-Add x) r = {!!}
-- sim (Sim-Print p) (E-Print-1 q) r = {!!}
-- sim (Sim-Print p) E-Print r = {!!}
-- sim (Sim-Seq p p₁) (E-Seq-1 q) r = {!!}
-- sim (Sim-Seq p p₁) (E-Seq-2 q) r = {!!}
-- sim (Sim-Seq p p₁) E-Seq r = {!!}
-- sim Sim-Lit () r
-- sim (Sim-Add p p₁) (E-Add-1 q) refl with sim p q (proj₂ transform-output-fn)
-- ... | leg x x₁ = leg {!!} {!!}
-- sim (Sim-Add p p₁) (E-Add-2 q) r = {!!}
-- sim (Sim-Add p p₁) (E-Add x) r = {!!}
-- sim (Sim-Print p) (E-Print-1 q) r = {!!}
-- sim (Sim-Print p) E-Print r = {!!}
-- sim (Sim-Seq p p₁) (E-Seq-1 q) r = {!!}

-- sim : ∀ {a a† b ω ω′ ω†} →
--   a ~ a† →
--   ⟨ a , ω ⟩⟶*⟨ b , ω′ ⟩ →
--   transform-output a ω ω† →
--   Leg a† b ω†
-- sim Sim-Lit E-Done refl = leg Sim-Lit E-Done′
-- sim (Sim-Add p p₁) E-Done refl = leg (Sim-Add p p₁) E-Done′
-- sim (Sim-Print p) E-Done refl = leg (Sim-Print p) E-Done′
-- sim (Sim-Seq p p₁) E-Done r = leg (Sim-Seq p p₁) E-Done′
-- sim (Sim-Add p p₁) (E-Step (E-Add-1 x) q) refl with sim p {!!}
-- ... | u = leg {!!} (E-Step′ (E-Add-1′ {!!}) {!!})
-- sim (Sim-Add p p₁) (E-Step (E-Add-2 x) q) refl = {!!}
-- sim (Sim-Add p p₁) (E-Step (E-Add x) q) refl = {!!}
-- sim (Sim-Print p) (E-Step (E-Print-1 x) q) refl = {!!}
-- sim (Sim-Print p) (E-Step E-Print q) refl = {!!}
-- sim (Sim-Seq p p₁) (E-Step (E-Seq-1 x) q) r = {!!}



-- data Leg a† b ω′ : Set where
--   leg : ∀ {ω† b† ω′†} →
--     -- ⟨ b , ω′ ⟩~⟨ b† , ω′† ⟩ →
--     b ~ b† →
--     ⟨ a† , ω† ⟩⟶′*⟨ b† , ω′† ⟩ →
--     -------------
--     Leg a† b ω′

-- data _[_]O~_ : Output → Expr → Output → Set where
--   O-Sim-Lit : ∀ {i ω} →
--     ω [ Lit i ]O~ ω

--   O-Sim-Add : ∀ {a b ω ω′ ω′′} →
--     ω [ a ]O~ ω′ →
--     ω′ [ b ]O~ ω′′ →
--     ω [ Add a b ]O~ ω′′

--   Sim-Add : ∀ {a b a† b† ω ω′ ω† ω†′ ω-r} →
--     ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
--     ⟨ b , ω′ ⟩~⟨ b† , ω†′ ⟩ →
--     -------------
--     ⟨ Add a b , ω ⟩~⟨ Add a† b† , ω-r ⟩


-- -- A (weak) simulation between the original one-step relation and the new one-step relation
-- data ⟨_,_⟩~⟨_,_⟩ : Expr → Output → Expr → Output → Set where
--   Sim-Lit : ∀ {i ω} →
--     -------------
--     ⟨ Lit i , ω ⟩~⟨ Lit i , ω ⟩

--   Sim-Add : ∀ {a b a† b† ω ω′ ω† ω†′ ω-r} →
--     ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
--     ⟨ b , ω′ ⟩~⟨ b† , ω†′ ⟩ →
--     -------------
--     ⟨ Add a b , ω ⟩~⟨ Add a† b† , ω-r ⟩

--   Sim-Print : ∀ {a a† ω ω†} →
--     ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
--     -------------
--     ⟨ Print a , ω ⟩~⟨ Print a† , ω† ⟩

--   Sim-Seq-1 : ∀ {a b a† b† ω ω† ω†′} →
--     ¬ Is-Value a →
--     ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
--     ⟨ b , ω ⟩~⟨ b† , ω†′ ⟩ →
--     -------------
--     ⟨ Seq a b , ω ⟩~⟨ b† , ω† ⟩

--   Sim-Seq : ∀ {a b a† b† ω ω† ω†′} →
--     Is-Value a →
--     ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
--     ⟨ b , ω ⟩~⟨ b† , ω†′ ⟩ →
--     -------------
--     ⟨ Seq a b , ω ⟩~⟨ b† , ω†′ ⟩


-- data Leg a† b ω′ : Set where
--   leg : ∀ {ω† b† ω′†} →
--     ⟨ b , ω′ ⟩~⟨ b† , ω′† ⟩ →
--     ⟨ a† , ω† ⟩⟶′*⟨ b† , ω′† ⟩ →
--     -------------
--     Leg a† b ω′

-- Lit-pure : ∀ {a i ω ω′} →
--   ⟨ Lit i , ω ⟩⟶⟨ a , ω′ ⟩ →
--   ω ≡ ω′
-- Lit-pure ()

-- change-state : ∀ {a a′ ω ω′ ω₁} →
--   ⟨ a , ω ⟩~⟨ a′ , ω′ ⟩ →
--   ∃[ ω₂ ]
--   ⟨ a , ω₁ ⟩~⟨ a′ , ω₂ ⟩
-- -- change-state Sim-Lit = _ , Sim-Lit
-- -- change-state (Sim-Add {ω†′ = ω†′} (Value-Choice-yes x) p p₁) = proj₁ (change-state p₁) , Sim-Add {ω′ = ω†′} (Value-Choice-yes x) (proj₂ (change-state p)) (proj₂ (change-state p₁))
-- -- change-state (Sim-Add {ω†′ = ω†′} (Value-Choice-no x) p p₁) = proj₁ (change-state p) , Sim-Add {ω′ = ω†′} (Value-Choice-no x) (proj₂ (change-state p)) (proj₂ (change-state p₁))
-- -- change-state (Sim-Print p) = _ , Sim-Print (proj₂ (change-state p))
-- -- change-state (Sim-Seq-1 x p p₁) = _ , Sim-Seq-1 x (proj₂ (change-state p)) (proj₂ (change-state p₁))
-- -- change-state (Sim-Seq x p p₁) = _ , Sim-Seq x (proj₂ (change-state p)) (proj₂ (change-state p₁))

-- eval-deterministic : ∀ {a b₁ b₂ ω ω′ ω₁ ω₂} →
--   ⟨ a , ω ⟩⟶⟨ b₁ , ω₁ ⟩ →
--   ⟨ a , ω′ ⟩⟶⟨ b₂ , ω₂ ⟩ →
--   b₁ ≡ b₂
-- eval-deterministic (E-Add-1 prf1) (E-Add-1 prf2) rewrite eval-deterministic prf1 prf2 = refl
-- eval-deterministic (E-Add-2 prf1) (E-Add-2 prf2) rewrite eval-deterministic prf1 prf2 = refl
-- eval-deterministic (E-Add refl) (E-Add refl) = refl
-- eval-deterministic (E-Print-1 prf1) (E-Print-1 prf2) rewrite eval-deterministic prf1 prf2 = refl
-- eval-deterministic E-Print E-Print = refl
-- eval-deterministic (E-Seq-1 prf1) (E-Seq-1 prf2) rewrite eval-deterministic prf1 prf2 = refl
-- eval-deterministic (E-Seq-2 prf1) (E-Seq-2 prf2) rewrite eval-deterministic prf1 prf2 = refl
-- eval-deterministic E-Seq E-Seq = refl

-- sim-value : ∀ {a a′ ω ω′} →
--   Is-Value a →
--   ⟨ a , ω ⟩~⟨ a′ , ω′ ⟩ →
--   Is-Value a′
-- sim-value a-val Sim-Lit = Is-Value-Lit

-- ⟨_,_⟩⇓⟨_,_⟩ : Expr → Output → Expr → Output → Set
-- ⟨_,_⟩⇓⟨_,_⟩ a ω b ω′ =
--   Is-Value b × (⟨ a , ω ⟩⟶*⟨ b , ω′ ⟩)

-- ⟨_,_⟩⇓′⟨_,_⟩ : Expr → Output → Expr → Output → Set
-- ⟨_,_⟩⇓′⟨_,_⟩ a ω b ω′ =
--   Is-Value b × (⟨ a , ω ⟩⟶′*⟨ b , ω′ ⟩)

-- sim : ∀ {a a† b ω ω′ ω†} →
--   ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
--   ⟨ a , ω ⟩⟶⟨ b , ω′ ⟩ →
--   Leg a† b ω′
-- sim Sim-Lit ()
-- sim (Sim-Add q prf1 prf2) (E-Add-1 prf3) with sim prf1 prf3
-- ... | leg x x₁ = leg (Sim-Add {!!} x prf2) (lift′* E-Add-1′ x₁)

-- sim (Sim-Add {b = b} q prf1 prf2) (E-Add-2 prf3) with value-or-can-step {b}
-- sim (Sim-Add {b = _} q prf1 prf2) (E-Add-2 ()) | inj₁ Is-Value-Lit
-- ... | inj₂ (fst , fst₁ , snd) with sim prf2 snd
-- sim (Sim-Add {b = _} q Sim-Lit prf2) (E-Add-2 prf3) | inj₂ (fst , fst₁ , snd) | leg x x₁
--   rewrite eval-deterministic prf3 snd = leg (Sim-Add {!!} Sim-Lit x) (lift′* E-Add-2′ {!!}) --(lift′* E-Add-2′ E-Done′)

-- sim (Sim-Add q Sim-Lit Sim-Lit) (E-Add refl) = leg Sim-Lit (one-step′ (E-Add′ refl))

-- sim (Sim-Print prf1) (E-Print-1 prf2) with sim prf1 prf2
-- ... | leg x x₁ = leg (Sim-Print x) (lift′* E-Print-1′ x₁)

-- sim (Sim-Print Sim-Lit) E-Print = leg Sim-Lit (one-step′ E-Print′)

-- sim (Sim-Seq-1 x prf1 prf2) (E-Seq-1 {a′ = a′} prf3) with dec-value a′
-- sim (Sim-Seq-1 x prf1 prf2) (E-Seq-1 {a′ = a′} prf3) | inj₂ y with sim prf1 prf3
-- ... | leg x₁ x₂ = leg (Sim-Seq-1 y x₁ (proj₂ (change-state prf2))) E-Done′

-- sim (Sim-Seq-1 x prf1 prf2) (E-Seq-1 {a′ = a′} prf3) | inj₁ Is-Value-Lit with sim prf1 prf3
-- sim (Sim-Seq-1 x prf1 prf2) (E-Seq-1 {_} {.(Lit _)} prf3) | inj₁ Is-Value-Lit | leg Sim-Lit x₂ = leg (Sim-Seq Is-Value-Lit Sim-Lit (proj₂ (change-state prf2))) E-Done′

-- sim (Sim-Seq-1 x prf1 prf2) (E-Seq-2 prf3) = ⊥-elim (x Is-Value-Lit)
-- sim (Sim-Seq-1 x prf1 prf2) E-Seq = ⊥-elim (x Is-Value-Lit)
-- sim (Sim-Seq Is-Value-Lit prf1 prf2) (E-Seq-1 ())
-- sim (Sim-Seq x prf1 prf2) (E-Seq-2 prf3) with sim prf2 prf3
-- ... | leg x₁ x₂ = leg (Sim-Seq Is-Value-Lit Sim-Lit x₁) x₂
-- sim (Sim-Seq x Sim-Lit Sim-Lit) E-Seq = leg Sim-Lit E-Done′

-- ~trans : ∀ {a a′ a† a′† ω ω′ ω† ω′†} →
--   ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
--   ⟨ a† , ω† ⟩⟶′⟨ a′† , ω′† ⟩ →
--   ⟨ a , ω ⟩⟶⟨ a′ , ω′ ⟩ →
--   ⟨ a′ , ω′ ⟩~⟨ a′† , ω′† ⟩
-- ~trans  (Sim-Add (Value-Choice-no x) p p₁) (E-Add-1′ q) (E-Add-1 {a′ = a′} r) with dec-value a′
-- ... | inj₂ y = Sim-Add (Value-Choice-no y) (~trans p q r) p₁
-- ... | inj₁ Is-Value-Lit = Sim-Add (Value-Choice-yes Is-Value-Lit) (~trans p q r) p₁

-- ~trans (Sim-Add (Value-Choice-no x) (Sim-Seq-1 x₁ p p₂) p₁) (E-Add-2′ q) (E-Add-1 r) = Sim-Add {!!} {!!} {!!}
-- ~trans (Sim-Add (Value-Choice-no x) (Sim-Seq x₁ p p₂) p₁) (E-Add-2′ q) (E-Add-1 r) = {!!}

-- ~trans p (E-Add′ x) (E-Add-1 r) = {!!}
-- ~trans p q (E-Add-2 r) = {!!}
-- ~trans p q (E-Add x) = {!!}
-- ~trans p q (E-Print-1 r) = {!!}
-- ~trans p q E-Print = {!!}
-- ~trans p q (E-Seq-1 r) = {!!}
-- ~trans p q (E-Seq-2 r) = {!!}
-- ~trans p q E-Seq = {!!}

-- -- ~trans p E-Done′ E-Done = p
-- -- ~trans (Sim-Add p p₁) E-Done′ (E-Step (E-Add-1 x) E-Done) = Sim-Add (~trans p E-Done′ (one-step x)) p₁
-- -- ~trans (Sim-Add p p₁) E-Done′ (E-Step (E-Add-1 x) (E-Step x₁ q)) = {!Sim-Add!}
-- -- ~trans p E-Done′ (E-Step (E-Add-2 x) q) = {!!}
-- -- ~trans p E-Done′ (E-Step (E-Add x) q) = {!!}
-- -- ~trans p E-Done′ (E-Step (E-Print-1 x) q) = {!!}
-- -- ~trans p E-Done′ (E-Step E-Print q) = {!!}
-- -- ~trans p E-Done′ (E-Step (E-Seq-1 x) q) = {!!}
-- -- ~trans p E-Done′ (E-Step (E-Seq-2 x) q) = {!!}
-- -- ~trans p E-Done′ (E-Step E-Seq q) = {!!}
-- -- ~trans p (E-Step′ x r) q = {!!}

-- -- ~trans (Sim-Add p p₁) (E-Add-1′ q) (E-Add-1 r) = Sim-Add (~trans p {!!} r) {!!}
-- -- ~trans p (E-Add-2′ q) (E-Add-1 r) = {!!}
-- -- ~trans p (E-Add′ x) (E-Add-1 r) = {!!}
-- -- ~trans p q (E-Add-2 r) = {!!}
-- -- ~trans p q (E-Add x) = {!!}
-- -- ~trans p q (E-Print-1 r) = {!!}
-- -- ~trans p q E-Print = {!!}
-- -- ~trans p q (E-Seq-1 r) = {!!}
-- -- ~trans p q (E-Seq-2 r) = {!!}
-- -- ~trans p q E-Seq = {!!}


-- extend-Leg : ∀ {a† b† b ω′ ω₁ ω₂} →
--   ⟨ a† , ω₁ ⟩⟶′*⟨ b† , ω₂ ⟩ →
--   Leg b† b ω′ →
--   Leg a† b ω′
-- extend-Leg E-Done′ (leg x x₁) = leg x x₁
-- extend-Leg (E-Step′ x₂ p) (leg x x₁) with extend-Leg p (leg x x₁)
-- ... | leg x₃ x₄ = leg x₃ (E-Step′ x₂ {!!})

-- append : ∀ {a b c d ω ω′ ω′′} →
--   ⟨ a , ω ⟩⟶′*⟨ b , ω′ ⟩ →
--   ⟨ b , ω′ ⟩⟶′*⟨ d , ω′′ ⟩ →
--   ⟨ a , ω ⟩⟶′*⟨ d , ω′′ ⟩
-- append E-Done′ q = q
-- append (E-Step′ x p) q = E-Step′ x (append p q)

-- sim* : ∀ {a a† b ω ω′ ω†} →
--   ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
--   ⟨ a , ω ⟩⟶*⟨ b , ω′ ⟩ →
--   Leg a† b ω′
-- sim* r E-Done = leg r E-Done′
-- sim* r (E-Step x p) with sim r x
-- ... | leg z w with sim* z p
-- sim* r (E-Step x p) | leg z E-Done′ | leg x₁ x₂ = leg x₁ x₂
-- sim* r (E-Step x p) | leg1@(leg z (E-Step′ x₃ w)) | leg2@(leg x₁ x₂ )= {!!} --leg {!!} {!!} -- (E-Step′ x₃ w)
--   -- let q = leg x₁ x₂
--   -- in
--   -- {!!}
--   -- -- extend-Leg w q

-- sim-same-value : ∀ {a a† c c† ω ω† ω′ ω′†} →
--   ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
--   ⟨ a , ω ⟩⇓⟨ c , ω′ ⟩ →
--   ⟨ a† , ω† ⟩⇓′⟨ c† , ω′† ⟩ →
--   c ≡ c†
-- sim-same-value Sim-Lit (fst , E-Done) (fst₁ , E-Done′) = refl
-- sim-same-value Sim-Lit (Is-Value-Lit , E-Done) (Is-Value-Lit , E-Step′ () snd₁)
-- sim-same-value (Sim-Seq-1 x₁ p p₁) (Is-Value-Lit , E-Step x snd) (Is-Value-Lit , E-Done′) = {!!}
-- sim-same-value (Sim-Seq x₁ p p₁) (Is-Value-Lit , E-Step x snd) (Is-Value-Lit , E-Done′) = {!!}
-- sim-same-value p (fst , E-Step x snd) (fst₁ , E-Step′ x₁ snd₁) = {!!}


-- -- -- output-deterministic : ∀ {a b₁ b₂ ω ω₁ ω₂} →
-- -- --   ⟨ a , ω ⟩⟶⟨ b₁ , ω₁ ⟩ →
-- -- --   ⟨ a , ω ⟩⟶⟨ b₂ , ω₂ ⟩ →
-- -- --   ω₁ ≡ ω₂
-- -- -- output-deterministic (E-Add-1 prf1) (E-Add-1 prf2) rewrite output-deterministic prf1 prf2 = refl
-- -- -- output-deterministic (E-Add-2 prf1) (E-Add-2 prf2) rewrite output-deterministic prf1 prf2 = refl
-- -- -- output-deterministic (E-Add x) (E-Add x₁) = refl
-- -- -- output-deterministic (E-Print-1 prf1) (E-Print-1 prf2) rewrite output-deterministic prf1 prf2 = refl
-- -- -- output-deterministic E-Print E-Print = refl
-- -- -- output-deterministic (E-Seq-1 prf1) (E-Seq-1 prf2) rewrite output-deterministic prf1 prf2 = refl
-- -- -- output-deterministic (E-Seq-2 prf1) (E-Seq-2 prf2) rewrite output-deterministic prf1 prf2 = refl
-- -- -- output-deterministic E-Seq E-Seq = refl

-- -- -- output-backwards-deterministic : ∀ {a b₁ b₂ ω₁ ω₂ ω′} →
-- -- --   ⟨ a , ω₁ ⟩⟶⟨ b₁ , ω′ ⟩ →
-- -- --   ⟨ a , ω₂ ⟩⟶⟨ b₂ , ω′ ⟩ →
-- -- --   ω₁ ≡ ω₂
-- -- -- output-backwards-deterministic (E-Add-1 prf1) (E-Add-1 prf2) = output-backwards-deterministic prf1 prf2
-- -- -- output-backwards-deterministic (E-Add-2 prf1) (E-Add-2 prf2) = output-backwards-deterministic prf1 prf2
-- -- -- output-backwards-deterministic (E-Add refl) (E-Add refl) = refl
-- -- -- output-backwards-deterministic (E-Print-1 prf1) (E-Print-1 prf2) = output-backwards-deterministic prf1 prf2
-- -- -- output-backwards-deterministic E-Print E-Print = refl
-- -- -- output-backwards-deterministic (E-Seq-1 prf1) (E-Seq-1 prf2) = output-backwards-deterministic prf1 prf2
-- -- -- output-backwards-deterministic (E-Seq-2 prf1) (E-Seq-2 prf2) = output-backwards-deterministic prf1 prf2
-- -- -- output-backwards-deterministic E-Seq E-Seq = refl

-- -- -- -- deterministic-O~ : ∀ {a ω ω₁ ω₂} →
-- -- -- --   ω [ a ]O~ ω₁ →
-- -- -- --   ω [ a ]O~ ω₂ →
-- -- -- --   ω₁ ≡ ω₂
-- -- -- -- deterministic-O~ O-Sim-Lit O-Sim-Lit = refl
-- -- -- -- deterministic-O~ (O-Sim-Add prf1 prf2) (O-Sim-Add prf3 prf4) rewrite deterministic-O~ prf1 prf3 | deterministic-O~ prf2 prf4 = refl
-- -- -- -- deterministic-O~ (O-Sim-Print x prf1 x₁) (O-Sim-Print x₂ prf2 x₃) = output-deterministic x₁ x₃
-- -- -- -- deterministic-O~ (O-Sim-Seq prf1 prf2) (O-Sim-Seq prf3 prf4) rewrite deterministic-O~ prf1 prf3 | deterministic-O~ prf2 prf4 = refl

-- -- -- -- backwards-deterministic-O~ : ∀ {a ω₁ ω₂ ω′} →
-- -- -- --   ω₁ [ a ]O~ ω′ →
-- -- -- --   ω₂ [ a ]O~ ω′ →
-- -- -- --   ω₁ ≡ ω₂
-- -- -- -- backwards-deterministic-O~ O-Sim-Lit O-Sim-Lit = refl
-- -- -- -- backwards-deterministic-O~ (O-Sim-Add prf1 prf2) (O-Sim-Add prf3 prf4)
-- -- -- --   rewrite backwards-deterministic-O~ prf2 prf4 | backwards-deterministic-O~ prf1 prf3 = refl
-- -- -- -- backwards-deterministic-O~ (O-Sim-Print x prf1 x₁) (O-Sim-Print x₂ prf2 x₃) = output-backwards-deterministic x₁ x₃
-- -- -- -- backwards-deterministic-O~ (O-Sim-Seq prf1 prf2) (O-Sim-Seq prf3 prf4)
-- -- -- --   rewrite backwards-deterministic-O~ prf2 prf4 | backwards-deterministic-O~ prf1 prf3 = refl

-- -- -- seq-steps : ∀ {a a† b c a† b† ω ω′ ω†} →
-- -- --   ⟨ Seq a b , ω ⟩⟶⟨ c , ω′ ⟩ →
-- -- --   ⟨ a , ω ⟩⟶′*⟨ a† , ω† ⟩ →
-- -- --   ⟨ Seq a b , ω ⟩⟶′*⟨ b , ω† ⟩
-- -- -- seq-steps (E-Seq-1 p) q = lift′* E-Seq′ q
-- -- -- seq-steps (E-Seq-2 p) E-Done′ = lift′* E-Seq′ E-Done′
-- -- -- seq-steps E-Seq q = lift′* E-Seq′ q

-- -- -- sim-lemma : ∀ {a b ω ω′ ω′′ ω′′′} →
-- -- --   ⟨ a , ω ⟩~⟨ a , ω′ ⟩ →
-- -- --   ⟨ a , ω′′ ⟩⟶⟨ b , ω′′′ ⟩ →
-- -- --   ∃[ ω₁ ] ∃[ ω₂ ]
-- -- --   ⟨ b , ω₁ ⟩~⟨ b , ω₂ ⟩
-- -- -- sim-lemma Sim-Lit ()
-- -- -- sim-lemma (Sim-Add p p₁) (E-Add-1 q) =
-- -- --   let x , y , r = sim-lemma p q
-- -- --   in
-- -- --   _ , _ , Sim-Add r p₁
-- -- -- sim-lemma (Sim-Add p p₁) (E-Add-2 q) = {!!}
-- -- -- sim-lemma (Sim-Add p p₁) (E-Add x) = {!!}
-- -- -- sim-lemma (Sim-Print p) (E-Print-1 q) = {!!}
-- -- -- sim-lemma (Sim-Print p) E-Print = {!!}
-- -- -- sim-lemma (Sim-Seq p p₁ r) (E-Seq-1 q) = {!!}
-- -- -- sim-lemma (Sim-Seq p p₁ r) (E-Seq-2 q) = {!!}
-- -- -- sim-lemma (Sim-Seq p p₁ r) E-Seq = {!!}

-- -- -- sim-Lit-lemma : ∀ {i j a ω ω′} →
-- -- --   ⟨ Seq (Lit i) (Lit j) , ω ⟩~⟨ a , ω′ ⟩ →
-- -- --   a ≡ Lit j
-- -- -- sim-Lit-lemma (Sim-Seq p p₁ r) = {!!}

-- -- -- Lit-flip : ∀ {a i ω ω′} →
-- -- --   ⟨ Lit i , ω ⟩⟶′*⟨ a , ω′ ⟩ →
-- -- --   ⟨ a , ω′ ⟩⟶′*⟨ Lit i , ω ⟩
-- -- -- Lit-flip E-Done′ = E-Done′

-- -- -- sim-lemma2  : ∀ {i j a† ω ω′} →
-- -- --   ⟨ Seq (Lit i) (Lit j) , ω ⟩~⟨ a† , ω′ ⟩ →
-- -- --   a† ≡ Lit j
-- -- -- sim-lemma2 (Sim-Seq p p₁ r) = {!!}

-- -- -- sim : ∀ {a a† b ω ω′ ω†} →
-- -- --   ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
-- -- --   ⟨ a , ω ⟩⟶⟨ b , ω′ ⟩ →
-- -- --   Leg a† b ω′
-- -- -- sim Sim-Lit ()
-- -- -- sim (Sim-Add prf1 prf2 ) (E-Add-1 prf3) with sim prf1 prf3
-- -- -- sim (Sim-Add prf1 prf2 ) (E-Add-1 prf3) | leg x₂ x₃ =
-- -- --   leg (Sim-Add x₂ prf2) (E-Add-1′* {!!})

-- -- -- sim (Sim-Add {b = b} {ω′ = ω′} Sim-Lit prf2) (E-Add-2 prf3) with value-or-can-step {b} {ω′}
-- -- -- sim (Sim-Add {b = _} {ω′ = ω′} Sim-Lit Sim-Lit) (E-Add-2 ()) | inj₁ Is-Value-Lit
-- -- -- sim (Sim-Add {b = _} {ω′ = ω′} Sim-Lit prf2) (E-Add-2 prf3) | inj₂ (fst , fst₁ , snd)
-- -- --   with sim prf2 snd
-- -- -- sim (Sim-Add {b = _} {ω′ = ω′} Sim-Lit prf2) (E-Add-2 prf3) | inj₂ (fst , fst₁ , snd) | leg x x₁
-- -- --   rewrite eval-deterministic prf3 snd =
-- -- --     leg (Sim-Add Sim-Lit x) (lift′* E-Add-2′ x₁)

-- -- -- sim (Sim-Add Sim-Lit Sim-Lit) (E-Add refl) = leg Sim-Lit (one-step′ (E-Add′ refl))

-- -- -- sim (Sim-Print prf1) (E-Print-1 prf2) with sim prf1 prf2
-- -- -- ... | leg x x₁ = leg (Sim-Print x) (lift′* E-Print-1′ x₁)

-- -- -- sim (Sim-Print Sim-Lit) E-Print = leg Sim-Lit (one-step′ E-Print′)

-- -- -- sim (Sim-Seq prf1 prf2 (r₁ , r₂)) (E-Seq-1 prf3) with sim prf1 prf3
-- -- -- sim (Sim-Seq prf1 prf2 (r₁ , E-Done)) (E-Seq-1 prf3) | leg x₁ E-Done′ = leg (Sim-Seq x₁ prf2 {!!}) E-Done′
-- -- -- sim (Sim-Seq prf1 prf2 (r₁ , E-Step x r₂)) (E-Seq-1 prf3) | leg x₁ E-Done′ = leg (Sim-Seq x₁ prf2 {!!}) E-Done′
-- -- -- ... | leg x₁ (E-Step′ x₂ x₃) = leg (Sim-Seq x₁ {!!} {!!}) E-Done′

-- -- -- sim (Sim-Seq p@Sim-Lit prf2 (.(Lit _) , E-Done)) (E-Seq-2 prf3)
-- -- --   with sim prf2 prf3
-- -- -- ... | leg x x₁ = leg (Sim-Seq Sim-Lit x (_ , E-Done)) x₁
-- -- --   -- leg (Sim-Seq Sim-Lit (proj₂ (proj₂ (sim-lemma {!!} prf3)))) {!!}

-- -- -- -- sim p@(Sim-Seq Sim-Lit Sim-Lit) q@E-Seq = leg Sim-Lit {!!}
-- -- -- sim p0@(Sim-Seq p@Sim-Lit prf2 r) q@E-Seq rewrite sim-lemma2 p0 = leg Sim-Lit E-Done′

-- -- -- -- sim : ∀ {a a† b ω ω′ ω†} →
-- -- -- --   ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
-- -- -- --   ⟨ a , ω ⟩⟶⟨ b , ω′ ⟩ →
-- -- -- --   Leg a† ω† b ω′
-- -- -- -- sim Sim-Lit ()
-- -- -- -- sim (Sim-Add prf1 prf2 ) (E-Add-1 prf3) with sim prf1 prf3
-- -- -- -- ... | leg x₂ x₃ x₄
-- -- -- --         = leg (Sim-Add x₂ prf2) (E-Add-1′ {!!}) (O-Sim-Add {!!} {!!})
-- -- -- -- sim (Sim-Add prf1 prf2) (E-Add-2 prf3) = {!!}
-- -- -- -- sim (Sim-Add prf1 prf2) (E-Add x₂) = {!!}
-- -- -- -- sim (Sim-Print prf1) (E-Print-1 prf2) = {!!}
-- -- -- -- sim (Sim-Print prf1) E-Print = {!!}
-- -- -- -- sim (Sim-Seq prf1 prf2 x) (E-Seq-1 prf3) = {!!}
-- -- -- -- sim (Sim-Seq prf1 prf2 x) (E-Seq-2 prf3) = {!!}
-- -- -- -- sim (Sim-Seq prf1 prf2 x) E-Seq = {!!}

-- -- -- -- sim Sim-Lit ()
-- -- -- -- sim (Sim-Add prf1 prf2 x x₁) (E-Add-1 prf3) with sim prf1 prf3
-- -- -- -- ... | leg x₂ x₃ = leg (Sim-Add x₂ prf2 {!!} {!!}) (E-Add-1′ {!!})
-- -- -- -- sim (Sim-Add prf1 prf2 x x₁) (E-Add-2 prf3) = {!!}
-- -- -- -- sim (Sim-Add prf1 prf2 x x₁) (E-Add x₂) = {!!}
-- -- -- -- sim (Sim-Print prf1) (E-Print-1 prf2) = {!!}
-- -- -- -- sim (Sim-Print prf1) E-Print = {!!}
-- -- -- -- sim (Sim-Seq prf1 prf2 x) (E-Seq-1 prf3) = {!!}
-- -- -- -- sim (Sim-Seq prf1 prf2 x) (E-Seq-2 prf3) = {!!}
-- -- -- -- sim (Sim-Seq prf1 prf2 x) E-Seq = {!!}


-- -- -- -- -- A simulation between the original one-step relation and the new one-step relation
-- -- -- -- data _~_ : Expr → Expr → Set where
-- -- -- --   Sim-Lit : ∀ {i} →
-- -- -- --     -------------
-- -- -- --     Lit i ~ Lit i

-- -- -- --   Sim-Add : ∀ {a b a† b†} →
-- -- -- --     a ~ a† →
-- -- -- --     b ~ b† →
-- -- -- --     -------------
-- -- -- --     Add a b ~ Add a† b†

-- -- -- --   Sim-Print : ∀ {a a†} →
-- -- -- --     a ~ a† →
-- -- -- --     -------------
-- -- -- --     Print a ~ Print a†

-- -- -- --   Sim-Seq : ∀ {a b b†} →
-- -- -- --     b ~ b† →
-- -- -- --     -------------
-- -- -- --     Seq a b ~ b†

-- -- -- -- eval-deterministic : ∀ {a b₁ b₂ ω ω₁ ω₂} →
-- -- -- --   ⟨ a , ω ⟩⟶⟨ b₁ , ω₁ ⟩ →
-- -- -- --   ⟨ a , ω ⟩⟶⟨ b₂ , ω₂ ⟩ →
-- -- -- --   b₁ ≡ b₂
-- -- -- -- eval-deterministic (E-Add-1 prf1) (E-Add-1 prf2) rewrite eval-deterministic prf1 prf2 = refl
-- -- -- -- eval-deterministic (E-Add-2 prf1) (E-Add-2 prf2) rewrite eval-deterministic prf1 prf2 = refl
-- -- -- -- eval-deterministic (E-Add refl) (E-Add refl) = refl
-- -- -- -- eval-deterministic (E-Print-1 prf1) (E-Print-1 prf2) rewrite eval-deterministic prf1 prf2 = refl
-- -- -- -- eval-deterministic E-Print E-Print = refl
-- -- -- -- eval-deterministic (E-Seq-1 prf1) (E-Seq-1 prf2) rewrite eval-deterministic prf1 prf2 = refl
-- -- -- -- eval-deterministic (E-Seq-2 prf1) (E-Seq-2 prf2) rewrite eval-deterministic prf1 prf2 = refl
-- -- -- -- eval-deterministic E-Seq E-Seq = refl

-- -- -- -- -- A simulation between the original one-step relation and the new one-step relation
-- -- -- -- data ⟨_,_⟩~⟨_,_⟩ : Expr → Output → Expr → Output → Set where
-- -- -- --   Sim-Lit : ∀ {i ω} →
-- -- -- --     -------------
-- -- -- --     ⟨ Lit i , ω ⟩~⟨ Lit i , ω ⟩

-- -- -- --   Sim-Add : ∀ {a b a† b† ω ω′ ω† ω†′} →
-- -- -- --     ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
-- -- -- --     ⟨ b , ω′ ⟩~⟨ b† , ω†′ ⟩ →
-- -- -- --     -------------
-- -- -- --     ⟨ Add a b , ω ⟩~⟨ Add a† b† , ω†′ ⟩

-- -- -- --   Sim-Print : ∀ {a a† ω ω†} →
-- -- -- --     ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
-- -- -- --     -------------
-- -- -- --     ⟨ Print a , ω ⟩~⟨ Print a† , ω† ⟩

-- -- -- --   Sim-Seq : ∀ {a b a† a†′ b† ω ω′ ω† ω†′} →
-- -- -- --     ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
-- -- -- --     ⟨ b , ω′ ⟩~⟨ b , ω†′ ⟩ →
-- -- -- --     ⟨ a† , ω† ⟩⟶⟨ a†′ , ω†′ ⟩ →
-- -- -- --     -------------
-- -- -- --     -- ⟨ b , ω ⟩~⟨ Seq a† b† , ω†′ ⟩
-- -- -- --     ⟨ Seq a b , ω ⟩~⟨ b† , ω†′ ⟩
-- -- -- --     -- ⟨ b† , ω†′ ⟩~⟨ Seq a b , ω ⟩

-- -- -- -- data Leg a† ω† ω′† b ω′ : Set where
-- -- -- --   leg : ∀ {b† ω′†₂} →
-- -- -- --     ⟨ b , ω′ ⟩~⟨ b† , ω′† ⟩ →
-- -- -- --     ⟨ a† , ω† ⟩⟶′⟨ b† , ω′† ⟩ →
-- -- -- --     -------------
-- -- -- --     Leg a† ω† ω′† b ω′

-- -- -- -- -- -- ~ relates values to values
-- -- -- -- -- ~Value : ∀ {a a† ω ω†} →
-- -- -- -- --   Is-Value a →
-- -- -- -- --   ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
-- -- -- -- --   Is-Value a†
-- -- -- -- -- ~Value a-value Sim-Lit = Is-Value-Lit

-- -- -- -- backwards-det⟶′ : ∀ {a b₁ b₂ ω₁ ω₂ ω′} →
-- -- -- --   ⟨ a , ω₁ ⟩⟶′⟨ b₁ , ω′ ⟩ →
-- -- -- --   ⟨ a , ω₂ ⟩⟶′⟨ b₂ , ω′ ⟩ →
-- -- -- --   ω₁ ≡ ω₂
-- -- -- -- backwards-det⟶′ (E-Add-1′ prf1) (E-Add-1′ prf2) = backwards-det⟶′ prf1 prf2
-- -- -- -- backwards-det⟶′ (E-Add-2′ prf1) (E-Add-2′ prf2) = backwards-det⟶′ prf1 prf2
-- -- -- -- backwards-det⟶′ (E-Add′ x) (E-Add′ x₁) = refl
-- -- -- -- backwards-det⟶′ (E-Print-1′ prf1) (E-Print-1′ prf2) = backwards-det⟶′ prf1 prf2
-- -- -- -- backwards-det⟶′ E-Print′ E-Print′ = refl
-- -- -- -- backwards-det⟶′ (E-Seq′ prf1) (E-Seq′ prf2) = backwards-det⟶′ prf1 prf2

-- -- -- -- det⟶′ : ∀ {a b₁ b₂ ω ω₁ ω₂} →
-- -- -- --   ⟨ a , ω ⟩⟶′⟨ b₁ , ω₁ ⟩ →
-- -- -- --   ⟨ a , ω ⟩⟶′⟨ b₂ , ω₂ ⟩ →
-- -- -- --   ω₁ ≡ ω₂
-- -- -- -- det⟶′ (E-Add-1′ prf1) (E-Add-1′ prf2) rewrite det⟶′ prf1 prf2 = refl
-- -- -- -- det⟶′ (E-Add-2′ prf1) (E-Add-2′ prf2) rewrite det⟶′ prf1 prf2 = refl
-- -- -- -- det⟶′ (E-Add′ x) (E-Add′ x₁) = refl
-- -- -- -- det⟶′ (E-Print-1′ prf1) (E-Print-1′ prf2) rewrite det⟶′ prf1 prf2 = refl
-- -- -- -- det⟶′ E-Print′ E-Print′ = refl
-- -- -- -- det⟶′ (E-Seq′ prf1) (E-Seq′ prf2) = det⟶′ prf1 prf2

-- -- -- -- -- Leg-output-det : ∀ {a† ω†₁ ω†₂ b ω′} →
-- -- -- -- --   Leg a† ω†₁ b ω′ →
-- -- -- -- --   Leg a† ω†₂ b ω′ →
-- -- -- -- --   ω†₁ ≡ ω†₂
-- -- -- -- -- Leg-output-det (leg x x₁) (leg x₂ x₃) = {!!}
-- -- -- -- --   --backwards-det⟶′ x₁ {!!}

-- -- -- -- -- --       ⟶
-- -- -- -- -- --   a  ---> b
-- -- -- -- -- --   |       |
-- -- -- -- -- -- ~ |       | ~
-- -- -- -- -- --   |       |
-- -- -- -- -- --   a† ---> b†
-- -- -- -- -- --       ⟶

-- -- -- -- -- ~eq : ∀ {a b a† b† ω ω′} →


-- -- -- -- sim : ∀ {a a† b ω ω′ ω†} →
-- -- -- --   ⟨ a , ω ⟩~⟨ a† , ω† ⟩ →
-- -- -- --   ⟨ a , ω ⟩⟶⟨ b , ω′ ⟩ →
-- -- -- --   Leg a† ω† ω† b ω′
-- -- -- -- sim Sim-Lit ()
-- -- -- -- sim (Sim-Add prf1 prf2 x) (E-Add-1 prf3) with sim prf1 prf3
-- -- -- -- ... | leg x₁ x₂ =
-- -- -- --   let eq = output-deterministic x prf3
-- -- -- --   in leg (Sim-Add x₁ prf2 {!!}) (E-Add-1′ {!!})
-- -- -- --   -- leg (Sim-Add x₁ prf2 {!!}) (E-Add-1′ x₂)
-- -- -- -- sim (Sim-Add prf1 prf2 x) (E-Add-2 prf3) = {!!}
-- -- -- -- sim (Sim-Add prf1 prf2 x) (E-Add x₁) = {!!}
-- -- -- -- sim (Sim-Print prf1) (E-Print-1 prf2) = {!!}
-- -- -- -- sim (Sim-Print prf1) E-Print = {!!}
-- -- -- -- sim (Sim-Seq prf1 prf2 x) (E-Seq-1 prf3) = {!!}
-- -- -- -- sim (Sim-Seq prf1 prf2 x) (E-Seq-2 prf3) = {!!}
-- -- -- -- sim (Sim-Seq prf1 prf2 x) E-Seq = {!!}
