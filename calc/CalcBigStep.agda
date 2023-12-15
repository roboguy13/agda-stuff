module CalcBigStep where

open import Data.Integer
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Syntax
open import CalcSmallStep hiding (⟨_,_⟩⟶′*⟨_,_⟩; counterexample)

data ⟨_,_⟩⇓⟨_,_⟩ : Expr → Output → ℤ → Output → Set where
  ⇓-Lit : ∀ {i ω} →
    -------------
    ⟨ Lit i , ω ⟩⇓⟨ i , ω ⟩

  ⇓-Add : ∀ {a b v₁ v₂ r ω ω′ ω′′} →
    ⟨ a , ω ⟩⇓⟨ v₁ , ω′ ⟩ →
    ⟨ b , ω′ ⟩⇓⟨ v₂ , ω′′ ⟩ →
    r ≡ v₁ + v₂ →
    -------------
    ⟨ Add a b , ω ⟩⇓⟨ r , ω′′ ⟩

  ⇓-Print : ∀ {a v ω ω′} →
    ⟨ a , ω ⟩⇓⟨ v , ω′ ⟩ →
    -------------
    ⟨ Print a , ω ⟩⇓⟨ v , (v ∷ ω′) ⟩

  ⇓-Seq : ∀ {a b v₁ v₂ ω ω′ ω′′} →
    ⟨ a , ω ⟩⇓⟨ v₁ , ω′ ⟩ →
    ⟨ b , ω′ ⟩⇓⟨ v₂ , ω′′ ⟩ →
    -------------
    ⟨ Seq a b , ω ⟩⇓⟨ v₂ , ω′′ ⟩

extend⇓ : ∀ {a a′ v ω ω′ ω′′} →
  ⟨ a , ω ⟩⟶⟨ a′ , ω′ ⟩ →
  ⟨ a′ , ω′ ⟩⇓⟨ v , ω′′ ⟩ →
  ⟨ a , ω ⟩⇓⟨ v , ω′′ ⟩
extend⇓ (E-Add-1 p) (⇓-Add q q₁ x) = ⇓-Add (extend⇓ p q) q₁ x
extend⇓ (E-Add-2 p) (⇓-Add ⇓-Lit q₁ refl) = ⇓-Add ⇓-Lit (extend⇓ p q₁) refl
extend⇓ (E-Add x) ⇓-Lit = ⇓-Add ⇓-Lit ⇓-Lit x
extend⇓ (E-Print-1 p) (⇓-Print q) = ⇓-Print (extend⇓ p q)
extend⇓ E-Print ⇓-Lit = ⇓-Print ⇓-Lit
extend⇓ (E-Seq-1 p) (⇓-Seq q q₁) = ⇓-Seq (extend⇓ p q) q₁
extend⇓ (E-Seq-2 p) (⇓-Seq ⇓-Lit q₁) = ⇓-Seq ⇓-Lit (extend⇓ p q₁)
extend⇓ E-Seq ⇓-Lit = ⇓-Seq ⇓-Lit ⇓-Lit

-- Two lemmas to show that ⇓ exactly corresponds to using ⟶* to get to a value: {
⟶*to⇓ : ∀ {a v ω ω′} →
  ⟨ a , ω ⟩⟶*⟨ Lit v , ω′ ⟩ →
  ⟨ a , ω ⟩⇓⟨ v , ω′ ⟩
⟶*to⇓ E-Done = ⇓-Lit

⟶*to⇓ (E-Step (E-Add-1 x) p) with ⟶*to⇓ p
... | ⇓-Add u u₁ x₁ = ⇓-Add (extend⇓ x u) u₁ x₁

⟶*to⇓ (E-Step (E-Add-2 x) p) with ⟶*to⇓ p
... | ⇓-Add ⇓-Lit u₁ x₁ = ⇓-Add ⇓-Lit (extend⇓ x u₁) x₁

⟶*to⇓ (E-Step (E-Add refl) E-Done) = ⇓-Add ⇓-Lit ⇓-Lit refl

⟶*to⇓ (E-Step (E-Print-1 x) p) with ⟶*to⇓ p
... | ⇓-Print u = ⇓-Print (extend⇓ x u)

⟶*to⇓ (E-Step E-Print p) with ⟶*to⇓ p
... | ⇓-Lit = ⇓-Print ⇓-Lit

⟶*to⇓ (E-Step (E-Seq-1 x) p) with ⟶*to⇓ p
... | ⇓-Seq u u₁ = ⇓-Seq (extend⇓ x u) u₁

⟶*to⇓ (E-Step (E-Seq-2 x) p) with ⟶*to⇓ p
... | ⇓-Seq ⇓-Lit u₁ = ⇓-Seq ⇓-Lit (extend⇓ x u₁)

⟶*to⇓ (E-Step E-Seq p) = ⇓-Seq ⇓-Lit (⟶*to⇓ p)

⇓to⟶* : ∀ {a v ω ω′} →
  ⟨ a , ω ⟩⇓⟨ v , ω′ ⟩ →
  ⟨ a , ω ⟩⟶*⟨ Lit v , ω′ ⟩
⇓to⟶* ⇓-Lit = E-Done
⇓to⟶* {ω = ω} (⇓-Add {a = a} p p₁ refl) with value-or-can-step {a} {ω}
⇓to⟶* {ω = ω} (⇓-Add {a = a} p p₁ refl) | inj₂ y with ⇓to⟶* p | ⇓to⟶* p₁
⇓to⟶* {ω = ω} (⇓-Add {_} p ⇓-Lit refl) | inj₂ y | E-Step x u | E-Done =
  E-Step (E-Add-1 x) (Add-1* u)
⇓to⟶* {ω = ω} (⇓-Add {_} p p₁ refl) | inj₂ y | E-Step x u | E-Step z w =
  let s = E-Step z w
  in
  E-Step (E-Add-1 x) (Add* u s)

⇓to⟶* {ω = ω} (⇓-Add {a = a} p p₁ refl) | inj₁ Is-Value-Lit with ⇓to⟶* p₁
⇓to⟶* {ω = _} (⇓-Add {.(Lit _)} ⇓-Lit ⇓-Lit refl) | inj₁ Is-Value-Lit | E-Done =
  one-step (E-Add refl)

⇓to⟶* {ω = _} (⇓-Add {.(Lit _)} ⇓-Lit p₁ refl) | inj₁ Is-Value-Lit | E-Step x u =
  E-Step (E-Add-2 x) (Add-2* u)

⇓to⟶* {ω = ω} (⇓-Print {a = a} p) with value-or-can-step {a} {ω}
⇓to⟶* {ω = ω} (⇓-Print {a = a} p) | inj₁ Is-Value-Lit with ⇓to⟶* p
... | E-Done = E-Step E-Print E-Done

⇓to⟶* {ω = ω} (⇓-Print {_} p) | inj₂ (fst , fst₁ , snd) with ⇓to⟶* p
... | E-Step x u rewrite ⟶deterministic-state x snd | ⟶deterministic-expr x snd =
  E-Step (E-Print-1 snd) (Print* u)

⇓to⟶* {ω = ω} (⇓-Seq {a = a} p p₁) with value-or-can-step {a} {ω}
⇓to⟶* {ω = ω} (⇓-Seq {a = a} ⇓-Lit p₁) | inj₁ Is-Value-Lit with ⇓to⟶* p₁
... | E-Done = one-step E-Seq
... | E-Step x u = E-Step (E-Seq-2 x) (Seq-2* u)

⇓to⟶* {ω = ω} (⇓-Seq {_} p p₁) | inj₂ (fst , fst₁ , snd) with ⇓to⟶* p
... | E-Step x u rewrite ⟶deterministic-state x snd | ⟶deterministic-expr x snd =
  E-Step (E-Seq-1 snd) (Seq* u (⇓to⟶* p₁))
-- }
