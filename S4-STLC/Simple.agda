{-# OPTIONS --cubical #-}

{-# OPTIONS --cumulativity #-}

-- open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import cubical-prelude hiding (_×_)

module Simple
  (ϕ : Set)
  (ϕ-prop : ∀ {a b : ϕ} → a ≡ b)
  where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Agda.Primitive
open import Level
open import Calc ϕ ϕ-prop

Simple : ∀ {ℓ} → LC {lsuc ℓ}
Simple {ℓ} =
  record
    { Type = Set ℓ
    ; El = λ σ → σ
    ; _:→_ = λ σ τ → (σ → τ)
    ; lam = λ u → u
    ; _·_ = λ u v → u v
    ; arrβ = refl
    ; arrη = refl
    ; _⊗_ = λ u v → _×_ {ℓ} {ℓ} u v
    ; pair = λ u v → u , v
    ; fst = λ { (u , v) → u }
    ; snd = λ { (u , v) → v }
    ; prodβ1 = refl
    ; prodβ2 = refl
    ; prodη = refl
    ; bool = _⊎_ {ℓ} {ℓ} ⊤ ⊤
    ; true = inj₁ tt
    ; false = inj₂ tt
    ; ite = λ { (inj₁ tt) t f → t ; (inj₂ tt) t f → f }
    ; boolβ1 = refl
    ; boolβ2 = refl
    ; boolη = λ { {x} {y} → funext λ { (inj₁ tt) → refl ; (inj₂ tt) → refl } }
    }

-- open LC


