open import Data.Integer

module Syntax where

data Expr : Set where
  Lit : ℤ → Expr
  Add : Expr → Expr → Expr

  Print : Expr → Expr
  Seq : Expr → Expr → Expr

data Output : Set where
  ∅ : Output                -- Empty output
  _∷_ : ℤ → Output → Output -- Put another item in an existing output
