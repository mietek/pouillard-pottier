module NotSoFresh.Examples.Term.DataTypes where

open import NotSoFresh.Base
open import Data.Nat using (ℕ)

infixr 5 _⟶_
data Ty : Set where
  _⟶_  : ∀ (τ σ : Ty) → Ty
  ι ο   : Ty

data Constant : Set where
  num     : ℕ → Constant
  suc     : Constant
  -- _`+`_  : Constant
  natFix  : (τ : Ty) → Constant

module Make (base : Base) where
 open Base base
 infixl 7 _·_
 data Tm α : Set where
  V    : ∀ (x : Name α) → Tm α
  _·_  : ∀ (t u : Tm α) → Tm α
  ƛ    : ∀ {β} (x : α ↼ β) (τ : Ty) (t : Tm β) → Tm α
  Let  : ∀ {β} (x : α ↼ β) (t : Tm α) (u : Tm β) → Tm α
  `_   : ∀ (κ : Constant) → Tm α
