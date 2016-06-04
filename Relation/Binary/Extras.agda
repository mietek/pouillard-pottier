{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.Extras where

open import Relation.Binary

-- could this be moved in place of Trans is Relation.Binary.Core
Trans' : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
        REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
Trans' P Q R = ∀ {i j k} (x : P i j) (xs : Q j k) → R i k

