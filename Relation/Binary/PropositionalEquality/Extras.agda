{-# OPTIONS --universe-polymorphism #-}
-- move this to propeq
module Relation.Binary.PropositionalEquality.Extras where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B → C → D) {a₁ a₂ b₁ b₂ c₁ c₂}
        → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong₃ f refl refl refl = refl

_≡≡_ : ∀ {a} {A : Set a} {i j : A}
         (i≡j₁ : i ≡ j) (i≡j₂ : i ≡ j) → i≡j₁ ≡ i≡j₂
_≡≡_ refl refl = refl

_≟≡_ : ∀ {a} {A : Set a} {i j : A} → Decidable {A = i ≡ j} _≡_
_≟≡_ refl refl = yes refl
