{-# OPTIONS --universe-polymorphism #-}
module Data.Maybe.Extras where

open import Agda.Primitive using (lzero)
open import Data.Maybe
open import Category.Applicative
open import Relation.Binary.PropositionalEquality using (_≡_;refl)
open import Function using (_∶_)

just-injective : ∀ {a} {A : Set a} {x y : A}
                 → (Maybe A ∶ just x) ≡ just y → x ≡ y
just-injective refl = refl

applicative : RawApplicative {lzero} Maybe
applicative = record { pure = just ; _⊛_  = _⊛_ }
  where
    _⊛_ : ∀ {a b}{A : Set a}{B : Set b} → Maybe (A → B) → Maybe A → Maybe B
    just f  ⊛ just x = just (f x)
    _       ⊛ _      = nothing
