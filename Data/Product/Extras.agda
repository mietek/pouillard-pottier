-- move this to product
{-# OPTIONS --universe-polymorphism #-}
module Data.Product.Extras where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary
open import Function
open import Function.Injection using (Injection; module Injection)

Σ,-injective₂ : ∀ {A : Set} {P : A → Set} {x : A} {y z : P x} → (Σ A P ∋ (x , y)) ≡ (x , z) → y ≡ z
Σ,-injective₂ refl = refl

Σ,-injective₁ : ∀ {A : Set} {P : A → Set} {x₁ x₂ : A} {y₁ : P x₁} {y₂ : P x₂} → (Σ A P ∋ (x₁ , y₁)) ≡ (x₂ , y₂) → x₁ ≡ x₂
Σ,-injective₁ refl = refl

proj₁-injective : ∀ {a b} {A : Set a} {B : A → Set b} {x y : Σ A B}
                    (B-uniq : ∀ {z} (p₁ p₂ : B z) → p₁ ≡ p₂)
                  → proj₁ x ≡ proj₁ y → x ≡ y
proj₁-injective {x = (a , p₁)} {y = (.a , p₂)} B-uniq refl
  = cong (λ p → (a , p)) (B-uniq p₁ p₂)

≟Σ : ∀ {A : Set} {P : A → Set}
       (decA : Decidable {A = A} _≡_)
       (decP : ∀ x → Decidable {A = P x} _≡_)
     → Decidable {A = Σ A P} _≡_
≟Σ decA decP (w₁ , p₁) (w₂ , p₂) with decA w₁ w₂
≟Σ decA decP (w  , p₁) (.w , p₂) | yes refl with decP w p₁ p₂ 
≟Σ decA decP (w  , p)  (.w , .p) | yes refl | yes refl = yes refl
≟Σ decA decP (w  , p₁) (.w , p₂) | yes refl | no  p≢
    = no (p≢ ∘ Σ,-injective₂)
≟Σ decA decP (w₁ , p₁) (w₂ , p₂) | no w≢ = no (w≢ ∘ cong proj₁)

≟Σ' : ∀ {A : Set} {P : A → Set}
       (decA : Decidable {A = A} _≡_)
       (uniqP : ∀ {x} (p q : P x) → p ≡ q)
     → Decidable {A = Σ A P} _≡_
≟Σ' decA uniqP (w₁ , p₁) (w₂ , p₂) with decA w₁ w₂
≟Σ' decA uniqP (w  , p₁) (.w , p₂) | yes refl
  = yes (cong (λ p → (w , p)) (uniqP p₁ p₂))
≟Σ' decA uniqP (w₁ , p₁) (w₂ , p₂) | no w≢ = no (w≢ ∘ cong proj₁)

proj₁-Injection : ∀ {a b} {A : Set a} {B : A →  Set b}
                  → (∀ {x} (p₁ p₂ : B x) → p₁ ≡ p₂)
                  → Injection (setoid (Σ A B))
                              (setoid A)
proj₁-Injection {B = B} B-uniq
     = record { to        = →-to-⟶ (proj₁ {B = B})
              ; injective = proj₁-injective B-uniq
              }
