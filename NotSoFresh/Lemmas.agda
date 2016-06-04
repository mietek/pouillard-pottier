open import NotSoFresh.Base
module NotSoFresh.Lemmas (laws : Laws) where

open Laws laws

open import Data.Maybe using (Maybe;just;nothing)
open import Data.Product using (∃;_×_;_,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_;_∋_)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_;inspect;[_];refl;sym;trans;cong;subst;_≗_)

nameOf↼-≡→failed-export↼ :
              ∀ {α β} {ℓ : α ↼ β} {a : Name β}
              → nameOf↼ ℓ ≡ a → export↼ {α = α} ℓ a ≡ nothing
nameOf↼-≡→failed-export↼ {ℓ = ℓ} .{nameOf↼ ℓ} refl = export↼∘nameOf↼-fails

failed-export↼→nameOf↼-≡ : ∀ {α β} {ℓ : α ↼ β} {a : Name β}
                       → export↼ ℓ a ≡ nothing → nameOf↼ ℓ ≡ a
failed-export↼→nameOf↼-≡
  = export↼-injective ∘ trans export↼∘nameOf↼-fails ∘ sym

export↼' : ∀ {α β} (ℓ : α ↼ β) (a : Name β) → nameOf↼ {α} ℓ ≡ a ⊎ (nameOf↼ {α} ℓ ≢ a × Name α)
export↼' {α} ℓ a with export↼ ℓ a | inspect (export↼ ℓ) a
... | nothing | [ eq ] = inj₁ (failed-export↼→nameOf↼-≡ eq)
... | just a' | [ eq ] with nameOf↼ ℓ ≟Name a
...      | yes nameOf↼ℓ≡a = ((_ → _) ∋ λ())
                          (trans (sym eq) (nameOf↼-≡→failed-export↼ nameOf↼ℓ≡a))
...      | no  nameOf↼ℓ≢a = inj₂ (nameOf↼ℓ≢a , a')


safeExport↼ : ∀ {α β} (ℓ : α ↼ β) (a : Name β)
              → nameOf↼ {α} ℓ ≢ a → Name α
safeExport↼ ℓ a ℓ≢a with export↼' ℓ a
... | inj₁ ℓ≡a = ⊥-elim (ℓ≢a ℓ≡a)
... | inj₂ (_ , b) = b
