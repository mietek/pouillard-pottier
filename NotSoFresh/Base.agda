module NotSoFresh.Base where

open import Agda.Primitive using (lzero)
import Category.Monad as Cat
open import Data.Empty using (⊥)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe;just;nothing;maybe) renaming (monad to maybeMonad)
open import Data.Product using (∃;_×_;proj₁;proj₂;_,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function using (id;_∘_;_∶_)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_;_≗_)

open Cat.RawMonad {lzero} maybeMonad

record Base : Set₁ where
  field
    World : Set

    Name : ∀ (α : World) → Set

    _↼_ : ∀ (α β : World) → Set

    _↼→_ : ∀ (α β : World) → Set

    _⊆_ : ∀ (α β : World) → Set

    _≟Name_ : ∀ {α} → Decidable {A = Name α} _≡_

    nameOf↼ : ∀ {α β} → α ↼ β → Name β

    weaken : ∀ {α β} → α ↼→ β → α ↼ β

    export↼ : ∀ {α β} → α ↼ β → Name β → Maybe (Name α)

    import⊆ : ∀ {α β} → α ⊆ β → Name α → Name β

    ø : World

    ø-bottom-⊆ : ∀ {α} → ø ⊆ α

    α⊆ø→α≡ø : ∀ {α} → α ⊆ ø → α ≡ ø

    ⊆-refl : ∀ {α} → α ⊆ α

    ⊆-trans : ∀ {α β γ} → α ⊆ β → β ⊆ γ → α ⊆ γ

    dropName : ∀ {α β} → α ↼→ β → α ⊆ β

    next↼→ : ∀ {α β γ} → α ↼ β → α ↼→ γ → ∃ λ δ → β ↼→ δ

    init↼→ : ∃ λ α → ø ↼→ α

    ¬nameø : ¬ (Name ø)

    recycle : ∀ {α} → Name α → ∃ λ β → α ↼ β × α ⊆ β

    _↼-commute-⊆_ : ∀ {α β γ} → α ↼ γ → α ⊆ β → ∃ λ δ → γ ⊆ δ × β ↼ δ

    -- "Fresh" is contravariant
    -- We can export through an inclusion witness a strong link
    _⊆-commute-↼→_ : ∀ {α β γ} → α ⊆ β → β ↼→ γ → ∃ λ δ → α ↼→ δ × δ ⊆ γ

record Laws : Set₁ where
  field
    isBase : Base

  open Base isBase

  field
    export↼∘nameOf↼-fails : ∀ {α β} {ℓ : α ↼ β} → export↼ ℓ (nameOf↼ ℓ) ≡ nothing

    export↼-injective : ∀ {α β} {a b : Name β} {ℓ : α ↼ β}
                        → export↼ ℓ a ≡ export↼ ℓ b → a ≡ b

    nameOf↼→isFresh : ∀ {α β} (ℓ : α ↼→ β) (a : Name α)
                      -- → nameOf↼→ ℓ ≢ import↼→ ℓ a
                      → nameOf↼ (weaken ℓ) ≢ import⊆ (dropName ℓ) a

    import⊆-injective : ∀ {α β} {a b : Name α} {α⊆β : α ⊆ β} →
                       import⊆ α⊆β a ≡ import⊆ α⊆β b → a ≡ b

    ⊆-witness-irrelevance : ∀ {α β} {a : Name α} {α⊆β₁ α⊆β₂ : α ⊆ β} →
                              import⊆ α⊆β₁ a ≡ import⊆ α⊆β₂ a

    export↼∘import⊆-success :
      ∀ {α β} {α↼→β : α ↼→ β}
      → export↼ (weaken α↼→β) ∘ import⊆ (dropName α↼→β) ≗ just

    import⊆∘export↼ :
      ∀ {α β} {α⊆β : α ⊆ β} {α↼β : α ↼ β} {a : Name β}
      → maybe id a (import⊆ α⊆β <$> export↼ α↼β a) ≡ a

    ↼-commute-⊆-lem :
      ∀ {α β γ} {α↼γ : α ↼ γ} {α⊆β : α ⊆ β} (a : Name γ) →
      let p = proj₂ (α↼γ ↼-commute-⊆ α⊆β) in
      import⊆ (proj₁ p) (nameOf↼ α↼γ) ≡ nameOf↼ (proj₂ p)

  open Base isBase public

