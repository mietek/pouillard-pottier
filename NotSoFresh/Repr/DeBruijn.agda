module NotSoFresh.Repr.DeBruijn where

import Algebra.Structures as Alg
open import NotSoFresh.Base
open import Data.Unit hiding (_≤_)
open import Data.Maybe
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
import Data.Fin as F
import Data.Fin.Properties as F
import Data.Nat as ℕ
open DecTotalOrder ℕ.decTotalOrder using () renaming (refl to ≤-refl ; trans to ≤-trans)
open ≡-Reasoning
open ℕ using (ℕ ; _≤_ ; _<_ ; z≤n ; s≤s ; zero ; suc) renaming (_+_ to _+ℕ_ ; _∸_ to _∸ℕ_)
import Data.Nat.Properties as ℕ
open import Function
open import Data.Fin hiding (_≤_ ; _<_)

data _↼_ α : ∀ (β : ℕ) → Set where
  zero : α ↼ suc α

_≤'_ : Rel ℕ _
m ≤' n = Σ ℕ (λ n-m → m +ℕ n-m ≡ n) 

module ℕCS = Alg.IsCommutativeSemiring ℕ.isCommutativeSemiring

m≤n→m+n-m≡n : ∀ {m n} → m ≤ n → m +ℕ (n ∸ℕ m) ≡ n
m≤n→m+n-m≡n z≤n = refl
m≤n→m+n-m≡n (s≤s m≤n) = cong suc (m≤n→m+n-m≡n m≤n)

≤'-sound : _≤'_ ⇒ _≤_
≤'-sound {m} .{m +ℕ n-m} (n-m , refl) = ℕ.m≤m+n m n-m

≤'-complete : _≤_ ⇒ _≤'_
≤'-complete {m} {n} m≤n = (n ∸ℕ m , m≤n→m+n-m≡n m≤n)

nameOf↼ : ∀ {α β} → α ↼ β → Fin β
nameOf↼ zero = zero

export↼ : ∀ {α β} → α ↼ β → Fin β → Maybe (Fin α)
export↼ _   zero    = nothing
export↼ zero (suc n) = just n

α≤'1+α : ∀ {α} → α ≤' suc α
α≤'1+α = (1 , ℕCS.+-comm _ 1)

to≤' : ∀ {α β} → α ↼ β → α ≤' β
to≤' zero = α≤'1+α

recycle : ∀ {α} → Fin α → ∃ λ β → α ↼ β × α ≤' β
recycle _ = (_ , zero , α≤'1+α)

next↼  : ∀ {α β γ} → α ↼ β → α ↼ γ → ∃ λ δ → β ↼ δ
next↼ zero zero = (_ , zero)

_↼-commute-≤_ : ∀ {α β γ} → α ↼ γ → α ≤' β → ∃ λ δ → γ ≤' δ × β ↼ δ
_↼-commute-≤_ zero (n , p) = suc _ , (n , cong suc p) , zero

_≤-commute-↼_ : ∀ {α β γ} → α ≤' β → β ↼ γ → ∃ λ δ → α ↼ δ × δ ≤' γ
_≤-commute-↼_ (n , p) zero = suc _ , zero , n , cong suc p

import≤' : ∀ {α β} → α ≤' β → Fin α → Fin β
import≤' {α} (β-α , refl) n
  rewrite ℕCS.+-comm α β-α
        | sym (cong Fin (cong (λ x → x +ℕ α) (F.to-from β-α)))
  = fromℕ β-α + n

-- unused
-- ↼refl is wrong in De Bruijn here is the proof
¬↼refl : ∀ {α} → ¬ (α ↼ α)
¬↼refl {α} l = ℕ.m≢1+m+n α (begin α ≡⟨ ↼⇒≡ l ⟩
                              suc α ≡⟨ cong suc (sym (proj₂ +-id α)) ⟩
                              suc α +ℕ 0
                            ∎)
   where
      ↼⇒≡ : ∀ {α β} → α ↼ β → β ≡ suc α
      ↼⇒≡ zero = refl
      +-id = Alg.IsCommutativeSemiring.+-identity ℕ.isCommutativeSemiring

-- push to Nat.Properties
n≤0→n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
n≤0→n≡0 {0} z≤n = refl
n≤0→n≡0 {suc n} ()

-- unused
extFinFun : ∀ {m n} → (Fin m → Fin n) → (Fin (suc m) → Fin (suc n))
extFinFun {m} f zero with m
... | suc m-1 = F.inject₁ (f zero)
... | zero    = zero
extFinFun f (suc i) = suc (f i)

-- unused
_↼-commute-→_ : ∀ {α β γ} → (Fin α → Fin β) → β ↼ γ → ∃ λ δ → α ↼ δ × (Fin δ → Fin γ)
_↼-commute-→_ f zero = (_ , zero , extFinFun f)

≤'-trans : Transitive _≤'_
≤'-trans {i} x y = ≤'-complete {i} (≤-trans (≤'-sound x) (≤'-sound y))

deBruijn : Base
deBruijn = record {
    World = ℕ
  ; Name = Fin
  ; ø = 0
  ; _↼→_ = _↼_
  ; _↼_ = _↼_
  ; _⊆_ = _≤'_
  ; nameOf↼ = nameOf↼
  ; _≟Name_ = F._≟_
  ; export↼ = export↼
  ; init↼→ = (1 , zero)
  ; next↼→ = next↼
  ; import⊆ = import≤'
  ; weaken = id
  ; ¬nameø = λ()
  ; _↼-commute-⊆_ = _↼-commute-≤_
  ; _⊆-commute-↼→_ = _≤-commute-↼_
  ; dropName = to≤'
  ; recycle = recycle
  ; α⊆ø→α≡ø = n≤0→n≡0 ∘ ≤'-sound
  ; ø-bottom-⊆ = ≤'-complete z≤n
  ; ⊆-refl = ≤'-complete ≤-refl
  ; ⊆-trans = λ {η} → ≤'-trans {η}
  }
