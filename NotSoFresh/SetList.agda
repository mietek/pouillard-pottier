module NotSoFresh.SetList where

import Algebra as Alg
import Algebra.Structures as Alg
open import NotSoFresh.Base
open import Data.Empty
open import Data.Nat as ℕ
import      Data.Nat.Properties as ℕ
open import Data.List hiding (any)
open import Data.List.Any as Any
open import Relation.Binary.PropositionalEquality
open Any.Membership-≡
open ≡-Reasoning
open import Data.Product
open import Function using (_∘_;_∋_)
open import Function.Equivalence using (_⇔_;equivalence;id;module Equivalence)
open import Function.Equality using (_⟨$⟩_) renaming (_∘_ to _∘FE_)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable

_≟ℕ_ : Decidable {A = ℕ} _≡_
_≟ℕ_ = ℕ._≟_

memℕ : ∀ (x : ℕ) (xs : List ℕ) → Dec (x ∈ xs)
memℕ x xs = any (_≟ℕ_ x) xs

infixr 5 _⊞_
_⊞_ : ℕ → List ℕ → List ℕ
x ⊞ xs with memℕ x xs
... | yes x∈xs = xs
... | no  x∉xs = x ∷ xs

n∈n⊞α : ∀ {n} α → n ∈ n ⊞ α
n∈n⊞α {n} α with memℕ n α
... | yes n∈α = n∈α
... | no  n∉α = here refl

α≡n⊞β→n∈α : ∀ {n α} β → α ≡ n ⊞ β → n ∈ α
α≡n⊞β→n∈α β refl = n∈n⊞α β

n∈α→α≡n⊞α : ∀ {α n} → n ∈ α → α ≡ n ⊞ α
n∈α→α≡n⊞α {α} {n} n∈α with memℕ n α
... | yes _   = refl
... | no  n∉α = ⊥-elim (n∉α n∈α)

n∉α→n∷α≡n⊞α : ∀ {α n} → n ∉ α → n ∷ α ≡ n ⊞ α
n∉α→n∷α≡n⊞α {α} {n} n∉α with memℕ n α
... | yes n∈α = ⊥-elim (n∉α n∈α)
... | no   _  = refl

n∈m⊞α⇔n∈α : ∀ {m n α} → n ≢ m → n ∈ m ⊞ α ⇔ n ∈ α
n∈m⊞α⇔n∈α {m} {n} {α} n≢m with memℕ m α
... | yes m∈α = id
... | no  m∉α = equivalence (Any.tail n≢m) there

y∈x⊞α⇔y∈x∷α : ∀ {x y α} → (y ∈ x ⊞ α) ⇔ (y ∈ x ∷ α)
y∈x⊞α⇔y∈x∷α {x} {y} {α} with memℕ x α
... | yes x∈α = equivalence there rl
  where
    rl : ∀ {y} → y ∈ x ∷ α → y ∈ α
    rl (here refl) = x∈α
    rl (there y∈α) = y∈α
... | no  _ = id

α⊆β→x∷α⊆x∷β : ∀ {A : Set} {x : A} {α β : List A} → α ⊆ β → x ∷ α ⊆ x ∷ β
α⊆β→x∷α⊆x∷β α⊆β (here refl) = here refl
α⊆β→x∷α⊆x∷β α⊆β (there y∈α) = there (α⊆β y∈α)

α⊆β→x⊞α⊆x⊞β : ∀ {x α β} → α ⊆ β → x ⊞ α ⊆ x ⊞ β
α⊆β→x⊞α⊆x⊞β α⊆β η =
  from y∈x⊞α⇔y∈x∷α ⟨$⟩ α⊆β→x∷α⊆x∷β α⊆β (to y∈x⊞α⇔y∈x∷α ⟨$⟩ η)
  where open Equivalence

a∉[] : ∀ {A : Set} {a : A} → a ∉ []
a∉[] ()

[]≢a⊞α : ∀ a α → [] ≢ a ⊞ α
[]≢a⊞α a α []≡a⊞α with memℕ a α
[]≢a⊞α _ .[] refl | yes a∈[] = a∉[] a∈[]
[]≢a⊞α _ _ ()   | no _

suc-inj : ∀ {n m : ℕ} → suc n ≡ suc m → n ≡ m
suc-inj refl = refl

data _≢ℕ_ : ℕ → ℕ → Set where
  z≢s : ∀ {n} → zero ≢ℕ suc n
  s≢z : ∀ {n} → suc n ≢ℕ zero
  s≢s : ∀ {m n} → m ≢ℕ n → suc m ≢ℕ suc n

≢ℕ-sound : ∀ {m n} → m ≢ℕ n → m ≢ n
≢ℕ-sound z≢s = λ()
≢ℕ-sound s≢z = λ()
≢ℕ-sound (s≢s y) = ≢ℕ-sound y ∘ suc-inj

≢ℕ-complete : ∀ {m n} → m ≢ n → m ≢ℕ n
≢ℕ-complete {zero} {zero} p   = ⊥-elim (p refl)
≢ℕ-complete {zero} {suc n} p  = z≢s
≢ℕ-complete {suc m} {zero} p  = s≢z
≢ℕ-complete {suc m} {suc n} p = s≢s (≢ℕ-complete (p ∘ cong suc))

≢ℕ-uniq : ∀ {m n} (p q : m ≢ℕ n) → p ≡ q
≢ℕ-uniq z≢s z≢s = refl
≢ℕ-uniq s≢z s≢z = refl
≢ℕ-uniq (s≢s p) (s≢s q) rewrite ≢ℕ-uniq p q = refl

infix 4 _∈'_

data _∈'_ : ℕ → List ℕ → Set where
  here : ∀ {x xs} → x ∈' x ∷ xs
  there : ∀ {x y xs} (x≢y : x ≢ℕ y) (x∈'xs : x ∈' xs) → x ∈' y ∷ xs

∈'-sound : ∀ {x xs} → x ∈' xs → x ∈ xs
∈'-sound here = here refl
∈'-sound (there x≢y x∈'xs) = there (∈'-sound x∈'xs)

∈'-complete : ∀ {x xs} → x ∈ xs → x ∈' xs
∈'-complete (here refl) = here
∈'-complete {x} {y ∷ xs}  (there pxs) with x ≟ℕ y
∈'-complete {x} {.x ∷ xs} (there pxs)
    | yes refl = here
... | no  x≢ℕy = there (≢ℕ-complete x≢ℕy) (∈'-complete pxs)

via-∈ : ∀ {x xs y ys} → (x ∈ xs → y ∈ ys) → x ∈' xs → y ∈' ys
via-∈ f = ∈'-complete ∘ f ∘ ∈'-sound

-- not used
there∈'-inj₁ : ∀ {x y xs} {x≢y x≢y' : x ≢ℕ y} {px px' : x ∈' xs}
               → (x ∈' y ∷ xs ∋ there x≢y px) ≡ there x≢y' px' → x≢y ≡ x≢y'
there∈'-inj₁ refl = refl

-- not used
there∈'-inj₂ : ∀ {x y xs} {x≢y x≢y' : x ≢ℕ y} {px px' : x ∈' xs}
               → (x ∈' y ∷ xs ∋ there x≢y px) ≡ there x≢y' px' → px ≡ px'
there∈'-inj₂ refl = refl

∈'-uniq : ∀ {a α} (p q : a ∈' α) → p ≡ q
∈'-uniq here here = refl
∈'-uniq here (there x≢y _) = ⊥-elim (≢ℕ-sound x≢y refl)
∈'-uniq (there x≢y _) here = ⊥-elim (≢ℕ-sound x≢y refl)
∈'-uniq (there x≢y pxs) (there x≢y' pxs') =
  cong₂ there (≢ℕ-uniq x≢y x≢y') (∈'-uniq pxs pxs')

n∈'n⊞α : ∀ {n} α → n ∈' n ⊞ α
n∈'n⊞α {n} α = ∈'-complete (n∈n⊞α {n} α)

α≡n⊞β→n∈'α : ∀ {n α} β → α ≡ n ⊞ β → n ∈' α
α≡n⊞β→n∈'α β refl = n∈'n⊞α β

n∈'α→α≡n⊞α : ∀ {α n} → n ∈' α → α ≡ n ⊞ α
n∈'α→α≡n⊞α {α} {n} n∈'α = n∈α→α≡n⊞α (∈'-sound n∈'α)

n∈'m⊞α⇔n∈'α : ∀ {m n α} → n ≢ m → n ∈' m ⊞ α ⇔ n ∈' α
n∈'m⊞α⇔n∈'α {m} {n} {α} n≢m with memℕ m α
... | yes m∈α = id
... | no  m∉α = equivalence (via-∈ (Any.tail n≢m)) (there (≢ℕ-complete n≢m))

y∈'x⊞α⇔y∈'x∷α : ∀ {x y α} → (y ∈' x ⊞ α) ⇔ (y ∈' x ∷ α)
y∈'x⊞α⇔y∈'x∷α {x} {y} {α} with memℕ x α
... | yes x∈α = equivalence (via-∈ there) rl
  where
    rl : ∀ {y} → y ∈' x ∷ α → y ∈' α
    rl here = ∈'-complete x∈α
    rl (there _ y∈'α) = y∈'α
... | no  _ = id

a∉'[] : ∀ {n : ℕ} → ¬ (n ∈' [])
a∉'[] ()

import Data.List.Properties as List

len-disc : ∀ {A : Set} {xs ys : List A} → length xs ≢ length ys → xs ≢ ys
len-disc {A} {[]} {[]} ineq eq = ineq refl
len-disc {A} {[]} {x ∷ xs} ineq ()
len-disc {A} {x ∷ xs} {[]} ineq ()
len-disc {A} {x ∷ xs} {x' ∷ xs'} ineq eq
   = len-disc (ineq ∘ cong suc)
              (proj₂ (List.∷-injective eq))

xs≢x∷xs : ∀ {A : Set} {x : A} {xs : List A} → xs ≢ x ∷ xs
xs≢x∷xs {A} {x} {xs} = len-disc helper
  where
    open Alg.CommutativeSemiring ℕ.commutativeSemiring using (+-identity)
    helper : ∀ {n} → n ≢ suc n
    helper {n} eq = ℕ.m≢1+m+n n
      (begin n     ≡⟨ eq ⟩
             suc n ≡⟨ cong suc ( sym ((proj₂ +-identity) n)) ⟩
             suc (n + 0)
           ∎)

a⊞α≡b∷α→a≡b : ∀ {a b α} → a ⊞ α ≡ b ∷ α → a ≡ b 
a⊞α≡b∷α→a≡b {a} {b} {α} eq with memℕ a α
... | yes a∈α = ⊥-elim (xs≢x∷xs eq)
... | no  a∉α = proj₁ (List.∷-injective eq)
