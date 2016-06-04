module NotSoFresh.Repr.Nominal where

open import Agda.Primitive using (lzero)
open import Algebra
open import NotSoFresh.Base
open import NotSoFresh.SetList
open import Data.Unit hiding (_≟_ ; _≤_)
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Data.Sum
open import Data.Maybe hiding (All)
open import Data.Maybe.Extras using (just-injective)
open import Data.Nat as ℕ
open import Data.List hiding (any)
import Data.List.Properties as L
import Data.List.Any as ListAny
import Data.List.All as ListAll
import Data.List.All.Properties as All
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary.PropositionalEquality.Extras
open ListAny using (Any ; any ; there ; here)
open ListAny.Membership-≡
open ListAll using ( [] ; _∷_ )
open PropEq.≡-Reasoning
open import Data.Product
open import Data.Product.Extras
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function
open import Function.Equality using (_⟶_;_⟨$⟩_)
open import Function.Equivalence using (module Equivalent)
open import Function.Injection using (Injection)
import Category.Monad as Cat

module E = Equivalent
open Cat.RawMonad {lzero} Data.Maybe.monad

import Data.Nat.Properties as ℕ

_MajorOf_ : ℕ → List ℕ → Set
x MajorOf xs = ListAll.All (_>_ x) xs

x-maj-xs-x⊔y-maj-xs : ∀ {x y xs} → x MajorOf xs → (x ⊔ y) MajorOf xs
x-maj-xs-x⊔y-maj-xs = ListAll.map (λ m≤n → ≤trans m≤n (ℕ.m≤m⊔n _ _))
  where open DecTotalOrder ℕ.decTotalOrder renaming (trans to ≤trans)

maj⟨xs⟩∉xs : ∀ {x xs} → x MajorOf xs → x ∉ xs
maj⟨xs⟩∉xs x-maj-xs x∈xs = ℕ.1+n≰n (ListAll.lookup x-maj-xs x∈xs)

World   : Set
World   = List ℕ

ø       : World
ø       = []

_↼_ : (α β : World) → Set
_↼_ α β = Σ ℕ (λ a → β ≡ a ⊞ α)

Atom : World → Set
Atom α = Σ ℕ (λ a → a ∈' α)

Injection⟨Atom⟶ℕ⟩ : ∀ {α} → Injection (PropEq.setoid (Atom α)) (PropEq.setoid ℕ)
Injection⟨Atom⟶ℕ⟩ = proj₁-Injection ∈'-uniq

_↼→_ : (α β : World) → Set
-- α ↼→ β = ∃₂ λ a γ → a ∷ γ ++ α ≡ β
α ↼→ β = ∃ λ a → β ≡ a ∷ α × a MajorOf α

nameOf↼ : ∀ {α β} → α ↼ β → Atom β
nameOf↼ {α} (a , β≡a⊞α) = (a , α≡n⊞β→n∈'α α β≡a⊞α)

-- ∈→Atm : ∀ a α → a ∈ α → Atom α
-- ∈→Atm a α a∈α = (α , lnk a (to n∈α⇔α≡n⊞α a∈α))

  -- ⊞-RightInjective : ∀ {a α β} → a ⊞ α ≡ a ⊞ β → α ≡ β
  -- _≟w_ : Decidable {A = World} _≡_

_≟↼_ : ∀ {β α} → Decidable {A = α ↼ β} _≡_
_≟↼_ = ≟Σ' _≟ℕ_ _≡≡_

_≟Atm_ : ∀ {α} → Decidable {A = Atom α} _≡_
_≟Atm_ = ℕ.eq? Injection⟨Atom⟶ℕ⟩

export↼ : ∀ {α β} → α ↼ β → Atom β → Maybe (Atom α)
export↼ (n , β≡n⊞α) (m , m∈'n⊞α) with m ≟ℕ n
... | yes m≡n = nothing
... | no  m≢n = just (m , proof)
  where open Equivalent (n∈'m⊞α⇔n∈'α m≢n)
        proof = to ⟨$⟩ subst (_∈'_ m) β≡n⊞α m∈'n⊞α

-- sadely this is well-typed
-- hopefully this is not in the logical relation
backCast : ∀ {α β} → α ↼ β → Atom α → Atom β
backCast {α} .{a ⊞ α} (a , refl) (b , b∈α) with b ≟ a
backCast {α} (a , refl) (.a , a∈'α)
    | yes refl = (a , n∈'n⊞α α)
... | no b≢a = (b , E.from (n∈'m⊞α⇔n∈'α b≢a) ⟨$⟩ b∈α)

import⊆ : ∀ {α β} → α ⊆ β → Atom α → Atom β
import⊆ α⊆β (n , n∈'α) = (n , via-∈ α⊆β n∈'α)

next↼→  : ∀ {α β γ} → α ↼ β → α ↼→ γ → ∃ λ δ → β ↼→ δ
next↼→ {α} .{y ⊞ α} (y , refl) (x , refl , x-maj-α)
    = (z ∷ β , z , refl , z-maj-β)
  where
    β = y ⊞ α
    z = x ⊔ (1 + y)
    z-maj-β : z MajorOf β
    z-maj-β with memℕ y α
    ... | yes y∈α = x-maj-xs-x⊔y-maj-xs x-maj-α
    ... | no  y∉α = m≤n⊔m (suc y) x ∷ (x-maj-xs-x⊔y-maj-xs x-maj-α)
       where
         open DistributiveLattice ℕ.distributiveLattice
         m≤n⊔m : ∀ m n → m ≤ n ⊔ m
         m≤n⊔m m n rewrite ∧-comm n m = ℕ.m≤m⊔n m n

weaken : ∀ {α β} → α ↼→ β → α ↼ β
weaken {α} (x , refl , x-maj-α)
  = (x , n∉α→n∷α≡n⊞α (maj⟨xs⟩∉xs x-maj-α))

_↼-commute-⊆_ : ∀ {α β γ} → α ↼ γ → α ⊆ β → ∃ λ δ → γ ⊆ δ × β ↼ δ
_↼-commute-⊆_ {α} {β} {γ} (x , γ≡x⊞α) α⊆β
  = (x ⊞ β , (λ {η} → proof γ≡x⊞α {η}) , x , refl)
    where proof : ∀ {γ} → γ ≡ x ⊞ α → γ ⊆ x ⊞ β
          proof refl = α⊆β→x⊞α⊆x⊞β α⊆β

_⊆-commute-↼→_ : ∀ {α β γ} → α ⊆ β → β ↼→ γ → ∃ λ δ → α ↼→ δ × δ ⊆ γ
_⊆-commute-↼→_ α⊆β (x , refl , x-maj-β) = (_ , α↼→δ , δ⊆γ)
  where α↼→δ = (_ , refl , All.anti-mono α⊆β x-maj-β)
        δ⊆γ = λ {η} → α⊆β→x∷α⊆x∷β α⊆β {η}

¬atomø : Atom ø → ⊥
¬atomø (a , a∈'ø) = a∉'[] a∈'ø

dropName : ∀ {α β} (α↼→β : α ↼→ β) → α ⊆ β
dropName (_ , refl , _) = there

recycle : ∀ {α} → Atom α → ∃ λ β → α ↼ β × α ⊆ β
recycle {α} (a , a∈'α) = (α , (a , n∈'α→α≡n⊞α a∈'α) , λ x → x)

α⊆ø→α≡ø : ∀ {α} → α ⊆ ø → α ≡ ø
α⊆ø→α≡ø {[]}          _ = refl
α⊆ø→α≡ø {x ∷ xs} x∷xs⊆ø = ⊥-elim (a∉[] (x∷xs⊆ø (here refl)))

nominal : Base
nominal = record { World    = World
              ; Name       = Atom
              ; ø          = ø
              ; _↼_       = _↼_
              ; _↼→_      = _↼→_
              ; _⊆_        = _⊆_
              ; dropName   = dropName
              ; nameOf↼   = λ {η} → nameOf↼ {η}
              ; weaken     = weaken
              ; _≟Name_    = _≟Atm_
              ; export↼   = export↼
              ; next↼→   = next↼→
              ; import⊆    = import⊆
              ; init↼→    = (0 ∷ [] , 0 , refl , [])
              ; ¬nameø     = ¬atomø
              ; recycle    = recycle
              ; α⊆ø→α≡ø    = α⊆ø→α≡ø
              ; ø-bottom-⊆ = λ()
              ; ⊆-refl     = id
              ; ⊆-trans    = Preorder.trans (⊆-preorder _)
              ; _↼-commute-⊆_ = _↼-commute-⊆_
              ; _⊆-commute-↼→_ = _⊆-commute-↼→_
              }

export↼∘nameOf↼-fails : ∀ {α β} {ℓ : α ↼ β}
                   → export↼ {α = α} ℓ (nameOf↼ {α} ℓ) ≡ nothing
export↼∘nameOf↼-fails {α} .{n ⊞ α} {n , refl} with n ≟ℕ n
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

export↼-injective : ∀ {α β} {a b : Atom β} {ℓ : α ↼ β}
                    → export↼ {α} ℓ a ≡ export↼ ℓ b → a ≡ b
export↼-injective {α} .{n ⊞ α} {a , p} {b , q} {n , refl} eq
 with a ≟ℕ n | b ≟ℕ n | a ≟ℕ b
... | no ¬P  | no ¬Q  | _ = proj₁-injective ∈'-uniq (Σ,-injective₁ (just-injective eq))
... | no  _  | yes _  | _ = ((_ → _)∶ λ()) eq
... | yes _  | no  _  | _ = ((_ → _)∶ λ()) eq
... | yes P  | yes Q  | no  a≢b = ⊥-elim (a≢b (trans P (sym Q)))
... | _      | _      | yes a≡b = proj₁-injective ∈'-uniq a≡b

import⊆-injective : ∀ {α β} {a b : Atom α} {α⊆β : α ⊆ β} →
                     import⊆ α⊆β a ≡ import⊆ α⊆β b → a ≡ b
import⊆-injective {a = a , p} {b , q}
  = proj₁-injective ∈'-uniq ∘ Σ,-injective₁

⊆-witness-irrelevance : ∀ {α β} {a : Atom α} {α⊆β₁ α⊆β₂ : α ⊆ β} →
                          import⊆ α⊆β₁ a ≡ import⊆ α⊆β₂ a
⊆-witness-irrelevance {a = a , p} = proj₁-injective ∈'-uniq refl

export↼∘import⊆≡just : ∀ {α β} {α↼→β : α ↼→ β} (x : Atom α)
                      → export↼ (weaken α↼→β) (import⊆ (dropName α↼→β) x) ≡ just x
export↼∘import⊆≡just {α↼→β = b , refl , b-maj-α} (a , p)
    with a ≟ℕ b
export↼∘import⊆≡just {α↼→β = b , refl , b-maj-α} (.b , p)
    | yes refl = ⊥-elim (maj⟨xs⟩∉xs b-maj-α (∈'-sound p))
... | no  a≢b = cong just (cong (λ p → a , p) (∈'-uniq _ p))

import⊆⟨refl⟩≡id : ∀ {α} (a : Atom α) → import⊆ (λ x → x) a ≡ a
import⊆⟨refl⟩≡id (_ , _) = proj₁-injective ∈'-uniq refl

import⊆-trans≡∘ : ∀ {α β γ} {ℓ₁ : α ⊆ β} {ℓ₂ : β ⊆ γ} (x : Atom α)
                     → import⊆ (ℓ₂ ∘ ℓ₁) x ≡ (import⊆ ℓ₂ ∘ import⊆ ℓ₁) x
import⊆-trans≡∘ (a , p) = proj₁-injective ∈'-uniq refl

↼-commute-⊆-lem :
  ∀ {α β γ} {α↼γ : α ↼ γ} {α⊆β : α ⊆ β} (a : Atom γ) →
  let p = proj₂ (α↼γ ↼-commute-⊆ α⊆β) in
  import⊆ α⊆β <$> export↼ α↼γ a ≡ export↼ (proj₂ p) (import⊆ (proj₁ p) a)
↼-commute-⊆-lem {α↼γ = b , _} (a , _) with a ≟ℕ b
... | yes a≡b = refl
... | no  a≢b = cong just (proj₁-injective ∈'-uniq refl)
