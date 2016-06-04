import NotSoFresh.Base
module NotSoFresh.BiDerived (base₁ base₂ : NotSoFresh.Base.Base) where

import Category.Applicative as Cat
import Category.Monad as Cat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Bool
open import Data.Nat using ( ℕ ; suc ; zero ) renaming (_≟_ to _≟ℕ_)
open import Data.Maybe
open import Data.Product
open import Data.Sum using ([_,_]′)
open import Data.Star using (_◅_)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary
import NotSoFresh.Derived

open NotSoFresh.Derived base₁
  using ()
  renaming ( World to World₁
           ; Name to Name₁
           ; SynAbs to SynAbs₁
           ; ø to ø₁
           ; _↼_ to _↼₁_
           ; _⇀_ to _⇀₁_
           ; _★↼_ to _★↼₁_
           ; IndexøTy to IndexøTy₁
           ; indexø★↼ to indexø★↼₁
           ; export↼ to export↼₁
           ; _|×|_ to _|×|₁_
           )

open NotSoFresh.Derived base₂
  using ()
  renaming ( World to World₂
           ; Name to Name₂
           ; SynAbs to SynAbs₂
           ; ø to ø₂
           ; _↼_ to _↼₂_
           ; _⇀_ to _⇀₂_
           ; _↼→_ to _↼→₂_
           ; _★↼_ to _★↼₂_
           ; IndexøTy to IndexøTy₂
           ; indexø★↼ to indexø★↼₂
           ; Import⊆ to Import⊆₂ 
           ; Fresh to Fresh₂
           ; freshø to freshø₂
           ; _|×|_ to _|×|₂_
           ; module FreshPack to FreshPack₂
           ; module StrongPack to StrongPack₂
           )

RelWorld₁₂ = World₁ → World₂ → Set

F₁₂ = (World₁ → Set) × (World₂ → Set)

Name₁₂ : F₁₂
Name₁₂ = (Name₁ , Name₂)

_|×|₁₂_ : ∀ (F G : F₁₂) → F₁₂
-- (F₁ , F₂) |×|₁₂ (G₁ , G₂) = ((F₁ |×|₁ G₁) , (F₂ |×|₂ G₂))
F |×|₁₂ G = (λ α → proj₁ F α × proj₁ G α) , (λ α → proj₂ F α × proj₂ G α)

SynAbs₁₂ : ∀ (F : F₁₂) → F₁₂
SynAbs₁₂ F = (SynAbs₁ (proj₁ F) , SynAbs₂ (proj₂ F)) -- SynAbs₁ ★★★ SynAbs₂

ComposeCommute₁₂ : (_₁↝₁_ : Rel World₁ _) (_₂↝₂_ : Rel World₂ _) (_₁↝₂_ : RelWorld₁₂) → Set
ComposeCommute₁₂ _₁↝₁_ _₂↝₂_ _₁↝₂_
  = ∀ {α β γ}  → α ₁↝₁ β → β ₁↝₂ γ
      → ∃ λ δ  → α ₁↝₂ δ × δ ₂↝₂ γ

Comm₁₂ : (_↝_ : RelWorld₁₂) → Set
Comm₁₂ _↝_ = ComposeCommute₁₂ _⇀₁_ _⇀₂_ _↝_

module αEq (CEnv₁   : World₁ → Set)
           (index₁  : IndexøTy₁ CEnv₁)
           (CEnv₂   : World₂ → Set)
           (index₂  : IndexøTy₂ CEnv₂) where
  αeqEnv : (α : World₁) (β : World₂) → Set
  αeqEnv α β = CEnv₁ α × CEnv₂ β

  αeqTy : (World₁ → Set) → (World₂ → Set) → Set
  αeqTy F₁ F₂ = ∀ {α β} → αeqEnv α β → F₁ α → F₂ β → Bool

  αeqNameR : αeqTy Name₁ Name₂
  αeqNameR (Γ , Δ) x y = ⌊ index₁ Γ x ≟ℕ index₂ Δ y ⌋

module αEqStarEnv where
  open αEq (_★↼₁_ ø₁) indexø★↼₁ (_★↼₂_ ø₂) indexø★↼₂
  extαeqEnv : ∀ {β β' γ γ'} → αeqEnv β γ → β ↼₁ β' → γ ↼₂ γ'
                            → αeqEnv β' γ'
  extαeqEnv (Γ , Δ) x y = (x ◅ Γ , y ◅ Δ)

Fresh₂×Name₁→FName₂ : (Set → Set) → RelWorld₁₂
Fresh₂×Name₁→FName₂ F α β = Fresh₂ β × (Name₁ α → F (Name₂ β))

module WithApplicative {F} (appli : Cat.RawApplicative F) where
  open Cat.RawApplicative appli

  importFun : ∀ {α β γ δ} → β ↼→₂ δ → α ↼₁ γ
                          → (Name₁ α → F (Name₂ β))
                          → (Name₁ γ → F (Name₂ δ))
  importFun β↼→δ α↼γ f bγ
      with export↼₁ α↼γ bγ
  ...    | just aα = importWith β↼→δ <$> f aα
      where open StrongPack₂
  ...    | nothing = pure (nameOf β↼→δ)
      where open StrongPack₂

  Fresh₂×Name₁→FName₂-Comm₁₂ : Comm₁₂ (Fresh₂×Name₁→FName₂ F)
  Fresh₂×Name₁→FName₂-Comm₁₂ x (y , f)
    = (_ , (nextOf y , importFun (strongOf y) x f) , weakOf y)
      where open FreshPack₂

Traverse : (_↝_ : RelWorld₁₂) (M : Set → Set) (F : F₁₂) → Set
-- Traverse _↝_ M (F₁ , F₂) = ∀ {α β} → α ↝ β → F₁ α → M (F₂ β)
Traverse _↝_ M F = ∀ {α β} → α ↝ β → proj₁ F α → M (proj₂ F β)

module Traversable {_↝_ M}
                   (appli : Cat.RawApplicative M)
                   (comm : Comm₁₂ _↝_)
   where
  open Cat.RawApplicative appli

  Tr : F₁₂ → Set
  Tr x = Traverse _↝_ M x

  ×-traverse : ∀ {G H} → Tr G → Tr H → Tr (G |×|₁₂ H)
  ×-traverse traverseG traverseH Γ (x , y) =
    traverseG Γ x ⊗ traverseH Γ y

  traverseAbs : ∀ {G} → Tr G → Tr (SynAbs₁₂ G)
  traverseAbs traverseG Γ (_ , x , t)
      with comm x Γ
  ... | (_ , Γ' , x') = (λ t' → (_ , x' , t')) <$> traverseG Γ' t

Traverse' : F₁₂ → Set₁
Traverse' F = ∀ {_↝_ M}
                (appli : Cat.RawApplicative M)
                (comm : Comm₁₂ _↝_)
                (traverseName : Traverse _↝_ M Name₁₂)
              → Traverse _↝_ M F

Freshen : F₁₂ → Set₁
Freshen F = ∀ {α β M} → Cat.RawApplicative M → Fresh₂ β
                      → (Name₁ α → M (Name₂ β))
                      → proj₁ F α → M (proj₂ F β)

freshen : ∀ {F} → Traverse' F → Freshen F
freshen traverseF appli x Γ
    = traverseF appli Fresh₂×Name₁→FName₂-Comm₁₂ proj₂ (x , Γ)
   where open WithApplicative appli

Close : F₁₂ → Set
Close F = ∀ {α} → proj₁ F α → Maybe (proj₂ F ø₂)

closeGen : ∀ {F} → Freshen F → Close F
closeGen freshenF = freshenF rawIApplicative freshø₂ (const nothing)
  where open Cat.RawMonad Data.Maybe.monad

module Substitution where
  Fresh₂×Name₁→F : (F : World₂ → Set) (α : World₁) (β : World₂) → Set
  Fresh₂×Name₁→F F α β = Fresh₂ β × (Name₁ α → F β)

  -- Subst F G can be read as F → G in HOAS
  Subst : (F : World₂ → Set) (G : F₁₂) → Set
  Subst F G = ∀ {α β} → (Fresh₂×Name₁→F F α β) → (proj₁ G α → proj₂ G β)

  extθ : ∀ {F α β γ δ} → Import⊆₂ F → (varF : ∀ {α} → Name₂ α → F α)
                       → (β ↼→₂ δ) → (α ↼₁ γ)
                       → (Name₁ α → F β) → (Name₁ γ → F δ)
  extθ imp var x y f z with export↼₁ y z
  ... | just z' = imp (⊆Of x) (f z')
    where open StrongPack₂
  ... | nothing = var (nameOf x)
    where open StrongPack₂

  commθ : ∀ {F} → Import⊆₂ F → (varF : ∀ {α} → Name₂ α → F α)
                → Comm₁₂ (Fresh₂×Name₁→F F)
  commθ imp var x (y , f) = (_ , (nextOf y , f') , weakOf y)
    where open FreshPack₂
          f' = maybe (imp (⊆Of y) ∘ f) (var (nameOf y)) ∘ export↼₁ x

  ×-subst : ∀ {F G H} → Subst F G → Subst F H → Subst F (G |×|₁₂ H)
  ×-subst substG substH θ (x , y) = (substG θ x , substH θ y)

  substAbs : ∀ {F G} → Import⊆₂ F → (∀ {α} → Name₂ α → F α)
                     → Subst F G → Subst F (SynAbs₁₂ G)
  substAbs impF varF substFG θ (_ , x , t)
    with commθ impF varF x θ
  ...  | (_ , θ' , x') = (_ , x' , substFG θ' t)
