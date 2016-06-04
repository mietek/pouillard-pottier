open import NotSoFresh.Base
module NotSoFresh.Examples.Term (base : Base) where


import NotSoFresh.Derived
open NotSoFresh.Derived base

open import Coinduction
import Category.Functor as Cat
import Category.Applicative as Cat
import Category.Monad as Cat
import Category.Monad.Identity as Id
import Category.Monad.Partiality as Pa
open Pa using (_⊥; run_for_steps)
open import Data.Empty using (⊥-elim)
open import Data.Unit
open import Data.Bool
open import Data.Maybe as Maybe
import Data.Maybe.Extras as Maybe
open import Data.Star hiding (return ; _>>=_)
import Data.List as List
open List
open import Data.Product
import Data.Nat as ℕ
open ℕ renaming (_≟_ to _≟ℕ_)
open import Function
open import Function.Equivalence using (equivalent; _⇔_)
open import Relation.Nullary
open import Relation.Nullary.Decidable renaming (map to mapDec)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans ; module ≡-Reasoning)
open ≡-Reasoning

open import NotSoFresh.Examples.Term.DataTypes as DataTypes public
open DataTypes.Make base public

data C α : (β : World) → Set where
  Hole  : C α α
  _·₁_  : ∀ {β} (c : C α β) (t : Tm α) → C α β
  _·₂_  : ∀ {β} (t : Tm α) (c : C α β) → C α β
  ƛ     : ∀ {β γ} (x : α ↼ β) (τ : Ty) (c : C β γ) → C α γ
  Let₁  : ∀ {β γ} (x : α ↼ β) (c : C α γ) (t : Tm β) → C α γ
  Let₂  : ∀ {β γ} (x : α ↼ β) (t : Tm α) (c : C β γ) → C α γ

mutual
  neu? : ∀ {α} → Tm α → Bool
  neu? (ƛ _ _ _)    = false
  neu? (Let _ _ _)  = false
  neu? (` _)        = true
  neu? (V _)        = true
  neu? (t · u)      = neu? t ∧ nf? u

  nf? : ∀ {α} → Tm α → Bool
  nf? (ƛ _ _ t)  = nf? t
  nf? t          = neu? t

module Contexts where
  plug : ∀ {α β} → C α β → Tm β → Tm α
  plug Hole          t  = t
  plug (c ·₁ t)      u  = plug c u · t
  plug (t ·₂ c)      u  = t · plug c u
  plug (ƛ x τ c)     t  = ƛ x τ (plug c t)
  plug (Let₁ x c t)  u  = Let x (plug c u) t
  plug (Let₂ x t c)  u  = Let x t (plug c u)

  CTm : World → Set
  CTm α = ∃ λ β → C α β × Tm β

  cmap : ∀ {α β} → (∀ {γ} → C α γ → C β γ) → CTm α → CTm β
  cmap f (_ , c , t) = (_ , f c , t)

  hole : ∀ {α} → Tm α → CTm α
  hole t = (_ , Hole , t)

  extFreshC : ∀ {α β} → Fresh α → C α β → Fresh β
  extFreshC g Hole          = g
  extFreshC g (c ·₁ _)      = extFreshC g c
  extFreshC g (_ ·₂ c)      = extFreshC g c
  extFreshC g (ƛ x _ c)     = extFreshC (import↼Fresh x g) c
  extFreshC g (Let₁ _ c _)  = extFreshC g c
  extFreshC g (Let₂ x _ c)  = extFreshC (import↼Fresh x g) c

module CBVBigStepEval where
  open CEnvPack funCEnv
  open Pa -- open Cat.RawMonad Pa.monad
  open Pa.Workaround

  data Val : Set where
    ƛ   : ∀ {α} → (Name α → Val) → SynAbs Tm α → Val
    `_  : Constant → Val

  neverP : {A : Set} → A ⊥P
  neverP = later (♯ neverP)

  ℕFix : ∀ {A : Set} → ℕ → (A → A) → (A → A)
  ℕFix zero    _  = id
  ℕFix (suc n) f  = f ∘ ℕFix n f

  -- λ f x → f (f (f ... (f x)))
  ℕFixø : ℕ → (τ : Ty) → Val
  ℕFixø n τ = ƛ Γ (_ , weakOf f ,
                  (ƛ (weakOf x) τ (ℕFix n (_·_ f') (V (nameOf x)))))
    where open FreshPack
          f : Fresh ø
          f = freshø
          β = innerOf f
          x : Fresh β
          x = nextOf f
          γ = innerOf x
          f' : Tm γ
          f' = V (import⊆ (⊆Of x) (nameOf f))
          Γ : CEnv Val ø
          Γ = nameø-elim

  evalCst : Constant → Val → Val ⊥P
  evalCst suc         (` num n)  = now (` num (suc n))
  evalCst (natFix τ)  (` num n)  = now (ℕFixø n τ)
  evalCst suc         _          = neverP -- ill typed program
  evalCst (natFix _)  _          = neverP -- ill typed program
  evalCst (num _)     _          = neverP -- ill typed program

  eval : ∀ {α} → Tm α → CEnv Val α → Val ⊥P
  eval (t · u) Γ = later (♯ eval u Γ) >>= λ v →
                   later (♯ eval t Γ) >>= λ w → app w v
   where
    app : Val → Val → Val ⊥P
    app (ƛ Δ (_ , x , body))  v = later (♯ eval body (Δ , x ↦ v))
    app (` κ)                 v = evalCst κ v

  eval (V x)        Γ  = now (Γ x)
  eval (ƛ x τ t)    Γ  = now (ƛ Γ (_ , x , t))
  eval (Let x t u)  Γ  = later (♯ eval t Γ) >>= λ v →
                         later (♯ eval u (Γ , x ↦ v))
  eval (` n)        _  = now (` n)

  eval′ : Tm ø → Val ⊥
  eval′ t = ⟦ eval t nameø-elim ⟧P

varImport⊆ : ∀ {β γ} → Name β → β ⊆ γ → Tm γ
varImport⊆ x ⊆w = V (import⊆ ⊆w x)


ƛ′ : ∀ {α}  → Ty
            → (∀ {β} → α ⊆ β → Tm β → FF Tm β)
            → FF Tm α
ƛ′ τ f g = ƛ (weakOf g) τ (f (⊆Of g) (V (nameOf g)) (nextOf g))
    where open FreshPack

ƛø : Ty → (∀ {β} → Tm β → FF Tm β) → Tm ø
ƛø τ f = ƛ′ τ (λ _ → f) freshø

⟶-inj₁  : ∀ {σ τ σ′ τ′} → σ ⟶ τ ≡ σ′ ⟶ τ′ → σ ≡ σ′
⟶-inj₁  refl = refl

⟶-inj₂  : ∀ {σ τ σ′ τ′} → σ ⟶ τ ≡ σ′ ⟶ τ′ → τ ≡ τ′
⟶-inj₂  refl = refl

Number-inj : ∀ {m n} → num m ≡ num n → m ≡ n
Number-inj refl = refl

NatFix-inj : ∀ {σ τ} → natFix σ ≡ natFix τ → σ ≡ τ
NatFix-inj refl = refl

Number-con : ∀ {m n} → m ≡ n ⇔ num m ≡ num n
Number-con = equivalent (cong num) Number-inj

NatFix-con : ∀ {m n} → m ≡ n ⇔ natFix m ≡ natFix n
NatFix-con = equivalent (cong natFix) NatFix-inj

_≟Ty_ : Decidable {A = Ty} _≡_
ι           ≟Ty ι           = yes refl
ι           ≟Ty ο           = no λ()
ι           ≟Ty (_ ⟶ _)    = no λ()
ο           ≟Ty ο           = yes refl
ο           ≟Ty ι           = no λ()
ο           ≟Ty (_  ⟶ _  ) = no λ()
(_  ⟶ _  ) ≟Ty ι           = no λ()
(_  ⟶ _  ) ≟Ty ο           = no λ()
(τ₁ ⟶ τ₁') ≟Ty (τ₂ ⟶ τ₂') with τ₁ ≟Ty τ₂ | τ₁' ≟Ty τ₂'
... | yes p | yes q = yes (cong₂ _⟶_ p q)
... | yes p | no ¬q = no (¬q ∘ ⟶-inj₂)
... | no ¬p | yes q = no (¬p ∘ ⟶-inj₁)
... | no ¬p | no ¬q = no (¬p ∘ ⟶-inj₁)


_≟κ_ : Decidable {A = Constant} _≡_
num m     ≟κ num n     = mapDec Number-con (m ≟ℕ n)
natFix σ  ≟κ natFix τ  = mapDec NatFix-con (σ ≟Ty τ)
suc       ≟κ suc       = yes refl
num _     ≟κ natFix _  = no λ()
num _     ≟κ suc       = no λ()
natFix _  ≟κ num _     = no λ()
natFix _  ≟κ suc       = no λ()
suc       ≟κ natFix _  = no λ()
suc       ≟κ num _     = no λ()

rm : ∀ {α β} → α ↼ β → List (Name β) → List (Name α)
rm x []         = []
rm x (y ∷ ys) with  export↼ x y
...                 |  just y'  = y'  ∷ rm x ys
...                 |  nothing  = rm x ys

fv : ∀ {α} → Tm α → List (Name α)
fv (` _)        = []
fv (V x)        = [ x ]
fv (fct · arg)  = fv fct ++ fv arg
fv (ƛ x _ t)    = rm x (fv t)
fv (Let x t u)  = fv t ++ rm x (fv u)

module αEqTm where
  open αEq _★↼_ index★↼
  open αEqStarEnv

  αeqTmR : αeqTy Tm
  αeqTmR _ (` κ) (` κ')
    = ⌊ κ ≟κ κ' ⌋
  αeqTmR Γ (V x) (V y)
    = αeqNameR Γ x y
  αeqTmR Γ (t · u) (v · w)
    = αeqTmR Γ t v ∧ αeqTmR Γ u w
  αeqTmR Γ (ƛ x τ t) (ƛ y σ u)
    = ⌊ τ ≟Ty σ ⌋  ∧ αeqTmR (extαeqEnv Γ x y) t u
  αeqTmR Γ (Let x t u) (Let y v w)
    = αeqTmR Γ t v ∧ αeqTmR (extαeqEnv Γ x y) u w
  αeqTmR _ _ _
    = false

  αeqTm : ∀ {α} → Tm α → Tm α → Bool
  αeqTm = αeqTmR (ε , ε)

size : ∀ {α} → Tm α → ℕ
size (V _)        = 1
size (t · u)      = 1 + size t + size u
size (ƛ _ _ t)    = 1 + size t
size (Let _ t u)  = 1 + size t + size u
size (` _)        = 1

count : ∀ {α} → Name α → Tm α → ℕ
count {α} x₀ = cnt ε
  where
    cnt : ∀ {β} → α ★↼ β → Tm β → ℕ
    cnt Γ (V x)
     with export★↼ Γ x
    ... | just x'  = if ⌊ x' ≟Name x₀ ⌋ then 1 else 0
    ... | nothing  = 0
    cnt Γ (t · u)      = cnt Γ t + cnt Γ u
    cnt Γ (ƛ x _ t)    = cnt (x ◅ Γ) t
    cnt Γ (Let x t u)  = cnt Γ t + cnt (x ◅ Γ) u
    cnt _ (` _)        = 0

fv' : ∀ {β α} → α ★↼ β → Tm β → List (Name α)
fv' Γ (V x)        = List.fromMaybe (export★↼ Γ x)
fv' Γ (t · u)      = fv' Γ t ++ fv' Γ u
fv' Γ (ƛ x _ t)    = fv' (x ◅ Γ) t
fv' Γ (Let x t u)  = fv' Γ t ++ fv' (x ◅ Γ) u
fv' _ (` _)        = []

fv₂Env : (α β : World) → Set
fv₂Env α β = Name α → List (Name β)

extfv₂ : ∀ {α β γ} → α ↼ γ → fv₂Env α β → fv₂Env γ β
extfv₂ x f = concatMap f ∘ List.fromMaybe ∘ export↼ x

fv₂ : ∀ {α β} → fv₂Env α β → Tm α → List (Name β)
fv₂ Γ (V x)        = Γ x
fv₂ Γ (t · u)      = fv₂ Γ t ++ fv₂ Γ u
fv₂ Γ (ƛ x _ t)    = fv₂ (extfv₂ x Γ) t
fv₂ Γ (Let x t u)  = fv₂ Γ t ++ fv₂ (extfv₂ x Γ) u
fv₂ _ (` _)        = []

member : ∀ {α} → Name α → Tm α → Bool
member {α} x = mem ε
  where
    mem : ∀ {β} → α ★↼ β → Tm β → Bool
    mem Γ (V y)        = ⌊ export★↼ Γ y ≟MaybeName just x ⌋
    mem Γ (t · u)      = mem Γ t ∨ mem Γ u
    mem Γ (ƛ y _ t)    = mem (y ◅ Γ) t
    mem Γ (Let y t u)  = mem Γ t ∨ mem (y ◅ Γ) u
    mem _ (` _)        = false

member' : ∀ {α} → Name α → Tm α → Bool
member' x = mem (λ y → ⌊ x ≟Name y ⌋)
  where
    ext : ∀ {α β} → α ↼ β → (Name α → Bool) → (Name β → Bool)
    ext x Γ y = maybe Γ false (export↼ x y)

    mem : ∀ {α} → (Name α → Bool) → Tm α → Bool
    mem Γ (V y)        = Γ y
    mem Γ (t · u)      = mem Γ t ∨ mem Γ u
    mem Γ (ƛ y _ t)    = mem (ext y Γ) t
    mem Γ (Let y t u)  = mem Γ t ∨ mem (ext y Γ) u
    mem _ (` _)        = false

Ext : (_↝_ : Rel World _) → Set
Ext _↝_ = ∀ {α β γ} → α ↼ β → α ↝ γ → β ↝ γ

Fold : (_↝_ : Rel World _) (F : World → Set) → Set → Set
Fold _↝_ F M = ∀ {α β} → α ↝ β → F α → M

module FoldTm {G _↝_} (_⊕_ : G → G → G)
                       (ε : G)
                       (ext : Ext _↝_)
                       (foldName : Fold _↝_ Name G) where
  foldTm : Fold _↝_ Tm G
  foldTm Γ (V y)        = foldName Γ y
  foldTm Γ (t · u)      = foldTm Γ t ⊕ foldTm Γ u
  foldTm Γ (ƛ y _ t)    = foldTm (ext y Γ) t
  foldTm Γ (Let y t u)  = foldTm Γ t ⊕ foldTm (ext y Γ) u
  foldTm _ (` _)        = ε

module TraverseTm  {M _↝_} (appli : Cat.RawApplicative M)
                   (comm : Comm _↝_)
                   (traverseName : Traverse _↝_ M Name) where
  open Cat.RawApplicative appli

  traverseTm : Traverse _↝_ M Tm
  traverseTm Γ (V x)    = V <$> traverseName Γ x
  traverseTm _ (` x)    = pure (` x)
  traverseTm Γ (t · u)  = _·_ <$> traverseTm Γ t ⊛ traverseTm Γ u
  traverseTm Γ (ƛ x τ t)
      with comm x Γ
  ... | (_ , Γ' , x') = ƛ x' τ <$> traverseTm Γ' t
  traverseTm Γ (Let x t u)
      with comm x Γ
  ... | (_ , Γ' , x')
     = Let x' <$> traverseTm Γ t ⊛ traverseTm Γ' u

traverseTm' : Traverse' Tm
traverseTm' = TraverseTm.traverseTm

freshenTm : Freshen Tm
freshenTm = freshen traverseTm'

impTm : Import⊆ Tm
impTm = import⊆Gen TraverseTm.traverseTm

-- export⊆Tm : Export⊆ Tm
-- export⊆Tm = export⊆Gen freshenTm

export↼Tm : Export↼ Tm
export↼Tm = export↼Gen freshenTm

closeTm : Close Tm
closeTm = closeGen freshenTm

fresheningImport⊆Tm : FresheningImport⊆ Tm
fresheningImport⊆Tm = fresheningImport⊆Gen freshenTm

absToLet : ∀ {α} → Tm α → SynAbs Tm α → Tm α
absToLet t (_ , x , u) = Let x t u

absToƛ : ∀ {α} → Ty → SynAbs Tm α → Tm α
absToƛ τ (_ , x , t) = ƛ x τ t

module TermExamples where

  idT : ∀ {α} → Ty → FF Tm α
  idT τ x = ƛ (weakOf x) τ (V (nameOf x))
    where open FreshPack

  idø : Ty → Tm ø
  idø τ = idT τ freshø

  appT : ∀ {α} (τ σ : Ty) → Fresh α → Tm α
  appT τ σ x
    = ƛ (weakOf x) (τ ⟶ σ)
        (ƛ (weakOf y) τ (V (import⊆ (⊆Of y) (nameOf x)) · V (nameOf y)))
    where open FreshPack
          y = nextOf x

  appø : (τ σ : Ty) → Tm ø
  appø τ σ = appT τ σ freshø

  compT : ∀ {α} (σ τ θ : Ty) → FF Tm α
  compT σ τ θ
    = ƛ′ (τ ⟶ θ) (λ _ fT →
        ƛ′ (σ ⟶ τ) (λ g⊆ gT →
          ƛ′ σ (λ x⊆ xT →
            const (impTm (⊆-trans g⊆ x⊆) fT · (impTm x⊆ gT · xT)))))

  compø : (σ τ θ : Ty) → Tm ø
  compø σ τ θ = compT σ τ θ freshø

open Substitution
substTm : Subst Tm Tm
substTm θ (V x) = proj₂ θ x
substTm θ (t · u)
  = substTm θ t · substTm θ u
substTm θ (ƛ x τ t)
    with commθ impTm V x θ
... | (_ , θ' , x') = ƛ x' τ (substTm θ' t)
substTm θ (Let x t u)
    with commθ impTm V x θ
... | (_ , θ' , x') = Let x' (substTm θ t) (substTm θ' u)
substTm _ (` κ) = ` κ

substPair : ∀ {α} → (Name α × Tm α) → Name α → Tm α
substPair (x , v) y = if ⌊ x ≟Name y ⌋ then v else V y

substPair' : ∀ {α β} → (α ↼ β × Tm α) → Name β → Tm α
substPair' (x , v) y with export↼ x y
... | just y' = V y'
... | nothing = v

β-red : ∀ {α} (g : Fresh α) (afct : SynAbs Tm α) (arg : Tm α) → Tm α
β-red g (_ , x , fct) arg = substTm (g , substPair' (x , arg)) fct

beta-red : ∀ {α β} {x : α ↼ β} {τ} {fct : Tm β} {arg : Tm α} {t : Tm α}
           → Fresh α
           → t ≡ ƛ x τ fct · arg
           → Tm α
beta-red {x = x} {_} {fct} {arg} g refl = β-red g (_ , x , fct) arg

open Contexts
module Reducer (split  : ∀ {α} → Tm α → CTm α)
               (val?   : ∀ {α} → Tm α → Bool)
               (reduce : ∀ {α} → Fresh α → Tm α → Tm α) where

  open Cat.RawMonad Pa.monad

  reduce★ : ∀ {α} → Fresh α → Tm α → (Tm α) ⊥
  reduce★ g t with val? t
  ... | true = return t
  ... | false = Pa.later (♯ r)
      where st = proj₂ (split t)
            c  = proj₁ st
            u  = proj₂ st
            r  = reduce★ g (plug c (reduce (extFreshC g c) u))

  module Check (n : ℕ) where
    infix 0 _↝★_
    _↝★_ : Tm ø → Tm ø → Set
    t ↝★ u = run (reduce★ freshø t) for n steps ≡ Pa.now u

module SmallStep where
  module Strong where
    -- one strategy among others
    split : ∀ {α} → Tm α → CTm α
    split (V x)        = hole (V x)
    split (t · u)      = if nf? t  then cmap (_·₂_ t) (split u)
                                   else cmap (flip _·₁_ u) (split t)
    split (ƛ x τ t)    = cmap (ƛ x τ) (split t)
    split (Let x t u)  = if nf? t  then cmap (Let₂ x t) (split u)
                                   else cmap (λ y → Let₁ x y u) (split t)
    split (` κ)        = hole (` κ)

  module WeakCBV where
    val? : ∀ {α} → Tm α → Bool
    val? (ƛ _ _ _)  = true
    val? (` _)      = true
    val? _          = false

    split : ∀ {α} → Tm α → CTm α
    split t0 with t0
    ... | t · u      =  if val? u then
                          if val? t then hole t0
                          else cmap (flip _·₁_ u) (split t)
                        else cmap (_·₂_ t) (split u)
    ... | Let x t u  =  if val? t then hole t0
                        else cmap (λ y → Let₁ x y u) (split t)
    ... | _          =  hole t0

    ℕFix : ∀ {A : Set} → ℕ → (A → A) → (A → A)
    ℕFix zero     _  = id
    ℕFix (suc n)  f  = f ∘ ℕFix n f

    open TermExamples using (idø; compø)

    ℕFixø : ℕ → Ty → Tm ø
    ℕFixø n τ = ƛø (τ ⟶ τ) (λ f →
                 ƛ′ τ (λ ⊆w x →
                   const (ℕFix n (_·_ (impTm ⊆w f)) x)))

    red : ∀ {α} → Fresh α → Tm α → Tm α
    red g (ƛ x τ fct · arg)           = β-red g (_ , x , fct) arg
    red g (Let x t u)                 = β-red g (_ , x , u)   t
    red g (` (natFix τ) · ` (num n))  = impTm ø-bottom-⊆ (ℕFixø n τ)
    red g (` suc · ` (num n))         = ` (num (suc n))
    red g t                           = t

    open Reducer split val? red public

module Typing (cenv : CEnvPack) where
  open Cat.RawMonad Maybe.monad
  open CEnvPack cenv

  typing-constants : Constant → Ty
  typing-constants (num _)     = ι
  typing-constants suc         = ι ⟶ ι
  typing-constants (natFix τ)  = ι ⟶ (τ ⟶ τ) ⟶ (τ ⟶ τ)

  typing : ∀ {α} → CEnv Ty α → Tm α → Maybe Ty
  typing Γ (V v) = just (lookupCEnv Γ v)
  typing Γ (ƛ x τ t) = _⟶_ τ <$> typing (Γ , x ↦ τ) t
  typing Γ (Let x t u) = typing Γ t >>= λ τ → typing (Γ , x ↦ τ) u
  typing _ (` κ) = just (typing-constants κ)
  typing Γ (t · u) with typing Γ t | typing Γ u
  ... | just (from ⟶ to) | just σ
            = if ⌊ from ≟Ty σ ⌋ then just to else nothing
  ... | _ | _ = nothing
