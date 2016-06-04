import NotSoFresh.Base

module NotSoFresh.Examples.Rec (base : NotSoFresh.Base.Base) where

open import  Coinduction
open import  Data.Nat using (ℕ ; suc ; zero) renaming (_≟_ to _≟ℕ_)
open import  Data.Empty using (⊥-elim)
open import  Data.Product hiding (map)
open import  Data.Maybe
open import  Function
open import  Data.List as L
import       Category.Monad.Partiality as Pa
open         Pa using (_⊥; run_for_steps)
open import  Relation.Nullary
open import  Relation.Nullary.Decidable
open import  Relation.Binary hiding (_⇒_)
open import  Relation.Binary.PropositionalEquality
import       NotSoFresh.Derived
open         NotSoFresh.Derived base
open import  NotSoFresh.Label

infixr 5 _⇒_
data Ty : Set where
  _⇒_  : ∀ (τ σ : Ty) → Ty
  ι ο  : Ty
  ⟨_⟩  : (ρ : LabelAssoc Ty) → Ty

open CEnvPack funCEnv

data Constant : ∀ τ → Set where
  Number  : (n : ℕ) → Constant ι
  suc     : Constant (ι ⇒ ι)
  NatFix  : ∀ τ → Constant (ι ⇒ (τ ⇒ τ) ⇒ (τ ⇒ τ))

data Trm α : Set where
  V    : ∀ (x : Name α) → Trm α
  _·_  : ∀ (t : Trm α) (u : Trm α) → Trm α
  ƛ    : ∀ {β} (x : α ↼ β) (t : Trm β) → Trm α
  Let  : ∀ {β} (x : α ↼ β) (t : Trm α) (u : Trm β) → Trm α
  Cst  : ∀ {τ} (κ : Constant τ) → Trm α
  ⟨_⟩  : ∀ (fs : LabelAssoc (Trm α)) → Trm α
  get  : ∀ (ℓ : Label) → Trm α
  update⟨_⟩ : ∀ (fs : LabelAssoc (Trm α)) → Trm α

ƛ′ : (∀ {α} → Trm α → Trm α) → Trm ø -- generalize me with importTrm⊆
ƛ′ f = ƛ (weakOf x) (f (V (nameOf x)))
  where x = freshø
        open FreshPack

set : ∀ (ℓ : Label) → Trm ø -- generalize me with importTrm⊆
set ℓ = ƛ′ (λ x → update⟨ L.[ ℓ , x ] ⟩)


module CBVBigStepEval where
  open Pa
  open Pa.Workaround

  sequencePa : ∀ {A : Set} → List (A ⊥P) → (List A) ⊥P
  sequencePa []        = now []
  sequencePa (x ∷ xs)  = x >>= λ y → sequencePa xs >>= λ ys → now (y ∷ ys)

  mapPa : ∀ {A : Set} {B} → (A → B ⊥P) → List A → (List B) ⊥P
  mapPa f = sequencePa ∘ L.map f

  data Val : Set where
    ƛ    : ∀ {α β}
             (Γ   : CEnv Val α)
             (x   : α ↼ β) (t : Trm β) → Val
    Cst  : ∀ {τ   : Ty} → Constant τ → Val
    ⟨_⟩  : ∀ (fs  : LabelAssoc Val) → Val
    get  : ∀ (ℓ   : Label) → Val
    update⟨_⟩ : ∀ (fs : LabelAssoc Val) → Val

  diverge : ∀ {A : Set} → A ⊥P
  diverge = later (♯ diverge)

  ℕFix : ∀ {A : Set} → ℕ → (A → A) → (A → A)
  ℕFix zero    _ = id
  ℕFix (suc n) f = f ∘ ℕFix n f

  -- λ f x → f (f (f ... (f x)))
  ℕFixø : ℕ → Val
  ℕFixø n = ƛ Γ (weakOf f)
                  (ƛ (weakOf x) (ℕFix n (_·_ f') (V (nameOf x))))
   where  open FreshPack
          f   : Fresh ø
          f   = freshø
          β   = innerOf f
          x   : Fresh β
          x   = nextOf f
          γ   = innerOf x
          f'  : Trm γ
          f'  = V (import⊆ (⊆Of x) (nameOf f))
          Γ   : CEnv Val ø
          Γ   = nameø-elim

  evalCst : ∀ {τ} → Constant τ → Val → Val ⊥P
  evalCst suc         (Cst (Number n))  = now (Cst (Number (suc n)))
  evalCst (NatFix τ)  (Cst (Number n))  = now (ℕFixø n)
  evalCst (Number _)  _                 = diverge
  evalCst suc         _                 = diverge
  evalCst (NatFix τ)  _                 = diverge

  mutual

   eval : ∀ {α}
           (t : Trm α) (Γ : CEnv Val α) → Val ⊥P
   eval (t · u) Γ = eval u Γ >>= λ v →
                    eval t Γ >>= λ w → app w v
    where
    app : Val → Val → Val ⊥P
    app (ƛ Γ x body)  v       = later (♯ eval body (Γ , x ↦ v))
    app (Cst κ)       v       = evalCst κ v
    app ⟨ _ ⟩         _       = diverge
    app (get ℓ)       ⟨ fs ⟩  = maybe now diverge (select ℓ fs)
    app (get _)       _       = diverge
    app update⟨ fs ⟩  ⟨ gs ⟩  = now ⟨ merge gs fs ⟩
    app update⟨ _ ⟩   _       = diverge

   eval (V x)         Γ  = now (Γ x)
   eval (ƛ x t)       Γ  = now (ƛ Γ x t)
   eval (Let x t u)   Γ  = eval t Γ >>= λ v → eval u (Γ , x ↦ v)
   eval (Cst n)       _  = now (Cst n)
   eval ⟨ fs ⟩        Γ  = evalFlds fs Γ >>= now ∘′ ⟨_⟩
   eval (get ℓ)       _  = now (get ℓ)
   eval update⟨ fs ⟩  Γ  = evalFlds fs Γ >>= now ∘′ update⟨_⟩

   evalFlds : ∀ {α} (fs : LabelAssoc (Trm α)) (Γ : CEnv Val α)
              → (LabelAssoc Val) ⊥P
   evalFlds []              _  =  now []
   evalFlds ((ℓ , t) ∷ fs)  Γ  =  eval t Γ >>= λ v →
                                  evalFlds fs Γ >>= λ vs →
                                  now ((ℓ , v) ∷ vs)

  eval′ : Trm ø → Val ⊥
  eval′ t = ⟦ eval t nameø-elim ⟧P
