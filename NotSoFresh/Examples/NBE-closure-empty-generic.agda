{-# OPTIONS --no-positivity-check --no-termination-check #-}
open import NotSoFresh.Base
module NotSoFresh.Examples.NBE-closure-empty-generic (base : Base) where

import NotSoFresh.Derived as D
open D base
open import Function
open import Data.Product
open import Data.Empty
open import Data.Star
open import Data.Maybe
open import Data.Sum

data T α : Set where
  V    : ∀ (x : Name α) → T α
  ƛ    : ∀ {β} (x : α ↼ β) (t : T β) → T α
  _·_  : ∀ (t u : T α) → T α


module NBE (envPack : CEnvPack) where
  open CEnvPack envPack
  -- In Case Of Emergency
  -- CEnv = CEnvPack.CEnv envPack
  -- ...

  mutual
    data S α : Set where
      ƛ  : ∀ {β} (Γ : CEnv (S α) β) (abs : Abs T β) → S α
      N  : ∀ (n : Neu α) → S α

    data Neu α : Set where
      V    : ∀ (x : Name α) → Neu α
      _·_  : ∀ (t : Neu α) (u : S α) → Neu α

  mutual
    importN⊆ : ∀ {α β} → α ⊆ β → Neu α → Neu β
    importN⊆ ⊆w (V a)    = V (import⊆ ⊆w a)
    importN⊆ ⊆w (t · u)  = importN⊆ ⊆w t · importV⊆ ⊆w u

    importV⊆ : ∀ {α β} → α ⊆ β → S α → S β
    importV⊆ ⊆w (ƛ Δ t)  = ƛ (mapCEnv (importV⊆ ⊆w) Δ) t
    importV⊆ ⊆w (N n)    = N (importN⊆ ⊆w n)

  mutual
    eval : ∀ {α β} → CEnv (S α) β → T β → S α
    eval Γ (ƛ a t)  = ƛ Γ (_ , a , t)
    eval Γ (V x)    = lookupCEnv Γ x
    eval Γ (t · u)  = eval Γ t ⟨ app ⟩ eval Γ u

    app : ∀ {α} → S α → S α → S α
    app (ƛ Δ (γ , a , t))  v = eval (Δ , a ↦ v) t
    app (N n)              v = N (n · v)

  mutual
    quote : ∀ {α} → Fresh α → S α → T α
    quote a (ƛ {β} Δ (δ , b , t))
       = ƛ (weakOf a) (quote (nextOf a) (eval Δ' t))
         where  open FreshPack
                Δ' = mapCEnv (importV⊆ (⊆Of a)) Δ , b ↦ N (V (nameOf a))
    quote g (N n)
       = quoten g n

    quoten : ∀ {α} → Fresh α → Neu α → T α
    quoten g (V y)    = V y
    quoten g (n · v)  = quoten g n · quote g v

  nf : ∀ {α} → Fresh α → CEnv (S α) α → T α → T α
  nf g Γ = quote g ∘ eval Γ

open NBE (closeEnv funEnv) renaming (nf to nfFunEnv)

nfFunEnv' : ∀ {α} → Fresh α → T α → T α
nfFunEnv' g = nfFunEnv g (inj₂ ∘ N ∘ V)

open NBE (closeEnv starEnv) renaming (nf to nfStarEnv)

nfStarEnvø : T ø  → T ø
nfStarEnvø = nfStarEnv freshø ε
