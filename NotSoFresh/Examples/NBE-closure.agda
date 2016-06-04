{-# OPTIONS --no-positivity-check --no-termination-check #-}
open import NotSoFresh.Base
module NotSoFresh.Examples.NBE-closure (base : Base) where

import       NotSoFresh.Derived
open         NotSoFresh.Derived base
open import  Function
open import  Data.Product
open import  Data.Empty
open import  Data.Maybe
open import  Data.Sum

data T α : Set where
  V    : ∀ (x : Name α) → T α
  ƛ    : ∀ {β} (x : α ↼ β) (t : T β) → T α
  _·_  : ∀ (t u : T α) → T α

module NBE (envPack : ImportableEnvPack) where
  open ImportableEnvPack envPack

  mutual
    data S α : Set where
      ƛ  : ∀ {β} (Γ : Env (S α) α β) (abs : SynAbs T β) → S α
      N  : Neu α → S α

    data Neu α : Set where
      V    : ∀ (x : Name α) → Neu α
      _·_  : ∀ (t : Neu α) (u : S α) → Neu α

  mutual
    importN⊆ : ∀ {α β} → α ⊆ β → Neu α → Neu β
    importN⊆ ⊆w (V a)    = V (import⊆ ⊆w a)
    importN⊆ ⊆w (t · u)  = importN⊆ ⊆w t · importV⊆ ⊆w u

    importV⊆ : ∀ {α β} → α ⊆ β → S α → S β
    importV⊆ ⊆w (ƛ a t)  = ƛ (importEnv⊆ ⊆w (mapEnv (importV⊆ ⊆w) a)) t
    importV⊆ ⊆w (N n)    = N (importN⊆ ⊆w n)

  mutual
    app : ∀ {α} → S α → S α → S α
    app (ƛ Δ (γ , a , t))  v = eval (Δ , a ↦ v) t
    app (N n)              v = N (n · v)

    eval : ∀ {α β} → Env (S α) α β → T β → S α
    eval Γ (ƛ a t)  = ƛ Γ (_ , a , t)
    eval Γ (V x)    = [ N ∘ V , id ]′ (lookupEnv Γ x)
    eval Γ (t · u)  = eval Γ t ⟨ app ⟩ eval Γ u

  mutual
    reify : ∀ {α} → Fresh α → S α → T α
    reify g (ƛ {β} Δ (δ , b , t))
      = ƛ (weakOf g) (reify (nextOf g) (eval (Δ' , b ↦ N (V a)) t))
      where open FreshPack
            a   = nameOf g
            ⊆w  = ⊆Of g
            Δ'  = importEnv⊆ ⊆w (mapEnv (importV⊆ ⊆w) Δ)
    reify g (N n)
      = reifyn g n

    reifyn : ∀ {α} → Fresh α → Neu α → T α
    reifyn g (V y)    = V y
    reifyn g (n · v)  = reifyn g n · reify g v

  nf : ∀ {α β} → Fresh α → Env (S α) α β → T β → T α
  nf g Γ = reify g ∘ eval Γ

  nfC : ∀ {α} → Fresh α → T α → T α
  nfC f = nf f emptyEnv

  nfø : T ø → T ø
  nfø = nfC freshø

open NBE importableFunEnv renaming (nf to nfFunEnv)

open NBE (endOpenEnv starEnv) renaming (nf to nfOEStarEnv)
