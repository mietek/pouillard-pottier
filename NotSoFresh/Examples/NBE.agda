{-# OPTIONS --no-positivity-check #-}
open import NotSoFresh.Base
module NotSoFresh.Examples.NBE (base : Base) where

import       NotSoFresh.Derived
open         NotSoFresh.Derived base
open import  Function
open import  Data.Product
open import  Data.Maybe
open import  Data.Sum

data T α : Set where
  V    : Name α → T α
  ƛ    : ∀ {β} → α ↼ β → T β → T α
  _·_  : T α → T α → T α

mutual
  data S α : Set where
    ƛ  : (∀ {β} → α ⊆ β → S β → S β) → S α
    N  : Neu α → S α

  data Neu α : Set where
    V    : Name α → Neu α
    _·_  : Neu α → S α → Neu α

mutual
  importN⊆ : ∀ {α β} → α ⊆ β → Neu α → Neu β
  importN⊆ ⊆w (V a)    = V (import⊆ ⊆w a)
  importN⊆ ⊆w (t · u)  = importN⊆ ⊆w t · importV⊆ ⊆w u

  importV⊆ : ∀ {α β} → α ⊆ β → S α → S β
  importV⊆ ⊆w (ƛ f)  = ƛ (λ ⊆w' v → f (⊆-trans ⊆w ⊆w') v)
  importV⊆ ⊆w (N n)  = N (importN⊆ ⊆w n)

module NBE (envPack : ImportableEnvPack) where
  open ImportableEnvPack envPack

  impEnv : ∀ {α β γ} → α ⊆ β → Env (S α) α γ → Env (S β) β γ
  impEnv ⊆w = importEnv⊆ ⊆w ∘ mapEnv (importV⊆ ⊆w)

  app : ∀ {α} → S α → S α → S α
  app (ƛ f)  v = f ⊆-refl v
  app (N n)  v = N (n · v)

  eval : ∀ {α β} → Env (S α) α β → T β → S α
  eval Γ (ƛ a t)  = ƛ (λ ⊆w v → eval (impEnv ⊆w Γ , a ↦ v) t)
  eval Γ (V x)    = [ N ∘ V , id ]′ (lookupEnv Γ x)
  eval Γ (t · u)  = eval Γ t ⟨ app ⟩ eval Γ u

  mutual
    reify : ∀ {α} → Fresh α → S α → T α
    reify g (N n)  = reifyn g n
    reify g (ƛ f)  =
           ƛ (weakOf g) (reify (nextOf g) (f (⊆Of g) (N (V (nameOf g)))))
      where open FreshPack

    reifyn : ∀ {α} → Fresh α → Neu α → T α
    reifyn g (V a)    = V a
    reifyn g (n · v)  = reifyn g n · reify g v

  nf : ∀ {α β} → Fresh α → Env (S α) α β → T β → T α
  nf g Γ = reify g ∘ eval Γ

  nfC : ∀ {α} → Fresh α → T α → T α
  nfC f = nf f emptyEnv

  nfø : T ø → T ø
  nfø = nfC freshø

open NBE importableFunEnv
