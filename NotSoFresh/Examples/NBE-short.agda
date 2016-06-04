{-# OPTIONS --no-positivity-check #-}
open import NotSoFresh.Base
module NotSoFresh.Examples.NBE-short (base : Base) where

import       NotSoFresh.Derived
open         NotSoFresh.Derived base
open import  Function
open import  Data.Product
open import  Data.Maybe
open import  Data.Sum

module M (Abs : (World → Set) → World → Set) where
  data T α : Set where
    V    : ∀ (x : Name α) → T α
    ƛ    : ∀ (abs : Abs T α) → T α
    _·_  : ∀ (t u : T α) → T α

open M SynAbs  renaming (T to Term)
open M FunAbs  renaming (T to Sem)

importSem⊆ : ∀ {α β} → α ⊆ β → Sem α → Sem β
importSem⊆ ⊆w (Term.V a)    = Sem.V (import⊆ ⊆w a)
importSem⊆ ⊆w (t Term.· u)  = importSem⊆ ⊆w t Sem.· importSem⊆ ⊆w u
importSem⊆ ⊆w (Term.ƛ f)    = Sem.ƛ (λ ⊆w' v → f (⊆-trans ⊆w ⊆w') v)

module NBE (envPack : ImportableEnvPack) where
  open ImportableEnvPack envPack

  impEnv : ∀ {α β γ} → α ⊆ β → Env (Sem α) α γ → Env (Sem β) β γ
  impEnv ⊆w = importEnv⊆ ⊆w ∘ mapEnv (importSem⊆ ⊆w)

  app : ∀ {α} → Sem α → Sem α → Sem α
  app (Sem.ƛ f)  v = f ⊆-refl v
  app n          v = n Sem.· v

  eval : ∀ {α β} → Env (Sem α) α β → Term β → Sem α
  eval Γ (Sem.ƛ (_ , a , t))  = Sem.ƛ (λ ⊆w v → eval (impEnv ⊆w Γ , a ↦ v) t)
  eval Γ (Sem.V x)            = [ Sem.V , id ]′ (lookupEnv Γ x)
  eval Γ (t Sem.· u)          = eval Γ t ⟨ app ⟩ eval Γ u

  reify : ∀ {α} → Fresh α → Sem α → Term α
  reify g (Sem.V a)    = Term.V a
  reify g (n Sem.· v)  = reify g n Term.· reify g v
  reify g (Sem.ƛ f)    =
      Term.ƛ (_ , weakOf g , reify (nextOf g) (f (⊆Of g) (Sem.V (nameOf g))))
    where open FreshPack

  nf : ∀ {α β} → Fresh α → Env (Sem α) α β → Term β → Term α
  nf g Γ = reify g ∘ eval Γ

  nfC : ∀ {α} → Fresh α → Term α → Term α
  nfC f = nf f emptyEnv

  nfø : Term ø → Term ø
  nfø = nfC freshø

open NBE importableFunEnv

