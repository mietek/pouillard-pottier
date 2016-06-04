open import NotSoFresh.Base
module NotSoFresh.Examples.Term.Conv (base₁ base₂ : Base) where

import Category.Monad as Cat
import Category.Applicative as Cat
import Category.Monad.Identity as Id
open import Data.Product
open import Function

idAppli = rawIApplicative
  where open Cat.RawMonad Id.IdentityMonad

import  NotSoFresh.Derived
open import  NotSoFresh.Examples.Term.DataTypes as Term

module BiConv (base₁ base₂ : Base) where

  open    NotSoFresh.Derived base₁
    using ()
    renaming ( World to World₁
             ; Name to Name₁
             ; SynAbs to SynAbs₁
             ; ø to ø₁
             ; _↼_ to _↼₁_
             ; nameø-elim to nameø-elim₁
             )

  open    NotSoFresh.Derived base₂
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

  import NotSoFresh.BiDerived
  open NotSoFresh.BiDerived base₁ base₂
  
  module  Term₁ = Term.Make base₁
  module  Term₂ = Term.Make base₂
  open    Term₁ using (V;ƛ;_·_;`_;Let) renaming (Tm to Tm₁)
  open    Term₂ using (V;ƛ;_·_;`_;Let) renaming (Tm to Tm₂)
  
  Tm₁₂ = (Tm₁ , Tm₂)

  module TraverseTm  {M _↝_} (appli : Cat.RawApplicative M)
                     (comm : Comm₁₂ _↝_)
                     (traverseName : Traverse _↝_ M Name₁₂) where
    open Cat.RawApplicative appli

    traverseTm : Traverse _↝_ M Tm₁₂
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

  traverseTm' : Traverse' Tm₁₂
  traverseTm' = TraverseTm.traverseTm

  freshenTm : Freshen Tm₁₂
  freshenTm = freshen traverseTm'

  convTm : ∀ {α₁ α₂} (Γ : Name₁ α₁ → Name₂ α₂) (x : Fresh₂ α₂) (t : Tm₁ α₁) → Tm₂ α₂
  convTm Γ x t = freshenTm idAppli x Γ t

  convTmø : Tm₁ ø₁ → Tm₂ ø₂
  convTmø = convTm nameø-elim₁ freshø₂

open import NotSoFresh.Repr.Nominal   using (nominal)
open import NotSoFresh.Repr.DeBruijn  using (deBruijn;zero)

module NomConv (base : Base) where
  open BiConv base nominal public using () renaming (convTm to toNom ; convTmø to toNomø)
  open BiConv nominal base public using () renaming (convTm to fromNom ; convTmø to fromNomø)

module DebConv (base : Base) where
  open BiConv base deBruijn public using () renaming (convTm to toDeb ; convTmø to toDebø)
  open BiConv deBruijn base public using () renaming (convTm to fromDeb ; convTmø to fromDebø)

open NomConv public using () renaming (toNom to debToNom ; fromNom to nomToDeb)

module DebTerm = Term.Make deBruijn
module NomTerm = Term.Make nominal

module ExampleDeb where
  open DebTerm
  open import Data.Fin
  appDeb : ∀ (τ σ : Ty) → Tm 0
  appDeb τ σ = ƛ zero (τ ⟶ σ) (ƛ zero τ (V (suc zero) · V zero))

module Example (base : Base) where
  open ExampleDeb
  open Base base
  open Term.Make base
  open DebConv base
  app : ∀ (τ σ : Ty) → Tm ø
  app τ σ = fromDebø (appDeb τ σ)
  
