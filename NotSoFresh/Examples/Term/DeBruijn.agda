module NotSoFresh.Examples.Term.DeBruijn where

open import NotSoFresh.Repr.DeBruijn
import NotSoFresh.Examples.Term as Term
open Term deBruijn
open TermExamples
open SmallStep.WeakCBV.Check 10
open import Relation.Binary.PropositionalEquality

ex₁ : idø (ι ⟶ ι) · ` (num 42) ↝★ ` (num 42)
ex₁ = refl

ex₂ : ((` (natFix ι) · ` (num 3)) · ` suc) · ` (num 0) ↝★ ` (num 3)
ex₂ = refl
