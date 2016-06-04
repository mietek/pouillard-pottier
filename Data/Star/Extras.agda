module Data.Star.Extras where

open import Agda.Primitive using (lzero)
open import Relation.Binary using (Rel;_⇒_)
open import Data.Star using (Star;ε;_◅_)
-- import Category as Cat

evalStar : ∀ {A : Set}
             {P Q : Rel A lzero} (idQ : ∀ {x} → Q x x)
             (_∘Q_ : ∀ {x y z} → Q y z → Q x y → Q x z)
           → (P ⇒ Q) → Star P ⇒ Q
evalStar idQ _    _ ε        = idQ
evalStar idQ _∘Q_ f (x ◅ xs) = evalStar idQ _∘Q_ f xs ∘Q f x 
