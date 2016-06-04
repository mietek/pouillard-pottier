import NotSoFresh.Base
module NotSoFresh.Derived (base : NotSoFresh.Base.Base) where

open import Agda.Primitive using (lzero)
import Category.Functor as Cat
import Category.Functor.Extras as Cat
import Category.Applicative as Cat
import Category.Monad as Cat
import Category.Monad.Identity as Id
open import Relation.Binary
open import Relation.Binary.Extras
open import Relation.Binary.PropositionalEquality
open import Coinduction
open import Function
open import Data.Bool
open import Data.Nat using ( ℕ ; suc ; zero ) renaming (_≟_ to _≟ℕ_)
open import Data.Maybe
open import Data.Product
open import Data.Empty
open import Data.Sum using (_⊎_;inj₁;inj₂;[_,_]′)
open import Data.Star hiding (_>>=_)
open import Data.Star.Extras
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary

open NotSoFresh.Base.Base base public renaming (recycle to recycleName)

module MaybeMonad = Cat.RawMonad {lzero} Data.Maybe.monad

maybeAppli = rawIApplicative
  where open MaybeMonad

idAppli = rawIApplicative
  where open Cat.RawMonad {lzero} Id.IdentityMonad

_|×|_ : ∀ (F G : World → Set) → (World → Set)
F |×| G = λ A → F A × G A

Star⁻¹ : ∀ {A : Set} → Rel A lzero → Rel A lzero
Star⁻¹ = flip ∘ Star ∘ flip

_⇀_ : (β α : World) → Set
β ⇀ α = α ↼ β

_←⇀_ : (β α : World) → Set
β ←⇀ α = α ↼→ β

_★↼_ : World → World → Set
_★↼_ = Star⁻¹ _↼_

_↼→★_ : World → World → Set
_↼→★_ = Star _↼→_

_★↼→_ : World → World → Set
_★↼→_ = Star⁻¹ _↼→_

SynAbs : (World → Set) → World → Set
SynAbs F α = ∃ λ γ → α ↼ γ × F γ

FunAbs : (World → Set) → World → Set
FunAbs F α = ∀ {β} → α ⊆ β → F β → F β

DAbs : (World → Set) → World → Set
DAbs F α = ∃ λ γ → α ↼→ γ × F γ

Partial : (World → Set) → World → World → Set
Partial F β α = F β → Maybe (F α)

_≟MaybeName_ : ∀ {α} → Decidable {A = Maybe (Name α)} _≡_
_≟MaybeName_ = DecSetoid._≟_ (Data.Maybe.decSetoid _≟Name_)

-- nameø-elim : ∀ {a} {A : Set a} → Name ø → A
nameø-elim : ∀ {A : Set} → Name ø → A
nameø-elim = ⊥-elim ∘′ ¬nameø

Fresh : World → Set
Fresh α = ∃ λ β → α ↼→ β

module NamePack {β} (x : Name β) where
  nameOf      : Name β
  nameOf      = x

  -- nameø-elim : ∀ {a} {A : Set a} → Name ø → A
  nameø-elim'  : ∀ {A : Set} → β ≡ ø → A
  nameø-elim' eq = go eq x
    where go : ∀ {α} {A : Set} → (α ≡ ø) → Name α → A
          go refl = nameø-elim

  recycle     : ∃ λ γ → β ↼ γ × β ⊆ γ
  recycle     = recycleName x

  _≟nameOf_ : (y : Name β) → Dec (x ≡ y)
  _≟nameOf_ = _≟Name_ x

module WorldRelPack (α β : World) where
  outerOf  : World
  outerOf  = α
  innerOf  : World
  innerOf  = β

module WeakPack {α β} (x : α ↼ β) where
  open NamePack (nameOf↼ x)  public
  open  WorldRelPack α β     public
  weakOf      : α ↼ β
  weakOf      = x
  exportWith  : Name β → Maybe (Name α)
  exportWith  = export↼ x

module ⊆Pack {α β} (x : α ⊆ β) where
  open  WorldRelPack α β public
  ⊆Of         : α ⊆ β
  ⊆Of         = x
  importWith  : Name α → Name β
  importWith  = import⊆ x

module StrongPack {α β} (x : α ↼→ β) where
  open  WeakPack (weaken x)  public
  open  ⊆Pack (dropName x)   public hiding (innerOf;outerOf)
  strongOf  : α ↼→ β
  strongOf  = x
  nextOf    : Fresh β
  nextOf    = next↼→ weakOf strongOf

module FreshPack {α} (x : Fresh α) where
  open StrongPack (proj₂ x) public

freshø : Fresh ø
freshø = init↼→

import↼Fresh : ∀ {α β} → α ↼ β → Fresh α → Fresh β
import↼Fresh a b = next↼→ a (proj₂ b)

data FS (α : World) : Set where
  _∷_ : ∀ {β} (x : α ↼→ β) (tl : ∞ (FS β)) → FS α

freshToFS : ∀ {α} → Fresh α → FS α
freshToFS x = strongOf x ∷ (♯ (freshToFS (nextOf x)))
  where open FreshPack


fsø : FS ø
fsø = freshToFS freshø

α↼→★ø→α≡ø : ∀ {α} → α ↼→★ ø → α ≡ ø
α↼→★ø→α≡ø ε = refl
α↼→★ø→α≡ø (α↼→ø ◅ xs) rewrite α↼→★ø→α≡ø xs = nameø-elim' α↼→ø refl
  where open StrongPack

module Incl' where
  data _⊆'_ : (α β : World) → Set where
    ø-bottom    : ∀ {α} → ø ⊆' α
    ⊆'-refl     : ∀ {α} → α ⊆' α
    ⊆'-trans    : ∀ {α β γ} → α ⊆' β → β ⊆' γ → α ⊆' γ
    dropName'   : ∀ {α β} → α ↼→ β → α ⊆' β

  import⊆' : ∀ {α β} → α ⊆' β → (Name α → Name β)
  import⊆' ⊆'-refl        = id
  import⊆' ø-bottom       = nameø-elim
  import⊆' (⊆'-trans x y) = import⊆' y ∘ import⊆' x
  import⊆' (dropName' α↼→β)  = importWith α↼→β
    where open StrongPack

  α⊆'ø→α≡ø : ∀ {α} → α ⊆' ø → α ≡ ø
  α⊆'ø→α≡ø ⊆'-refl    = refl
  α⊆'ø→α≡ø ø-bottom   = refl
  α⊆'ø→α≡ø (⊆'-trans x y) rewrite α⊆'ø→α≡ø y = α⊆'ø→α≡ø x
  α⊆'ø→α≡ø (dropName' α↼→ø) = nameø-elim' α↼→ø refl
    where open StrongPack

module Incl₂ where
  data Bottomize (_∼_ : Rel World _) : (α β : World) → Set where
    ø-bottom : ∀ {α} → Bottomize _∼_ ø α
    lift     : ∀ {α β} → α ∼ β → Bottomize _∼_ α β

  _⊆₂_ : Rel World _
  _⊆₂_ = Bottomize _↼→★_

  ⊆₂-refl : Reflexive _⊆₂_
  ⊆₂-refl = lift ε

  ⊆₂-trans : ∀ {α β γ} → α ⊆₂ β → β ⊆₂ γ → α ⊆₂ γ
  ⊆₂-trans ø-bottom    _           = ø-bottom
  ⊆₂-trans (lift α↼→★ø) ø-bottom      rewrite α↼→★ø→α≡ø α↼→★ø = ø-bottom
  ⊆₂-trans (lift α↼→★β) (lift β↼→★γ) = lift (α↼→★β ◅◅ β↼→★γ)

α⊆ø→α⊆β : ∀ {α} β → α ⊆ ø → α ⊆ β
α⊆ø→α⊆β β α⊆ø = ⊆-trans α⊆ø ø-bottom-⊆


export★↼ : ∀ {α β} → α ★↼ β → Name β → Maybe (Name α)
export★↼ ε       y = just y
export★↼ (x ◅ Γ) y = export↼ x y >>= export★↼ Γ
  where open MaybeMonad

import↼→★ : ∀ {α β} → α ↼→★ β → Name α → Name β
import↼→★ = evalStar id _∘′_ StrongPack.importWith

-- infixr 5 _◅_
-- data _>>>_ {I : Set} (P Q : Rel I (suc zero)) : Rel I (suc zero) where
--  _◅_ : Trans' P Q (P >>> Q)

-- K : {I : Set} → Set → Rel I _
-- K A _ _ = A

Carry : ∀ {I : Set} (P : Rel I lzero) (A : Set) → Rel I lzero
Carry P A i j = (P i j × A)

IndexTy : Rel World _ → Set
IndexTy Env = ∀ {α β} → Env α β → Name β → Name α ⊎ ℕ

index★↼ : IndexTy _★↼_
index★↼ ε x = inj₁ x
index★↼ (β↼γ ◅ Γ) x
  with export↼ β↼γ x
...  | just x' = [ inj₁ , inj₂ ∘ ℕ.suc ]′ (index★↼ Γ x')
...  | nothing = inj₂ 0

IndexøTy : ∀ (CEnv : World → Set) → Set
IndexøTy CEnv = ∀ {α} → CEnv α → Name α → ℕ

indexø★↼ : IndexøTy (_★↼_ ø)
indexø★↼ x = [ nameø-elim , id ]′ ∘ index★↼ x

record EnvPack : Set₁ where
  field
    Env        : Set → World → World → Set
    emptyEnv   : ∀ {A α} → Env A α α
    lookupEnv  : ∀ {A α β} → Env A α β → Name β → Name α ⊎ A
    _,_↦_      : ∀ {α β γ A} → Env A α β → β ↼ γ → A → Env A α γ
    mapEnv     : ∀ {α β A B} → (A → B) → Env A α β → Env B α β

record ImportableEnvPack : Set₁ where
  field
    envPack : EnvPack
  open EnvPack envPack
  field
    importEnv⊆ : ∀ {α β γ A} → α ⊆ β → Env A α γ → Env A β γ
  open EnvPack envPack public

-- CEnv is for closed Env
record CEnvPack : Set₁ where
  field
    CEnv        : Set → World → Set
    emptyCEnv   : ∀ {A} → CEnv A ø
    lookupCEnv  : ∀ {A α} → CEnv A α → Name α → A
    _,_↦_      : ∀ {α β A} → CEnv A α → α ↼ β → A → CEnv A β
    mapCEnv     : ∀ {α A B} → (A → B) → CEnv A α → CEnv B α

-- DCEnv is for distinct closed Env
record DCEnvPack : Set₁ where
  field
    DCEnv        : Set → World → Set
    emptyDCEnv   : ∀ {A} → DCEnv A ø
    lookupDCEnv  : ∀ {A α} → DCEnv A α → Name α → A
    _,_↦_        : ∀ {α β A} → DCEnv A α → α ↼→ β → A → DCEnv A β
    mapDCEnv     : ∀ {α A B} → (A → B) → DCEnv A α → DCEnv B α

lookupStar : ∀ {α β} {_↝_ : Rel World lzero} → (∀ {γ δ} → γ ↝ δ → Name γ → Maybe (Name δ))
                         → Star _↝_ α β → Name α → Name β ⊎ ∃₂ _↝_
lookupStar _ ε y = inj₁ y
lookupStar f (x ◅ Γ) y
 with f x y
... | just y' = lookupStar f Γ y'
... | nothing = inj₂ (_ , _ , x)

starEnv : EnvPack
starEnv = record { Env = Env ; emptyEnv = ε ; lookupEnv = lookupEnv
                 ; _,_↦_ = λ Γ x v → (x , v) ◅ Γ ; mapEnv = mapEnv }
   where
     Env : (A : Set) → Rel World _
     Env = Star⁻¹ ∘ Carry _↼_

     lookupEnv : ∀ {α γ τ} → Env τ α γ → Name γ → Name α ⊎ τ
     lookupEnv ε x = inj₁ x
     lookupEnv ((y , z) ◅ Γ) x
       with export↼ y x
     ...  | just x' = lookupEnv Γ x'
     ...  | nothing = inj₂ z

     mapEnv : ∀ {α β A B} → (A → B) → Env A α β → Env B α β
     mapEnv f ε              = ε
     mapEnv f ((x , v) ◅ xs) = (x , f v) ◅ mapEnv f xs

module Env = EnvPack starEnv

closeEnv : EnvPack → CEnvPack
closeEnv env = record { CEnv = CEnv
                      ; emptyCEnv = emptyEnv
                      ; lookupCEnv = lookupCEnv
                      ; mapCEnv = mapEnv
                      ; _,_↦_ = _,_↦_ }
  where
    open EnvPack env

    CEnv : Set → World → Set
    CEnv A = Env A ø

    lookupCEnv : ∀ {α τ} → CEnv τ α → Name α → τ
    lookupCEnv Γ = [ nameø-elim , id ]′ ∘ lookupEnv Γ
      where open NamePack

module CEnv = CEnvPack (closeEnv starEnv)

funEnv : EnvPack
funEnv = record { Env = Env
                ; emptyEnv = inj₁
                ; _,_↦_ = _,_↦_
                ; lookupEnv = id
                ; mapEnv = mapEnv }
  where
    Env : Set → World → World → Set
    Env A α β = Name β → Name α ⊎ A

    _,_↦_  : ∀ {α β γ A} → Env A α β → β ↼ γ → A → Env A α γ
    _,_↦_ Γ x v y = maybe Γ (inj₂ v) (export↼ x y)

    mapEnv : ∀ {α β A B} → (A → B) → Env A α β → Env B α β
    mapEnv f g x = [ inj₁ , inj₂ ∘ f ]′ (g x)

funCEnv : CEnvPack
funCEnv = record { CEnv        = CEnv
                 ; emptyCEnv   = nameø-elim
                 ; _,_↦_       = _,_↦_
                 ; lookupCEnv  = id
                 ; mapCEnv     = _∘′_ }
  where
    open NamePack

    CEnv : Set → World → Set
    CEnv A α = Name α → A

    _,_↦_  : ∀ {α β A} → CEnv A α → α ↼ β → A → CEnv A β
    _,_↦_ Γ x v y = maybe Γ v (export↼ x y)

funDCEnv : DCEnvPack
funDCEnv = record { DCEnv        = DCEnv
                  ; emptyDCEnv   = nameø-elim
                  ; _,_↦_        = _,_↦_
                  ; lookupDCEnv  = id
                  ; mapDCEnv     = _∘′_ }
  where
    open NamePack

    DCEnv : Set → World → Set
    DCEnv A α = Name α → A

    _,_↦_  : ∀ {α β A} → DCEnv A α → α ↼→ β → A → DCEnv A β
    _,_↦_ Γ x v y = maybe Γ v (export↼ (weaken x) y)

importableFunEnv : ImportableEnvPack
importableFunEnv = record { envPack = funEnv ; importEnv⊆ = importEnv⊆ }
  where
    open EnvPack funEnv
    importEnv⊆ : ∀ {α β γ A} → α ⊆ β → Env A α γ → Env A β γ
    importEnv⊆ ⊆w Γ = [ inj₁ ∘ import⊆ ⊆w , inj₂ ]′ ∘ Γ

endOpenEnv : EnvPack → ImportableEnvPack
endOpenEnv env = record
  { envPack = record { Env = Env
                     ; emptyEnv = emptyEnv
                     ; _,_↦_ = _,_↦_
                     ; lookupEnv = lookupEnv
                     ; mapEnv = mapEnv }
  ; importEnv⊆ = importEnv⊆ }
  where
    module E = EnvPack env

    Env : Set → World → World → Set
    Env A α γ = ∃ λ β → β ⊆ α × E.Env A β γ

    emptyEnv : ∀ {A α} → Env A α α
    emptyEnv = (_ , ⊆-refl , E.emptyEnv)

    lookupEnv : ∀ {A α β} → Env A α β → Name β → Name α ⊎ A
    lookupEnv (γ , ⊆w , Γ) y = [ inj₁ ∘ import⊆ ⊆w , inj₂ ]′ (E.lookupEnv Γ y)

    _,_↦_ : ∀ {α β γ A} → Env A α β → (β ↼ γ) → A → Env A α γ
    _,_↦_ (_ , ⊆w , Γ) x v = (_ , ⊆w , E._,_↦_ Γ x v)

    importEnv⊆ : ∀ {α β γ A} → α ⊆ β → Env A α γ → Env A β γ
    importEnv⊆ ⊆w (γ , ⊆w' , Γ) = (_ , ⊆-trans ⊆w' ⊆w , Γ)

    mapEnv : ∀ {α β A B} → (A → B) → Env A α β → Env B α β
    mapEnv f (_ , ⊆w , Γ) = (_ , ⊆w , E.mapEnv f Γ)

module VecChain where
  data _⇀⟨_⟩_ : World → ℕ → World → Set where
    ε : ∀ {α} → α ⇀⟨ 0 ⟩ α
    _◅_ : ∀ {α β γ n} → α ⇀ β → β ⇀⟨ n ⟩ γ → α ⇀⟨ ℕ.suc n ⟩ γ

module αEq (Env   : Rel World _)
           (index : IndexTy Env) where
  αeqEnv : (α β γ : World) → Set
  αeqEnv α β γ = Env α β × Env α γ

  αeqTy : (World → Set) → Set
  αeqTy F = ∀ {α β γ} → αeqEnv α β γ → F β → F γ → Bool

  αeqNameR : αeqTy Name
  αeqNameR (Γ , Δ) x y with index Γ x | index Δ y
  ...                     | inj₁ x'   | inj₁ y'   = ⌊ x' ≟Name y' ⌋
  ...                     | inj₂ m    | inj₂ n    = ⌊ m  ≟ℕ    n  ⌋
  ...                     | _         | _         = false

module αEqStarEnv where
  open αEq _★↼_ index★↼
  extαeqEnv : ∀ {α β β' γ γ'} → αeqEnv α β γ → β ↼ β' → γ ↼ γ'
                              → αeqEnv α β' γ'
  extαeqEnv (Γ , Δ) x y = (x ◅ Γ , y ◅ Δ)



ComposeCommute : (_↝₁_ _↝₂_ : Rel World _) → Set
ComposeCommute _↝₁_ _↝₂_
  = ∀ {α β γ}  → α ↝₁ β → β ↝₂ γ
      → ∃ λ δ  → α ↝₂ δ × δ ↝₁ γ

Comm : (_↝_ : Rel World _) → Set
Comm _↝_ = ComposeCommute _⇀_ _↝_

DComm : (_↝_ : Rel World _) → Set
DComm _↝_ = ComposeCommute _←⇀_ _↝_

flipComm : ∀ {_↝₁_ _↝₂_}  → ComposeCommute _↝₁_ _↝₂_
                          → ComposeCommute (flip _↝₂_) (flip _↝₁_)
flipComm comm x y with comm y x
... | (_ , z , t) = (_ , t , z)

Fresh×Name→FName : (Set → Set) → Rel World _
Fresh×Name→FName F α β = Fresh β × (Name α → F (Name β))

module WithApplicative {F} (appli : Cat.RawApplicative F) where
  open Cat.RawApplicative {lzero} appli

  importFun : ∀ {α β γ δ} → β ↼→ δ → α ↼ γ
                       → (Name α → F (Name β))
                       → (Name γ → F (Name δ))
  importFun β↼→δ α↼γ f bγ
      with export↼ α↼γ bγ
  ...    | just aα = importWith β↼→δ <$> f aα
    where open StrongPack
  ...    | nothing = pure (nameOf β↼→δ)
    where open StrongPack

  Fresh×Name→FName-Comm : Comm (Fresh×Name→FName F)
  Fresh×Name→FName-Comm x (y , f)
    = (_ , (nextOf y , importFun (strongOf y) x f) , weakOf y)
      where open FreshPack

  Fresh×Name→FName-DComm : DComm (Fresh×Name→FName F)
  Fresh×Name→FName-DComm x (y , f)
    = (_ , (nextOf y , importFun (strongOf y) (weaken x) f) , strongOf y)
      where open FreshPack

Kleisli : (M : Set → Set) → Rel Set _
Kleisli M A B = A → M B

Traverse : (_↝_ : Rel World _) (M : Set → Set) (F : World → Set) → Set
Traverse _↝_ M F = Cat.Fmap _↝_ (Kleisli M) F
-- Traverse _↝_ M F = ∀ {α β} → α ↝ β → F α → M (F β)

module Traversable {_↝_ M}
                   (appli : Cat.RawApplicative M)
                   (comm : Comm _↝_)
   where
  open Cat.RawApplicative {lzero} appli

  Tr : (World → Set) → Set
  Tr F = Traverse _↝_ M F

  ×-traverse : ∀ {G H} → Tr G → Tr H → Tr (G |×| H)
  ×-traverse traverseG traverseH Γ (x , y) =
    traverseG Γ x ⊗ traverseH Γ y

  traverseAbs : ∀ {G} → Tr G → Tr (SynAbs G)
  traverseAbs traverseG Γ (_ , x , t)
      with comm x Γ
  ... | (_ , Γ' , x') = (λ t' → (_ , x' , t')) <$> traverseG Γ' t

Traverse' : (World → Set) → Set₁
Traverse' F = ∀ {_↝_ M}
                (appli : Cat.RawApplicative M)
                (comm : Comm _↝_)
                (traverseName : Traverse _↝_ M Name)
              → Traverse _↝_ M F

module DTraversable {_↝_ M}
                    (appli : Cat.RawApplicative M)
                    (comm : Comm _↝_)
                    (dcomm : DComm _↝_)
   where
  open Cat.RawApplicative {lzero} appli

  Tr : (World → Set) → Set
  Tr F = Traverse _↝_ M F

  ×-traverse : ∀ {G H} → Tr G
                       → Tr H → Tr (G |×| H)
  ×-traverse traverseG traverseH Γ (x , y) =
    traverseG Γ x ⊗ traverseH Γ y

  traverseAbs : ∀ {G} → Tr G → Tr (SynAbs G)
  traverseAbs traverseG Γ (_ , x , t)
      with comm x Γ
  ... | (_ , Γ' , x') = (λ t' → (_ , x' , t')) <$> traverseG Γ' t

  traverseDAbs : ∀ {G} → Tr G → Tr (DAbs G)
  traverseDAbs traverseG Γ (_ , x , t)
      with dcomm x Γ
  ... | (_ , Γ' , x') = (λ t' → (_ , x' , t')) <$> traverseG Γ' t

DTraverse' : (World → Set) → Set₁
DTraverse' F = ∀ {_↝_ M}
                 (appli : Cat.RawApplicative M)
                 (comm : Comm _↝_)
                 (dcomm : DComm _↝_)
                 (traverseName : Traverse _↝_ M Name)
               → Traverse _↝_ M F

FF : (World → Set) → World → Set
FF F α = Fresh α → F α

Freshen : (World → Set) → Set₁
Freshen F = ∀ {α β M} → Cat.RawApplicative M → Fresh β
                      → (Name α → M (Name β))
                      → F α → M (F β)

freshen : ∀ {F} → Traverse' F → Freshen F
freshen traverseF appli x Γ
    = traverseF appli Fresh×Name→FName-Comm proj₂ (x , Γ)
  where open WithApplicative appli

freshenD : ∀ {F} → DTraverse' F → Freshen F
freshenD traverseF appli x Γ
    = traverseF appli Fresh×Name→FName-Comm Fresh×Name→FName-DComm
                proj₂ (x , Γ)
  where open WithApplicative appli

Import⊆ : (World → Set) → Set
Import⊆ F = ∀ {α β} → α ⊆ β → F α → F β

-- not very useful since Import⊆ is an instance of Traverse
importAbs⊆ : ∀ {F} → Import⊆ F → Import⊆ (SynAbs F)
importAbs⊆ impF α⊆β (_ , γ⇀α , tγ)
     with γ⇀α ↼-commute-⊆ α⊆β
...     | (_ , γ⊆δ , δ⇀β) = (_ , δ⇀β , impF γ⊆δ tγ)

-- one can import⊆ a FunAbs without knowing how to import the body
importFunAbs⊆ : ∀ {F} → Import⊆ (FunAbs F)
importFunAbs⊆ α⊆β f {γ} β⊆γ = f (⊆-trans α⊆β β⊆γ)

import⊆Gen : ∀ {F} → Traverse' F → Import⊆ F
import⊆Gen traverseF = traverseF idAppli _↼-commute-⊆_ import⊆

Export⊆ : (World → Set) → Set
Export⊆ F = ∀ {α β} → β ⊆ α → F α → F β

exportDAbs⊆ : ∀ {F} → Export⊆ F → Export⊆ (DAbs F)
exportDAbs⊆ expF β⊆α (γ , α↼→γ , tγ)
     with  β⊆α ⊆-commute-↼→ α↼→γ
...     | (δ , β↼→δ , δ⊆γ) = (_ , β↼→δ , expF δ⊆γ tγ)

Export↼ : (World → Set) → Set
Export↼ F = ∀ {α β} → α ↼ β → Fresh α → Partial F β α

export↼Gen : ∀ {F} → Freshen F → Export↼ F
export↼Gen freshenF x y = freshenF maybeAppli y (export↼ x)

Close : (World → Set) → Set
Close F = ∀ {α} → Partial F α ø

closeGen : ∀ {F} → Freshen F → Close F
closeGen freshenF = freshenF maybeAppli freshø (const nothing)

FresheningImport⊆ : (World → Set) → Set
FresheningImport⊆ F = ∀ {α β} → α ⊆ β → Fresh β → F α → F β

fresheningImport⊆Gen : ∀ {F} → Freshen F → FresheningImport⊆ F
fresheningImport⊆Gen freshenF ⊆w x = freshenF idAppli x (import⊆ ⊆w)

module Substitution where
  Fresh×Name→F : (F : World → Set) (α β : World) → Set
  Fresh×Name→F F α β = Fresh β × (Name α → F β)

  -- Subst F G can be read as F → G in HOAS
  Subst : (F G : World → Set) → Set
  Subst F G = ∀ {α β} → (Fresh×Name→F F α β) → (G α → G β)

  extθ : ∀ {F α β γ δ} → Import⊆ F → (varF : ∀ {α} → Name α → F α)
                       → (β ↼→ δ) → (α ↼ γ)
                       → (Name α → F β) → (Name γ → F δ)
  extθ imp var x y f z with export↼ y z
  ... | just z' = imp (⊆Of x) (f z')
    where open StrongPack
  ... | nothing = var (nameOf x)
    where open StrongPack

  commθ : ∀ {F} → Import⊆ F → (varF : ∀ {α} → Name α → F α)
                → Comm (Fresh×Name→F F)
  commθ imp var x (y , f) = (_ , (nextOf y , f') , weakOf y)
    where open FreshPack
          f' = maybe (imp (⊆Of y) ∘ f) (var (nameOf y)) ∘ export↼ x

  dcommθ : ∀ {F} → FresheningImport⊆ F → (varF : ∀ {α} → Name α → F α)
                 → DComm (Fresh×Name→F F)
  dcommθ imp var x (y , f) = (_ , (y' , f') , strongOf y)
    where open FreshPack
          y' = nextOf y
          f' = maybe (imp (⊆Of y) y' ∘ f) (var (nameOf y)) ∘ StrongPack.exportWith x

  ×-subst : ∀ {F G H} → Subst F G → Subst F H → Subst F (G |×| H)
  ×-subst substG substH θ (x , y) = (substG θ x , substH θ y)

  substAbs : ∀ {F G} → Import⊆ F → (∀ {α} → Name α → F α)
                     → Subst F G → Subst F (SynAbs G)
  substAbs impF varF substFG θ (_ , x , t)
    with commθ impF varF x θ
  ...  | (_ , θ' , x') = (_ , x' , substFG θ' t)
