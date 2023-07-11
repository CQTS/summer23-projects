module CQTS.DataStructures where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.SIP
-- open import Cubical.Functions.FunExtEquiv

-- open import Cubical.Structures.Auto

-- open import Cubical.Data.Bool hiding (_≤_; _≟_; _≥_)
-- open import Cubical.Data.Nat
-- open import Cubical.Data.Nat.Properties
-- open import Cubical.Data.Nat.Order
-- open import Cubical.Data.Sigma
open import Cubical.Structures.Macro
open import Cubical.Structures.Axioms

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv

open import Cubical.Structures.Auto

open import Cubical.Data.Int hiding (sucℤ; _+_)
open import Cubical.Core.Everything


open import Cubical.Data.Bool hiding (_≤_; _≟_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

private
  variable
   ℓ : Level


module BST-on (A : Type ℓ) (Aset : isSet A) where
-- Our BST structure has three main components, the empty Tree, an insert function and a member function

  rawBSTDesc =
    autoDesc (λ (X : Type ℓ) → X × (A → X → X) × (A → X → Bool)) 
  
  open Macro ℓ rawBSTDesc public renaming
    ( structure to RawBSTStructure
    ; equiv to RawBSTEquivStr
    ; univalent to rawBSTUnivalentStr
    )

  RawBST : Type (ℓ-suc ℓ)
  RawBST = TypeWithStr ℓ RawBSTStructure

  BSTAxioms : (X : Type ℓ) → RawBSTStructure X → Type ℓ
  BSTAxioms X S@(empty , insert , member) = 
      (isSet X)
    × (∀ n → (member n empty ≡ false))            -- membering empty tree always fails
    × (∀ n t → member n (insert n t) ≡ true)  -- Inserted element is a member
    × (∀ n m t → member n t ≡ true → member n (insert m t) ≡ true)  -- Non-inserted element is not affected
    × (∀ n m t →  ¬ ( n ≡ m ) → member n (insert m t) ≡ true → member n t ≡ true)  -- Membership status unaffected by inserting other elements

  isPropBSTAxioms : ∀ X S → isProp (BSTAxioms X S)
  isPropBSTAxioms X (empty , insert , member) =
    isPropΣ isPropIsSet
      (λ XSet → isProp×3 (isPropΠ λ n → isSetBool (member n empty) false) 
                        (isPropΠ2 λ n t → isSetBool (member n (insert n t)) true)
                        (isPropΠ4 λ n m t p → isSetBool (member n (insert m t)) true)
                        (isPropΠ5 λ n m t np p → isSetBool (member n t) true)
      )
      

  BSTStructure : Type ℓ → Type ℓ
  BSTStructure = AxiomsStructure RawBSTStructure BSTAxioms

  BST : Type (ℓ-suc ℓ)
  BST = TypeWithStr ℓ BSTStructure

  BSTEquivStr : StrEquiv BSTStructure ℓ
  BSTEquivStr = AxiomsEquivStr RawBSTEquivStr BSTAxioms

  bstUnivalentStr : UnivalentStr BSTStructure BSTEquivStr
  bstUnivalentStr = axiomsUnivalentStr RawBSTEquivStr isPropBSTAxioms rawBSTUnivalentStr
  
