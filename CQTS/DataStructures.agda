module CQTS.DataStructures where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv

open import Cubical.Structures.Auto

open import Cubical.Data.Bool hiding (_≤_; _≟_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

module _ (A : Type ℓ) (Aset : isSet A) where

 BSTStructure : Type ℓ → Type ℓ
 BSTStructure X = X × (A → X → X) × (A → X → Bool)

 BSTEquivStr = AutoEquivStr BSTStructure

 BSTUnivalentStr : UnivalentStr _ BSTEquivStr
 BSTUnivalentStr = autoUnivalentStr BSTStructure

 BST : Type (ℓ-suc ℓ)
 BST = TypeWithStr ℓ BSTStructure

 BSTAxioms : (X : Type ℓ) → BSTStructure X → Type ℓ
 BSTAxioms X (empty , insert , member) = 
     ∀ n → (member n empty ≡ false) 

-- Naive implementation of BSTs

-- Data type
data Tree : Set where
  leaf : Tree
  node : ℕ → Tree → Tree → Tree

-- Insert an element into a tree
insert : (x : ℕ) → Tree → Tree
insert x leaf = node x leaf leaf
insert x (node y l r) with x ≟ y
... | (lt _) = node y (insert x l) r
... | (eq _) = node y l r
... | (gt _) = node y l (insert x r)



-- -- Check if an element is in a tree
member : (x : ℕ) → Tree → Bool
member x leaf = false
member x (node y l r) with x ≟ y
... | (lt _) = member x l
... | (eq _) = true
... | (gt _) = member x r

TreeSet : BST ℕ isSetℕ
TreeSet = Tree , leaf , insert , member

