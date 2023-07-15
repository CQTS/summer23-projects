module CQTS.DataStructures.RedBlackNew where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv

open import Cubical.Structures.Auto

open import Cubical.Data.Int hiding (sucℤ; _+_)
open import Cubical.Core.Everything

open import Cubical.Data.Bool hiding (_≤_; _≟_; _≥_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe
open import Cubical.Relation.Nullary
open import Cubical.Structures.Macro
open import Cubical.Structures.Axioms


open import CQTS.DataStructures2

module RBTrees where
  open BST ℕ isSetℕ

  -- Red-black tree
  data RBTree : Set where
    Empty : RBTree
    Node : Color → RBTree → ℕ → RBTree → RBTree
  
  -- Helper function to calculate the black height of a Red-Black Tree
  blackHeight : RBTree → ℕ
  blackHeight Empty = 0
  blackHeight (Node Black l _ r) = 1 + max (blackHeight l) (blackHeight r)
  blackHeight (Node Red l _ r) = max (blackHeight l) (blackHeight r)
  
  -- implementation of join and split based on the algorithms found here: https://en.wikipedia.org/wiki/Red%E2%80%93black_tree#Set_operations_and_bulk_operations
  -- joinRB and its helper functions
  rotateLeft : RBTree → RBTree
  rotateLeft t = {!   !}

  joinRightHelper : RBTree → RBTree → RBTree
  joinRightHelper (Node Black left x right) (Node Color left₁ y (Node Red left₂ z (Node Red left₃ w right₂))) = rotateLeft (Node Color left₁ y (Node Red left₂ z (Node Black left₃ w right₂)))
  joinRightHelper t1 t2 = t2

  joinRightRB : RBTree → ℕ → RBTree → RBTree
  joinRightRB Empty k TR = Node Red Empty k TR
  joinRightRB (Node Red left x right) k TR = Node Red left x (joinRightRB right k TR)
  joinRightRB (Node Black left x right) k TR with blackHeight (Node Black left x right) | blackHeight TR 
  joinRightRB (Node Black left kl right) k TR | heightL | heightR with heightL ≟ heightL
  ... | lt _ = joinRightHelper (Node Black left kl right) (Node Black left kl (joinRightRB right k TR))
  ... | eq _ = Node Red (Node Black left kl right) k TR
  ... | gt _ = joinRightHelper (Node Black left kl right) (Node Black left kl (joinRightRB right k TR))
  
  -- joinLeftRB and its helper functions
  rotateRight : RBTree → RBTree
  rotateRight t = {!   !}

  joinLeftHelper : RBTree → RBTree → RBTree
  joinLeftHelper (Node Black left x right) (Node Color (Node Red (Node Red left₃ x₃ right₃) x₂ right₂) x₁ right₁) = rotateRight (Node Color (Node Red (Node Black left₃ x₃ right₃) x₂ right₂) x₁ right₁)
  joinLeftHelper t1 t2 = t2

  joinLeftRB : RBTree → ℕ → RBTree → RBTree
  joinLeftRB Empty k TR = Node Red Empty k TR
  joinLeftRB (Node Red left x right) k TR = Node Red (joinLeftRB left k ((Node Red left x right))) x TR
  joinLeftRB (Node Black left x right) k TR  with blackHeight (Node Black left x right) | blackHeight TR 
  joinLeftRB (Node Black left kl right) k TR | heightL | heightR with heightL ≟ heightL
  ... | lt _ = joinLeftHelper (Node Black left kl right) (Node Black (joinLeftRB left k (Node Black left kl right)) kl TR)
  ... | eq _ = Node Red (Node Black left kl right) k TR
  ... | gt _ = joinLeftHelper (Node Black left kl right) (Node Black (joinLeftRB left k (Node Black left kl right)) kl TR)
  
  -- joinRB and its helper functions
  joinRightHelper' : RBTree → RBTree
  joinRightHelper' (Node Red left x (Node Red left₁ x₁ right)) = (Node Black left x (Node Red left₁ x₁ right))
  joinRightHelper' t1 = t1
  
  joinLeftHelper' : RBTree → RBTree
  joinLeftHelper' (Node Red (Node Red left x₁ right₁) x right) = (Node Black (Node Red left x₁ right₁) x right)
  joinLeftHelper' t1 = t1

  joinRB : RBTree → ℕ → RBTree → RBTree
  joinRB TL k TR with blackHeight TL | blackHeight TR
  joinRB TL k TR | heightL | heightR with heightL ≟ heightL
  ... | lt _ = joinLeftHelper' (joinLeftRB TL k TR)
  joinRB (Node Black TL₁ x₁ TR₁) k (Node Black TL₂ x₂ TR₂) | heightL | heightR | eq _ = Node Red (Node Black TL₁ x₁ TR₁) k (Node Black TL₂ x₂ TR₂)
  joinRB TL k TR | heightL | heightR | eq _ = Node Black TL k TR
  ... | gt _ = joinRightHelper' (joinRightRB TL k TR)
  
  -- splitRB
  splitRB : RBTree → (x : ℕ) → (RBTree × Maybe ℕ × RBTree)
  splitRB Empty k = Empty , nothing , Empty
  splitRB (Node color left x right) k with k ≟ x
  ... | lt _ = let (L , b , R) = splitRB left k in (L , b , joinRB R x right)
  ... | eq _ = left , just k , right
  ... | gt _ = let (L , b , R) = splitRB right k in (joinRB left x L , b , right)


