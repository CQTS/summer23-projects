module CQTS.DataStructures.RBTrees where

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
open import Cubical.Relation.Nullary
open import Cubical.Structures.Macro
open import Cubical.Structures.Axioms

-- RedBlack Tree Implemetation
-- Colors of nodes
data Color : Set where
  Red : Color
  Black : Color

-- Red-black tree
data RBTree : Set where
  Empty : RBTree
  Node : Color → RBTree → ℕ → RBTree → RBTree

-- Check if an element is in a red-black tree
memberRB : (x : ℕ) → RBTree → Bool
memberRB x Empty = false
memberRB x (Node _ left value right) with x ≟ value
... | lt _ = memberRB x left
... | eq _ = true
... | gt _ = memberRB x right

-- Helper function to balance the red-black tree
balance : Color → RBTree → ℕ → RBTree → RBTree
balance Black (Node Red (Node Red a x b) y c) z d = Node Red (Node Black a x b) y (Node Black c z d)
balance Black (Node Red a x (Node Red b y c)) z d = Node Red (Node Black a x b) y (Node Black c z d)
balance Black a x (Node Red (Node Red b y c) z d) = Node Red (Node Black a x b) y (Node Black c z d)
balance Black a x (Node Red b y (Node Red c z d)) = Node Red (Node Black a x b) y (Node Black c z d)
balance color left value right = Node color left value right

-- Helper function for insert
ins : (x : ℕ) → RBTree → RBTree
ins x Empty = Node Red Empty x Empty
ins x (Node color left value right) with x ≟ value
... | (lt _) = balance color (ins x left) value right
... | (eq _) = Node color left value right
... | (gt _) = balance color left value (ins x right)

-- helper function to blacken root
blackenRoot : RBTree → RBTree
blackenRoot Empty = Empty
blackenRoot (Node color l x r) = Node Black l x r

-- Insert an element into a red-black tree
insertRB : ((x : ℕ) → RBTree → RBTree)
insertRB x t = blackenRoot (ins x t) 

mergeRB : RBTree → RBTree → RBTree
mergeRB t1 Empty = {!   !}
mergeRB t1 (Node col t2 x t3) = Node {!   !} (mergeRB t1 t2) x t3

RBTreeSet : BST ℕ isSetℕ
RBTreeSet = RBTree , Empty , insertRB , memberRB