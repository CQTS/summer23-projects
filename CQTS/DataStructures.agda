module CQTS.DataStructures where

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

-- 1. For any element n, the member function applied to the empty tree should return false.
-- 2. If we insert an element n into a tree t, then the member function applied to n in the resulting tree should return true.  
-- 3. If n is a member of a tree and we insert an element m into a tree t, the member function applied to n in the resulting tree should return true. 
-- 4. If we insert an element m into a tree t and then check for membership of an element n (where n is different from m), it should return the same result as checking membership in the original tree t. 

 -- define axioms
 BSTAxioms : (X : Type ℓ) → BSTStructure X → Type ℓ
 BSTAxioms X (empty , insert , member) = 
     ∀ n → (member n empty ≡ false) × -- Empty tree has no members
     (∀ n t → member n (insert n t) ≡ true) × -- Inserted element is a member
     (∀ n m t → member n t ≡ true → member n (insert m t) ≡ true) × -- Non-inserted element is not affected
     (∀ n m t → member n (insert m t) ≡ true → member n t ≡ true)  -- Membership status unaffected by inserting other elements


-- For any element m not in the tree t, then the member function applied to m in the resulting tree should return false. 
-- If the member function applied to an element n in a tree t returns true, then inserting n into t should return the same tree. 
--  (∀ n t → member n t ≡ true → t \eq (insert n t)) × -- Inserting duplicate element returns the same tree 

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


-- Check if an element is in a tree
member : (x : ℕ) → Tree → Bool
member x leaf = false
member x (node y l r) with x ≟ y
... | (lt _) = member x l
... | (eq _) = true
... | (gt _) = member x r

TreeSet : BST ℕ isSetℕ
TreeSet = Tree , leaf , insert , member

-- prove axioms 
-- axiom 1 
emptyTree : (n : ℕ) → member n leaf ≡ false
emptyTree n = refl 

-- axiom 2
insertedElementIsMember : (n :  ℕ) ( t : Tree) → member n (insert n t ) ≡ true
insertedElementIsMember n leaf with n ≟ n
... | (lt x) = ⊥.rec (¬m<m x) 
... | (eq _) = refl 
... | (gt x) = ⊥.rec (¬m<m x) 
insertedElementIsMember n (node m l r) with n ≟ m 
insertedElementIsMember n (node m l r) | (lt x) with n ≟ m 
... | (lt y) = insertedElementIsMember n l 
... | (eq y) = refl 
... | (gt y) = ⊥.rec (<-asym x (<-weaken y) )  
insertedElementIsMember n (node m l r) | (eq x) with n ≟ m 
... | (lt y) = ⊥.rec (<→≢ y x) 
... | (eq y) = refl 
... | (gt y) = ⊥.rec (<→≢ y (sym x)) 
insertedElementIsMember n (node m l r) | (gt x) with n ≟ m 
... | (lt y) = ⊥.rec (<-asym x (<-weaken y) ) 
... | (eq y) = refl 
... | (gt y) = insertedElementIsMember n r 


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

-- Insert an element into a red-black tree
insertRB : (x : ℕ) → RBTree → RBTree
insertRB x Empty = Node Red Empty x Empty
insertRB x (Node color left value right) with x ≟ value
... | (lt _) = balance color (insertRB x left) value right
... | (eq _) = Node color left value right
... | (gt _) = balance color left value (insertRB x right)

RBTreeSet : BST ℕ isSetℕ
RBTreeSet = RBTree , Empty , insertRB , memberRB
  