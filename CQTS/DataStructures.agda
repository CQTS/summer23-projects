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
open import Cubical.Relation.Nullary


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
     (∀ n m t →  ¬ ( n ≡ m ) → member n (insert m t) ≡ true → member n t ≡ true)  -- Membership status unaffected by inserting other elements


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
... | (eq x) = refl 
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

-- axiom 3
insertPreservesMembership :  (n m : ℕ) (t : Tree) → member n t ≡ true → member n (insert m t) ≡ true -- Non-inserted element is not affected
insertPreservesMembership n m leaf with n ≟ m
... | (lt x) = λ y → y
... | (eq x) = λ y → refl
... | (gt x) = λ y → y
insertPreservesMembership n m (node x l r) with m ≟ x  
insertPreservesMembership n m (node x l r) | (lt z) with n ≟ x
... | (lt y) = insertPreservesMembership n m l 
... | (eq y) = λ p i → true 
... | (gt y) = λ p i → p i 
insertPreservesMembership n m (node x l r) | (eq z) with n ≟ x 
... | (lt y) = λ p i → p i 
... | (eq y) = λ p i → true
... | (gt y) = λ p i → p i  
insertPreservesMembership n m (node x l r) | (gt z) with n ≟ x 
... | (lt y) = λ p i → p i 
... | (eq y) = λ p i → true
... | (gt y) = insertPreservesMembership n m r 

-- axiom 4 
isMemberAfterInsertion : (n m : ℕ) (t : Tree) → ( ¬ ( n ≡ m ) ) → (member n (insert m t) ≡ true → member n t ≡ true)
isMemberAfterInsertion n m leaf with n ≟ m
... | (lt x) = λ p q i → q i 
... | (eq x) =  λ p q → ⊥.rec (p x) 
... | (gt x) = λ p q i → q i 
isMemberAfterInsertion n m (node s l r) neq with m ≟ s 
isMemberAfterInsertion n m (node s l r) neq | (lt x) with n ≟ s
... | (lt y) = isMemberAfterInsertion n m l neq 
... | (eq y) = λ p i → true
... | (gt y) = λ p i → p i 
isMemberAfterInsertion n m (node s l r) neq | (eq x) with n ≟ s 
... | (lt y) = λ p i → p i
... | (eq y) = λ p i → true
... | (gt y) = λ p i → p i
isMemberAfterInsertion n m (node s l r) neq | (gt x) with n ≟ s 
... | (lt y) = λ p i → p i 
... | (eq y) = λ p i → true
... | (gt y) = isMemberAfterInsertion n m r neq 


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

-- transfer proofs of axioms   

-- define relation 
R : Tree → RBTree → Type 
R nt rbt = ∀ n → member n nt ≡ memberRB n rbt

-- function from naive tree to red-black tree
φ : Tree → RBTree 
φ leaf = Empty
-- φ (node x leaf leaf) = Node Red Empty x Empty
-- φ (node x t1 t2) = insertRB x (mergeRB t1 t2)
φ (node x leaf leaf) = insertRB x Empty
-- check this case (adding x?)
φ (node x leaf (node x₁ right right₁)) = insertRB x ((Node _ Empty x (φ (node x₁ right right₁ )) ))
φ (node x (node x₁ left left₁) leaf) = {!   !}
φ (node x (node x₁ left left₁) (node x₂ right right₁)) = {!   !} 


-- function from red-black tree to naive tree
ψ : RBTree → Tree
ψ Empty = leaf
ψ (Node color Empty x Empty) = node x leaf leaf
ψ (Node color Empty x (Node color1 right x₂ right₁)) = node x leaf (ψ (Node color1 right x₂ right₁))
ψ (Node color (Node color2 left x₂ left₁) x Empty) = node x (ψ (Node color2 left x₂ left₁)) leaf
ψ (Node color (Node color3 left x₂ left₁) x (Node x₃ right x₄ right₁)) = node x (ψ (Node color3 left x₂ left₁))  (ψ (Node x₃ right x₄ right₁)) 


