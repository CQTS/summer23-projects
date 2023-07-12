module CQTS.DataStructures.Relation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv

open import CQTS.DataStructures.NaiveBST
open import CQTS.DataStructures.RBTrees
open import CQTS.DataStructures

open import Cubical.Structures.Auto

open import Cubical.Data.Bool hiding (_≤_; _≟_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary


open RBTrees
open BSTNaiveBST

-- transfer proofs of axioms   

-- define relation 
R : NaiveBST → RBTree → Type 
R nt rbt = ∀ n → member n nt ≡ memberRB n rbt

-- function from naive tree to red-black tree
φ : NaiveBST → RBTree
φ leaf = Empty
φ (node x leaf leaf) = Node Red Empty x Empty
φ (node x t1 t2) = 
    let rb1 = φ t1
        rb2 = φ t2
    in insertRB x (mergeRB rb1 rb2)

-- test example for φ
aTree : NaiveBST
aTree =  insert 10 (insert 9 ( insert 4 (insert 2 (insert 3 ( insert 7 (insert 5 leaf))))))


-- function from red-black tree to naive tree
ψ : RBTree → NaiveBST
ψ Empty = leaf
ψ (Node color Empty x Empty) = node x leaf leaf
ψ (Node color Empty x (Node color1 right x₂ right₁)) = node x leaf (ψ (Node color1 right x₂ right₁))
ψ (Node color (Node color2 left x₂ left₁) x Empty) = node x (ψ (Node color2 left x₂ left₁)) leaf
ψ (Node color (Node color3 left x₂ left₁) x (Node x₃ right x₄ right₁)) = node x (ψ (Node color3 left x₂ left₁))  (ψ (Node x₃ right x₄ right₁)) 

-- test example for ψ
anRBTree : RBTree
anRBTree = insertRB 22 (insertRB 10 (insertRB 18 ( insertRB 3 (insertRB 7 Empty))))

helper : (left right : NaiveBST) → (x : ℕ) → (n : ℕ) → member n (node x left right) ≡ memberRB n (φ (node x left right))
helper t1 leaf x n with n ≟ x
... | lt y = {!   !}
... | eq y = {!   !}
... | gt y = {!   !}
helper t1 (node x₂ right right₁) x n with n ≟ x
... | lt y = {!   !}
... | eq y = {!   !}
... | gt y = {!   !}


η' : (left right : NaiveBST) → (x : ℕ) → R left (φ left) → R right (φ right) → R (node x left right) (φ (node x left right))
η' left right x R_left R_right = {!  !}

η : ∀ xs → R xs (φ xs)
η leaf = λ n → refl
η (node x left right) = η' left right x (η left) (η right)

-- ε : ∀ y → R (ψ y) y
-- ε Empty p = refl 
-- ε (Node color l x r) = {!   !} 