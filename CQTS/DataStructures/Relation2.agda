module CQTS.DataStructures.Relation2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv

open import CQTS.DataStructures.BST
open import CQTS.DataStructures.SplayTree
open import CQTS.DataStructures2

open import Cubical.Relation.ZigZag.Base
open import Cubical.Structures.Relational.Auto
open import Cubical.Structures.Relational.Macro
open import Cubical.Structures.Auto

open import Cubical.Data.Bool hiding (_≤_; _≟_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation

open NaiveBST
open SplayBST
open BST

-- transfer proofs of axioms   

-- define relation 
R : SimpleBST → SplayBST → Type 
R nt st = ∀ n → memberNaive nt n ≡ memberSplay st n

-- function from naive tree to splay tree
φ : SimpleBST → SplayBST
φ leaf = leaf
φ (node x left right) = node x (φ left) (φ right)

-- test example for φ
aTree : SimpleBST
aTree =  insertNaive 10 (insertNaive 9 ( insertNaive 4 (insertNaive 2 (insertNaive 3 ( insertNaive 7 (insertNaive 5 leaf))))))

-- alternate implementation
ψ : SplayBST → SimpleBST
ψ leaf = leaf
ψ (node x left right) = node x (ψ left) (ψ right)

-- test example for ψ
aSplayTree : SplayBST
aSplayTree = insertSplay 15 (insertSplay 22 (insertSplay 10 (insertSplay 18 ( insertSplay 3 (insertSplay 7 leaf)))))

-- prove relations 

-- splay tree to naive tree
-- helper : (left right : SplayBST) → (x : ℕ) → (n : ℕ) → memberNaive (ψ (node x left right)) n ≡ memberSplay (node x left right) n
-- helper leaf leaf x n with n ≟ x 
-- helper leaf leaf x n | gt x₁ with x ≟ n
-- helper leaf leaf x n | gt x₁ | lt x₂ with n ≟ x
-- helper leaf leaf x n | gt x₁ | lt x₂ | lt x₃ = refl
-- helper leaf leaf x n | gt x₁ | lt x₂ | eq x₃ = ⊥.rec {!   !}
-- helper leaf leaf x n | gt x₁ | lt x₂ | gt x₃ = refl
-- helper leaf leaf x n | gt x₁ | eq x₂ with n ≟ x 
-- helper leaf leaf x n | gt x₁ | eq x₂ | lt x₃ = refl
-- helper leaf leaf x n | gt x₁ | eq x₂ | eq x₃ = ⊥.rec {!   !}
-- helper leaf leaf x n | gt x₁ | eq x₂ | gt x₃ = refl
-- helper leaf leaf x n | gt x₁ | gt x₂ with n ≟ x
-- helper leaf leaf x n | gt x₁ | gt x₂ | lt x₃ = refl
-- helper leaf leaf x n | gt x₁ | gt x₂ | eq x₃ = ⊥.rec {!   !}
-- helper leaf leaf x n | gt x₁ | gt x₂ | gt x₃ = refl
-- helper leaf leaf x n | eq x₁ with x ≟ n 
-- helper leaf leaf x n | eq x₁ | lt x₂ with n ≟ x
-- helper leaf leaf x n | eq x₁ | lt x₂ | lt x₃ = ⊥.rec {!   !}
-- helper leaf leaf x n | eq x₁ | lt x₂ | eq x₃ = refl
-- helper leaf leaf x n | eq x₁ | lt x₂ | gt x₃ = ⊥.rec {!   !}
-- helper leaf leaf x n | eq x₁ | eq x₂ = {!   !}
-- helper leaf leaf x n | eq x₁ | gt x₂ = {!   !}
-- helper leaf leaf x n | lt x₁ with x ≟ n  
-- helper leaf leaf x n | lt x₁ | gt x₂ with n ≟ x 
-- helper leaf leaf x n | lt x₁ | gt x₂ | lt x₃ = refl
-- helper leaf leaf x n | lt x₁ | gt x₂ | eq x₃ = ⊥.rec {!   !}
-- helper leaf leaf x n | lt x₁ | gt x₂ | gt x₃ = refl
-- helper leaf leaf x n | lt x₁ | eq x₂ with n ≟ x
-- helper leaf leaf x n | lt x₁ | eq x₂ | lt x₃ = refl
-- helper leaf leaf x n | lt x₁ | eq x₂ | eq x₃ = ⊥.rec {!  !}
-- helper leaf leaf x n | lt x₁ | eq x₂ | gt x₃ = refl
-- helper leaf leaf x n | lt x₁ | lt x₂ with n ≟ x
-- helper leaf leaf x n | lt x₁ | lt x₂ | lt x₃ = refl
-- helper leaf leaf x n | lt x₁ | lt x₂ | eq x₃ = ⊥.rec {!   !}
-- helper leaf leaf x n | lt x₁ | lt x₂ | gt x₃ = refl



-- helper : (left right : SplayBST) → (x : ℕ) → (n : ℕ) → memberNaive (ψ (node x left right)) n ≡ memberSplay (node x left right) n
-- helper leaf right x n  with x ≟ n 
-- helper leaf right x n | gt _ with n ≟ x
-- helper leaf right x n | gt _ | gt _ = {!   !}
-- helper leaf right x n | gt _ | eq _ = refl
-- helper leaf right x n | gt _ | lt _ = refl
-- helper leaf right x n | eq _ = {!   !}
-- helper leaf right x n | lt _ = {!   !}
-- helper (node x₁ left left₁) right x n with x ≟ n 
-- helper (node x₁ left left₁) right x n | gt _ with n ≟ x
-- helper (node x₁ left left₁) right x n | gt _ | gt _ with x₁ ≟ n
-- helper (node x₁ leaf left₁) leaf x n | gt _ | gt _ | gt _ with n ≟ x₁
-- helper (node x₁ leaf left₁) leaf x n | gt _ | gt _ | gt _ | gt _ = refl
-- helper (node x₁ leaf left₁) leaf x n | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ leaf left₁) leaf x n | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₂ left left₂) left₁) leaf x n | gt _ | gt _ | gt _ with x₂ ≟ n
-- helper (node x₁ (node x₂ leaf left₂) left₁) leaf x n | gt _ | gt _ | gt _ | gt _ with n ≟ x₂ 
-- helper (node x₁ (node x₂ leaf left₂) left₁) leaf x n | gt _ | gt _ | gt _ | gt _ | gt _ = refl
-- helper (node x₁ (node x₂ leaf left₂) left₁) leaf x n | gt _ | gt _ | gt _ | gt _ | eq _ =  {!   !}
-- helper (node x₁ (node x₂ leaf left₂) left₁) leaf x n | gt _ | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₂ (node x₃ left left₃) left₂) left₁) leaf x n | gt _ | gt _ | gt _ | gt _ = {!   !}
-- helper (node x₁ (node x₂ leaf left₂) left₁) leaf x n | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ (node x₂ (node x₃ left left₃) left₂) left₁) leaf x n | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ (node x₂ left left₂) left₁) leaf x n | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ left left₁) (node x₂ right right₁) x n | gt _ | gt _ | gt _ = {!   !}
-- helper (node x₁ left left₁) right x n | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ left left₁) right x n | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ left left₁) right x n | gt _ | eq _ = {!   !}
-- helper (node x₁ left left₁) right x n | gt _ | lt _ = {!   !}
-- helper (node x₁ left left₁) right x n | eq _ = {!   !}
-- helper (node x₁ left left₁) right x n | lt _ = {!   !}

-- helper leaf leaf x n with n ≟ x 
-- helper leaf leaf x n | gt x₁ with x ≟ n 
-- helper leaf leaf x n | gt x₁ | gt x₂ with n ≟ x 
-- helper leaf leaf x n | gt x₁ | gt x₂ | gt x₃ = {!   !}
-- helper leaf leaf x n | gt x₁ | gt x₂ | eq x₃ = {!   !}
-- helper leaf leaf x n | gt x₁ | gt x₂ | lt x₃ = {!   !}
-- helper leaf leaf x n | gt x₁ | eq x₂ = {!   !}
-- helper leaf leaf x n | gt x₁ | lt x₂ = {!   !}
-- helper leaf leaf x n | eq x₁ = {!   !}
-- helper leaf leaf x n | lt x₁ = {!   !}
-- helper leaf (node x₁ t2 t3) x n = {!   !}
-- helper (node x₁ t1 t2) leaf x n = {!   !}
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n with n ≟ x 
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | gt _ with n ≟ x₂ 
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | gt _ | gt _ with x ≟ n 
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | gt _ | gt _ | gt _ with x₁ ≟ n 
-- helper (node x₁ leaf t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ with n ≟ x₁
-- helper (node x₁ leaf t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ = refl
-- helper (node x₁ leaf t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ leaf t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₃ t1 t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ with x₃ ≟ n
-- helper (node x₁ (node x₃ leaf t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ with n ≟ x₃ 
-- helper (node x₁ (node x₃ leaf t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ = refl
-- helper (node x₁ (node x₃ leaf t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ leaf t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ t1 t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ with x₄ ≟ n 
-- helper (node x₁ (node x₃ (node x₄ leaf t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with n ≟ x₄
-- helper (node x₁ (node x₃ (node x₄ leaf t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ leaf t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ leaf t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ t1 t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with x₅ ≟ n 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ leaf t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with n ≟ x₅
-- helper (node x₁ (node x₃ (node x₄ (node x₅ leaf t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ leaf t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ leaf t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with x₆ ≟ n 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with n ≟ x₆ 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ =  {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ with x₆ ≟ n
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | lt _ with n ≟ x₆ 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | lt _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | lt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | lt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | eq _ with n ≟ x₆ 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | eq _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | eq _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | eq _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | gt _ with n ≟ x₆ 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | gt _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf leaf) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ with n ≟ x₆ 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf leaf) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf leaf) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf leaf) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf (node x₇ t7 t8)) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ with n ≟ x₇
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf (node x₇ t7 t8)) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf (node x₇ t7 t8)) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ leaf (node x₇ t7 t8)) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ t1 t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with x₆ ≟ n 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ t1 t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with x₇ ≟ n
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ leaf t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with n ≟ x₇ 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ leaf t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ leaf t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ leaf t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ t1 t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with x₈ ≟ n 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ leaf t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with n ≟ x₈ 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ leaf t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ = refl 
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ leaf t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ leaf t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ t1 t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with x₉ ≟ n
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ leaf t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with n ≟ x₉
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ leaf t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ leaf t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ leaf t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ (node x₁₀ t1 t11) t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with x₁₀ ≟ n
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ (node x₁₀ leaf t11) t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with n ≟ x₁₀
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ (node x₁₀ leaf t11) t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ (node x₁₀ leaf t11) t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ (node x₁₀ leaf t11) t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = refl
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ (node x₁₀ (node x₁₁ t1 t12) t11) t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ with x₁₁ ≟ n = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ (node x₁₀ t1 t11) t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ (node x₁₀ t1 t11) t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ t1 t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ (node x₉ t1 t10) t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ t1 t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ (node x₈ t1 t9) t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ t1 t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ t1 t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ t1 t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ (node x₆ (node x₇ t1 t8) t7) t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ t1 t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ (node x₅ t1 t6) t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ t1 t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ (node x₄ t1 t5) t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ (node x₃ t1 t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ (node x₃ t1 t4) t2) (node x₂ t3 leaf) x n | gt _ | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ t1 t2) (node x₂ t3 (node x₃ t4 t5)) x n | gt _ | gt _ | gt _ | gt _ = {!   !}
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | gt _ | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | gt _ | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | gt _ | gt _ | eq _ = {!   !}
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | gt _ | gt _ | lt _ = {!   !}
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | gt _ | eq _ = {!   !}
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | gt _ | lt _ = {!   !}
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | eq x₃ = {!   !}
-- helper (node x₁ t1 t2) (node x₂ t3 t4) x n | lt x₃ = {!   !}

helper : (left right : SplayBST) → (x : ℕ) → (n : ℕ) → memberNaive (ψ (node x left right)) n ≡ memberSplay (node x left right) n
helper left right x n = {!   !}

ε' : (x : ℕ) → (left right : SplayBST) → R (ψ left) left → R (ψ right) right → R (ψ (node x left right)) (node x left right)
ε' x left right R_left R_right n = helper left right x n

ε : ∀ y → R (ψ y) y
ε leaf = λ n → refl
ε (node x left right) = ε' x left right (ε left) (ε right)

helper' : (left right : SimpleBST) → (x : ℕ) → (n : ℕ) → memberNaive (node x left right) n ≡ memberSplay (node x (φ left) (φ right)) n
helper' leaf right x n = {!   !}
helper' (node x₁ left left₁) right x n with x ≟ n 
helper' (node x₁ left left₁) right x n | lt _ with n ≟ x 
helper' (node x₁ left left₁) right x n | lt _ | lt _ = {!   !}
helper' (node x₁ left left₁) right x n | lt _ | eq _ = {!   !}
helper' (node x₁ left left₁) right x n | lt _ | gt _ = {!   !}
helper' (node x₁ left left₁) right x n | eq _ = {!   !}
helper' (node x₁ left left₁) right x n | gt _ = {!   !}

η' : (left right : SimpleBST) → (x : ℕ) → R left (φ left) → R right (φ right) → R (node x left right) (φ (node x left right))
η' left right x R_left R_right n = helper' left right x n

η : ∀ xs → R xs (φ xs)
η leaf = λ n → refl
η (node x left right) = η' left right x (η left) (η right)


-- open isQuasiEquivRel

-- -- prove that R is a quasi equivalence relation
-- QuasiR : QuasiEquivRel NaiveBST RBTree ℓ-zero
-- QuasiR .fst .fst = R
-- QuasiR .fst .snd a b = isPropΠ λ x → isSetBool (member x a)  (memberRB x b)
-- QuasiR .snd .zigzag r r' r'' = λ n → (r n) ∙∙ sym (r' n) ∙∙ (r'' n)
-- QuasiR .snd .fwd a = ∣ φ a , η a ∣₁
-- QuasiR .snd .bwd b = ∣ ψ b , ε b ∣₁

-- isStructuredInsert : {t : NaiveBST} {rb : RBTree} (x : ℕ) 
--     → R t rb → R (insert x t) (insertRB x rb)
-- isStructuredInsert {t} {rb} x r = {!   !}

-- isStructuredMember : {t : NaiveBST} {rb : RBTree} (x : ℕ) 
--     → R t rb → member x t ≡ memberRB x rb
-- isStructuredMember {t} {rb} x r = r x

-- -- R itself should be structured
-- isStructuredR : RawBSTRelStr ℕ isSetℕ R NaiveRawStructure RBRawStructure
-- isStructuredR = {!!}
 