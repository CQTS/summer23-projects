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
φ (node x left right) = let 
    l = φ left
    r = φ right
  in 
    insertSplay x (joinSplay nothing l r) 

-- test example for φ
aTree : SimpleBST
aTree =  insertNaive 10 (insertNaive 9 ( insertNaive 4 (insertNaive 2 (insertNaive 3 ( insertNaive 7 (insertNaive 5 leaf))))))

-- alternate implementation
ψ : SplayBST → SimpleBST
ψ leaf = leaf
ψ (node x left right) = 
  let 
    l = ψ left
    r = ψ right
  in 
    insertNaive x (joinNaive nothing l r)

-- test example for ψ
aSplayTree : SplayBST
aSplayTree = insertSplay 15 (insertSplay 22 (insertSplay 10 (insertSplay 18 ( insertSplay 3 (insertSplay 7 leaf)))))

-- prove relations 

-- splay tree to naive tree
helper : (left right : SplayBST) → (x : ℕ) → (n : ℕ) → memberNaive (ψ (node x left right)) n ≡ memberSplay (node x left right) n
helper leaf leaf x n with n ≟ x 
helper leaf leaf x n | gt x₁ with x ≟ n
helper leaf leaf x n | gt x₁ | lt x₂ with n ≟ x
helper leaf leaf x n | gt x₁ | lt x₂ | lt x₃ = refl
helper leaf leaf x n | gt x₁ | lt x₂ | eq x₃ = ⊥.rec {!   !}
helper leaf leaf x n | gt x₁ | lt x₂ | gt x₃ = refl
helper leaf leaf x n | gt x₁ | eq x₂ with n ≟ x 
helper leaf leaf x n | gt x₁ | eq x₂ | lt x₃ = refl
helper leaf leaf x n | gt x₁ | eq x₂ | eq x₃ = ⊥.rec {!   !}
helper leaf leaf x n | gt x₁ | eq x₂ | gt x₃ = refl
helper leaf leaf x n | gt x₁ | gt x₂ with n ≟ x
helper leaf leaf x n | gt x₁ | gt x₂ | lt x₃ = refl
helper leaf leaf x n | gt x₁ | gt x₂ | eq x₃ = ⊥.rec {!   !}
helper leaf leaf x n | gt x₁ | gt x₂ | gt x₃ = refl
helper leaf leaf x n | eq x₁ with x ≟ n 
helper leaf leaf x n | eq x₁ | lt x₂ with n ≟ x
helper leaf leaf x n | eq x₁ | lt x₂ | lt x₃ = ⊥.rec {!   !}
helper leaf leaf x n | eq x₁ | lt x₂ | eq x₃ = refl
helper leaf leaf x n | eq x₁ | lt x₂ | gt x₃ = ⊥.rec {!   !}
helper leaf leaf x n | eq x₁ | eq x₂ = {!   !}
helper leaf leaf x n | eq x₁ | gt x₂ = {!   !}
helper leaf leaf x n | lt x₁ with x ≟ n  
helper leaf leaf x n | lt x₁ | gt x₂ with n ≟ x 
helper leaf leaf x n | lt x₁ | gt x₂ | lt x₃ = refl
helper leaf leaf x n | lt x₁ | gt x₂ | eq x₃ = ⊥.rec {!   !}
helper leaf leaf x n | lt x₁ | gt x₂ | gt x₃ = refl
helper leaf leaf x n | lt x₁ | eq x₂ with n ≟ x
helper leaf leaf x n | lt x₁ | eq x₂ | lt x₃ = refl
helper leaf leaf x n | lt x₁ | eq x₂ | eq x₃ = ⊥.rec {!  !}
helper leaf leaf x n | lt x₁ | eq x₂ | gt x₃ = refl
helper leaf leaf x n | lt x₁ | lt x₂ with n ≟ x
helper leaf leaf x n | lt x₁ | lt x₂ | lt x₃ = refl
helper leaf leaf x n | lt x₁ | lt x₂ | eq x₃ = ⊥.rec {!   !}
helper leaf leaf x n | lt x₁ | lt x₂ | gt x₃ = refl



helper leaf (node x₁ right right₁) x n = {!   !}

helper (node x₁ left left₁) leaf x n = {!   !}
helper (node x₁ left left₁) (node x₂ right right₁) x n = {!   !}

ε' : (x : ℕ) → (left right : SplayBST) → R (ψ left) left → R (ψ right) right → R (ψ (node x left right)) (node x left right)
ε' x left right R_left R_right n = helper left right x n

ε : ∀ y → R (ψ y) y
ε leaf = λ n → refl
ε (node x left right) = ε' x left right (ε left) (ε right)

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
 