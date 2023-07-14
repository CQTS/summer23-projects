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

open import Cubical.Relation.ZigZag.Base
open import Cubical.Structures.Relational.Auto
open import Cubical.Structures.Relational.Macro
open import Cubical.Structures.Auto

open import Cubical.Data.Bool hiding (_≤_; _≟_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation

open RBTrees
open BSTNaiveBST
open BST-on

-- transfer proofs of axioms   

-- BSTShape2 : ∀ {ℓ} → Type ℓ → Type ℓ
-- BSTShape2 X = X × (ℕ → X → X) × (ℕ → X → Bool)
-- module S = RelMacro ℓ-zero (autoRelDesc (λ (X : Type ℓ-zero) → BSTShape2 X) )

-- define relation 
R : NaiveBST → RBTree → Type 
R nt rbt = ∀ n → member n nt ≡ memberRB n rbt

-- function from naive tree to red-black tree
φ : NaiveBST → RBTree
φ leaf = Empty
-- φ (node x leaf leaf) = Node Red Empty x Empty
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

-- prove relations 

-- rbt to nt
helper' : (color : Color) → (left right : RBTree) → (x : ℕ) → (n : ℕ) → member n (ψ (Node color left x right)) ≡ memberRB n (Node color left x right)
helper' color Empty Empty x n with n ≟ x
... | lt z = refl
... | eq z = refl
... | gt z = refl
helper' color Empty (Node color₁ right x₂ right₁) x n with n ≟ x
... | (lt z) = refl
... | (eq z) = refl
... | (gt z) = helper' color₁ right right₁ x₂ n
helper' color (Node color₁ left x₂ left₁) Empty x n with n ≟ x
... | (lt z) = helper' color₁ left left₁ x₂ n
... | (eq z) = refl
... | (gt z) = refl
helper' color (Node color₁ left x₂ left₁) (Node color₂ right x₄ right₁) x n with n ≟ x
... | (lt z) = helper' color₁ left left₁ x₂ n
... | (eq z) = refl
... | (gt z) = helper' color₂ right right₁ x₄ n

ε' : (color : Color) → (left right : RBTree) → (x : ℕ) → R (ψ left) left → R (ψ right) right → R (ψ (Node color left x right)) (Node color left x right)
ε' color left right x R_left R_right n = helper' color left right x n

ε : ∀ y → R (ψ y) y
ε Empty = λ n → refl
ε (Node color left x right) = ε' color left right x (ε left) (ε right)


-- nt to rbt 

-- helper to show balance preserves membership 
balancePreservesMembership : (clr : Color) (n m : ℕ) (l r : RBTree) → memberRB n (Node clr l m r) ≡ true → memberRB n (balance clr l m r) ≡ true 
balancePreservesMembership Red n m l r with n ≟ m
... | (lt x) = λ x → x
... | (eq x) = λ _ → refl
... | (gt x) = λ x → x
balancePreservesMembership Black n m Empty Empty with n ≟ m
... | (lt x) = λ x → x
... | (eq x) = λ x → x
... | (gt x) = λ x → x
balancePreservesMembership Black n m Empty (Node x r x₁ r₁) with n ≟ m
... | (lt x) = {! !}
... | (eq x) = {!   !}
... | (gt x) = {!   !}
balancePreservesMembership Black n m (Node x l x₁ l₁) Empty = {!   !}
balancePreservesMembership Black n m (Node x l x₁ l₁) (Node x₂ r x₃ r₁) = {!   !}

-- helper to show blackenRoot preserves membership 
blackenRootPreservesMembership :  (n : ℕ) (t : RBTree) → memberRB n t ≡ true → memberRB n (blackenRoot t) ≡ true 
blackenRootPreservesMembership n Empty = λ i → i
blackenRootPreservesMembership n (Node x t x₁ t₁) with n ≟ x₁
... | lt _ = λ i → i
... | eq _ = λ i → i
... | gt _ = λ i → i

-- helper to show ins preserves membership 
insPreservesMembership : (n m : ℕ) (t : RBTree) → memberRB n t ≡ true → memberRB n (ins m t) ≡ true
insPreservesMembership n m Empty with n ≟ m
... | (lt x) = λ x → x
... | (eq x) = {!   !}
... | (gt x) = λ x → x
insPreservesMembership n m (Node x t x₁ t₁) = {!   !} 


-- helper to show insert preserves membership (axiom 3 for rbt)
insertRBPreservesMembership :  (n m : ℕ) (t : RBTree) → memberRB n t ≡ true → memberRB n (insertRB m t) ≡ true -- Non-inserted element is not affected
insertRBPreservesMembership n m Empty with n ≟ m
... | (lt y) = λ y → y
... | (eq y) = λ y → refl
... | (gt y) = λ y → y
insertRBPreservesMembership n m (Node clr l x r) with m ≟ x  
insertRBPreservesMembership n m (Node clr l x r) | (lt z) with n ≟ x
... | (lt y) = {!   !}
... | (eq y) = {!   !}
... | (gt y) = {!   !} 
insertRBPreservesMembership n m (Node clr l x r) | (eq z) with n ≟ x 
... | (lt y) = λ y → y
... | (eq y) = λ y → y 
... | (gt y) = λ y → y 
insertRBPreservesMembership n m (Node clr l x r) | (gt z) with n ≟ x 
... | (lt y) = {!   !}
... | (eq y) = {!   !}
... | (gt y) = {!   !} 

-- helper to show merge preserves membership 
mergePreservesMembership : (n : ℕ) (t1 t2  : RBTree) → memberRB n t1 ≡ true → memberRB n (mergeRB t1 t2) ≡ true
mergePreservesMembership n t1 Empty = λ i → i
mergePreservesMembership n t1 (Node x t2 x₁ t3) = {!   !}

-- helper to show relation between member and memberRB
helper : (left right : NaiveBST) → (x : ℕ) → (n : ℕ) → member n (node x left right) ≡ memberRB n (φ (node x left right))
helper t1 leaf x n with n ≟ x
... | lt y = {!   !}
... | eq y = {!   !}
... | gt y = {!   !}
helper t1 (node x₂ right right₁) x n with n ≟ x
... | lt y = {!   !}
... | eq y = {!   !}
... | gt y = {!   !}

-- helper leaf leaf x n with n ≟ x
-- ... | lt y = refl
-- ... | eq y = refl
-- ... | gt y = refl
-- helper leaf (node x₂ right right₁) x n with n ≟ x
-- ... | lt y = {!    !}
-- ... | eq y = {!   !}
-- ... | gt y = {!   !}
-- helper (node x₂ left left₁) leaf x n with n ≟ x
-- ... | lt y = {!   !}
-- ... | eq y = {!   !}
-- ... | gt y = {!   !}
-- helper (node x₂ left left₁)  (node x₃ right right₁) x n with n ≟ x
-- ... | lt y = {!   !}
-- ... | eq y = {!   !}
-- ... | gt y = {!   !}


η' : (left right : NaiveBST) → (x : ℕ) → R left (φ left) → R right (φ right) → R (node x left right) (φ (node x left right))
η' left right x R_left R_right n = helper left right x n

η : ∀ xs → R xs (φ xs)
η leaf = λ n → refl
η (node x left right) = η' left right x (η left) (η right)



open isQuasiEquivRel

-- prove that R is a quasi equivalence relation
QuasiR : QuasiEquivRel NaiveBST RBTree ℓ-zero
QuasiR .fst .fst = R
QuasiR .fst .snd a b = isPropΠ λ x → isSetBool (member x a)  (memberRB x b)
QuasiR .snd .zigzag r r' r'' = λ n → (r n) ∙∙ sym (r' n) ∙∙ (r'' n)
QuasiR .snd .fwd a = ∣ φ a , η a ∣₁
QuasiR .snd .bwd b = ∣ ψ b , ε b ∣₁

isStructuredInsert : {t : NaiveBST} {rb : RBTree} (x : ℕ) 
    → R t rb → R (insert x t) (insertRB x rb)
isStructuredInsert {t} {rb} x r = {!   !}

isStructuredMember : {t : NaiveBST} {rb : RBTree} (x : ℕ) 
    → R t rb → member x t ≡ memberRB x rb
isStructuredMember {t} {rb} x r = r x


-- R itself should be structured 
-- isStructuredR : BSTStructure R Raw RawRBTree
-- isStructuredR = {!   !}