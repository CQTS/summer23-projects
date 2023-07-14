module CQTS.DataStructures.NaiveBST where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv

open import Cubical.Structures.Auto

open import Cubical.Data.Bool hiding (_≤_; _≟_; _≥_)
open import Cubical.Data.Nat 
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Structures.Macro
open import Cubical.Structures.Axioms
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import CQTS.DataStructures

module BSTNaiveBST where
  open BST-on ℕ isSetℕ

  -- A naive implementation of BSTs, where the tree is either empty or a node
  data NaiveBST : Type where
    leaf : NaiveBST
    node  : ℕ → (left : NaiveBST) → (right : NaiveBST) → NaiveBST
  
  -- Insert an element into a tree
  insert : (x : ℕ) → NaiveBST → NaiveBST
  insert x leaf = node x leaf leaf
  insert x (node y l r) with x ≟ y
  ... | (lt _) = node y (insert x l) r
  ... | (eq _) = node y l r
  ... | (gt _) = node y l (insert x r)

  -- Check if an element is in a tree
  member : (x : ℕ) → NaiveBST → Bool
  member x leaf = false
  member x (node y l r) with x ≟ y
  ... | (lt _) = member x l
  ... | (eq _) = true
  ... | (gt _) = member x r

  NaiveRawStructure : RawBSTStructure NaiveBST
  NaiveRawStructure = leaf , insert , member

  Raw : RawBST
  Raw = NaiveBST , NaiveRawStructure

  NaiveWithLaws : BST
  NaiveWithLaws = NaiveBST , S , isSetNaiveBST , emptyNaiveBST , 
    insertedElementIsMember , insertPreservesMembership , isMemberAfterInsertion
    where 
      S = str Raw

      get-n : (t : NaiveBST) → ℕ
      get-n leaf = 0
      get-n (node x t t₁) = x

      get-left : (t : NaiveBST) → NaiveBST
      get-left leaf = leaf
      get-left (node x t t₁) = t

      get-right : (t : NaiveBST) → NaiveBST
      get-right leaf = leaf
      get-right (node x t t1) = t1

      n-path : {x y : ℕ} → {t1 t2 s1 s2 : NaiveBST} → (p : node x t1 t2 ≡ node y s1 s2) → x ≡ y
      n-path p i = get-n (p i)

      right-path : {x y : ℕ} {t1 t2 s1 s2 : NaiveBST} → (p : node x t1 t2 ≡ node y s1 s2) → t2 ≡ s2
      right-path p = cong get-right p

      left-path : {x y : ℕ} {t1 t2 s1 s2 : NaiveBST} → (p : node x t1 t2 ≡ node y s1 s2) → t1 ≡ s1
      left-path p = cong get-left p

      node-path : {x y : ℕ} {t1 t2 s1 s2 : NaiveBST} → (p1 : x ≡ y) → (p2 : t1 ≡ s1) → (p3 : t2 ≡ s2) → node x t1 t2 ≡ node y s1 s2
      node-path p1 p2 p3 i = node (p1 i) (p2 i) (p3 i)

      data ⊤ : Type₀ where
        tt : ⊤

      _≡Naive_ : (a b : NaiveBST) → Type
      leaf ≡Naive leaf = ⊤
      leaf ≡Naive node x b b₁ = ⊥
      node x a a₁ ≡Naive leaf = ⊥
      node x t1 t2 ≡Naive node y s1 s2 with x ≟ y
      ... | (lt _) = ⊥
      ... | (eq _) = (t1 ≡Naive s1) × (t2 ≡Naive s2)
      ... | (gt _) = ⊥

      leaf≢node : (x : ℕ) → (t1 t2 : NaiveBST) → ¬ leaf ≡ node x t1 t2
      leaf≢node x t1 t2 p =  subst (λ n → leaf ≡Naive n) p tt

      hasDecEqNaiveBST : (x y : NaiveBST) → Dec (x ≡ y)
      hasDecEqNaiveBST leaf leaf = yes refl
      hasDecEqNaiveBST leaf (node x y y₁) = no (leaf≢node x y y₁)
      hasDecEqNaiveBST (node x x₁ x₂) leaf = no (leaf≢node x x₁ x₂ ∘ sym)
      hasDecEqNaiveBST (node x t1 t2) (node y s1 s2) with discreteℕ x y 
      
      hasDecEqNaiveBST (node x t1 t2) (node y s1 s2) | yes p with hasDecEqNaiveBST t1 s1
      hasDecEqNaiveBST (node x t1 t2) (node y s1 s2) | yes p | yes q with hasDecEqNaiveBST t2 s2
      hasDecEqNaiveBST (node x t1 t2) (node y s1 s2) | yes p | yes q | yes r = yes (node-path p q r)
      hasDecEqNaiveBST (node x t1 t2) (node y s1 s2) | yes p | yes q | no r = no λ e → r (right-path e)
      hasDecEqNaiveBST (node x t1 t2) (node y s1 s2) | yes p | no c = no λ q → c (left-path q)

      hasDecEqNaiveBST (node x t1 t2) (node y s1 s2) | no c = no λ q → c (n-path q)


      isSetNaiveBST : isSet NaiveBST
      isSetNaiveBST = Discrete→isSet hasDecEqNaiveBST 
          

      -- prove axioms 
      -- axiom 1 
      emptyNaiveBST : (n : ℕ) → member n leaf ≡ false
      emptyNaiveBST n = refl 

      -- axiom 2
      insertedElementIsMember : (n :  ℕ) ( t : NaiveBST) → member n (insert n t ) ≡ true
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
      insertPreservesMembership :  (n m : ℕ) (t : NaiveBST) → member n t ≡ true → member n (insert m t) ≡ true -- Non-inserted element is not affected
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
      isMemberAfterInsertion : (n m : ℕ) (t : NaiveBST) → ( ¬ ( n ≡ m ) ) → (member n (insert m t) ≡ true → member n t ≡ true)
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