module CQTS.DataStructures.SplayTree where

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

open import Cubical.Data.List


open import CQTS.DataStructures2

module SplayBST where
  open BST ℕ isSetℕ

  -- Splay tree
  data SplayBST : Type where
    leaf : SplayBST 
    node : ℕ → (left : SplayBST) → (right : SplayBST) → SplayBST
  
 
  rotateLeft : SplayBST → SplayBST
  rotateLeft (node x₁ left (node x₂ right₁ right₂)) = node x₂ (node x₁ left right₁) right₂
  rotateLeft t = t

  rotateRight : SplayBST → SplayBST
  rotateRight (node x₁ (node x₂ left₁ left₂) right) = node x₂ left₁ (node x₁ left₂ right)
  rotateRight t = t 

  rotateLeftWhenLRNotNull :  SplayBST → SplayBST
  rotateLeftWhenLRNotNull (node x (node x₁ left leaf) right) = (node x (node x₁ left leaf) right)
  rotateLeftWhenLRNotNull (node x (node x₁ left (node x₂ right₁ right₂)) right) = (node x (rotateLeft (node x₁ left (node x₂ right₁ right₂))) right)
  rotateLeftWhenLRNotNull t = t
  
  secondRotationZigZig : SplayBST → SplayBST
  secondRotationZigZig (node x leaf right) = node x leaf right
  secondRotationZigZig t = rotateRight t
  
  rotateRightWhenRLNotNull :  SplayBST → SplayBST
  rotateRightWhenRLNotNull (node x left (node x₁ leaf right)) = (node x left (node x₁ leaf right))
  rotateRightWhenRLNotNull (node x left (node x₁ (node x₂ left₁ left₂) right)) = (node x left (rotateRight (node x₁ (node x₂ left₁ left₂) right)))
  rotateRightWhenRLNotNull t = t
  
  secondRotationZagZag : SplayBST → SplayBST
  secondRotationZagZag (node x left leaf) = node x left leaf
  secondRotationZagZag t = rotateLeft t


  splay : SplayBST → (x : ℕ) → SplayBST
  splay leaf x = leaf
  splay (node x₁ left right) x with x₁ ≟ x 
  ... | eq _ = (node x₁ left right)
  splay (node x₁ left leaf) x | lt _ = (node x₁ left leaf)
  splay (node x₁ left (node x₂ right right₁)) x | lt _ with x₂ ≟ x
  ... | lt _ = secondRotationZagZag (rotateLeft (node x₁ left (node x₂ right (splay right₁ x) )))
  ... | eq _ = secondRotationZagZag (node x₁ left (node x₂ right right₁))
  ... | gt _ = secondRotationZagZag (rotateRightWhenRLNotNull (node x₁ left (node x₂ (splay right x) right₁)))
  splay (node x₁ leaf right) x | gt _ = (node x₁ leaf right)
  splay (node x₁ (node x₂ left left₁) right) x | gt _ with x₂ ≟ x
  ... | lt _ = secondRotationZigZig (rotateLeftWhenLRNotNull (node x₁ (node x₂ left left₁) (splay right x)))
  ... | eq _ = secondRotationZigZig (node x₁ (node x₂ left left₁) right)
  ... | gt _ = secondRotationZigZig (rotateRight (node x₁ (node x₂ (splay left x) left₁) right))


--   merge : SplayBST → SplayBST → SplayBST 
--   merge leaf right = right
--   merge left leaf = left
--   merge (node x left right) right' = node x left (merge right right') 

--   join : Maybe ℕ → SplayBST → SplayBST → SplayBST
--   join Nothing left right = merge left right
--   join (just x) left right = splay (merge left right) x


--   split : (x : ℕ) → SplayBST → (SplayBST × Maybe ℕ × SplayBST)
--   split x t = {! !}
 