module CQTS.DataStructures.BST where

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

module NaiveBST where
  open BST ℕ  isSetℕ

  data SimpleBST : Type where
    leaf : SimpleBST 
    node : ℕ → (left : SimpleBST) → (right : SimpleBST) → SimpleBST

  splitNaive : (x : ℕ) → SimpleBST → (SimpleBST × Maybe ℕ × SimpleBST)
  splitNaive x leaf = leaf , nothing , leaf
  splitNaive x (node val l r) with x ≟ val
  ... | lt _ = let (l' , m , r') = splitNaive x l in (l' , m , node val r' r)
  ... | eq _ = l , just val , r
  ... | gt _ = let (l' , m , r') = splitNaive x r in (node val l l' , m , r')

  joinNaive : Maybe ℕ → SimpleBST → SimpleBST → SimpleBST
  joinNaive nothing leaf r = r
  joinNaive nothing (node x l r1) r = node x l (joinNaive nothing r1 r)
  joinNaive (just x) l r = node x l r 

  exposeNaive : SimpleBST → Maybe ( ℕ × SimpleBST × SimpleBST)
  exposeNaive leaf = nothing
  exposeNaive (node x l r) = just (x , l , r)

  searchNaive : (x : ℕ) → SimpleBST → Maybe ℕ
  searchNaive n t = fst (snd (splitNaive n t))

  insertNaive : (x : ℕ) → SimpleBST → SimpleBST
  insertNaive x t = 
    let 
      (l , _ , r) = splitNaive x t
    in 
      joinNaive (just x) l r

  memberNaive : SimpleBST → (x : ℕ) → Bool
  memberNaive t x with (fst (snd (splitNaive x t)))
  ... | nothing = false
  ... | just x = true
                                             
 -- show that simpleBST has a split-join structure
  NaiveRawStructure : RawBSTStructure SimpleBST
  NaiveRawStructure = leaf , splitNaive , joinNaive , exposeNaive 


          
