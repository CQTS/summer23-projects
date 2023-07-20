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
  ... | lt _ = splitNaive x l
  ... | eq _ = l , just x , r
  ... | gt _ = splitNaive x r

  joinNaive : Maybe ℕ → SimpleBST → SimpleBST → SimpleBST
  joinNaive nothing leaf r = r
  joinNaive nothing (node x l r1) r = node x l (joinNaive nothing r1 r)
  joinNaive (just x) l r = node x l r 

  exposeNaive : SimpleBST → Maybe ( ℕ × SimpleBST × SimpleBST)
  exposeNaive leaf = nothing
  exposeNaive (node x l r) = just (x , l , r)

  -- search : (x : ℕ) → SimpleBST → Maybe ℕ
  -- search n t = fst (snd (splitNaive n t))


  -- insert : (x : ℕ) → SimpleBST → SimpleBST
  -- insert x t = 
  --   let 
  --     (l , _ , r) = splitNaive x t
  --   in 
  --     joinNaive (just x) l r

 -- show that simpleBST has a split-join structure
  NaiveRawStructure : RawBSTStructure SimpleBST
  NaiveRawStructure = leaf , splitNaive , joinNaive , exposeNaive 


          
