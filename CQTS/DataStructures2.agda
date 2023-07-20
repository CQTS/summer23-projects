module CQTS.DataStructures2 where

open import Cubical.Structures.Macro
open import Cubical.Structures.Axioms
open import Cubical.Structures.Relational.Auto

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv

open import Cubical.Structures.Auto
open import Cubical.Structures.Relational.Auto
open import Cubical.Structures.Relational.Macro

open import Cubical.Data.Int hiding (sucℤ; _+_)
open import Cubical.Core.Everything


open import Cubical.Data.Bool hiding (_≤_; _≟_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe
open import Cubical.Relation.Nullary


private
  variable
   ℓ : Level


module BST (A : Type ℓ) (Aset : isSet A) where
-- Our BST structure has three main components an empty tree, a split function and a join function

  BstShape : Type ℓ → Type ℓ
  BstShape X = X × (A → X → (X × Maybe (Const[ A , Aset ]) × X))
                 × (Maybe A → X → X → X)
                 × (X → Maybe (Const[ A , Aset ] × X × X))


  open RelMacro ℓ (autoRelDesc BstShape) public renaming
    ( structure to RawBSTStructure
    ; equiv to RawBSTEquivStr
    ; univalent to rawBSTUnivalentStr
    ; relation to RawBSTRelStr
    ; suitable to rawBSTSuitableRel
    ; matches to rawBSTMatchesEquiv
    )

  module _ {TreeStr : TypeWithStr ℓ RawBSTStructure} where
    Tree = fst TreeStr
    emptyTree : Tree
    emptyTree = fst (snd TreeStr)
    split : A → Tree → (Tree × Maybe A × Tree)
    split = fst (snd (snd TreeStr))
    join : Maybe A → Tree → Tree → Tree
    join =  fst (snd (snd (snd TreeStr)))
    expose : Tree → Maybe (A × Tree × Tree)
    expose = snd (snd (snd (snd TreeStr)))

    search : (x : A) → Tree → Maybe A
    search n t = let (_ , found , _) = split n t in found

    insert : (x : A) → Tree → Tree 
    insert x  t = 
      let 
        (l , _ , r) = split x t
      in 
        join (just x) l r

    delete : (x : A) → Tree → Tree
    delete x t = 
      let 
        (l , _ , r) = split x t
      in 
        join nothing l r

    member : (x : A) → Tree → Bool 
    member x t with (fst (snd (split x t)))
    ... | nothing = false
    ... | just x = true


    -- We mark the following functions as TERMINATING because Agda does not know that `expose` and `split` always reduce the size of the tree.
    {-# TERMINATING #-}
    union : (T1 T2 : Tree) → Tree
    union T1 T2 with (expose T1)
    ... | nothing = T2
    ... | just (x1 , l1 , r1) = 
            let 
              (l2 , x2 , r2) = split x1 T2 
              L = union l1 l2 
              R = union r1 r2
            in join (just x1) L R

