module CQTS.BraidGroups.TaffyStructure where

open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

open import Cubical.HITs.S1
open import Cubical.HITs.Bouquet

open import Cubical.Structures.Macro
open import Cubical.Structures.Auto

open import CQTS.BraidGroups

module _ {ℓ} (n : ℕ) where

  taffyDesc : Desc ℓ ℓ ℓ
  taffyDesc = autoDesc (λ (X : Type ℓ) → (S¹ → X) × (Fin n → (S¹ → X)))

  open Macro ℓ taffyDesc public renaming
    ( structure to TaffyStructure
    ; equiv to TaffyEquivStr
    ; univalent to taffyUnivalentStr
    )

-- ConditionOne : 

BouquetInstance : ∀ n → TaffyStructure n (Bouquet (Fin n))
BouquetInstance n = circMap n , {!   !}