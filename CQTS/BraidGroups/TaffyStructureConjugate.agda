module homework-solutions.Extra.TaffyStructureConjugate where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Group
open import Cubical.HITs.Bouquet
open import Cubical.HITs.S1

open import Cubical.Data.Fin
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; znots; predℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData.Base using(predFin)
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP
open import Cubical.Structures.Pointed
open import Cubical.HITs.S1.Base

open import Cubical.HITs.S1
open import Cubical.HITs.Bouquet

open import Cubical.Structures.Macro
open import Cubical.Structures.Auto

private
   variable
      ℓ ℓ' : Level

module _ {ℓ} (n : ℕ) where

  taffyDesc : Desc ℓ ℓ ℓ
  taffyDesc = autoDesc (λ (X : Type ℓ) → (S¹ → X) × (Fin n → (S¹ → X)))

  open Macro ℓ taffyDesc public renaming
    ( structure to TaffyStructure
    ; equiv to TaffyEquivStr
    ; univalent to TaffyUnivalentStr
    )

circleHelper : (k : ℕ) →  (n : ℕ) → (k < n) →  S¹ → Bouquet (Fin n)
circleHelper k n _ base = base
circleHelper k zero _ s = base
circleHelper zero (suc n) _ (loop i) = loop (zero , suc-≤-suc zero-≤) i
circleHelper (suc k) (suc n) p (loop i) = ( (λ j → circleHelper k (suc n) (suc-< p) (loop j)) ∙ loop (suc k , p )) i

circToBouq : (n : ℕ) → S¹ → Bouquet (Fin n)
circToBouq zero s = base
circToBouq (suc n) s = circleHelper n (suc n) ≤-refl s

BouquetInstance : ∀ n → TaffyStructure n (Bouquet (Fin n))
BouquetInstance n = circToBouq n , λ x y → circToBouq n y

unwoundEquivStr : ∀ n → (A B : TypeWithStr ℓ (TaffyStructure n)) 
                  → (typ A ≃ typ B) → Type ℓ
-- * Preserving 1) boundary loop & 2) generator loops
unwoundEquivStr n (A , Abd , Agens) (B , Bbd , Bgens) f = ((s : S¹) → equivFun f (Abd s) ≡ Bbd s) 
                                                        × ((k : Fin n) → (s : S¹) → equivFun f (Agens k s) ≡ (Bgens k s))
-- ? equivFun : [...] → A ≃ B → A → B
-- ? equivFun f = equivFun (typ A ≃ typ B) → typ A → typ B

tmp : TaffyEquivStr ≡ unwoundEquivStr
tmp = refl

unwoundSIP : ∀ n → {A B : TypeWithStr ℓ (TaffyStructure n)}
             → A ≃[ unwoundEquivStr n ] B ≃ (A ≡ B)
-- * Equivalences within unwoundEquivStr are the same as
-- * paths in the type of all taffy-structured types
unwoundSIP n {A} {B} = SIP (TaffyUnivalentStr n) A B

BouquetWithStr : ∀ n → TypeWithStr ℓ-zero (TaffyStructure n)
BouquetWithStr n = Bouquet (Fin n) , BouquetInstance n

l : (n : ℕ) → BouquetWithStr n ≡ BouquetWithStr n
l n = λ i → BouquetWithStr n

underlyingEquiv : {ℓ : Level} (n : ℕ) → TypeWithStr ℓ (TaffyStructure n) ≃ TypeWithStr ℓ (TaffyStructure n)
underlyingEquiv n = (λ x → x) , {!   !}
-- underlyingEquiv = {!   !}

tmp2 : {ℓ : Level} (n : ℕ) 
       → (B : TypeWithStr ℓ (TaffyStructure n)) 
       → (e : TypeWithStr ℓ (TaffyStructure n) ≃ TypeWithStr ℓ (TaffyStructure n))
       → (x : S¹ → (TypeWithStr ℓ (TaffyStructure n))) 
       → ({!  !} ∙ {!   !}) ≡ {!   !}
       → Type
tmp2 n B e x t = {! !}

h : (n : ℕ) → (f g : S¹ → Bouquet (Fin n))
  → (f ≡ g)
  → (S¹ → Bouquet (Fin n))
h n f g p base = f base
h n f g p (loop i) = hcomp (λ { j (i = i0) → (sym p) j base 
                              ; j (i = i1) → (sym p) j base }) 
                           (g (loop i))

h' : (n : ℕ) 
   → (f : {!   !})
   → (g : {!   !})
   → (f ≡ g)
   → (S¹ → Bouquet (Fin n))
h' = {!   !}

∂ : I → I
∂ i = i ∨ ~ i

lemmaFaces : (n : ℕ) → (f g : S¹ → Bouquet (Fin n)) 
           → (p : f ≡ g) → (i : I) → (j : I) → I
           → Partial (∂ i ∨ ∂ j) (Bouquet (Fin n))
lemmaFaces n f g p i j k (i = i0) = sym p k (loop j)
lemmaFaces n f g p i j k (i = i1) = hfill (λ { k (j = i0) → sym p k base 
                                             ; k (j = i1) → sym p k base }) 
                                          (inS (g (loop j))) k
lemmaFaces n f g p i j k (j = i0) = sym p k base
lemmaFaces n f g p i j k (j = i1) = sym p k base

lemma : (n : ℕ) → (f g : S¹ → Bouquet (Fin n)) 
      → (p : f ≡ g) → (f ≡ h n f g p)
lemma n f g p i base = h n f g p base
lemma n f g p i (loop j) = hcomp (lemmaFaces n f g p i j) (g (loop j))    