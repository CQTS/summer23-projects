module CQTS.BraidGroups where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism 
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Group
open import Cubical.HITs.Bouquet
open import Cubical.Data.Fin
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; znots)
open import Cubical.Data.Nat.Order



data Bouquet3 : Type where 
  base : Bouquet3
  loop1 : base ≡ base
  loop2 : base ≡ base
  loop3 : base ≡ base 

automorph : Bouquet3 → Bouquet3
automorph base = base
automorph (loop1 i) = (loop1 ∙ loop2 ∙ loop3 ∙ (sym loop2) ∙ (sym loop1)) i
automorph (loop2 i) = loop2 i
automorph (loop3 i) = (sym loop2 ∙ loop1 ∙ loop2) i


data ThreeThings : Type where
  x1 : ThreeThings
  x2 : ThreeThings
  x3 : ThreeThings

BouquetNew = Bouquet ThreeThings
automorphnew : BouquetNew → BouquetNew

automorphnew base = base
automorphnew (loop x1 i) = (loop x1 ∙ loop x2 ∙ loop x3 ∙ sym (loop x2) ∙ sym (loop x3)) i
automorphnew (loop x2 i) = loop x2 i
automorphnew (loop x3 i) = (sym (loop x2) ∙ loop x1 ∙ loop x2) i



automorphGeneral : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin n)
automorphGeneral zero b = base
automorphGeneral (suc zero) base = base
automorphGeneral (suc zero) (loop x i) = loop x i
automorphGeneral (suc (suc  n)) base = base
automorphGeneral (suc (suc n)) (loop (zero , p) i) = loop  ((suc zero) , suc-≤-suc (suc-≤-suc (zero-≤ ))) i
automorphGeneral (suc (suc n)) (loop (suc zero , p) i) = loop (zero , (suc-≤-suc (≤-suc (zero-≤ )))) i
automorphGeneral (suc (suc n)) (loop (suc (suc k) , x) i) = loop (suc (suc k) , x) i


encodeDecodeAG : (n : ℕ) → (b : Bouquet (Fin n)) → automorphGeneral n (automorphGeneral n b)  ≡ b
encodeDecodeAG zero base = refl
encodeDecodeAG zero (loop (x , p) i) j = lemma i j
  where lemma : Square refl refl refl (loop (x , p)) 
        lemma = ⊥.rec (¬-<-zero p)
encodeDecodeAG (suc zero) base = refl
encodeDecodeAG (suc zero) (loop x i) = refl
encodeDecodeAG (suc (suc n)) base = refl
encodeDecodeAG (suc (suc n)) (loop (zero , p) i) j = loop (zero , isProp≤ (suc-≤-suc (≤-suc (zero-≤ ))) p j) i 
encodeDecodeAG (suc (suc n)) (loop (suc zero , p) i) j = loop (suc zero , isProp≤ (suc-≤-suc (suc-≤-suc (zero-≤ ))) p j) i
encodeDecodeAG (suc (suc n)) (loop (suc (suc x) , p) i) = refl



MyIsomoprh : (n : ℕ) → Iso (Bouquet (Fin n)) (Bouquet (Fin n))
Iso.fun (MyIsomoprh n) = automorphGeneral n 
Iso.inv (MyIsomoprh n) = automorphGeneral n 
Iso.rightInv (MyIsomoprh n) = encodeDecodeAG n
Iso.leftInv (MyIsomoprh n) = encodeDecodeAG n
    
 