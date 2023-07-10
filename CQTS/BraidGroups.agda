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

open import Cubical.Foundations.SIP
open import Cubical.Structures.Pointed


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


-- New Automorphism

automorphismGen : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin n)
automorphismGen zero b = base
automorphismGen (suc zero) b = b
automorphismGen (suc (suc n)) base = base
automorphismGen (suc (suc n)) (loop (zero , p) i) = (loop (zero , suc-≤-suc (≤-suc zero-≤)) ∙ loop (suc zero , suc-≤-suc (suc-≤-suc (zero-≤ ))) ∙ sym (loop (zero , suc-≤-suc (≤-suc zero-≤)))) i
automorphismGen (suc (suc n)) (loop (suc zero , p) i) = loop (zero , (suc-≤-suc (≤-suc (zero-≤ )))) i
automorphismGen (suc (suc n)) (loop (suc (suc x) , p) i) = (loop (suc (suc x) , p) i)


-- Inverse of automorphism
-- y1 -> y2 = x1
-- y2 -> y-2 y1 y2 = x-1 x1x2x-1 x1
-- yi -> yi 
automorphismGenInv : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin n)
automorphismGenInv zero b = base
automorphismGenInv (suc zero) b = b
automorphismGenInv (suc (suc n)) base = base
automorphismGenInv (suc (suc n)) (loop (zero , _) i) = loop (suc zero , suc-≤-suc (suc-≤-suc (zero-≤ ))) i
automorphismGenInv (suc (suc n)) (loop (suc zero , p) i) = (sym (loop (suc zero , suc-≤-suc (suc-≤-suc (zero-≤ )) )) ∙ loop (zero , (suc-≤-suc (≤-suc (zero-≤ )))) ∙ loop (suc zero , suc-≤-suc (suc-≤-suc (zero-≤ )))) i
automorphismGenInv (suc (suc n)) (loop (suc (suc x) , p) i) = (loop (suc (suc x) , p) i)


encodeDecodeAutomorph : (n : ℕ) → (b : Bouquet (Fin n)) → automorphismGenInv n (automorphismGen n b)  ≡ b
encodeDecodeAutomorph zero base = refl
encodeDecodeAutomorph zero (loop (x , p) i) j =  lemma i j
  where lemma : Square refl refl refl (loop (x , p)) 
        lemma = ⊥.rec (¬-<-zero p) 
encodeDecodeAutomorph (suc zero) b = refl
encodeDecodeAutomorph (suc (suc n)) base = refl
encodeDecodeAutomorph (suc (suc n)) (loop (zero , p) i) j = {!   !}
encodeDecodeAutomorph (suc (suc n)) (loop (suc zero , p) i)  = {!   !}
encodeDecodeAutomorph (suc (suc n)) (loop (suc (suc x) , p) i) = refl



MyIsomoprh : (n : ℕ) → Iso (Bouquet (Fin n)) (Bouquet (Fin n))
Iso.fun (MyIsomoprh n) = automorphGeneral n 
Iso.inv (MyIsomoprh n) = automorphGeneral n 
Iso.rightInv (MyIsomoprh n) = encodeDecodeAG n
Iso.leftInv (MyIsomoprh n) = encodeDecodeAG n
    
-- Proof that MyIsomoprh is an equivalence
MyIsomoprhEquiv : (n : ℕ) → (Bouquet (Fin n)) ≃ (Bouquet (Fin n))
MyIsomoprhEquiv n =  isoToEquiv (MyIsomoprh n)

BouquetStr : (n : ℕ) → TypeWithStr _ PointedStructure
BouquetStr n = Bouquet (Fin n) , base

MyIsomoprhPtdEquiv : (n : ℕ) → BouquetStr n ≃[ PointedEquivStr ] BouquetStr n
fst (MyIsomoprhPtdEquiv n) = MyIsomoprhEquiv n
snd (MyIsomoprhPtdEquiv zero) = refl
snd (MyIsomoprhPtdEquiv (suc zero)) = refl
snd (MyIsomoprhPtdEquiv (suc (suc n))) = refl

MyIsomorphPtdPath : (n : ℕ) → BouquetStr n ≡ BouquetStr n
MyIsomorphPtdPath n = pointed-sip (BouquetStr n) (BouquetStr n) (MyIsomoprhPtdEquiv n)