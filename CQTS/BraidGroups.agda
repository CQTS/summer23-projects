module CQTS.BraidGroups where

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

open import Cubical.Foundations.SIP
open import Cubical.Structures.Pointed
open import Cubical.HITs.S1.Base

private
  variable
    ℓ : Level


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

-- x1 -> x1 x2 x1_1
-- x2 -> x1
-- xi -> xi

automorphismGen : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin n)
automorphismGen zero b = base
automorphismGen (suc zero) b = b
automorphismGen (suc (suc n)) base = base
automorphismGen (suc (suc n)) (loop (zero , p) i) = (loop (zero , suc-≤-suc (≤-suc zero-≤)) ∙∙ loop (suc zero , suc-≤-suc (suc-≤-suc (zero-≤ ))) ∙∙ sym (loop (zero , suc-≤-suc (≤-suc zero-≤)))) i
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
automorphismGenInv (suc (suc n)) (loop (suc zero , p) i) = (sym (loop (suc zero , suc-≤-suc (suc-≤-suc (zero-≤ )) )) ∙∙ loop (zero , (suc-≤-suc (≤-suc (zero-≤ )))) ∙∙ loop (suc zero , suc-≤-suc (suc-≤-suc (zero-≤ )))) i
automorphismGenInv (suc (suc n)) (loop (suc (suc x) , p) i) = (loop (suc (suc x) , p) i)

hardCase-lemma : ∀ {ℓ} {A : Type ℓ} {x₁ x₂ x₃ x₄ x₅ x₆ : A}
  {s : x₁ ≡ x₂}
  {r : x₂ ≡ x₃}
  {p : x₃ ≡ x₄}
  {q : x₄ ≡ x₅}
  {t : x₅ ≡ x₆}
  →
  (s ∙ r) ∙∙ p ∙∙ (q ∙ t) ≡ (s ∙∙ (r ∙∙ p ∙∙ q) ∙∙ t)
hardCase-lemma {A = A} {s = s} {r} {p} {q} {t} i j = hcomp faces (doubleCompPath-filler r p q i j)
  where faces : I → Partial (j ∨ ~ j) A
        -- faces k (i = i0) = doubleCompPath-filler (s ∙ r) p (q ∙ t) k j
        -- faces k (i = i1) = doubleCompPath-filler s (r ∙∙ p ∙∙ q) t k j
        faces k (j = i0) = compPath-filler s r (~ i) (~ k)
        faces k (j = i1) = compPath-filler' q t (~ i) k

hardCase-cancelSides : ∀ {ℓ} {A : Type ℓ} {x₂ x₃ x₄ x₅ : A}
  (s : x₃ ≡ x₂)
  (p : x₃ ≡ x₄)
  (q : x₄ ≡ x₅)
  →
  (s ∙ sym s) ∙∙ p ∙∙ (q ∙ sym q) ≡ p
hardCase-cancelSides {A = A} s p q i j = hcomp faces (p j)
  where faces : I → Partial (i ∨ j ∨ ~ j) A
        faces k (i = i1) = p j
        faces k (j = i0) = rCancel s i (~ k)
        faces k (j = i1) = rCancel q i k

hardCase : ∀ n p →
           (λ i → automorphismGenInv (suc (suc n)) (automorphismGen (suc (suc n)) (loop (zero , p) i)))
           ≡ loop (zero , p)
hardCase n p =
  (λ i → automorphismGenInv (suc (suc n)) (automorphismGen (suc (suc n)) (loop (zero , p) i)))

    ≡⟨ refl ⟩

  (λ i → automorphismGenInv (suc (suc n)) ((loop (zero , suc-≤-suc (≤-suc zero-≤))
                                            ∙∙ loop (suc zero , suc-≤-suc (suc-≤-suc zero-≤))
                                            ∙∙ (sym (loop (zero , suc-≤-suc (≤-suc zero-≤))))) i))

    ≡⟨ cong-∙∙ (automorphismGenInv (suc (suc n))) (loop (zero , suc-≤-suc (≤-suc zero-≤)))
                                                  (loop (suc zero , suc-≤-suc (suc-≤-suc zero-≤)))
                                                  ((sym (loop (zero , suc-≤-suc (≤-suc zero-≤))))) ⟩

  (cong (automorphismGenInv (suc (suc n))) (loop (zero , suc-≤-suc (≤-suc zero-≤)))
   ∙∙ cong (automorphismGenInv (suc (suc n))) (loop (suc zero , suc-≤-suc (suc-≤-suc zero-≤)))
   ∙∙ cong (automorphismGenInv (suc (suc n))) ((sym (loop (zero , suc-≤-suc (≤-suc zero-≤))))))

    ≡⟨ refl ⟩

  (loop (suc zero , _)
   ∙∙ (λ i →    (sym (loop (suc zero , suc-≤-suc (suc-≤-suc zero-≤) ))
             ∙∙ loop (zero , (suc-≤-suc (≤-suc zero-≤)))
             ∙∙ loop (suc zero , suc-≤-suc (suc-≤-suc zero-≤))) i)
   ∙∙ sym (loop (suc zero , _)))

    ≡⟨ sym (hardCase-lemma {s = loop (suc zero , _)}) ⟩

  (loop (suc zero , _) ∙ (sym (loop (suc zero , _))))
   ∙∙ loop (zero , _)
   ∙∙ (loop (suc zero , _) ∙ sym (loop (suc zero , _)))

    ≡⟨ hardCase-cancelSides (loop (suc zero , _)) (loop (zero , _)) (loop (suc zero , _)) ⟩
  loop (zero , suc-≤-suc (≤-suc zero-≤))
    ≡⟨ (λ i → loop (zero , isProp≤ (suc-≤-suc (≤-suc zero-≤)) p i)) ⟩
  loop (zero , p)
  ∎

encodeDecodeAutomorph : (n : ℕ) → (b : Bouquet (Fin n)) → automorphismGenInv n (automorphismGen n b)  ≡ b
encodeDecodeAutomorph zero base = refl
encodeDecodeAutomorph zero (loop (x , p) i) j =  lemma i j
  where lemma : Square refl refl refl (loop (x , p))
        lemma = ⊥.rec (¬-<-zero p)
encodeDecodeAutomorph (suc zero) b = refl
encodeDecodeAutomorph (suc (suc n)) base = refl
encodeDecodeAutomorph (suc (suc n)) (loop (zero , p) i) j = hardCase n p j i
encodeDecodeAutomorph (suc (suc n)) (loop (suc zero , p) i) j  = loop (suc zero , isProp≤ (suc-≤-suc (suc-≤-suc (zero-≤ ))) p j) i
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

circleHelper : (k : ℕ) →  (n : ℕ) → (k < n) →  S¹ → Bouquet (Fin n)
circleHelper k n _ base = base
circleHelper k zero _ s = base
circleHelper zero (suc n) _ (loop i) = loop (zero , suc-≤-suc zero-≤) i
circleHelper (suc k) (suc n) p (loop i) = ( (λ j → circleHelper k (suc n) (suc-< p) (loop j)) ∙ loop (suc k , p )) i


circMap : (n : ℕ) →  S¹ → Bouquet (Fin n)
circMap zero s = base
circMap (suc n) s = circleHelper n (suc n) ≤-refl s

-- Defining a circle structure
TypeWithLoop :  ∀ {ℓ} → Type (ℓ-suc ℓ)
TypeWithLoop {ℓ} = Σ[ X ∈ Type ℓ ] (S¹ → X)
--  Σ (n : ℕ) (f : S¹ → Bouquet A) , (f ≡ circMap n)

-- CircleStructure : Type ℓ → Type ℓ
-- CircleStructure X = Σ[ xX ] (S¹ → X)


-- BouquetCircStr : (n : ℕ) → TypeWithStr _ {! CircleStructure  !}
-- BouquetCircStr n = Bouquet (Fin n) , circMap n 


swappy : (k : ℕ) → (n : ℕ) → (k < n) → (Bouquet (Fin n)) → (Bouquet (Fin n))
swappy k zero p b = base
swappy k (suc zero) p b = base
swappy zero (suc (suc n)) p b = automorphGeneral {! suc suc n  !} {!   !}
swappy (suc k) (suc n) p b = {!   !}