module CQTS.BraidGroups where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Group
open import Cubical.HITs.Bouquet
open import Cubical.HITs.S1

open import Cubical.Data.Fin
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; znots)
open import Cubical.Data.Nat.Order

open import Cubical.Foundations.SIP
open import Cubical.Structures.Pointed
open import Cubical.HITs.S1.Base

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open import CQTS.BraidGroups.Ars

-- example about the relations without using the bouquet library

data Bouquet3 : Type where 
  base : Bouquet3
  loop1 : base ≡ base
  loop2 : base ≡ base
  loop3 : base ≡ base 

auto : Bouquet3 → Bouquet3
auto base = base
auto (loop1 i) = (loop1 ∙ loop2 ∙ loop3 ∙ (sym loop2) ∙ (sym loop1)) i
auto (loop2 i) = loop2 i
auto (loop3 i) = (sym loop2 ∙ loop1 ∙ loop2) i

data ThreeThings : Type where
  x1 : ThreeThings
  x2 : ThreeThings
  x3 : ThreeThings

BouquetNew = Bouquet ThreeThings
auto0 : BouquetNew → BouquetNew

auto0 base = base
auto0 (loop x1 i) = (loop x1 ∙ loop x2 ∙ loop x3 ∙ sym (loop x2) ∙ sym (loop x3)) i
auto0 (loop x2 i) = loop x2 i
auto0 (loop x3 i) = (sym (loop x2) ∙ loop x1 ∙ loop x2) i

-- examples using the bouquet library

-- example 1 (or example 0 but with the lib) (the inverse is obviously the same)

-- x₁ → x₂
-- x₂ → x₁
-- xᵢ → xᵢ

auto1 : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin n)
auto1 zero b = base
auto1 (suc zero) base = base
auto1 (suc zero) (loop x i) = loop x i
auto1 (suc (suc n)) base = base
auto1 (suc (suc n)) (loop (zero , p) i) = loop  ((suc zero) , suc-≤-suc (suc-≤-suc (zero-≤ ))) i
auto1 (suc (suc n)) (loop (suc zero , p) i) = loop (zero , (suc-≤-suc (≤-suc (zero-≤ )))) i
auto1 (suc (suc n)) (loop (suc (suc k) , x) i) = loop (suc (suc k) , x) i

encodeDecode1 : (n : ℕ) → (b : Bouquet (Fin n)) → auto1 n (auto1 n b)  ≡ b
encodeDecode1 zero base = refl
encodeDecode1 zero (loop (x , p) i) j = lemma i j
  where lemma : Square refl refl refl (loop (x , p)) 
        lemma = ⊥.rec (¬-<-zero p)
encodeDecode1 (suc zero) base = refl
encodeDecode1 (suc zero) (loop x i) = refl
encodeDecode1 (suc (suc n)) base = refl
encodeDecode1 (suc (suc n)) (loop (zero , p) i) j = loop (zero , isProp≤ (suc-≤-suc (≤-suc (zero-≤ ))) p j) i 
encodeDecode1 (suc (suc n)) (loop (suc zero , p) i) j = loop (suc zero , isProp≤ (suc-≤-suc (suc-≤-suc (zero-≤ ))) p j) i
encodeDecode1 (suc (suc n)) (loop (suc (suc x) , p) i) = refl

iso1 : (n : ℕ) → Iso (Bouquet (Fin n)) (Bouquet (Fin n))
Iso.fun (iso1 n) = auto1 n 
Iso.inv (iso1 n) = auto1 n 
Iso.rightInv (iso1 n) = encodeDecode1 n
Iso.leftInv (iso1 n) = encodeDecode1 n

-- Proof that iso1 is an equivalence

iso1eq : (n : ℕ) → (Bouquet (Fin n)) ≃ (Bouquet (Fin n))
iso1eq n =  isoToEquiv (iso1 n)

BouquetStr : (n : ℕ) → TypeWithStr _ PointedStructure
BouquetStr n = Bouquet (Fin n) , base

iso1ptdEq : (n : ℕ) → BouquetStr n ≃[ PointedEquivStr ] BouquetStr n
fst (iso1ptdEq n) = iso1eq n
snd (iso1ptdEq zero) = refl
snd (iso1ptdEq (suc zero)) = refl
snd (iso1ptdEq (suc (suc n))) = refl

iso1ptdEqPath : (n : ℕ) → BouquetStr n ≡ BouquetStr n
iso1ptdEqPath n = pointed-sip (BouquetStr n) (BouquetStr n) (iso1ptdEq n)

-- example 2

-- xᵢ → xᵢ₊₁
-- xₙ → x₁

-- the inverse:
-- xₙ → x₁
-- xᵢ₊₁ → xᵢ

includeStart : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin (suc n))
includeStart n base = base
includeStart n (loop (k , p) i) = loop (k , ≤-suc p) i

includeEnd : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin (suc n))
includeEnd n base = base
includeEnd n (loop (k , p) i) = loop (suc k , suc-≤-suc p) i

dropStart : (n : ℕ) → Bouquet (Fin (suc n)) → Bouquet (Fin n)
dropStart n x = {!!}

dropEnd : (n : ℕ) → Bouquet (Fin (suc n)) → Bouquet (Fin n)
dropEnd n x = {!!}

grabLast : (n : ℕ) → Path (Bouquet (Fin n)) base base
grabLast zero = {!!}
grabLast (suc n) = {!!}

auto2 : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin n)
auto2 n base = base
auto2 n (loop (zero , _) i) = grabLast n i
auto2 n (loop (suc k , p) i) = loop (k , suc-< p) i

-- auto2inv : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin n)
-- auto2inv n base = base
-- auto2inv n grabLast = helper {!!} {!!} {!!}
--   where helper : (n : ℕ) → Path (Bouquet (Fin n)) base base → Bouquet (Fin n) → Bouquet (Fin n)
--         helper n remembered b = {!!}
-- auto2inv n (loop (k , p) i) = loop (suc k , {!!}) i

-- example 3

-- x₁ → x₁ x₂ x₁⁻¹
-- x₂ → x₁
-- xᵢ → xᵢ

-- the inverse:

-- x₁ → x₂
-- x₂ → x₂⁻¹ x₁ x₂
-- xᵢ → xᵢ

auto3 : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin n)
auto3 zero b = base
auto3 (suc zero) b = b
auto3 (suc (suc n)) base = base
auto3 (suc (suc n)) (loop (zero , p) i) = (loop (zero , suc-≤-suc (≤-suc zero-≤)) ∙∙ loop (suc zero , suc-≤-suc (suc-≤-suc (zero-≤ ))) ∙∙ sym (loop (zero , suc-≤-suc (≤-suc zero-≤)))) i
auto3 (suc (suc n)) (loop (suc zero , p) i) = loop (zero , (suc-≤-suc (≤-suc (zero-≤ )))) i
auto3 (suc (suc n)) (loop (suc (suc x) , p) i) = (loop (suc (suc x) , p) i)

auto3Inv : (n : ℕ) → Bouquet (Fin n) → Bouquet (Fin n)
auto3Inv zero b = base
auto3Inv (suc zero) b = b
auto3Inv (suc (suc n)) base = base
auto3Inv (suc (suc n)) (loop (zero , _) i) = loop (suc zero , suc-≤-suc (suc-≤-suc (zero-≤ ))) i
auto3Inv (suc (suc n)) (loop (suc zero , p) i) = (sym (loop (suc zero , suc-≤-suc(suc-≤-suc(zero-≤)))) ∙∙ loop (zero , (suc-≤-suc(≤-suc(zero-≤)))) ∙∙ loop (suc zero , suc-≤-suc(suc-≤-suc(zero-≤)))) i
auto3Inv (suc (suc n)) (loop (suc (suc x) , p) i) = (loop (suc (suc x) , p) i)

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
           (λ i → auto3Inv (suc (suc n)) (auto3 (suc (suc n)) (loop (zero , p) i)))
           ≡ loop (zero , p)
hardCase n p =
  (λ i → auto3Inv (suc (suc n)) (auto3 (suc (suc n)) (loop (zero , p) i)))

    ≡⟨ refl ⟩

  (λ i → auto3Inv (suc (suc n)) ((loop (zero , suc-≤-suc (≤-suc zero-≤))
                                            ∙∙ loop (suc zero , suc-≤-suc (suc-≤-suc zero-≤))
                                            ∙∙ (sym (loop (zero , suc-≤-suc (≤-suc zero-≤))))) i))

    ≡⟨ cong-∙∙ (auto3Inv (suc (suc n))) (loop (zero , suc-≤-suc (≤-suc zero-≤)))
                                                  (loop (suc zero , suc-≤-suc (suc-≤-suc zero-≤)))
                                                  ((sym (loop (zero , suc-≤-suc (≤-suc zero-≤))))) ⟩

  (cong (auto3Inv (suc (suc n))) (loop (zero , suc-≤-suc (≤-suc zero-≤)))
   ∙∙ cong (auto3Inv (suc (suc n))) (loop (suc zero , suc-≤-suc (suc-≤-suc zero-≤)))
   ∙∙ cong (auto3Inv (suc (suc n))) ((sym (loop (zero , suc-≤-suc (≤-suc zero-≤))))))

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

encodeDecode3 : (n : ℕ) → (b : Bouquet (Fin n)) → auto3Inv n (auto3 n b) ≡ b
encodeDecode3 zero base = refl
encodeDecode3 zero (loop (x , p) i) j =  lemma i j
  where lemma : Square refl refl refl (loop (x , p))
        lemma = ⊥.rec (¬-<-zero p)
encodeDecode3 (suc zero) b = refl
encodeDecode3 (suc (suc n)) base = refl
encodeDecode3 (suc (suc n)) (loop (zero , p) i) j = hardCase n p j i
encodeDecode3 (suc (suc n)) (loop (suc zero , p) i) j  = loop (suc zero , isProp≤ (suc-≤-suc (suc-≤-suc (zero-≤ ))) p  j) i
encodeDecode3 (suc (suc n)) (loop (suc (suc x) , p) i) = refl

circleHelper : (k : ℕ) →  (n : ℕ) → (k < n) →  S¹ → Bouquet (Fin n)
circleHelper k n _ base = base
circleHelper k zero _ s = base
circleHelper zero (suc n) _ (loop i) = loop (zero , suc-≤-suc zero-≤) i
circleHelper (suc k) (suc n) p (loop i) = ( (λ j → circleHelper k (suc n) (suc-< p) (loop j)) ∙ loop (suc k , p )) i

-- cHelper : (k : ℕ) → (n : ℕ) → S¹ → (k < n) → Bouquet (Fin n)
-- cHelper zero zero base p = base
-- cHelper zero zero (loop i) p = base
-- cHelper zero (suc n) base p = base
-- cHelper zero (suc n) (loop i) p = {!!}
-- cHelper (suc k) zero base p = base
-- cHelper (suc k) zero (loop i) p = base
-- cHelper (suc k) (suc n) base p = base
-- cHelper (suc k) (suc n) (loop i) p = cHelper {!!} {!!} {!!} p

circMap : (n : ℕ) →  S¹ → Bouquet (Fin n)
circMap zero s = base
circMap (suc n) s = circleHelper n (suc n) ≤-refl s

-- Defining a circle structure
-- TypeWithLoop :  ∀ {ℓ} → Type (ℓ-suc ℓ)
-- TypeWithLoop {ℓ} = Σ[ X ∈ Type ℓ ] (S¹ → X)
--  Σ (n : ℕ) (f : S¹ → Bouquet A) , (f ≡ circMap n)

-- CircleStructure : Type ℓ → Type ℓ
-- CircleStructure X = Σ[ xX ] (S¹ → X)

-- BouquetCircStr : (n : ℕ) → TypeWithStr _ {! CircleStructure  !}
-- BouquetCircStr n = Bouquet (Fin n) , circMap n

-- swappy : (k : ℕ) → (n : ℕ) → (k < n) → (Bouquet (Fin n)) → (Bouquet (Fin n))
-- swappy k zero p b = base
-- swappy k (suc zero) p b = base
-- swappy zero (suc (suc n)) p b = auto1 {! suc suc n  !} {!   !}
-- swappy (suc k) (suc n) p b = {!   !}

index1 : (n : ℕ) → Fin (suc (suc n)) → Fin (suc (suc n)) -- we want to swap 0 and 1
index1 zero f = (suc zero , suc-≤-suc ≤-refl)
index1 (suc zero) f = (zero , ≤-suc (≤-suc ≤-refl))
index1 (suc (suc n)) f = (suc (suc n) , ≤-suc ≤-refl)

deleteZero : {n : ℕ} → (j : Fin (suc n)) → (¬ 0 ≡ fst j) → Fin n
deleteZero j pr = punchOut {i = (zero , suc-≤-suc zero-≤)} {j = j} {!!}

indexN : (n : ℕ) (m : Fin (suc n)) → Fin (suc (suc n)) → Fin (suc (suc n)) -- we want to swap m and m + 1
indexN zero (m , _) f = index1 zero f
indexN (suc n) (zero , _) f = index1 (suc n) f
indexN (suc n) (suc m , x) (zero , b) = index1 (suc n) (zero , b)
indexN (suc n) (suc m , x) (suc a , b) = fsuc (indexN n (m , pred-≤-pred x) (deleteZero (suc a , b) (<→≢ (suc-≤-suc zero-≤))))

bouqueter : {A B : Set} → (A → B) → (Bouquet A → Bouquet B) -- same as bouquet-map in BraidGroups.Ars
bouqueter f base = base
bouqueter f (loop x i) = loop (f x) i

bouqueterG : {A : Set} → (A → Path (Bouquet A) base base) → (Bouquet A → Bouquet A)
bouqueterG f base = base
bouqueterG f (loop x i) = (f x ∙ loop x ∙ sym (f x)) i

bouqueterA : {A : Set} → (A → Path (Bouquet A) base base) → (Bouquet A → Bouquet A)
bouqueterA f base = base
bouqueterA f (loop x i) = f x i

bouq : (n : ℕ) (m : Fin (suc n)) → Bouquet (Fin (suc (suc n))) → Bouquet (Fin (suc (suc n)))
bouq n m = bouqueter (indexN n m)

auto1new : (n : ℕ) → (Fin (suc (suc n))) → (Path (Bouquet (Fin (suc (suc n)))) base base)
auto1new zero f = (loop (zero , ≤-suc ≤-refl)) ∙ (loop (suc zero , suc-≤-suc ≤-refl))
auto1new (suc zero) f = loop (zero , ≤-suc (≤-suc ≤-refl))
auto1new (suc (suc n)) f = refl

auto1newBouq : (n : ℕ) → Bouquet (Fin (suc (suc n))) → Bouquet (Fin (suc (suc n)))
auto1newBouq n = bouqueterG (auto1new n)

-- Here is the old definition of Ars and all of its auxiliary functions and proofs.
-- All of the new auxiliary functions and proofs will either be in this file (after the commented section) or BraidGroups.Ars
-- Note that uncommenting the following code does not break anything, it's just full of unnecessary goals that are near impossible to solve for now,
-- which is why they're being rewritten using the new Ars definition.
-- To distinguish between the two version, the older version uses an ' at the end of all names.

-- Ars-index' : (n : ℕ) (r : Fin (suc (suc n))) (s : Fin (suc (suc n))) → (fst r < fst s) → (i : Fin (suc (suc n))) →  Path (Bouquet (Fin (suc (suc n)))) base base
-- Ars-index' n (zero , a) (zero , b) p i = ⊥.rec (¬-<-zero p)
-- Ars-index' zero (zero , a) (suc s , b) p (zero , c) = loop (zero , c) ∙ loop (suc zero , ≤-refl) ∙ loop (zero , c) ∙ sym (loop (suc zero , ≤-refl)) ∙ sym (loop (zero , c))
-- Ars-index' zero (zero , a) (suc s , b) p (suc i , c) = loop (zero , a) ∙ loop (suc zero , ≤-refl) ∙ sym (loop (zero , a))
-- Ars-index' (suc n) (zero , a) (suc s , b) p (zero , c) = loop (zero , c) ∙ loop (suc s , b) ∙ loop (zero , c) ∙ sym (loop (suc s , b)) ∙ sym (loop (zero , c)) 
-- Ars-index' (suc n) (zero , a) (suc s , b) p (suc i , c) = helper (s ≟ i)
--   where helper : Trichotomy s i → base ≡ base
--         helper (lt q) = refl
--         helper (eq q) = loop (zero , a) ∙ loop (suc i , c) ∙ sym (loop (zero , a))
--         helper (gt q) = loop (zero , a) ∙ loop (suc s , b) ∙ sym (loop (zero , a)) ∙ sym (loop (suc s , b)) ∙ loop (suc i , c) ∙ loop (suc s , b) ∙ loop (zero , a) ∙ sym (loop (suc s , b)) ∙ sym (loop (zero , a))
-- Ars-index' n (suc r , a) (zero , b) p i = ⊥.rec (¬-<-zero p)
-- Ars-index' zero (suc r , a) (suc s , b) p i = ⊥.rec (¬-<-zero (<≤-trans (pred-≤-pred p) (pred-≤-pred (pred-≤-pred b))))
-- Ars-index' (suc n) (suc r , a) (suc s , b) p (zero , c) = helper (s ≟ r)
--   where helper : Trichotomy s r → base ≡ base
--         helper (lt q) = ⊥.rec (¬m<m (<-trans q (pred-≤-pred p)))
--         helper (eq q) = ⊥.rec (<→≢ (pred-≤-pred p) (sym q))
--         helper (gt q) = refl
-- Ars-index' (suc n) (suc r , a) (suc s , b) p (suc i , c) = cong (bouqueter fsuc) (Ars-index' n (r , pred-≤-pred a) (s , pred-≤-pred b) (pred-≤-pred p) (i , pred-≤-pred c))

-- Ars' : (n : ℕ) (r : Fin (suc (suc n))) (s : Fin (suc (suc n))) → (fst r < fst s) → Bouquet (Fin (suc (suc n))) → Bouquet (Fin (suc (suc n)))
-- Ars' n r s p = bouqueterA (Ars-index' n r s p)

-- ArsInv-index' : (n : ℕ) (r : Fin (suc (suc n))) (s : Fin (suc (suc n))) → (fst r < fst s) → (i : Fin (suc (suc n))) →  Path (Bouquet (Fin (suc (suc n)))) base base
-- ArsInv-index' n (zero , a) (zero , b) p i = ⊥.rec (¬-<-zero p)
-- ArsInv-index' zero (zero , a) (suc s , b) p (zero , c) = sym (loop (suc s , b)) ∙ loop (zero , c) ∙ loop (suc s , b)
-- ArsInv-index' zero (zero , a) (suc s , b) p (suc i , c) = sym (loop (suc zero , ≤-refl)) ∙ sym (loop (zero , a)) ∙ loop (suc zero , ≤-refl) ∙ loop (zero , a) ∙ loop (suc zero , ≤-refl)
-- ArsInv-index' n (suc r , a) (zero , b) p i = ⊥.rec (¬-<-zero p)
-- ArsInv-index' zero (suc r , a) (suc s , b) p i = ⊥.rec (¬-<-zero (<≤-trans (pred-≤-pred p) (pred-≤-pred (pred-≤-pred b)))) 
-- ArsInv-index' (suc n) (zero , a) (suc s , b) p (zero , c) = sym (loop (suc s , b)) ∙ loop (zero , a) ∙ loop (suc s , b)
-- ArsInv-index' (suc n) (zero , a) (suc s , b) p (suc i , c) = helper (s ≟ i)
--    where helper : Trichotomy s i → base ≡ base
--          helper (lt q) = refl
--          helper (eq q) = sym (loop (suc i , c)) ∙ sym (loop (zero , a)) ∙ loop (suc i , c) ∙ loop (zero , a) ∙ loop (suc i , c)
--          helper (gt q) = sym (loop (suc s , b)) ∙ sym (loop (zero , a)) ∙ loop (suc s , b) ∙ loop (zero , a) ∙ loop (suc i , c) ∙ sym (loop (zero , a)) ∙ sym (loop (suc s , b)) ∙ loop (zero , a) ∙ loop (suc s , b)
-- ArsInv-index' (suc n) (suc r , a) (suc s , b) p (zero , c) = helper (s ≟ r)
--   where helper : Trichotomy s r → base ≡ base
--         helper (lt q) = ⊥.rec (¬m<m (<-trans q (pred-≤-pred p)))
--         helper (eq q) = ⊥.rec (<→≢ (pred-≤-pred p) (sym q))
--         helper (gt q) = refl
-- ArsInv-index' (suc n) (suc r , a) (suc s , b) p (suc i , c) = cong (bouqueter fsuc) (ArsInv-index' n (r , pred-≤-pred a) (s , pred-≤-pred b) (pred-≤-pred p) (i , pred-≤-pred c))

-- ArsInv' : (n : ℕ) (r : Fin (suc (suc n))) (s : Fin (suc (suc n))) → (fst r < fst s) → Bouquet (Fin (suc (suc n))) → Bouquet (Fin (suc (suc n)))
-- ArsInv' n r s p = bouqueterA (ArsInv-index' n r s p)

-- productAll' : (n : ℕ) → Path (Bouquet (Fin (suc (suc n)))) base base
-- productAll' zero = refl
-- productAll' (suc n) = loop (zero , suc-≤-suc zero-≤) ∙ cong (bouqueter fsuc) (productAll' n)

-- ArsProduct' : (n : ℕ) → (r : Fin (suc (suc n))) → (s : Fin (suc (suc n))) → (p : fst r < fst s) → cong (Ars' n r s p) (productAll' n) ≡ productAll' n
-- ArsProduct' n (zero , a) (zero , b) p = ⊥.rec (¬-<-zero p)
-- ArsProduct' zero (zero , a) (suc s , b) p = refl
-- ArsProduct' zero (suc r , a) (zero , b) p = refl
-- ArsProduct' zero (suc r , a) (suc s , b) p = refl
-- ArsProduct' (suc n) (zero , a) (suc s , b) p = 

--            cong (Ars' (suc n) (zero , a) (suc s , b) p)
--              (loop (zero , suc-≤-suc zero-≤) ∙
--              (λ i → bouqueter fsuc (productAll' n i)))        

--             ≡⟨ cong-∙ (Ars' (suc n) (zero , a) (suc s , b) p) (loop (zero , suc-≤-suc zero-≤)) ((λ i → bouqueter fsuc (productAll' n i))) ⟩

--            ((cong (Ars' (suc n) (zero , a) (suc s , b) p) (loop (zero , suc-≤-suc zero-≤)))
--                ∙ (cong (Ars' (suc n) (zero , a) (suc s , b) p) (λ i → bouqueter fsuc (productAll' n i))))

--             ≡⟨ refl ⟩

--            ((loop (zero , suc-≤-suc (≤-suc zero-≤)) ∙ loop (suc s , b) ∙ loop (zero , suc-≤-suc (≤-suc zero-≤)) ∙ sym (loop (suc s , b)) ∙ sym (loop (zero , suc-≤-suc (≤-suc zero-≤))) )
--               ∙ (cong (Ars' (suc n) (zero , a) (suc s , b) p) (λ i → bouqueter fsuc (productAll' n i))))

--             ≡⟨ {!!} ⟩

--            {!!}

--             ≡⟨ {!!} ⟩

--            loop (zero , suc-≤-suc zero-≤) ∙ (λ i → bouqueter fsuc (productAll' n i))

--           ∎

-- ArsProduct' (suc n) (suc r , a) (zero , b) p = ⊥.rec (¬-<-zero p)
-- ArsProduct' (suc n) (suc r , a) (suc s , b) p = helper (s ≟ r)
--   where helper : Trichotomy s r →  cong (Ars' (suc n) (suc r , a) (suc s , b) p) (productAll' (suc n)) ≡ productAll' (suc n)
--         helper (lt q) = ⊥.rec (¬m<m (<-trans q (pred-≤-pred p)))
--         helper (eq q) = ⊥.rec (<→≢ (pred-≤-pred p) (sym q))
--         helper (gt q) =  

--           cong (Ars' (suc n) (suc r , a) (suc s , b) p)
--           (loop (zero , suc-≤-suc zero-≤) ∙
--           (λ i → bouqueter fsuc (productAll' n i)))

--             ≡⟨ cong-∙ ((Ars' (suc n) (suc r , a) (suc s , b) p)) ((loop (zero , suc-≤-suc zero-≤))) ((λ i → bouqueter fsuc (productAll' n i))) ⟩

--           (cong (Ars' (suc n) (suc r , a) (suc s , b) p)
--           (loop (zero , suc-≤-suc zero-≤) ) ∙ ( cong (Ars' (suc n) (suc r , a) (suc s , b) p)
--           (λ i → bouqueter fsuc (productAll' n i))) )

--             ≡⟨ {!!} ⟩

--           {!!}

--             ≡⟨ {!!} ⟩

--           loop (zero , suc-≤-suc zero-≤) ∙ (λ i → bouqueter fsuc (productAll' n i))

--           ∎

-- proofInv' : (n : ℕ) (r : Fin (suc (suc n))) (s : Fin (suc (suc n))) → (p : fst r < fst s) → (Ars' n r s p) ∘ (ArsInv' n r s p) ≡ idfun _
-- proofInv' n r (zero , b) p = ⊥.rec (¬-<-zero p)
-- proofInv' zero (zero , a) (suc s , b) p =

--         Ars' zero (zero , a) (suc s , b) p ∘ ArsInv' zero (zero , a) (suc s , b) p

--              ≡⟨ refl ⟩

--             bouqueterA (Ars-index' zero (zero , a) (suc s , b) p) ∘ bouqueterA (ArsInv-index' zero (zero , a) (suc s , b) p)

--              ≡⟨ {!!} ⟩

--             {!!}

--              ≡⟨ {!!} ⟩

         
--          idfun (Bouquet (Fin 2))

--          ∎
         
-- proofInv' zero (suc r , a) (suc s , b) p = ⊥.rec (¬-<-zero (<≤-trans (pred-≤-pred p) (pred-≤-pred (pred-≤-pred b))))
-- proofInv' (suc n) (zero , a) (suc s , b) p = {!!}
-- proofInv' (suc n) (suc r , a) (suc s , b) p = helper (s ≟ r)
--   where helper : Trichotomy s r →  (Ars' (suc n) (suc r , a) (suc s , b) p) ∘ (ArsInv' (suc n) (suc r , a) (suc s , b) p) ≡ idfun _
--         helper (lt q) = ⊥.rec (¬m<m (<-trans q (pred-≤-pred p)))
--         helper (eq q) = ⊥.rec (<→≢ (pred-≤-pred p) (sym q))
--         helper (gt q) =

--           Ars' (suc n) (suc r , a) (suc s , b) p ∘
--            ArsInv' (suc n) (suc r , a) (suc s , b) p

--             ≡⟨ refl ⟩

--           bouqueterA (Ars-index' (suc n) (suc r , a) (suc s , b) p) ∘ bouqueterA (ArsInv-index' (suc n) (suc r , a) (suc s , b) p)

--             ≡⟨ {!!} ⟩

--           {!!}

--             ≡⟨ {!!} ⟩

--           idfun (Bouquet (Fin (suc (suc (suc n)))))

--           ∎

-- All the previous proofs using the new definition of Ars and its inverse (provided in BraidGroups.Ars)

productAll : (n : ℕ) → Path (Bouquet (Fin n)) base base
productAll zero = refl
productAll (suc n) = loop (zero , suc-≤-suc zero-≤) ∙ cong (bouquet-map fsuc) (productAll n) -- bouquet-map is the same as bouqueter

Ars01Product : {n : ℕ} → (p : 1 < n) → cong (Ars (zero , suc-< p) (suc zero , p) ≤-refl) (productAll n) ≡ productAll n
Ars01Product {zero} p = ⊥.rec (¬-<-zero p)
Ars01Product {suc zero} p = ⊥.rec ((¬m<m p))
Ars01Product {suc (suc n)} p =

        cong (Ars (zero , suc-≤-suc zero-≤) (suc zero , suc-≤-suc (suc-≤-suc zero-≤)) ≤-refl) (productAll (suc (suc n)))

        ≡⟨ refl ⟩

        cong (conj-constructor (Ars-index (zero , suc-≤-suc zero-≤) (suc zero , suc-≤-suc (suc-≤-suc zero-≤)) ≤-refl)) (productAll (suc (suc n)))

        ≡⟨ refl ⟩

        cong (conj-constructor (A0s-index (suc zero , suc-≤-suc (suc-≤-suc zero-≤)) ≤-refl)) (productAll (suc (suc n)))

        ≡⟨ refl ⟩

        cong (conj-constructor (A01-index (suc-≤-suc (suc-≤-suc zero-≤)))) (productAll (suc (suc n)))

        ≡⟨ refl ⟩

        cong (conj-constructor (A01-index (suc-≤-suc (suc-≤-suc zero-≤)))) (loop (zero , suc-≤-suc zero-≤) ∙ cong (bouquet-map fsuc) (productAll (suc n)))

        ≡⟨ cong-∙ (conj-constructor (A01-index (suc-≤-suc (suc-≤-suc zero-≤)))) (loop (zero , suc-≤-suc zero-≤)) (cong (bouquet-map fsuc) (productAll (suc n))) ⟩

        (cong (conj-constructor (A01-index (suc-≤-suc (suc-≤-suc zero-≤)))) (loop (zero , suc-≤-suc zero-≤))) ∙ (cong (conj-constructor (A01-index (suc-≤-suc (suc-≤-suc zero-≤)))) (cong (bouquet-map fsuc) (productAll (suc n))))

        ≡⟨ refl ⟩

        (λ i → conj-constructor (A01-index (suc-≤-suc (suc-≤-suc zero-≤))) (loop (zero , suc-≤-suc zero-≤) i)) ∙ (cong (conj-constructor (A01-index (suc-≤-suc (suc-≤-suc zero-≤)))) (cong (bouquet-map fsuc) (productAll (suc n))))

        ≡⟨ {!!} ⟩

        {!λ i → (A01-index (suc-≤-suc (suc-≤-suc zero-≤)) (loop (zero , suc-≤-suc zero-≤) i)) ∙ (loop (zero , suc-≤-suc zero-≤) i) ∙ sym (A01-index (suc-≤-suc (suc-≤-suc zero-≤)) (loop (zero , suc-≤-suc zero-≤) i))!} -- λ i → loop (0 , ?) ∙ loop (1 , ?) ∙ ? ∙ sym (loop (0 , ?) ∙ loop (1 , ?)) i
        ∙ (cong (conj-constructor (A01-index (suc-≤-suc (suc-≤-suc zero-≤)))) (cong (bouquet-map fsuc) (productAll (suc n))))

        ≡⟨ refl ⟩

        {!!}

        ≡⟨ {!!} ⟩

        productAll (suc (suc n))

        ∎

Ars0sProduct : {n : ℕ} (s : Fin n) → (m : 1 < n) → (p : 0 < fst s) → cong (Ars (zero , suc-< m) (fst s , {!!}) p) (productAll n) ≡ productAll n
Ars0sProduct {n} s m p = {!!}

ArsProduct : {n : ℕ} → (r s : Fin n) → (p : fst r < fst s) → cong (Ars r s p) (productAll n) ≡ productAll n
ArsProduct {n} r (zero , b) p = ⊥.rec (¬-<-zero p)
ArsProduct {zero} (zero , a) (suc s , b) p = ⊥.rec (¬-<-zero b)
ArsProduct {zero} (suc r , a) (suc s , b) p = ⊥.rec (¬-<-zero a)
ArsProduct {suc zero} (r , a) (suc s , b) p = ⊥.rec (¬-<-zero (pred-≤-pred b))
ArsProduct {suc (suc n)} (zero , a) (suc zero , b) p = Ars01Product b
ArsProduct {suc (suc n)} (zero , a) (suc (suc s) , b) p = 

        cong (Ars (zero , a) (suc (suc s) , b) p) (productAll (suc (suc n)))

        ≡⟨ refl ⟩

        cong (conj-constructor (Ars-index (zero , a) (suc (suc s) , b) p)) (productAll (suc (suc n)))

        ≡⟨ refl ⟩

        cong (conj-constructor (A0s-index (suc (suc s) , b) p)) (productAll (suc (suc n)))

        ≡⟨ refl ⟩

        {!!}

        ≡⟨ {!!} ⟩

        {!!}

        ≡⟨ {!!} ⟩

        productAll (suc (suc n))

        ∎

ArsProduct {suc (suc n)} (suc r , a) (suc s , b) p = 

        cong (Ars (suc r , a) (suc s , b) p) (productAll (suc (suc n)))

        ≡⟨ refl ⟩

        cong (conj-constructor (Ars-index (suc r , a) (suc s , b) p)) (productAll (suc (suc n)))

        ≡⟨ refl ⟩

        {!!}

        ≡⟨ {!!} ⟩

        {!!}

        ≡⟨ {!!} ⟩

        productAll (suc (suc n))

        ∎

proofInv : {n : ℕ} → (r s : Fin n) → (p : fst r < fst s) → (Ars r s p) ∘ (ArsInv r s p) ≡ idfun _
proofInv r (zero , b) p = ⊥.rec (¬-<-zero p)
proofInv {zero} (zero , a) (suc s , b) p = ⊥.rec (¬-<-zero b)
proofInv {zero} (suc r , a) (suc s , b) p = ⊥.rec (¬-<-zero a)
proofInv {suc zero} (r , a) (suc s , b) p = ⊥.rec (¬-<-zero (pred-≤-pred b))
proofInv {suc (suc n)} (zero , a) (suc zero , b) p = 

          Ars (zero , a) (suc zero , b) p ∘ ArsInv (zero , a) (suc zero , b) p

          ≡⟨ refl ⟩

          conj-constructor (Ars-index (zero , a) (suc zero , b) p) ∘ ArsInv (zero , a) (suc zero , b) p

          ≡⟨ refl ⟩

          conj-constructor (Ars-index (zero , a) (suc zero , b) p) ∘ conj-constructor (ArsInv-index (zero , a) (suc zero , b) p)

          ≡⟨ refl ⟩

          conj-constructor (A0s-index (suc zero , b) p) ∘ conj-constructor (A0sInv-index (suc zero , b) p)

          ≡⟨ refl ⟩

          conj-constructor (A01-index (suc-≤-suc (suc-≤-suc zero-≤))) ∘ conj-constructor (A01Inv-index (suc-≤-suc (suc-≤-suc zero-≤)))

          ≡⟨ refl ⟩

          {!!}

          ≡⟨ {!!} ⟩

          {!!}

          ≡⟨ {!!} ⟩

          idfun (Bouquet (Fin (suc (suc n))))

          ∎

proofInv {suc (suc n)} (zero , a) (suc (suc s) , b) p = 

          Ars (zero , a) (suc (suc s) , b) p ∘ ArsInv (zero , a) (suc (suc s) , b) p

          ≡⟨ refl ⟩

          conj-constructor (Ars-index (zero , a) (suc (suc s) , b) p) ∘ ArsInv (zero , a) (suc (suc s) , b) p

          ≡⟨ refl ⟩

          conj-constructor (Ars-index (zero , a) (suc (suc s) , b) p) ∘ conj-constructor (ArsInv-index (zero , a) (suc (suc s) , b) p)

          ≡⟨ refl ⟩

          conj-constructor (A0s-index (suc (suc s) , b) p) ∘ conj-constructor (A0sInv-index (suc (suc s) , b) p)

          ≡⟨ refl ⟩

          {!!}

          ≡⟨ {!!} ⟩

          {!!}

          ≡⟨ {!!} ⟩

          idfun (Bouquet (Fin (suc (suc n))))

          ∎

proofInv {suc (suc n)} (suc r , a) (suc s , b) p = 

          Ars (suc r , a) (suc s , b) p ∘ ArsInv (suc r , a) (suc s , b) p

          ≡⟨ refl ⟩

          conj-constructor (Ars-index (suc r , a) (suc s , b) p) ∘ ArsInv (suc r , a) (suc s , b) p

          ≡⟨ refl ⟩

          conj-constructor (Ars-index (suc r , a) (suc s , b) p) ∘ conj-constructor (ArsInv-index (suc r , a) (suc s , b) p)

          ≡⟨ refl ⟩

          {!!}

          ≡⟨ {!!} ⟩

          {!!}

          ≡⟨ {!!} ⟩

          idfun (Bouquet (Fin (suc (suc n))))

          ∎