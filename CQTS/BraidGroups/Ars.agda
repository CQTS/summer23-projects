module CQTS.BraidGroups.Ars where

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

bouquet-map : ∀ {A B : Type ℓ} → (A → B) → Bouquet A → Bouquet B
bouquet-map f base = base
bouquet-map f (loop x i) = loop (f x) i

-- This is `fsuc`, but keeping `zero` at `zero`.
fstretch : ∀ {n} → Fin (suc n) → Fin (suc (suc n))
fstretch (zero , p) = (zero , ≤-suc p)
fstretch (suc n , x) = fsuc (suc n , x) -- this was previously fstretch n = fsuc n but I believe this is more correct. revert it to the previous one if I'm wrong

-- bouquet-suc : ∀ {n} → (Bouquet (Fin n)) → (Bouquet (Fin (suc n)))
-- bouquet-suc base = base
-- bouquet-suc (loop x i) = {!loop (fsuc x) i!}

conj-constructor : ∀ {n} → (Fin n → Path (Bouquet (Fin n)) base base) → (Bouquet (Fin n) → Bouquet (Fin n))
conj-constructor f base = base
conj-constructor f (loop x i) = (f x ∙∙ loop x ∙∙ sym (f x)) i

A01-index : {n : ℕ} → (1 < n) → Fin n → Path (Bouquet (Fin n)) base base
A01-index {suc (suc n)} p (zero , px) = loop (0 , suc-≤-suc zero-≤) ∙ loop (1 , suc-≤-suc (suc-≤-suc zero-≤))
A01-index {suc (suc n)} p (suc zero , px) = loop (0 , suc-≤-suc zero-≤)
A01-index {suc (suc n)} p (suc (suc x) , px) = refl
-- Impossible cases:
A01-index {zero} p x = ⊥.rec (¬-<-zero p)
A01-index {suc zero} p x = ⊥.rec (¬m<m p)

A0s-index : {n : ℕ} → (s : Fin n) → (0 < fst s) → Fin n → Path (Bouquet (Fin n)) base base
A0s-index {suc (suc n)} (suc zero , ps) p x = A01-index (suc-≤-suc (suc-≤-suc zero-≤)) x
A0s-index {suc (suc n)} (suc (suc s) , ps) p (zero , px) = cong (bouquet-map fstretch) (A0s-index (suc s , pred-≤-pred ps) (suc-≤-suc zero-≤) (zero , suc-≤-suc zero-≤))
A0s-index {suc (suc n)} (suc (suc s) , ps) p (suc zero , px) =
  loop (0 , suc-≤-suc zero-≤) ∙ loop (1 , suc-≤-suc (suc-≤-suc zero-≤))
  ∙ sym (loop (0 , suc-≤-suc zero-≤)) ∙ sym (loop (1 , suc-≤-suc (suc-≤-suc zero-≤)))
A0s-index {suc (suc n)} (suc (suc s) , ps) p (suc (suc x) , px) = cong (bouquet-map fstretch) (A0s-index (suc s , pred-≤-pred ps) (suc-≤-suc zero-≤) (suc x , pred-≤-pred px))

-- Impossible cases:
A0s-index {zero} s p b = ⊥.rec (¬Fin0 s)
A0s-index {suc zero} (zero , ps) p b = ⊥.rec (¬-<-zero p)
A0s-index {suc zero} (suc s , ps) p b = ⊥.rec (¬-<-zero (pred-≤-pred ps))
A0s-index {suc (suc n)} (zero , ps) p (x , px) = ⊥.rec (¬-<-zero p)

Ars-index : {n : ℕ} → (r s : Fin n) → (fst r < fst s) → Fin n → Path (Bouquet (Fin n)) base base
Ars-index {suc n} (zero , pr) (suc s , ps) p = A0s-index (suc s , ps) p
Ars-index {suc n} (suc r , pr) (suc s , ps) p (zero , px) = refl
Ars-index {suc n} (suc r , pr) (suc s , ps) p (suc x , px)
  = cong (bouquet-map fsuc) (Ars-index (r , pred-≤-pred pr)
                                       (s , pred-≤-pred ps)
                                       (pred-≤-pred p)
                                       (x , pred-≤-pred px))

-- remaining cases are impossible:
Ars-index {n} (r , pr) (zero , ps) p x = ⊥.rec (¬-<-zero p)
Ars-index {zero} (zero , pr) (suc s , ps) p x = ⊥.rec (¬-<-zero ps)
Ars-index {zero} (suc r , pr) (suc s , ps) p x = ⊥.rec (¬-<-zero pr)

Ars : {n : ℕ} → (r s : Fin n) → (fst r < fst s) → Bouquet (Fin n) → Bouquet (Fin n)
Ars r s p = conj-constructor (Ars-index r s p)

A01Inv-index : {n : ℕ} → (1 < n) → Fin n → Path (Bouquet (Fin n)) base base
A01Inv-index {suc (suc n)} p (zero , px) = sym (loop (1 , suc-≤-suc (suc-≤-suc zero-≤)))
A01Inv-index {suc (suc n)} p (suc zero , px) = sym (loop (1 , suc-≤-suc (suc-≤-suc zero-≤))) ∙ sym (loop (0 , suc-≤-suc zero-≤))
A01Inv-index {suc (suc n)} p (suc (suc x) , px) = refl
-- Impossible cases:
A01Inv-index {zero} p x = ⊥.rec (¬-<-zero p)
A01Inv-index {suc zero} p x = ⊥.rec (¬m<m p)

A0sInv-index : {n : ℕ} → (s : Fin n) → (0 < fst s) → Fin n → Path (Bouquet (Fin n)) base base
A0sInv-index {suc (suc n)} (suc zero , ps) p x = A01Inv-index (suc-≤-suc (suc-≤-suc zero-≤)) x
A0sInv-index {suc (suc n)} (suc (suc s) , ps) p (zero , px) = cong (bouquet-map fstretch) (A0sInv-index (suc s , pred-≤-pred ps) (suc-≤-suc zero-≤) (zero , suc-≤-suc zero-≤))
A0sInv-index {suc (suc n)} (suc (suc s) , ps) p (suc zero , px) =
  sym (loop (1 , suc-≤-suc (suc-≤-suc zero-≤))) ∙ sym (loop (0 , suc-≤-suc zero-≤))
  ∙ loop (1 , suc-≤-suc (suc-≤-suc zero-≤)) ∙ loop (0 , suc-≤-suc zero-≤)
A0sInv-index {suc (suc n)} (suc (suc s) , ps) p (suc (suc x) , px) = cong (bouquet-map fstretch) (A0sInv-index (suc s , pred-≤-pred ps) (suc-≤-suc zero-≤) (suc x , pred-≤-pred px))

-- Impossible cases:
A0sInv-index {zero} s p b = ⊥.rec (¬Fin0 s)
A0sInv-index {suc zero} (zero , ps) p b = ⊥.rec (¬-<-zero p)
A0sInv-index {suc zero} (suc s , ps) p b = ⊥.rec (¬-<-zero (pred-≤-pred ps))
A0sInv-index {suc (suc n)} (zero , ps) p (x , px) = ⊥.rec (¬-<-zero p)

ArsInv-index : {n : ℕ} → (r s : Fin n) → (fst r < fst s) → Fin n → Path (Bouquet (Fin n)) base base
ArsInv-index {suc n} (zero , pr) (suc s , ps) p = A0sInv-index (suc s , ps) p
ArsInv-index {suc n} (suc r , pr) (suc s , ps) p (zero , px) = refl
ArsInv-index {suc n} (suc r , pr) (suc s , ps) p (suc x , px)
  = cong (bouquet-map fsuc) (ArsInv-index (r , pred-≤-pred pr)
                                       (s , pred-≤-pred ps)
                                       (pred-≤-pred p)
                                       (x , pred-≤-pred px))

-- remaining cases are impossible:
ArsInv-index {n} (r , pr) (zero , ps) p x = ⊥.rec (¬-<-zero p)
ArsInv-index {zero} (zero , pr) (suc s , ps) p x = ⊥.rec (¬-<-zero ps)
ArsInv-index {zero} (suc r , pr) (suc s , ps) p x = ⊥.rec (¬-<-zero pr)

ArsInv : {n : ℕ} → (r s : Fin n) → (fst r < fst s) → Bouquet (Fin n) → Bouquet (Fin n)
ArsInv r s p = conj-constructor (ArsInv-index r s p)