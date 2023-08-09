module CQTS.Schreier.Schreier where

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Functions.Fibration
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels

open import Cubical.Homotopy.Base
open import Cubical.Homotopy.Loopspace



{-- TODO
    1. rename (fst , snd) on Pointed to (typ , pt) for consistency
    2. create iterative (Σ-cong-equiv-snd λ _ → ?) function 
-}



{-----------------------------------------------------------------------------
|                                                                            |
|                         [PART 0]  General Lemmas                           |
|                                                                            |
-----------------------------------------------------------------------------}

module Connectedness where

  isPathConnected : ∀{ℓ} → Type ℓ → Type ℓ
  isPathConnected A = isContr (∥ A ∥₂)

  isPathConnected' : ∀{ℓ} → Type ℓ → Type ℓ
  isPathConnected' A = ∥ A ∥₂ × ((a b : A) → ∥ a ≡ b ∥₁)

  isPropIsPathConnected : ∀{ℓ} {A : Type ℓ} → isProp (isPathConnected A)
  isPropIsPathConnected = isPropIsContr

  -- isPropIsPathConnected' : ∀{ℓ} {A : Type ℓ} → isProp (isPathConnected' A)
  -- isPropIsPathConnected' = {!   !}
    
  isPathConnected→isPathConnected' : ∀{ℓ} {A : Type ℓ} → 
                                     isPathConnected A → isPathConnected' A
  isPathConnected→isPathConnected' (c , C) =
    (c , λ a b → PT.rec 
      squash₁
      (Iso.fun PathIdTrunc₀Iso)
      (helper (c , C) ∣ a ∣₂ ∣ b ∣₂))
    where
      helper : ∀{ℓ} {A : Type ℓ} →
               isPathConnected A → (a b : ∥ A ∥₂) → ∥ a ≡ b ∥₁
      helper (c , C) a b = ∣ sym (C a) ∙ C b ∣₁


  -- isPathConnected≃isPathConnected' : isPathConnected A ≃ isPathConnected' A
  -- isPathConnected≃isPathConnected' = pathToEquiv (hPropExt isPropIsContr {!   !} {!   !} {!   !})
  -- isProp→Iso :  (Aprop : isProp A) (Bprop : isProp B) (f : A → B) (g : B → A) → Iso A B


  connected→PBaseSufficient : ∀ {ℓ} {E B : Type ℓ} → 
                              (P : Type ℓ → Type ℓ) → ((T : Type ℓ) → isProp (P T)) →
                              (f : E → B) → isPathConnected B →
                              (ptB : B) → P (fiber f ptB) →
                              (x : B) → P (fiber f x)
  connected→PBaseSufficient {_} {E} {B} P isPropP f connB ptB connFptB x =
    PT.rec
      (isPropP (fiber f x))
      (λ p → subst (λ y → P (fiber f y)) p connFptB)
      (isPathConnected→isPathConnected' connB .snd ptB x)    -- : ∥ ptB ≡ x ∥₁


  connected→connectedBaseSufficient : ∀ {ℓ} {E B : Type ℓ} → 
                                      (f : E → B) → isPathConnected B →
                                      (ptB : B) → isPathConnected (fiber f ptB) →
                                      (x : B) → isPathConnected (fiber f x)
  connected→connectedBaseSufficient {ℓ} {E} {B} = 
    connected→PBaseSufficient isPathConnected (λ T → isPropIsPathConnected {A = T}) 


  isPathConnectedTotal : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} →
                         isPathConnected A →
                         ((x : A) → isPathConnected (B x)) →
                         isPathConnected (Σ[ x ∈ A ] B x)
  isPathConnectedTotal connA connBx = invEq (e connBx) connA
    where
      e : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} →
          ((x : A) → isPathConnected (B x)) → 
          (isPathConnected (Σ[ x ∈ A ] B x) ≃ isPathConnected A)
      e {_} {A} {B} connBx = 
        isPathConnected (Σ[ x ∈ A ] B x)    ≃⟨ idEquiv _ ⟩
        isContr ∥ Σ[ x ∈ A ] B x ∥₂         ≃⟨ cong≃ isContr (isoToEquiv setSigmaIso) ⟩
        isContr ∥ Σ[ x ∈ A ] ∥ B x ∥₂ ∥₂     ≃⟨ cong≃ (λ T → isContr ∥ T ∥₂)  (Σ-contractSnd connBx) ⟩
        isContr ∥ A ∥₂  ≃⟨ idEquiv _ ⟩
        isPathConnected A ■


open Connectedness


idInv-≃ : ∀{ℓ} {A : Type ℓ} → {a b : A} →
          (a ≡ b) ≃ (b ≡ a)
idInv-≃ {_} {A} {a} {b} = isoToEquiv (iso sym sym ∼-refl ∼-refl)


module isEquiv≃ where

  Unit×-≃ : ∀{ℓ} {B : Type ℓ} → 
          B ≃ (Unit* {ℓ} × B)
  Unit×-≃ = isoToEquiv (iso
                  (λ b → tt* , b)
                  (λ x → snd x)
                  ∼-refl
                  ∼-refl
              )


  equivCompToUnit× : ∀{ℓ} {A B : Type ℓ} → 
                    (A ≃ B) ≃ (A ≃ (Unit* {ℓ} × B))
  equivCompToUnit× = equivComp (idEquiv _) (Unit×-≃)


  isEquiv-Unit×-≡ : ∀{ℓ} {A B : Type ℓ} → (f : A → B) → 
                    isEquiv {A = A} {B = B} (λ x → f x) ≡
                    isEquiv {A = A} {B = ((Unit* {ℓ}) × B)} (λ x → tt* , f x)
  isEquiv-Unit×-≡ f = hPropExt (isPropIsEquiv _) (isPropIsEquiv _)
                      (λ e → snd (fst   equivCompToUnit× (f                 , e)))
                      (λ e → snd (invEq equivCompToUnit× ((λ x → tt* , f x) , e)))



  Σ-sym-≃ : ∀{ℓ} {F E G : Type ℓ} →
            (ptG : G) → (i : F → E) → (p : E → G) →
            (H : (x : F) → (ptG ≡ p (i x))) →
            (Σ[ y ∈ E ] ptG ≡ p y) ≃ (Σ[ y ∈ E ] p y ≡ ptG)
  Σ-sym-≃ ptG i p H = Σ-cong-equiv-snd (λ y → idInv-≃)

  
  equivCompToΣ-sym : ∀{ℓ} {F E G : Type ℓ} →
                     (ptG : G) → (i : F → E) → (p : E → G) →
                     (H : (x : F) → (ptG ≡ p (i x))) →
                     (F ≃ (Σ[ y ∈ E ] ptG ≡ p y)) ≃ (F ≃ (Σ[ y ∈ E ] p y ≡ ptG))
  equivCompToΣ-sym ptG i p H = equivComp (idEquiv _) (Σ-sym-≃ ptG i p H)


  isEquiv-Σ-snd-≃ : ∀{ℓ} {F E G : Type ℓ} →
                    (ptG : G) → (i : F → E) → (p : E → G) →
                    (H : (x : F) → (ptG ≡ p (i x))) → 
                    isEquiv {A = F} {B = (Σ[ y ∈ E ] ptG ≡ p y)} (λ x → i x , H x) ≡
                    isEquiv {A = F} {B = (Σ[ y ∈ E ] p y ≡ ptG)} (λ x → i x , sym (H x))
  isEquiv-Σ-snd-≃ ptG i p H = hPropExt (isPropIsEquiv _) (isPropIsEquiv _)
                             (λ e → snd (fst (equivCompToΣ-sym ptG i p H) ((λ x → i x , H x) , e)))
                             (λ e → snd (invEq (equivCompToΣ-sym ptG i p H) ((λ x → i x , sym (H x)) , e)))


  -- ! create a generic functon and refactor this module
  -- isEquiv-≃ : ∀{ℓ} {A B C : Type ℓ} → (e : ((A ≃ B) ≃ (A ≃ C))) → (f : A → B) → 
  --             isEquiv {A = A} {B = B} (f) ≡
  --             isEquiv {A = A} {B = C} (fst e (f , _) )
  -- isEquiv-≃ = ?


  

open isEquiv≃
-- open isEquiv≃ using (isEquiv-Unit×-≡ ; isEquiv-Σ-snd-≃ )






{-----------------------------------------------------------------------------
|                                                                            |
|                         [PART 1]  Lemma 2.5.4                              |
|                                                                            |
-----------------------------------------------------------------------------}


-- ! replace with Prelude.isContrSingl
isContrBasedPathSpaceReverse : ∀ {ℓ} {A : Type ℓ} (a : A) → isContr (Σ[ x ∈ A ] (x ≡ a))
--                                                          isContr (fiber (idfun A) y)
isContrBasedPathSpaceReverse {_} {A} a = snd (idEquiv A) .equiv-proof a


isContrBasedPathSpace : ∀ {ℓ} {A : Type ℓ} (a : A) → isContr (Σ[ x ∈ A ] (a ≡ x))
isContrBasedPathSpace {ℓ} {A} a = (a , refl) , contraction {ℓ} {A} a
  where
    contraction : ∀ {ℓ} {A : Type ℓ} (a : A) → (y : (Σ[ x ∈ A ] (a ≡ x)) ) → (a , refl) ≡ y
    contraction {ℓ} {A} a (x , p) i =  p i ,  λ j → p (i ∧ j)


Σ-swap-2-≃ : ∀ {ℓ} {A B : Type ℓ} {C : A → B → Type ℓ} → 
             (Σ[ a ∈ A ] Σ[ b ∈ B ] (C a b)) ≃ 
             (Σ[ b ∈ B ] Σ[ a ∈ A ] (C a b))
Σ-swap-2-≃ {_} {A} {B} {C} =
  (Σ[ a ∈ A ] Σ[ b ∈ B ] (C a b))         ≃⟨ invEquiv Σ-assoc-≃ ⟩
  (Σ[ z ∈ (A × B) ] (C (fst z) (snd z)))  ≃⟨ Σ-cong-equiv-fst Σ-swap-≃ ⟩
  (Σ[ z ∈ (B × A) ] (C (snd z) (fst z)))  ≃⟨ Σ-assoc-≃ ⟩
  (Σ[ b ∈ B ] Σ[ a ∈ A ] (C a b)) ■

-- equivFun : A ≃ B → A → B
-- invEquiv : A ≃ B → B ≃ A

-- fiberEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') (y : A) → 
--            fiber fst y                   ≃ B y
--            (Σ (Σ A B) (λ x → fst x ≡ y)) ≃ B y
-- Note that 
--   fst : Σ A B → A

-- totalEquiv : E ≃ Σ B (fiber p)

_ : ∀ {ℓ} {A B : Type ℓ} {f : A → B} →
    (equivFun ∘ invEquiv) (totalEquiv f) ≡ (fst ∘ snd)
_ = refl


-- fibrationEquiv : (Σ[ E ∈ Type ℓ' ] (E → B)) ≃ (B → Type ℓ')
equivIntoAndOutMaps : ∀ {ℓ} {B : Type ℓ} → (Σ[ E ∈ Type ℓ ] (E → B)) ≃ (B → Type ℓ) 
equivIntoAndOutMaps {ℓ} {B} = fibrationEquiv B ℓ


fibProperty : ∀ {ℓ} {E B : Type ℓ} → {f : E → B} → ((b , e , p) : (Σ[ b ∈ B ] fiber f b)) → 
                             f e ≡ b
fibProperty {_} {E} {B} {f} (b , e , p) = p


-- This is lemma 2.5.4
equivIntoAndOutMaps∙ : ∀ {ℓ} {(B , ptB) : Pointed ℓ} → 
            (Σ[ E∙ ∈ (Pointed ℓ) ] (E∙ →∙ (B , ptB))) ≃
            (Σ[ c ∈ (B → Type ℓ) ] (c ptB))
equivIntoAndOutMaps∙ {ℓ} {B , ptB} = 
  Σ[ E∙ ∈ (Pointed ℓ) ]
      (E∙ →∙ (B , ptB))                                                     ≃⟨ Σ-assoc-≃ ⟩
  Σ[ E ∈ Type ℓ ] Σ[ ptE ∈ E ]
      Σ[ f ∈ (E → B) ] (f ptE ≡ ptB)                                        ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-swap-2-≃) ⟩
  Σ[ E ∈ Type ℓ ] Σ[ f ∈ (E → B) ]
      Σ[ ptE ∈ E ] (f ptE ≡ ptB)                                            ≃⟨ invEquiv Σ-assoc-≃ ⟩
  Σ[ E-f ∈ (Σ[ E ∈ Type ℓ ] (E → B)) ]
      Σ[ ptE ∈ (fst E-f) ] ((snd E-f) ptE ≡ ptB)                            ≃⟨ Σ-cong-equiv-fst equivIntoAndOutMaps ⟩
  Σ[ c ∈ (B → Type ℓ) ]
      (c ptB) ■





{-----------------------------------------------------------------------------
|                                                                            |
|                         [PART 2]  Lemma 2.5.5                              |
|                                                                            |
-----------------------------------------------------------------------------}


fiber∙ : ∀ {ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'} (f∙ : A∙ →∙ B∙) → Pointed (ℓ-max ℓ ℓ')
fiber∙ {_} {_} {A∙} {B∙} f∙ = (fiber (fst f∙) (pt B∙) , (pt A∙ , snd f∙))


-- Characterizing the identity type of the pointed functions
→∙≡≃ : ∀{ℓ} {A∙@(A , ptA) B∙@(B , ptB) : Pointed ℓ} {f∙@(f , ptf) g∙@(g , ptg) : A∙ →∙ B∙} →
       (f∙ ≡ g∙) ≃ (Σ[ H ∈ (f ∼ g) ] Square (ptf) (ptg) (H ptA) refl)
→∙≡≃ {ℓ} {A∙@(A , ptA)} {B∙@(B , ptB)} {f∙@(f , ptf)} {g∙@(g , ptg)} =
  (f∙ ≡ g∙)                                                     ≃⟨ invEquiv ΣPath≃PathΣ ⟩
  Σ[ H ∈ (f ≡ g) ]
      PathP (λ i → (H i) ptA ≡ ptB) ptf ptg                     ≃⟨ Σ-cong-equiv-fst (invEquiv funExtEquiv) ⟩
  Σ[ H ∈ (f ∼ g) ]
      PathP (λ i → (H ptA) i ≡ ptB) ptf ptg                     ≃⟨ idEquiv _ ⟩
  Σ[ H ∈ (f ∼ g) ]
      Square (ptf) (ptg) (H ptA) refl ■                          


→∙≡ToHomotopy : ∀{ℓ} {A∙ B∙ : Pointed ℓ} {f∙@(f , ptf) g∙@(g , ptg) : A∙ →∙ B∙} →
                (f∙ ≡ g∙) → (f ∼ g)
→∙≡ToHomotopy p = (fst (fst →∙≡≃ p))


module SquareLemmas where

  -- flipSquareEquiv : Square a b c d ≃ Square c d a b
  -- slideSquareEquiv : (Square a b c refl) ≃ (Square refl b c a)

  rotateSquareEquiv : ∀{ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
                      {a : a00 ≡ a01} {b : a10 ≡ a11} {c : a00 ≡ a10} {d : a01 ≡ a11} →
                      Square a b c d ≃ Square (sym c) (sym d) b a
  rotateSquareEquiv = isoToEquiv (iso
      (λ sq i j → sq (~ j) i)
      (λ sq i j → sq j (~ i))
      ∼-refl
      ∼-refl
    )


  -- Square≃doubleComp : Square a₀₋ a₁₋ a₋₀ a₋₁ ≃ (a₋₀ ⁻¹ ∙∙ a₀₋ ∙∙ a₋₁ ≡ a₁₋)
  -- doubleCompPath≡compPath : p ∙∙ q ∙∙ r ≡ p ∙ q ∙ r
  -- p ∙ q = refl ∙∙ p ∙∙ q
  {-          
               d                            refl           
        a01 - - - > a11              a11 - - - > a11     
          ^           ^                ^           ^     
        a |           | b        a ∙ d |           | b   
          |           |                |           |     
        a00 — — — > a10              a00 — — — > a10     
                c                            c           
  -}
  -- ! define later using hcomps to be computationally efficient
  slideConcatSquareEquiv : ∀{ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
                           {a : a00 ≡ a01} {b : a10 ≡ a11} {c : a00 ≡ a10} {d : a01 ≡ a11} →
                           Square a b c d ≃ Square (a ∙ d) b c refl
  slideConcatSquareEquiv {a = a} {b = b} {c = c} {d = d} = 
      Square a b c d                        ≃⟨ Square≃doubleComp a b c d ⟩
      ((sym c) ∙∙ a ∙∙ d          ≡ b)      ≃⟨ compPathlEquiv (sym (doubleCompPath≡compPath (sym c) a d)) ⟩ 
      ((sym c) ∙ a ∙ d            ≡ b)      ≃⟨ compPathlEquiv (sym (rUnit ((sym c) ∙ (a ∙ d)))) ⟩
      (((sym c) ∙ a ∙ d) ∙ refl   ≡ b)      ≃⟨ compPathlEquiv (assoc (sym c) (a ∙ d) refl) ⟩ 
      ((sym c) ∙ (a ∙ d) ∙ refl   ≡ b)      ≃⟨ compPathlEquiv (doubleCompPath≡compPath _ _ _) ⟩ 
      ((sym c) ∙∙ (a ∙ d) ∙∙ refl ≡ b)      ≃⟨ invEquiv (Square≃doubleComp (a ∙ d) b c refl) ⟩ 
      Square (a ∙ d) b c refl ■


  {-          
               d                         d ∙ sym b           
        a01 - - - > a11              a01 - - - > a10     
          ^           ^                ^           ^     
        a |           | b           a  |           | refl 
          |           |                |           |     
        a00 — — — > a10              a00 — — — > a10     
                c                            c           
  -}
  slideInvConcatSquareEquiv : ∀{ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
                              {a : a00 ≡ a01} {b : a10 ≡ a11} {c : a00 ≡ a10} {d : a01 ≡ a11} →
                              Square a b c d ≃ Square a refl c (d ∙ sym b)
  slideInvConcatSquareEquiv {a = a} {b = b} {c = c} {d = d} =
      Square a b c d                        ≃⟨ invEquiv rotateSquareEquiv ⟩
      Square d c (sym a) (sym b)            ≃⟨ slideConcatSquareEquiv ⟩
      Square (d ∙ (sym b)) c (sym a) refl   ≃⟨ rotateSquareEquiv ⟩
      Square a refl c (d ∙ sym b) ■


  theLemma : ∀{ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
             {a : a00 ≡ a01} {b : a10 ≡ a11} {c : a00 ≡ a10} {d : a01 ≡ a11} →
             Square (a ∙ d) b c refl ≃ Square c (d ∙ sym b) a refl
  theLemma {a = a} {b = b} {c = c} {d = d} = 
      Square (a ∙ d) b c refl               ≃⟨ invEquiv slideConcatSquareEquiv ⟩
      Square a b c d                        ≃⟨ slideInvConcatSquareEquiv ⟩
      Square a refl c (d ∙ sym b)           ≃⟨ flipSquareEquiv ⟩
      Square c (d ∙ sym b) a refl ■


-- End Module


-- This is Lemma 2.5.5

--       E
--     / |
--   /   v π   ≃ (x : X) →∙ fiber π (f x)
-- X --> B
--    f
triangleCompletion≃ : ∀{ℓ} {X∙ : Pointed ℓ} {E∙ : Pointed ℓ} {B∙ : Pointed ℓ} 
                      (f∙@(f , ptf) : X∙ →∙ B∙) → (π∙@(π , ptπ) : E∙ →∙ B∙) →
                      --                                     ≃ ((x : X) →∙ fiber π (f x))
                      (Σ[ g∙ ∈ (X∙ →∙ E∙) ] (π∙ ∘∙ g∙ ≡ f∙)) ≃ (Π∙ X∙ (λ x → fiber π (f x)) ((pt E∙ , ptπ ∙ sym ptf)))
triangleCompletion≃ {ℓ} {X∙@(X , ptX)} {E∙@(E , ptE)} {B∙@(B , ptB)} f∙@(f , ptf) π∙@(π , ptπ) =
  Σ[ g∙ ∈ (X∙ →∙ E∙) ]
      (π∙ ∘∙ g∙ ≡ f∙)                                                           ≃⟨ idEquiv _ ⟩
  Σ[ g∙ ∈ (Σ[ g ∈ (X → E) ] (g ptX ≡ ptE)) ]
      (π∙ ∘∙ g∙ ≡ f∙)                                                           ≃⟨ Σ-cong-equiv-snd (λ _ → →∙≡≃) ⟩
  Σ[ g∙ ∈ (Σ[ g ∈ (X → E) ] (g ptX ≡ ptE)) ]
      Σ[ H ∈ ((π ∘ (fst g∙)) ∼ f) ] (Square ((cong π (snd g∙)) ∙ ptπ) (ptf) (H ptX) refl)   
                                                                                ≃⟨ Σ-assoc-≃ ⟩
  Σ[ g ∈ (X → E) ] Σ[ ptg ∈ (g ptX ≡ ptE) ] Σ[ H ∈ ((π ∘ g) ∼ f) ]
      (Square ((cong π ptg) ∙ ptπ) (ptf) (H ptX) refl)                          ≃⟨ Σ-cong-equiv-snd (λ _ → 
                                                                                      Σ-cong-equiv-snd λ _ →
                                                                                          Σ-cong-equiv-snd λ _ → SquareLemmas.theLemma) ⟩
  Σ[ g ∈ (X → E) ] Σ[ ptg ∈ (g ptX ≡ ptE) ] Σ[ H ∈ ((π ∘ g) ∼ f) ]
      (Square (H ptX) (ptπ ∙ sym ptf) (cong π ptg) refl)                        ≃⟨ idEquiv _ ⟩
  Σ[ g ∈ (X → E) ] Σ[ ptg ∈ (g ptX ≡ ptE) ] Σ[ H ∈ ((π ∘ g) ∼ f) ]
      (PathP (λ i → π (ptg i) ≡ f ptX) (H ptX) (ptπ ∙ sym ptf))                 ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-swap-2-≃) ⟩
  Σ[ g ∈ (X → E) ] Σ[ H ∈ ((π ∘ g) ∼ f) ] Σ[ ptg ∈ (g ptX ≡ ptE) ]
      (PathP (λ i → π (ptg i) ≡ f ptX) (H ptX) (ptπ ∙ sym ptf))                 ≃⟨ invEquiv Σ-assoc-≃ ⟩
  Σ[ h ∈ (Σ[ g ∈ (X → E) ] ((π ∘ g) ∼ f)) ] Σ[ ptg ∈ ((fst h) ptX ≡ ptE) ]
      (PathP (λ i → π (ptg i) ≡ f ptX) ((snd h) ptX) (ptπ ∙ sym ptf))           ≃⟨ Σ-cong-equiv-snd (λ _ → ΣPath≃PathΣ ) ⟩
  Σ[ h ∈ (Σ[ g ∈ (X → E) ] ((π ∘ g) ∼ f)) ]
      (((fst h) ptX , (snd h) ptX) ≡ (ptE , ptπ ∙ sym ptf))                     ≃⟨ Σ-cong-equiv-fst (invEquiv Σ-Π-≃) ⟩
  Σ[ h ∈ ((x : X) → (Σ[ y ∈ E ] π y ≡ f x)) ]
      (h ptX ≡ (ptE , ptπ ∙ sym ptf))                                           ≃⟨ idEquiv _ ⟩
  Π∙ X∙ (λ x → fiber π (f x)) ((ptE , ptπ ∙ sym ptf)) ■ 





{-----------------------------------------------------------------------------
|                                                                            |
|                       [PART 3]  Defs & Lemma 2.5.6                         |
|                                                                            |
-----------------------------------------------------------------------------}

-- add more about the trunction level of the group
-- and abstract to concrete with torsors

-- If we have a group G, we refer to
--   the delooping by BG
--   the group itself is identified with the loopspace Ω(BG)
record ∞-Group {ℓ} : Type (ℓ-suc ℓ) where
  constructor ∞-grp
  field
    deloop : Pointed ℓ 
    connectednessWitness : isPathConnected (fst deloop)


∞-Group-Σ≃ : ∀ {ℓ} →
    (∞-Group {ℓ}) ≃ (Σ[ BG∙@(BG , ptBG) ∈ (Pointed ℓ) ] (isPathConnected BG))
∞-Group-Σ≃ = isoToEquiv (iso 
    (λ { (∞-grp deloop connectednessWitness) → (deloop , connectednessWitness) }) 
    (uncurry ∞-grp)
    ∼-refl ∼-refl
  )


-- loop space of a group
Ωgrp : ∀{ℓ} → ∞-Group {ℓ} → Pointed ℓ 
Ωgrp grp = Ω (∞-Group.deloop grp)


-- Group of symmetries of an object x : X
Aut : ∀ {ℓ} (X : Type ℓ) → (x : X) → Pointed ℓ
(Aut X x) .fst = (x ≡ x)
(Aut X x) .snd = refl -- is that the exemplar ?!


-- (BAut X x) can be thought of as the connected component
-- of X around x. it's a subtype of X
BAut : ∀ {ℓ} (X : Type ℓ) → (x : X) → Pointed ℓ
(BAut X x) .fst = Σ[ y ∈ X ] ∥ y ≡ x ∥₁
(BAut X x) .snd = (x , ∣ refl ∣₁)


BAut∙ : ∀ {ℓ} (X∙ : Pointed ℓ) → Pointed ℓ
BAut∙ (X∙) = BAut (typ X∙) (pt X∙)


BAut≡≃ : ∀ {ℓ} {X : Type ℓ} → {x : X} → {p q : (typ (BAut X x))} → 
         (p ≡ q) ≃ ((fst p) ≡ (fst q))
BAut≡≃ {_} {X} {x} {y1 , t1} {y2 , t2} = (invEquiv (Σ≡PropEquiv λ _ → squash₁))


-- Aut≡ΩBAut : ∀ {ℓ} (X : Type ℓ) → (x : X) → (Aut X x ≡ Ω (BAut X x))
-- Aut≡ΩBAut X x = ΣPathP (ua (helper) , λ i → {!   !}) 
--   where 
--     helper : (x ≡ x) ≃ fst (Ω (BAut X x))
--     helper = Σ≡PropEquiv (λ _ → squash₁)


   
--  C -- q ⟶ B
--  |         |  
--  p         g
--  ↓         ↓
--  A -- f ⟶ X
record Commutative-Square {ℓ} (C A B X : Type ℓ) : Type ℓ where
  constructor commutative-square
  field
    p : C → A
    q : C → B
    f : A → X
    g : B → X
    H : (f ∘ p) ∼ (g ∘ q)


canonicalPullback : ∀ {ℓ} {A B X : Type ℓ} → 
                    (A → X) → (B → X) → 
                    (Type ℓ)
canonicalPullback {_} {A} {B} {_} f g = Σ[ x ∈ A ] Σ[ y ∈ B ] (f x ≡ g y)


gap : ∀ {ℓ} {C A B X : Type ℓ} → ((commutative-square p q f g H) : Commutative-Square C A B X) → 
      (C → canonicalPullback f g)
gap (commutative-square p q f g H) c = (p c , q c , H c)


-- alternative definition
isPullback : ∀ {ℓ} {C A B X : Type ℓ} → (Commutative-Square C A B X) → 
              (Type ℓ)
isPullback sq = isEquiv (gap sq)


--  F -- i ⟶ E
--  |         |  
--  |         p
--  ↓         ↓
--  1 -----⟶ G
record Fiber-Sequence {ℓ} (F∙ E∙ G∙ : Pointed ℓ) : Type ℓ where
  constructor fiber-sequence
  field
    i∙ : F∙ →∙ E∙
    p∙ : E∙ →∙ G∙
    H : (const∙ F∙ G∙) ≡ (p∙ ∘∙ i∙)
    pb : isPullback (commutative-square (const tt*) (fst i∙) (const (pt G∙)) (fst p∙) (→∙≡ToHomotopy H))

-- _↪∙_↠∙_ -- \hookrightarrow , \rr- 
syntax Fiber-Sequence F E G = F ↪∙ E ↠∙ G


fiber-sequence-Σ≃ : ∀ {ℓ} {F∙ E∙ G∙ : Pointed ℓ} →
    (F∙ ↪∙ E∙ ↠∙ G∙) ≃
    (Σ[ i∙ ∈ (F∙ →∙ E∙) ] Σ[ p∙ ∈ (E∙ →∙ G∙) ] Σ[ H ∈ (const∙ F∙ G∙) ≡ (p∙ ∘∙ i∙) ]
        (isPullback (commutative-square (const tt*) (fst i∙) (const (pt G∙)) (fst p∙) (→∙≡ToHomotopy H))))
fiber-sequence-Σ≃ = isoToEquiv (iso 
    (λ { (fiber-sequence i∙ p∙ H pb) → (i∙ , p∙ , H , pb) }) 
    (uncurry3 fiber-sequence)
    ∼-refl ∼-refl
  )


fiber-sequence-pb≡ : ∀ {ℓ} {F∙@(F , ptF) E∙@(E , ptE) G∙@(_ , ptG) : Pointed ℓ} →
                     (i∙ : F∙ →∙ E∙) (p∙ : E∙ →∙ G∙) (H : (const∙ F∙ G∙) ≡ (p∙ ∘∙ i∙)) → 
                     (isPullback (commutative-square (const tt*) (fst i∙) (const ptG) (fst p∙) (→∙≡ToHomotopy H))) ≡
                     (isEquiv {A = F} {B = fiber (fst p∙) ptG} (λ x → (fst i∙ x) , (sym (→∙≡ToHomotopy H x))))
fiber-sequence-pb≡ {ℓ} {F∙@(F , ptF)} {E∙@(E , ptE)} {G∙@(B , ptG)} i∙ p∙ H =
  isPullback (commutative-square (const tt*) (fst i∙) (const ptG) (fst p∙) (→∙≡ToHomotopy H))     ≡⟨ refl ⟩
  isEquiv (gap (commutative-square (const tt*) (fst i∙) (const ptG) (fst p∙) (→∙≡ToHomotopy H))) ≡⟨ refl ⟩
  isEquiv {A = F} {B = canonicalPullback (const ptG) (fst p∙)}
      (λ x → const tt* x , fst i∙ x , →∙≡ToHomotopy H x)                ≡⟨ refl ⟩
  isEquiv {A = F} {B = (Σ[ x ∈ Unit* {ℓ} ] Σ[ y ∈ E ] (ptG ≡ (fst p∙) y))}
      (λ x → const tt* x , fst i∙ x , →∙≡ToHomotopy H x)                ≡⟨ refl ⟩
  isEquiv {A = F} {B = ((Unit* {ℓ}) × (Σ[ y ∈ E ] ptG ≡ (fst p∙) y))}
      (λ x → tt* , fst i∙ x , →∙≡ToHomotopy H x)                        ≡⟨ sym (isEquiv-Unit×-≡ (λ x → fst i∙ x , →∙≡ToHomotopy H x)) ⟩
  isEquiv {A = F} {B = (Σ[ y ∈ E ] ptG ≡ (fst p∙) y)}
      (λ x → fst i∙ x , →∙≡ToHomotopy H x)                              ≡⟨ isEquiv-Σ-snd-≃ ptG (fst i∙) (fst p∙) (→∙≡ToHomotopy H) ⟩
  isEquiv {A = F} {B = (Σ[ y ∈ E ] (fst p∙) y ≡ ptG)}
      (λ x → fst i∙ x , sym (→∙≡ToHomotopy H x))                        ≡⟨ refl ⟩
  isEquiv {A = F} {B = (fiber (fst p∙) ptG)}
      (λ x → fst i∙ x , sym (→∙≡ToHomotopy H x)) ∎ 


fiber-sequence-Σ≃' : ∀ {ℓ} {F∙@(F , _) E∙@(_ , _) G∙@(_ , ptG) : Pointed ℓ} →
                     (F∙ ↪∙ E∙ ↠∙ G∙) ≃
                     (Σ[ p∙ ∈ (E∙ →∙ G∙) ] Σ[ i∙ ∈ (F∙ →∙ E∙) ] Σ[ H ∈ (p∙ ∘∙ i∙) ≡ (const∙ F∙ G∙) ]
                        isEquiv {A = F} {B = fiber (fst p∙) ptG} (λ x → (fst i∙ x) , (→∙≡ToHomotopy H x)))
fiber-sequence-Σ≃' {ℓ} {F∙@(F , _)} {E∙@(_ , _)} {G∙@(_ , ptG)} =
    (F∙ ↪∙ E∙ ↠∙ G∙)                                                                 ≃⟨ fiber-sequence-Σ≃ ⟩
    Σ[ i∙ ∈ (F∙ →∙ E∙) ] Σ[ p∙ ∈ (E∙ →∙ G∙) ] Σ[ H ∈ (const∙ F∙ G∙) ≡ (p∙ ∘∙ i∙) ]
        isPullback (commutative-square (const tt*) (fst i∙) (const (pt G∙)) (fst p∙) (→∙≡ToHomotopy H)) 
                                                                                      ≃⟨ (Σ-cong-equiv-snd λ i∙ →
                                                                                            Σ-cong-equiv-snd λ p∙ →
                                                                                              Σ-cong-equiv-snd λ H →
                                                                                                pathToEquiv (fiber-sequence-pb≡ i∙ p∙ H)) ⟩
    Σ[ i∙ ∈ (F∙ →∙ E∙) ] Σ[ p∙ ∈ (E∙ →∙ G∙) ] Σ[ H ∈ (const∙ F∙ G∙) ≡ (p∙ ∘∙ i∙) ]
        isEquiv {A = F} {B = fiber (fst p∙) ptG} (λ x → (fst i∙ x) , (sym (→∙≡ToHomotopy H x))) 
                                                                                      ≃⟨ (Σ-cong-equiv-snd λ _ →
                                                                                            Σ-cong-equiv-snd λ _ →
                                                                                              Σ-cong-equiv-fst (isoToEquiv symIso)) ⟩
    Σ[ i∙ ∈ (F∙ →∙ E∙) ] Σ[ p∙ ∈ (E∙ →∙ G∙) ] Σ[ H ∈ (p∙ ∘∙ i∙) ≡ (const∙ F∙ G∙) ]
        isEquiv {A = F} {B = fiber (fst p∙) ptG} (λ x → (fst i∙ x) , (→∙≡ToHomotopy H x)) 
                                                                                      ≃⟨ Σ-swap-2-≃ ⟩
    Σ[ p∙ ∈ (E∙ →∙ G∙) ] Σ[ i∙ ∈ (F∙ →∙ E∙) ] Σ[ H ∈ (p∙ ∘∙ i∙) ≡ (const∙ F∙ G∙) ]
        isEquiv {A = F} {B = fiber (fst p∙) ptG} (λ x → (fst i∙ x) , (→∙≡ToHomotopy H x)) ■ 



record ∞-Group-Extension {ℓ} (G F : ∞-Group {ℓ}) : Type (ℓ-suc ℓ) where
  constructor ext
  field
    E : ∞-Group {ℓ}
    seq : (∞-Group.deloop F) ↪∙ (∞-Group.deloop E) ↠∙ (∞-Group.deloop G)

∞-Group-Extension-Σ≃ : ∀ {ℓ} {G F : ∞-Group {ℓ}} →
    (∞-Group-Extension G F) ≃ (Σ[ E ∈ ∞-Group ] ((∞-Group.deloop F) ↪∙ (∞-Group.deloop E) ↠∙ (∞-Group.deloop G)))
∞-Group-Extension-Σ≃ = isoToEquiv (iso 
    (λ { (ext E seq) → (E , seq) }) 
    (uncurry ext) -- λ pair → ext (fst pair) (snd pair)
    ∼-refl ∼-refl
  )



-- alternative ≃∙ definition equivalency with the normal one
alt≃∙Equiv : ∀{ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'} →
    (A∙ ≃∙ B∙)                      ≃ (Σ[ f∙ ∈ (A∙ →∙ B∙) ] isEquiv (fst f∙))
--  Σ[ e ∈ A ≃ B ] fst e ptA ≡ ptB
alt≃∙Equiv {ℓ} {ℓ'} {A∙@(A , ptA)} {B∙@(B , ptB)} =
    (A∙ ≃∙ B∙)                                ≃⟨ idEquiv _ ⟩
    Σ[ e ∈ A ≃ B ]
        (fst e ptA ≡ ptB)                     ≃⟨ idEquiv _ ⟩
    Σ[ e ∈ (Σ[ f ∈ (A → B)] (isEquiv f)) ]
        (fst e ptA ≡ ptB)                     ≃⟨ Σ-assoc-≃ ⟩
    Σ[ f ∈ (A → B)] Σ[ eproof ∈ (isEquiv f) ]
        (f ptA ≡ ptB)                         ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-swap-≃) ⟩
    Σ[ f ∈ (A → B)] Σ[ ptf ∈ (f ptA ≡ ptB) ]
        (isEquiv f)                           ≃⟨ invEquiv Σ-assoc-≃ ⟩
    Σ[ f∙ ∈ (Σ[ f ∈ (A → B) ] (f ptA ≡ ptB))]
        (isEquiv (fst f∙))                    ≃⟨ idEquiv _ ⟩
    Σ[ f∙ ∈ (A∙ →∙ B∙) ]
        (isEquiv (fst f∙))  ■ 



invEquivEquiv∙ : ∀{ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'} →
            (A∙ ≃∙ B∙) ≃ (B∙ ≃∙ A∙)
invEquivEquiv∙ {_} {_} {A∙@(A , ptA)} {B∙@(B , ptB)} = 
    (A∙ ≃∙ B∙)                                
                                              ≃⟨ idEquiv _ ⟩
    Σ[ e ∈ A ≃ B ]
      fst e ptA ≡ ptB                         
                                              ≃⟨ Σ-cong-equiv-fst invEquivEquiv ⟩
    Σ[ e ∈ B ≃ A ]
      fst (invEquiv e) ptA ≡ ptB              
                                              ≃⟨ (Σ-cong-equiv-snd λ e → congEquiv e) ⟩
    Σ[ e ∈ B ≃ A ]
      (fst e) (fst (invEquiv e) ptA) ≡ (fst e) ptB 
                                              ≃⟨ (Σ-cong-equiv-snd λ _ → idInv-≃) ⟩
    Σ[ e ∈ B ≃ A ]
      (fst e) ptB ≡ (fst e) (fst (invEquiv e) ptA)
                                              ≃⟨ idEquiv _ ⟩
    Σ[ e ∈ B ≃ A ]
      (let eiso = (equivToIso e) in
      ((fst e) ptB) ≡ ((Iso.fun eiso) ∘ (Iso.inv eiso)) ptA)
                                              ≃⟨ (Σ-cong-equiv-snd λ e → 
                                                    compPathrEquiv (Iso.rightInv (equivToIso e) ptA)) ⟩
    Σ[ e ∈ B ≃ A ]
      (fst e) ptB ≡ ptA         
                                              ≃⟨ idEquiv _ ⟩
    (B∙ ≃∙ A∙)  ■ 


∞-Group-Extension-lemma≃ : ∀{ℓ} {G@(∞-grp BG∙ WG) F@(∞-grp BF∙ WF) : ∞-Group {ℓ}} →
                           (∞-Group-Extension G F) ≃
                           (Σ[ BE∙ ∈ (Pointed ℓ) ] Σ[ Bp ∈ (BE∙ →∙ BG∙) ] ((fiber∙ Bp) ≃∙ BF∙))
∞-Group-Extension-lemma≃ {ℓ} {G@(∞-grp BG∙@(BG , ptBG) WG)} {F@(∞-grp BF∙@(BF , ptBF) WF)} =
    ∞-Group-Extension G F                          
                            ≃⟨ ∞-Group-Extension-Σ≃ ⟩
    Σ[ (∞-grp BE∙@(BE , ptBE) _) ∈ ∞-Group ]
        (BF∙ ↪∙ BE∙ ↠∙ BG∙)                       
                            ≃⟨ (Σ-cong-equiv-snd λ _ → fiber-sequence-Σ≃') ⟩

    Σ[ (∞-grp BE∙@(BE , ptBE) _) ∈ ∞-Group {ℓ} ]
        Σ[ p∙ ∈ (BE∙ →∙ BG∙) ] Σ[ i∙ ∈ (BF∙ →∙ BE∙) ] Σ[ H ∈ (p∙ ∘∙ i∙) ≡ (const∙ BF∙ BG∙) ]
            isEquiv {A = BF} {B = fiber (fst p∙) ptBG} (λ x → (fst i∙ x) , (→∙≡ToHomotopy H x))
                            ≃⟨ idEquiv _ ⟩

    Σ[ (∞-grp BE∙@(BE , ptBE) _) ∈ ∞-Group {ℓ} ] Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
        Σ[ i∙ ∈ (BF∙ →∙ BE∙) ] Σ[ H ∈ (p∙ ∘∙ i∙) ≡ (const∙ BF∙ BG∙) ]
            isEquiv {A = BF} {B = fiber (fst p∙) ptBG} (λ x → (fst i∙ x) , (→∙≡ToHomotopy H x)) 
                            ≃⟨ (Σ-cong-equiv-snd λ _ →
                                    Σ-cong-equiv-snd λ _ → invEquiv Σ-assoc-≃) ⟩

    Σ[ (∞-grp BE∙@(BE , ptBE) _) ∈ ∞-Group {ℓ} ] Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
        Σ[ i∙,H ∈ (Σ[ i∙ ∈ (BF∙ →∙ BE∙) ] (p∙ ∘∙ i∙) ≡ (const∙ BF∙ BG∙)) ] 
            isEquiv {A = BF} {B = fiber (fst p∙) ptBG} (λ x → (fst (fst i∙,H) x) , (→∙≡ToHomotopy (snd i∙,H) x))
                            ≃⟨ (Σ-cong-equiv-snd λ _ →
                                    Σ-cong-equiv-snd λ p∙ →
                                        Σ-cong-equiv-fst (triangleCompletion≃ (const∙ BF∙ BG∙) p∙)) ⟩

    Σ[ (∞-grp BE∙@(BE , ptBE) _) ∈ ∞-Group {ℓ} ] Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
        Σ[ theMap ∈ (Π∙ BF∙ (λ x → fiber (fst p∙) (fst (const∙ BF∙ BG∙) x)) ((ptBE , (snd p∙) ∙ sym (snd (const∙ BF∙ BG∙))))) ] 
            isEquiv {A = BF} {B = fiber (fst p∙) ptBG} (λ x → fst theMap x)
                            ≃⟨ idEquiv _ ⟩

    Σ[ (∞-grp BE∙@(BE , ptBE) _) ∈ ∞-Group {ℓ} ] Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
        Σ[ theMap ∈ (Π∙ BF∙ (λ x → fiber (fst p∙) ptBG) (ptBE , (snd p∙) ∙ refl)) ] 
            isEquiv (fst theMap)
                            ≃⟨ idEquiv _ ⟩

    Σ[ (∞-grp BE∙@(BE , ptBE) _) ∈ ∞-Group {ℓ} ] Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
        Σ[ e ∈ (Σ[ f ∈ (fst BF∙ → fst (fiber∙ p∙)) ] f ptBF ≡ (ptBE , (snd p∙) ∙ refl)) ]
            isEquiv (fst e)
                            ≃⟨ (Σ-cong-equiv-snd λ _ →
                                    Σ-cong-equiv-snd λ p∙ →
                                        Σ-cong-equiv-fst (Σ-cong-equiv-snd λ _ →
                                                            compPathrEquiv (ΣPathP (refl , sym (rUnit (snd p∙)))))) ⟩

    Σ[ (∞-grp BE∙@(BE , ptBE) _) ∈ ∞-Group {ℓ} ] Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
        Σ[ e ∈ (Σ[ f ∈ (fst BF∙ → fst (fiber∙ p∙)) ] f ptBF ≡ (ptBE , snd p∙)) ]
            isEquiv (fst e)
                            ≃⟨ idEquiv _ ⟩

    Σ[ (∞-grp BE∙ _) ∈ ∞-Group {ℓ} ] Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
        Σ[ e ∈ (BF∙ →∙ (fiber∙ p∙)) ]
            isEquiv (fst e)
                            ≃⟨ (Σ-cong-equiv-snd λ _ → Σ-cong-equiv-snd λ _ → invEquiv alt≃∙Equiv) ⟩

    Σ[ (∞-grp BE∙ _) ∈ ∞-Group {ℓ} ] Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
        BF∙ ≃∙ (fiber∙ p∙)
                            ≃⟨ (Σ-cong-equiv-snd λ _ → Σ-cong-equiv-snd λ _ → invEquivEquiv∙) ⟩

    Σ[ (∞-grp BE∙ _) ∈ ∞-Group {ℓ} ] Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
        (fiber∙ p∙) ≃∙ BF∙
                            ≃⟨ Σ-cong-equiv-fst ∞-Group-Σ≃ ⟩

    Σ[ (BE∙@(BE , _) , WE) ∈ (Σ[ BE∙ ∈ (Pointed ℓ) ] (isPathConnected (fst BE∙))) ]
        Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
            (fiber∙ p∙) ≃∙ BF∙
                            ≃⟨ Σ-assoc-≃ ⟩

    Σ[ BE∙@(BE , _) ∈ (Pointed ℓ) ] Σ[ WE ∈ (isPathConnected BE) ]
        Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
            (fiber∙ p∙) ≃∙ BF∙
                            ≃⟨ (Σ-cong-equiv-snd λ _ → Σ-swap-2-≃) ⟩

    Σ[ BE∙@(BE , _) ∈ (Pointed ℓ) ] Σ[ p∙ ∈ (BE∙ →∙ BG∙) ]
        Σ[ WE ∈ (isPathConnected BE) ]
            (fiber∙ p∙) ≃∙ BF∙
                            ≃⟨ (Σ-cong-equiv-snd λ _ → Σ-cong-equiv-snd λ _ → Σ-swap-≃) ⟩

    Σ[ BE∙@(BE , _) ∈ (Pointed ℓ) ] Σ[ Bp∙ ∈ (BE∙ →∙ BG∙) ]
        Σ[ e∙ ∈ ((fiber∙ Bp∙) ≃∙ BF∙) ]
            isPathConnected BE
                            ≃⟨ (Σ-cong-equiv-snd λ BE∙@(BE , _) →
                                    Σ-cong-equiv-snd λ Bp∙@(Bp , _) →
                                        Σ-contractSnd λ e∙ → let isConnFibBp : isPathConnected (fiber Bp ptBG)
                                                                 isConnFibBp = invEq (cong≃ isPathConnected (fst e∙)) WF

                                                                 isConnFibX : (x : BG) → isPathConnected (fiber Bp x)
                                                                 isConnFibX = connected→connectedBaseSufficient Bp WG ptBG isConnFibBp

                                                                 isEquivTotal : BE ≃ Σ BG (fiber Bp)
                                                                 isEquivTotal = totalEquiv Bp

                                                                 isConnTotal : isPathConnected (Σ BG (fiber Bp))
                                                                 isConnTotal = isPathConnectedTotal WG isConnFibX
                                                                  
                                                             in inhProp→isContr 
                                                                    (invEq (cong≃ isPathConnected isEquivTotal) isConnTotal)
                                                                    isPropIsPathConnected)⟩

    Σ[ BE∙ ∈ (Pointed ℓ) ] Σ[ Bp ∈ (BE∙ →∙ BG∙) ]
        (fiber∙ Bp) ≃∙ BF∙  ■ 





{-----------------------------------------------------------------------------
|                                                                            |
|                  [PART 4]  Putting Everything Together                     |
|                                 Theorem 2.5.7                              |
|                                                                            |
-----------------------------------------------------------------------------}


connectedTypeMapsIntoConnectedComponent : ∀ {ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'} → isPathConnected (typ A∙) →
                                          (A∙ →∙ B∙) ≃ (A∙ →∙ BAut∙ B∙)             
connectedTypeMapsIntoConnectedComponent {_} {_} {A∙@(A , ptA)} {B∙@(B , ptB)} W =
  (A∙ →∙ B∙)            ≃⟨ invEquiv (Σ-contractSnd (λ { (g , ptg) → 
                                                        isContrΠ λ a → 
                                                          inhProp→isContr 
                                                            (PT.map 
                                                              (λ p → cong g p ∙ ptg) 
                                                              (a ≡ptA))
                                                            squash₁
                                                      })) ⟩                    
  (Σ[ g∙ ∈ (A∙ →∙ B∙) ] ((a : A) → ∥ (fst g∙) a ≡ ptB ∥₁))                  ≃⟨ Σ-assoc-≃ ⟩
  (Σ[ g ∈ (A → B) ] (g ptA ≡ ptB) × ((a : A) → ∥ g a ≡ ptB ∥₁))             ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-swap-≃) ⟩
  (Σ[ g ∈ (A → B) ] ((a : A) → ∥ g a ≡ ptB ∥₁) × (g ptA ≡ ptB))             ≃⟨ idEquiv _ ⟩
  (Σ[ g ∈ (A → B) ] Σ[ p ∈ ((a : A) → ∥ g a ≡ ptB ∥₁) ] (g ptA ≡ ptB))      ≃⟨ invEquiv Σ-assoc-≃ ⟩
  (Σ[ f ∈ (Σ[ g ∈ (A → B) ] ((a : A) → ∥ g a ≡ ptB ∥₁)) ] ((fst f) ptA ≡ ptB))
                                                                            ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv BAut≡≃) ⟩
  (Σ[ f ∈ (Σ[ g ∈ (A → B) ] ((a : A) → ∥ g a ≡ ptB ∥₁)) ] (((fst f) ptA , (snd f) ptA) ≡ (ptB , ∣ refl ∣₁)))
                                                                            ≃⟨ Σ-cong-equiv-fst (invEquiv Σ-Π-≃) ⟩
  (Σ[ f ∈ (A → (Σ[ b ∈ B ] ∥ b ≡ ptB ∥₁)) ] (f ptA ≡ (ptB , ∣ refl ∣₁)))      ≃⟨ idEquiv _ ⟩
  (A∙ →∙ ((Σ[ b ∈ B ] ∥ b ≡ ptB ∥₁) ,
          (ptB , ∣ refl ∣₁)))                                                 ≃⟨ idEquiv _ ⟩
  (A∙ →∙ (BAut∙ B∙)) ■
    where
      _≡ptA : (a : A) → ∥ a ≡ ptA ∥₁
      _≡ptA a = (isPathConnected→isPathConnected' W) .snd a ptA



_ : ∀ {ℓ} {BG∙@(BG , ptBG) : Pointed ℓ} → 
    {x@((BE , ptBE) , (Bp , ptBp)) : (Σ[ BE∙ ∈ (Pointed ℓ) ] (BE∙ →∙ BG∙) )} → 
    (equivFun equivIntoAndOutMaps∙ x) ≡ (fiber Bp , ptBE , ptBp)
_ = refl


theorem : ∀{ℓ} {G@(∞-grp BG∙@(BG , ptBG) WG) 
                F@(∞-grp BF∙@(BF , ptBF) WF) : ∞-Group {ℓ}} →
          (∞-Group-Extension G F) ≃ (BG∙ →∙ BAut (Type ℓ) BF)
theorem {ℓ} {G@(∞-grp BG∙@(BG , ptBG) WG)} {F@(∞-grp BF∙@(BF , ptBF) WF)}=
  ∞-Group-Extension G F                                   ≃⟨ ∞-Group-Extension-lemma≃ ⟩
  Σ[ BE∙ ∈ (Pointed ℓ) ] Σ[ Bp ∈ (BE∙ →∙ BG∙) ]
      (fiber∙ Bp) ≃∙ BF∙                                  ≃⟨ invEquiv Σ-assoc-≃ ⟩
  Σ[ x ∈ (Σ[ BE∙ ∈ (Pointed ℓ) ] (BE∙ →∙ BG∙) ) ]
      (fiber∙ (snd x)) ≃∙ BF∙                             ≃⟨ idEquiv _ ⟩ -- using the previous refl lemma
  Σ[ x ∈ (Σ[ BE∙ ∈ (Pointed ℓ) ] (BE∙ →∙ BG∙) ) ]
      (fiber (fst (snd x)) ptBG , (snd ∘ fst) x , (snd ∘ snd) x) ≃∙ BF∙
                                                          ≃⟨ Σ-cong-equiv-fst equivIntoAndOutMaps∙ ⟩
  Σ[ y ∈ (Σ[ c ∈ (BG → Type ℓ) ] (c ptBG)) ]
      ((fst y) ptBG , (snd y)) ≃∙ BF∙                     ≃⟨ Σ-assoc-≃ ⟩
  Σ[ c ∈ (BG → Type ℓ) ] Σ[ ptC ∈ (c ptBG) ] 
      (c ptBG , ptC) ≃∙ BF∙                               ≃⟨ (Σ-cong-equiv-snd λ _ → Σ-cong-equiv-snd λ _ → invEquivEquiv∙) ⟩
  Σ[ c ∈ (BG → Type ℓ) ] Σ[ ptC ∈ (c ptBG) ] 
      BF∙ ≃∙ (c ptBG , ptC)                               ≃⟨ idEquiv _ ⟩
  Σ[ c ∈ (BG → Type ℓ) ] Σ[ ptC ∈ (c ptBG) ] 
      Σ[ e ∈ (BF ≃ c ptBG)] (equivFun e) ptBF ≡ ptC
                                                          ≃⟨ (Σ-cong-equiv-snd λ _ → Σ-swap-2-≃) ⟩
  Σ[ c ∈ (BG → Type ℓ) ] Σ[ e ∈ (BF ≃ c ptBG)]
      Σ[ ptC ∈ (c ptBG) ] (equivFun e) ptBF ≡ ptC         ≃⟨ (Σ-cong-equiv-snd λ _ →
                                                          Σ-contractSnd λ e → isContrBasedPathSpace ((equivFun e) ptBF)) ⟩
  Σ[ c ∈ (BG → Type ℓ) ]
      BF ≃ c ptBG                                         ≃⟨ (Σ-cong-equiv-snd λ _ → invEquivEquiv) ⟩
  Σ[ c ∈ (BG → Type ℓ) ]
      c ptBG ≃ BF                                         ≃⟨ (Σ-cong-equiv-snd λ _ → invEquiv univalence) ⟩
  Σ[ c ∈ (BG → Type ℓ) ]
      c ptBG ≡ BF                                         ≃⟨ idEquiv _ ⟩
  BG∙ →∙ (Type ℓ , BF)                                    ≃⟨ connectedTypeMapsIntoConnectedComponent {A∙ = BG∙} WG ⟩
  BG∙ →∙ BAut (Type ℓ) BF ■
