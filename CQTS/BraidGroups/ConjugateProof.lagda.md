{-# OPTIONS --safe #-}
```
module homework-solutions.Extra.ConjugateProof where

open import Cubical.Foundations.Prelude

private
    variable
        ℓ : Level

-- * Define the circle
data S¹ : Type where
    base : S¹
    loop : base ≡ base

TypeWithALoop : ∀ {ℓ} →  Type (ℓ-suc ℓ)
TypeWithALoop {ℓ} = Σ[ X ∈ Type ℓ ] (S¹ → X) 

-- Paths (X , c) ≡ (X , c) in TypeWithALoop are
-- f : X ≃ X  so that f(c) = β ∙ c ∙ β⁻¹
```

-- * betterloop (h) square:

      f base       f base
        ^             ^
        |             |
        |             |
 sym p  |             | sym p
        |             |               ^
        |             |             j |
        g — — — - - - > g             ∙ — >
            g loop i                    i

```
betterloop : {X : Type ℓ} (f g : S¹ → X) 
             → (f ≡ g) 
             → (S¹ → X)
betterloop f g p base = f base
betterloop f g p (loop i) = hcomp (λ { j (i = i0) → (sym p) j base 
                                     ; j (i = i1) → (sym p) j base }) 
                            (g (loop i))

∂ : I → I
∂ i = i ∨ ~ i

betterloopSides : {X : Type ℓ} (f g : S¹ → X) → (p : f ≡ g) 
                  → (i j : I) → Partial (∂ i) X
betterloopSides f g p i j (i = i0) = sym p j base
betterloopSides f g p i j (i = i1) = sym p j base
```

-- * lemma cube:

                        refl
            f base - - - - - - - - > f base
              / ^                 / ^
      f l   /   |            h  /   |
          /     |   refl      /     |
   f base - - - - - - - - > f base  |
        ^       |           ^       | sym p              ^   j
        |       | sym p     |       |                  k | /
        |       |           | sym p |                    ∙ — >
        |       |    refl   |       |                      i
  sym p |       g - - - - - | - - > g
        | g l /             |     /
        |   /               |   /  g loop j
        | /                 | /
        g - - - - - - - - > g
                refl

```
lemmaFaces : {X : Type ℓ} (f g : S¹ → X) → (p : f ≡ g) 
             → (i : I) → (j : I) → I → Partial (∂ i ∨ ∂ j) X
lemmaFaces f g p i j k (i = i0) = sym p k (loop j)
lemmaFaces f g p i j k (i = i1) = hfill (betterloopSides f g p j) (inS (g (loop j))) k
lemmaFaces f g p i j k (j = i0) = sym p k base
lemmaFaces f g p i j k (j = i1) = sym p k base

lemma : {X : Type ℓ} (f g : S¹ → X) 
        → (p : f ≡ g)
        → (f ≡ betterloop f g p)
lemma f g p i base = betterloop f g p base
lemma f g p i (loop j) = hcomp (lemmaFaces f g p i j) (g (loop j))
```

-- * h' square:

     f base        f base
        ^             ^
        |             |
        |             |
 sym β  |             | sym β
        |             |               ^
        |             |             j |
        g — — — - - - > g             ∙ — >
            g loop i                    i

```
h' : {X : Type ℓ} (f g : S¹ → X) 
     → (β : f base ≡ g base)
     → (S¹ → X)
h' f g β base = f base
h' f g β (loop i) = hcomp (λ {j (i = i0) → sym β j ; 
                              j (i = i1) → sym β j}) 
                    (g (loop i))

h'Sides : {X : Type ℓ} (f g : S¹ → X) 
          → (β : f base ≡ g base)
          → (i j : I) → Partial (∂ i) X
h'Sides f g β i j (i = i0) = sym β j
h'Sides f g β i j (i = i1) = sym β j

lemma2Faces : {X : Type ℓ} (f g : S¹ → X) 
              → (β : f base ≡ g base)
              → (p : Square (cong f loop) (λ j → h' f g β (loop j)) refl refl )
              → (i : I) → (j : I) → I → Partial (∂ i ∨ ∂ j) X
lemma2Faces f g β p i j k (i = i0) = p (~ k) j
lemma2Faces f g β p i j k (i = i1) = hfill (h'Sides f g β j) (inS (g (loop j))) (~ k )
lemma2Faces f g β p i j k (j = i0) = β (i ∧ k) 
lemma2Faces f g β p i j k (j = i1) = β (i ∧ k) 

lemma2 : {X : Type ℓ} (f g : S¹ → X) 
         → (β : f base ≡ g base)
         → (p : Square (cong f loop) ((λ j → h' f g β (loop j))) refl refl )
         → (f ≡ g)
lemma2 f g β p i base = β i
lemma2 f g β p i (loop j) = hcomp (lemma2Faces f g β p i j) 
                                  (h' f g β (loop j))
``` 