module InductiveBraidGroup where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; zero; suc; predℕ; _+_)
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Empty as ⊥

data BBraidGroup : (n : ℕ) → Type where
  base  : BBraidGroup zero
  ι : ∀ {n} → BBraidGroup n → BBraidGroup (suc n)
  σ : ∀ {n} → ℕ.elim {A = BBraidGroup} base (λ n → ι) n ≡ ℕ.elim {A = BBraidGroup} base (λ n → ι) n

  comm : ∀ {n} (p : ℕ.elim {A = BBraidGroup} base (λ n → ι) n ≡ ℕ.elim {A = BBraidGroup} base (λ n → ι) n) →
    Square σ σ (λ i → ι (ι (p i))) (λ i → ι (ι (p i)))

  pull-common : ∀ {n} → Path (BBraidGroup (suc n))
                             (ℕ.elim {A = BBraidGroup} base (λ n → ι) (suc n))
                             (ℕ.elim {A = BBraidGroup} base (λ n → ι) (suc n))
  pull-left : ∀ {n} → Square σ (cong ι σ) σ (pull-common {n})
  pull-right : ∀ {n} → Square (cong ι σ) σ (cong ι σ) (pull-common {n})
