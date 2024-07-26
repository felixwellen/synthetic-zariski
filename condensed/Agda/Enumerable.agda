{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude hiding (_∧_;_∨_)
open import Cubical.Functions.Surjection 
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra.Base

private 
  variable 
   ℓ ℓ' : Level

isEnumerable : Type ℓ  → Type ℓ
isEnumerable A = ∥ Σ (ℕ → (Unit ⊎ A)) isSurjection ∥₁

data freeBA (G : Type ℓ) : Type ℓ where
  generator : G → freeBA G
  _∧_ : freeBA G → freeBA G → freeBA G
  _∨_ : freeBA G → freeBA G → freeBA G
  ¬_  : freeBA G → freeBA G
  1B : freeBA G
  0B : freeBA G
  assoc∨ : {x y z : freeBA G} →  (x ∨ ( y ∨ z ) ≡ ( x ∨ y ) ∨ z )
  assoc∧ : {x y z : freeBA G} →  (x ∧ ( y ∧ z ) ≡ ( x ∧ y ) ∧ z )
  com∨ : {x y : freeBA G} →  (x ∨  y ) ≡ (y ∨ x)
  com∧ : {x y : freeBA G} →  (x ∧  y ) ≡ (y ∧ x)
  distrA : {x y z : freeBA G} → ( x ∧ ( y ∨ z)) ≡ (x ∧ y) ∨ (x ∧ z)
  distrB : {x y z : freeBA G} → ( x ∨ ( y ∧ z)) ≡ (x ∨ y) ∧ (x ∨ z)
  0∨ : {x : freeBA G} → x ∨ 0B ≡ x
  0∧ : {x : freeBA G} → x ∧ 0B ≡ 0B
  1∨ : {x : freeBA G} → x ∨ 1B ≡ 1B 
  1∧ : {x : freeBA G} → x ∧ 1B ≡ x
  ∨idem   : {x : freeBA G} → x ∧ x ≡ x
  ∧idem   : {x : freeBA G} → x ∧ x ≡ x
  absorpA : {x y : freeBA G} →  x ∧ (x ∨ y )  ≡ x
  absorpB : {x y : freeBA G} →  x ∨ (x ∧ y )  ≡ x
  ¬∧ : {x : freeBA G} → (x ∧ (¬ x)) ≡ 0B
  ¬∨ : {x : freeBA G} → (x ∨ (¬ x)) ≡ 1B

¬¬law : {G : Type ℓ} → { x : freeBA G} → ¬ ¬ x ≡ x
¬¬law = {! !}

