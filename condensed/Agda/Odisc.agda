{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit.Base

private
  variable
    ℓ ℓ' : Level

Odisc : Type (ℓ) → Type (ℓ-suc ℓ)
Odisc {ℓ = ℓ} Y = Σ[ X ∈ (Sequence ℓ) ] ((SeqColim X ≡ Y) × ((n : ℕ) → isFinSet (Sequence.obj X n)))

data Two : Type₀ where
  𝟘 : Two
  𝟙 : Two

Cantor : Type₀
Cantor = ℕ → Two

isOpen : Type (ℓ) → Type {! !}
isOpen P = (isProp P) × (∃[ α ∈ Cantor ] ( ( P →  (∃[ n ∈ ℕ ] (α n ≡ 𝟙))) × ( ∃[ n ∈ ℕ ] (α n ≡ 𝟙) → P)))

isDiscrete : Type ℓ → Type {! !}
isDiscrete X = (x y : X) → isOpen ( x ≡ y)

Odisc→Discrete : (E : Type ℓ) → Odisc E → isDiscrete E
Odisc→Discrete E (En , ColimEn=E , EnFinite) x y = {! !} , {! !}

