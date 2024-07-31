{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude --hiding (_∧_;_∨_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection 
open import Cubical.HITs.PropositionalTruncation renaming (map to truncMap)
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
--open import Cubical.Data.Nat.Properties --equality in Nat
--open import Cubical.Data.Maybe
open import Cubical.Data.Bool renaming (true to 𝟙  ; false to 𝟘 ; Bool to 𝟚)
--open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra.Base
--open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to ⊥-elim)

private 
  variable 
   ℓ ℓ' : Level

enumeration : Type ℓ → Type _
enumeration A = Σ (ℕ → (Unit ⊎ A)) isSurjection
-- Note that Unit ⊎ A ≡ Maybe A by Maybe≡SumUnit 

enumℕ : enumeration ℕ 
enumℕ = eN , esurj where 
  eN : ℕ → Unit ⊎ ℕ 
  eN zero = inl tt
  eN (suc n) = inr n 
  esec : (x : Unit ⊎ ℕ ) → Σ ℕ (λ n → eN n ≡ x)
  esec (inl tt) = zero , refl
  esec (inr n) = suc n , refl 
  esurj : (x : Unit ⊎ ℕ) → ∥ Σ ℕ (λ z → eN z ≡ x) ∥₁ 
  esurj x = ∣ esec x ∣₁ 

mapMaybe : {A : Type ℓ } → {B : Type ℓ'} → (f : A → B)  → Unit ⊎ A → Unit ⊎ B
mapMaybe f (inl tt) = inl tt
mapMaybe f (inr x) = inr (f x) 

enumeration-Iso : {A : Type ℓ} → { B : Type ℓ' } → (Iso A B ) → enumeration A → enumeration B 
enumeration-Iso {ℓ} {ℓ'} {A} {B} isom (eA , is-surj-eA) = surj  where
  isom' : Iso (Unit ⊎ A) (Unit ⊎ B)
  isom' = ⊎Iso idIso isom
  isom'-surj : isSurjection (Iso.fun(isom'))
  isom'-surj = isEquiv→isSurjection (isoToIsEquiv isom')
  surj : Σ ((x : ℕ) → Unit ⊎ B) (λ z → (x : Unit ⊎ B) → ∥ Σ ℕ (λ z₁ → z z₁ ≡ x) ∥₁) 
  surj = compSurjection (eA , is-surj-eA) (Iso.fun isom' , isom'-surj) 

counting : Type ℓ → Type ℓ
counting A =  Σ (ℕ → 𝟚 ) (\( f ) → Iso A (Σ ℕ (λ n → f n ≡ 𝟙) ))

fromCountingToEnumeration : {A : Type ℓ } → counting A → enumeration A
fromCountingToEnumeration ( f , isoAD ) = enumeration-Iso (invIso isoAD) enumerateD where 
  D : Type 
  D = (Σ ℕ ( λ n → f n ≡ 𝟙 ))
  
  boolhelper : (b : 𝟚) → Unit ⊎ ( b ≡ 𝟙 )
  boolhelper 𝟘 = inl tt
  boolhelper 𝟙 = inr refl 

  g : ℕ → Unit ⊎ D
  g n = mapMaybe (n ,_) (boolhelper (f n)) 

  boolhelperreturnsallPossibleProofs : (b : 𝟚 ) → (p : b ≡ 𝟙) → boolhelper b ≡ inr (p)
  boolhelperreturnsallPossibleProofs 𝟘 p = ⊥-elim (false≢true p)
  boolhelperreturnsallPossibleProofs 𝟙 p = cong inr (isSetBool _ _ _ _)

  gHitsD : (x : D) →  g (fst x) ≡  inr x
  gHitsD  (n , p) = cong (mapMaybe (n ,_)) (boolhelperreturnsallPossibleProofs (f n) p) 
  
  eD : ℕ → Unit ⊎ D
  eD zero = inl tt
  eD (suc n) = g n  
  eD-sec : Unit ⊎ D → ℕ 
  eD-sec (inl tt) = zero
  eD-sec (inr (n , p)) = suc n 
  sect-eD : section eD eD-sec
  sect-eD (inl tt) i =  inl tt 
  sect-eD (inr x) = gHitsD x  

  enumerateD : enumeration D
  enumerateD = eD , λ { b → ∣ eD-sec b , sect-eD b ∣₁ } 

isEnumerable : Type ℓ  → Type ℓ
isEnumerable A = ∥ enumeration A ∥₁

isCountable : Type ℓ → Type _
isCountable A = ∥ counting A ∥₁ 

countable→enumerable : {A : Type ℓ} → isCountable A → isEnumerable A
countable→enumerable  = truncMap fromCountingToEnumeration 
