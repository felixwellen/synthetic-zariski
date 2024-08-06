{- In this agda file, we consider two definitions of countability. 
-- One definition, which we call enumerable, says there exists a surjection ℕ → 1 + A. (This is used for example in Davorin Lesnik's PhD thesis). 
-- Another definition, which we call countable, says A is merely isomorphic to some decidable subtype of ℕ.
-}

{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection 
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Bool renaming (true to 𝟙  ; false to 𝟘 ; Bool to 𝟚)
open import Cubical.Data.Empty as ⊥ 

module Enumerable where

private 
  variable 
   ℓ ℓ' : Level

enumeration : Type ℓ → Type _
enumeration A = Σ (ℕ → (Unit ⊎ A)) isSurjection

shiftToSurjective : {A : Type ℓ} → (f : ℕ → Unit ⊎ A) → ( ( a : A) → ∥ Σ[ n ∈ ℕ ] f n ≡ inr (a) ∥₁  ) → enumeration A
shiftToSurjective {A = A} f fsurj = f' , f'surj where
  f' : ℕ → Unit ⊎ A
  f' zero = inl tt
  f' (suc n) = f n 
  f'surj : (x : Unit ⊎ A) → ∥ Σ ℕ (λ z → f' z ≡ x) ∥₁ 
  f'surj (inl tt) = ∣ zero , refl ∣₁
  f'surj (inr a) = PT.rec PT.isPropPropTrunc (λ { (n , fn≡a) → ∣ suc n , fn≡a ∣₁ }) (fsurj a) 

⊥-enum : enumeration ⊥ 
⊥-enum = shiftToSurjective (λ { n → inl tt }) λ { a → ⊥.rec a } 

ℕsurjectionToEnumeration : {A : Type ℓ} → (f : ℕ → A) → (isSurjection f) → enumeration A
ℕsurjectionToEnumeration f fsurj = shiftToSurjective ( inr ∘ f ) (λ  a → PT.rec isPropPropTrunc (λ { (n , fn≡a) → ∣ n , cong inr fn≡a ∣₁ }) (fsurj a) ) 

enumℕ : enumeration ℕ 
enumℕ = ℕsurjectionToEnumeration (λ n → n) λ { b → ∣ b , refl ∣₁ } 

liftUnit⊎ : {A : Type ℓ } → {B : Type ℓ'} → (f : A → B)  → Unit ⊎ A → Unit ⊎ B
liftUnit⊎ f (inl tt) = inl tt
liftUnit⊎ f (inr x) = inr (f x) 

enumeration-Iso : {A : Type ℓ} → { B : Type ℓ' } → (Iso A B ) → enumeration A → enumeration B 
enumeration-Iso {ℓ} {ℓ'} {A} {B} isom enumA = surj  where
  isom' : Iso (Unit ⊎ A) (Unit ⊎ B)
  isom' = ⊎Iso idIso isom
  isom'-surj : isSurjection (Iso.fun(isom'))
  isom'-surj = isEquiv→isSurjection (isoToIsEquiv isom')
  surj : Σ ((x : ℕ) → Unit ⊎ B) (λ z → (x : Unit ⊎ B) → ∥ Σ ℕ (λ z₁ → z z₁ ≡ x) ∥₁) 
  surj = compSurjection enumA (Iso.fun isom' , isom'-surj) 

-- A ``count" of a type is an explicit isomorphism with a decidable subset of ℕ 
count : Type ℓ → Type ℓ 
count A =  Σ[ f ∈ (ℕ → 𝟚) ]  Iso A (Σ[ n ∈ ℕ ]  f n ≡ 𝟙 )

fromCountToEnumeration : {A : Type ℓ } → count A → enumeration A
fromCountToEnumeration ( f , isoAD ) = enumeration-Iso (invIso isoAD) enumerateD where 
  D : Type 
  D = Σ[ n ∈ ℕ ] f n ≡ 𝟙 
  
  boolhelper : (b : 𝟚) → Unit ⊎ ( b ≡ 𝟙 )
  boolhelper 𝟘 = inl tt
  boolhelper 𝟙 = inr refl 

  boolhelperReturnsAllPossibleProofs : (b : 𝟚 ) → (p : b ≡ 𝟙) → boolhelper b ≡ inr (p)
  boolhelperReturnsAllPossibleProofs 𝟘 p = ⊥.rec (false≢true p)
  boolhelperReturnsAllPossibleProofs 𝟙 p = cong inr (isSetBool _ _ _ _)

  g : ℕ → Unit ⊎ D
  g n = liftUnit⊎ (n ,_) (boolhelper (f n)) 

  gHitsD : (x : D) →  g (fst x) ≡ inr x
  gHitsD  (n , fn≡1) = cong (liftUnit⊎ (n ,_)) (boolhelperReturnsAllPossibleProofs (f n) fn≡1) 
  
  enumerateD :  enumeration  D
  enumerateD = shiftToSurjective g (λ d → ∣ fst d , gHitsD d ∣₁)

isEnumerable : Type ℓ  → Type ℓ
isEnumerable A = ∥ enumeration A ∥₁

isCountable : Type ℓ → Type _
isCountable A = ∥ count A ∥₁ 

countable→enumerable : {A : Type ℓ} → isCountable A → isEnumerable A
countable→enumerable  = PT.map fromCountToEnumeration 
