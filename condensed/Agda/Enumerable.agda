{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude hiding (_∧_;_∨_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection 
open import Cubical.HITs.PropositionalTruncation renaming (rec to untruncate)
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool renaming (true to 𝟙  ; false to 𝟘 ; Bool to 𝟚)
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (elim to ⊥-elim)

private 
  variable 
   ℓ ℓ' : Level

--data 𝟚 : Type where 
--  𝟘 : 𝟚 
--  𝟙 : 𝟚 

all-elements-of-𝟚 : (n : 𝟚 ) → ((n ≡ 𝟘) ⊎ (n ≡ 𝟙 ) )
all-elements-of-𝟚 𝟘 = inl refl
all-elements-of-𝟚 𝟙 = inr refl 


isSet2 : isSet 𝟚 
isSet2 = isSetBool

enumeration : Type ℓ → Type _
enumeration A = Σ (ℕ → (Unit ⊎ A)) isSurjection

enumeration-Iso : {A B : Type} → (Iso A B ) → enumeration A → enumeration B 
enumeration-Iso {A} {B} isom (eA , is-surj-eA) = surj  where
  isom' : Iso (Unit ⊎ A) (Unit ⊎ B)
  isom' = iso f g fg=1 gf=1 where 
    f : Unit ⊎ A → Unit ⊎ B
    f (inl tt) = inl tt
    f (inr x) = inr (Iso.fun isom x) 
    g : Unit ⊎ B → Unit ⊎ A
    g (inl tt) = inl tt
    g (inr x) = inr (Iso.inv isom x) 
    fg=1 : (x : Unit ⊎ B) → f (g x) ≡ x 
    fg=1 (inl tt) i =  inl tt
    fg=1 (inr x) i = inr (Iso.rightInv isom x i)
    gf=1 : (x : Unit ⊎ A) → g (f x) ≡ x 
    gf=1 (inl x) i =  inl x 
    gf=1 (inr x) i = inr (Iso.leftInv isom x i) 
  isom'-surj : isSurjection (Iso.fun(isom'))
  isom'-surj = isEquiv→isSurjection (isoToIsEquiv isom')
  surj : Σ ((x : ℕ) → Unit ⊎ B) (λ z → (x : Unit ⊎ B) → ∥ Σ ℕ (λ z₁ → z z₁ ≡ x) ∥₁) 
  surj = compSurjection (eA , is-surj-eA) (Iso.fun isom' , isom'-surj) 

counting : Type ℓ → Type _
counting A =  Σ (ℕ → 𝟚 ) (\( f ) → Iso A (Σ ℕ (λ n → f n ≡ 𝟙) ))

fromCountingToEnumeration : {A : Type ℓ } → counting A → enumeration A
fromCountingToEnumeration ( f , isoAD ) = {! !} where -- {!enumeration-Iso isoAD enumerateD !} where
  D : Type 
  D = (Σ ℕ ( λ n → f n ≡ 𝟙 ))
  helper : (g : ℕ → 𝟚 ) → (n : ℕ ) → ((g n ≡ 𝟘 ) ⊎ (g n ≡ 𝟙 )) → (Unit ⊎  Σ ℕ (\m → g m ≡ 𝟙 ))
  helper g n (inl gn=0) = inl tt
  helper g n (inr gn=1) = inr (n , gn=1)
  onlyonePossible : (b : 𝟚 ) → (p : b ≡ 𝟙 ) → (x : (b ≡ 𝟘 ) ⊎ (b ≡ 𝟙 )) → x ≡ inr p
  onlyonePossible 𝟘 p (_) = ⊥-elim (false≢true p) 
  onlyonePossible 𝟙 p (inl x) = ⊥-elim (true≢false x)
  onlyonePossible 𝟙 p (inr x) = cong inr (isSet2 𝟙 𝟙 x p) 
  helperNice : (g : ℕ → 𝟚 ) → (n : ℕ ) → (p : g n ≡ 𝟙 ) → (helper g n (all-elements-of-𝟚 (g n) )) ≡  inr ( n , p)
  helperNice g n p = {!subst !}-- (onlyonePossible (g n) p (all-elements-of-𝟚 (g n))) )!}
  eD : ℕ → Unit ⊎ D
  eD zero = inl tt
  eD (suc n) = helper f n (all-elements-of-𝟚 (f n)) 
  eD-sec : Unit ⊎ D → ℕ 
  eD-sec (inl tt) = zero
  eD-sec (inr (n , p)) = suc n 
  sect-eD : section eD eD-sec
  sect-eD (inl tt) i =  inl tt 
  sect-eD (inr (n , fn=1)) i = {!inr ? !} -- {!isSet-2 ?inr (n , fn=1) !}

--  enumerateD : enumeration D
--  enumerateD = (λ { zero → inl tt
--                  ; (suc x) → helper f x (all-elements-of-𝟚 (f x)) }) , 
--                  λ { (inl tt) → ∣ zero , (λ { i → inl tt }) ∣₁ ; (inr (n , fn=1)) → ∣ n , (λ { i → {! !} }) ∣₁ } 
--  enumerateD = (λ { zero → inl(tt) } ; {suc (n) → helper f n (all-elements-of-𝟚 (f n)) }) , λ { b → {! !} } 

--fromCountingToEnumeration {ℓ} {A} (f , isoAandSigmaf) = surjA where  
--  helper : (g : ℕ → 𝟚 ) → (n : ℕ ) → ((g n ≡ 𝟘 ) ⊎ (g n ≡ 𝟙 )) → (Unit ⊎  Σ ℕ (\m → g m ≡ 𝟙 ))
--  helper g n (inl gn=0) = inl tt
--  helper g n (inr gn=1) = inr (n , gn=1)
--  surjA : {! !}
--  surjA = {! !} 
----
----
----
----  transformToA : (Unit ⊎  Σ ℕ (\m → f m ≡ 𝟙 )) → (Unit ⊎ A)
----  transformToA (inl tt) = inl tt
----  transformToA (inr x) = inr (Iso.inv isoAandSigmaf x) 
----  mapToA : (n : ℕ ) → ((f n ≡ 𝟘 ) ⊎ (f n ≡ 𝟙 )) → (Unit ⊎  A)
----  mapToA n equalityweneed = transformToA (helper f n equalityweneed)
----  enum' : ℕ → Unit ⊎ A 
----  enum' n = mapToA n (all-elements-of-𝟚 (f n)) 
----  enum : ℕ → Unit ⊎ A 
----  enum zero = inl tt
----  enum (suc n) = enum' n 
----  surjectivity-enum : (x : Unit ⊎ A) → ∥ Σ ℕ (λ z → enum z  ≡ x) ∥₁ 
----  surjectivity-enum = {! !} 
----  surjectivity-enum : (x : Unit ⊎ A) → ∥ Σ ℕ (λ z → enum z  ≡ x) ∥₁ 
----  surjectivity-enum (inl tt) = ∣ zero , (λ { i → inl tt }) ∣₁
----  surjectivity-enum (inr a) = {! Iso.inv isoAandSigmaf !} 
--


isEnumerable : Type ℓ  → Type ℓ
isEnumerable A = ∥ enumeration A ∥₁

is-Enum-N : isEnumerable ℕ 
is-Enum-N = ∣ (λ { zero → inl tt
         ; (suc n) → inr n }) , (λ { (inl tt) → ∣ 0 , (λ { i → inl tt }) ∣₁ ; (inr n) → ∣ suc n , (λ { i → inr n }) ∣₁ }) ∣₁

isCountable : Type ℓ → Type _
isCountable A = ∥ counting A ∥₁ 

