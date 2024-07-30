{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude --hiding (_∧_;_∨_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection 
open import Cubical.HITs.PropositionalTruncation renaming (rec to untruncate)
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Properties --equality in Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Bool renaming (true to 𝟙  ; false to 𝟘 ; Bool to 𝟚)
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (elim to ⊥-elim)



private 
  variable 
   ℓ ℓ' : Level

_⋅_ : {A : Type ℓ } → {x y z : A } → x ≡ y → y ≡ z → x ≡ z
_⋅_ = _∙_ 




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


enumeration' : Type ℓ → Type _
enumeration' A = Σ (ℕ → (Maybe A)) isSurjection

--Σ-eq : {A : Type ℓ } → (P : A → Type ℓ') → ( x y : Σ A P ) → ( p : fst x ≡ fst y ) → subst P p (snd x) ≡ snd y  → x ≡ y
--Σ-eq {A} P (a₁ , x₁) (a₂ , y₂) p1 p2 i = {!Σ=Prop!} 
---- (q : transp ? (snd x) ≡ snd y )

subtypeUniqueOnFirstElt : {A : Type ℓ} → (P : A → Type ℓ') → ( (a : A) → isProp (P a)) → ( x y : Σ A P) → (fst x  ≡ fst y) → x ≡ y
subtypeUniqueOnFirstElt {A} P isprop (x1 , x2) (y1 , y2) p = Σ≡Prop isprop p 



enumeration-Iso : {A : Type ℓ} → { B : Type ℓ' } → (Iso A B ) → enumeration A → enumeration B 
enumeration-Iso {ℓ} {ℓ'} {A} {B} isom (eA , is-surj-eA) = surj  where
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

counting : Type ℓ → Type ℓ
counting A =  Σ (ℕ → 𝟚 ) (\( f ) → Iso A (Σ ℕ (λ n → f n ≡ 𝟙) ))

fromCountingToEnumeration : {A : Type ℓ } → counting A → enumeration A
fromCountingToEnumeration ( f , isoAD ) = enumeration-Iso (invIso isoAD) enumerateD where 
  D : Type 
  D = (Σ ℕ ( λ n → f n ≡ 𝟙 ))
--  DhasUniqueFirstElt : ( x y : D) → fst x ≡ fst y → x ≡ y
--  DhasUniqueFirstElt (n , a) (m , b) p = Σ≡Prop (λ (n : ℕ) → isSetBool (f n) 𝟙) p 
--
--  helper : (g : ℕ → 𝟚 ) → (n : ℕ ) → ((g n ≡ 𝟘 ) ⊎ (g n ≡ 𝟙 )) → (Unit ⊎  Σ ℕ (\m → g m ≡ 𝟙 ))
--  helper g n (inl gn=0) = inl tt
--  helper g n (inr gn=1) = inr (n , gn=1)
  boolhelper : (b : 𝟚) → Unit ⊎ ( Σ 𝟚 ( λ b' → b ≡ b'  ))
  boolhelper 𝟘 = inl tt
  boolhelper 𝟙 = inr (𝟙 , refl) 
  
  helper' : (n : ℕ ) → (Unit ⊎ D)
  helper' n with boolhelper (f n) 
  ... | (inl tt ) = inl tt 
  ... | (inr ( 𝟘 , p) ) = inl tt -- this case shouldn't happen, maybe an ex-falso something ?
  ... | (inr (𝟙 , p ) ) = inr (n , p) 
--                | true  = inr ( n , ? )
--                | false = inl tt

--  if (f n) then inr (n , {!refl {_}  {_} {f n} !}) else inl tt -- little confused about way it says refl i1 
  
  boolhelperreturnsallproofs : (b : 𝟚 ) → ( p : b ≡ 𝟙) → boolhelper b ≡ (inr (𝟙 , p))
  boolhelperreturnsallproofs 𝟘 p = ⊥-elim (false≢true p)
  boolhelperreturnsallproofs 𝟙 p = cong inr (Σ≡Prop (isSetBool 𝟙) p) 

  helper-D-surjective : (n : ℕ ) → ( p : f n ≡ 𝟙 ) → (helper' n ≡ inr (n , p))
  helper-D-surjective n p = {! (boolhelperreturnsallproofs (f n)  p ) !} --again confused as to why but it works

---  onlyonePossible : (b : 𝟚 ) → (p : b ≡ 𝟙 ) → (x : (b ≡ 𝟘 ) ⊎ (b ≡ 𝟙 )) → x ≡ inr p
---  onlyonePossible 𝟘 p (_) = ⊥-elim (false≢true p) 
---  onlyonePossible 𝟙 p (inl x) = ⊥-elim (true≢false x)
---  onlyonePossible 𝟙 p (inr x) = cong inr (isSet2 𝟙 𝟙 x p) 
---  helperNice : (g : ℕ → 𝟚 ) → (n : ℕ ) → (p : g n ≡ 𝟙 ) → (helper g n (all-elements-of-𝟚 (g n) )) ≡  inr ( n , p)
---  helperNice g n p = {!    !} -- (onlyonePossible (g n) p (all-elements-of-𝟚 (g n))) )!}

  eD : ℕ → Unit ⊎ D
  eD zero = inl tt
  eD (suc n) = helper' n  
  eD-sec : Unit ⊎ D → ℕ 
  eD-sec (inl tt) = zero
  eD-sec (inr (n , p)) = suc n 
  sect-eD : section eD eD-sec
  sect-eD (inl tt) i =  inl tt 
  sect-eD (inr (n , fn=1)) = helper-D-surjective n fn=1 -- {!isSet-2 ?inr (n , fn=1) !}

  enumerateD : enumeration D
  enumerateD = eD , λ { b → ∣ eD-sec b , sect-eD b ∣₁ } 




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

