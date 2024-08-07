{-# OPTIONS --cubical --postfix-projections #-}
open import Cubical.Foundations.Prelude hiding (_∧_;_∨_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection 
open import Cubical.HITs.PropositionalTruncation renaming (map to truncMap)
--open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_∧_;_∨_)
--open import Cubical.Data.Nat.Properties --equality in Nat
--open import Cubical.Data.Maybe
--open import Cubical.Data.Bool renaming (true to 𝟙  ; false to 𝟘 ; Bool to 𝟚)
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra.Base
--open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
-- 
open import Enumerable
--open import Algebra.Lattice.Structures
open import Cubical.Algebra.Algebra.Base
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.AbGroup.Base

open import Cubical.Foundations.Structure


open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Ring.Properties

private 
  variable 
   ℓ ℓ' : Level

record IsBooleanRing {B : Type ℓ}
              (𝟘 𝟙 : B) (_+_ _·_ : B → B → B) (-_ : B → B) : Type ℓ where

  field
    isCommRing   : IsCommRing 𝟘 𝟙 _+_ _·_ -_ 
    ·IsIdempotent : (x : B) → x · x ≡ x

  open IsCommRing isCommRing public

record BooleanStr (A : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    𝟘          : A
    𝟙          : A
    _+_        : A → A → A
    _·_        : A → A → A
    -_         : A → A
    isBooleanRing : IsBooleanRing 𝟘 𝟙 _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsBooleanRing isBooleanRing public

BooleanRing : ∀ ℓ → Type (ℓ-suc ℓ)
BooleanRing ℓ = TypeWithStr ℓ BooleanStr

BooleanStrToCommRingStr : { A : Type ℓ } →  BooleanStr A  → CommRingStr A
BooleanStrToCommRingStr x .CommRingStr.0r = BooleanStr.𝟘 x
BooleanStrToCommRingStr x .CommRingStr.1r = BooleanStr.𝟙 x
BooleanStrToCommRingStr x .CommRingStr._+_ = BooleanStr._+_ x
BooleanStrToCommRingStr x .CommRingStr._·_ = BooleanStr._·_ x
BooleanStrToCommRingStr x .CommRingStr.-_  = BooleanStr.- x
BooleanStrToCommRingStr x .CommRingStr.isCommRing = IsBooleanRing.isCommRing (BooleanStr.isBooleanRing x) 

BooleanRingToCommRing : BooleanRing ℓ → CommRing ℓ
BooleanRingToCommRing (carrier , structure ) = carrier , BooleanStrToCommRingStr structure 

module BooleanAlgebraStr (A : BooleanRing ℓ)  where 
  open BooleanStr (A . snd)
  _∨_ : ⟨ A ⟩ → ⟨ A ⟩ → ⟨ A ⟩ 
  a ∨ b = (a + b) + (a · b) 
  _∧_ : ⟨ A ⟩ → ⟨ A ⟩ → ⟨ A ⟩ 
  a ∧ b = (a · b) 
  ¬_ : ⟨ A ⟩ → ⟨ A ⟩ 
  ¬ a = 𝟙 + a

  variable x y z : ⟨ A ⟩ 

  ∧IsIdempotent : x ∧ x ≡ x
  ∧IsIdempotent = ·IsIdempotent _ 

  ∧Assoc : (x ∧ ( y ∧ z ) ≡ ( x ∧ y ) ∧ z )
  ∧Assoc = ·Assoc _ _ _ 

  ∨Com : (x ∨ y ) ≡ (y ∨ x)
  ∨Com  = solve! (BooleanRingToCommRing A)

  ∧Com :  (x ∧ y) ≡ (y ∧ x)
  ∧Com = ·Comm _ _ 
  
  x≡-x : x + x ≡ 𝟘
  x≡-x {x = x} =  RingTheory.+Idempotency→0 (CommRing→Ring (BooleanRingToCommRing A)) (x + x) 2x≡4x
    where 
      2x≡4x : x + x ≡ (x + x) + (x + x)
      2x≡4x =  
        (x + x)
          ≡⟨ sym (·IsIdempotent (x + x)) ⟩
        ((x + x) · (x + x))
          ≡⟨ solve! (BooleanRingToCommRing A) ⟩
        ((x · x) + (x · x)) + ((x · x) + (x · x))
          ≡⟨ cong₂ _+_ (cong₂ _+_ (·IsIdempotent x) (·IsIdempotent x)) (cong₂ _+_ (·IsIdempotent x) (·IsIdempotent x)) ⟩
        (x + x) + (x + x) ∎

  distrA : ( x ∧ ( y ∨ z)) ≡ (x ∧ y) ∨ (x ∧ z)
  distrA {x = x} {y = y} { z = z} = 
    (x · ((y + z) + (y · z))) 
      ≡⟨ solve! (BooleanRingToCommRing A) ⟩
    ((x · y) + (x · z)) + ((  x  ) · (y · z))
      ≡⟨ cong (λ a → ((x · y) + (x · z)) + (a · (y · z))) (sym (·IsIdempotent x)) ⟩
    ((x · y) + (x · z)) + ((x · x) · (y · z))
      ≡⟨  solve! (BooleanRingToCommRing A) ⟩
    (((x · y) + (x · z)) + ((x · y) · (x · z))) ∎

  distrB : ( x ∨ ( y ∧ z)) ≡ (x ∨ y) ∧ (x ∨ z)
  distrB {x = x} {y = y} { z = z} = 
    ((x + (y · z)) + (x · (y · z))) 
      ≡⟨ solve! (BooleanRingToCommRing A) ⟩ 
    (((((x + 𝟘) + 𝟘) + (y · z)) + 𝟘) + ((x · y) · z))
      ≡⟨ cong (λ a → ((((a + 𝟘) + 𝟘) + (y · z)) + 𝟘) + ((a · y) · z)) (sym (·IsIdempotent x)) ⟩ 
    (((((x · x) + 𝟘  + 𝟘 ) + (y · z)) + 𝟘) + (((x · x) · y) · z))
      ≡⟨ cong (λ a → (((((x · x) + 𝟘) + 𝟘) + (y · z)) + a) + (((x · x) · y) · z)) (sym (x≡-x {x = (x · y) · z})) ⟩ 
    ((((((x · x) + 𝟘) + 𝟘) + (y · z)) + (((x · y) · z) + ((x · y) · z))) + (((x · x) · y) · z)) 
      ≡⟨ (cong₂ (λ a b → (((((x · x) + a) + b) + (y · z)) + (((x · y) · z) + ((x · y) · z))) + (((x · x) · y) · z))) (xa-xxa≡0 z) (xa-xxa≡0 y) ⟩ 
    ((((((x · x) + ((x · z) + ((x · x) · z))) + ((x · y) + ((x · x) · y))) + (y · z)) + (((x · y) · z) + ((x · y) · z))) + (((x · x) · y) · z)) 
      ≡⟨ solve! (BooleanRingToCommRing A) ⟩ 
    (((x + y) + (x · y)) · ((x + z) + (x · z))) ∎ where
      xa≡xxa : (a : ⟨ A ⟩) → x · a ≡ (x · x ) · a
      xa≡xxa a = cong (λ y → y · a) (sym (·IsIdempotent x)) 
      xa-xxa≡0 : (a : ⟨ A ⟩) → 𝟘 ≡ ((x · a) + ((x · x) · a)) 
      xa-xxa≡0 a =  
       𝟘
         ≡⟨ sym x≡-x ⟩ 
       ((x · a) + (x · a))
         ≡⟨ cong (λ y → (x · a) + (y · a)) (sym (·IsIdempotent x)) ⟩ 
       ((x · a) + ((x · x) · a)) ∎

  0∨IdR : x ∨ 𝟘 ≡ x
  0∨IdR = solve! (BooleanRingToCommRing A)

  0∨IdL : 𝟘 ∨ x ≡ x
  0∨IdL = solve! (BooleanRingToCommRing A)

  0∧RightAnnihilates : x ∧ 𝟘 ≡ 𝟘
  0∧RightAnnihilates = RingTheory.0RightAnnihilates (CommRing→Ring (BooleanRingToCommRing A)) _

  0∧LeftAnnihilates : 𝟘 ∧ x ≡ 𝟘
  0∧LeftAnnihilates = RingTheory.0LeftAnnihilates (CommRing→Ring (BooleanRingToCommRing A)) _ 

  1∨RightAbsorbs : x ∨ 𝟙 ≡ 𝟙 
  1∨RightAbsorbs {x = x} = 
    ((x + 𝟙) + (x · 𝟙)) 
      ≡⟨ solve! (BooleanRingToCommRing A) ⟩ 
    (𝟙 + (x + x))
      ≡⟨ cong (λ y → 𝟙 + y) x≡-x ⟩ 
    (𝟙 + 𝟘)
      ≡⟨ +IdR 𝟙 ⟩ 
    𝟙 ∎
  
  1∨LeftAbsorbs : 𝟙 ∨ x ≡ 𝟙 
  1∨LeftAbsorbs {x = x} = ∨Com ∙ 1∨RightAbsorbs

  1∧IdR : x ∧ 𝟙 ≡ x
  1∧IdR = ·IdR _  

  1∧IdL : 𝟙 ∧ x ≡ x
  1∧IdL = ·IdL _  

  absorpA : x ∧ (x ∨ y )  ≡ x
  absorpA {x = x} {y = y} = 
    (x · ((x + y) + (x · y))) 
      ≡⟨ solve! (BooleanRingToCommRing A) ⟩ 
    ((x · x) + ((x · y) + ((x · x) · y))) 
      ≡⟨ cong (λ z → z + ((x · y) + (z · y))) (·IsIdempotent x) ⟩ 
    (x + ((x · y) + (x · y))) 
      ≡⟨ cong (_+_ x) x≡-x ⟩ 
    (x + 𝟘) 
      ≡⟨ +IdR x ⟩ 
    x ∎ 

  absorpB : x ∨ (x ∧ y )  ≡ x
  absorpB {x = x} { y = y}  = 
    ((x + (x · y)) + (x · (x · y))) 
      ≡⟨ solve! (BooleanRingToCommRing A)  ⟩ 
    (x + ((x · y) + (x · x) · y)) 
      ≡⟨ cong (λ z → x + ((x · y) + (z · y))) (·IsIdempotent x) ⟩ 
    (x + ((x · y) + (x · y))) 
      ≡⟨ cong (_+_ x) x≡-x ⟩ 
    (x + 𝟘) 
      ≡⟨ +IdR x ⟩ 
    x ∎ 

  assoc∨ : (x ∨ ( y ∨ z ) ≡ ( x ∨ y ) ∨ z )
  assoc∨ =  solve! (BooleanRingToCommRing A)  

  ∨idem   : x ∨ x ≡ x
  ∨idem { x = x } = 
    (x + x) + (x · x)
      ≡⟨ cong (λ y → y + (x · x)) x≡-x ⟩ 
    𝟘  + (x · x) 
      ≡⟨ +IdL (x · x) ⟩ 
    (x · x) 
      ≡⟨ ·IsIdempotent x ⟩ 
    x ∎ 

  ∧idem : x ∧ x ≡ x
  ∧idem = ·IsIdempotent _ 

  ¬Cancels∧Right : (x ∧ (¬ x)) ≡ 𝟘
  ¬Cancels∧Right {x = x} = 
    (x · (𝟙 + x)) 
      ≡⟨ solve! (BooleanRingToCommRing A) ⟩ 
    (x + (x · x)) 
      ≡⟨ cong (λ y → x + y) (·IsIdempotent x) ⟩ 
    (x + x)
      ≡⟨ x≡-x ⟩ 
    𝟘 ∎ 
  
  ¬Cancels∧Left : ((¬ x) ∧ x) ≡ 𝟘
  ¬Cancels∧Left = ∧Com ∙ ¬Cancels∧Right

  ¬Completes∨Right : (x ∨ (¬ x)) ≡ 𝟙
  ¬Completes∨Right {x = x} = 
    ((x + (¬ x)) + (x ∧ (¬ x))) 
      ≡⟨ cong (λ z → (x + (¬ x)) + z) ¬Cancels∧Right ⟩ 
    (x + (¬ x) + 𝟘)
      ≡⟨ solve! (BooleanRingToCommRing A) ⟩ 
    (x ∨ 𝟙)
      ≡⟨ 1∨RightAbsorbs ⟩ 
    𝟙 ∎
  
  ¬Completes∨Left : ((¬ x) ∨ x) ≡ 𝟙
  ¬Completes∨Left = ∨Com ∙ ¬Completes∨Right 

  ¬¬ : ¬ ¬ x ≡ x
  ¬¬ {x = x} = 
    (𝟙 + (𝟙 + x)) 
      ≡⟨ +Assoc 𝟙 𝟙 x ⟩ 
    ((𝟙 + 𝟙) + x) 
      ≡⟨ cong (λ y → y + x) ( x≡-x {x = 𝟙}) ⟩ 
    (𝟘 + x) 
      ≡⟨ +IdL x ⟩ 
    x ∎ 

  ¬0 : ¬ 𝟘 ≡ 𝟙
  ¬0 = +IdR 𝟙

  ¬1 : ¬ 𝟙 ≡ 𝟘
  ¬1 = x≡-x {x = 𝟙}


data freeBA (G : Type ℓ) : Type ℓ where
  generator : G → freeBA G
  _∧_ : freeBA G → freeBA G → freeBA G
  _∨_ : freeBA G → freeBA G → freeBA G
  ¬_  : freeBA G → freeBA G
  𝟙 : freeBA G
  𝟘 : freeBA G
  assoc∨ : {x y z : freeBA G} →  (x ∨ ( y ∨ z ) ≡ ( x ∨ y ) ∨ z )
  assoc∧ : {x y z : freeBA G} →  (x ∧ ( y ∧ z ) ≡ ( x ∧ y ) ∧ z )
  com∨ : {x y : freeBA G} →  (x ∨  y ) ≡ (y ∨ x)
  com∧ : {x y : freeBA G} →  (x ∧  y ) ≡ (y ∧ x)
  distrA : {x y z : freeBA G} → ( x ∧ ( y ∨ z)) ≡ (x ∧ y) ∨ (x ∧ z)
  distrB : {x y z : freeBA G} → ( x ∨ ( y ∧ z)) ≡ (x ∨ y) ∧ (x ∨ z)
  0∨ : {x : freeBA G} → x ∨ 𝟘 ≡ x
  0∧ : {x : freeBA G} → x ∧ 𝟘 ≡ 𝟘
  1∨ : {x : freeBA G} → x ∨ 𝟙 ≡ 𝟙 
  1∧ : {x : freeBA G} → x ∧ 𝟙 ≡ x
  ∨idem   : {x : freeBA G} → x ∧ x ≡ x
  ∧idem   : {x : freeBA G} → x ∧ x ≡ x
  absorpA : {x y : freeBA G} →  x ∧ (x ∨ y )  ≡ x
  absorpB : {x y : freeBA G} →  x ∨ (x ∧ y )  ≡ x
  ¬∧ : {x : freeBA G} → (x ∧ (¬ x)) ≡ 𝟘
  ¬∨ : {x : freeBA G} → (x ∨ (¬ x)) ≡ 𝟙
  ¬¬ : {x : freeBA G} → ¬ ¬ x ≡ x
  ¬0 : ¬ 𝟘 ≡ 𝟙
  ¬1 : ¬ 𝟙 ≡ 𝟘

_+_ : {G : Type ℓ} → (freeBA G) → (freeBA G ) → (freeBA G) 
b + c = (b ∧ (¬ c)) ∨ ( (¬ b) ∧ c)

_·_ : {G : Type ℓ} → (freeBA G) → (freeBA G ) → (freeBA G) 
_·_ = _∧_

-_ : {G : Type ℓ} → (freeBA G) → (freeBA G ) 
-_ = \x → x




--freeBAisBooleanRing : {G : Type ℓ} → 


--freeBAareRing : {G : Type ℓ} → IsRing {ℓ} {freeBA G} 𝟘 𝟙 _+_ _∧_ (λ x → x)
--freeBAareRing = isring isAbGroup {! !} {! !} {! !}  where
--  isAbGroup : IsAbGroup 𝟘 _+_ (λ z → z) 
--  isAbGroup = {! !} 
----record IsRing {R : Type ℓ}
----              (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where
--
----  isRing = isring (IsLeftModule.+IsAbGroup +IsLeftModule) ·IsMonoid ·DistR+ ·DistL+



--freeBAareBA : {G : Type ℓ} →  IsBooleanAlgebra {_} {_} {freeBA G} (λ _ _ → freeBA G) _∨_ _∧_ ¬_ 𝟙 𝟘 -- I'm not sure what the first explicit argument is supposed to be


