module Relation.Binary.Domain.Definitions where

open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Core using (Rel)
open import Level using (Level; _⊔_; suc; Lift; lift; lower)
open import Function using (_∘_; id)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Reasoning.PartialOrder
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.Morphism.Structures
open import Relation.Binary.Morphism.Structures using (IsOrderHomomorphism)
open import Data.Nat.Properties using (≤-trans)

private variable
  o ℓ e o' ℓ' e' ℓ₂ : Level
  Ix A B : Set o

module _ where 
  IsMonotone : (P : Poset o ℓ e) → (Q : Poset o' ℓ' e') → (f : Poset.Carrier P → Poset.Carrier Q) → Set (o ⊔ ℓ ⊔ e ⊔ ℓ' ⊔ e')
  IsMonotone P Q f = IsOrderHomomorphism (Poset._≈_ P) (Poset._≈_ Q) (Poset._≤_ P) (Poset._≤_ Q) f

module _ {c ℓ₁ ℓ₂ : Level} (P : Poset c ℓ₁ ℓ₂) where
  open Poset P

  IsSemidirectedFamily : ∀ {Ix : Set c} → (s : Ix → Carrier) → Set _
  IsSemidirectedFamily s = ∀ i j → ∃[ k ] (s i ≤ s k × s j ≤ s k)

  record IsDirectedFamily {Ix : Set c} (s : Ix → Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    no-eta-equality
    field
      elt : Ix
      SemiDirected : IsSemidirectedFamily s

  record IsLub {Ix : Set c} (s : Ix → Carrier) (lub : Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      is-upperbound : ∀ i → s i ≤ lub
      is-least : ∀ y → (∀ i → s i ≤ y) → lub ≤ y
  
  record Lub {Ix : Set c} (s : Ix → Carrier)  : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    constructor mkLub
    field
      lub : Carrier
      is-upperbound : ∀ i → s i ≤ lub
      is-least : ∀ y → (∀ i → s i ≤ y) → lub ≤ y

  record IsDCPO : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      ⋁ : ∀ {Ix : Set c} 
        → (s : Ix → Carrier)
        → IsDirectedFamily s
        → Carrier
      ⋁-isLub : ∀ {Ix : Set c} 
        → (s : Ix → Carrier)
        → (dir : IsDirectedFamily s)
        → IsLub s (⋁ s dir)

    module _ {Ix : Set c} {s : Ix → Carrier} {dir : IsDirectedFamily s} where
      open IsLub (⋁-isLub s dir)
        renaming (is-upperbound to ⋁-≤; is-least to ⋁-least)
        public
       

record DCPO (c ℓ₁ ℓ₂ : Level) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    poset    : Poset c ℓ₁ ℓ₂
    DcpoStr  : IsDCPO poset

  open Poset poset public
  open IsDCPO DcpoStr public

module _ {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {Q : Poset c ℓ₁ ℓ₂} where
  
  private
    module P = Poset P
    module Q = Poset Q
  
  record IsScottContinuous (f : P.Carrier → Q.Carrier) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      PreserveLub : ∀ {Ix : Set c} {s : Ix → P.Carrier}
        → (dir-s : IsDirectedFamily P s)
        → (lub : P.Carrier)
        → IsLub P s lub
        → IsLub Q (f ∘ s) (f lub)
      PreserveEquality : ∀ {x y} → x P.≈ y → f x Q.≈ f y

  dcpo+scott→monotone : (P-dcpo : IsDCPO P)
    → (f : P.Carrier → Q.Carrier)
    → (scott : IsScottContinuous f)
    → IsMonotone P Q f
  dcpo+scott→monotone P-dcpo f scott = record
    { cong = λ {x} {y} x≈y → IsScottContinuous.PreserveEquality scott x≈y
    ; mono = λ {x} {y} x≤y → mono-proof x y x≤y
    }
    where
      mono-proof : ∀ x y → x P.≤ y → f x Q.≤ f y
      mono-proof x y x≤y = IsLub.is-upperbound fs-lub (lift true)
        where
          s : Lift c Bool → P.Carrier 
          s (lift b) = if b then x else y

          sx≤sfalse : ∀ b → s b P.≤ s (lift false)
          sx≤sfalse (lift true) = x≤y
          sx≤sfalse (lift false) = P.refl

          s-directed : IsDirectedFamily P s
          s-directed = record 
            { elt = lift true 
            ; SemiDirected = λ i j → (lift false , sx≤sfalse i , sx≤sfalse j)
            }
          
          s-lub : IsLub P s y
          s-lub = record
            { is-upperbound = sx≤sfalse
            ; is-least = λ z proof → proof (lift false)
            }
          
          fs-lub : IsLub Q (f ∘ s) (f y)
          fs-lub = IsScottContinuous.PreserveLub scott s-directed y s-lub


  monotone∘directed : ∀ {Ix : Set c} {s : Ix → P.Carrier}
    → (f : P.Carrier → Q.Carrier)
    → IsMonotone P Q f
    → IsDirectedFamily P s
    → IsDirectedFamily Q (f ∘ s)
  monotone∘directed f ismonotone dir = record 
    { elt = IsDirectedFamily.elt dir
    ; SemiDirected = λ i j →
        let (k , s[i]≤s[k] , s[j]≤s[k]) = IsDirectedFamily.SemiDirected dir i j
        in k , IsOrderHomomorphism.mono ismonotone s[i]≤s[k] , IsOrderHomomorphism.mono ismonotone s[j]≤s[k]
    }

module _ where

  ScottId : ∀ {c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} → IsScottContinuous {P = P} {Q = P} id 
  ScottId = record
    { PreserveLub = λ dir-s lub z → z
    ; PreserveEquality = λ z → z }
  
  scott-∘ : ∀ {c ℓ₁ ℓ₂} {P Q R : Poset c ℓ₁ ℓ₂}
    → (f : Poset.Carrier R → Poset.Carrier Q) (g : Poset.Carrier P → Poset.Carrier R)
    → IsScottContinuous {P = R} {Q = Q} f → IsScottContinuous {P = P} {Q = R} g
    → IsMonotone R Q f → IsMonotone P R g
    → IsScottContinuous {P = P} {Q = Q} (f ∘ g)
  scott-∘ f g scottf scottg monotonef monotoneg = record 
    { PreserveLub = λ dir-s lub z → f.PreserveLub 
        (monotone∘directed g monotoneg dir-s)  
        (g lub) 
        (g.PreserveLub dir-s lub z)
    ; PreserveEquality = λ {x} {y} z → 
      f.PreserveEquality (g.PreserveEquality z)
    }
    where 
      module f = IsScottContinuous scottf
      module g = IsScottContinuous scottg

module _ {c ℓ₁ ℓ₂} (D : DCPO c ℓ₁ ℓ₂) (let module D = DCPO D) where
  open DCPO D

  open import Relation.Binary.Reasoning.PartialOrder poset public

  ⋃-pointwise : ∀ {Ix} {s s' : Ix → Carrier}
    → {fam : IsDirectedFamily poset s} {fam' : IsDirectedFamily poset s'}
    → (∀ ix → s ix ≤ s' ix)
    → ⋁ s fam ≤ ⋁ s' fam'
  ⋃-pointwise {s = s} {s'} {fam} {fam'} p = 
    ⋁-least (⋁ s' fam') λ i → trans (p i) (⋁-≤ i)

module Scott 
    {c ℓ₁ ℓ₂} 
    {D E : DCPO c ℓ₁ ℓ₂}
    (let module D = DCPO D)
    (let module E = DCPO E)
    (f : D.Carrier → E.Carrier)
    (mono : IsMonotone D.poset E.poset f) where

    res-directed-lub : ∀ {Ix} (s : Ix → D.Carrier)
      → IsDirectedFamily D.poset s
      → ∀ x → IsLub D.poset s x
      → IsLub E.poset (f ∘ s) (f x)
    res-directed-lub s dir x lub = {!   !}
      
    directed : ∀ {Ix} {s : Ix → D.Carrier} → IsDirectedFamily D.poset s → IsDirectedFamily E.poset (f ∘ s)
    directed = monotone∘directed f mono
    
    pres-⋃
      : ∀ {Ix} (s : Ix → D.Carrier) → (dir : IsDirectedFamily D.poset s)
      → f (D.⋁ s dir) ≡ E.⋁ (f ∘ s) (monotone∘directed f mono dir)
    pres-⋃ s dir = {!   !} 

module _ {c ℓ₁ ℓ₂} (D E : DCPO c ℓ₁ ℓ₂) where
  private
    module D = DCPO D
    module E = DCPO E

  to-scott : (f : D.Carrier → E.Carrier) → IsMonotone D.poset E.poset f  
    → (∀ {Ix} (s : Ix → D.Carrier) (dir : IsDirectedFamily D.poset s) →
    IsLub E.poset (f ∘ s) (f (D.⋁ s dir))) → IsScottContinuous {P = D.poset} {Q = E.poset} f 
  to-scott f monotone pres-⋃ = {!   !} 

  -- res-lub : ∀ {Ix} (s : Ix → D.Carrier) → (dir : is-directed-family D.poset s)
  --       → ∀ x → is-lub D.poset s x → is-lub E.poset (f ⊙ s) (f x)
  --     pres-lub s dir x x-lub .is-lub.fam≤lub i = ?  