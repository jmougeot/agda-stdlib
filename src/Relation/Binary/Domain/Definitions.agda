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

  record IsDCPO : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      HasDirectedLub : ∀ {Ix : Set c} {s : Ix → Carrier}
        → IsDirectedFamily s
        → ∃[ lub ] ((∀ i → s i ≤ lub) × ∀ y → (∀ i → s i ≤ y) → lub ≤ y)

record DCPO (c ℓ₁ ℓ₂ : Level) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    poset    : Poset c ℓ₁ ℓ₂
    DcpoStr  : IsDCPO poset

module _ {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {Q : Poset c ℓ₁ ℓ₂} where
  
  private
    module P = Poset P
    module Q = Poset Q
  
  record IsScottContinuous (f : P.Carrier → Q.Carrier) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      PreserveLub : ∀ {Ix : Set c} {s : Ix → P.Carrier}
        → (dir-s : IsDirectedFamily P s)
        → ∀ lub → ((∀ i → s i P.≤ lub) × ∀ y → (∀ i → s i P.≤ y) → lub P.≤ y)
        → ((∀ i → f (s i) Q.≤ f lub) × ∀ y → (∀ i → f (s i) Q.≤ y) → f lub Q.≤ y)
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
      mono-proof x y x≤y = proj₁ fs-lub (lift true)
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

          s-lub : P.Carrier × ((∀ i → s i P.≤ y) × (∀ z → (∀ i → s i P.≤ z) → y P.≤ z))
          s-lub = y , (sx≤sfalse , λ z lt → lt (lift false))

          fs-lub = IsScottContinuous.PreserveLub scott
                    s-directed y (sx≤sfalse , λ z lt → lt (lift false))

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
    { PreserveLub = λ dir-s lub z →  IsScottContinuous.PreserveLub scottf 
    (monotone∘directed g monotoneg dir-s)  
    (g lub) ( IsScottContinuous.PreserveLub scottg dir-s lub z)
    ; PreserveEquality = λ {x} {y} z → IsScottContinuous.PreserveEquality scottf 
    (IsScottContinuous.PreserveEquality scottg z)
    }

-- Module for the DCPO record
module _ {c ℓ₁ ℓ₂} (D : DCPO c ℓ₁ ℓ₂) where
  open DCPO D public

  posetD : Poset c ℓ₁ ℓ₂
  posetD = poset

  open Poset posetD
  open import Relation.Binary.Reasoning.PartialOrder posetD public

  dcpoD : IsDCPO posetD
  dcpoD = DcpoStr

  ⋃ : ∀ {Ix : Set c} (s : Ix → Carrier) → (dir : IsDirectedFamily posetD s) → Carrier
  ⋃ s dir = proj₁ (IsDCPO.HasDirectedLub dcpoD dir)

  module ⋃ {Ix : Set c} (s : Ix → Carrier) (dir : IsDirectedFamily posetD s) where
    fam≤lub : ∀ ix → s ix ≤ ⋃ s dir
    fam≤lub ix = proj₁ (proj₂ (IsDCPO.HasDirectedLub dcpoD dir)) ix
    
    least : ∀ ub → (∀ ix → s ix ≤ ub) → ⋃ s dir ≤ ub
    least ub p = proj₂ (proj₂ (IsDCPO.HasDirectedLub dcpoD dir)) ub p

  ⋃-pointwise : ∀ {Ix} {s s' : Ix → Carrier}
    → {fam : IsDirectedFamily posetD s} {fam' : IsDirectedFamily posetD s'}
    → (∀ ix → s ix ≤ s' ix)
    → ⋃ s fam ≤ ⋃ s' fam'
  ⋃-pointwise {s = s} {s'} {fam} {fam'} p = ⋃.least s fam (⋃ s' fam') λ ix →
    trans (p ix) (⋃.fam≤lub s' fam' ix)

module Scott {c} {ℓ₁} {ℓ₂} {D E : DCPO c ℓ₁ ℓ₂}
             (f : Poset.Carrier (DCPO.poset D) → Poset.Carrier (DCPO.poset E))
             (mono : IsMonotone (DCPO.poset D) (DCPO.poset E) f) where``

  private
    module D = DCPO D
    module E = DCPO E

  pres-directed-lub : ∀ {Ix} (s : Ix → Carrier) → is-directed-family D.poset s
      → ∀ x → is-lub (D .fst) s x → is-lub (E .fst) (apply f ⊙ s) (f · x)

