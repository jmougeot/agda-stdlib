module Relation.Binary.Domain.Definitions where

open import Relation.Binary.Core
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
open import Relation.Binary.Lattice.Bundles
open import Relation.Binary.Lattice.Structures
open import Level using (Level; _⊔_; suc; Lift; lift)
open import Function using (_∘_; id)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Unary using (Pred)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Reasoning.PartialOrder
open import Data.Bool using (Bool; true; false)

private variable
  o ℓ ℓ' ℓ₂ : Level
  Ix A B : Set o


module _ {c ℓ₁ ℓ₂ : Level} (P : Poset c ℓ₁ ℓ₂) where
  open Poset P

  module PartialOrderReasoning = Relation.Binary.Reasoning.PartialOrder P

  is-semidirected-family : ∀ {Ix : Set c} → (f : Ix → Carrier) → Set _
  is-semidirected-family f = ∀ i j → ∃[ k ] (f i ≤ f k × f j ≤ f k)

  record is-directed-family {Ix : Set c} (f : Ix → Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    no-eta-equality
    field
      elt : Ix
      semidirected : is-semidirected-family f

  record is-dcpo : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      has-directed-lub : ∀ {Ix : Set c} {f : Ix → Carrier}
        → is-directed-family f
        → ∃[ lub ] ((∀ i → f i ≤ lub) × ∀ y → (∀ i → f i ≤ y) → lub ≤ y)

  record DCPO : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      poset    : Poset c ℓ₁ ℓ₂
      dcpo-str : is-dcpo

module _ {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {Q : Poset c ℓ₁ ℓ₂} where
  
  private
    module P = Poset P
    module Q = Poset Q

  record is-monotone (f : P.Carrier → Q.Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      monotone : ∀ {x y} → x P.≤ y → f x Q.≤ f y

  record is-scott-continuous (f : P.Carrier → Q.Carrier) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      monotone : is-monotone f
      preserve-lub : ∀ {Ix : Set c} {g : Ix → P.Carrier}
        → (df : is-directed-family P g)
        → (dlub : ∃[ lub ] ((∀ i → g i P.≤ lub) × ∀ y → (∀ i → g i P.≤ y) → lub P.≤ y))
        → ∃[ qlub ] ((∀ i → f (g i) Q.≤ qlub) × ∀ y → (∀ i → f (g i) Q.≤ y) → qlub Q.≤ y)

  dcpo+scott→monotone : (P-dcpo : is-dcpo P)
    → (f : P.Carrier → Q.Carrier)
    → (scott : is-scott-continuous f)
    → ∀ {x y} → x P.≤ y → f x Q.≤ f y

  dcpo+scott→monotone P-dcpo f scott {x} {y} p =
    Q.trans (ub-proof (lift true)) (least-proof (f y) upper-bound-proof)
    where
      s : Lift c Bool → P.Carrier
      s (lift true)  = x
      s (lift false) = y

      s-directed : is-directed-family P s
      s-directed .is-directed-family.elt = lift true
      s-directed .is-directed-family.semidirected i j =
        lift false , p' i , p' j
        where
          p' : (i : Lift c Bool) → s i P.≤ s (lift false)
          p' (lift true)  = p
          p' (lift false) = P.refl

      s-lub = is-dcpo.has-directed-lub P-dcpo s-directed
      q-lub = is-scott-continuous.preserve-lub scott s-directed s-lub

      ub-proof : ∀ i → f (s i) Q.≤ proj₁ q-lub
      ub-proof = proj₁ (proj₂ q-lub)

      least-proof : ∀ y → (∀ i → f (s i) Q.≤ y) → proj₁ q-lub Q.≤ y
      least-proof = proj₂ (proj₂ q-lub)
      
      upper-bound-proof : ∀ i → f (s i) Q.≤ f y
      upper-bound-proof (lift true) = is-monotone.monotone (is-scott-continuous.monotone scott) p
      upper-bound-proof (lift false) = Q.refl

  monotone∘directed : ∀ {Ix : Set c} → {s : Ix → P.Carrier}
    → (f : P.Carrier → Q.Carrier)
    → (mon : is-monotone f)
    → is-directed-family P s
    → is-directed-family Q (f ∘ s)
  monotone∘directed f mon dir .is-directed-family.elt = dir .is-directed-family.elt
  monotone∘directed f mon dir .is-directed-family.semidirected i j =
    let k , p = dir .is-directed-family.semidirected i j
    in k , mon .is-monotone.monotone (proj₁ p) , mon .is-monotone.monotone (proj₂ p)



{-module _ where
  open import Relation.Binary.Bundles using (Poset)
  open import Function using (_∘_)

  private
    module P {o ℓ₁ ℓ₂} (P : Poset o ℓ₁ ℓ₂) = Poset P
    module Q {o ℓ₁ ℓ₂} (Q : Poset o ℓ₁ ℓ₂) = Poset Q
    module R {o ℓ₁ ℓ₂} (R : Poset o ℓ₁ ℓ₂) = Poset R

  scott-id : ∀ {o ℓ₁ ℓ₂} {P : Poset o ℓ₁ ℓ₂}
    → is-scott-continuous (id {A = Poset.Carrier P})
  scott-id = record
    { monotone = record { monotone = λ {x} {y} z → x }
    ; preserve-lub = λ {Ix} {g} df dlub → dlub
    }
  
  scott-∘
    : ∀ {o ℓ₁ ℓ₂} {P Q R : Poset o ℓ₁ ℓ₂}
    → (f : Q.Carrier Q → R.Carrier R) (g : P.Carrier P → Q.Carrier Q)
    → is-scott-continuous f → is-scott-continuous g
    → is-scott-continuous (f ∘ g)
  scott-∘ {P = P} {Q} {R} f g f-scott g-scott s dir x lub =
    f-scott (g ∘ s)
      (monotone∘directed g (is-scott-continuous.monotone g-scott) dir)
      (g x)
      (g-scott s dir x lub)-}
