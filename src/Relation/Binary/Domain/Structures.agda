------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for domain theory
------------------------------------------------------------------------

module Relation.Binary.Domain.Structures where

open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Core using (Rel)
open import Level using (Level; _⊔_; suc; Lift; lift; lower)
open import Function using (_∘_; id)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong)
open import Relation.Binary.Reasoning.PartialOrder
open import Relation.Binary.Structures
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.Morphism.Structures
open import Relation.Binary.Morphism.Structures using (IsOrderHomomorphism)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Binary.Domain.Definitions

private variable
  o ℓ e o' ℓ' e' ℓ₂ : Level
  Ix A B : Set o

module _ {c ℓ₁ ℓ₂ : Level} (P : Poset c ℓ₁ ℓ₂) where
  open Poset P

  record IsDirectedFamily {Ix : Set c} (s : Ix → Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    no-eta-equality
    field
      elt : Ix
      SemiDirected : IsSemidirectedFamily P s

  record IsLub {Ix : Set c} (s : Ix → Carrier) (lub : Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
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

module _ {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {Q : Poset c ℓ₁ ℓ₂} where

  private
    module P = Poset P
    module Q = Poset Q

  record IsScottContinuous (f : P.Carrier → Q.Carrier) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      PreserveLub : ∀ {Ix : Set c} {s : Ix → P.Carrier}
        → (dir : IsDirectedFamily P s)
        → (lub : P.Carrier)
        → IsLub P s lub
        → IsLub Q (f ∘ s) (f lub)
      PreserveEquality : ∀ {x y} → x P.≈ y → f x Q.≈ f y
