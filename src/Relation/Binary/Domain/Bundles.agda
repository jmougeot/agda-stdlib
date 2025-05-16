------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for domain theory
------------------------------------------------------------------------

module Relation.Binary.Domain.Bundles where

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

open import Relation.Binary.Domain.Structures
open import Relation.Binary.Domain.Definitions

private variable
  o ℓ e o' ℓ' e' ℓ₂ : Level
  Ix A B : Set o
module _ {c ℓ₁ ℓ₂ : Level} (P : Poset c ℓ₁ ℓ₂) where
  open Poset P

  record Lub {Ix : Set c} (s : Ix → Carrier)  : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    constructor mkLub
    field
      lub : Carrier
      is-upperbound : ∀ i → s i ≤ lub
      is-least : ∀ y → (∀ i → s i ≤ y) → lub ≤ y

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

  -- record ScottContinuous : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  --   field
  --     Function : (f : P.Carrier → Q.Carrier)
  --     Scottfunciton : IsScottContinuous f

