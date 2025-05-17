------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for domain theory
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Domain.Bundles where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Domain.Structures
open import Relation.Binary.Domain.Definitions

private
  variable
    o ℓ e o' ℓ' e' ℓ₂ : Level
    Ix A B : Set o

------------------------------------------------------------------------
-- DCPOs
------------------------------------------------------------------------

record DCPO (c ℓ₁ ℓ₂ : Level) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    poset   : Poset c ℓ₁ ℓ₂
    DcpoStr : IsDCPO poset

  open Poset poset public
  open IsDCPO DcpoStr public

------------------------------------------------------------------------
-- Scott-continuous functions
------------------------------------------------------------------------

module _ {c ℓ₁ ℓ₂ : Level} (P : Poset c ℓ₁ ℓ₂) (Q : Poset c ℓ₁ ℓ₂) where
  private
    module P = Poset P
    module Q = Poset Q

  record ScottContinuous : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      f             : P.Carrier → Q.Carrier
      Scottfunction : IsScottContinuous {P = P} {Q = Q} f

------------------------------------------------------------------------
-- Lubs
------------------------------------------------------------------------

module _ {c ℓ₁ ℓ₂ : Level} (P : Poset c ℓ₁ ℓ₂) where
  open Poset P

  record Lub {Ix : Set c} (s : Ix → Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    constructor mkLub
    field
      lub           : Carrier
      is-upperbound : ∀ i → s i ≤ lub
      is-least      : ∀ y → (∀ i → s i ≤ y) → lub ≤ y