------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for domain theory
------------------------------------------------------------------------

module Relation.Binary.Domain.Definitions where

open import Data.Product using (∃-syntax; _×_; _,_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Morphism.Structures using (IsOrderHomomorphism)

private variable
  c o ℓ e o' ℓ' e' ℓ₂ : Level
  Ix A B : Set o
  P : Poset c ℓ e

module _ where
  IsMonotone : (P : Poset o ℓ e) → (Q : Poset o' ℓ' e') → (f : Poset.Carrier P → Poset.Carrier Q) → Set (o ⊔ ℓ ⊔ e ⊔ ℓ' ⊔ e')
  IsMonotone P Q f = IsOrderHomomorphism (Poset._≈_ P) (Poset._≈_ Q) (Poset._≤_ P) (Poset._≤_ Q) f

module _ {c ℓ₁ ℓ₂ : Level} (P : Poset c ℓ₁ ℓ₂) where
  open Poset P
  IsSemidirectedFamily : ∀ {Ix : Set c} → (s : Ix → Carrier) → Set _
  IsSemidirectedFamily s = ∀ i j → ∃[ k ] (s i ≤ s k × s j ≤ s k)

