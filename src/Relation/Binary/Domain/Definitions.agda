module Relation.Binary.Domain.Definitions where

open import Relation.Binary.Bundles using (Poset)
open import Level using (Level; _⊔_; suc; Lift; lift; lower)
open import Function using (_∘_; id)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Reasoning.PartialOrder
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.Morphism.Structures

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
  
  open IsOrderHomomorphism {_≈₁_ = P._≈_} {_≈₂_ = Q._≈_} {_≲₁_ = P._≤_} {_≲₂_ = Q._≤_}

  record is-scott-continuous (f : P.Carrier → Q.Carrier) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      preserve-lub : ∀ {Ix : Set c} {g : Ix → P.Carrier}
        → (df : is-directed-family P g)
        → (dlub : ∃[ lub ] ((∀ i → g i P.≤ lub) × ∀ y → (∀ i → g i P.≤ y) → lub P.≤ y))
        → ∃[ qlub ] ((∀ i → f (g i) Q.≤ qlub) × ∀ y → (∀ i → f (g i) Q.≤ y) → qlub Q.≤ y)

  dcpo+scott→monotone : (P-dcpo : is-dcpo P)
    → (f : P.Carrier → Q.Carrier)
    → (scott : is-scott-continuous f)
    → ∀ {x y} → x P.≤ y → f x Q.≤ f y  
  dcpo+scott→monotone P-dcpo f scott {x} {y} p =
    -- f x ≤ f y follows by considering the directed family {x, y} and applying Scott-continuity.
    Q.trans (proj₁ (proj₂ f-lub) (lift true)) (Q.reflexive ( fy-is-lub ))
    where
      -- The directed family indexed by Lift c Bool: s (lift true) = x, s (lift false) = y
      s : Lift c Bool → P.Carrier
      s (lift b) = if b then x else y

      -- For any index k, s k ≤ s (lift false) (i.e., x ≤ y and y ≤ y)
      sx≤sfalse : ∀ k → s k P.≤ s (lift false)
      sx≤sfalse k with lower k
      ... | true  = p
      ... | false = P.refl

      -- s is a directed family: both elements are below y
      s-directed : is-directed-family P s
      s-directed = record
        { elt = lift false ; semidirected = λ i j → lift false , (sx≤sfalse i , sx≤sfalse j)}

      -- The least upper bound of s is y
      lub = is-dcpo.has-directed-lub P-dcpo s-directed

      -- For any i, s i P.≤ y
      h′ : ∀ i → s i P.≤ y
      h′ i with lower i
      ... | true  = p
      ... | false = P.refl

      -- y is the least upper bound of s (in the poset sense)
      y-is-lub : proj₁ lub P.≈ y
      y-is-lub = P.antisym
        (proj₂ (proj₂ lub) y (λ i → h′ i))
        (proj₁ (proj₂ lub) (lift false))

      -- f preserves the lub, so f-lub is the lub of the image family
      f-lub = is-scott-continuous.preserve-lub scott s-directed lub

      -- f y is the least upper bound of the image family (in the codomain poset)
      fy-is-lub : proj₁ f-lub Q.≈ f y
      fy-is-lub = {!   !} 


-- module _ where
--   open import Relation.Binary.Bundles using (Poset)
--   open import Function using (_∘_)

--   private
--     module P {o ℓ₁ ℓ₂} (P : Poset o ℓ₁ ℓ₂) = Poset P
--     module Q {o ℓ₁ ℓ₂} (Q : Poset o ℓ₁ ℓ₂) = Poset Q
--     module R {o ℓ₁ ℓ₂} (R : Poset o ℓ₁ ℓ₂) = Poset R

--   scott-id : ∀ {o ℓ₁ ℓ₂} {P : Poset o ℓ₁ ℓ₂} → is-scott-continuous {P = P} {Q = P} id
--   -- scott-id : ∀ {o ℓ₁ ℓ₂} {P : Poset o ℓ₁ ℓ₂} → is-scott-continuous (id {A = Poset.Carrier P})
--   scott-id = record
--     { monotone = record { monotone = λ {x} {y} p → p }
--     ; preserve-lub = λ {Ix} {g} df dlub → dlub
--     }
  
-- scott-∘
--     : ∀ {o ℓ₁ ℓ₂} {P Q R : Poset o ℓ₁ ℓ₂}
--     → (f : Q.Carrier Q → R.Carrier R) (g : P.Carrier P → Q.Carrier Q)
--     → is-scott-continuous f → is-scott-continuous g
--     → is-scott-continuous (f ∘ g)
--   scott-∘ {P = P} {Q} {R} f g f-scott g-scott s dir x lub =
--     f-scott (g ∘ s) 
--       (monotone∘directed g (is-scott-continuous.monotone g-scott) dir)
--       (g x)
--       (g-scott s dir x lub)
