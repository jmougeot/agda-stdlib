\begin{code}
{-# OPTIONS --without-K --safe #-}

module Category.Functor.Naperian where

open import Effect.Functor using (RawFunctor)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

private
  variable
    ℓ ℓ′ ℓₛ : Level

-- RawNaperian contains just the functions, not the proofs
record RawNaperian {F : Set ℓ → Set ℓ′} (ℓ″ : Level) (RF : RawFunctor F) : Set (suc (ℓ ⊔ ℓ″) ⊔ ℓ′) where
  field
    Log : Set ℓ″
    index : ∀ {A} → F A → (Log → A)
    tabulate : ∀ {A} → (Log → A) → F A

-- Full Naperian has the coherence conditions too. Propositional version (hard to work with).
record Naperian {F : Set ℓ → Set ℓ′} (ℓ″ : Level) (RF : RawFunctor F) : Set (suc (ℓ ⊔ ℓ″) ⊔ ℓ′) where
  field
    rawNaperian : RawNaperian ℓ″ RF
  open RawNaperian rawNaperian public
  field
    tabulate-index : ∀ {A} → (fa : F A) → tabulate (index fa) ≡ fa
    index-tabulate : ∀ {A} → (f : Log → A) → ((l : Log) → index (tabulate f) l ≡ f l)

-- Should perhaps be called Indexed-Naperian?
record Raw-S-Naperian {F : Set ℓ → Set ℓ′} (ℓ″ : Level) (RF : RawFunctor F) (S : Set ℓₛ) : Set (suc (ℓ ⊔ ℓ″) ⊔ ℓ′ ⊔ ℓₛ) where
  field
    Log : S → Set ℓ″
    shape : ∀ {A} → F A → S
    index : ∀ {A} → (fa : F A) → (Log (shape fa) → A)
    tabulate : ∀ {A s} → (Log s → A) → F A

record S-Naperian {F : Set ℓ → Set ℓ′} (ℓ″ : Level) (RF : RawFunctor F) (S : Set ℓₛ) : Set (suc (ℓ ⊔ ℓ″) ⊔ ℓ′ ⊔ ℓₛ) where
  field
    raw-S-Naperian : Raw-S-Naperian ℓ″ RF S
  open Raw-S-Naperian raw-S-Naperian public
  field
    tabulate-index : ∀ {A} → (fa : F A) → tabulate (index fa) ≡ fa
    shape-pres : ∀ {A s} → (f : Log s → A) → shape (tabulate f) ≡ s
    index-tabulate : ∀ {A s} → (f : Log s → A) →
      let fa = tabulate f in
      ((l : Log (shape fa)) → index fa l ≡ f (subst Log (shape-pres f) l))
\end{code}
