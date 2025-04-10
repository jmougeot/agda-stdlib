------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointers into star-lists
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Star.Pointer {ℓ} {I : Set ℓ} where

open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Star.Decoration
open import Data.Unit.Base using (tt)
open import Function.Base using (const; case_of_)
open import Level using (Level; _⊔_; lift)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (NonEmpty; nonEmpty)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
      using (Star; ε; _◅_; gmap; map; _◅◅_; _▻▻_; _⋆)

private
  variable
    r p q : Level

-- Pointers into star-lists. The edge pointed to is decorated with Q,
-- while other edges are decorated with P.

data Pointer {T : Rel I r}
             (P : EdgePred p T) (Q : EdgePred q T)
             : Rel (Maybe (NonEmpty (Star T))) (ℓ ⊔ r ⊔ p ⊔ q) where
  step : ∀ {i j k} {x : T i j} {xs : Star T j k}
         (p : P x) → Pointer P Q (just (nonEmpty (x ◅ xs)))
                                 (just (nonEmpty xs))
  done : ∀ {i j k} {x : T i j} {xs : Star T j k}
         (q : Q x) → Pointer P Q (just (nonEmpty (x ◅ xs))) nothing

-- Any P Q xs means that some edge in xs satisfies Q, while all
-- preceding edges satisfy P. A star-list of type Any Always Always xs
-- is basically a prefix of xs; the existence of such a prefix
-- guarantees that xs is non-empty.

Any : {T : Rel I r} (P : EdgePred p T) (Q : EdgePred q T) →
      EdgePred (ℓ ⊔ (r ⊔ (p ⊔ q))) (Star T)
Any P Q xs = Star (Pointer P Q) (just (nonEmpty xs)) nothing

module _ {T : Rel I r} {P : EdgePred p T} {Q : EdgePred q T} where

  this : ∀ {i j k} {x : T i j} {xs : Star T j k} →
         Q x → Any P Q (x ◅ xs)
  this q = done q ◅ ε

  that : ∀ {i j k} {x : T i j} {xs : Star T j k} →
         P x → Any P Q xs → Any P Q (x ◅ xs)
  that p = _◅_ (step p)

-- Safe lookup.

data Result (T : Rel I r)
            (P : EdgePred p T) (Q : EdgePred q T) : Set (ℓ ⊔ r ⊔ p ⊔ q) where
  result : ∀ {i j} {x : T i j} (p : P x) (q : Q x) → Result T P Q

-- The first argument points out which edge to extract. The edge is
-- returned, together with proofs that it satisfies Q and R.

module _ {T : Rel I r} {P : EdgePred p T} {Q : EdgePred q T} where

  lookup : ∀ {r} {R : EdgePred r T} {i j} {xs : Star T i j} →
           All R xs → Any P Q xs → Result T Q R
  lookup (↦ r ◅ _)  (done q ◅ ε)  = result q r
  lookup (↦ _ ◅ rs) (step p ◅ ps) = lookup rs ps

-- We can define something resembling init.

  prefixIndex : ∀ {i j} {xs : Star T i j} → Any P Q xs → I
  prefixIndex (done {i = i} q ◅ _)  = i
  prefixIndex (step p         ◅ ps) = prefixIndex ps

  prefix : ∀ {i j} {xs : Star T i j} →
           (ps : Any P Q xs) → Star T i (prefixIndex ps)
  prefix (done q         ◅ _)  = ε
  prefix (step {x = x} p ◅ ps) = x ◅ prefix ps

-- Here we are taking the initial segment of ps (all elements but the
-- last, i.e. all edges satisfying P).

  init : ∀ {i j} {xs : Star T i j} →
        (ps : Any P Q xs) → All P (prefix ps)
  init (done q ◅ _)  = ε
  init (step p ◅ ps) = ↦ p ◅ init ps

-- One can simplify the implementation by not carrying around the
-- indices in the type:

  last : ∀ {i j} {xs : Star T i j} →
         Any P Q xs → NonEmptyEdgePred T Q
  last ps with result q _ ← lookup {r = p} (decorate (const (lift tt)) _) ps =
    nonEmptyEdgePred q
