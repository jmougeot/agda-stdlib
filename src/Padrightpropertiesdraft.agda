------------------------------------------------------------------------
-- Draft: Additional padRight properties for agda-stdlib
-- These should eventually be integrated into Data.Vec.Properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Padrightpropertiesdraft where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n)
open import Data.Vec.Base
open import Data.Vec.Properties using (map-replicate; zipWith-replicate; padRight-trans)
open import Data.Fin using (Fin; zero; suc; inject≤; _↑ˡ_; fromℕ<)
open import Function.Base using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning) 


variable
  A B C : Set
  m n p : ℕ

map-padRight : ∀ (f : A → B) (m≤n : m ≤ n) (a : A) (xs : Vec A m) →
               map f (padRight m≤n a xs) ≡ padRight m≤n (f a) (map f xs)
map-padRight f z≤n a [] = map-replicate f a _
map-padRight f (s≤s m≤n) a (x ∷ xs) = cong (f x ∷_) (map-padRight f m≤n a xs)

lookup-padRight : ∀ (m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin m) →
                          lookup (padRight m≤n a xs) (inject≤ i m≤n) ≡ lookup xs i
lookup-padRight (s≤s m≤n) a (x ∷ xs) zero = refl
lookup-padRight (s≤s m≤n) a (x ∷ xs) (suc i) = lookup-padRight m≤n a xs i

zipWith-padRight : ∀ {n} (f : A → B → C) (m≤n : m ≤ n) (a : A) (b : B) 
                   (xs : Vec A m) (ys : Vec B m) → zipWith f (padRight m≤n a xs) (padRight m≤n b ys) ≡ padRight m≤n (f a b) (zipWith f xs ys)

zipWith-padRight {n} f z≤n a b [] [] = zipWith-replicate f a b
zipWith-padRight f (s≤s m≤n) a b (x ∷ xs) (y ∷ ys) =  cong (f x y ∷_) (zipWith-padRight f m≤n a b xs ys)

PadRight-zipWith : ∀ {m p n} (f : A → B → C) (m≤n : m ≤ n)  (p≤m : p ≤ m) (a : A) (b : B) (xs : Vec A m) (ys : Vec B p) →
                   zipWith f (padRight m≤n a xs) (padRight (≤-trans p≤m m≤n) b ys) ≡ padRight m≤n (f a b) (zipWith f xs (padRight p≤m b ys))
PadRight-zipWith {m} {p} {n} f m≤n p≤m a b xs ys = trans (cong (zipWith f (padRight m≤n a xs)) (padRight-trans p≤m m≤n b ys))
    (zipWith-padRight f m≤n a b xs (padRight p≤m b ys))

take-padRight : ∀ {p} (m≤n : m ≤ n) (a : A) (xs : Vec A m) → (n≡m+p : n ≡ m + p) → take m (subst (Vec A) n≡m+p (padRight m≤n a xs)) ≡ xs
take-padRight {m = zero} z≤n a [] refl = refl
take-padRight {m = suc m} {p = p} (s≤s m≤n) a (x ∷ xs) refl = cong (x ∷_) (take-padRight {p = p} m≤n a xs refl)

drop-padRight : ∀ {p} (m≤n : m ≤ n) (a : A) (xs : Vec A m) → 
                (n≡m+p : n ≡ m + p) → drop m (subst (Vec A) n≡m+p (padRight m≤n a xs)) ≡ replicate p a
drop-padRight {m = zero} z≤n a [] refl = refl
drop-padRight {m = suc m} {p = p} (s≤s m≤n) a (x ∷ xs) refl = drop-padRight {p = p} m≤n a xs refl


updateAt-padRight : ∀ (m≤n : m ≤ n) (xs : Vec A m) (f : A → A) (i : Fin m) (x : A) → 
                    updateAt (padRight m≤n x xs) (inject≤ i m≤n) f ≡ padRight m≤n x (updateAt xs i f)
updateAt-padRight (s≤s m≤n) (y ∷ xs) f zero x = refl
updateAt-padRight (s≤s m≤n) (y ∷ xs) f (suc i) x = cong (y ∷_) (updateAt-padRight m≤n xs f i x)





