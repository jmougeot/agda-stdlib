------------------------------------------------------------------------
-- Draft: Additional padRight properties for agda-stdlib
-- These should eventually be integrated into Data.Vec.Properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module padright-properties-draft where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n)
open import Data.Vec.Base using (Vec; []; _∷_; map; lookup; updateAt; zipWith; replicate; padRight; _++_; take; drop; tabulate)
open import Data.Vec.Properties using (map-replicate; zipWith-replicate)
open import Data.Fin using (Fin; zero; suc; inject≤; _↑ˡ_; fromℕ<)
open import Function.Base using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

variable
  A B C : Set
  m n p : ℕ

-- map : (A → B) → Vec A n → Vec B n
-- padRight : ∀ {m n} → m ≤ n → A → Vec A m → Vec A n
map-padRight : ∀ (f : A → B) (m≤n : m ≤ n) (a : A) (xs : Vec A m) →
               map f (padRight m≤n a xs) ≡ padRight m≤n (f a) (map f xs)
map-padRight f z≤n a [] = map-replicate f a _
map-padRight f (s≤s m≤n) a (x ∷ xs) = cong (f x ∷_) (map-padRight f m≤n a xs)

-- lookup : Vec A n → Fin n → A
-- padRight : ∀ {m n} → m ≤ n → A → Vec A m → Vec A n
-- inject≤ : ∀ {m n} → Fin m → m ≤ n → Fin n
lookup-padRight-inject≤ : ∀ (m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin m) →
                          lookup (padRight m≤n a xs) (inject≤ i m≤n) ≡ lookup xs i
lookup-padRight-inject≤ (s≤s m≤n) a (x ∷ xs) zero = refl
lookup-padRight-inject≤ (s≤s m≤n) a (x ∷ xs) (suc i) = lookup-padRight-inject≤ m≤n a xs i

-- zipWith : (A → B → C) → Vec A n → Vec B n → Vec C n
-- padRight : ∀ {m n} → m ≤ n → A → Vec A m → Vec A n
zipWith-padRight : ∀ {n} (f : A → B → C) (m≤n : m ≤ n) (a : A) (b : B) 
                   (xs : Vec A m) (ys : Vec B m) →
                   zipWith f (padRight m≤n a xs) (padRight m≤n b ys) ≡ 
                   padRight m≤n (f a b) (zipWith f xs ys)
zipWith-padRight {n} f z≤n a b [] [] = zipWith-replicate f a b
zipWith-padRight f (s≤s m≤n) a b (x ∷ xs) (y ∷ ys) = 
  cong (f x y ∷_) (zipWith-padRight f m≤n a b xs ys)

-- Properties for take and padRight
-- take : ∀ m {n} → Vec A (m + n) → Vec A m
-- padRight : ∀ {m n} → m ≤ n → A → Vec A m → Vec A n
-- subst : ∀ {a}{A : Set a}{x y} → x ≡ y → A x → A y
take-padRight : ∀ {p} (m≤n : m ≤ n) (a : A) (xs : Vec A m) → 
                (n≡m+p : n ≡ m + p) → take m (subst (Vec A) n≡m+p (padRight m≤n a xs)) ≡ xs
take-padRight {m = zero} z≤n a [] refl = refl
take-padRight {m = suc m} {p = p} (s≤s m≤n) a (x ∷ xs) refl = 
  cong (x ∷_) (take-padRight {p = p} m≤n a xs refl)

-- Properties for drop and padRight
-- drop : ∀ m {n} → Vec A (m + n) → Vec A n
-- padRight : ∀ {m n} → m ≤ n → A → Vec A m → Vec A n
-- subst : ∀ {a}{A : Set a}{x y} → x ≡ y → A x → A y
drop-padRight : ∀ {p} (m≤n : m ≤ n) (a : A) (xs : Vec A m) → 
                (n≡m+p : n ≡ m + p) → drop m (subst (Vec A) n≡m+p (padRight m≤n a xs)) ≡ replicate p a
drop-padRight {m = zero} z≤n a [] refl = refl
drop-padRight {m = suc m} {p = p} (s≤s m≤n) a (x ∷ xs) refl = drop-padRight {p = p} m≤n a xs refl

-- replicate : (n : ℕ) → A → Vec A n
-- padRight : ∀ {m n} → m ≤ n → A → Vec A m → Vec A n
replicate-padRight : ∀ (m≤n : m ≤ n) (a : A) → padRight m≤n a (replicate m a) ≡ replicate n a
replicate-padRight {m = zero} z≤n a = refl
replicate-padRight {m = suc m} (s≤s m≤n) a = 
  cong (a ∷_) (replicate-padRight m≤n a)

-- lookup-padRight-↑ˡ : ∀ (m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin (n ∸ m)) →
--                      lookup (padRight m≤n a xs) {!   !} ≡ a
-- lookup-padRight-↑ˡ {m = zero} z≤n a [] i = {!   !}
-- lookup-padRight-↑ˡ {m = suc m} (s≤s m≤n) a (x ∷ xs) i = lookup-padRight-↑ˡ m≤n a xs i

updateAt-padRight-inject≤ : ∀ (m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin m) (x : A) →
                           updateAt (inject≤ i m≤n) (λ _ → x) (padRight m≤n a xs) ≡ 
                           padRight m≤n a (updateAt i (λ _ → x) xs)
updateAt-padRight-inject≤ (s≤s m≤n) a (y ∷ xs) zero x = refl
updateAt-padRight-inject≤ (s≤s m≤n) a (y ∷ xs) (suc i) x = 
  cong (y ∷_) (updateAt-padRight-inject≤ m≤n a xs i x)

-- updateAt-padRight-↑ˡ : ∀ (m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin (n ∸ m)) (x : A) →
--                       updateAt (m ↑ˡ i) (λ _ → x) (padRight m≤n a xs) ≡ 
--                       padRight m≤n x xs
-- updateAt-padRight-↑ˡ {m = zero} z≤n a [] zero x = refl
-- updateAt-padRight-↑ˡ {m = zero} z≤n a [] (suc i) x = 
--   cong (a ∷_) (updateAt-padRight-↑ˡ z≤n a [] i x)
-- updateAt-padRight-↑ˡ {m = suc m} (s≤s m≤n) a (y ∷ xs) i x = 
--   cong (y ∷_) (updateAt-padRight-↑ˡ m≤n a xs i x)

-- _++_ : Vec A m → Vec A n → Vec A (m + n)
-- padRight : ∀ {m n} → m ≤ n → A → Vec A m → Vec A n
-- replicate : (n : ℕ) → A → Vec A n

-- padRight-++ : ∀ (m≤n : m ≤ n) (a : A) (xs : Vec A m) (ys : Vec A p) →
--               padRight m≤n a xs ++ ys ≡ xs ++ (replicate (n ∸ m) a ++ ys)
-- padRight-++ z≤n a [] ys = refl
-- padRight-++ (s≤s m≤n) a (x ∷ xs) ys = cong (x ∷_) (padRight-++ m≤n a xs ys)

-- _++_ : Vec A m → Vec A n → Vec A (m + n)
-- padRight : ∀ {m n} → m ≤ n → A → Vec A m → Vec A n
-- replicate : (n : ℕ) → A → Vec A n

-- ++-padRight : ∀ (xs : Vec A p) (m≤n : m ≤ n) (a : A) (ys : Vec A m) →
--               xs ++ padRight m≤n a ys ≡ xs ++ ys ++ replicate (n ∸ m) a
-- ++-padRight [] m≤n a ys = padRight-++ m≤n a ys []
-- ++-padRight (x ∷ xs) m≤n a ys = cong (x ∷_) (++-padRight xs m≤n a ys)




