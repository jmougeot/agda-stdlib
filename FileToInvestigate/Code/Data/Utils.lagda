Everything in this module should really be in stdlib.
\begin{code}
{-# OPTIONS --without-K --safe #-}
module Data.Utils where

import Data.Maybe as Maybe
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.List
  using (List; []; _∷_; take; drop; head; map; length; tabulate; _++_; [_]; _∷ʳ_)
open import Data.List.Properties using (length-tabulate; ++-identityʳ)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _≥_; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive)
open import Function.Base using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning; subst)
\end{code}

Some set-up to make the statements below nicer to read.
\begin{code}
private
  variable
    a b : Level
    A : Set a
    B : Set b
\end{code}

Taking and dropping from an empty list do nothing.
\begin{code}
take-[] : ∀ m → take {A = A} m [] ≡ []
take-[] ℕ.zero = refl
take-[] (suc m) = refl

drop-[] : ∀ m → drop {A = A} m [] ≡ []
drop-[] ℕ.zero = refl
drop-[] (suc m) = refl

take-drop-[] : ∀ m n → take n (drop {A = A} m []) ≡ []
take-drop-[] m n = trans (cong (take n) (drop-[] m)) (take-[] n)
\end{code}

You can 'commute' List.head and List.map, to obtain a Maybe.map and List.head.
\begin{code}
head-map-commute : {f : A → B} (l : List A) → head (map f l) ≡ Maybe.map f (head l)
head-map-commute [] = refl
head-map-commute (_ ∷ _) = refl
\end{code}

If you take at least as many elements from a list as it has, you get the whole list.
\begin{code}
take-all : {a : Level} {A : Set a} (k : ℕ) (l : List A) → (k ≥ length l) → take k l ≡ l
take-all ℕ.zero [] _ = refl
take-all (suc _) [] _ = refl
take-all (suc k) (x ∷ l) (s≤s pf) = cong (x ∷_) (take-all k l pf)
\end{code}

If we take and drop in a specific way, a concatenation of these "adds up". This is basically
interval arithmetic.
\begin{code}
take-drop-++ : {a : Level} {A : Set a} (s l₁ l₂ : ℕ) (lst : List A)  →
  take l₁ (drop s lst) ++ take l₂ (drop (s + l₁) lst) ≡ take (l₁ + l₂) (drop s lst)
take-drop-++ s l₁ l₂ [] = begin
  take l₁ (drop s []) ++ take l₂ (drop (s + l₁) []) ≡⟨ cong₂ _++_ (take-drop-[] s l₁) (take-drop-[] (s + l₁) l₂) ⟩
  [] ++ []                                          ≡⟨ ++-identityʳ [] ⟩
  []                                                ≡˘⟨ take-drop-[] s _ ⟩
  take (l₁ + l₂) (drop s [])                        ∎
  where open ≡-Reasoning
take-drop-++ ℕ.zero ℕ.zero   l₂ (x ∷ lst) = refl
take-drop-++ ℕ.zero (suc l₁) l₂ (x ∷ lst) = cong (x ∷_) (take-drop-++ ℕ.zero l₁ l₂ lst)
take-drop-++ (suc s) l₁       l₂ (x ∷ lst) = take-drop-++ s l₁ l₂ lst
\end{code}

take and drop commute with map.
\begin{code}
take-map-commute : {x y : Level} {X : Set x} {Y : Set y} {f : X → Y} → (m : ℕ) (l : List X) → take m (map f l) ≡ map f (take m l)
take-map-commute zero l = refl
take-map-commute (suc s) [] = refl
take-map-commute (suc s) (x ∷ l) = cong (_ ∷_) (take-map-commute s l)

drop-map-commute : {x y : Level} {X : Set x} {Y : Set y} {f : X → Y} → (m : ℕ) (l : List X) → drop m (map f l) ≡ map f (drop m l)
drop-map-commute zero l = refl
drop-map-commute (suc m) [] = refl
drop-map-commute (suc m) (x ∷ l) = drop-map-commute m l
\end{code}

\begin{code}
take+0 : {x : Level} {X : Set x} → (m : ℕ) (l : List X) → take (m + 0) l ≡ take m l
take+0 zero _ = refl
take+0 (suc m) [] = refl
take+0 (suc m) (l ∷ ls) =  begin
  take (suc m + 0) (l ∷ ls) ≡⟨⟩
  l ∷ take (m + 0) ls ≡⟨ cong (l ∷_) (take+0 m ls) ⟩
  l ∷ take m ls ∎
  where open ≡-Reasoning
\end{code}

\begin{code}
take-drop-1 : {x : Level} {X : Set x} {k : ℕ} (f : Fin k → X) (n : Fin k) →
  drop (toℕ n) (take (suc (toℕ n)) (tabulate f)) ≡ [ f n ]
take-drop-1 f zero    = refl
take-drop-1 f (suc n) = take-drop-1 (f ∘ suc) n
\end{code}

\begin{code}
take-one-more : {ℓ : Level} {X : Set ℓ} {m : ℕ} (x : Fin m) (f : Fin m → X) →
   take (toℕ x) (tabulate f) ∷ʳ f x ≡ take (suc (toℕ x)) (tabulate f)
take-one-more {m = suc m} zero    f = refl
take-one-more {m = suc m} (suc x) f = cong (f zero ∷_) (take-one-more x (f ∘ suc))
\end{code}
