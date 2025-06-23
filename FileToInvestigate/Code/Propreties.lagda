Miscellaneous properties that really ought to be somewhere in the
standard library. But they can go here for now.

\begin{code}
{-# OPTIONS --without-K --safe #-}

module Properties where

open import Data.Empty using (⊥; ⊥-elim)
import Data.Empty.Polymorphic as P
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (0↔⊥; +↔⊎; ¬Fin0)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_]′) renaming (map to map-⊎)
open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂; map₂)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as U
open import Function using (Inverseˡ; Inverseʳ)
open import Function.Base using (_∘_)
import Data.Vec.Functional as V
open import Function.Bundles using (Inverse;_↔_; mk↔ₛ′)
open import Function.Construct.Composition using (_↔-∘_)
open import Function.Construct.Identity using (↔-id)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; refl; subst)
open import Relation.Binary.PropositionalEquality.Properties
\end{code}

Singleton |Fin| is indeed the same thing as |⊤|, both at level $0$ and above.
\begin{code}
Fin1↔⊤ : Fin 1 ↔ ⊤
Fin1↔⊤ = mk↔ₛ′ (λ _ → tt) (λ tt → zero) (λ _ → refl) λ { zero → refl; (suc ()) }

Fin1↔⊤′ : {ℓ : Level} → Fin 1 ↔ U.⊤ {ℓ}
Fin1↔⊤′ = mk↔ₛ′ (λ _ → U.tt) (λ tt → zero) (λ _ → refl) λ { zero → refl; (suc ()) }
\end{code}

Polymorphic version of \AgdaFunction{Fin0↔⊥}.
\begin{code}
Fin0↔⊥′ : ∀ {ℓ} → Fin 0 ↔ P.⊥ {ℓ}
Fin0↔⊥′ = mk↔ₛ′ (λ ()) (λ ()) (λ ()) (λ ())
\end{code}

Parallel composition of equivalences.
\begin{code}
_⊎-↔_ : {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  A ↔ B → C ↔ D → (A ⊎ C) ↔ (B ⊎ D)
A↔B ⊎-↔ C↔D = mk↔ₛ′
  (map-⊎ (f A↔B) (f C↔D))
  (map-⊎ (f⁻¹ A↔B) (f⁻¹ C↔D))
  (λ { (inj₁ x) → ≡.cong inj₁ (inverseˡ A↔B refl) ; (inj₂ y) → ≡.cong inj₂ (inverseˡ C↔D refl)})
  (λ { (inj₁ x) → ≡.cong inj₁ (inverseʳ A↔B refl) ; (inj₂ y) → ≡.cong inj₂ (inverseʳ C↔D refl)})
  where open Inverse renaming (to to f; from to f⁻¹)
\end{code}

This is a generalization of |Data.Fin.splitAt|.
\begin{code}
sum↔⨄ : {k : ℕ} (x : Fin k → ℕ) → Fin (V.foldr _+_ 0 x) ↔ V.foldr _⊎_ ⊥ (Fin ∘ x)
sum↔⨄ {ℕ.zero} x =  0↔⊥ 
sum↔⨄ {ℕ.suc k} x = (↔-id _ ⊎-↔ sum↔⨄ (x ∘ suc)) ↔-∘  +↔⊎ {V.head x}
\end{code}

Borrowing from |Function.Related.TypeIsomorphism|, but just one direction is needed.
\begin{code}
Σ-≡,≡⇒≡ : ∀ {a b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B} →
          (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
             subst B p (proj₂ p₁) ≡ proj₂ p₂) →
          (p₁ ≡ p₂)
Σ-≡,≡⇒≡ (refl , refl) = refl
\end{code}

Changing just the first component of a |Σ|.
\begin{code}
Σ₁↔ : ∀ {i j p} {I : Set i} (J : Set j) (C : I → Set p)
  (I↔J : I ↔ J) → let open Inverse I↔J renaming (to to f; from to f⁻¹) in
  (coh : ∀ j → ≡.cong f⁻¹ (inverseˡ refl) ≡ inverseʳ refl) →
  Σ I C ↔ Σ J (C ∘ f⁻¹)
Σ₁↔ J C iso coh =
  mk↔ₛ′ (λ { (i , c) → f i , subst C (≡.sym (inverseʳ refl)) c})
       (λ { (j , c′) → f⁻¹ j , c′})
       (λ { (j , c′) → Σ-≡,≡⇒≡ (inverseˡ refl , invˡ j c′)})
       λ { (i , c) → Σ-≡,≡⇒≡ (inverseʳ refl , subst-subst-sym (inverseʳ refl))}
  where
  open Inverse iso renaming (to to f; from to f⁻¹)
  open ≡.≡-Reasoning
  invˡ : (j : J) (c′ : C (f⁻¹ j)) → subst (C ∘ f⁻¹) (inverseˡ refl)
          (subst C (≡.sym (inverseʳ refl)) c′) ≡ c′
  invˡ j c′ = begin
    subst (C ∘ f⁻¹) (inverseˡ refl) (subst C (≡.sym (inverseʳ refl)) c′)      ≡⟨ subst-∘ (inverseˡ refl) ⟩
    subst C (≡.cong f⁻¹ (inverseˡ refl)) (subst C (≡.sym (inverseʳ refl)) c′) ≡⟨ ≡.cong (λ z → subst C z (subst C (≡.sym (proj₂ inverse refl)) c′)) (coh j) ⟩
    subst C (inverseʳ refl) (subst C (≡.sym (inverseʳ refl)) c′)        ≡⟨ subst-subst-sym (inverseʳ _) ⟩
    c′ ∎

Σ₂↔ : ∀ {i p q} {I : Set i} (C : I → Set p) (D : I → Set q)
  (C↔D : ∀ i → C i ↔ D i) → Σ I C ↔ Σ I D
Σ₂↔ C D iso =
  mk↔ₛ′ (λ { (i , c) → i , f (iso i) c})
       (λ { (i , d) → (i , f⁻¹ (iso i) d)})
       (λ { (i , d) → ≡.cong (i ,_) (inverseˡ (iso i) refl) })
       (λ { (i , c) → ≡.cong (i ,_) (inverseʳ (iso i) refl) })
  where open Inverse renaming (to to f; from to f⁻¹)
\end{code}

Whether we use unary numbers encoded via injections or explicit numbering, we end up with the same types.
The zero case is weird, so don't worry about it at all. Note the non-trivial pattern of recursion!
\begin{code}
⨄↔ΣFin : (k : ℕ) (C : Fin (suc k) → Set) → V.foldr _⊎_ ⊥ C ↔ Σ (Fin (suc k)) C
⨄↔ΣFin k C = mk↔ₛ′ (f k C) (g k C) (f∘g≗id k C) (g∘f≗id k C)
  where
    f : (n : ℕ) (D : Fin (suc n) → Set) → D zero ⊎ V.foldr _⊎_ ⊥ (D ∘ suc) → Σ (Fin (suc n)) D
    f n       _ (inj₁ x) = zero , x
    f (suc n) D (inj₂ y) = let (m , z) = f n (D ∘ suc) y in suc m , z
    g : (n : ℕ) (D : Fin (suc n) → Set) → Σ (Fin (suc n)) D → D zero ⊎ V.foldr _⊎_ ⊥ (D ∘ suc)
    g n D (zero , d) = inj₁ d
    g (suc n) D (suc k , d) = inj₂ (g n (D ∘ suc) (k , d))
    f∘g≗id : (n : ℕ) (D : Fin (suc n) → Set) → (x : Σ (Fin (suc n)) D) → f n D (g n D x) ≡ x
    f∘g≗id n D (zero , d) = refl
    f∘g≗id (suc n) D (suc k , d) = ≡.cong (λ z → (suc (proj₁ z) , proj₂ z)) (f∘g≗id n (D ∘ suc) (k , d))
    g∘f≗id : (n : ℕ) (D : Fin (suc n) → Set) → (z : D zero ⊎ V.foldr _⊎_ ⊥ (D ∘ suc)) → g n D (f n D z) ≡ z
    g∘f≗id n D (inj₁ x) = refl
    g∘f≗id (suc n) D (inj₂ y) = ≡.cong inj₂ (g∘f≗id n (D ∘ suc) y)
\end{code}
