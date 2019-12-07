------------------------------------------------------------------------
-- Some alternative definitions of the concept of being an
-- equivalence: n-path-split and ∞-path-split
------------------------------------------------------------------------

-- Based on the blog post "Universal properties without function
-- extensionality" by Mike Shulman
-- (https://homotopytypetheory.org/2014/11/02/universal-properties-without-function-extensionality/),
-- and the corresponding code in the Coq HoTT library
-- (https://github.com/HoTT/HoTT).

{-# OPTIONS --without-K --safe #-}

open import Equality

module Equivalence.Path-split
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Embedding eq using (Embedding)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Function-universe eq hiding (_∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Surjection eq using (Split-surjective; _↠_)

private
  variable
    a b : Level
    A B : Set a
    x y : A
    f   : A → B
    k   : Kind
    n   : ℕ

-- An alternative definition of "Is-equivalence".

Path-split : {A : Set a} {B : Set b} → ℕ → (A → B) → Set (a ⊔ b)
Path-split zero    f = ↑ _ ⊤
Path-split (suc n) f =
  Split-surjective f ×
  (∀ x y → Path-split n (cong {x = x} {y = y} f))

private

  -- A lemma.

  eq→emb : Is-equivalence f → Is-equivalence (cong {x = x} {y = y} f)
  eq→emb eq =
    Embedding.is-embedding (from-isomorphism Eq.⟨ _ , eq ⟩) _ _

-- Equivalences are path-split.

Is-equivalence→Path-split : Is-equivalence f → Path-split n f
Is-equivalence→Path-split {n = zero}  eq = _
Is-equivalence→Path-split {n = suc n} eq =
    _≃_.split-surjective Eq.⟨ _ , eq ⟩
  , λ x y → Is-equivalence→Path-split (eq→emb eq)

private

  -- Path-split n f holds, for n ≥ 2, iff f is an equivalence.

  Path-split⇔Is-equivalence :
    Path-split (2 + n) f ⇔ Is-equivalence f
  Path-split⇔Is-equivalence {f = f} = record
    { to   = λ (s , p) →
               let inv    = proj₁ ∘ s
                   is-inv = proj₂ ∘ s
               in _≃_.is-equivalence $ Eq.↔⇒≃ (record
                    { surjection = record
                      { right-inverse-of = is-inv
                      }
                    ; left-inverse-of = λ x →  $⟨ is-inv (f x) ⟩
                        f (inv (f x)) ≡ f x    ↝⟨ proj₁ ∘ proj₁ (p _ _) ⟩
                        inv (f x) ≡ x          □
                    })
    ; from = Is-equivalence→Path-split
    }

-- If f is an equivalence, then Split-surjective f is contractible
-- (assuming extensionality).

Split-surjective-contractible-for-equivalences :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} →
  Extensionality b (a ⊔ b) →
  Is-equivalence f →
  Contractible (Split-surjective f)
Split-surjective-contractible-for-equivalences
  {A = A} {B = B} {f = f} ext eq =

  propositional⇒inhabited⇒contractible
    (Π-closure ext 1 λ y →
     let surj : (∃ λ x → x ≡ _≃_.from A≃B y) ↠ (∃ λ x → f x ≡ y)
         surj = ∃-cong λ x →
           x ≡ _≃_.from A≃B y        ↔⟨ inverse $ Eq.≃-≡ A≃B ⟩
           f x ≡ f (_≃_.from A≃B y)  ↝⟨ ≡⇒↝ _ $ cong (_ ≡_) $ _≃_.right-inverse-of A≃B _ ⟩□
           f x ≡ y                   □
     in
     H-level.respects-surjection surj 1 $
     mono₁ 0 $
     singleton-contractible _)
    (_≃_.split-surjective A≃B)
  where
  A≃B : A ≃ B
  A≃B = Eq.⟨ _ , eq ⟩

-- If f is an equivalence, then Path-split n f is contractible
-- (assuming extensionality).

Path-split-contractible-for-equivalences :
  {A : Set a} {B : Set b} {f : A → B} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-equivalence f →
  Contractible (Path-split n f)
Path-split-contractible-for-equivalences {n = zero} _ _ =
  ↑-closure 0 $
  ⊤-contractible

Path-split-contractible-for-equivalences
  {a = a} {b = b} {n = suc n} {A = A} {B = B} {f = f} ext eq =

  ×-closure 0
    (Split-surjective-contractible-for-equivalences
       (lower-extensionality a lzero ext) eq)
    (Π-closure (lower-extensionality b lzero ext) 0 λ _ →
     Π-closure (lower-extensionality b lzero ext) 0 λ _ →
     Path-split-contractible-for-equivalences
        ext (eq→emb eq))

-- Path-split n is pointwise propositional for n ≥ 2 (assuming
-- extensionality).

Path-split-propositional :
  {A : Set a} {B : Set b} {f : A → B} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-proposition (Path-split (2 + n) f)
Path-split-propositional ext =
  [inhabited⇒contractible]⇒propositional λ p →
  Path-split-contractible-for-equivalences ext $
    _⇔_.to Path-split⇔Is-equivalence p

-- There is a bijection between Path-split n f, for n ≥ 2, and
-- Is-equivalence f (assuming extensionality).

Path-split↔Is-equivalence :
  {A : Set a} {B : Set b} {f : A → B} →
  Extensionality? k (a ⊔ b) (a ⊔ b) →
  Path-split (2 + n) f ↝[ k ] Is-equivalence f
Path-split↔Is-equivalence =
  generalise-ext?-prop
    Path-split⇔Is-equivalence
    Path-split-propositional
    (λ ext → Eq.propositional ext _)

-- Another alternative definition of "Is-equivalence".

Path-split-∞ : {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Path-split-∞ f = ∀ n → Path-split n f

-- Path-split-∞ is pointwise propositional (assuming extensionality).

Path-split-∞-propositional :
  {A : Set a} {B : Set b} {f : A → B} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-proposition (Path-split-∞ f)
Path-split-∞-propositional ext =
  [inhabited⇒contractible]⇒propositional λ p →
  Π-closure (lower-extensionality _ lzero ext) 0 λ _ →
  Path-split-contractible-for-equivalences ext $
    _⇔_.to Path-split⇔Is-equivalence (p 2)

-- There is a bijection between Path-split-∞ f and Is-equivalence f
-- (assuming extensionality).

Path-split-∞↔Is-equivalence :
  {A : Set a} {B : Set b} {f : A → B} →
  Extensionality? k (a ⊔ b) (a ⊔ b) →
  Path-split-∞ f ↝[ k ] Is-equivalence f
Path-split-∞↔Is-equivalence =
  generalise-ext?-prop
    (record
       { to   = λ p → _⇔_.to Path-split⇔Is-equivalence (p 2)
       ; from = λ eq _ → Is-equivalence→Path-split eq
       })
    Path-split-∞-propositional
    (λ ext → Eq.propositional ext _)
