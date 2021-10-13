------------------------------------------------------------------------
-- Some alternative definitions of the concept of being an equivalence
------------------------------------------------------------------------

-- Partly based on the blog post "Universal properties without
-- function extensionality" by Mike Shulman
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

import Bijection eq as B
open import Embedding eq using (Embedding)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Function-universe eq hiding (_∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Surjection eq using (Split-surjective; _↠_)

private
  variable
    a b c d p : Level
    A B       : Type a
    x y       : A
    f         : A → B
    k         : Kind
    n         : ℕ

------------------------------------------------------------------------
-- Path-split

-- An alternative definition of "Is-equivalence".

Path-split : {A : Type a} {B : Type b} → ℕ → (A → B) → Type (a ⊔ b)
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
  ∀ {a b} {A : Type a} {B : Type b} {f : A → B} →
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
  {A : Type a} {B : Type b} {f : A → B} →
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
  {A : Type a} {B : Type b} {f : A → B} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-proposition (Path-split (2 + n) f)
Path-split-propositional ext =
  [inhabited⇒contractible]⇒propositional λ p →
  Path-split-contractible-for-equivalences ext $
    _⇔_.to Path-split⇔Is-equivalence p

-- There is a bijection between Path-split n f, for n ≥ 2, and
-- Is-equivalence f (assuming extensionality).

Path-split↔Is-equivalence :
  {A : Type a} {B : Type b} {f : A → B} →
  Path-split (2 + n) f ↝[ a ⊔ b ∣ a ⊔ b ] Is-equivalence f
Path-split↔Is-equivalence =
  generalise-ext?-prop
    Path-split⇔Is-equivalence
    Path-split-propositional
    (λ ext → Eq.propositional ext _)

-- Another alternative definition of "Is-equivalence".

Path-split-∞ : {A : Type a} {B : Type b} → (A → B) → Type (a ⊔ b)
Path-split-∞ f = ∀ n → Path-split n f

-- Path-split-∞ is pointwise propositional (assuming extensionality).

Path-split-∞-propositional :
  {A : Type a} {B : Type b} {f : A → B} →
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
  {A : Type a} {B : Type b} {f : A → B} →
  Path-split-∞ f ↝[ a ⊔ b ∣ a ⊔ b ] Is-equivalence f
Path-split-∞↔Is-equivalence =
  generalise-ext?-prop
    (record
       { to   = λ p → _⇔_.to Path-split⇔Is-equivalence (p 2)
       ; from = λ eq _ → Is-equivalence→Path-split eq
       })
    Path-split-∞-propositional
    (λ ext → Eq.propositional ext _)

-- A preservation lemma for Path-split.

Path-split-cong :
  {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  {f : A → B} {g : C → D} →
  Extensionality? k (a ⊔ b ⊔ c ⊔ d) (a ⊔ b ⊔ c ⊔ d) →
  (A≃C : A ≃ C) (B≃D : B ≃ D) →
  (∀ x → g (_≃_.to A≃C x) ≡ _≃_.to B≃D (f x)) →
  ∀ n → Path-split n f ↝[ k ] Path-split n g
Path-split-cong
  {a = a} {b = b} {c = c} {d = d} {k = k} {f = f} {g = g}
  ext A≃C B≃D hyp = λ where

  zero →
    ↑ _ ⊤  ↔⟨ B.↑↔ ⟩
    ⊤      ↔⟨ inverse B.↑↔ ⟩□
    ↑ _ ⊤  □

  (suc n) →

    (Split-surjective f                   ↔⟨⟩

     (∀ y → ∃ λ x → f x ≡ y)              ↝⟨ (Π-cong (lower-extensionality? k (a ⊔ c) lzero ext) B≃D λ y →
                                              Σ-cong A≃C λ x →

       (f x ≡ y)                                ↔⟨ inverse $ Eq.≃-≡ B≃D ⟩
       (_≃_.to B≃D (f x) ≡ _≃_.to B≃D y)        ↝⟨ ≡⇒↝ _ $ cong (_≡ _) $ sym $ hyp x ⟩□
       (g (_≃_.to A≃C x) ≡ _≃_.to B≃D y)        □) ⟩

     (∀ y → ∃ λ x → g x ≡ y)              ↔⟨⟩

     Split-surjective g                   □)

      ×-cong

    (Π-cong (lower-extensionality? k (b ⊔ d) lzero ext) A≃C λ x →
     Π-cong (lower-extensionality? k (b ⊔ d) lzero ext) A≃C λ y →
     Path-split-cong ext

       (x ≡ y                        ↝⟨ inverse $ Eq.≃-≡ A≃C ⟩□
        _≃_.to A≃C x ≡ _≃_.to A≃C y  □)

       (f x ≡ f y                            ↝⟨ inverse $ Eq.≃-≡ B≃D ⟩
        _≃_.to B≃D (f x) ≡ _≃_.to B≃D (f y)  ↝⟨ ≡⇒↝ _ $ cong₂ _≡_ (sym $ hyp x) (sym $ hyp y) ⟩□
        g (_≃_.to A≃C x) ≡ g (_≃_.to A≃C y)  □)

       (λ x≡y →
          cong g (cong (_≃_.to A≃C) x≡y)                            ≡⟨ cong-∘ _ _ _ ⟩

          cong (g ∘ _≃_.to A≃C) x≡y                                 ≡⟨ elim¹
                                                                         (λ {y} x≡y →
                                                                            cong (g ∘ _≃_.to A≃C) x≡y ≡
                                                                            trans (trans (hyp x) (cong (_≃_.to B≃D ∘ f) x≡y))
                                                                              (sym $ hyp y))
                                                                         (
            cong (g ∘ _≃_.to A≃C) (refl _)                                ≡⟨ cong-refl _ ⟩

            refl _                                                        ≡⟨ sym $ trans-symʳ _ ⟩

            trans (hyp x) (sym $ hyp x)                                   ≡⟨ cong (flip trans _) $
                                                                             trans (sym $ trans-reflʳ _) $
                                                                             cong (trans _) $ sym $ cong-refl _ ⟩∎
            trans (trans (hyp x) (cong (_≃_.to B≃D ∘ f) (refl _)))
              (sym $ hyp x)                                               ∎)
                                                                         _ ⟩
          trans (trans (hyp x) (cong (_≃_.to B≃D ∘ f) x≡y))
            (sym $ hyp y)                                           ≡⟨ trans (cong (flip trans _) $ sym $
                                                                              subst-trans _) $
                                                                       trans-subst ⟩
          subst (_ ≡_) (sym $ hyp y)
            (subst (_≡ _) (sym $ hyp x)
               (cong (_≃_.to B≃D ∘ f) x≡y))                         ≡⟨ trans (cong (subst _ _) $
                                                                              subst-in-terms-of-≡⇒↝ equivalence _ _ _) $
                                                                       subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
          _≃_.to (≡⇒↝ _ (cong (_ ≡_) (sym $ hyp y)))
            (_≃_.to (≡⇒↝ _ (cong (_≡ _) (sym $ hyp x)))
               (cong (_≃_.to B≃D ∘ f) x≡y))                         ≡⟨ cong (_$ cong (_≃_.to B≃D ∘ f) x≡y) $ sym $
                                                                       ≡⇒↝-trans equivalence ⟩
          _≃_.to
            (≡⇒↝ _ $
             trans (cong (_≡ _) (sym $ hyp x))
               (cong (_ ≡_) (sym $ hyp y)))
            (cong (_≃_.to B≃D ∘ f) x≡y)                             ≡⟨⟩

          _≃_.to (≡⇒↝ _ $ cong₂ _≡_ (sym $ hyp x) (sym $ hyp y))
            (cong (_≃_.to B≃D ∘ f) x≡y)                             ≡⟨ cong (_≃_.to (≡⇒↝ _ _)) $ sym $
                                                                       cong-∘ _ _ _ ⟩∎
          _≃_.to (≡⇒↝ _ $ cong₂ _≡_ (sym $ hyp x) (sym $ hyp y))
            (cong (_≃_.to B≃D) (cong f x≡y))                        ∎)

       n)

------------------------------------------------------------------------
-- Extendable along

-- Is-[ n ]-extendable-along-[ f ] P means that P is n-extendable
-- along f.

Is-[_]-extendable-along-[_] :
  {A : Type a} {B : Type b} →
  ℕ → (A → B) → (B → Type c) → Type (a ⊔ b ⊔ c)
Is-[ zero  ]-extendable-along-[ f ] P = ↑ _ ⊤
Is-[ suc n ]-extendable-along-[ f ] P =
  ((g : ∀ x → P (f x)) →
     ∃ λ (h : ∀ x → P x) → ∀ x → h (f x) ≡ g x) ×
  ((g h : ∀ x → P x) →
     Is-[ n ]-extendable-along-[ f ] (λ x → g x ≡ h x))

-- Is-∞-extendable-along-[ f ] P means that P is ∞-extendable along f.

Is-∞-extendable-along-[_] :
  {A : Type a} {B : Type b} →
  (A → B) → (B → Type c) → Type (a ⊔ b ⊔ c)
Is-∞-extendable-along-[ f ] P =
  ∀ n → Is-[ n ]-extendable-along-[ f ] P

-- In the presence of extensionality Is-[_]-extendable-along-[_] can
-- be expressed using Path-split.

Is-extendable-along≃Path-split :
  {A : Type a} {B : Type b} {P : B → Type p} {f : A → B} →
  Extensionality (a ⊔ b ⊔ p) (a ⊔ b ⊔ p) →
  ∀ n →
  Is-[ n ]-extendable-along-[ f ] P ≃
  Path-split n (λ (g : ∀ x → P x) → g ∘ f)
Is-extendable-along≃Path-split {a = a} {b = b} {p = p} {f = f} ext =
  λ where
    zero    → Eq.id
    (suc n) →
      (∀-cong (lower-extensionality b lzero ext) λ g →
       ∃-cong λ h →
         (∀ x → h (f x) ≡ g x)  ↝⟨ Eq.extensionality-isomorphism
                                     (lower-extensionality (b ⊔ p) (a ⊔ b) ext) ⟩□
         h ∘ f ≡ g              □)
        ×-cong
      (∀-cong (lower-extensionality a lzero ext) λ g →
       ∀-cong (lower-extensionality a lzero ext) λ h →
         Is-[ n ]-extendable-along-[ f ] (λ x → g x ≡ h x)  ↝⟨ Is-extendable-along≃Path-split ext n ⟩
         Path-split n (_∘ f)                                ↝⟨ Path-split-cong ext
                                                                 (Eq.extensionality-isomorphism ext₁)
                                                                 (Eq.extensionality-isomorphism ext₂)
                                                                 (λ eq →
          cong (_∘ f) (apply-ext (Eq.good-ext ext₁) eq)             ≡⟨ Eq.cong-pre-∘-good-ext ext₂ ext₁ _ ⟩∎
          apply-ext (Eq.good-ext ext₂) (eq ∘ f)                     ∎)
                                                                 n ⟩□
         Path-split n (cong (_∘ f))                         □)
  where
  ext₁ = lower-extensionality (a ⊔ p) (a ⊔ b) ext
  ext₂ = lower-extensionality (b ⊔ p) (a ⊔ b) ext

-- In the presence of extensionality Is-∞-extendable-along-[_] can
-- be expressed using Path-split-∞.

Is-∞-extendable-along≃Path-split-∞ :
  {A : Type a} {B : Type b} {P : B → Type p} {f : A → B} →
  Extensionality (a ⊔ b ⊔ p) (a ⊔ b ⊔ p) →
  Is-∞-extendable-along-[ f ] P ≃
  Path-split-∞ (λ (g : ∀ x → P x) → g ∘ f)
Is-∞-extendable-along≃Path-split-∞ ext =
  ∀-cong (lower-extensionality _ lzero ext) $
  Is-extendable-along≃Path-split ext

-- In the presence of extensionality Is-∞-extendable-along-[_] can be
-- expressed using Is-equivalence.

Is-∞-extendable-along≃Is-equivalence :
  {A : Type a} {B : Type b} {P : B → Type p} {f : A → B} →
  Extensionality (a ⊔ b ⊔ p) (a ⊔ b ⊔ p) →
  Is-∞-extendable-along-[ f ] P ≃
  Is-equivalence (λ (g : ∀ x → P x) → g ∘ f)
Is-∞-extendable-along≃Is-equivalence {P = P} {f = f} ext =
  Is-∞-extendable-along-[ f ] P  ↝⟨ Is-∞-extendable-along≃Path-split-∞ ext ⟩
  Path-split-∞ (_∘ f)            ↝⟨ Path-split-∞↔Is-equivalence ext ⟩□
  Is-equivalence (_∘ f)          □

-- The definitions below are not directly based on "Universal
-- properties without function extensionality".

-- If f is an equivalence, then n-extendability along f is
-- contractible (assuming extensionality).

Is-extendable-along-contractible-for-equivalences :
  {A : Type a} {B : Type b} {f : A → B} {P : B → Type p} →
  Extensionality (a ⊔ b ⊔ p) (a ⊔ b ⊔ p) →
  Is-equivalence f →
  ∀ n → Contractible (Is-[ n ]-extendable-along-[ f ] P)
Is-extendable-along-contractible-for-equivalences _ _ zero =
  ↑-closure 0 ⊤-contractible

Is-extendable-along-contractible-for-equivalences
  {a = a} {b = b} {p = p} {f = f} {P = P} ext eq (suc n) =

  ×-closure 0
    (Π-closure (lower-extensionality b lzero ext) 0 λ g →
                                                             $⟨ singleton-contractible _ ⟩
       Contractible (∃ λ h → h ≡ subst P (inv _) ∘ g ∘ f⁻¹)  ↝⟨ H-level-cong _ 0 (lemma g) ⦂ (_ → _) ⟩□
       Contractible (∃ λ h → ∀ x → h (f x) ≡ g x)            □)
    (Π-closure (lower-extensionality a lzero ext) 0 λ _ →
     Π-closure (lower-extensionality a lzero ext) 0 λ _ →
     Is-extendable-along-contractible-for-equivalences ext eq n)
  where
  f⁻¹ = _≃_.from Eq.⟨ _ , eq ⟩
  inv = _≃_.left-inverse-of (inverse Eq.⟨ _ , eq ⟩)

  lemma : ∀ _ → _ ≃ _
  lemma g =
    (∃ λ h → h ≡ subst P (inv _) ∘ g ∘ f⁻¹)  ↔⟨ (∃-cong λ h → inverse $
                                                 ∘from≡↔≡∘to′ (lower-extensionality p (a ⊔ b) ext) (inverse Eq.⟨ _ , eq ⟩)) ⟩
    (∃ λ h → h ∘ f ≡ g)                      ↝⟨ (∃-cong λ _ → inverse $
                                                 Eq.extensionality-isomorphism (lower-extensionality (b ⊔ p) (a ⊔ b) ext)) ⟩□
    (∃ λ h → ∀ x → h (f x) ≡ g x)            □

-- If f is an equivalence, then ∞-extendability along f is
-- contractible (assuming extensionality).

Is-∞-extendable-along-contractible-for-equivalences :
  {A : Type a} {B : Type b} {f : A → B} {P : B → Type p} →
  Extensionality (a ⊔ b ⊔ p) (a ⊔ b ⊔ p) →
  Is-equivalence f →
  Contractible (Is-∞-extendable-along-[ f ] P)
Is-∞-extendable-along-contractible-for-equivalences ext eq =
  Π-closure (lower-extensionality _ lzero ext) 0 λ n →
  Is-extendable-along-contractible-for-equivalences ext eq n
