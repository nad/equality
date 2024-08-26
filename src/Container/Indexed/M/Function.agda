------------------------------------------------------------------------
-- M-types for indexed containers, defined using functions
------------------------------------------------------------------------

-- Based on "Non-wellfounded trees in Homotopy Type Theory" by Ahrens,
-- Capriotti and Spadotti.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Container.Indexed.M.Function
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_)
open import Container.Indexed eq
open import Container.Indexed.Coalgebra eq
open import Equivalence eq as Eq using (_≃_)
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level using (H-level)
open import H-level.Closure eq
import Nat eq as Nat
open import Surjection eq using (_↠_)
open import Tactic.Sigma-cong eq
open import Univalence-axiom eq

private
  variable
    a ℓ o p s             : Level
    A I O                 : Type a
    b ext ext₁ ext₂ i k x : A
    Q                     : A → Type p
    C                     : Container I s p
    n                     : ℕ

------------------------------------------------------------------------
-- Chains

-- Chains (indexed).

Chain : Type i → ∀ ℓ → Type (i ⊔ lsuc ℓ)
Chain {i} I ℓ =
  ∃ λ (P : ℕ → I → Type ℓ) → ∀ n → P (suc n) ⇾ P n

-- Limits of chains.

Limit : {I : Type i} → Chain I ℓ → I → Type ℓ
Limit (P , down) i =
  ∃ λ (f : ∀ n → P n i) →
    ∀ n → down n i (f (suc n)) ≡ f n

-- A kind of dependent universal property for limits.

universal-property-Π :
  {A : Type a} {I : Type i} {g : A → I} →
  (X@(P , down) : Chain I ℓ) →

  ((a : A) → Limit X (g a))
    ≃
  (∃ λ (f : ∀ n (a : A) → P n (g a)) →
     ∀ n a → down n (g a) (f (suc n) a) ≡ f n a)

universal-property-Π {g} X@(P , down) =
  (∀ a → Limit X (g a))                           ↔⟨⟩

  (∀ a → ∃ λ (f : ∀ n → P n (g a)) →
           ∀ n → down n (g a) (f (suc n)) ≡ f n)  ↔⟨ ΠΣ-comm ⟩

  (∃ λ (f : ∀ a n → P n (g a)) →
     ∀ a n → down n (g a) (f a (suc n)) ≡ f a n)  ↝⟨ Σ-cong-refl Π-comm (λ _ → Π-comm) ⟩□

  (∃ λ (f : ∀ n a → P n (g a)) →
     ∀ n a → down n (g a) (f (suc n) a) ≡ f n a)  □

-- A universal property for limits.

universal-property :
  {I : Type i} {P : I → Type p} →
  (X@(Q , down) : Chain I ℓ) →

  (P ⇾ Limit X)
    ↝[ i ∣ p ⊔ ℓ ]
  (∃ λ (f : ∀ n → P ⇾ Q n) →
     ∀ n i x → down n i (f (suc n) i x) ≡ f n i x)

universal-property {P} X@(Q , down) ext =
  (P ⇾ Limit X)                                     ↔⟨⟩

  (∀ i → P i → Limit X i)                           ↝⟨ (∀-cong ext λ _ → from-equivalence $ universal-property-Π X) ⟩

  (∀ i → ∃ λ (f : ∀ n → P i → Q n i) →
           ∀ n x → down n i (f (suc n) x) ≡ f n x)  ↔⟨ ΠΣ-comm ⟩

  (∃ λ (f : ∀ i n → P i → Q n i) →
     ∀ i n x → down n i (f i (suc n) x) ≡ f i n x)  ↝⟨ Σ-cong-refl Π-comm (λ _ → Π-comm) ⟩

  (∃ λ (f : ∀ n i → P i → Q n i) →
     ∀ n i x → down n i (f (suc n) i x) ≡ f n i x)  ↔⟨⟩

  (∃ λ (f : ∀ n → P ⇾ Q n) →
     ∀ n i x → down n i (f (suc n) i x) ≡ f n i x)  □

-- Cones.

Cone : {I : Type i} → (I → Type p) → Chain I ℓ → Type (i ⊔ p ⊔ ℓ)
Cone P (Q , down) =
  ∃ λ (f : ∀ n → P ⇾ Q n) →
    ∀ n → down n ∘⇾ f (suc n) ≡ f n

-- A variant of the non-dependent universal property.

universal-property-≃ :
  {I : Type i} {P : I → Type p} →
  Extensionality (i ⊔ p) (i ⊔ p ⊔ ℓ) →
  (X : Chain I ℓ) →

  (P ⇾ Limit X) ≃ Cone P X

universal-property-≃ {i = iℓ} {p} {ℓ} {P} ext X@(Q , down) =
  with-other-function
    (with-other-inverse equiv from′ from≡from′)
    to′ to≡to′
  where
  ext₃ : Extensionality iℓ (p ⊔ ℓ)
  ext₃ = lower-extensionality (iℓ ⊔ p) (iℓ ⊔ p) ext

  ext₄ : Extensionality p ℓ
  ext₄ = lower-extensionality (iℓ ⊔ p) (iℓ ⊔ p) ext

  to′ : P ⇾ Limit X → Cone P X
  to′ f =
      (λ n i x → f i x .proj₁ n)
    , (λ n →
         apply-ext ext₃ λ i →
         apply-ext ext₄ λ x →
         f i x .proj₂ n)

  from′ : Cone P X → P ⇾ Limit X
  from′ c i x =
      (λ y → c .proj₁ y i x)
    , (λ y → ext⁻¹ (ext⁻¹ (c .proj₂ y) i) x)

  opaque

    equiv : (P ⇾ Limit X) ≃ Cone P X
    equiv =
      P ⇾ Limit X                                       ↝⟨ universal-property X (lower-extensionality p iℓ ext) ⟩

      (∃ λ (f : ∀ n → P ⇾ Q n) →
         ∀ n i x → down n i (f (suc n) i x) ≡ f n i x)  ↝⟨ (∃-cong λ _ → ∀-cong (lower-extensionality _ lzero ext) λ _ →
                                                            ∀-cong (lower-extensionality p iℓ ext) λ _ →
                                                            Eq.extensionality-isomorphism ext₄) ⟩
      (∃ λ (f : ∀ n → P ⇾ Q n) →
         ∀ n i → down n i ∘ f (suc n) i ≡ f n i)        ↝⟨ (∃-cong λ _ → ∀-cong (lower-extensionality _ lzero ext) λ _ →
                                                            Eq.extensionality-isomorphism ext₃) ⟩
      (∃ λ (f : ∀ n → P ⇾ Q n) →
         ∀ n → down n ∘⇾ f (suc n) ≡ f n)               ↔⟨⟩

      Cone P X                                          □

    to≡to′ : ∀ f → _≃_.to equiv f ≡ to′ f
    to≡to′ _ = refl _

    from≡from′ : ∀ c → _≃_.from equiv c ≡ from′ c
    from≡from′ _ = refl _

-- Shifts a chain one step.

shift : Chain I ℓ → Chain I ℓ
shift = Σ-map (_∘ suc) (_∘ suc)

-- Shifting does not affect the limit (assuming extensionality).
--
-- This is a variant of Lemma 12 in "Non-wellfounded trees in Homotopy
-- Type Theory".

Limit-shift :
  ∀ (X : Chain I ℓ) {i} →
  Limit (shift X) i ↝[ lzero ∣ ℓ ] Limit X i
Limit-shift {ℓ} X@(P , down) {i} ext =
  Limit (shift X) i                                ↔⟨⟩

  (∃ λ (p : ∀ n → P (suc n) i) →
     ∀ n → down (suc n) i (p (suc n)) ≡ p n)       ↔⟨ (∃-cong λ _ → inverse $
                                                       drop-⊤-left-× λ _ →
                                                       _⇔_.to contractible⇔↔⊤ $
                                                       other-singleton-contractible _) ⟩
  (∃ λ (p : ∀ n → P (suc n) i) →
     (∃ λ (p₀ : P 0 i) → down 0 i (p 0) ≡ p₀) ×
     ∀ n → down (suc n) i (p (suc n)) ≡ p n)       ↔⟨ Σ-assoc F.∘
                                                      ∃-comm F.∘
                                                      (∃-cong λ _ → inverse Σ-assoc) ⟩
  (∃ λ ((p₀ , p) : P 0 i × (∀ n → P (suc n) i)) →
     down 0 i (p 0) ≡ p₀ ×
     ∀ n → down (suc n) i (p (suc n)) ≡ p n)       ↝⟨ inverse-ext?
                                                        (generalise-ext?
                                                           (_↠_.logical-equivalence lemma₂-↠)
                                                           (λ ext →
                                                                _↠_.right-inverse-of lemma₂-↠
                                                              , _↔_.left-inverse-of (lemma₂-↔ ext)))
                                                        ext ⟩
  (∃ λ (p : ∀ n → P n i) →
     ∀ n → down n i (p (suc n)) ≡ p n)             ↔⟨⟩

  Limit X i                                        □
  where
  lemma₁-↠ :
    {P : ℕ → Type ℓ} →
    (∀ n → P n) ↠ (P 0 × (∀ n → P (suc n)))
  lemma₁-↠ ._↠_.logical-equivalence ._⇔_.to   = λ p → p 0 , p ∘ suc
  lemma₁-↠ ._↠_.logical-equivalence ._⇔_.from = uncurry ℕ-case
  lemma₁-↠ ._↠_.right-inverse-of              = refl

  lemma₁-↔ :
    {P : ℕ → Type ℓ} →
    Extensionality lzero ℓ →
    (∀ n → P n) ↔ (P 0 × (∀ n → P (suc n)))
  lemma₁-↔ _   ._↔_.surjection      = lemma₁-↠
  lemma₁-↔ ext ._↔_.left-inverse-of = λ f →
    apply-ext ext $ ℕ-case (refl _) λ _ → refl _

  lemma₂-↠ : _ ↠ _
  lemma₂-↠ =
    (∃ λ (p : ∀ n → P n i) →
       ∀ n → down n i (p (suc n)) ≡ p n)              ↝⟨ (∃-cong λ _ → lemma₁-↠) ⟩

    (∃ λ (p : ∀ n → P n i) →
       down 0 i (p 1) ≡ p 0 ×
       ∀ n → down (suc n) i (p (2 + n)) ≡ p (1 + n))  ↝⟨ Σ-cong-id-↠ lemma₁-↠ ⟩□

    (∃ λ ((p₀ , p) : P 0 i × (∀ n → P (suc n) i)) →
       down 0 i (p 0) ≡ p₀ ×
       ∀ n → down (suc n) i (p (suc n)) ≡ p n)        □

  lemma₂-↔ : Extensionality lzero ℓ → _ ↔ _
  lemma₂-↔ ext =
    (∃ λ (p : ∀ n → P n i) →
       ∀ n → down n i (p (suc n)) ≡ p n)              ↝⟨ (∃-cong λ _ → lemma₁-↔ ext) ⟩

    (∃ λ (p : ∀ n → P n i) →
       down 0 i (p 1) ≡ p 0 ×
       ∀ n → down (suc n) i (p (2 + n)) ≡ p (1 + n))  ↝⟨ Σ-cong-id (Eq.↔⇒≃ $ lemma₁-↔ ext) ⟩□

    (∃ λ ((p₀ , p) : P 0 i × (∀ n → P (suc n) i)) →
       down 0 i (p 0) ≡ p₀ ×
       ∀ n → down (suc n) i (p (suc n)) ≡ p n)        □

------------------------------------------------------------------------
-- Cochains

-- Cochains (non-indexed).

Cochain : ∀ ℓ → Type (lsuc ℓ)
Cochain ℓ =
  ∃ λ (P : ℕ → Type ℓ) → ∀ n → P n → P (suc n)

-- There is a pointwise split surjection from the "limit" of a cochain
-- to the first element.

cochain-limit-↠ :
  ((P , up) : Cochain ℓ) →

  (∃ λ (p : ∀ n → P n) → ∀ n → p (suc n) ≡ up n (p n))
    ↠
  P 0
cochain-limit-↠ (_ , up) = λ where
  ._↠_.logical-equivalence ._⇔_.to   (p , _)     → p 0
  ._↠_.logical-equivalence ._⇔_.from p₀ .proj₁   → ℕ-rec p₀ up
  ._↠_.logical-equivalence ._⇔_.from p₀ .proj₂ _ → refl _
  ._↠_.right-inverse-of                          → refl

-- The "limit" of a cochain is pointwise equivalent to the first
-- element (assuming extensionality).
--
-- This is a variant of Lemma 11 in "Non-wellfounded trees in Homotopy
-- Type Theory".

cochain-limit :
  ((P , up) : Cochain ℓ) →

  (∃ λ (p : ∀ n → P n) → ∀ n → p (suc n) ≡ up n (p n))
    ↝[ lzero ∣ ℓ ]
  P 0
cochain-limit X@(_ , up) ext =
  generalise-ext?
  (_↠_.logical-equivalence cl)
  (λ ext → _↠_.right-inverse-of cl , from∘to ext)
  ext
  where
  cl = cochain-limit-↠ X

  open _↠_ cl

  from₁∘to : ∀ l n → proj₁ (from (to l)) n ≡ proj₁ l n
  from₁∘to _         zero    = refl _
  from₁∘to l@(p , q) (suc n) =
    up n (proj₁ (from (to l)) n)  ≡⟨ cong (up n) $ from₁∘to l n ⟩
    up n (p n)                    ≡⟨ sym $ q n ⟩∎
    p (suc n)                     ∎

  from∘to :
    Extensionality lzero _ →
    ∀ l → from (to l) ≡ l
  from∘to ext l@(p , q) = Σ-≡,≡→≡
    (apply-ext ext (from₁∘to l))
    (apply-ext ext λ n →

     subst (λ p → ∀ n → p (suc n) ≡ up n (p n))
       (apply-ext ext (from₁∘to l))
       (λ _ → refl _) n                                            ≡⟨ sym $ push-subst-application _ _ ⟩

     subst (λ p → p (suc n) ≡ up n (p n))
       (apply-ext ext (from₁∘to l))
       (refl _)                                                    ≡⟨ trans subst-in-terms-of-trans-and-cong $
                                                                      cong (trans _) $
                                                                      trans-reflˡ _ ⟩
     trans (sym $ cong (_$ suc n) (apply-ext ext (from₁∘to l)))
       (cong (λ p → up n (p n)) (apply-ext ext (from₁∘to l)))      ≡⟨ cong₂ trans
                                                                        (cong sym $ cong-ext ext)
                                                                        (trans (sym $ cong-∘ _ _ _) $
                                                                         cong (cong _) $ cong-ext ext) ⟩
     trans (sym $ from₁∘to l (suc n))
       (cong (up n) $ from₁∘to l n)                                ≡⟨⟩

     trans (sym $ trans (cong (up n) $ from₁∘to l n) (sym $ q n))
       (cong (up n) $ from₁∘to l n)                                ≡⟨ cong (flip trans _) $
                                                                      trans (sym-trans _ _) $
                                                                      cong (flip trans _) $
                                                                      sym-sym _ ⟩
     trans (trans (q n) (sym $ cong (up n) $ from₁∘to l n))
       (cong (up n) $ from₁∘to l n)                                ≡⟨ trans-[trans-sym]- _ _ ⟩∎

     q n                                                           ∎)

-- A variant of cochain-limit-↠ for simple cochains.

simple-cochain-limit-↠ :
  (∃ λ (f : ℕ → A) → ∀ n → f (suc n) ≡ f n) ↠ A
simple-cochain-limit-↠ = λ where
  ._↠_.logical-equivalence ._⇔_.to   (f , _)     → f 0
  ._↠_.logical-equivalence ._⇔_.from f₀ .proj₁ _ → f₀
  ._↠_.logical-equivalence ._⇔_.from f₀ .proj₂ _ → refl _
  ._↠_.right-inverse-of                          → refl

-- The first projection of the right-to-left direction of
-- simple-cochain-limit-↠ computes in a certain way.

_ : proj₁ (_↠_.from simple-cochain-limit-↠ x) n ≡ x
_ = refl _

-- A variant of cochain-limit for simple cochains.

simple-cochain-limit :
  {A : Type a} →
  (∃ λ (f : ℕ → A) → ∀ n → f (suc n) ≡ f n) ↝[ lzero ∣ a ] A
simple-cochain-limit =
  generalise-ext?
    (_↠_.logical-equivalence scl)
    (λ ext → _↠_.right-inverse-of scl , from∘to ext)
  where
  scl = simple-cochain-limit-↠

  open _↠_ scl

  from₁∘to : ∀ l n → proj₁ (from (to l)) n ≡ proj₁ l n
  from₁∘to _         zero    = refl _
  from₁∘to l@(f , p) (suc n) =
    proj₁ (from (to l)) n  ≡⟨ from₁∘to l n ⟩
    f n                    ≡⟨ sym $ p n ⟩∎
    f (suc n)              ∎

  from∘to :
    Extensionality lzero _ →
    ∀ l → from (to l) ≡ l
  from∘to ext l@(f , p) = Σ-≡,≡→≡
    (apply-ext ext (from₁∘to l))
    (apply-ext ext λ n →

     subst (λ f → ∀ n → f (suc n) ≡ f n)
       (apply-ext ext (from₁∘to l))
       (λ _ → refl _) n                                             ≡⟨ sym $ push-subst-application _ _ ⟩

     subst (λ f → f (suc n) ≡ f n)
       (apply-ext ext (from₁∘to l))
       (refl _)                                                     ≡⟨ trans subst-in-terms-of-trans-and-cong $
                                                                       cong (trans _) $
                                                                       trans-reflˡ _ ⟩
     trans (sym $ cong (_$ suc n) (apply-ext ext (from₁∘to l)))
       (cong (_$ n) (apply-ext ext (from₁∘to l)))                   ≡⟨ cong₂ trans
                                                                         (cong sym $ cong-ext ext)
                                                                         (cong-ext ext) ⟩
     trans (sym $ from₁∘to l (suc n)) (from₁∘to l n)                ≡⟨⟩

     trans (sym $ trans (from₁∘to l n) (sym $ p n)) (from₁∘to l n)  ≡⟨ cong (flip trans _) $
                                                                       trans (sym-trans _ _) $
                                                                       cong (flip trans _) $
                                                                       sym-sym _ ⟩

     trans (trans (p n) (sym $ from₁∘to l n)) (from₁∘to l n)        ≡⟨ trans-[trans-sym]- _ _ ⟩∎

     p n                                                            ∎)

-- The first projection of the right-to-left direction of
-- simple-cochain-limit computes in a certain way (at least when "k"
-- has certain values).

_ : proj₁ (_⇔_.from (simple-cochain-limit _) x) n ≡ x
_ = refl _

_ : proj₁ (_≃_.from (simple-cochain-limit ext) x) n ≡ x
_ = refl _

------------------------------------------------------------------------
-- Chains and containers

-- Containers can be applied to chains.

Container-chain :
  {I : Type i} {O : Type o} →
  Container₂ I O s p → Chain I ℓ → Chain O (s ⊔ p ⊔ ℓ)
Container-chain C = Σ-map (⟦ C ⟧ ∘_) (map C ∘_)

opaque

  -- A more opaque variant of ⟦⟧-Limit≃ (which is defined below).

  ⟦⟧-Limit≃-opaque :
    {I : Type i} {O : Type o} →
    Extensionality p (s ⊔ p ⊔ ℓ) →
    (C : Container₂ I O s p) (X : Chain I ℓ) {o : O} →

    ⟦ C ⟧ (Limit X) o ≃ Limit (Container-chain C X) o
  ⟦⟧-Limit≃-opaque {i} {p} {s = sℓ} {ℓ} ext C X@(Q , down) {o} =
    ⟦ C ⟧ (Limit X) o                                            ↔⟨⟩

    (∃ λ (s : Shape C o) →
       (p : Position C s) → Limit X (index C p))                 ↝⟨ (∃-cong λ _ →
                                                                     universal-property-Π X) ⟩
    (∃ λ (s : Shape C o) →
     ∃ λ (f : ∀ n (p : Position C s) → Q n (index C p)) →
       ∀ n p → down n (index C p) (f (suc n) p) ≡ f n p)         ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                     ∀-cong (lower-extensionality p r ext) λ _ →
                                                                     Eq.extensionality-isomorphism (lower-extensionality p r ext)) ⟩
    (∃ λ (s : Shape C o) →
     ∃ λ (f : ∀ n (p : Position C s) → Q n (index C p)) →
       ∀ n → down n _ ∘ f (suc n) ≡ f n)                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong (lower-extensionality p r ext) λ _ →
                                                                     ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                     subst-refl _ _) ⟩
    (∃ λ (s : Shape C o) →
     ∃ λ (f : ∀ n (p : Position C s) → Q n (index C p)) →
       ∀ n → subst (λ s → (p : Position C s) → Q n (index C p))
               (refl _) (down n _ ∘ f (suc n)) ≡
             f n)                                                ↝⟨ (Σ-cong (inverse $
                                                                             simple-cochain-limit {k = equivalence}
                                                                               (lower-extensionality p r ext)) λ _ →
                                                                     F.id) ⟩
    (∃ λ ((s , eq) : ∃ λ (s : ℕ → Shape C o) →
                       ∀ n → s (suc n) ≡ s n) →
     ∃ λ (f : ∀ n (p : Position C (s n)) → Q n (index C p)) →
       ∀ n → subst (λ s → (p : Position C s) → Q n (index C p))
               (eq n) (down n _ ∘ f (suc n)) ≡
             f n)                                                ↔⟨ (∃-cong λ _ →
                                                                     (∃-cong λ _ →
                                                                      (∀-cong (lower-extensionality p r ext) λ _ →
                                                                       Bijection.Σ-≡,≡↔≡) F.∘
                                                                      inverse ΠΣ-comm) F.∘
                                                                     ∃-comm) F.∘
                                                                    inverse Σ-assoc ⟩
    (∃ λ (s : ℕ → Shape C o) →
     ∃ λ (f : ∀ n (p : Position C (s n)) → Q n (index C p)) →
       ∀ n → (s (suc n) , down n _ ∘ f (suc n)) ≡ (s n , f n))   ↔⟨⟩

    (∃ λ (s : ℕ → Shape C o) →
     ∃ λ (f : ∀ n (p : Position C (s n)) → Q n (index C p)) →
       ∀ n → map C (down n) o (s (suc n) , f (suc n)) ≡
             (s n , f n))                                        ↝⟨ (inverse $ Σ-cong-id (Eq.↔⇒≃ ΠΣ-comm)) F.∘
                                                                    Eq.↔⇒≃ Σ-assoc ⟩
    (∃ λ (f : ∀ n → ∃ λ (s : Shape C o) →
                      (p : Position C s) → Q n (index C p)) →
       ∀ n → map C (down n) o (f (suc n)) ≡ f n)                 ↔⟨⟩

    Limit (Container-chain C X) o                                □
    where
    r : Level
    r = sℓ ⊔ p ⊔ ℓ

-- The polynomial functor (for a container C) of the limit of a chain
-- is pointwise equivalent to the limit of C applied to the chain
-- (assuming extensionality).
--
-- This is a variant of Lemma 13 in "Non-wellfounded trees in Homotopy
-- Type Theory".

⟦⟧-Limit≃ :
  {I : Type i} {O : Type o} →
  Extensionality p (s ⊔ p ⊔ ℓ) →
  (C : Container₂ I O s p) (X : Chain I ℓ) {o : O} →

  ⟦ C ⟧ (Limit X) o ≃ Limit (Container-chain C X) o
⟦⟧-Limit≃ {i} {p} {s = sℓ} {ℓ} ext C X@(Q , down) {o} =
  Eq.with-other-function equiv to′ to≡to′
  where
  ext′ = apply-ext (lower-extensionality p (sℓ ⊔ p ⊔ ℓ) ext)

  to′ : ⟦ C ⟧ (Limit X) o → Limit (Container-chain C X) o
  to′ (s , f) =
      (λ n → s , λ x → f x .proj₁ n)
    , (λ n → cong (s ,_) (ext′ λ x → f x .proj₂ n))

  equiv : ⟦ C ⟧ (Limit X) o ≃ Limit (Container-chain C X) o
  equiv =
    ⟦⟧-Limit≃-opaque ext C X

  opaque
    unfolding ⟦⟧-Limit≃-opaque

    to≡to′ : ∀ x → _≃_.to equiv x ≡ to′ x
    to≡to′ (s , f) =
      cong (_,_ λ n → s , λ x → f x .proj₁ n)
        (apply-ext (lower-extensionality p (sℓ ⊔ p ⊔ ℓ) ext) λ n →

         Σ-≡,≡→≡
           (refl s)
           (≡⇒→
              (cong (_≡ λ y → f y .proj₁ n)
                 (sym
                    (subst-refl
                       (λ s → (p : Position C s) → Q n (index C p))
                       _)))
              (ext′ λ x → f x .proj₂ n))                                ≡⟨ Σ-≡,≡→≡-reflˡ _ ⟩

         cong (s ,_)
           (trans
              (sym (subst-refl _ _))
              (≡⇒→
                 (cong
                    (_≡ λ y → f y .proj₁ n)
                    (sym
                       (subst-refl
                          (λ s → (p : Position C s) → Q n (index C p))
                          _)))
                 (ext′ λ x → f x .proj₂ n)))                            ≡⟨ cong (cong _) $ cong (trans _) $ sym $
                                                                           subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
         cong (s ,_)
           (trans
              (sym (subst-refl _ _))
              (subst (_≡ λ y → f y .proj₁ n)
                 (sym
                    (subst-refl
                       (λ s → (p : Position C s) → Q n (index C p))
                       _))
                 (ext′ λ x → f x .proj₂ n)))                            ≡⟨ cong (cong _) $ cong (trans _) $
                                                                           subst-trans _ ⟩
         cong (s ,_)
           (trans
              (sym (subst-refl _ _))
              (trans
                 (subst-refl
                    (λ s → (p : Position C s) → Q n (index C p)) _)
                 (ext′ λ x → f x .proj₂ n)))                            ≡⟨ cong (cong _) $
                                                                           trans-sym-[trans] _ _ ⟩∎
         cong (s ,_) (ext′ λ x → f x .proj₂ n)                          ∎)

------------------------------------------------------------------------
-- M-types

private

  -- Up-to C n is the n-fold application of ⟦ C ⟧ to something
  -- trivial.

  Up-to : {I : Type i} → Container I s p → ℕ → I → Type (i ⊔ s ⊔ p)
  Up-to C zero    = λ _ → ↑ _ ⊤
  Up-to C (suc n) = ⟦ C ⟧ (Up-to C n)

  -- Up-to C is downwards closed.

  down : ∀ n → Up-to C (suc n) ⇾ Up-to C n
  down zero    = _
  down (suc n) = map _ (down n)

-- One can combine Up-to and down into a chain.

M-chain : {I : Type i} → Container I s p → Chain I (i ⊔ s ⊔ p)
M-chain C = Up-to C , down

-- An M-type for a given container.

M : {I : Type i} → Container I s p → I → Type (i ⊔ s ⊔ p)
M C = Limit (M-chain C)

-- M C is, in a certain sense, a fixpoint of ⟦ C ⟧ (assuming
-- extensionality).

M-fixpoint :
  Block "M-fixpoint" →
  {I : Type i} →
  Extensionality p (i ⊔ s ⊔ p) →
  {C : Container I s p} {i : I} →
  ⟦ C ⟧ (M C) i ≃ M C i
M-fixpoint ⊠ ext {C} {i} =
  ⟦ C ⟧ (M C) i                            ↔⟨⟩
  ⟦ C ⟧ (Limit (M-chain C)) i              ↝⟨ ⟦⟧-Limit≃ ext C (M-chain C) ⟩
  Limit (Container-chain C (M-chain C)) i  ↔⟨⟩
  Limit (shift (M-chain C)) i              ↝⟨ Limit-shift (M-chain C) (lower-extensionality _ lzero ext) ⟩
  Limit (M-chain C) i                      ↔⟨⟩
  M C i                                    □

-- One direction of the fixpoint.

out-M :
  Block "M-fixpoint" →
  {I : Type i} {C : Container I s p} →
  Extensionality p (i ⊔ s ⊔ p) →
  M C ⇾ ⟦ C ⟧ (M C)
out-M b ext _ = _≃_.from (M-fixpoint b ext)

-- The other direction of the fixpoint.

in-M :
  Block "M-fixpoint" →
  {I : Type i} {C : Container I s p} →
  Extensionality p (i ⊔ s ⊔ p) →
  ⟦ C ⟧ (M C) ⇾ M C
in-M b ext _ = _≃_.to (M-fixpoint b ext)

-- A "computation" rule for in-M.

in-M≡ :
  (b : Block "M-fixpoint")
  {I : Type i}
  (ext : Extensionality p (i ⊔ s ⊔ p)) →
  let ext′ = apply-ext $ lower-extensionality p (i ⊔ s ⊔ p) ext in
  {C : Container I s p} {i : I}
  (x@(s , f) : ⟦ C ⟧ (M C) i) →
  in-M b ext _ x ≡
  ( ℕ-case _ (λ n → s , λ p → proj₁ (f p) n)
  , ℕ-case (refl _) (λ n → cong (s ,_) $ ext′ λ p → proj₂ (f p) n)
  )
in-M≡ ⊠ _ _ = refl _

-- A coalgebra defined using M and out-M.

M-coalgebra :
  Block "M-fixpoint" →
  {I : Type i} →
  Extensionality p (i ⊔ s ⊔ p) →
  (C : Container I s p) → Coalgebra C
M-coalgebra b ext C = M C , out-M b ext

-- Definitions used to implement unfold.

private
 module Unfold
  ((P , f) : Coalgebra C)
  where
  up : ∀ n → P ⇾ Up-to C n
  up zero    = _
  up (suc n) = map C (up n) ∘⇾ f

  ok : ∀ n → down n ∘⇾ up (suc n) ≡ up n
  ok zero    = refl _
  ok (suc n) =
    map C (down n ∘⇾ up (suc n)) ∘⇾ f  ≡⟨ cong (λ g → map C g ∘⇾ f) $ ok n ⟩∎
    map C (up n) ∘⇾ f                  ∎

-- A direct implementation of an unfold operation.

unfold :
  ((P , _) : Coalgebra C) →
  P ⇾ M C
unfold Y i p =
    (λ n → up n i p)
  , (λ n → cong (λ f → f i p) (ok n))
  where
  open Unfold Y

-- Definitions used to implement M-final.

private
 module M-final
  (b : Block "M-fixpoint")
  {I : Type i} {C : Container I s p}
  (ext : Extensionality p (i ⊔ s ⊔ p))
  (ext′ : Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p))
  (Y@(P , f) : Coalgebra C)
  where

  step : P ⇾ Q → P ⇾ ⟦ C ⟧ Q
  step h = map C h ∘⇾ f

  univ : Cone P (M-chain C) → P ⇾ M C
  univ = _≃_.from (universal-property-≃ ext′ (M-chain C))

  steps₁ : (∀ n → P ⇾ Up-to C n) → (∀ n → P ⇾ Up-to C n)
  steps₁ g n i p =
    ℕ-case
      {P = λ n → Up-to C n i}
      _
      (λ n → step (g n) i p)
      n

  Eq : (∀ n → P ⇾ Up-to C n) → Type (i ⊔ s ⊔ p)
  Eq g = ∀ n → down n ∘⇾ g (suc n) ≡ g n

  steps₂ : {g : ∀ n → P ⇾ Up-to C n} → Eq g → Eq (steps₁ g)
  steps₂     p zero    = refl _
  steps₂ {g} p (suc n) =
    down (suc n) ∘⇾ steps₁ g (suc (suc n))  ≡⟨⟩
    step (down n ∘⇾ g (suc n))              ≡⟨ cong step (p n) ⟩∎
    step (g n)                              ∎

  steps : Cone P (M-chain C) → Cone P (M-chain C)
  steps = Σ-map steps₁ steps₂

  ext-i : Extensionality i (i ⊔ s ⊔ p)
  ext-i = lower-extensionality (s ⊔ p) lzero ext′

  ext₀ : Extensionality lzero (i ⊔ s ⊔ p)
  ext₀ = lower-extensionality _ lzero ext

  ext₀′ :
    {A : Type} {P : A → Type (i ⊔ s ⊔ p)} →
    Function-extensionality′ A P
  ext₀′ = apply-ext ext₀

  ≡univ-steps : ∀ c → in-M b ext ∘⇾ step (univ c) ≡ univ (steps c)
  ≡univ-steps c@(g , eq) = apply-ext ext-i λ i → apply-ext ext′ λ p →
    in-M b ext i (step (univ c) i p)                                  ≡⟨ in-M≡ b ext (step (univ c) i p) ⟩

    ( (λ n → steps₁ g n i p)
    , ℕ-case (refl _)
        (λ n →
           cong (proj₁ (f i p) ,_)
             (ext‴ λ p′ →
              ext⁻¹ (ext⁻¹ (eq n) (index C p′)) (proj₂ (f i p) p′)))
    )                                                                 ≡⟨ cong ((λ n → steps₁ g n i p) ,_) $
                                                                         ext₀′ $ ℕ-case
                                                                           (
        refl _                                                              ≡⟨ sym $ ext⁻¹-refl {x = p} _ ⟩
        ext⁻¹ (refl _) p                                                    ≡⟨ cong (flip ext⁻¹ p) $ sym $ ext⁻¹-refl _ ⟩
        ext⁻¹ (ext⁻¹ {P = λ x → P x → ↑ _ ⊤} (refl _) i) p                  ≡⟨⟩
        ext⁻¹ (ext⁻¹ (steps₂ eq zero) i) p                                  ∎)
                                                                           (λ n →
        cong (proj₁ (f i p) ,_)
          (ext‴ λ p′ →
           ext⁻¹ (ext⁻¹ (eq n) (index C p′)) (proj₂ (f i p) p′))              ≡⟨ elim₁
                                                                                   (λ eq →
                                                                                      cong (proj₁ (f i p) ,_)
                                                                                        (ext‴ λ p′ →
                                                                                         ext⁻¹ (ext⁻¹ eq (index C p′)) (proj₂ (f i p) p′)) ≡
                                                                                      ext⁻¹ (ext⁻¹ (cong (λ g → map C g ∘⇾ f) eq) i) p)
                                                                                   (
            cong (proj₁ (f i p) ,_)
              (ext‴ λ p′ →
               ext⁻¹ (ext⁻¹ (refl (g n)) (index C p′))
                 (proj₂ (f i p) p′))                                                ≡⟨ (cong (cong _) $
                                                                                        cong ext‴ $ ext‴ λ _ →
                                                                                        trans (cong (flip ext⁻¹ _) $
                                                                                               ext⁻¹-refl _) $
                                                                                        ext⁻¹-refl _) ⟩

            cong (proj₁ (f i p) ,_) (ext‴ λ _ → refl _)                            ≡⟨ trans (cong (cong _) $
                                                                                             ext-refl ext″) $
                                                                                       cong-refl _ ⟩

            refl _                                                                  ≡⟨ sym $
                                                                                       trans (cong (flip ext⁻¹ _) $
                                                                                              trans (cong (flip ext⁻¹ _) $
                                                                                                     cong-refl _) $
                                                                                              ext⁻¹-refl _) $
                                                                                       ext⁻¹-refl _ ⟩∎
            ext⁻¹ (ext⁻¹ (cong step (refl (g n))) i) p                              ∎)
                                                                                   (eq n) ⟩
        ext⁻¹ (ext⁻¹ (cong step (eq n)) i) p                                  ∎) ⟩

    ( (λ n → steps₁ g n i p)
    , (λ n → ext⁻¹ (ext⁻¹ (steps₂ eq n) i) p)
    )                                                                 ≡⟨⟩

    univ (steps c) i p                                                ∎
    where
    ext″ = lower-extensionality p (i ⊔ s ⊔ p) ext
    ext‴ = apply-ext ext″

  contr : Contractible (P ⇾ Up-to C 0)
  contr =
    Π-closure ext-i 0 λ _ →
    Π-closure ext′ 0 λ _ →
    ↑-closure 0 ⊤-contractible

  steps₁-fixpoint≃ :
    {g : ∀ n → P ⇾ Up-to C n} →
    (g ≡ steps₁ g) ≃ (∀ n → g (suc n) ≡ step (g n))
  steps₁-fixpoint≃ {g} =
    g ≡ steps₁ g                                             ↝⟨ inverse $ Eq.extensionality-isomorphism ext₀ ⟩

    (∀ n → g n ≡ steps₁ g n)                                 ↝⟨ Πℕ≃ ext₀ ⟩

    g 0 ≡ steps₁ g 0 × (∀ n → g (suc n) ≡ steps₁ g (suc n))  ↔⟨⟩

    (λ _ _ → lift tt) ≡ (λ _ _ → lift tt) ×
    (∀ n → g (suc n) ≡ step (g n))                           ↔⟨ (drop-⊤-left-× λ _ →
                                                                 _⇔_.to contractible⇔↔⊤ $
                                                                 H-level.⇒≡ 0 contr) ⟩□
    (∀ n → g (suc n) ≡ step (g n))                           □

  cochain₁ : Cochain (i ⊔ s ⊔ p)
  cochain₁ = (λ n → P ⇾ Up-to C n)
           , (λ _ → step)

  cl₁← : P ⇾ Up-to C 0 → ∀ n → P ⇾ Up-to C n
  cl₁← = proj₁ ∘ _↠_.from (cochain-limit-↠ cochain₁)

  ⇾↔⊤ : (P ⇾ Up-to C 0) ↔ ⊤
  ⇾↔⊤ = _⇔_.to contractible⇔↔⊤ contr

  g₀ : P ⇾ Up-to C 0
  g₀ = _↔_.from ⇾↔⊤ _

  steps₁-fixpoint : ∀ n → cl₁← g₀ n ≡ steps₁ (cl₁← g₀) n
  steps₁-fixpoint = ℕ-case (refl _) (λ _ → refl _)

  steps₁-fixpoint-lemma :
    {p : Eq (cl₁← g₀)} →
    subst Eq (_≃_.from steps₁-fixpoint≃ (λ _ → refl _)) p n ≡
    trans (p n) (steps₁-fixpoint n)
  steps₁-fixpoint-lemma {n} {p} =
    subst Eq (_≃_.from steps₁-fixpoint≃ (λ _ → refl _)) p n    ≡⟨⟩

    subst Eq (ext₀′ (ℕ-case _ (λ _ → refl _))) p n             ≡⟨ cong (λ eq → subst Eq eq p n) $
                                                                  cong ext₀′ $
                                                                  cong (flip ℕ-case _) $
                                                                  H-level.mono (Nat.zero≤ 2) contr _ _ ⟩

    subst Eq (ext₀′ steps₁-fixpoint) p n                       ≡⟨ sym $ push-subst-application _ _ ⟩

    subst (λ g → down n ∘⇾ g (suc n) ≡ g n)
      (ext₀′ steps₁-fixpoint) (p n)                            ≡⟨ trans subst-in-terms-of-trans-and-cong $
                                                                  cong (flip trans _) $ cong sym $ sym $
                                                                  cong-∘ _ _ _ ⟩
    trans (sym (cong (down n ∘⇾_)
                  (cong (_$ suc n) (ext₀′ steps₁-fixpoint))))
      (trans (p n) (cong (_$ n) (ext₀′ steps₁-fixpoint)))      ≡⟨ cong₂ (λ eq₁ eq₂ → trans (sym (cong (down n ∘⇾_) eq₁)) (trans _ eq₂))
                                                                    (cong-ext ext₀)
                                                                    (cong-ext ext₀) ⟩
    trans (sym (cong (down n ∘⇾_) (steps₁-fixpoint (suc n))))
      (trans (p n) (steps₁-fixpoint n))                        ≡⟨⟩

    trans (sym (cong (down n ∘⇾_) (refl _)))
      (trans (p n) (steps₁-fixpoint n))                        ≡⟨ trans (cong (flip trans _) $
                                                                         trans (cong sym $ cong-refl _)
                                                                         sym-refl) $
                                                                  trans-reflˡ _ ⟩∎
    trans (p n) (steps₁-fixpoint n)                            ∎

  cochain₂ : Cochain (i ⊔ s ⊔ p)
  cochain₂ = (λ n → down n ∘⇾ step (cl₁← g₀ n) ≡ cl₁← g₀ n)
           , (λ _ → cong step)

  equiv : Block "equiv" → (Y ⇨ M-coalgebra b ext C) ≃ ⊤
  equiv ⊠ =
    Y ⇨ M-coalgebra b ext C                                             ↔⟨⟩

    (∃ λ (h : P ⇾ M C) → out-M b ext ∘⇾ h ≡ step h)                     ↝⟨ (∃-cong λ _ → inverse $
                                                                            Eq.≃-≡ $ ∀-cong ext-i λ _ → ∀-cong ext′ λ _ →
                                                                            M-fixpoint b ext) ⟩
    (∃ λ (h : P ⇾ M C) →
       (in-M b ext ∘⇾ out-M b ext) ∘⇾ h ≡ in-M b ext ∘⇾ step h)         ↝⟨ (∃-cong λ h → ≡⇒↝ _ $ cong (_≡ in-M b ext ∘⇾ step h) $
                                                                            apply-ext ext-i λ _ → apply-ext ext′ λ _ →
                                                                            _≃_.right-inverse-of (M-fixpoint b ext) _) ⟩

    (∃ λ (h : P ⇾ M C) → h ≡ in-M b ext ∘⇾ step h)                      ↝⟨ (inverse $
                                                                            Σ-cong (inverse $ universal-property-≃ ext′ (M-chain C)) λ _ →
                                                                            F.id) ⟩
    (∃ λ (c : Cone P (M-chain C)) →
       univ c ≡ in-M b ext ∘⇾ step (univ c))                            ↝⟨ (∃-cong λ c → ≡⇒↝ _ $ cong (univ c ≡_) $ ≡univ-steps c) ⟩

    (∃ λ (c : Cone P (M-chain C)) → univ c ≡ univ (steps c))            ↝⟨ (∃-cong λ _ →
                                                                            Eq.≃-≡ $ inverse $ universal-property-≃ ext′ (M-chain C)) ⟩

    (∃ λ (c : Cone P (M-chain C)) → c ≡ steps c)                        ↔⟨ (∃-cong λ _ → inverse
                                                                            Bijection.Σ-≡,≡↔≡) ⟩
    (∃ λ ((g , p) : Cone P (M-chain C)) →
     ∃ λ (q : g ≡ steps₁ g) → subst Eq q p ≡ steps₂ p)                  ↔⟨ Σ-assoc F.∘
                                                                           (∃-cong λ _ → ∃-comm) F.∘
                                                                           inverse Σ-assoc ⟩
    (∃ λ ((g , q) : ∃ λ (g : ∀ n → P ⇾ Up-to C n) → g ≡ steps₁ g) →
     ∃ λ (p : Eq g) → subst Eq q p ≡ steps₂ p)                          ↝⟨ (inverse $
                                                                            Σ-cong (inverse $
                                                                                    ∃-cong λ _ →
                                                                                    steps₁-fixpoint≃) λ _ →
                                                                            F.id) ⟩
    (∃ λ ((g , q) : ∃ λ (g : ∀ n → P ⇾ Up-to C n) →
                      ∀ n → g (suc n) ≡ step (g n)) →
     ∃ λ (p : Eq g) →
       subst Eq (_≃_.from steps₁-fixpoint≃ q) p ≡ steps₂ p)             ↝⟨ (inverse $
                                                                            Σ-cong (inverse $
                                                                                    cochain-limit cochain₁ {k = equivalence} ext₀) λ _ →
                                                                            F.id) ⟩
    (∃ λ (g : P ⇾ Up-to C 0) →
     ∃ λ (p : Eq (cl₁← g)) →
       subst Eq (_≃_.from steps₁-fixpoint≃ (λ _ → refl _)) p ≡
       steps₂ p)                                                        ↔⟨ drop-⊤-left-Σ ⇾↔⊤ ⟩

    (∃ λ (p : Eq (cl₁← g₀)) →
       subst Eq (_≃_.from steps₁-fixpoint≃ (λ _ → refl _)) p ≡
       steps₂ p)                                                        ↝⟨ (∃-cong λ _ → inverse $
                                                                            Eq.extensionality-isomorphism ext₀) ⟩
    (∃ λ (p : Eq (cl₁← g₀)) →
       ∀ n → subst Eq (_≃_.from steps₁-fixpoint≃ (λ _ → refl _)) p n ≡
             steps₂ p n)                                                ↝⟨ (∃-cong λ p → ∀-cong ext₀ λ n → ≡⇒↝ _ $ cong (_≡ steps₂ p n)
                                                                            steps₁-fixpoint-lemma) ⟩
    (∃ λ (p : Eq (cl₁← g₀)) →
       ∀ n → trans (p n) (steps₁-fixpoint n) ≡ steps₂ p n)              ↝⟨ (∃-cong λ _ → ∀-cong ext₀ λ _ → ≡⇒↝ _ $
                                                                            [trans≡]≡[≡trans-symʳ] _ _ _) ⟩
    (∃ λ (p : Eq (cl₁← g₀)) →
       ∀ n → p n ≡ trans (steps₂ p n) (sym (steps₁-fixpoint n)))        ↝⟨ (∃-cong λ _ →
                                                                            Πℕ≃ ext₀) ⟩
    (∃ λ (p : Eq (cl₁← g₀)) →
       p zero ≡ trans (steps₂ p zero) (sym (steps₁-fixpoint zero)) ×
       (∀ n → p (suc n) ≡
              trans (steps₂ p (suc n))
                (sym (steps₁-fixpoint (suc n)))))                       ↔⟨ (∃-cong λ _ → drop-⊤-left-× λ _ →
                                                                            _⇔_.to contractible⇔↔⊤ $
                                                                            H-level.⇒≡ 0 $ H-level.⇒≡ 0 contr) ⟩
    (∃ λ (p : Eq (cl₁← g₀)) →
       ∀ n → p (suc n) ≡
             trans (steps₂ p (suc n)) (sym (steps₁-fixpoint (suc n))))  ↔⟨⟩

    (∃ λ (p : Eq (cl₁← g₀)) →
       ∀ n → p (suc n) ≡
             trans (cong step (p n)) (sym (refl _)))                    ↝⟨ (∃-cong λ _ → ∀-cong ext₀ λ _ → ≡⇒↝ _ $ cong (_ ≡_) $
                                                                            trans (cong (trans _) sym-refl) $
                                                                            trans-reflʳ _) ⟩
    (∃ λ (p : Eq (cl₁← g₀)) →
       ∀ n → p (suc n) ≡ cong step (p n))                               ↝⟨ cochain-limit cochain₂ ext₀ ⟩

    down {C = C} 0 ∘⇾ step (cl₁← g₀ 0) ≡ cl₁← g₀ 0                      ↔⟨ _⇔_.to contractible⇔↔⊤ $
                                                                           H-level.⇒≡ 0 contr ⟩□
    ⊤                                                                   □

  -- The definition of M-final is set up so that it returns unfold Y
  -- rather than the function obtained directly from equiv. Here it is
  -- shown that the two functions are equal.

  ≡-unfold : ∀ b → proj₁ (_≃_.from (equiv b) _) ≡ unfold Y
  ≡-unfold ⊠ =
    apply-ext ext-i λ i → apply-ext ext′ λ p →
    Σ-≡,≡→≡
      (ext₀′ λ n → cong (λ f → f i p) (lemma₁ n))
      (lemma₃ i p)
    where

    -- Pieces of the function obtained from equiv.
    --
    -- These pieces are rather similar to pieces of unfold. I chose to
    -- implement unfold using explicit pattern matching rather than
    -- ℕ-rec to ensure that things do not unfold too much.

    up′ : ∀ n → P ⇾ Up-to C n
    up′ = ℕ-rec _ (λ _ ih → map C ih ∘⇾ f)

    ok′ : ∀ n → down n ∘⇾ up′ (suc n) ≡ up′ n
    ok′ = ℕ-rec
      (proj₁ (H-level.⇒≡ 0 contr))
      (λ _ → cong step)

    lemma₁ : ∀ n → up′ n ≡ Unfold.up Y n
    lemma₁ zero    = refl _
    lemma₁ (suc n) =
      step (up′ n)          ≡⟨ cong step $ lemma₁ n ⟩∎
      step (Unfold.up Y n)  ∎

    lemma₂ :
      ∀ n →
      trans (sym (cong (down n ∘⇾_) (lemma₁ (suc n))))
        (trans (ok′ n) (lemma₁ n)) ≡
      Unfold.ok Y n
    lemma₂ zero =
      trans (sym (cong (const _) (cong step (refl _))))
        (trans (proj₁ (H-level.⇒≡ 0 contr)) (refl _))    ≡⟨ trans (cong (flip trans _) $
                                                                   trans (cong sym $ cong-const _) $
                                                                   sym-refl) $
                                                            trans (trans-reflˡ _) $
                                                            trans-reflʳ _ ⟩

      proj₁ (H-level.⇒≡ 0 contr)                         ≡⟨ H-level.mono (Nat.zero≤ 2) contr _ _ ⟩∎

      refl _                                             ∎
    lemma₂ (suc n) =
      trans (sym (cong (down (1 + n) ∘⇾_) (lemma₁ (2 + n))))
        (trans (ok′ (1 + n)) (lemma₁ (1 + n)))                           ≡⟨⟩

      trans (sym (cong (map C (down n) ∘⇾_)
                    (cong step (lemma₁ (suc n)))))
        (trans (cong step (ok′ n)) (cong step (lemma₁ n)))               ≡⟨ cong (flip trans _) $ cong sym $
                                                                            cong-∘ _ _ _ ⟩
      trans (sym (cong ((map C (down n) ∘⇾_) ∘ step) (lemma₁ (suc n))))
        (trans (cong step (ok′ n)) (cong step (lemma₁ n)))               ≡⟨⟩

      trans (sym (cong (step ∘ (down n ∘⇾_)) (lemma₁ (suc n))))
        (trans (cong step (ok′ n)) (cong step (lemma₁ n)))               ≡⟨ sym $
                                                                            trans (cong-trans _ _ _) $
                                                                            cong₂ trans
                                                                              (trans (cong-sym _ _) $
                                                                               cong sym $ cong-∘ _ _ _)
                                                                              (cong-trans _ _ _) ⟩
      cong step
        (trans (sym (cong (down n ∘⇾_) (lemma₁ (suc n))))
           (trans (ok′ n) (lemma₁ n)))                                   ≡⟨ cong (cong _) $ lemma₂ n ⟩

      cong step (Unfold.ok Y n)                                          ≡⟨⟩

      Unfold.ok Y (1 + n)                                                ∎

    lemma₃ :
      ∀ i p →
      subst (λ f → ∀ n → down n i (f (suc n)) ≡ f n)
        (ext₀′ λ n → cong (λ f → f i p) (lemma₁ n))
        (cong (_$ p) ∘ cong (_$ i) ∘ ok′) ≡
      (λ n → cong (λ f → f i p) (Unfold.ok Y n))
    lemma₃ i p = ext₀′ λ n →
      subst (λ f → ∀ n → down n i (f (suc n)) ≡ f n)
        (ext₀′ λ n → cong (λ f → f i p) (lemma₁ n))
        (cong (_$ p) ∘ cong (_$ i) ∘ ok′) n                            ≡⟨ sym $
                                                                          push-subst-application _ _ ⟩
      subst (λ f → down n i (f (suc n)) ≡ f n)
        (ext₀′ λ n → cong (λ f → f i p) (lemma₁ n))
        (cong (_$ p) (cong (_$ i) (ok′ n)))                            ≡⟨ cong (subst (λ f → down n i (f (suc n)) ≡ f n) _) $
                                                                          cong-∘ _ _ _ ⟩
      subst (λ f → down n i (f (suc n)) ≡ f n)
        (ext₀′ λ n → cong (λ f → f i p) (lemma₁ n))
        (cong (λ f → f i p) (ok′ n))                                   ≡⟨ subst-in-terms-of-trans-and-cong ⟩

      trans (sym (cong (λ f → down n i (f (suc n)))
                    (ext₀′ λ n → cong (λ f → f i p) (lemma₁ n))))
        (trans (cong (λ f → f i p) (ok′ n))
           (cong (_$ n) (ext₀′ λ n → cong (λ f → f i p) (lemma₁ n))))  ≡⟨ cong₂ (λ eq₁ eq₂ →
                                                                                   trans (sym eq₁) (trans (cong (λ f → f i p) (ok′ n)) eq₂))
                                                                            (trans (sym $ cong-∘ _ _ _) $
                                                                             cong (cong _) $
                                                                             cong-ext ext₀)
                                                                            (cong-ext ext₀) ⟩
      trans (sym (cong (down n i)
                    (cong (λ f → f i p) (lemma₁ (suc n)))))
        (trans (cong (λ f → f i p) (ok′ n))
           (cong (λ f → f i p) (lemma₁ n)))                            ≡⟨ cong (flip trans _) $ cong sym $
                                                                          cong-∘ _ _ _ ⟩
      trans (sym (cong (λ f → down n i (f i p)) (lemma₁ (suc n))))
        (trans (cong (λ f → f i p) (ok′ n))
           (cong (λ f → f i p) (lemma₁ n)))                            ≡⟨ sym $
                                                                          trans (cong-trans _ _ _) $
                                                                          cong₂ trans
                                                                            (trans (cong-sym _ _) $
                                                                             cong sym $
                                                                             cong-∘ _ _ _)
                                                                            (cong-trans _ _ _) ⟩
      cong (λ f → f i p)
        (trans (sym (cong (down n ∘⇾_) (lemma₁ (suc n))))
           (trans (ok′ n) (lemma₁ n)))                                 ≡⟨ cong (cong _) $ lemma₂ n ⟩∎

      cong (λ f → f i p) (Unfold.ok Y n)                               ∎

  unfold-lemma :
    Block "equiv" →
    out-M b ext ∘⇾ unfold Y ≡ map _ (unfold Y) ∘⇾ f
  unfold-lemma b′ =
    subst
       (λ h → out-M b ext ∘⇾ h ≡ map C h ∘⇾ f)
       (≡-unfold b′)
       (proj₂ (_≃_.from (equiv b′) _))

  unfold-morphism :
    Block "equiv" → Y ⇨ M-coalgebra b ext C
  unfold-morphism b = unfold Y , unfold-lemma b

  ≡-unfold-morphism : ∀ b → _≃_.from (equiv b) _ ≡ unfold-morphism b
  ≡-unfold-morphism b =
    Σ-≡,≡→≡ (≡-unfold b) (refl (unfold-lemma b))

  M-final : Contractible (Y ⇨ M-coalgebra b ext C)
  M-final =
    block λ b →
    _↔_.from (contractible↔≃⊤ ext′) $
    Eq.with-other-inverse
      (equiv b)
      (λ _ → unfold-morphism b)
      (λ _ → ≡-unfold-morphism b)

  -- Note that unfold is not blocked, but that the other pieces are.

  M-final-partly-blocked :
    Block "M-final" →
    Contractible (Y ⇨ M-coalgebra b ext C)
  M-final-partly-blocked _ .proj₁ .proj₁ = unfold Y
  M-final-partly-blocked ⊠ .proj₁ .proj₂ = M-final .proj₁ .proj₂
  M-final-partly-blocked ⊠ .proj₂        = M-final .proj₂

-- M-coalgebra b ext C is a final coalgebra (assuming extensionality).
--
-- This is a variant of Theorem 7 from "Non-wellfounded trees in
-- Homotopy Type Theory".

M-final :
  (b : Block "M-final")
  {I : Type i} {C : Container I s p} →
  (ext : Extensionality p (i ⊔ s ⊔ p)) →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  Final (M-coalgebra b ext C)
M-final b ext ext′ Y =
  M-final.M-final-partly-blocked b ext ext′ Y b

-- The morphism returned by M-final is definitionally equal to an
-- instance of unfold.

_ :
  {Y : Coalgebra C} →
  proj₁ (proj₁ (M-final b ext₁ ext₂ Y)) ≡ unfold Y
_ = refl _

------------------------------------------------------------------------
-- H-levels

-- If the shape types of C have h-level n, then M C i has h-level n
-- (assuming extensionality).
--
-- This is a variant of Lemma 14 from "Non-wellfounded trees in
-- Homotopy Type Theory".

H-level-M :
  Extensionality p (i ⊔ s ⊔ p) →
  {I : Type i} {C : Container I s p} {i : I} →
  (∀ i → H-level n (Shape C i)) →
  H-level n (M C i)
H-level-M {p} {i = iℓ} {n = m} ext {C} hyp =
  Σ-closure m
    (Π-closure ext′ m
     H-level-Up-to) λ _ →
  Π-closure ext′ m $
  H-level.⇒≡ m ∘ H-level-Up-to
  where
  ext′ = lower-extensionality _ lzero ext

  step :
    ∀ P → (∀ {i} → H-level m (P i)) → (∀ {i} → H-level m (⟦ C ⟧ P i))
  step P h =
    Σ-closure m (hyp _) λ _ →
    Π-closure ext m λ _ →
    h

  H-level-Up-to : ∀ n → H-level m (Up-to C n i)
  H-level-Up-to (suc n) = step (Up-to C n) (H-level-Up-to n)
  H-level-Up-to zero    =
    ↑-closure m (H-level.mono (Nat.zero≤ m) ⊤-contractible)

-- If the shape types of C have h-level n, then F i has h-level n,
-- where F is the carrier of any final coalgebra of C, and "final
-- coalgebra" is defined using Final′. (Assuming extensionality.)

H-level-final-coalgebra′ :
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  {I : Type i} {C : Container I s p} {i : I} →
  (((X , _) , _) : Final-coalgebra′ C) →
  (∀ i → H-level n (Shape C i)) →
  H-level n (X i)
H-level-final-coalgebra′ {i = iℓ} {s} {n} ext {C} {i} F@((X , _) , _) =
  block λ b →

  (∀ i → H-level n (Shape C i))  ↝⟨ H-level-M ext′ ⟩
  H-level n (M C i)              ↝⟨ H-level-cong _ n $
                                    carriers-of-final-coalgebras-equivalent′
                                      (Final-coalgebra→Final-coalgebra′ $
                                       M-coalgebra b ext′ C , M-final b ext′ ext)
                                      F _ ⟩□
  H-level n (X i)                □
  where
  ext′ = lower-extensionality (iℓ ⊔ s) lzero ext

-- The previous result holds also if Final-coalgebra′ is replaced by
-- Final-coalgebra.

H-level-final-coalgebra :
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  {I : Type i} {C : Container I s p} {i : I} →
  (((X , _) , _) : Final-coalgebra C) →
  (∀ i → H-level n (Shape C i)) →
  H-level n (X i)
H-level-final-coalgebra ext =
  H-level-final-coalgebra′ ext ∘
  Final-coalgebra→Final-coalgebra′
