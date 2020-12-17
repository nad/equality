------------------------------------------------------------------------
-- M-types for indexed containers, defined using functions
------------------------------------------------------------------------

-- Based on "Non-wellfounded trees in Homotopy Type Theory" by Ahrens,
-- Capriotti and Spadotti. However, the indexed containers that are
-- used are not those used in that paper, but rather (more or less)
-- those presented in "Indexed containers" by Altenkirch, Ghani,
-- Hancock, McBride and Morris.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Container.Indexed.M.Function
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_)
open import Container.Indexed eq
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level using (H-level)
open import H-level.Closure eq
import Nat eq as Nat
open import Surjection eq using (_↠_)
open import Tactic.Sigma-cong eq
open import Univalence-axiom eq

private
  variable
    a ℓ p     : Level
    A I O     : Type a
    ext i k x : A
    Q         : A → Type p
    C         : Container I
    n         : ℕ

------------------------------------------------------------------------
-- Chains

-- Chains (indexed).

Chain : Type i → Type (lsuc i)
Chain {i = i} I =
  ∃ λ (P : ℕ → I → Type i) → ∀ n → P (suc n) ⇾ P n

-- Limits of chains.

Limit : {I : Type i} → Chain I → I → Type i
Limit (P , down) i =
  ∃ λ (f : ∀ n → P n i) →
    ∀ n → down n i (f (suc n)) ≡ f n

-- A kind of dependent universal property for limits.

universal-property-Π :
  {A : Type a} {I : Type i} {g : A → I} →
  (X@(P , down) : Chain I) →

  ((a : A) → Limit X (g a))
    ≃
  (∃ λ (f : ∀ n (a : A) → P n (g a)) →
     ∀ n a → down n (g a) (f (suc n) a) ≡ f n a)

universal-property-Π {g = g} X@(P , down) =
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
  Extensionality? k i (i ⊔ p) →
  (X@(Q , down) : Chain I) →

  (P ⇾ Limit X)
    ↝[ k ]
  (∃ λ (f : ∀ n → P ⇾ Q n) →
     ∀ n i x → down n i (f (suc n) i x) ≡ f n i x)

universal-property {P = P} ext X@(Q , down) =
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

Cone : {I : Type i} → (I → Type p) → Chain I → Type (i ⊔ p)
Cone P (Q , down) =
  ∃ λ (f : ∀ n → P ⇾ Q n) →
    ∀ n → down n ∘⇾ f (suc n) ≡ f n

-- A variant of the non-dependent universal property.

universal-property-≃ :
  {I : Type i} {P : I → Type p} →
  Extensionality (i ⊔ p) (i ⊔ p) →
  (X : Chain I) →

  (P ⇾ Limit X) ≃ Cone P X

universal-property-≃ {i = i} {p = p} {P = P} ext X@(Q , down) =
  P ⇾ Limit X                                       ↝⟨ universal-property (lower-extensionality p lzero ext) X ⟩

  (∃ λ (f : ∀ n → P ⇾ Q n) →
     ∀ n i x → down n i (f (suc n) i x) ≡ f n i x)  ↝⟨ (∃-cong λ _ → ∀-cong (lower-extensionality _ lzero ext) λ _ →
                                                        ∀-cong (lower-extensionality p lzero ext) λ _ →
                                                        Eq.extensionality-isomorphism (lower-extensionality i p ext)) ⟩
  (∃ λ (f : ∀ n → P ⇾ Q n) →
     ∀ n i → down n i ∘ f (suc n) i ≡ f n i)        ↝⟨ (∃-cong λ _ → ∀-cong (lower-extensionality _ lzero ext) λ _ →
                                                        Eq.extensionality-isomorphism (lower-extensionality p (i ⊔ p) ext)) ⟩
  (∃ λ (f : ∀ n → P ⇾ Q n) →
     ∀ n → down n ∘⇾ f (suc n) ≡ f n)               ↔⟨⟩

  Cone P X                                          □

-- Shifts a chain one step.

shift : Chain I → Chain I
shift = Σ-map (_∘ suc) (_∘ suc)

-- Shifting does not affect the limit (assuming extensionality).
--
-- This is a variant of Lemma 12 in "Non-wellfounded trees in Homotopy
-- Type Theory".

Limit-shift :
  {I : Type i} →
  Extensionality? k lzero i →
  ∀ (X : Chain I) {i} →
  Limit (shift X) i ↝[ k ] Limit X i
Limit-shift {i = iℓ} ext X@(P , down) {i = i} =
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
                                                           lemma₂-↔)
                                                        ext ⟩
  (∃ λ (p : ∀ n → P n i) →
     ∀ n → down n i (p (suc n)) ≡ p n)             ↔⟨⟩

  Limit X i                                        □
  where
  lemma₁-↠ :
    {P : ℕ → Type iℓ} →
    (∀ n → P n) ↠ (P 0 × (∀ n → P (suc n)))
  lemma₁-↠ ._↠_.logical-equivalence ._⇔_.to   = λ p → p 0 , p ∘ suc
  lemma₁-↠ ._↠_.logical-equivalence ._⇔_.from = uncurry ℕ-case
  lemma₁-↠ ._↠_.right-inverse-of              = refl

  lemma₁-↔ :
    {P : ℕ → Type iℓ} →
    Extensionality lzero iℓ →
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

  lemma₂-↔ : Extensionality lzero iℓ → _ ↔ _
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
  Extensionality? k lzero ℓ →
  ((P , up) : Cochain ℓ) →

  (∃ λ (p : ∀ n → P n) → ∀ n → p (suc n) ≡ up n (p n))
    ↝[ k ]
  P 0
cochain-limit ext X@(_ , up) =
  generalise-ext?
  (_↠_.logical-equivalence cl)
  (λ ext → record { surjection      = cl
                  ; left-inverse-of = from∘to ext
                  })
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
    (apply-ext ext′ (from₁∘to l))
    (apply-ext ext λ n →

     subst (λ p → ∀ n → p (suc n) ≡ up n (p n))
       (apply-ext ext′ (from₁∘to l))
       (λ _ → refl _) n                                            ≡⟨ sym $ push-subst-application _ _ ⟩

     subst (λ p → p (suc n) ≡ up n (p n))
       (apply-ext ext′ (from₁∘to l))
       (refl _)                                                    ≡⟨ trans subst-in-terms-of-trans-and-cong $
                                                                      cong (trans _) $
                                                                      trans-reflˡ _ ⟩
     trans (sym $ cong (_$ suc n) (apply-ext ext′ (from₁∘to l)))
       (cong (λ p → up n (p n)) (apply-ext ext′ (from₁∘to l)))     ≡⟨ cong₂ trans
                                                                        (cong sym $ Eq.cong-good-ext ext _)
                                                                        (trans (sym $ cong-∘ _ _ _) $
                                                                         cong (cong _) $ Eq.cong-good-ext ext _) ⟩
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
    where
    ext′ = Eq.good-ext ext

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
  Extensionality? k lzero a →

  (∃ λ (f : ℕ → A) → ∀ n → f (suc n) ≡ f n) ↝[ k ] A
simple-cochain-limit ext =
  generalise-ext?
    (_↠_.logical-equivalence scl)
    (λ ext → record { surjection      = scl
                    ; left-inverse-of = from∘to ext
                    })
    ext
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
    (apply-ext ext′ (from₁∘to l))
    (apply-ext ext λ n →

     subst (λ f → ∀ n → f (suc n) ≡ f n)
       (apply-ext ext′ (from₁∘to l))
       (λ _ → refl _) n                                             ≡⟨ sym $ push-subst-application _ _ ⟩

     subst (λ f → f (suc n) ≡ f n)
       (apply-ext ext′ (from₁∘to l))
       (refl _)                                                     ≡⟨ trans subst-in-terms-of-trans-and-cong $
                                                                       cong (trans _) $
                                                                       trans-reflˡ _ ⟩
     trans (sym $ cong (_$ suc n) (apply-ext ext′ (from₁∘to l)))
       (cong (_$ n) (apply-ext ext′ (from₁∘to l)))                  ≡⟨ cong₂ trans
                                                                         (cong sym $ Eq.cong-good-ext ext _)
                                                                         (Eq.cong-good-ext ext _) ⟩
     trans (sym $ from₁∘to l (suc n)) (from₁∘to l n)                ≡⟨⟩

     trans (sym $ trans (from₁∘to l n) (sym $ p n)) (from₁∘to l n)  ≡⟨ cong (flip trans _) $
                                                                       trans (sym-trans _ _) $
                                                                       cong (flip trans _) $
                                                                       sym-sym _ ⟩

     trans (trans (p n) (sym $ from₁∘to l n)) (from₁∘to l n)        ≡⟨ trans-[trans-sym]- _ _ ⟩∎

     p n                                                            ∎)
    where
    ext′ = Eq.good-ext ext

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
  Container₂ I O → Chain I → Chain O
Container-chain C = Σ-map (⟦ C ⟧ ∘_) (map C ∘_)

-- The polynomial functor (for a container C) of the limit of a chain
-- is pointwise equivalent to the limit of C applied to the chain
-- (assuming extensionality).
--
-- This is a variant of Lemma 13 in "Non-wellfounded trees in Homotopy
-- Type Theory".

⟦⟧-Limit≃ :
  {I O : Type i} →
  Extensionality i i →
  (C : Container₂ I O) (X : Chain I) {o : O} →

  ⟦ C ⟧ (Limit X) o ≃ Limit (Container-chain C X) o
⟦⟧-Limit≃ ext C@(S ◁ P) X@(Q , down) {o = o} =
  ⟦ C ⟧ (Limit X) o                                          ↔⟨⟩

  (∃ λ (s : S o) → P s ⇾ Limit X)                            ↝⟨ (∃-cong λ _ → universal-property-≃ ext X) ⟩

  (∃ λ (s : S o) → ∃ λ (f : ∀ n → P s ⇾ Q n) →
     ∀ n → down n ∘⇾ f (suc n) ≡ f n)                        ↝⟨ (Σ-cong (inverse $ simple-cochain-limit {k = equivalence} ext′) λ _ →
                                                                 ∃-cong λ _ → ∀-cong ext′ λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                 subst-refl _ _) ⟩
  (∃ λ ((s , eq) : ∃ λ (s : ℕ → S o) →
                     ∀ n → s (suc n) ≡ s n) →
   ∃ λ (f : ∀ n → P (s n) ⇾ Q n) →
     ∀ n → subst (λ s → P s ⇾ Q n) (eq n)
             (down n ∘⇾ f (suc n)) ≡
           f n)                                              ↔⟨ (∃-cong λ _ →
                                                                 (∃-cong λ _ →
                                                                  (∀-cong ext′ λ _ → Bijection.Σ-≡,≡↔≡) F.∘
                                                                  inverse ΠΣ-comm) F.∘
                                                                 ∃-comm) F.∘
                                                                inverse Σ-assoc ⟩
  (∃ λ (s : ℕ → S o) →
   ∃ λ (f : ∀ n → P (s n) ⇾ Q n) →
     ∀ n → (s (suc n) , down n ∘⇾ f (suc n)) ≡ (s n , f n))  ↔⟨⟩

  (∃ λ (s : ℕ → S o) →
   ∃ λ (f : ∀ n → P (s n) ⇾ Q n) →
     ∀ n → map C (down n) o (s (suc n) , f (suc n)) ≡
           (s n , f n))                                      ↝⟨ (inverse $ Σ-cong-id (Eq.↔⇒≃ ΠΣ-comm)) F.∘
                                                                Eq.↔⇒≃ Σ-assoc ⟩
  (∃ λ (f : ∀ n → ∃ λ (s : S o) → P s ⇾ Q n) →
     ∀ n → map C (down n) o (f (suc n)) ≡ f n)               ↔⟨⟩

  Limit (Container-chain C X) o                              □
  where
  ext′ = lower-extensionality _ lzero ext

------------------------------------------------------------------------
-- M-types

private

  -- Up-to C n is the n-fold application of ⟦ C ⟧ to something
  -- trivial.

  Up-to : {I : Type i} → Container I → ℕ → I → Type i
  Up-to C zero    = λ _ → ↑ _ ⊤
  Up-to C (suc n) = ⟦ C ⟧ (Up-to C n)

  -- Up-to C is downwards closed.

  down : ∀ n → Up-to C (suc n) ⇾ Up-to C n
  down zero    = _
  down (suc n) = map _ (down n)

  -- One can combine Up-to and down into a chain.

  M-chain : Container I → Chain I
  M-chain C = Up-to C , down

-- An M-type for a given container.

M : {I : Type i} → Container I → I → Type i
M C = Limit (M-chain C)

-- M C is, in a certain sense, a fixpoint of ⟦ C ⟧ (assuming
-- extensionality).

M-fixpoint :
  Block "M-fixpoint" →
  {I : Type i} →
  Extensionality i i →
  {C : Container I} {i : I} →
  ⟦ C ⟧ (M C) i ≃ M C i
M-fixpoint ⊠ ext {C = C} {i = i} =
  ⟦ C ⟧ (M C) i                            ↔⟨⟩
  ⟦ C ⟧ (Limit (M-chain C)) i              ↝⟨ ⟦⟧-Limit≃ ext C (M-chain C) ⟩
  Limit (Container-chain C (M-chain C)) i  ↔⟨⟩
  Limit (shift (M-chain C)) i              ↝⟨ Limit-shift (lower-extensionality _ lzero ext) (M-chain C) ⟩
  Limit (M-chain C) i                      ↔⟨⟩
  M C i                                    □

-- One direction of the fixpoint.

out-M :
  Block "M-fixpoint" →
  {I : Type i} {C : Container I} →
  Extensionality i i →
  M C ⇾ ⟦ C ⟧ (M C)
out-M b ext _ = _≃_.from (M-fixpoint b ext)

-- The other direction of the fixpoint.

in-M :
  Block "M-fixpoint" →
  {I : Type i} {C : Container I} →
  Extensionality i i →
  ⟦ C ⟧ (M C) ⇾ M C
in-M b ext _ = _≃_.to (M-fixpoint b ext)

-- A "computation" rule for in-M.

in-M≡ :
  (b : Block "M-fixpoint")
  {I : Type i}
  (ext : Extensionality i i) →
  let ext′ = apply-ext (Eq.good-ext (lower-extensionality i i ext)) in
  {C : Container I} {i : I}
  (x@(s , f) : ⟦ C ⟧ (M C) i) →
  in-M b ext _ x ≡
  ( ℕ-case _ (λ n → map C (λ _ m → proj₁ m n) _ x)
  , ℕ-case (refl _)
      (λ n → cong (s ,_) $ ext′ λ i → ext′ λ p → proj₂ (f i p) n)
  )
in-M≡ {i = i} ⊠ ext {C = C} x@(s , f) =
  ( ℕ-case _ (λ n → map C (λ _ m → proj₁ m n) _ x)
  , ℕ-case (refl _)
      (λ n → Σ-≡,≡→≡
         (refl _)
         (≡⇒→
            (cong (_≡ λ i p → proj₁ (f i p) n) $ sym $
             subst-refl _ _)
            (ext′ λ i → ext′ λ p → proj₂ (f i p) n)))
  )                                                                ≡⟨ cong (ℕ-case _ (λ n → map C (λ _ m → proj₁ m n) _ x) ,_) $
                                                                      cong (ℕ-case (refl _)) $
                                                                      apply-ext (lower-extensionality _ lzero ext) lemma ⟩∎
  ( ℕ-case _ (λ n → map C (λ _ m → proj₁ m n) _ x)
  , ℕ-case (refl _)
      (λ n → cong (s ,_) $ ext′ λ i → ext′ λ p → proj₂ (f i p) n)
  )                                                                ∎
  where
  ext′ = apply-ext (Eq.good-ext (lower-extensionality i i ext))

  lemma = λ n →
    Σ-≡,≡→≡
      (refl _)
      (≡⇒→
         (cong (_≡ λ i p → proj₁ (f i p) n) $ sym $
          subst-refl _ _)
         (ext′ λ i → ext′ λ p → proj₂ (f i p) n))       ≡⟨ Σ-≡,≡→≡-reflˡ _ ⟩

    cong (_ ,_)
         (trans (sym $ subst-refl _ _) $
          ≡⇒→
            (cong (_≡ λ i p → proj₁ (f i p) n) $ sym $
             subst-refl _ _)
            (ext′ λ i → ext′ λ p → proj₂ (f i p) n))    ≡⟨ cong (cong (_ ,_)) $ cong (trans _) $ sym $
                                                           subst-id-in-terms-of-≡⇒↝ equivalence ⟩
    cong (_ ,_)
         (trans (sym $ subst-refl _ _) $
          subst id
            (cong (_≡ λ i p → proj₁ (f i p) n) $ sym $
             subst-refl _ _)
            (ext′ λ i → ext′ λ p → proj₂ (f i p) n))    ≡⟨ cong (cong (_ ,_)) $ cong (trans _) $ sym $
                                                           subst-∘ _ _ _ ⟩
    cong (_ ,_)
         (trans (sym $ subst-refl _ _) $
          subst (_≡ λ i p → proj₁ (f i p) n)
            (sym $ subst-refl _ _)
            (ext′ λ i → ext′ λ p → proj₂ (f i p) n))    ≡⟨ cong (cong (_ ,_)) $ cong (trans _) $
                                                           subst-trans _ ⟩
    cong (_ ,_)
         (trans (sym $ subst-refl _ _) $
          trans (subst-refl _ _)
            (ext′ λ i → ext′ λ p → proj₂ (f i p) n))    ≡⟨ cong (cong (_ ,_)) $
                                                           trans-sym-[trans] _ _ ⟩∎
    cong (_ ,_)
         (ext′ λ i → ext′ λ p → proj₂ (f i p) n)        ∎

-- A coalgebra defined using M and out-M.

M-coalgebra :
  Block "M-fixpoint" →
  {I : Type i} →
  Extensionality i i →
  (C : Container I) → Coalgebra C
M-coalgebra b ext C = M C , out-M b ext

-- M-coalgebra b ext C is a final coalgebra.

M-final :
  (b : Block "M-fixpoint")
  {I : Type i} {C : Container I} →
  (ext : Extensionality i i) →
  Final (M-coalgebra b ext C)
M-final {i = i} b {C = C} ext Y@(P , f) =
  _↔_.from (contractible↔≃⊤ ext)
    (Y ⇨ M-coalgebra b ext C                                             ↔⟨⟩

     (∃ λ (h : P ⇾ M C) → out-M b ext ∘⇾ h ≡ step h)                     ↝⟨ (∃-cong λ _ → inverse $
                                                                             Eq.≃-≡ $ ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                             M-fixpoint b ext) ⟩
     (∃ λ (h : P ⇾ M C) →
        (in-M b ext ∘⇾ out-M b ext) ∘⇾ h ≡ in-M b ext ∘⇾ step h)         ↝⟨ (∃-cong λ h → ≡⇒↝ _ $ cong (_≡ in-M b ext ∘⇾ step h) $
                                                                             apply-ext ext λ _ → apply-ext ext λ _ →
                                                                             _≃_.right-inverse-of (M-fixpoint b ext) _) ⟩

     (∃ λ (h : P ⇾ M C) → h ≡ in-M b ext ∘⇾ step h)                      ↝⟨ (inverse $
                                                                             Σ-cong (inverse $ universal-property-≃ ext (M-chain C)) λ _ →
                                                                             F.id) ⟩
     (∃ λ (c : Cone P (M-chain C)) →
        univ c ≡ in-M b ext ∘⇾ step (univ c))                            ↝⟨ (∃-cong λ c → ≡⇒↝ _ $ cong (univ c ≡_) $ ≡univ-steps c) ⟩

     (∃ λ (c : Cone P (M-chain C)) → univ c ≡ univ (steps c))            ↝⟨ (∃-cong λ _ →
                                                                             Eq.≃-≡ $ inverse $ universal-property-≃ ext (M-chain C)) ⟩

     (∃ λ (c : Cone P (M-chain C)) → c ≡ steps c)                        ↔⟨ (∃-cong λ _ → inverse
                                                                             Bijection.Σ-≡,≡↔≡) ⟩
     (∃ λ ((g , p) : Cone P (M-chain C)) →
      ∃ λ (q : g ≡ steps₁ g) → subst Eq q p ≡ steps₂ p)                  ↔⟨ Σ-assoc F.∘
                                                                            (∃-cong λ _ → ∃-comm) F.∘
                                                                            inverse Σ-assoc ⟩
     (∃ λ ((g , q) : ∃ λ (g : ∀ n → P ⇾ Up-to C n) → g ≡ steps₁ g) →
      ∃ λ (p : Eq g) → subst Eq q p ≡ steps₂ p)                          ↝⟨ (Σ-cong-contra (inverse $ ∃-cong λ _ →
                                                                                            steps₁-fixpoint≃) λ _ →
                                                                             F.id) ⟩
     (∃ λ ((g , q) : ∃ λ (g : ∀ n → P ⇾ Up-to C n) →
                       ∀ n → g (suc n) ≡ step (g n)) →
      ∃ λ (p : Eq g) →
        subst Eq (_≃_.from steps₁-fixpoint≃ q) p ≡ steps₂ p)             ↝⟨ (inverse $
                                                                             Σ-cong (inverse $
                                                                                     cochain-limit {k = equivalence} ext₀ cochain₁) λ _ →
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
        ∀ n → p (suc n) ≡ cong step (p n))                               ↝⟨ cochain-limit ext₀ cochain₂ ⟩

     down {C = C} 0 ∘⇾ step (cl₁← g₀ 0) ≡ cl₁← g₀ 0                      ↔⟨ _⇔_.to contractible⇔↔⊤ $
                                                                            H-level.⇒≡ 0 contr ⟩□
     ⊤                                                                   □)
  where
  step : P ⇾ Q → P ⇾ ⟦ C ⟧ Q
  step h = map C h ∘⇾ f

  univ = _≃_.from (universal-property-≃ ext (M-chain C))

  steps₁ : (∀ n → P ⇾ Up-to C n) → (∀ n → P ⇾ Up-to C n)
  steps₁ g n i p =
    ℕ-case
      {P = λ n → Up-to C n i}
      _
      (λ n → step (g n) i p)
      n

  Eq : (∀ n → P ⇾ Up-to C n) → Type i
  Eq g = ∀ n → down n ∘⇾ g (suc n) ≡ g n

  steps₂ : {g : ∀ n → P ⇾ Up-to C n} → Eq g → Eq (steps₁ g)
  steps₂         p zero    = refl _
  steps₂ {g = g} p (suc n) =
    down (suc n) ∘⇾ steps₁ g (suc (suc n))  ≡⟨⟩
    step (down n ∘⇾ g (suc n))              ≡⟨ cong step (p n) ⟩∎
    step (g n)                              ∎

  steps : Cone P (M-chain C) → Cone P (M-chain C)
  steps = Σ-map steps₁ steps₂

  ext₀ : Extensionality lzero i
  ext₀ = lower-extensionality i lzero ext

  ≡univ-steps : ∀ c → in-M b ext ∘⇾ step (univ c) ≡ univ (steps c)
  ≡univ-steps c@(g , eq) = apply-ext ext λ i → apply-ext ext λ p →
    in-M b ext i (step (univ c) i p)                                 ≡⟨ in-M≡ b ext (step (univ c) i p) ⟩

    ( (λ n → steps₁ g n i p)
    , ℕ-case (refl _)
        (λ n →
           cong (proj₁ (f i p) ,_)
             (ext″ λ i′ → ext″ λ p′ →
              ext⁻¹ (ext⁻¹ (eq n) i′) (proj₂ (f i p) i′ p′)))
    )                                                                ≡⟨ cong ((λ n → steps₁ g n i p) ,_) $
                                                                        apply-ext ext₀ $ ℕ-case
                                                                          (
        refl _                                                             ≡⟨ sym $ ext⁻¹-refl _ {x = p} ⟩
        ext⁻¹ (refl _) p                                                   ≡⟨ cong (flip ext⁻¹ p) $ sym $ ext⁻¹-refl _ ⟩
        ext⁻¹ (ext⁻¹ {B = λ x → P x → ↑ _ ⊤} (refl _) i) p                 ≡⟨⟩
        ext⁻¹ (ext⁻¹ (steps₂ eq zero) i) p                                 ∎)
                                                                          (λ n →
        cong (proj₁ (f i p) ,_)
          (ext″ λ i′ → ext″ λ p′ →
           ext⁻¹ (ext⁻¹ (eq n) i′) (proj₂ (f i p) i′ p′))                    ≡⟨ elim₁
                                                                                  (λ eq →
                                                                                     cong (proj₁ (f i p) ,_)
                                                                                       (ext″ λ i′ → ext″ λ p′ →
                                                                                        ext⁻¹ (ext⁻¹ eq i′) (proj₂ (f i p) i′ p′)) ≡
                                                                                     ext⁻¹ (ext⁻¹ (cong (λ g → map C g ∘⇾ f) eq) i) p)
                                                                                  (
            cong (proj₁ (f i p) ,_)
              (ext″ λ i′ → ext″ λ p′ →
               ext⁻¹ (ext⁻¹ (refl (g n)) i′) (proj₂ (f i p) i′ p′))                ≡⟨ (cong (cong _) $
                                                                                       cong ext″ $ ext″ λ _ →
                                                                                       cong ext″ $ ext″ λ _ →
                                                                                       trans (cong (flip ext⁻¹ _) $
                                                                                              ext⁻¹-refl _) $
                                                                                       ext⁻¹-refl _) ⟩

            cong (proj₁ (f i p) ,_) (ext″ λ _ → ext″ λ _ → refl _)                 ≡⟨ trans (cong (cong _) $
                                                                                             trans (cong ext″ $ ext″ λ _ →
                                                                                                    Eq.good-ext-refl ext′ _) $
                                                                                             Eq.good-ext-refl ext′ _) $
                                                                                      cong-refl _ ⟩

            refl _                                                                 ≡⟨ sym $
                                                                                      trans (cong (flip ext⁻¹ _) $
                                                                                             trans (cong (flip ext⁻¹ _) $
                                                                                                    cong-refl _) $
                                                                                             ext⁻¹-refl _) $
                                                                                      ext⁻¹-refl _ ⟩∎
            ext⁻¹ (ext⁻¹ (cong step (refl (g n))) i) p                             ∎)
                                                                                  (eq n) ⟩
        ext⁻¹ (ext⁻¹ (cong step (eq n)) i) p                                 ∎) ⟩

    ( (λ n → steps₁ g n i p)
    , (λ n → ext⁻¹ (ext⁻¹ (steps₂ eq n) i) p)
    )                                                                ≡⟨⟩

    univ (steps c) i p                                               ∎
    where
    ext′ = lower-extensionality i i ext
    ext″ = apply-ext (Eq.good-ext ext′)

  contr : Contractible (P ⇾ Up-to C 0)
  contr =
    Π-closure ext 0 λ _ →
    Π-closure ext 0 λ _ →
    ↑-closure 0 ⊤-contractible

  steps₁-fixpoint≃ :
    {g : ∀ n → P ⇾ Up-to C n} →
    (g ≡ steps₁ g) ≃ (∀ n → g (suc n) ≡ step (g n))
  steps₁-fixpoint≃ {g = g} =
    g ≡ steps₁ g                                             ↝⟨ inverse $ Eq.extensionality-isomorphism ext₀ ⟩

    (∀ n → g n ≡ steps₁ g n)                                 ↝⟨ Πℕ≃ ext₀ ⟩

    g 0 ≡ steps₁ g 0 × (∀ n → g (suc n) ≡ steps₁ g (suc n))  ↔⟨⟩

    (λ _ _ → lift tt) ≡ (λ _ _ → lift tt) ×
    (∀ n → g (suc n) ≡ step (g n))                           ↔⟨ (drop-⊤-left-× λ _ →
                                                                 _⇔_.to contractible⇔↔⊤ $
                                                                 H-level.⇒≡ 0 contr) ⟩□
    (∀ n → g (suc n) ≡ step (g n))                           □

  cochain₁ : Cochain i
  cochain₁ = (λ n → P ⇾ Up-to C n)
           , (λ _ → step)

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
  steps₁-fixpoint-lemma {n = n} {p = p} =
    subst Eq (_≃_.from steps₁-fixpoint≃ (λ _ → refl _)) p n          ≡⟨⟩

    subst Eq (ext′ (ℕ-case _ (λ _ → refl _))) p n                    ≡⟨ cong (λ eq → subst Eq eq p n) $
                                                                        cong ext′ $
                                                                        cong (flip ℕ-case _) $
                                                                        H-level.mono (Nat.zero≤ 2) contr _ _ ⟩

    subst Eq (ext′ s) p n                                            ≡⟨ sym $ push-subst-application _ _ ⟩

    subst (λ g → down n ∘⇾ g (suc n) ≡ g n) (ext′ s) (p n)           ≡⟨ trans subst-in-terms-of-trans-and-cong $
                                                                        cong (flip trans _) $ cong sym $ sym $
                                                                        cong-∘ _ _ _ ⟩
    trans (sym (cong (down n ∘⇾_) (cong (_$ suc n) (ext′ s))))
      (trans (p n) (cong (_$ n) (ext′ s)))                           ≡⟨ cong₂ (λ eq₁ eq₂ → trans (sym (cong (down n ∘⇾_) eq₁)) (trans _ eq₂))
                                                                          (Eq.cong-good-ext ext₀ _)
                                                                          (Eq.cong-good-ext ext₀ _) ⟩
    trans (sym (cong (down n ∘⇾_) (s (suc n)))) (trans (p n) (s n))  ≡⟨⟩

    trans (sym (cong (down n ∘⇾_) (refl _))) (trans (p n) (s n))     ≡⟨ trans (cong (flip trans _) $
                                                                               trans (cong sym $ cong-refl _)
                                                                               sym-refl) $
                                                                        trans-reflˡ _ ⟩∎
    trans (p n) (s n)                                                ∎
    where
    ext′ = apply-ext (Eq.good-ext ext₀)
    s    = steps₁-fixpoint

  cochain₂ : Cochain i
  cochain₂ = (λ n → down n ∘⇾ step (cl₁← g₀ n) ≡ cl₁← g₀ n)
           , (λ _ → cong step)

------------------------------------------------------------------------
-- H-levels

-- If the shape types of C have h-level n, then M C i has h-level n
-- (assuming extensionality).
--
-- This is a variant of Lemma 14 from "Non-wellfounded trees in
-- Homotopy Type Theory".

H-level-M :
  Extensionality i i →
  {I : Type i} {C : Container I} {i : I} →
  (∀ {i} → H-level n (Shape C i)) →
  H-level n (M C i)
H-level-M {n = m} ext {C = C} hyp =
  Σ-closure m
    (Π-closure ext′ m
     H-level-Up-to) λ _ →
  Π-closure ext′ m $
  H-level.⇒≡ m ∘ H-level-Up-to
  where
  ext′ = lower-extensionality _ lzero ext

  step : ∀ P → (∀ {i} → H-level m (P i)) → (∀ {i} → H-level m (⟦ C ⟧ P i))
  step P h =
    Σ-closure m hyp λ _ →
    Π-closure ext m λ _ →
    Π-closure ext m λ _ →
    h

  H-level-Up-to : ∀ n → H-level m (Up-to C n i)
  H-level-Up-to (suc n) = step (Up-to C n) (H-level-Up-to n)
  H-level-Up-to zero    =
    ↑-closure m (H-level.mono (Nat.zero≤ m) ⊤-contractible)

-- If the shape types of C have h-level n, then F i has h-level n,
-- where F is the carrier of any final coalgebra of C (assuming
-- extensionality).

H-level-final-coalgebra :
  Extensionality i i →
  {I : Type i} {C : Container I} {i : I} →
  (((X , _) , _) : Final-coalgebra C) →
  (∀ {i} → H-level n (Shape C i)) →
  H-level n (X i)
H-level-final-coalgebra {n = n} ext {C = C} {i = i} F@((X , _) , _) =
  block λ b →

  (∀ {i} → H-level n (Shape C i))  ↝⟨ H-level-M ext ⟩
  H-level n (M C i)                ↝⟨ H-level-cong _ n $
                                      carriers-of-final-coalgebras-equivalent (M-coalgebra b ext C , M-final b ext) F _ ⟩□
  H-level n (X i)                  □
