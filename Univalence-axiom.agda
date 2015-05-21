------------------------------------------------------------------------
-- The univalence axiom
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module Univalence-axiom
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection using (_↔_)
open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq
  hiding (id; inverse) renaming (_∘_ to _⊚_)
open import Function-universe eq as F hiding (id; _∘_)
open import Groupoid eq
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (Injective)
open import Logical-equivalence hiding (id; _∘_; inverse)
open import Prelude
open import Surjection eq hiding (id; _∘_; ∃-cong)

------------------------------------------------------------------------
-- The univalence axiom

-- If two sets are equal, then they are equivalent.

≡⇒≃ : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
≡⇒≃ = ≡⇒↝ equivalence

-- The univalence axiom states that ≡⇒≃ is an equivalence.

Univalence′ : ∀ {ℓ} → Set ℓ → Set ℓ → Set (lsuc ℓ)
Univalence′ A B = Is-equivalence (≡⇒≃ {A = A} {B = B})

Univalence : ∀ ℓ → Set (lsuc ℓ)
Univalence ℓ = {A B : Set ℓ} → Univalence′ A B

-- An immediate consequence is that equalities are equivalent to
-- equivalences.

≡≃≃ : ∀ {ℓ} {A B : Set ℓ} → Univalence′ A B → (A ≡ B) ≃ (A ≃ B)
≡≃≃ univ = ⟨ ≡⇒≃ , univ ⟩

-- In the case of sets equalities are equivalent to bijections (if we
-- add the assumption of extensionality).

≡≃↔ : ∀ {ℓ} {A B : Set ℓ} →
      Univalence′ A B →
      Extensionality ℓ ℓ →
      Is-set A →
      (A ≡ B) ≃ (A ↔ B)
≡≃↔ {A = A} {B} univ ext A-set =
  (A ≡ B)  ↝⟨ ≡≃≃ univ ⟩
  (A ≃ B)  ↔⟨ inverse $ ↔↔≃ ext A-set ⟩□
  (A ↔ B)  □

-- Some abbreviations.

≡⇒→ : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
≡⇒→ = _≃_.to ∘ ≡⇒≃

≡⇒← : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → B → A
≡⇒← = _≃_.from ∘ ≡⇒≃

≃⇒≡ : ∀ {ℓ} {A B : Set ℓ} → Univalence′ A B → A ≃ B → A ≡ B
≃⇒≡ univ = _≃_.from (≡≃≃ univ)

------------------------------------------------------------------------
-- A consequence: Set is not a set

-- The univalence axiom implies that Set is not a set. (This was
-- pointed out to me by Thierry Coquand.)

abstract

  -- First a lemma: Some equality types have infinitely many
  -- inhabitants (assuming univalence).
  --
  -- (This lemma is more general than what is necessary for proving
  -- ¬-Set-set below. For that lemma it is enough to observe that
  -- there are two proofs of Bool ≡ Bool, corresponding to id and
  -- not.)

  equality-can-have-infinitely-many-inhabitants :
    Univalence′ ℕ ℕ →
    ∃ λ (A : Set) → ∃ λ (B : Set) →
    ∃ λ (p : ℕ → A ≡ B) → Injective p
  equality-can-have-infinitely-many-inhabitants univ =
    (ℕ , ℕ , cast ∘ p , cast-preserves-injections p p-injective)
    where
    cast : ℕ ≃ ℕ → ℕ ≡ ℕ
    cast = ≃⇒≡ univ

    cast-preserves-injections :
      {A : Set} (f : A → ℕ ≃ ℕ) →
      Injective f → Injective (cast ∘ f)
    cast-preserves-injections f inj {x = x} {y = y} cast-f-x≡cast-f-y =
      inj (f x               ≡⟨ sym $ _≃_.right-inverse-of (≡≃≃ univ) (f x) ⟩
           ≡⇒≃ (cast (f x))  ≡⟨ cong ≡⇒≃ cast-f-x≡cast-f-y ⟩
           ≡⇒≃ (cast (f y))  ≡⟨ _≃_.right-inverse-of (≡≃≃ univ) (f y) ⟩∎
           f y               ∎)

    swap : ℕ → ℕ → ℕ
    swap i zero    = i
    swap i (suc n) with ℕ._≟_ i (suc n)
    ... | yes i≡1+n = zero
    ... | no  i≢1+n = suc n

    swap∘swap : ∀ i n → swap i (swap i n) ≡ n
    swap∘swap zero    zero    = refl zero
    swap∘swap (suc i) zero    with ℕ._≟_ i i
    ... | yes _   = refl 0
    ... | no  i≢i = ⊥-elim $ i≢i (refl i)
    swap∘swap i       (suc n) with ℕ._≟_ i (suc n)
    ... | yes i≡1+n = i≡1+n
    ... | no  i≢1+n with ℕ._≟_ i (suc n)
    ...   | yes i≡1+n = ⊥-elim $ i≢1+n i≡1+n
    ...   | no  _     = refl (suc n)

    p : ℕ → ℕ ≃ ℕ
    p i = ↔⇒≃ record
      { surjection = record
        { logical-equivalence = record { to = swap i; from = swap i }
        ; right-inverse-of    = swap∘swap i
        }
      ; left-inverse-of = swap∘swap i
      }

    p-injective : Injective p
    p-injective {x = i₁} {y = i₂} p-i₁≡p-i₂ =
      i₁         ≡⟨ refl i₁ ⟩
      swap i₁ 0  ≡⟨ cong (λ f → f 0) swap-i₁≡swap-i₂ ⟩
      swap i₂ 0  ≡⟨ refl i₂ ⟩∎
      i₂         ∎
      where
      swap-i₁≡swap-i₂ : swap i₁ ≡ swap i₂
      swap-i₁≡swap-i₂ = cong _≃_.to p-i₁≡p-i₂

  -- Set is not a set.

  ¬-Set-set : Univalence′ ℕ ℕ → ¬ Is-set Set
  ¬-Set-set univ is-set
    with equality-can-have-infinitely-many-inhabitants univ
  ... | (A , B , p , inj) =
    ℕ.0≢+ $ inj $ proj₁ $ is-set A B (p 0) (p 1)

------------------------------------------------------------------------
-- A consequence: extensionality for functions

abstract

  -- The transport theorem.

  transport-theorem :
    ∀ {p₁ p₂} (P : Set p₁ → Set p₂) →
    (resp : ∀ {A B} → A ≃ B → P A → P B) →
    (∀ {A} (p : P A) → resp Eq.id p ≡ p) →
    ∀ {A B} (univ : Univalence′ A B) →
    (A≃B : A ≃ B) (p : P A) →
    resp A≃B p ≡ subst P (≃⇒≡ univ A≃B) p
  transport-theorem P resp resp-id univ A≃B p =
    resp A≃B p              ≡⟨ sym $ cong (λ q → resp q p) (right-inverse-of A≃B) ⟩
    resp (to (from A≃B)) p  ≡⟨ elim (λ {A B} A≡B → ∀ p →
                                       resp (≡⇒≃ A≡B) p ≡ subst P A≡B p)
                                    (λ A p →
                                       resp (≡⇒≃ (refl A)) p  ≡⟨ trans (cong (λ q → resp q p) ≡⇒↝-refl) (resp-id p) ⟩
                                       p                      ≡⟨ sym $ subst-refl P p ⟩∎
                                       subst P (refl A) p     ∎) _ _ ⟩∎
    subst P (from A≃B) p    ∎
    where open _≃_ (≡≃≃ univ)

  -- If the univalence axiom holds, then any "resp" function that
  -- preserves identity is an equivalence family.

  resp-is-equivalence :
    ∀ {p₁ p₂} (P : Set p₁ → Set p₂) →
    (resp : ∀ {A B} → A ≃ B → P A → P B) →
    (∀ {A} (p : P A) → resp Eq.id p ≡ p) →
    ∀ {A B} (univ : Univalence′ A B) →
    (A≃B : A ≃ B) → Is-equivalence (resp A≃B)
  resp-is-equivalence P resp resp-id univ A≃B =
    Eq.respects-extensional-equality
      (λ p → sym $ transport-theorem P resp resp-id univ A≃B p)
      (subst-is-equivalence P (≃⇒≡ univ A≃B))

  -- If f is an equivalence, then (non-dependent) precomposition with
  -- f is also an equivalence (assuming univalence).

  precomposition-is-equivalence :
    ∀ {ℓ c} {A B : Set ℓ} {C : Set c} →
    Univalence′ B A → (A≃B : A ≃ B) →
    Is-equivalence (λ (g : B → C) → g ∘ _≃_.to A≃B)
  precomposition-is-equivalence {ℓ} {c} {C = C} univ A≃B =
    resp-is-equivalence P resp refl univ (Eq.inverse A≃B)
    where
    P : Set ℓ → Set (ℓ ⊔ c)
    P X = X → C

    resp : ∀ {A B} → A ≃ B → P A → P B
    resp A≃B p = p ∘ _≃_.from A≃B

-- If h is an equivalence, then one can cancel (non-dependent)
-- precompositions with h (assuming univalence).

precompositions-cancel :
  ∀ {ℓ c} {A B : Set ℓ} {C : Set c} →
  Univalence′ B A → (A≃B : A ≃ B) {f g : B → C} →
  let open _≃_ A≃B in
  f ∘ to ≡ g ∘ to → f ≡ g
precompositions-cancel univ A≃B {f} {g} f∘to≡g∘to =
  f            ≡⟨ sym $ left-inverse-of f ⟩
  from (to f)  ≡⟨ cong from f∘to≡g∘to ⟩
  from (to g)  ≡⟨ left-inverse-of g ⟩∎
  g            ∎
  where open _≃_ (⟨ _ , precomposition-is-equivalence univ A≃B ⟩)

-- Pairs of equal elements.

_²/≡ : ∀ {ℓ} → Set ℓ → Set ℓ
A ²/≡ = ∃ λ (x : A) → ∃ λ (y : A) → y ≡ x

-- The set of such pairs is isomorphic to the underlying type.

-²/≡↔- : ∀ {a} {A : Set a} → (A ²/≡) ↔ A
-²/≡↔- {A = A} =
  (∃ λ (x : A) → ∃ λ (y : A) → y ≡ x)  ↝⟨ ∃-cong (λ _ → inverse $ _⇔_.to contractible⇔⊤↔ (singleton-contractible _)) ⟩
  A × ⊤                                ↝⟨ ×-right-identity ⟩□
  A                                    □

abstract

  -- The univalence axiom implies non-dependent functional
  -- extensionality.

  extensionality :
    ∀ {a b} {A : Set a} {B : Set b} →
    Univalence′ (B ²/≡) B →
    {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
  extensionality {A = A} {B} univ {f} {g} f≡g =
    f          ≡⟨ refl f ⟩
    f′ ∘ pair  ≡⟨ cong (λ (h : B ²/≡ → B) → h ∘ pair) f′≡g′ ⟩
    g′ ∘ pair  ≡⟨ refl g ⟩∎
    g          ∎
    where
    f′ : B ²/≡ → B
    f′ = proj₁ ∘ proj₂

    g′ : B ²/≡ → B
    g′ = proj₁

    f′≡g′ : f′ ≡ g′
    f′≡g′ = precompositions-cancel
              univ
              (↔⇒≃ $ Bijection.inverse -²/≡↔-)
              (refl id)

    pair : A → B ²/≡
    pair x = (g x , f x , f≡g x)

  -- The univalence axiom implies that contractibility is closed under
  -- Π A.

  Π-closure-contractible :
    ∀ {b} → Univalence′ (Set b ²/≡) (Set b) →
    ∀ {a} {A : Set a} {B : A → Set b} →
    (∀ x → Univalence′ (↑ b ⊤) (B x)) →
    (∀ x → Contractible (B x)) → Contractible ((x : A) → B x)
  Π-closure-contractible {b} univ₁ {A = A} {B} univ₂ contr =
    subst Contractible A→⊤≡[x:A]→Bx →⊤-contractible
    where
    const-⊤≡B : const (↑ b ⊤) ≡ B
    const-⊤≡B = extensionality univ₁ λ x →
      _≃_.from (≡≃≃ (univ₂ x)) $ ↔⇒≃ $
        Bijection.contractible-isomorphic
          (↑-closure 0 ⊤-contractible) (contr x)

    A→⊤≡[x:A]→Bx : (A → ↑ b ⊤) ≡ ((x : A) → B x)
    A→⊤≡[x:A]→Bx = cong (λ X → (x : A) → X x) const-⊤≡B

    →⊤-contractible : Contractible (A → ↑ b ⊤)
    →⊤-contractible = (_ , λ _ → refl _)

  -- Thus we also get extensionality for dependent functions.

  dependent-extensionality :
    ∀ {b} → Univalence′ (Set b ²/≡) (Set b) →
    ∀ {a} {A : Set a} →
    (∀ {B : A → Set b} x → Univalence′ (↑ b ⊤) (B x)) →
    {B : A → Set b} → Extensionality′ A B
  dependent-extensionality univ₁ univ₂ =
    _⇔_.to Π-closure-contractible⇔extensionality
      (Π-closure-contractible univ₁ univ₂)

------------------------------------------------------------------------
-- Pow and Fam

-- Slightly different variants of Pow and Fam are described in
-- "Specifying interactions with dependent types" by Peter Hancock and
-- Anton Setzer (in APPSEM Workshop on Subtyping & Dependent Types in
-- Programming, DTP'00). The fact that Pow and Fam are logically
-- equivalent is proved in "Programming Interfaces and Basic Topology"
-- by Peter Hancock and Pierre Hyvernat (Annals of Pure and Applied
-- Logic, 2006). The results may be older than this.

-- Pow.

Pow : ∀ ℓ {a} → Set a → Set (lsuc (a ⊔ ℓ))
Pow ℓ {a} A = A → Set (a ⊔ ℓ)

-- Fam.

Fam : ∀ ℓ {a} → Set a → Set (lsuc (a ⊔ ℓ))
Fam ℓ {a} A = ∃ λ (I : Set (a ⊔ ℓ)) → I → A

-- Pow and Fam are pointwise logically equivalent.

Pow⇔Fam : ∀ ℓ {a} {A : Set a} →
          Pow ℓ A ⇔ Fam ℓ A
Pow⇔Fam _ = record
  { to   = λ P → ∃ P , proj₁
  ; from = λ { (I , f) a → ∃ λ i → f i ≡ a }
  }

-- Pow and Fam are pointwise isomorphic (assuming extensionality and
-- univalence).

Pow↔Fam : ∀ ℓ {a} {A : Set a} →
          Extensionality a (lsuc (a ⊔ ℓ)) →
          Univalence (a ⊔ ℓ) →
          Pow ℓ A ↔ Fam ℓ A
Pow↔Fam ℓ {A = A} ext univ = record
  { surjection = record
    { logical-equivalence = Pow⇔Fam ℓ
    ; right-inverse-of    = λ { (I , f) →
        let lemma₁ =
              (∃ λ a → ∃ λ i → f i ≡ a)  ↔⟨ ∃-comm ⟩
              (∃ λ i → ∃ λ a → f i ≡ a)  ↔⟨ ∃-cong (λ _ → inverse $ _⇔_.to contractible⇔⊤↔ (other-singleton-contractible _)) ⟩
              I × ⊤                      ↔⟨ ×-right-identity ⟩□
              I                          □

            lemma₂ =
              subst (λ I → I → A) (≃⇒≡ univ lemma₁) proj₁  ≡⟨ sym $ transport-theorem (λ I → I → A) (λ eq → _∘ _≃_.from eq) refl univ _ _ ⟩
              proj₁ ∘ _≃_.from lemma₁                      ≡⟨ refl _ ⟩∎
              f                                            ∎
        in
        (∃ λ a → ∃ λ i → f i ≡ a) , proj₁  ≡⟨ Σ-≡,≡→≡ (≃⇒≡ univ lemma₁) lemma₂ ⟩∎
        I                         , f      ∎ }
    }
  ; left-inverse-of = λ P →
      let lemma = λ a →
            (∃ λ (i : ∃ P) → proj₁ i ≡ a)  ↔⟨ inverse Σ-assoc ⟩
            (∃ λ a′ → P a′ × a′ ≡ a)       ↔⟨ inverse $ ∃-intro _ _ ⟩□
            P a                            □
      in
      (λ a → ∃ λ (i : ∃ P) → proj₁ i ≡ a)  ≡⟨ ext (λ a → ≃⇒≡ univ (lemma a)) ⟩∎
      P                                    ∎
  }

-- An isomorphism that follows from Pow↔Fam.
--
-- This isomorphism was suggested to me by Paolo Capriotti.

→↔Σ≃Σ :
  ∀ ℓ {a b} {A : Set a} {B : Set b} →
  Extensionality (a ⊔ b ⊔ ℓ) (lsuc (a ⊔ b ⊔ ℓ)) →
  Univalence (a ⊔ b ⊔ ℓ) →
  (A → B) ↔ ∃ λ (P : B → Set (a ⊔ b ⊔ ℓ)) → A ≃ Σ B P
→↔Σ≃Σ ℓ {a} {b} {A} {B} ext univ =
  (A → B)                                                   ↝⟨ →-cong (lower-extensionality lzero _ ext) (inverse Bijection.↑↔) F.id ⟩
  (↑ (b ⊔ ℓ) A → B)                                         ↝⟨ inverse ×-left-identity ⟩
  ⊤ × (↑ _ A → B)                                           ↝⟨ _⇔_.to contractible⇔⊤↔ (singleton-contractible _) ×-cong F.id ⟩
  (∃ λ (A′ : Set ℓ′) → A′ ≡ ↑ _ A) × (↑ _ A → B)            ↝⟨ inverse Σ-assoc ⟩
  (∃ λ (A′ : Set ℓ′) → A′ ≡ ↑ _ A × (↑ _ A → B))            ↝⟨ (∃-cong λ _ → ∃-cong λ eq → →-cong (lower-extensionality lzero _ ext) (≡⇒↝ _ (sym eq)) F.id) ⟩
  (∃ λ (A′ : Set ℓ′) → A′ ≡ ↑ _ A × (A′ → B))               ↝⟨ (∃-cong λ _ → ×-comm) ⟩
  (∃ λ (A′ : Set ℓ′) → (A′ → B) × A′ ≡ ↑ _ A)               ↝⟨ Σ-assoc ⟩
  (∃ λ (p : ∃ λ (A′ : Set ℓ′) → A′ → B) → proj₁ p ≡ ↑ _ A)  ↝⟨ inverse $ Σ-cong (Pow↔Fam (a ⊔ ℓ) (lower-extensionality ℓ′ lzero ext) univ) (λ _ → F.id) ⟩
  (∃ λ (P : B → Set ℓ′) → ∃ P ≡ ↑ _ A)                      ↔⟨ (∃-cong λ _ → ≡≃≃ univ) ⟩
  (∃ λ (P : B → Set ℓ′) → ∃ P ≃ ↑ _ A)                      ↝⟨ (∃-cong λ _ → Groupoid.⁻¹-bijection (groupoid (lower-extensionality ℓ′ _ ext))) ⟩
  (∃ λ (P : B → Set ℓ′) → ↑ _ A ≃ ∃ P)                      ↔⟨ (∃-cong λ _ → ≃-preserves (lower-extensionality lzero _ ext) (↔⇒≃ Bijection.↑↔) F.id) ⟩□
  (∃ λ (P : B → Set ℓ′) → A ≃ ∃ P)                          □
  where
  ℓ′ = a ⊔ b ⊔ ℓ

------------------------------------------------------------------------
-- More lemmas

abstract

  -- The univalence axiom is propositional (assuming extensionality).

  Univalence′-propositional :
    ∀ {ℓ} → Extensionality (lsuc ℓ) (lsuc ℓ) →
    {A B : Set ℓ} → Is-proposition (Univalence′ A B)
  Univalence′-propositional ext =
    Eq.propositional ext ≡⇒≃

  Univalence-propositional :
    ∀ {ℓ} → Extensionality (lsuc ℓ) (lsuc ℓ) →
    Is-proposition (Univalence ℓ)
  Univalence-propositional ext =
    implicit-Π-closure ext 1 λ _ →
    implicit-Π-closure ext 1 λ _ →
    Univalence′-propositional ext

  -- "Evaluation rule" for ≡⇒≃.

  ≡⇒≃-refl : ∀ {a} {A : Set a} →
             ≡⇒≃ (refl A) ≡ Eq.id
  ≡⇒≃-refl = ≡⇒↝-refl

  -- "Evaluation rule" for ≡⇒→.

  ≡⇒→-refl : ∀ {a} {A : Set a} →
             ≡⇒→ (refl A) ≡ id
  ≡⇒→-refl = cong _≃_.to ≡⇒≃-refl

  -- "Evaluation rule" (?) for ≃⇒≡.

  ≃⇒≡-id : ∀ {a} {A : Set a}
           (univ : Univalence′ A A) →
           ≃⇒≡ univ Eq.id ≡ refl A
  ≃⇒≡-id univ =
    ≃⇒≡ univ Eq.id           ≡⟨ sym $ cong (≃⇒≡ univ) ≡⇒≃-refl ⟩
    ≃⇒≡ univ (≡⇒≃ (refl _))  ≡⟨ _≃_.left-inverse-of (≡≃≃ univ) _ ⟩∎
    refl _                   ∎

  -- Simplification lemma for ≃⇒≡.

  ≡⇒→-≃⇒≡ : ∀ k {ℓ} {A B : Set ℓ} {eq : A ≃ B}
            (univ : Univalence′ A B) →
            to-implication (≡⇒↝ k (≃⇒≡ univ eq)) ≡ _≃_.to eq
  ≡⇒→-≃⇒≡ k {eq = eq} univ =
    to-implication (≡⇒↝ k (≃⇒≡ univ eq))  ≡⟨ to-implication-≡⇒↝ k _ ⟩
    ≡⇒↝ implication (≃⇒≡ univ eq)         ≡⟨ sym $ to-implication-≡⇒↝ equivalence _ ⟩
    ≡⇒→ (≃⇒≡ univ eq)                     ≡⟨ cong _≃_.to (_≃_.right-inverse-of (≡≃≃ univ) _) ⟩∎
    _≃_.to eq                             ∎

  -- ≡⇒≃ commutes with sym/Eq.inverse (assuming extensionality).

  ≡⇒≃-sym :
    ∀ {ℓ} → Extensionality ℓ ℓ →
    {A B : Set ℓ} (A≡B : A ≡ B) →
    ≡⇒≃ (sym A≡B) ≡ Eq.inverse (≡⇒≃ A≡B)
  ≡⇒≃-sym ext = elim¹

    (λ eq → ≡⇒≃ (sym eq) ≡ Eq.inverse (≡⇒≃ eq))

    (≡⇒≃ (sym (refl _))         ≡⟨ cong ≡⇒≃ sym-refl ⟩
     ≡⇒≃ (refl _)               ≡⟨ ≡⇒≃-refl ⟩
     Eq.id                      ≡⟨ sym $ Groupoid.identity (Eq.groupoid ext) ⟩
     Eq.inverse Eq.id           ≡⟨ cong Eq.inverse $ sym ≡⇒≃-refl ⟩∎
     Eq.inverse (≡⇒≃ (refl _))  ∎)

  -- ≃⇒≡ univ commutes with Eq.inverse/sym (assuming extensionality).

  ≃⇒≡-inverse :
    ∀ {ℓ} (univ : Univalence ℓ) → Extensionality ℓ ℓ →
    {A B : Set ℓ} (A≃B : A ≃ B) →
    ≃⇒≡ univ (Eq.inverse A≃B) ≡ sym (≃⇒≡ univ A≃B)
  ≃⇒≡-inverse univ ext A≃B =
    ≃⇒≡ univ (Eq.inverse A≃B)                   ≡⟨ sym $ cong (λ p → ≃⇒≡ univ (Eq.inverse p)) (_≃_.right-inverse-of (≡≃≃ univ) _) ⟩
    ≃⇒≡ univ (Eq.inverse (≡⇒≃ (≃⇒≡ univ A≃B)))  ≡⟨ cong (≃⇒≡ univ) $ sym $ ≡⇒≃-sym ext _ ⟩
    ≃⇒≡ univ (≡⇒≃ (sym (≃⇒≡ univ A≃B)))         ≡⟨ _≃_.left-inverse-of (≡≃≃ univ) _ ⟩∎
    sym (≃⇒≡ univ A≃B)                          ∎

  -- ≡⇒≃ commutes with trans/_⊚_ (assuming extensionality).

  ≡⇒≃-trans :
    ∀ {ℓ} → Extensionality ℓ ℓ →
    {A B C : Set ℓ} (A≡B : A ≡ B) (B≡C : B ≡ C) →
    ≡⇒≃ (trans A≡B B≡C) ≡ ≡⇒≃ B≡C ⊚ ≡⇒≃ A≡B
  ≡⇒≃-trans ext A≡B = elim¹

    (λ eq → ≡⇒≃ (trans A≡B eq) ≡ ≡⇒≃ eq ⊚ ≡⇒≃ A≡B)

    (≡⇒≃ (trans A≡B (refl _))  ≡⟨ cong ≡⇒≃ $ trans-reflʳ _ ⟩
     ≡⇒≃ A≡B                   ≡⟨ sym $ Groupoid.left-identity (Eq.groupoid ext) _ ⟩
     Eq.id ⊚ ≡⇒≃ A≡B           ≡⟨ sym $ cong (λ eq → eq ⊚ ≡⇒≃ A≡B) ≡⇒≃-refl ⟩∎
     ≡⇒≃ (refl _) ⊚ ≡⇒≃ A≡B    ∎)

  -- ≃⇒≡ univ commutes with _⊚_/flip trans (assuming extensionality).

  ≃⇒≡-∘ :
    ∀ {ℓ} (univ : Univalence ℓ) → Extensionality ℓ ℓ →
    {A B C : Set ℓ} (A≃B : A ≃ B) (B≃C : B ≃ C) →
    ≃⇒≡ univ (B≃C ⊚ A≃B) ≡ trans (≃⇒≡ univ A≃B) (≃⇒≡ univ B≃C)
  ≃⇒≡-∘ univ ext A≃B B≃C =
    ≃⇒≡ univ (B≃C ⊚ A≃B)                                  ≡⟨ sym $ cong₂ (λ p q → ≃⇒≡ univ (p ⊚ q)) (_≃_.right-inverse-of (≡≃≃ univ) _)
                                                                                                    (_≃_.right-inverse-of (≡≃≃ univ) _) ⟩
    ≃⇒≡ univ (≡⇒≃ (≃⇒≡ univ B≃C) ⊚ ≡⇒≃ (≃⇒≡ univ A≃B))    ≡⟨ cong (≃⇒≡ univ) $ sym $ ≡⇒≃-trans ext _ _ ⟩
    ≃⇒≡ univ (≡⇒≃ (trans (≃⇒≡ univ A≃B) (≃⇒≡ univ B≃C)))  ≡⟨ _≃_.left-inverse-of (≡≃≃ univ) _ ⟩∎
    trans (≃⇒≡ univ A≃B) (≃⇒≡ univ B≃C)                   ∎

  -- A variant of the transport theorem.

  transport-theorem′ :
    ∀ {a p r} {A : Set a}
    (P : A → Set p) (R : A → A → Set r)
    (≡↠R : ∀ {x y} → (x ≡ y) ↠ R x y)
    (resp : ∀ {x y} → R x y → P x → P y) →
    (∀ x p → resp (_↠_.to ≡↠R (refl x)) p ≡ p) →
    ∀ {x y} (r : R x y) (p : P x) →
    resp r p ≡ subst P (_↠_.from ≡↠R r) p
  transport-theorem′ P R ≡↠R resp hyp r p =
    resp r p              ≡⟨ sym $ cong (λ r → resp r p) (right-inverse-of r) ⟩
    resp (to (from r)) p  ≡⟨ elim (λ {x y} x≡y → ∀ p →
                                     resp (_↠_.to ≡↠R x≡y) p ≡ subst P x≡y p)
                                  (λ x p →
                                     resp (_↠_.to ≡↠R (refl x)) p  ≡⟨ hyp x p ⟩
                                     p                             ≡⟨ sym $ subst-refl P p ⟩∎
                                     subst P (refl x) p            ∎) _ _ ⟩∎
    subst P (from r) p    ∎
    where open _↠_ ≡↠R

  -- Simplification (?) lemma for transport-theorem′.

  transport-theorem′-refl :
    ∀ {a p r} {A : Set a}
    (P : A → Set p) (R : A → A → Set r)
    (≡≃R : ∀ {x y} → (x ≡ y) ≃ R x y)
    (resp : ∀ {x y} → R x y → P x → P y) →
    (resp-refl : ∀ x p → resp (_≃_.to ≡≃R (refl x)) p ≡ p) →
    ∀ {x} (p : P x) →
    transport-theorem′ P R (_≃_.surjection ≡≃R) resp resp-refl
                       (_≃_.to ≡≃R (refl x)) p ≡
    trans (trans (resp-refl x p) (sym $ subst-refl P p))
          (sym $ cong (λ eq → subst P eq p)
                      (_≃_.left-inverse-of ≡≃R (refl x)))
  transport-theorem′-refl P R ≡≃R resp resp-refl {x} p =

    let body = λ x p → trans (resp-refl x p) (sym $ subst-refl P p)

        lemma =
          trans (sym $ cong (λ r → resp (to r) p) $ refl (refl x))
                (elim (λ {x y} x≡y →
                         ∀ p → resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                      (λ x p → trans (resp-refl x p)
                                     (sym $ subst-refl P p))
                      (refl x) p)                                        ≡⟨ cong₂ (λ q r → trans q (r p))
                                                                                  (sym $ cong-sym (λ r → resp (to r) p) _)
                                                                                  (elim-refl (λ {x y} x≡y → ∀ p →
                                                                                                resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p) _) ⟩
          trans (cong (λ r → resp (to r) p) $ sym $ refl (refl x))
                (body x p)                                               ≡⟨ cong (λ q → trans (cong (λ r → resp (to r) p) q) (body x p))
                                                                                 sym-refl ⟩
          trans (cong (λ r → resp (to r) p) $ refl (refl x)) (body x p)  ≡⟨ cong (λ q → trans q (body x p)) $
                                                                                 cong-refl (λ r → resp (to r) p) ⟩
          trans (refl (resp (to (refl x)) p)) (body x p)                 ≡⟨ trans-reflˡ _ ⟩

          body x p                                                       ≡⟨ sym $ trans-reflʳ _ ⟩

          trans (body x p) (refl (subst P (refl x) p))                   ≡⟨ cong (trans (body x p)) $ sym $
                                                                                 cong-refl (λ eq → subst P eq p) ⟩
          trans (body x p)
                (cong (λ eq → subst P eq p) (refl (refl x)))             ≡⟨ cong (trans (body x p) ∘ cong (λ eq → subst P eq p)) $
                                                                                 sym sym-refl ⟩
          trans (body x p)
                (cong (λ eq → subst P eq p) (sym (refl (refl x))))       ≡⟨ cong (trans (body x p)) $ cong-sym (λ eq → subst P eq p) _ ⟩∎

          trans (body x p)
                (sym $ cong (λ eq → subst P eq p) (refl (refl x)))       ∎
    in

    trans (sym $ cong (λ r → resp r p) $ right-inverse-of (to (refl x)))
          (elim (λ {x y} x≡y →
                   ∀ p → resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                body (from (to (refl x))) p)                              ≡⟨ cong (λ eq → trans (sym $ cong (λ r → resp r p) eq)
                                                                                                (elim (λ {x y} x≡y → ∀ p →
                                                                                                         resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                                                                                                      body (from (to (refl x))) p)) $
                                                                                  sym $ left-right-lemma (refl x) ⟩
    trans (sym $ cong (λ r → resp r p) $ cong to $
             left-inverse-of (refl x))
          (elim (λ {x y} x≡y →
                   ∀ p → resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                body (from (to (refl x))) p)                              ≡⟨ cong (λ eq → trans (sym eq)
                                                                                                (elim (λ {x y} x≡y → ∀ p →
                                                                                                         resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                                                                                                      body (from (to (refl x))) p)) $
                                                                                  cong-∘ (λ r → resp r p) to _ ⟩
    trans (sym $ cong (λ r → resp (to r) p) $ left-inverse-of (refl x))
          (elim (λ {x y} x≡y →
                   ∀ p → resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                body (from (to (refl x))) p)                              ≡⟨ elim₁ (λ {q} eq → trans (sym $ cong (λ r → resp (to r) p) eq)
                                                                                                     (elim (λ {x y} x≡y → ∀ p →
                                                                                                              resp (_≃_.to ≡≃R x≡y) p ≡
                                                                                                              subst P x≡y p)
                                                                                                           body q p) ≡
                                                                                               trans (body x p)
                                                                                                     (sym $ cong (λ eq → subst P eq p) eq))
                                                                                   lemma
                                                                                   (left-inverse-of (refl x)) ⟩∎

    trans (body x p)
          (sym $ cong (λ eq → subst P eq p) (left-inverse-of (refl x)))   ∎

    where open _≃_ ≡≃R

  -- Simplification (?) lemma for transport-theorem.

  transport-theorem-≡⇒≃-refl :
    ∀ {p₁ p₂} (P : Set p₁ → Set p₂)
    (resp : ∀ {A B} → A ≃ B → P A → P B)
    (resp-id : ∀ {A} (p : P A) → resp Eq.id p ≡ p)
    (univ : Univalence p₁) {A} (p : P A) →
    transport-theorem P resp resp-id univ (≡⇒≃ (refl A)) p ≡
    trans (trans (trans (cong (λ eq → resp eq p) ≡⇒≃-refl)
                    (resp-id p))
             (sym $ subst-refl P p))
      (sym $ cong (λ eq → subst P eq p)
                  (_≃_.left-inverse-of (≡≃≃ univ) (refl A)))
  transport-theorem-≡⇒≃-refl P resp resp-id univ {A} p =
    transport-theorem′-refl P _≃_ (≡≃≃ univ) resp
      (λ _ p → trans (cong (λ eq → resp eq p) ≡⇒≃-refl) (resp-id p)) p

  -- A variant of resp-is-equivalence.

  resp-is-equivalence′ :
    ∀ {a p r} {A : Set a}
    (P : A → Set p) (R : A → A → Set r)
    (≡↠R : ∀ {x y} → (x ≡ y) ↠ R x y)
    (resp : ∀ {x y} → R x y → P x → P y) →
    (∀ x p → resp (_↠_.to ≡↠R (refl x)) p ≡ p) →
    ∀ {x y} (r : R x y) → Is-equivalence (resp r)
  resp-is-equivalence′ P R ≡↠R resp hyp r =
    Eq.respects-extensional-equality
      (λ p → sym $ transport-theorem′ P R ≡↠R resp hyp r p)
      (subst-is-equivalence P (_↠_.from ≡↠R r))

  -- A lemma relating ≃⇒≡, →-cong and cong₂.

  ≃⇒≡-→-cong :
    ∀ {ℓ} {A₁ A₂ B₁ B₂ : Set ℓ}
    (ext : Extensionality ℓ ℓ) →
    (univ : Univalence ℓ)
    (A₁≃A₂ : A₁ ≃ A₂) (B₁≃B₂ : B₁ ≃ B₂) →
    ≃⇒≡ univ (→-cong ext A₁≃A₂ B₁≃B₂) ≡
      cong₂ (λ A B → A → B) (≃⇒≡ univ A₁≃A₂) (≃⇒≡ univ B₁≃B₂)
  ≃⇒≡-→-cong {A₂ = A₂} {B₁} ext univ A₁≃A₂ B₁≃B₂ =
    ≃⇒≡ univ (→-cong ext A₁≃A₂ B₁≃B₂)                        ≡⟨ cong (≃⇒≡ univ) (lift-equality ext lemma) ⟩

    ≃⇒≡ univ (≡⇒≃ (cong₂ (λ A B → A → B) (≃⇒≡ univ A₁≃A₂)
                                         (≃⇒≡ univ B₁≃B₂)))  ≡⟨ left-inverse-of (≡≃≃ univ) _ ⟩∎

    cong₂ (λ A B → A → B) (≃⇒≡ univ A₁≃A₂) (≃⇒≡ univ B₁≃B₂)  ∎
    where
    open _≃_

    lemma :
      (λ f → to B₁≃B₂ ∘ f ∘ from A₁≃A₂) ≡
      to (≡⇒≃ (cong₂ (λ A B → A → B) (≃⇒≡ univ A₁≃A₂)
                                     (≃⇒≡ univ B₁≃B₂)))
    lemma =
      (λ f → to B₁≃B₂ ∘ f ∘ from A₁≃A₂)                  ≡⟨ ext (λ _ → transport-theorem (λ B → A₂ → B) (λ A≃B g → _≃_.to A≃B ∘ g)
                                                                                         refl univ B₁≃B₂ _) ⟩
      subst (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂) ∘
      (λ f → f ∘ from A₁≃A₂)                             ≡⟨ cong (_∘_ (subst (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂))) (ext λ f →
                                                              transport-theorem (λ A → A → B₁) (λ A≃B g → g ∘ _≃_.from A≃B) refl univ A₁≃A₂ f) ⟩
      subst (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂) ∘
      subst (λ A → A → B₁) (≃⇒≡ univ A₁≃A₂)              ≡⟨ cong₂ (λ g h f → g (h f)) (ext $ subst-in-terms-of-≡⇒↝ equivalence _ (λ B → A₂ → B))
                                                                                      (ext $ subst-in-terms-of-≡⇒↝ equivalence _ (λ A → A → B₁)) ⟩
      to (≡⇒≃ (cong (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂))) ∘
      to (≡⇒≃ (cong (λ A → A → B₁) (≃⇒≡ univ A₁≃A₂)))    ≡⟨⟩

      to (≡⇒≃ (cong (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂)) ⊚
          ≡⇒≃ (cong (λ A → A → B₁) (≃⇒≡ univ A₁≃A₂)))    ≡⟨ cong to $ sym $ ≡⇒≃-trans ext _ _ ⟩∎

      to (≡⇒≃ (cong₂ (λ A B → A → B) (≃⇒≡ univ A₁≃A₂)
                                     (≃⇒≡ univ B₁≃B₂)))  ∎

  -- One can sometimes push cong through ≃⇒≡ (assuming
  -- extensionality).

  cong-≃⇒≡ :
    ∀ {ℓ p} {A B : Set ℓ} {A≃B : A ≃ B} →
    Extensionality p p →
    (univ₁ : Univalence ℓ)
    (univ₂ : Univalence p)
    (P : Set ℓ → Set p)
    (P-cong : ∀ {A B} → A ≃ B → P A ≃ P B) →
    (∀ {A} (p : P A) → _≃_.to (P-cong Eq.id) p ≡ p) →
    cong P (≃⇒≡ univ₁ A≃B) ≡ ≃⇒≡ univ₂ (P-cong A≃B)
  cong-≃⇒≡ {A≃B = A≃B} ext univ₁ univ₂ P P-cong P-cong-id =
    cong P (≃⇒≡ univ₁ A≃B)                    ≡⟨ sym $ _≃_.left-inverse-of (≡≃≃ univ₂) _ ⟩
    ≃⇒≡ univ₂ (≡⇒≃ (cong P (≃⇒≡ univ₁ A≃B)))  ≡⟨ cong (≃⇒≡ univ₂) $ lift-equality ext lemma ⟩∎
    ≃⇒≡ univ₂ (P-cong A≃B)                    ∎
    where
    lemma : ≡⇒→ (cong P (≃⇒≡ univ₁ A≃B)) ≡ _≃_.to (P-cong A≃B)
    lemma = ext λ x →
      ≡⇒→ (cong P (≃⇒≡ univ₁ A≃B)) x  ≡⟨ sym $ subst-in-terms-of-≡⇒↝ equivalence _ P x ⟩
      subst P (≃⇒≡ univ₁ A≃B) x       ≡⟨ sym $ transport-theorem P (_≃_.to ∘ P-cong) P-cong-id univ₁ A≃B x ⟩∎
      _≃_.to (P-cong A≃B) x           ∎

  -- Any "resp" function that preserves identity also preserves
  -- compositions (assuming univalence and extensionality).

  resp-preserves-compositions :
    ∀ {p₁ p₂} (P : Set p₁ → Set p₂) →
    (resp : ∀ {A B} → A ≃ B → P A → P B) →
    (∀ {A} (p : P A) → resp Eq.id p ≡ p) →
    Univalence p₁ → Extensionality p₁ p₁ →
    ∀ {A B C} (A≃B : A ≃ B) (B≃C : B ≃ C) p →
    resp (B≃C ⊚ A≃B) p ≡ (resp B≃C ∘ resp A≃B) p
  resp-preserves-compositions P resp resp-id univ ext A≃B B≃C p =
    resp (B≃C ⊚ A≃B) p                                 ≡⟨ transport-theorem P resp resp-id univ _ _ ⟩
    subst P (≃⇒≡ univ (B≃C ⊚ A≃B)) p                   ≡⟨ cong (λ eq → subst P eq p) $ ≃⇒≡-∘ univ ext A≃B B≃C ⟩
    subst P (trans (≃⇒≡ univ A≃B) (≃⇒≡ univ B≃C)) p    ≡⟨ sym $ subst-subst P _ _ _ ⟩
    subst P (≃⇒≡ univ B≃C) (subst P (≃⇒≡ univ A≃B) p)  ≡⟨ sym $ transport-theorem P resp resp-id univ _ _ ⟩
    resp B≃C (subst P (≃⇒≡ univ A≃B) p)                ≡⟨ sym $ cong (resp _) $ transport-theorem P resp resp-id univ _ _ ⟩∎
    resp B≃C (resp A≃B p)                              ∎

  -- Any "resp" function that preserves identity also preserves
  -- inverses (assuming univalence and extensionality).

  resp-preserves-inverses :
    ∀ {p₁ p₂} (P : Set p₁ → Set p₂) →
    (resp : ∀ {A B} → A ≃ B → P A → P B) →
    (∀ {A} (p : P A) → resp Eq.id p ≡ p) →
    Univalence p₁ → Extensionality p₁ p₁ →
    ∀ {A B} (A≃B : A ≃ B) p q →
    resp A≃B p ≡ q → resp (inverse A≃B) q ≡ p
  resp-preserves-inverses P resp resp-id univ ext A≃B p q eq =
    let lemma =
          q                                     ≡⟨ sym eq ⟩
          resp A≃B p                            ≡⟨ transport-theorem P resp resp-id univ _ _ ⟩
          subst P (≃⇒≡ univ A≃B) p              ≡⟨ cong (λ eq → subst P eq p) $ sym $ sym-sym _ ⟩∎
          subst P (sym (sym (≃⇒≡ univ A≃B))) p  ∎
    in

    resp (inverse A≃B) q                                                 ≡⟨ transport-theorem P resp resp-id univ _ _ ⟩
    subst P (≃⇒≡ univ (inverse A≃B)) q                                   ≡⟨ cong (λ eq → subst P eq q) $ ≃⇒≡-inverse univ ext A≃B ⟩
    subst P (sym (≃⇒≡ univ A≃B)) q                                       ≡⟨ cong (subst P (sym (≃⇒≡ univ A≃B))) lemma ⟩
    subst P (sym (≃⇒≡ univ A≃B)) (subst P (sym (sym (≃⇒≡ univ A≃B))) p)  ≡⟨ subst-subst-sym P _ _ ⟩∎
    p                                                                    ∎

-- Equality preserves equivalences (assuming extensionality and
-- univalence).

≡-preserves-≃ :
  ∀ {ℓ₁ ℓ₂} {A₁ : Set ℓ₁} {A₂ : Set ℓ₂} {B₁ : Set ℓ₁} {B₂ : Set ℓ₂} →
  Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
  Univalence′ A₁ B₁ →
  Univalence′ A₂ B₂ →
  A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ ≡ B₁) ≃ (A₂ ≡ B₂)
≡-preserves-≃ {ℓ₁} {ℓ₂} {A₁} {A₂} {B₁} {B₂}
              ext univ₁ univ₂ A₁≃A₂ B₁≃B₂ = ↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  })
  where
  to = λ A₁≡B₁ → ≃⇒≡ univ₂ (
    A₂  ↝⟨ inverse A₁≃A₂ ⟩
    A₁  ↝⟨ ≡⇒≃ A₁≡B₁ ⟩
    B₁  ↝⟨ B₁≃B₂ ⟩□
    B₂  □)

  from = λ A₂≡B₂ → ≃⇒≡ univ₁ (
    A₁  ↝⟨ A₁≃A₂ ⟩
    A₂  ↝⟨ ≡⇒≃ A₂≡B₂ ⟩
    B₂  ↝⟨ inverse B₁≃B₂ ⟩□
    B₁  □)

  abstract

    to∘from : ∀ eq → to (from eq) ≡ eq
    to∘from A₂≡B₂ =
      let ext₂ = lower-extensionality ℓ₁ ℓ₁ ext in

      _≃_.to (≃-≡ (≡≃≃ univ₂)) (lift-equality ext₂ (

        ≡⇒→ (≃⇒≡ univ₂ ((B₁≃B₂ ⊚ ≡⇒≃ (≃⇒≡ univ₁ ((inverse B₁≃B₂ ⊚
                             ≡⇒≃ A₂≡B₂) ⊚ A₁≃A₂))) ⊚ inverse A₁≃A₂))  ≡⟨ cong _≃_.to $ _≃_.right-inverse-of (≡≃≃ univ₂) _ ⟩

        (_≃_.to B₁≃B₂ ∘
         ≡⇒→ (≃⇒≡ univ₁ ((inverse B₁≃B₂ ⊚ ≡⇒≃ A₂≡B₂) ⊚ A₁≃A₂)) ∘
         _≃_.from A₁≃A₂)                                              ≡⟨ cong (λ eq → _≃_.to B₁≃B₂ ∘ _≃_.to eq ∘ _≃_.from A₁≃A₂) $
                                                                           _≃_.right-inverse-of (≡≃≃ univ₁) _ ⟩
        ((_≃_.to B₁≃B₂ ∘ _≃_.from B₁≃B₂) ∘ ≡⇒→ A₂≡B₂ ∘
         (_≃_.to A₁≃A₂ ∘ _≃_.from A₁≃A₂))                             ≡⟨ cong₂ (λ f g → f ∘ ≡⇒→ A₂≡B₂ ∘ g)
                                                                               (ext₂ $ _≃_.right-inverse-of B₁≃B₂)
                                                                               (ext₂ $ _≃_.right-inverse-of A₁≃A₂) ⟩∎
        ≡⇒→ A₂≡B₂                                                     ∎))

    from∘to : ∀ eq → from (to eq) ≡ eq
    from∘to A₁≡B₁ =
      let ext₁ = lower-extensionality ℓ₂ ℓ₂ ext in

      _≃_.to (≃-≡ (≡≃≃ univ₁)) (lift-equality ext₁ (

        ≡⇒→ (≃⇒≡ univ₁ ((inverse B₁≃B₂ ⊚ ≡⇒≃ (≃⇒≡ univ₂ ((B₁≃B₂ ⊚
                             ≡⇒≃ A₁≡B₁) ⊚ inverse A₁≃A₂))) ⊚ A₁≃A₂))  ≡⟨ cong _≃_.to $ _≃_.right-inverse-of (≡≃≃ univ₁) _ ⟩

        (_≃_.from B₁≃B₂ ∘
         ≡⇒→ (≃⇒≡ univ₂ ((B₁≃B₂ ⊚ ≡⇒≃ A₁≡B₁) ⊚ inverse A₁≃A₂)) ∘
         _≃_.to A₁≃A₂)                                                ≡⟨ cong (λ eq → _≃_.from B₁≃B₂ ∘ _≃_.to eq ∘ _≃_.to A₁≃A₂) $
                                                                           _≃_.right-inverse-of (≡≃≃ univ₂) _ ⟩
        ((_≃_.from B₁≃B₂ ∘ _≃_.to B₁≃B₂) ∘ ≡⇒→ A₁≡B₁ ∘
         (_≃_.from A₁≃A₂ ∘ _≃_.to A₁≃A₂))                             ≡⟨ cong₂ (λ f g → f ∘ ≡⇒→ A₁≡B₁ ∘ g)
                                                                               (ext₁ $ _≃_.left-inverse-of B₁≃B₂)
                                                                               (ext₁ $ _≃_.left-inverse-of A₁≃A₂) ⟩∎
        ≡⇒→ A₁≡B₁                                                     ∎))

-- Singletons expressed using equivalences instead of equalities are
-- isomorphic to the unit type (assuming extensionality and
-- univalence).

singleton-with-≃-↔-⊤ :
  ∀ {a b} {B : Set b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Univalence (a ⊔ b) →
  (∃ λ (A : Set (a ⊔ b)) → A ≃ B) ↔ ⊤
singleton-with-≃-↔-⊤ {a} {B = B} ext univ =
  (∃ λ A → A ≃ B)      ↝⟨ inverse (∃-cong λ _ → Eq.≃-preserves-bijections ext F.id Bijection.↑↔) ⟩
  (∃ λ A → A ≃ ↑ a B)  ↔⟨ inverse (∃-cong λ _ → ≡≃≃ univ) ⟩
  (∃ λ A → A ≡ ↑ a B)  ↝⟨ inverse $ _⇔_.to contractible⇔⊤↔ (singleton-contractible _) ⟩□
  ⊤                    □

other-singleton-with-≃-↔-⊤ :
  ∀ {a b} {A : Set a} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Univalence (a ⊔ b) →
  (∃ λ (B : Set (a ⊔ b)) → A ≃ B) ↔ ⊤
other-singleton-with-≃-↔-⊤ {b = b} {A} ext univ =
  (∃ λ B → A ≃ B)  ↝⟨ (∃-cong λ _ → inverse-isomorphism ext) ⟩
  (∃ λ B → B ≃ A)  ↝⟨ singleton-with-≃-↔-⊤ {a = b} ext univ ⟩□
  ⊤                □

-- ∃ Contractible is isomorphic to the unit type (assuming
-- extensionality and univalence).

∃Contractible↔⊤ :
  ∀ {a} →
  Extensionality a a →
  Univalence a →
  (∃ λ (A : Set a) → Contractible A) ↔ ⊤
∃Contractible↔⊤ ext univ =
  (∃ λ A → Contractible A)  ↝⟨ (∃-cong λ _ → contractible↔⊤≃ ext) ⟩
  (∃ λ A → ⊤ ≃ A)           ↝⟨ other-singleton-with-≃-↔-⊤ ext univ ⟩
  ⊤                         □

-- ∃ λ A → H-level n A has h-level 1 + n (assuming extensionality and
-- univalence).

∃-H-level-H-level-1+ :
  ∀ {a} →
  Extensionality a a →
  Univalence a →
  ∀ n → H-level (1 + n) (∃ λ (A : Set a) → H-level n A)
∃-H-level-H-level-1+ ext univ n (A₁ , h₁) (A₂ , h₂) =
                                     $⟨ h₁ , h₂ ⟩
  H-level n A₁ × H-level n A₂        ↝⟨ uncurry (Eq.h-level-closure ext n) ⟩
  H-level n (A₁ ≃ A₂)                ↝⟨ H-level.respects-surjection (_≃_.surjection $ inverse $ ≡≃≃ univ) n ⟩
  H-level n (A₁ ≡ A₂)                ↝⟨ H-level.respects-surjection
                                          (_↔_.surjection $ ignore-propositional-component
                                                              (H-level-propositional ext _)) n ⟩□
  H-level n ((A₁ , h₁) ≡ (A₂ , h₂))  □

-- ∃ λ A → H-level n A does not in general have h-level n.
--
-- (Kraus and Sattler show that, for all n,
-- ∃ λ (A : Set (# n)) → H-level (2 + n) A does not have h-level
-- 2 + n, assuming univalence. See "Higher Homotopies in a Hierarchy
-- of Univalent Universes".)

¬-∃-H-level-H-level :
  ∀ {a} →
  ¬ (∀ n → H-level n (∃ λ (A : Set a) → H-level n A))
¬-∃-H-level-H-level =
  (∀ n → H-level n (∃ λ A → H-level n A))                 ↝⟨ _$ 1 ⟩
  Is-proposition (∃ λ A → Is-proposition A)               ↝⟨ _⇔_.to propositional⇔irrelevant ⟩
  ((p q : ∃ λ A → Is-proposition A) → p ≡ q)              ↝⟨ (λ f p q → cong proj₁ (f p q)) ⟩
  ((p q : ∃ λ A → Is-proposition A) → proj₁ p ≡ proj₁ q)  ↝⟨ (_$ (⊥ , ⊥-propositional)) ∘
                                                             (_$ (↑ _ ⊤ , ↑-closure 1 (mono₁ 0 ⊤-contractible))) ⟩
  ↑ _ ⊤ ≡ ⊥                                               ↝⟨ flip (subst id) _ ⟩
  ⊥                                                       ↝⟨ ⊥-elim ⟩□
  ⊥₀                                                      □

-- A certain type of uninhabited types is isomorphic to the unit type
-- (assuming extensionality and univalence).

∃¬↔⊤ :
  ∀ {a} →
  Extensionality a a →
  Univalence a →
  (∃ λ (A : Set a) → ¬ A) ↔ ⊤
∃¬↔⊤ ext univ =
  (∃ λ A → ¬ A)     ↔⟨ inverse (∃-cong λ _ → ≃⊥≃¬ ext) ⟩
  (∃ λ A → A ≃ ⊥₀)  ↔⟨ singleton-with-≃-↔-⊤ ext univ ⟩
  ⊤                 □
