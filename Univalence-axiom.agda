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
open import Equivalence hiding (id; _∘_; inverse)
open import Function-universe eq hiding (id; _∘_)
open import Groupoid eq
open import H-level eq
open import H-level.Closure eq
open import Injection eq using (Injective)
open import Prelude
open import Surjection eq hiding (id; _∘_)
open import Weak-equivalence eq as Weak
  hiding (id; inverse) renaming (_∘_ to _⊚_)

------------------------------------------------------------------------
-- The univalence axiom

-- If two sets are equal, then they are weakly equivalent.

≡⇒≃ : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
≡⇒≃ = ≡⇒↝ weak-equivalence

-- The univalence axiom states that ≡⇒≃ is a weak equivalence.

Univalence′ : ∀ {ℓ} → Set ℓ → Set ℓ → Set (lsuc ℓ)
Univalence′ A B = Is-weak-equivalence (≡⇒≃ {A = A} {B = B})

Univalence : ∀ ℓ → Set (lsuc ℓ)
Univalence ℓ = {A B : Set ℓ} → Univalence′ A B

-- An immediate consequence is that equalities are weakly equivalent
-- to weak equivalences.

≡≃≃ : ∀ {ℓ} {A B : Set ℓ} → Univalence′ A B → (A ≡ B) ≃ (A ≃ B)
≡≃≃ univ = weq ≡⇒≃ univ

-- In the case of sets equalities are weakly equivalent to bijections
-- (if we add the assumption of extensionality).

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
    ... | inj₁ i≡1+n = zero
    ... | inj₂ i≢1+n = suc n

    swap∘swap : ∀ i n → swap i (swap i n) ≡ n
    swap∘swap zero    zero    = refl zero
    swap∘swap (suc i) zero    with ℕ._≟_ i i
    ... | inj₁ _   = refl 0
    ... | inj₂ i≢i = ⊥-elim $ i≢i (refl i)
    swap∘swap i       (suc n) with ℕ._≟_ i (suc n)
    ... | inj₁ i≡1+n = i≡1+n
    ... | inj₂ i≢1+n with ℕ._≟_ i (suc n)
    ...   | inj₁ i≡1+n = ⊥-elim $ i≢1+n i≡1+n
    ...   | inj₂ _     = refl (suc n)

    p : ℕ → ℕ ≃ ℕ
    p i = ↔⇒≃ record
      { surjection = record
        { equivalence      = record { to = swap i; from = swap i }
        ; right-inverse-of = swap∘swap i
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

  -- If the univalence axiom holds, then "subst P ∘ from" is unique
  -- (up to extensional equality).

  subst-unique :
    ∀ {p₁ p₂} (P : Set p₁ → Set p₂) →
    (resp : ∀ {A B} → A ≃ B → P A → P B) →
    (∀ {A} (p : P A) → resp Weak.id p ≡ p) →
    ∀ {A B} (univ : Univalence′ A B) →
    (A≃B : A ≃ B) (p : P A) →
    resp A≃B p ≡ subst P (≃⇒≡ univ A≃B) p
  subst-unique P resp resp-id univ A≃B p =
    resp A≃B p              ≡⟨ sym $ cong (λ q → resp q p) (right-inverse-of A≃B) ⟩
    resp (to (from A≃B)) p  ≡⟨ elim (λ {A B} A≡B → ∀ p →
                                       resp (≡⇒≃ A≡B) p ≡ subst P A≡B p)
                                    (λ A p →
                                       resp (≡⇒≃ (refl A)) p  ≡⟨ cong (λ q → resp q p) (elim-refl (λ {A B} _ → A ≃ B) _) ⟩
                                       resp Weak.id p         ≡⟨ resp-id p ⟩
                                       p                      ≡⟨ sym $ subst-refl P p ⟩∎
                                       subst P (refl A) p     ∎) _ _ ⟩∎
    subst P (from A≃B) p    ∎
    where open _≃_ (≡≃≃ univ)

  -- If the univalence axiom holds, then any "resp" function
  -- satisfying resp Weak.id p ≡ p is a weak equivalence family.

  resp-is-weak-equivalence :
    ∀ {p₁ p₂} (P : Set p₁ → Set p₂) →
    (resp : ∀ {A B} → A ≃ B → P A → P B) →
    (∀ {A} (p : P A) → resp Weak.id p ≡ p) →
    ∀ {A B} (univ : Univalence′ A B) →
    (A≃B : A ≃ B) → Is-weak-equivalence (resp A≃B)
  resp-is-weak-equivalence P resp resp-id univ A≃B =
    Weak.respects-extensional-equality
      (λ p → sym $ subst-unique P resp resp-id univ A≃B p)
      (subst-is-weak-equivalence P (≃⇒≡ univ A≃B))

  -- If f is a weak equivalence, then (non-dependent) precomposition
  -- with f is also a weak equivalence (assuming univalence).

  precomposition-is-weak-equivalence :
    ∀ {ℓ c} {A B : Set ℓ} {C : Set c} →
    Univalence′ B A → (A≃B : A ≃ B) →
    Is-weak-equivalence (λ (g : B → C) → g ∘ _≃_.to A≃B)
  precomposition-is-weak-equivalence {ℓ} {c} {C = C} univ A≃B =
    resp-is-weak-equivalence P resp refl univ (Weak.inverse A≃B)
    where
    P : Set ℓ → Set (ℓ ⊔ c)
    P X = X → C

    resp : ∀ {A B} → A ≃ B → P A → P B
    resp A≃B p = p ∘ _≃_.from A≃B

-- If h is a weak equivalence, then one can cancel (non-dependent)
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
  where open _≃_ (weq _ (precomposition-is-weak-equivalence univ A≃B))

-- Pairs of equal elements.

_²/≡ : ∀ {ℓ} → Set ℓ → Set ℓ
A ²/≡ = ∃ λ (x : A) → ∃ λ (y : A) → y ≡ x

-- The set of such pairs is isomorphic to the underlying type.

-²/≡↔- : ∀ {a} {A : Set a} → (A ²/≡) ↔ A
-²/≡↔- = record
  { surjection = record
    { equivalence = record
      { to   = proj₁
      ; from = λ x → (x , x , refl x)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = λ p →
      (proj₁ p , proj₁ p , refl (proj₁ p))  ≡⟨ cong (_,_ (proj₁ p))
                                                    (proj₂ (singleton-contractible (proj₁ p)) (proj₂ p)) ⟩∎
      p                                     ∎
  }

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
-- More lemmas

abstract

  -- The univalence axiom is propositional (assuming extensionality).

  Univalence′-propositional :
    ∀ {ℓ} → Extensionality (lsuc ℓ) (lsuc ℓ) →
    {A B : Set ℓ} → Propositional (Univalence′ A B)
  Univalence′-propositional ext =
    Weak.propositional ext ≡⇒≃

  Univalence-propositional :
    ∀ {ℓ} → Extensionality (lsuc ℓ) (lsuc ℓ) →
    Propositional (Univalence ℓ)
  Univalence-propositional ext =
    implicit-Π-closure ext 1 λ _ →
    implicit-Π-closure ext 1 λ _ →
    Univalence′-propositional ext

  -- A variant of subst-unique.

  subst-unique′ :
    ∀ {a p r} {A : Set a}
    (P : A → Set p) (R : A → A → Set r)
    (≡↠R : ∀ {x y} → (x ≡ y) ↠ R x y)
    (resp : ∀ {x y} → R x y → P x → P y) →
    (∀ x p → resp (_↠_.to ≡↠R (refl x)) p ≡ p) →
    ∀ {x y} (r : R x y) (p : P x) →
    resp r p ≡ subst P (_↠_.from ≡↠R r) p
  subst-unique′ P R ≡↠R resp hyp r p =
    resp r p              ≡⟨ sym $ cong (λ r → resp r p) (right-inverse-of r) ⟩
    resp (to (from r)) p  ≡⟨ elim (λ {x y} x≡y → ∀ p →
                                     resp (_↠_.to ≡↠R x≡y) p ≡ subst P x≡y p)
                                  (λ x p →
                                     resp (_↠_.to ≡↠R (refl x)) p  ≡⟨ hyp x p ⟩
                                     p                             ≡⟨ sym $ subst-refl P p ⟩∎
                                     subst P (refl x) p            ∎) _ _ ⟩∎
    subst P (from r) p    ∎
    where open _↠_ ≡↠R

  -- Simplification (?) lemma for subst-unique′.

  subst-unique′-refl :
    ∀ {a p r} {A : Set a}
    (P : A → Set p) (R : A → A → Set r)
    (≡≃R : ∀ {x y} → (x ≡ y) ≃ R x y)
    (resp : ∀ {x y} → R x y → P x → P y) →
    (resp-refl : ∀ x p → resp (_≃_.to ≡≃R (refl x)) p ≡ p) →
    ∀ {x} (p : P x) →
    subst-unique′ P R (_≃_.surjection ≡≃R) resp resp-refl
                  (_≃_.to ≡≃R (refl x)) p ≡
    trans (trans (resp-refl x p) (sym $ subst-refl P p))
          (cong (λ eq → subst P eq p)
                (sym (_≃_.left-inverse-of ≡≃R (refl x))))
  subst-unique′-refl P R ≡≃R resp resp-refl {x} p =

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
                                                                                 sym sym-refl ⟩∎
          trans (body x p)
                (cong (λ eq → subst P eq p) (sym (refl (refl x))))       ∎
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
                                                                                                     (cong (λ eq → subst P eq p) (sym eq)))
                                                                                   lemma
                                                                                   (left-inverse-of (refl x)) ⟩∎

    trans (body x p)
          (cong (λ eq → subst P eq p) (sym (left-inverse-of (refl x))))   ∎

    where open _≃_ ≡≃R

  -- A variant of resp-is-weak-equivalence.

  resp-is-weak-equivalence′ :
    ∀ {a p r} {A : Set a}
    (P : A → Set p) (R : A → A → Set r)
    (≡↠R : ∀ {x y} → (x ≡ y) ↠ R x y)
    (resp : ∀ {x y} → R x y → P x → P y) →
    (∀ x p → resp (_↠_.to ≡↠R (refl x)) p ≡ p) →
    ∀ {x y} (r : R x y) → Is-weak-equivalence (resp r)
  resp-is-weak-equivalence′ P R ≡↠R resp hyp r =
    Weak.respects-extensional-equality
      (λ p → sym $ subst-unique′ P R ≡↠R resp hyp r p)
      (subst-is-weak-equivalence P (_↠_.from ≡↠R r))

  -- "Evaluation rule" for ≡⇒≃.

  ≡⇒≃-refl : ∀ {a} {A : Set a} →
             ≡⇒≃ (refl A) ≡ Weak.id
  ≡⇒≃-refl = ≡⇒↝-refl

  -- "Evaluation rule" for ≡⇒→.

  ≡⇒→-refl : ∀ {a} {A : Set a} →
             ≡⇒→ (refl A) ≡ id
  ≡⇒→-refl = cong _≃_.to ≡⇒≃-refl

  -- "Evaluation rule" (?) for ≃⇒≡.

  ≃⇒≡-id : ∀ {a} {A : Set a}
           (univ : Univalence′ A A) →
           ≃⇒≡ univ Weak.id ≡ refl A
  ≃⇒≡-id univ =
    ≃⇒≡ univ Weak.id         ≡⟨ sym $ cong (≃⇒≡ univ) ≡⇒≃-refl ⟩
    ≃⇒≡ univ (≡⇒≃ (refl _))  ≡⟨ _≃_.left-inverse-of (≡≃≃ univ) _ ⟩∎
    refl _                   ∎

  -- ≡⇒≃ commutes with sym/Weak.inverse (assuming extensionality).

  ≡⇒≃-sym :
    ∀ {ℓ} → Extensionality ℓ ℓ →
    {A B : Set ℓ} (A≡B : A ≡ B) →
    ≡⇒≃ (sym A≡B) ≡ Weak.inverse (≡⇒≃ A≡B)
  ≡⇒≃-sym ext = elim¹

    (λ eq → ≡⇒≃ (sym eq) ≡ Weak.inverse (≡⇒≃ eq))

    (≡⇒≃ (sym (refl _))           ≡⟨ cong ≡⇒≃ sym-refl ⟩
     ≡⇒≃ (refl _)                 ≡⟨ ≡⇒≃-refl ⟩
     Weak.id                      ≡⟨ sym $ Groupoid.identity (Weak.groupoid ext) ⟩
     Weak.inverse Weak.id         ≡⟨ cong Weak.inverse $ sym ≡⇒≃-refl ⟩∎
     Weak.inverse (≡⇒≃ (refl _))  ∎)

  -- ≡⇒≃ commutes with trans/_⊚_ (assuming extensionality).

  ≡⇒≃-trans :
    ∀ {ℓ} → Extensionality ℓ ℓ →
    {A B C : Set ℓ} (A≡B : A ≡ B) (B≡C : B ≡ C) →
    ≡⇒≃ (trans A≡B B≡C) ≡ ≡⇒≃ B≡C ⊚ ≡⇒≃ A≡B
  ≡⇒≃-trans ext A≡B = elim¹

    (λ eq → ≡⇒≃ (trans A≡B eq) ≡ ≡⇒≃ eq ⊚ ≡⇒≃ A≡B)

    (≡⇒≃ (trans A≡B (refl _))  ≡⟨ cong ≡⇒≃ $ trans-reflʳ _ ⟩
     ≡⇒≃ A≡B                   ≡⟨ sym $ Groupoid.left-identity (Weak.groupoid ext) _ ⟩
     Weak.id ⊚ ≡⇒≃ A≡B         ≡⟨ sym $ cong (λ eq → eq ⊚ ≡⇒≃ A≡B) ≡⇒≃-refl ⟩∎
     ≡⇒≃ (refl _) ⊚ ≡⇒≃ A≡B    ∎)

  -- One can express subst in terms of ≡⇒≃.

  subst-in-terms-of-≡⇒≃ :
    ∀ {a p} {A : Set a} {x y} (x≡y : x ≡ y) (P : A → Set p) p →
    subst P x≡y p ≡ ≡⇒→ (cong P x≡y) p
  subst-in-terms-of-≡⇒≃ x≡y P p = elim¹

    (λ eq → subst P eq p ≡ ≡⇒→ (cong P eq) p)

    (subst P (refl _) p       ≡⟨ subst-refl P p ⟩
     p                        ≡⟨⟩
     _≃_.to Weak.id p         ≡⟨ sym $ cong (λ eq → _≃_.to eq p) ≡⇒≃-refl ⟩
     ≡⇒→ (refl _) p           ≡⟨ sym $ cong (λ eq → ≡⇒→ eq p) $ cong-refl P ⟩∎
     ≡⇒→ (cong P (refl _)) p  ∎)

    x≡y

  subst-in-terms-of-from∘≡⇒≃ :
    ∀ {a p} → Extensionality p p →
    ∀ {A : Set a} {x y} (x≡y : x ≡ y) (P : A → Set p) p →
    subst P (sym x≡y) p ≡ _≃_.from (≡⇒≃ (cong P x≡y)) p
  subst-in-terms-of-from∘≡⇒≃ ext x≡y P p =
    subst P (sym x≡y) p                ≡⟨ subst-in-terms-of-≡⇒≃ (sym x≡y) P p ⟩
    _≃_.to (≡⇒≃ (cong P (sym x≡y))) p  ≡⟨ cong (λ eq → _≃_.to (≡⇒≃ eq) p) $ cong-sym P _ ⟩
    _≃_.to (≡⇒≃ (sym $ cong P x≡y)) p  ≡⟨ cong (λ eq → _≃_.to eq p) $ ≡⇒≃-sym ext _ ⟩∎
    _≃_.from (≡⇒≃ (cong P x≡y)) p      ∎

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
      (λ f → to B₁≃B₂ ∘ f ∘ from A₁≃A₂)                  ≡⟨ ext (λ _ → subst-unique (λ B → A₂ → B) (λ A≃B g → _≃_.to A≃B ∘ g)
                                                                                    refl univ B₁≃B₂ _) ⟩
      subst (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂) ∘
      (λ f → f ∘ from A₁≃A₂)                             ≡⟨ cong (_∘_ (subst (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂))) (ext λ f →
                                                              subst-unique (λ A → A → B₁) (λ A≃B g → g ∘ _≃_.from A≃B) refl univ A₁≃A₂ f) ⟩
      subst (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂) ∘
      subst (λ A → A → B₁) (≃⇒≡ univ A₁≃A₂)              ≡⟨ cong₂ (λ g h f → g (h f)) (ext $ subst-in-terms-of-≡⇒≃ _ (λ B → A₂ → B))
                                                                                      (ext $ subst-in-terms-of-≡⇒≃ _ (λ A → A → B₁)) ⟩
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
    (∀ {A} (p : P A) → _≃_.to (P-cong Weak.id) p ≡ p) →
    cong P (≃⇒≡ univ₁ A≃B) ≡ ≃⇒≡ univ₂ (P-cong A≃B)
  cong-≃⇒≡ {A≃B = A≃B} ext univ₁ univ₂ P P-cong P-cong-id =
    cong P (≃⇒≡ univ₁ A≃B)                    ≡⟨ sym $ _≃_.left-inverse-of (≡≃≃ univ₂) _ ⟩
    ≃⇒≡ univ₂ (≡⇒≃ (cong P (≃⇒≡ univ₁ A≃B)))  ≡⟨ cong (≃⇒≡ univ₂) $ lift-equality ext lemma ⟩∎
    ≃⇒≡ univ₂ (P-cong A≃B)                    ∎
    where
    lemma : ≡⇒→ (cong P (≃⇒≡ univ₁ A≃B)) ≡ _≃_.to (P-cong A≃B)
    lemma = ext λ x →
      ≡⇒→ (cong P (≃⇒≡ univ₁ A≃B)) x  ≡⟨ sym $ subst-in-terms-of-≡⇒≃ _ P x ⟩
      subst P (≃⇒≡ univ₁ A≃B) x       ≡⟨ sym $ subst-unique P (_≃_.to ∘ P-cong) P-cong-id univ₁ A≃B x ⟩∎
      _≃_.to (P-cong A≃B) x           ∎
