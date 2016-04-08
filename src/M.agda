------------------------------------------------------------------------
-- M-types
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module M
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection hiding (_∘_)
open Derived-definitions-and-properties eq
open import H-level eq
open import H-level.Closure eq
open import Logical-equivalence hiding (_∘_)
open import Prelude
open import Surjection eq as Surjection hiding (_∘_)

------------------------------------------------------------------------
-- M-types

mutual

  data M {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    dns : (x : A) (f : B x → M′ A B) → M A B

  record M′ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    coinductive
    field
      ♭ : M A B

-- Projections.

pɐǝɥ : ∀ {a b} {A : Set a} {B : A → Set b} →
       M A B → A
pɐǝɥ (dns x f) = x

lıɐʇ : ∀ {a b} {A : Set a} {B : A → Set b} →
       (x : M A B) → B (pɐǝɥ x) → M A B
lıɐʇ (dns x f) y = M′.♭ (f y)

------------------------------------------------------------------------
-- Equality

-- M-types are isomorphic to Σ-types containing M-types (almost).

M-unfolding : ∀ {a b} {A : Set a} {B : A → Set b} →
              M A B ↔ ∃ λ (x : A) → B x → M′ A B
M-unfolding = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (dns x f) → x , f }
      ; from = uncurry dns
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = λ { (dns x f) → refl (dns x f) }
  }

abstract

  -- Equality between elements of an M-type can be proved using a pair
  -- of equalities (assuming extensionality and a kind of η law).
  --
  -- Note that M-≡,≡↠≡ does not preserve or establish guardedness, so
  -- this lemma is perhaps not very useful.

  M-≡,≡↠≡ :
    ∀ {a b} {A : Set a} {B : A → Set b} →
    (∀ {x} {C : B x → Set (a ⊔ b)} → Extensionality′ (B x) C) →
    (∀ {x} {f g : B x → M′ A B} → M′.♭ ∘ f ≡ M′.♭ ∘ g ↠ f ≡ g) →
    ∀ {x y} {f : B x → M′ A B} {g : B y → M′ A B} →
    (∃ λ (p : x ≡ y) → ∀ i → M′.♭ (f i) ≡ M′.♭ (g (subst B p i))) ↠
    _≡_ {A = M A B} (dns x f) (dns y g)
  M-≡,≡↠≡ {a} {A = A} {B} ext η {x} {y} {f} {g} =
    (∃ λ (p : x ≡ y) → ∀ i → M′.♭ (f i) ≡ M′.♭ (g (subst B p i)))  ↠⟨ Surjection.∃-cong lemma ⟩
    (∃ λ (p : x ≡ y) → subst (λ x → B x → M′ A B) p f ≡ g)         ↠⟨ _↔_.surjection Σ-≡,≡↔≡ ⟩
    (_≡_ {A = ∃ λ (x : A) → B x → M′ A B} (x , f) (y , g))         ↠⟨ ↠-≡ (_↔_.surjection (Bijection.inverse (M-unfolding {A = A} {B = B}))) ⟩□
    (dns x f ≡ dns y g)                                            □
    where
    lemma : (p : x ≡ y) →
            (∀ i → M′.♭ (f i) ≡ M′.♭ (g (subst B p i))) ↠
            (subst (λ x → B x → M′ A B) p f ≡ g)
    lemma p = elim
      (λ {x y} p → (f : B x → M′ A B) (g : B y → M′ A B) →
                   (∀ i → M′.♭ (f i) ≡ M′.♭ (g (subst B p i))) ↠
                   (subst (λ x → B x → M′ A B) p f ≡ g))
      (λ x f g →
         (∀ i → M′.♭ (f i) ≡ M′.♭ (g (subst B (refl x) i)))  ↠⟨ subst (λ h → (∀ i → M′.♭ (f i) ≡ M′.♭ (g (h i))) ↠ (∀ i → M′.♭ (f i) ≡ M′.♭ (g i)))
                                                                      (sym (lower-extensionality₂ a ext (subst-refl B)))
                                                                      Surjection.id ⟩
         (∀ i → M′.♭ (f i) ≡ M′.♭ (g i))                     ↠⟨ ext-surj ext ⟩
         (M′.♭ ∘ f ≡ M′.♭ ∘ g)                               ↠⟨ η ⟩
         (f ≡ g)                                             ↠⟨ subst (λ h → (f ≡ g) ↠ (h ≡ g))
                                                                      (sym $ subst-refl (λ x' → B x' → M′ A B) f)
                                                                      Surjection.id ⟩□
         (subst (λ x → B x → M′ A B) (refl x) f ≡ g)         □)
      p f g

------------------------------------------------------------------------
-- Bisimilarity and bisimilarity for bisimilarity

-- Bisimilarity.

mutual

  infix 4 _≡M_ _≡M′_

  data _≡M_ {a b} {A : Set a} {B : A → Set b}
            (x y : M A B) : Set (a ⊔ b) where
    dns : (p : pɐǝɥ x ≡ pɐǝɥ y) →
          (∀ b → lıɐʇ x b ≡M′ lıɐʇ y (subst B p b)) →
          x ≡M y

  record _≡M′_ {a b} {A : Set a} {B : A → Set b}
               (x y : M A B) : Set (a ⊔ b) where
    coinductive
    field
      ♭ : x ≡M y

-- Projections.

pɐǝɥ≡ : ∀ {a b} {A : Set a} {B : A → Set b} {x y : M A B} →
        x ≡M y → pɐǝɥ x ≡ pɐǝɥ y
pɐǝɥ≡ (dns p q) = p

lıɐʇ≡ : ∀ {a b} {A : Set a} {B : A → Set b} {x y : M A B} →
        (p : x ≡M y) →
        ∀ b → lıɐʇ x b ≡M lıɐʇ y (subst B (pɐǝɥ≡ p) b)
lıɐʇ≡ (dns p q) y = _≡M′_.♭ (q y)

-- Equality implies bisimilarity.

≡⇒≡M : ∀ {a b} {A : Set a} {B : A → Set b} {x y : M A B} →
       x ≡ y → x ≡M y
≡⇒≡M {B = B} {dns x f} {dns y g} p =
  dns (proj₁ q) helper
  where
  q = elim (λ {m m′} m≡m′ →
              ∃ λ (x≡y : pɐǝɥ m ≡ pɐǝɥ m′) →
                  ∀ b → lıɐʇ m b ≡ lıɐʇ m′ (subst B x≡y b))
           (λ m → refl (pɐǝɥ m) , λ b →
              lıɐʇ m b                            ≡⟨ cong (lıɐʇ m) (sym $ subst-refl B _) ⟩∎
              lıɐʇ m (subst B (refl (pɐǝɥ m)) b)  ∎)
           p

  helper :
    ∀ b → lıɐʇ (dns x f) b ≡M′ lıɐʇ (dns y g) (subst B (proj₁ q) b)
  _≡M′_.♭ (helper b) = ≡⇒≡M (proj₂ q b)

-- Bisimilarity for the bisimilarity type.

mutual

  data _≡≡M_ {a b} {A : Set a} {B : A → Set b} {x y : M A B}
             (p q : x ≡M y) : Set (a ⊔ b) where
    dns : (r : pɐǝɥ≡ p ≡ pɐǝɥ≡ q) →
          (∀ b → lıɐʇ≡ p b ≡≡M′
                 subst (λ p → lıɐʇ x b ≡M lıɐʇ y (subst B p b)) (sym r)
                       (lıɐʇ≡ q b)) →
          p ≡≡M q

  record _≡≡M′_ {a b} {A : Set a} {B : A → Set b} {x y : M A B}
                (p q : x ≡M y) : Set (a ⊔ b) where
    coinductive
    field
      ♭ : p ≡≡M q

------------------------------------------------------------------------
-- Closure under various h-levels

abstract

  -- If we assume a notion of extensionality (bisimilarity implies
  -- equality) then Contractible is closed under M.

  M-closure-contractible :
    ∀ {a b} {A : Set a} {B : A → Set b} →
    ({x y : M A B} → x ≡M y → x ≡ y) →
    Contractible A → Contractible (M A B)
  M-closure-contractible {A = A} {B} ext (z , irrA) = (x , ext ∘ irr)
    where
    x : M A B
    x = dns z (λ _ → helper)
      where
      helper : M′ A B
      M′.♭ helper = x

    irr : ∀ y → x ≡M y
    irr (dns x′ f) = dns (irrA x′) helper
      where
      helper : ∀ y → x ≡M′ M′.♭ (f (subst B (irrA x′) y))
      _≡M′_.♭ (helper _) = irr _

  -- The same applies to Is-proposition.

  M-closure-propositional :
    ∀ {a b} {A : Set a} {B : A → Set b} →
    ({x y : M A B} → x ≡M y → x ≡ y) →
    Is-proposition A → Is-proposition (M A B)
  M-closure-propositional {A = A} {B} ext p =
    _⇔_.from propositional⇔irrelevant
             (λ x y → ext $ irrelevant x y)
    where
    irrelevant : (x y : M A B) → x ≡M y
    irrelevant (dns x f) (dns y g) =
      dns (proj₁ (p x y)) helper
      where
      helper : (y′ : B x) →
               M′.♭ (f y′) ≡M′ M′.♭ (g (subst B (proj₁ (p x y)) y′))
      _≡M′_.♭ (helper _) = irrelevant _ _

  -- If we assume that we have another notion of extensionality, then
  -- Contractible is closed under M.

  M-closure-set :
    ∀ {a b} {A : Set a} {B : A → Set b} →
    ({x y : M A B} {p q : x ≡ y} → ≡⇒≡M p ≡≡M ≡⇒≡M q → p ≡ q) →
    Is-set A → Is-set (M A B)
  M-closure-set {A = A} {B} ext s =
    _⇔_.from set⇔UIP (λ p q → ext $ uip (≡⇒≡M p) (≡⇒≡M q))
    where
    uip : {x y : M A B} (p q : x ≡M y) → p ≡≡M q
    uip {x} {y} (dns p f) (dns q g) =
      dns (proj₁ (s _ _ p q)) helper
      where
      helper : (b : B (pɐǝɥ x)) →
               _≡M′_.♭ (f b)
                 ≡≡M′
               subst (λ eq → lıɐʇ x b ≡M lıɐʇ y (subst B eq b))
                     (sym (proj₁ (s (pɐǝɥ x) (pɐǝɥ y) p q)))
                     (_≡M′_.♭ (g b))
      _≡≡M′_.♭ (helper _) = uip _ _
