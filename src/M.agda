------------------------------------------------------------------------
-- M-types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module M
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection using (_↔_)
open Derived-definitions-and-properties eq
import Equivalence eq as Eq
open import Function-universe eq hiding (_∘_)
open import H-level eq
open import H-level.Closure eq
open import Logical-equivalence hiding (_∘_)
open import Prelude

------------------------------------------------------------------------
-- M-types

mutual

  data M {a b} (A : Set a) (B : A → Set b) (i : Size) :
         Set (a ⊔ b) where
    dns : (x : A) (f : B x → M′ A B i) → M A B i

  record M′ {a b} (A : Set a) (B : A → Set b) (i : Size) :
            Set (a ⊔ b) where
    coinductive
    field
      force : {j : Size< i} → M A B j

open M′ public

-- Projections.

pɐǝɥ : ∀ {a b i} {A : Set a} {B : A → Set b} →
       M A B i → A
pɐǝɥ (dns x f) = x

lıɐʇ : ∀ {a b i} {j : Size< i} {A : Set a} {B : A → Set b} →
       (x : M A B i) → B (pɐǝɥ x) → M A B j
lıɐʇ (dns x f) y = force (f y)

------------------------------------------------------------------------
-- Equality

-- M-types are isomorphic to Σ-types containing M-types (almost).

M-unfolding : ∀ {a b} {i} {A : Set a} {B : A → Set b} →
              M A B i ↔ ∃ λ (x : A) → B x → M′ A B i
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
  -- Note that, because the equality type former is not sized, this
  -- lemma is perhaps not very useful.

  M-≡,≡↔≡ :
    ∀ {a b i} {A : Set a} {B : A → Set b} →
    Extensionality b (a ⊔ b) →
    (∀ {x} {f g : B x → M′ A B i} →
       _≡_ {A = B x → {j : Size< i} → M A B j}
           (force ∘ f) (force ∘ g) ↔
       f ≡ g) →
    ∀ {x y} {f : B x → M′ A B i} {g : B y → M′ A B i} →
    (∃ λ (p : x ≡ y) → ∀ b {j : Size< i} →
       force (f b) {j = j} ≡ force (g (subst B p b))) ↔
    _≡_ {A = M A B i} (dns x f) (dns y g)
  M-≡,≡↔≡ {a} {i = i} {A} {B} ext η {x} {y} {f} {g} =
    (∃ λ (p : x ≡ y) → ∀ b {j : Size< i} →
       force (f b) {j = j} ≡ force (g (subst B p b)))         ↝⟨ ∃-cong lemma ⟩
    (∃ λ (p : x ≡ y) → subst (λ x → B x → M′ A B i) p f ≡ g)  ↝⟨ Bijection.Σ-≡,≡↔≡ ⟩
    (_≡_ {A = ∃ λ (x : A) → B x → M′ A B i} (x , f) (y , g))  ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ M-unfolding) ⟩□
    (dns x f ≡ dns y g)                                       □
    where
    lemma : (p : x ≡ y) →
            ((b : B x) {j : Size< i} →
             force (f b) {j = j} ≡ force (g (subst B p b))) ↔
            (subst (λ x → B x → M′ A B i) p f ≡ g)
    lemma p = elim
      (λ {x y} p → (f : B x → M′ A B i) (g : B y → M′ A B i) →
                   (∀ b {j} → force (f b) {j = j} ≡
                              force (g (subst B p b))) ↔
                   (subst (λ x → B x → M′ A B i) p f ≡ g))
      (λ x f g →
         (∀ b {j} → force (f b) {j = j} ≡
                    force (g (subst B (refl x) b)))               ↝⟨ subst (λ h → (∀ b {j} → force (f b) ≡ force (g (h b))) ↔
                                                                                  (∀ b {j} → force (f b) ≡ force (g b)))
                                                                           (sym (apply-ext (lower-extensionality lzero a ext) (subst-refl B)))
                                                                           Bijection.id ⟩

         (∀ b {j : Size< i} → force (f b) {j = j} ≡ force (g b))  ↝⟨ ∀-cong ext (λ _ → Bijection.implicit-Π↔Π) ⟩

         (∀ b (j : Size< i) → force (f b) {j = j} ≡ force (g b))  ↝⟨ ∀-cong ext (λ _ → implicit-extensionality-isomorphism
                                                                                         (lower-extensionality _ lzero ext)) ⟩
         ((b : B x) → _≡_ {A = {j : Size< i} → _}
                          (force (f b)) (force (g b)))            ↔⟨ Eq.extensionality-isomorphism ext ⟩

         (force ∘ f ≡ force ∘ g)                                  ↝⟨ η ⟩

         (f ≡ g)                                                  ↝⟨ subst (λ h → (f ≡ g) ↔ (h ≡ g))
                                                                           (sym $ subst-refl (λ x' → B x' → M′ A B i) f)
                                                                           Bijection.id ⟩□
         (subst (λ x → B x → M′ A B i) (refl x) f ≡ g)            □)
      p f g

------------------------------------------------------------------------
-- Bisimilarity and bisimilarity for bisimilarity

-- Bisimilarity.

mutual

  infix 4 [_]_≡M_ [_]_≡M′_

  data [_]_≡M_ {a b} {A : Set a} {B : A → Set b}
               (i : Size) (x y : M A B ∞) : Set (a ⊔ b) where
    dns : (p : pɐǝɥ x ≡ pɐǝɥ y) →
          (∀ b → [ i ] lıɐʇ x b ≡M′ lıɐʇ y (subst B p b)) →
          [ i ] x ≡M y

  record [_]_≡M′_ {a b} {A : Set a} {B : A → Set b}
                  (i : Size) (x y : M A B ∞) : Set (a ⊔ b) where
    coinductive
    field
      force : {j : Size< i} → [ j ] x ≡M y

open [_]_≡M′_ public

-- Projections.

pɐǝɥ≡ :
  ∀ {a b i} {A : Set a} {B : A → Set b} {x y : M A B ∞} →
  [ i ] x ≡M y → pɐǝɥ x ≡ pɐǝɥ y
pɐǝɥ≡ (dns p q) = p

lıɐʇ≡ :
  ∀ {a b i} {A : Set a} {B : A → Set b} {x y : M A B ∞} →
  (p : [ i ] x ≡M y) →
  ∀ b {j : Size< i} → [ j ] lıɐʇ x b ≡M lıɐʇ y (subst B (pɐǝɥ≡ p) b)
lıɐʇ≡ (dns p q) y = force (q y)

-- Equality implies bisimilarity.

≡⇒≡M : ∀ {a b i} {A : Set a} {B : A → Set b} {x y : M A B ∞} →
       x ≡ y → [ i ] x ≡M y
≡⇒≡M {i = i} {B = B} {dns x f} {dns y g} p =
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
    ∀ b →
    [ i ] lıɐʇ (dns x f) b ≡M′ lıɐʇ (dns y g) (subst B (proj₁ q) b)
  force (helper b) = ≡⇒≡M (proj₂ q b)

-- Bisimilarity for the bisimilarity type.

mutual

  data [_]_≡≡M_ {a b} {A : Set a} {B : A → Set b} {x y : M A B ∞}
                (i : Size) (p q : [ ∞ ] x ≡M y) : Set (a ⊔ b) where
    dns : (r : pɐǝɥ≡ p ≡ pɐǝɥ≡ q) →
          (∀ b → [ i ] lıɐʇ≡ p b ≡≡M′
                       subst (λ p → [ ∞ ] lıɐʇ x b ≡M
                                          lıɐʇ y (subst B p b))
                             (sym r)
                             (lıɐʇ≡ q b)) →
          [ i ] p ≡≡M q

  record [_]_≡≡M′_ {a b} {A : Set a} {B : A → Set b} {x y : M A B ∞}
                   (i : Size) (p q : [ ∞ ] x ≡M y) : Set (a ⊔ b) where
    coinductive
    field
      force : {j : Size< i} → [ j ] p ≡≡M q

open [_]_≡≡M′_ public

------------------------------------------------------------------------
-- Closure under various h-levels

abstract

  -- If we assume a notion of extensionality (bisimilarity implies
  -- equality) then Contractible is closed under M.

  M-closure-contractible :
    ∀ {a b} {A : Set a} {B : A → Set b} →
    ({x y : M A B ∞} → [ ∞ ] x ≡M y → x ≡ y) →
    Contractible A → Contractible (M A B ∞)
  M-closure-contractible {A = A} {B} ext (z , irrA) = (x , ext ∘ irr)
    where
    x : ∀ {i} → M A B i
    x = dns z λ _ → λ { .force → x }

    irr : ∀ {i} y → [ i ] x ≡M y
    irr {i} (dns x′ f) = dns (irrA x′) helper
      where
      helper : ∀ y → [ i ] x ≡M′ force (f (subst B (irrA x′) y))
      force (helper _) = irr _

  -- The same applies to Is-proposition.

  M-closure-propositional :
    ∀ {a b} {A : Set a} {B : A → Set b} →
    ({x y : M A B ∞} → [ ∞ ] x ≡M y → x ≡ y) →
    Is-proposition A → Is-proposition (M A B ∞)
  M-closure-propositional {A = A} {B} ext p =
    _⇔_.from propositional⇔irrelevant
             (λ x y → ext $ irrelevant x y)
    where
    irrelevant : ∀ {i} (x y : M A B ∞) → [ i ] x ≡M y
    irrelevant {i} (dns x f) (dns y g) =
      dns (proj₁ (p x y)) helper
      where
      helper :
        (y′ : B x) →
        [ i ] force (f y′) ≡M′ force (g (subst B (proj₁ (p x y)) y′))
      force (helper _) = irrelevant _ _

  -- If we assume that we have another notion of extensionality, then
  -- Is-set is closed under M.

  M-closure-set :
    ∀ {a b} {A : Set a} {B : A → Set b} →
    ({x y : M A B ∞} {p q : x ≡ y} → [ ∞ ] ≡⇒≡M p ≡≡M ≡⇒≡M q → p ≡ q) →
    Is-set A → Is-set (M A B ∞)
  M-closure-set {A = A} {B} ext s =
    _⇔_.from set⇔UIP (λ p q → ext $ uip (≡⇒≡M p) (≡⇒≡M q))
    where
    uip : ∀ {i} {x y : M A B ∞} (p q : [ ∞ ] x ≡M y) → [ i ] p ≡≡M q
    uip {i} {x} {y} (dns p f) (dns q g) =
      dns (proj₁ (s _ _ p q)) helper
      where
      helper :
        (b : B (pɐǝɥ x)) →
        [ i ] force (f b) ≡≡M′
              subst (λ eq → [ ∞ ] lıɐʇ x b ≡M lıɐʇ y (subst B eq b))
                    (sym (proj₁ (s (pɐǝɥ x) (pɐǝɥ y) p q)))
                    (force (g b))
      force (helper _) = uip _ _
