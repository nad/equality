------------------------------------------------------------------------
-- Quotients
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Partly based on the presentation of quotients in the HoTT book.
-- Perhaps that presentation is partly based on work by Voevodsky.

-- The generalisation from propositional equivalence relations to
-- "strong" equivalence relations is my own. In light of the results
-- below I see little use for this generalisation…

open import Equality

module Quotient {r} (eq : ∀ {a p} → Equality-with-J a p r) where

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bij using (_↔_)
open import Bool eq
private
  module D = Derived-definitions-and-properties eq
  open D hiding (elim)
open import Equality.Decidable-UIP eq using (Constant)
open import Equality.Decision-procedures eq
import Equality.Groupoid eq as EG
open import Equivalence eq as Eq using (_≃_)
open import Fin eq
open import Function-universe eq as F hiding (_∘_)
open import Groupoid
open import H-level eq as H-level
open import H-level.Closure eq
open import H-level.Truncation eq as Trunc hiding (rec)
open import Nat eq as Nat
open import Univalence-axiom eq

------------------------------------------------------------------------
-- Equivalence relations

-- The definition of an equivalence relation.

record Is-equivalence-relation
         {a r} {A : Set a} (R : A → A → Set r) : Set (a ⊔ r) where
  field
    reflexive  : ∀ {x} → R x x
    symmetric  : ∀ {x y} → R x y → R y x
    transitive : ∀ {x y z} → R x y → R y z → R x z

------------------------------------------------------------------------
-- Strong equivalence relations

-- A strengthening of the concept of "equivalence relation".

Strong-equivalence : ∀ {a r} {A : Set a} →
                     (A → A → Set r) → Set (a ⊔ lsuc r)
Strong-equivalence R = ∀ {x y} → R x y ≃ (R x ≡ R y)

-- Strong equivalence relations are equivalence relations.

strong-equivalence⇒equivalence :
  ∀ {a r} {A : Set a} {R : A → A → Set r} →
  Strong-equivalence R →
  Is-equivalence-relation R
strong-equivalence⇒equivalence {R = R} strong-equivalence = record
  { reflexive = λ {x} →
                 $⟨ refl (R x) ⟩
      R x ≡ R x  ↝⟨ _≃_.from strong-equivalence ⟩□
      R x x      □
  ; symmetric = λ {x y} →
      R x y      ↝⟨ _≃_.to strong-equivalence ⟩
      R x ≡ R y  ↝⟨ sym ⟩
      R y ≡ R x  ↝⟨ _≃_.from strong-equivalence ⟩□
      R y x      □
  ; transitive = λ {x y z} Rxy Ryz →
     _≃_.from strong-equivalence (
       R x  ≡⟨ _≃_.to strong-equivalence Rxy ⟩
       R y  ≡⟨ _≃_.to strong-equivalence Ryz ⟩∎
       R z  ∎)
  }

-- A relation that is an equivalence relation, and a family of
-- propositions, is a strong equivalence relation (assuming
-- extensionality and univalence).

propositional-equivalence⇒strong-equivalence :
  ∀ {a r} {A : Set a} {R : A → A → Set r} →
  Extensionality (a ⊔ r) (lsuc r) →
  Univalence r →
  Is-equivalence-relation R →
  (∀ x y → Is-proposition (R x y)) →
  Strong-equivalence R
propositional-equivalence⇒strong-equivalence
  {a} {r} {R = R} ext univ R-equiv R-prop {x = x} {y = y} =

  Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to = λ Rxy → apply-ext (lower-extensionality r lzero ext) λ z →
                 ≃⇒≡ univ $
                 _↔_.to (Eq.⇔↔≃ (lower-extensionality a _ ext)
                                (R-prop x z) (R-prop y z))
                 (R x z  ↝⟨ record { to   = transitive (symmetric Rxy)
                                   ; from = transitive Rxy
                                   } ⟩□
                  R y z  □)
        ; from = λ Rx≡Ry →        $⟨ reflexive ⟩
                           R y y  ↝⟨ subst (_$ y) (sym Rx≡Ry) ⟩□
                           R x y  □
        }
      ; right-inverse-of = λ _ →
          _⇔_.to propositional⇔irrelevant
            (H-level.respects-surjection
               (_≃_.surjection $ Eq.extensionality-isomorphism
                                   (lower-extensionality r lzero ext))
               1 $
             Π-closure (lower-extensionality r lzero ext) 1 λ z →
             H-level-H-level-≡ˡ
               (lower-extensionality a _ ext)
               univ 0 (R-prop x z))
            _ _
      }
    ; left-inverse-of = λ _ →
        _⇔_.to propositional⇔irrelevant (R-prop x y) _ _
    })
  where
  open Is-equivalence-relation R-equiv

-- _≡_ is a strong equivalence relation (assuming extensionality and
-- univalence).

equality-strong-equivalence :
  ∀ {a} {A : Set a} →
  Extensionality a (lsuc a) →
  Univalence a →
  Strong-equivalence (_≡_ {A = A})
equality-strong-equivalence ext univ {x = x} {y = y} =
  x ≡ y                      ↔⟨ inverse $ Π≡≃≡-↔-≡ (lower-extensionality lzero _ ext) _ _ ⟩
  (∀ z → (z ≡ x) ≃ (z ≡ y))  ↝⟨ (∀-cong (lower-extensionality lzero _ ext) λ _ → Eq.↔⇒≃ $
                                 Eq.≃-preserves-bijections (lower-extensionality lzero _ ext)
                                   (Groupoid.⁻¹-bijection (EG.groupoid _))
                                   (Groupoid.⁻¹-bijection (EG.groupoid _))) ⟩
  (∀ z → (x ≡ z) ≃ (y ≡ z))  ↝⟨ (∀-cong ext λ _ → inverse $ ≡≃≃ univ) ⟩
  (∀ z → (x ≡ z) ≡ (y ≡ z))  ↝⟨ Eq.extensionality-isomorphism ext ⟩□
  (x ≡_) ≡ (y ≡_)            □

-- If λ (_ _ : ⊤) → Fin n is a strong equivalence relation, then n is
-- equal to n ! (assuming extensionality and univalence).

const-Fin-strong-equivalence⇒≡! :
  Extensionality (# 0) (# 1) →
  Univalence (# 0) →
  ∀ n → Strong-equivalence (λ (_ _ : ⊤) → Fin n) → n ≡ n !
const-Fin-strong-equivalence⇒≡! ext univ n strong-equivalence =
  _⇔_.to isomorphic-same-size (
    Fin n                          ↔⟨ strong-equivalence ⟩
    const (Fin n) ≡ const (Fin n)  ↔⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
    (⊤ → Fin n ≡ Fin n)            ↝⟨ Π-left-identity ⟩
    Fin n ≡ Fin n                  ↝⟨ [Fin≡Fin]↔Fin! (lower-extensionality _ _ ext) univ n ⟩
    Fin (n !)                      □)

-- Thus there is at least one equivalence relation that is not a
-- strong equivalence relation (assuming extensionality and
-- univalence).

equivalence-but-not-strong-equivalence :
  Extensionality (# 0) (# 1) →
  Univalence (# 0) →
  ∃ λ (A : Set) →
  ∃ λ (R : A → A → Set) →
    (∀ {x} → R x x) ×
    (∀ {x y} → R x y → R y x) ×
    (∀ {x y z} → R x y → R y z → R x z) ×
    ¬ Strong-equivalence R
equivalence-but-not-strong-equivalence ext univ =
  A , R , rfl , sm , trns , not-strong-equivalence
  where
  A : Set
  A = ⊤

  R : A → A → Set
  R _ _ = Fin 3

  rfl : ∀ {x} → R x x
  rfl = fzero

  sm : ∀ {x y} → R x y → R y x
  sm _ = fzero

  trns : ∀ {x y z} → R x y → R y z → R x z
  trns _ _ = fzero

  not-strong-equivalence : ¬ Strong-equivalence R
  not-strong-equivalence =
    Strong-equivalence R  ↝⟨ const-Fin-strong-equivalence⇒≡! ext univ 3 ⟩
    3 ≡ 3 !               ↝⟨ from-⊎ (3 Nat.≟ (3 !)) ⟩□
    ⊥                     □

-- On the other hand, if n is 2, then λ (_ _ : ⊤) → Fin n is a strong
-- equivalence relation (assuming extensionality and univalence).

const-Fin-2-strong-equivalence :
  Extensionality (# 0) (# 1) →
  Univalence (# 0) →
  Strong-equivalence (λ (_ _ : ⊤) → Fin 2)
const-Fin-2-strong-equivalence ext univ =
  Fin 2                          ↔⟨ inverse $ [Fin≡Fin]↔Fin! (lower-extensionality _ _ ext) univ 2 ⟩
  Fin 2 ≡ Fin 2                  ↔⟨ inverse Π-left-identity ⟩
  (⊤ → Fin 2 ≡ Fin 2)            ↝⟨ Eq.extensionality-isomorphism ext ⟩□
  const (Fin 2) ≡ const (Fin 2)  □

-- Thus there is at least one example of a strong equivalence relation
-- that is neither propositional nor the identity type (assuming
-- extensionality and univalence).

strong-equivalence-that-is-neither-propositional-nor-≡ :
  Extensionality (# 0) (# 1) →
  Univalence (# 0) →
  ∃ λ (A : Set) →
  ∃ λ (R : A → A → Set) →
    Strong-equivalence R ×
    ¬ (∀ x y → Is-proposition (R x y)) ×
    ¬ (∀ x y → R x y ≃ (x ≡ y))
strong-equivalence-that-is-neither-propositional-nor-≡ ext univ =
  ⊤ , (λ _ _ → Fin 2) , const-Fin-2-strong-equivalence ext univ ,
  (λ is-prop →                   $⟨ is-prop _ _ ⟩
     Is-proposition (⊤ ⊎ ⊤ ⊎ ⊥)  ↝⟨ H-level.respects-surjection (_↔_.surjection $ inverse Bool↔Fin2) 1 ⟩
     Is-proposition Bool         ↝⟨ ¬-Bool-propositional ⟩□
     ⊥                           □) ,
  (λ ≃≡ → let eq = ≃≡ tt tt in
     ⊎.inj₁≢inj₂ (
       fzero                                 ≡⟨ sym $ _≃_.left-inverse-of eq _ ⟩
       _≃_.from eq (_≃_.to eq fzero)         ≡⟨ cong (_≃_.from eq) $
                                                _⇔_.to propositional⇔irrelevant
                                                  (mono (zero≤ 2) ⊤-contractible _ _)
                                                  _ _ ⟩
       _≃_.from eq (_≃_.to eq (fsuc fzero))  ≡⟨ _≃_.left-inverse-of eq _ ⟩∎
       fsuc fzero                            ∎))

-- It is not in general the case that, if R is a strong equivalence
-- relation, then R on f is a strong equivalence relation (assuming
-- extensionality and univalence).

strong-equivalence-not-closed-under-on :
  Extensionality (# 1) (# 2) →
  Univalence (# 1) →
  Univalence (# 0) →
  ∃ λ (A : Set₁) →
  ∃ λ (B : Set₁) →
  ∃ λ (R : A → A → Set₁) →
  ∃ λ (f : B → A) →
    Strong-equivalence R ×
    ¬ Strong-equivalence (R on f)
strong-equivalence-not-closed-under-on ext univ₁ univ₀ =
  Set , ↑ _ ⊤ , _≡_ , const (Fin 3) ,
  equality-strong-equivalence ext univ₁ ,
  not-strong-equivalence
  where
  not-strong-equivalence : ¬ Strong-equivalence (_≡_ on const (Fin 3))
  not-strong-equivalence strong-equivalence = contradiction
    where
    3!≡3!! = _⇔_.to isomorphic-same-size (
      Fin (3 !)                                      ↝⟨ inverse $ [Fin≡Fin]↔Fin! (lower-extensionality _ _ ext) univ₀ 3 ⟩
      Fin 3 ≡ Fin 3                                  ↔⟨ strong-equivalence ⟩
      const (Fin 3 ≡ Fin 3) ≡ const (Fin 3 ≡ Fin 3)  ↔⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
      (↑ _ ⊤ → (Fin 3 ≡ Fin 3) ≡ (Fin 3 ≡ Fin 3))    ↝⟨ →-cong ext Bij.↑↔ F.id ⟩
      (⊤ → (Fin 3 ≡ Fin 3) ≡ (Fin 3 ≡ Fin 3))        ↝⟨ Π-left-identity ⟩
      (Fin 3 ≡ Fin 3) ≡ (Fin 3 ≡ Fin 3)              ↔⟨ ≡-preserves-≃ (lower-extensionality lzero _ ext) univ₁ univ₀
                                                                      (Eq.↔⇒≃ $ [Fin≡Fin]↔Fin! (lower-extensionality _ _ ext) univ₀ 3)
                                                                      (Eq.↔⇒≃ $ [Fin≡Fin]↔Fin! (lower-extensionality _ _ ext) univ₀ 3) ⟩
      Fin (3 !) ≡ Fin (3 !)                          ↝⟨ [Fin≡Fin]↔Fin! (lower-extensionality _ _ ext) univ₀ (3 !) ⟩□
      Fin (3 ! !)                                    □)

    contradiction : ⊥
    contradiction = from-⊎ ((3 !) Nat.≟ (3 ! !)) 3!≡3!!

-- However, Strong-equivalence is closed under _on f when f is an
-- equivalence (assuming extensionality).

strong-equivalence-closed-under-on :
  ∀ {a b r} {A : Set a} {B : Set b} {R : A → A → Set r} →
  Extensionality (a ⊔ b) (lsuc r) →
  (B≃A : B ≃ A) →
  Strong-equivalence R →
  Strong-equivalence (R on _≃_.to B≃A)
strong-equivalence-closed-under-on
  {a} {b} {R = R} ext B≃A strong-equivalence {x} {y} =

  R (f x) (f y)                                  ↝⟨ strong-equivalence ⟩
  R (f x) ≡ R (f y)                              ↝⟨ F.id ⟩
  (λ z → R (f x)    z)  ≡ (λ z → R (f y)    z)   ↝⟨ inverse $ Eq.extensionality-isomorphism
                                                                (lower-extensionality b lzero ext) ⟩
  (∀ z → R (f x)    z   ≡        R (f y)    z)   ↝⟨ (Π-cong ext (inverse B≃A) λ z →
                                                     ≡⇒≃ $ cong₂ _≡_ (lemma x z) (lemma y z)) ⟩
  (∀ z → R (f x) (f z)  ≡        R (f y) (f z))  ↝⟨ Eq.extensionality-isomorphism
                                                      (lower-extensionality a lzero ext) ⟩
  (λ z → R (f x) (f z)) ≡ (λ z → R (f y) (f z))  ↝⟨ F.id ⟩□
  (R on f) x ≡ (R on f) y                        □
  where
  f   = _≃_.to   B≃A
  f⁻¹ = _≃_.from B≃A

  lemma = λ x z →
    R (f x) z            ≡⟨ cong (R (f x)) $ sym $ _≃_.right-inverse-of B≃A _ ⟩∎
    R (f x) (f (f⁻¹ z))  ∎

-- Various closure properties related to _×_ and _⊎_ fail to hold for
-- Strong-equivalence (assuming extensionality and univalence).

strong-equivalence-not-closed-under-×-or-⊎ :
  Extensionality (# 0) (# 1) →
  Univalence (# 0) →
  ∃ λ (A : Set) →
  ∃ λ (R₁ : A → A → Set) →
  ∃ λ (R₂ : A → A → Set) →
    Strong-equivalence R₁ ×
    Strong-equivalence R₂ ×
    ¬ Strong-equivalence (λ x y → R₁ x y × R₂ x y) ×
    ¬ Strong-equivalence (λ x y → R₁ x y ⊎ R₂ x y) ×
    ¬ Strong-equivalence (λ x y → R₁ (proj₁ x) (proj₁ y) ×
                                  R₂ (proj₂ x) (proj₂ y)) ×
    ¬ Strong-equivalence (λ x y → R₁ (proj₁ x) (proj₁ y) ⊎
                                  R₂ (proj₂ x) (proj₂ y))
strong-equivalence-not-closed-under-×-or-⊎ ext univ =
  ⊤ , R , R ,
  strong-equivalence , strong-equivalence ,
  not-strong-equivalence  (Fin×Fin↔Fin* 2 2) ,
  not-strong-equivalence  (Fin⊎Fin↔Fin+ 2 2) ,
  not-strong-equivalence′ (Fin×Fin↔Fin* 2 2) ,
  not-strong-equivalence′ (Fin⊎Fin↔Fin+ 2 2)
  where
  R : ⊤ → ⊤ → Set
  R = λ _ _ → Fin 2

  strong-equivalence : Strong-equivalence R
  strong-equivalence =
    proj₁ $ proj₂ $ proj₂ $
      strong-equivalence-that-is-neither-propositional-nor-≡ ext univ

  not-strong-equivalence :
    {B : Set} →
    B ↔ Fin 4 →
    ¬ Strong-equivalence (λ (_ _ : ⊤) → B)
  not-strong-equivalence {B} B↔Fin4 =
    Strong-equivalence (λ _ _ → B)      ↝⟨ (≡⇒↝ _ $ cong Strong-equivalence $ apply-ext ext λ _ → apply-ext ext λ _ →
                                            ≃⇒≡ univ $ Eq.↔⇒≃ B↔Fin4) ⟩
    Strong-equivalence (λ _ _ → Fin 4)  ↝⟨ const-Fin-strong-equivalence⇒≡! ext univ 4 ⟩
    4 ≡ 4 !                             ↝⟨ from-⊎ (4 Nat.≟ (4 !)) ⟩□
    ⊥                                   □

  not-strong-equivalence′ :
    {B : Set} →
    B ↔ Fin 4 →
    ¬ Strong-equivalence (λ (_ _ : ⊤ × ⊤) → B)
  not-strong-equivalence′ {B} B↔Fin4 =
    Strong-equivalence (λ (_ _ : ⊤ × ⊤) → B)  ↝⟨ (λ se {_ _} →
        B                                           ↝⟨ se {y = _} ⟩
        const B ≡ const B                           ↝⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
        (⊤ × ⊤ → B ≡ B)                             ↔⟨ →-cong ext ×-right-identity F.id ⟩
        (⊤ → B ≡ B)                                 ↝⟨ Eq.extensionality-isomorphism ext ⟩□
        const B ≡ const B                           □) ⟩
    Strong-equivalence (λ (_ _ : ⊤)     → B)  ↝⟨ not-strong-equivalence B↔Fin4 ⟩□
    ⊥                                         □

-- Is the following a strong equivalence relation?
--
--   R (x , _) (y , _) = x ≡ y
--
-- (This is a combination of equality and the trivial relation, both
-- of which are strong equivalence relations.)
--
-- Answer: No, not in general (assuming extensionality and
-- univalence).

another-negative-result :
  Extensionality (# 1) (# 2) →
  Univalence (# 1) →
  Univalence (# 0) →
  ∃ λ (A : Set₁) →
  ∃ λ (B : Set) →
    ¬ Strong-equivalence {A = A × B} (_≡_ on proj₁)
another-negative-result ext univ₁ univ₀ =
  Set , Fin 2 , not-strong-equivalence
  where
  not-strong-equivalence : ¬ Strong-equivalence (_≡_ on proj₁)
  not-strong-equivalence strong-equivalence = contradiction
    where
    4≡2 = _⇔_.to isomorphic-same-size (
      Fin 4                                                        ↝⟨ inverse $ [Fin→Fin]↔Fin^ (lower-extensionality _ _ ext) 2 2 ⟩
      (Fin 2 → Fin 2)                                              ↝⟨ →-cong (lower-extensionality _ _ ext) F.id $ inverse $
                                                                      [Fin≡Fin]↔Fin! (lower-extensionality _ _ ext) univ₀ 2 ⟩
      (Fin 2 → Fin 2 ≡ Fin 2)                                      ↔⟨ →-cong (lower-extensionality _ lzero ext) F.id $
                                                                      equality-strong-equivalence ext univ₁ ⟩
      (Fin 2 → (λ A → Fin 2 ≡       A) ≡ (λ A → Fin 2 ≡       A))  ↔⟨ →-cong (lower-extensionality _ lzero ext) F.id $ inverse $
                                                                      Eq.extensionality-isomorphism ext ⟩
      (Fin 2 → ∀ A → (Fin 2 ≡       A) ≡       (Fin 2 ≡       A))  ↝⟨ Π-comm ⟩
      (∀ A → Fin 2 → (Fin 2 ≡       A) ≡       (Fin 2 ≡       A))  ↝⟨ inverse currying ⟩
      (∀ A →         (Fin 2 ≡ proj₁ A) ≡       (Fin 2 ≡ proj₁ A))  ↔⟨ Eq.extensionality-isomorphism ext ⟩
      (λ A →          Fin 2 ≡ proj₁ A) ≡ (λ A → Fin 2 ≡ proj₁ A)   ↔⟨ inverse $ strong-equivalence {x = _ , fzero} {y = _ , fzero} ⟩
      Fin 2 ≡ Fin 2                                                ↝⟨ [Fin≡Fin]↔Fin! (lower-extensionality _ _ ext) univ₀ 2 ⟩□
      Fin 2                                                        □)

    contradiction : ⊥
    contradiction = from-⊎ (4 Nat.≟ 2) 4≡2

------------------------------------------------------------------------
-- Quotients

-- Equivalence classes.

_is-equivalence-class-of_ :
  ∀ {a} {A : Set a} →
  (A → Set a) → (A → A → Set a) → Set (lsuc (lsuc a))
_is-equivalence-class-of_ {a} P R =
  ∥ (∃ λ x → R x ≡ P) ∥ 1 (lsuc a)

-- Quotients.

infix 5 _/_

_/_ : ∀ {a} (A : Set a) → (A → A → Set a) → Set (lsuc (lsuc a))
A / R = ∃ λ (P : A → Set _) → P is-equivalence-class-of R

-- Quotienting with equality amounts to the same thing as not
-- quotienting at all (assuming extensionality and univalence).

/≡↔ :
  ∀ {a} {A : Set a} →
  Extensionality (lsuc (lsuc a)) (lsuc a) →
  Univalence a →
  A / _≡_ ↔ A
/≡↔ {A = A} ext univ =
  (∃ λ P → ∥ (∃ λ x → (x ≡_) ≡ P) ∥ 1 _)  ↝⟨ (∃-cong λ _ → ∥∥↔ lzero ext $ _⇔_.from propositional⇔irrelevant irr) ⟩
  (∃ λ P → ∃ λ x → (x ≡_) ≡ P)            ↝⟨ ∃-comm ⟩
  (∃ λ x → ∃ λ P → (x ≡_) ≡ P)            ↝⟨ drop-⊤-right (λ _ → _⇔_.to contractible⇔↔⊤ $ other-singleton-contractible _) ⟩□
  A                                       □
  where
  se = equality-strong-equivalence
         (lower-extensionality _ lzero ext) univ

  se-refl :
    ∀ x → _≃_.to se (refl x) ≡ refl (x ≡_)
  se-refl x = _≃_.from-to se (
    sym (_≃_.to (≡⇒↝ _ (cong (_$ x) (refl (x ≡_)))) (sym (refl x)))  ≡⟨ cong (λ p → sym (_≃_.to (≡⇒↝ _ p) (sym (refl x)))) $ cong-refl _ ⟩
    sym (_≃_.to (≡⇒↝ _ (refl (x ≡ x))) (sym (refl x)))               ≡⟨ cong (λ eq → sym (_≃_.to eq (sym (refl x)))) ≡⇒↝-refl ⟩
    sym (sym (refl x))                                               ≡⟨ sym-sym _ ⟩∎
    refl x                                                           ∎)

  lemma :
    {x y : A} (p : (x ≡_) ≡ (y ≡_)) →
    cong _≡_ (subst (_$ x) p (refl x)) ≡ sym p
  lemma {x = x} p =
    cong _≡_ (subst (_$ x) p (refl x))                            ≡⟨ cong (λ p → cong _≡_ (subst (_$ x) p (refl x))) $ sym $
                                                                       _≃_.right-inverse-of se _ ⟩
    cong _≡_ (subst (_$ x) (_≃_.to se (_≃_.from se p)) (refl x))  ≡⟨ D.elim (λ p → cong _≡_ (subst (_$ _) (_≃_.to se p) (refl _)) ≡
                                                                                   sym (_≃_.to se p))
                                                                            (λ x →
        cong _≡_ (subst (_$ x) (_≃_.to se (refl x)) (refl x))                  ≡⟨ cong (λ p → cong _≡_ (subst (_$ x) p (refl x))) $ se-refl x ⟩
        cong _≡_ (subst (_$ x) (refl (x ≡_)) (refl x))                         ≡⟨ cong (cong _≡_) $ subst-refl _ _ ⟩
        cong _≡_ (refl x)                                                      ≡⟨ cong-refl _ ⟩
        refl (x ≡_ )                                                           ≡⟨ sym sym-refl ⟩
        sym (refl (x ≡_ ))                                                     ≡⟨ cong sym $ sym $ se-refl x ⟩∎
        sym (_≃_.to se (refl x))                                               ∎)
                                                                            (_≃_.from se p) ⟩
    sym (_≃_.to se (_≃_.from se p))                               ≡⟨ cong sym $ _≃_.right-inverse-of se _ ⟩∎
    sym p                                                         ∎

  irr : ∀ {P} (p q : ∃ λ x → (x ≡_) ≡ P) → p ≡ q
  irr {P} (x , x≡≡) (y , y≡≡) =
    Σ-≡,≡→≡
      (_≃_.from se ((x ≡_)  ≡⟨ x≡≡ ⟩
                    P       ≡⟨ sym y≡≡ ⟩∎
                    (y ≡_)  ∎))

      (subst (λ x → (x ≡_) ≡ P)
             (_≃_.from se (trans x≡≡ (sym y≡≡)))
             x≡≡                                                        ≡⟨⟩

       subst (λ x → (x ≡_) ≡ P)
             (sym $ _≃_.to (≡⇒↝ _ (cong (_$ x) (trans x≡≡ (sym y≡≡))))
                           (sym (refl x)))
             x≡≡                                                        ≡⟨ cong (λ eq → subst (λ x → (x ≡_) ≡ P) (sym eq) x≡≡) $ sym $
                                                                             subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
       subst (λ x → (x ≡_) ≡ P)
             (sym $ subst (_$ x) (trans x≡≡ (sym y≡≡)) (sym (refl x)))
             x≡≡                                                        ≡⟨ cong (λ eq → subst (λ x → (x ≡_) ≡ P)
                                                                                              (sym (subst (_$ x) (trans x≡≡ (sym y≡≡)) eq)) _)
                                                                             sym-refl ⟩
       subst (λ x → (x ≡_) ≡ P)
             (sym $ subst (_$ x) (trans x≡≡ (sym y≡≡)) (refl x))
             x≡≡                                                        ≡⟨ subst-∘ _ _ _ ⟩

       subst (λ Q → Q ≡ P)
             (cong _≡_ $
                sym $ subst (_$ x) (trans x≡≡ (sym y≡≡)) (refl x))
             x≡≡                                                        ≡⟨ cong (λ eq → subst (λ Q → Q ≡ P) eq _) $ cong-sym _ _ ⟩

       subst (λ Q → Q ≡ P)
             (sym $ cong _≡_ $
                subst (_$ x) (trans x≡≡ (sym y≡≡)) (refl x))
             x≡≡                                                        ≡⟨ subst-trans _ ⟩

       trans (cong _≡_ $ subst (_$ x) (trans x≡≡ (sym y≡≡)) (refl x))
             x≡≡                                                        ≡⟨ cong (flip trans x≡≡) $ lemma _ ⟩

       trans (sym (trans x≡≡ (sym y≡≡))) x≡≡                            ≡⟨ cong (flip trans x≡≡) $ sym-trans _ _ ⟩

       trans (trans (sym (sym y≡≡)) (sym x≡≡)) x≡≡                      ≡⟨ trans-[trans-sym]- _ _ ⟩

       sym (sym y≡≡)                                                    ≡⟨ sym-sym _ ⟩∎

       y≡≡                                                              ∎)

module _ {a} {A : Set a} {R : A → A → Set a} where

  -- Equality characterisation lemmas for the quotient type.

  equality-characterisation₁ :
    Extensionality (lsuc (lsuc a)) (lsuc a) →
    {x y : A / R} →
    x ≡ y
      ↔
    proj₁ x ≡ proj₁ y
  equality-characterisation₁ ext {x} {y} =
    x ≡ y                                                          ↝⟨ inverse Bij.Σ-≡,≡↔≡ ⟩

    (∃ λ (eq : proj₁ x ≡ proj₁ y) →
       subst (_is-equivalence-class-of R) eq (proj₂ x) ≡ proj₂ y)  ↝⟨ (drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ $
                                                                       truncation-has-correct-h-level 1 ext _ _) ⟩□
    proj₁ x ≡ proj₁ y                                              □

  equality-characterisation₂ :
    Extensionality (lsuc (lsuc a)) (lsuc a) →
    {x y : A / R} →
    x ≡ y
      ↔
    (∀ z → proj₁ x z ≡ proj₁ y z)
  equality-characterisation₂ ext {x} {y} =
    x ≡ y                          ↝⟨ equality-characterisation₁ ext ⟩

    proj₁ x ≡ proj₁ y              ↔⟨ inverse $ Eq.extensionality-isomorphism
                                                  (lower-extensionality _ lzero ext) ⟩□
    (∀ z → proj₁ x z ≡ proj₁ y z)  □

  equality-characterisation₃ :
    Extensionality (lsuc (lsuc a)) (lsuc a) →
    Univalence a →
    {x y : A / R} →
    x ≡ y
      ↔
    (∀ z → proj₁ x z ≃ proj₁ y z)
  equality-characterisation₃ ext univ {x} {y} =
    x ≡ y                          ↝⟨ equality-characterisation₂ ext ⟩

    (∀ z → proj₁ x z ≡ proj₁ y z)  ↔⟨ (∀-cong (lower-extensionality _ lzero ext) λ _ →
                                       ≡≃≃ univ) ⟩□
    (∀ z → proj₁ x z ≃ proj₁ y z)  □

  -- Constructor for the quotient type.

  [_] : A → A / R
  [ a ] = R a , ∣ (a , refl (R a)) ∣

  -- [_] is surjective (assuming extensionality).

  []-surjective :
    Extensionality (lsuc (lsuc a)) (lsuc a) →
    Surjective (lsuc a) [_]
  []-surjective ext (P , P-is-class) =
    ∥∥-map
      (Σ-map
         F.id
         (λ {x} Rx≡P →
            [ x ]             ≡⟨ _↔_.from (equality-characterisation₁ ext) Rx≡P ⟩∎
            (P , P-is-class)  ∎))
      P-is-class

  -- If the relation is a family of types of h-level n, then the
  -- equivalence classes are also families of types of h-level n
  -- (assuming extensionality).

  equivalence-classes-have-same-h-level-as-relation :
    Extensionality a a →
    ∀ n →
    (∀ x y → H-level n (R x y)) →
    (x : A / R) → ∀ y → H-level n (proj₁ x y)
  equivalence-classes-have-same-h-level-as-relation
    ext n h (P , P-is-class) y =

    Trunc.rec
      (H-level-propositional ext n)
      (λ { (z , Rz≡P) → H-level.respects-surjection
                          (≡⇒↝ _ (R z y  ≡⟨ cong (_$ y) Rz≡P ⟩∎
                                  P y    ∎))
                          n
                          (h z y) })
      (with-lower-level _ P-is-class)

  -- If R is a family of types of h-level n, then A / R has h-level
  -- 1 + n (assuming extensionality and univalence).

  quotient's-h-level-is-1-+-relation's-h-level :
    Extensionality (lsuc (lsuc a)) (lsuc a) →
    Univalence a →
    Univalence (# 0) →
    ∀ n →
    (∀ x y → H-level n (R x y)) →
    H-level (1 + n) (A / R)
  quotient's-h-level-is-1-+-relation's-h-level ext univ univ₀ = h′
    where
    lemma₁ :
      ∀ n →
      (∀ x y z → H-level n (proj₁ x z ≡ proj₁ y z)) →
      H-level (1 + n) (A / R)
    lemma₁ n h x y =                             $⟨ h x y ⟩
      (∀ z → H-level n (proj₁ x z ≡ proj₁ y z))  ↝⟨ Π-closure (lower-extensionality _ lzero ext) n ⟩
      H-level n (∀ z → proj₁ x z ≡ proj₁ y z)    ↝⟨ H-level.respects-surjection
                                                      (_↔_.surjection (inverse $ equality-characterisation₂ ext))
                                                      n ⟩□
      H-level n (x ≡ y)                          □

    lemma₂ :
      ∀ n →
      (∀ x y → H-level (1 + n) (R x y)) →
      ∀ x y z → H-level (1 + n) (proj₁ x z ≡ proj₁ y z)
    lemma₂ n h x _ z =
      H-level-H-level-≡ˡ
        (lower-extensionality _ _ ext) univ n
        (equivalence-classes-have-same-h-level-as-relation
           (lower-extensionality _ _ ext) (1 + n) h x z)

    h′ : ∀ n →
         (∀ x y → H-level n (R x y)) →
         H-level (1 + n) (A / R)
    h′ (suc n) h = lemma₁ (suc n) (lemma₂ n h)
    h′ zero    h =
      lemma₁ zero λ x y z →
        propositional⇒inhabited⇒contractible
          (lemma₂ 0 (λ x y → mono₁ 0 (h x y)) x y z)
          (                       $⟨ refl _ ⟩
           ⊤ ≡ ⊤                  ↝⟨ ≡-preserves-≃ (lower-extensionality _ _ ext) univ₀ univ
                                       (lemma₃ x z) (lemma₃ y z) ⟩
           proj₁ x z ≡ proj₁ y z  □)
      where
      lemma₃ : ∀ x z → ⊤ ≃ proj₁ x z
      lemma₃ x z =                $⟨ equivalence-classes-have-same-h-level-as-relation
                                       (lower-extensionality _ _ ext)
                                       0 h x z ⟩
        Contractible (proj₁ x z)  ↝⟨ _⇔_.to contractible⇔↔⊤ ⟩
        proj₁ x z ↔ ⊤             ↝⟨ inverse ⟩
        ⊤ ↔ proj₁ x z             ↝⟨ Eq.↔⇒≃ ⟩□
        ⊤ ≃ proj₁ x z             □

  -- If the relation is a strong equivalence relation, then it is
  -- isomorphic to equality under [_] (assuming extensionality).

  related↔[equal] :
    Extensionality (lsuc (lsuc a)) (lsuc a) →
    Strong-equivalence R →
    ∀ {x y} → R x y ↔ [ x ] ≡ [ y ]
  related↔[equal] ext strong-equivalence {x} {y} =
    R x y          ↔⟨ strong-equivalence ⟩
    R x ≡ R y      ↝⟨ inverse $ equality-characterisation₁ ext ⟩□
    [ x ] ≡ [ y ]  □

  -- If the relation is a strong equivalence relation, then functions
  -- from quotients to sets are isomorphic to relation-respecting
  -- functions (assuming extensionality).

  /→set↔relation-respecting :
    Extensionality (lsuc (lsuc a)) (lsuc (lsuc a)) →
    Strong-equivalence R →
    {B : Set a} →
    Is-set B →
    (A / R → B) ↔ ∃ λ (f : A → B) → ∀ x y → R x y → f x ≡ f y
  /→set↔relation-respecting ext strong-equivalence {B = B} B-set =

    ((∃ λ P → ∥ (∃ λ x → R x ≡ P) ∥ 1 _) → B)             ↝⟨ currying ⟩

    (∀ P → ∥ (∃ λ x → R x ≡ P) ∥ 1 _ → B)                 ↔⟨ (∀-cong (lower-extensionality _ lzero ext) λ P → inverse $
                                                              constant-function≃∥inhabited∥⇒inhabited
                                                                lzero (lower-extensionality lzero _ ext) B-set) ⟩
    (∀ P → ∃ λ (f : (∃ λ x → R x ≡ P) → B) → Constant f)  ↝⟨ (∀-cong (lower-extensionality _ _ ext) λ _ →
                                                              Σ-cong currying λ _ → F.id) ⟩
    (∀ P → ∃ λ (f : (x : A) → R x ≡ P → B) →
               Constant (uncurry f))                      ↝⟨ ΠΣ-comm ⟩

    (∃ λ (f : ∀ P → (x : A) → R x ≡ P → B) →
       ∀ P → Constant (uncurry (f P)))                    ↝⟨ Σ-cong Π-comm (λ _ → F.id) ⟩

    (∃ λ (f : (x : A) → ∀ P → R x ≡ P → B) →
       ∀ P → Constant (uncurry (flip f P)))               ↝⟨ Σ-cong (∀-cong (lower-extensionality _ _ ext) λ _ →
                                                                     inverse currying) (λ _ →
                                                             F.id) ⟩
    (∃ λ (f : (x : A) → (∃ λ P → R x ≡ P) → B) →
       ∀ P → Constant (uncurry λ x eq → f x (P , eq)))    ↝⟨ inverse $
                                                             Σ-cong (Bij.inverse $
                                                                     ∀-cong (lower-extensionality _ _ ext) λ _ →
                                                                     drop-⊤-left-Π (lower-extensionality _ _ ext) $
                                                                     _⇔_.to contractible⇔↔⊤ $
                                                                     other-singleton-contractible _)
                                                             lemma ⟩□
    (∃ λ (f : A → B) → ∀ x y → R x y → f x ≡ f y)         □

    where

    lemma = λ f →
      (∀ x y → R x y → f x ≡ f y)                                    ↔⟨ (∀-cong (lower-extensionality _ _ ext) λ x →
                                                                         ∀-cong (lower-extensionality _ _ ext) λ y →
                                                                         →-cong (lower-extensionality _ _ ext) strong-equivalence F.id) ⟩
      (∀ x y → R x ≡ R y → f x ≡ f y)                                ↝⟨ (∀-cong (lower-extensionality _ _ ext) λ _ →
                                                                         ∀-cong (lower-extensionality _ _ ext) λ _ →
                                                                         →-cong (lower-extensionality _ _ ext)
                                                                                (Groupoid.⁻¹-bijection (EG.groupoid _))
                                                                                F.id) ⟩
      (∀ x y → R y ≡ R x → f x ≡ f y)                                ↝⟨ (∀-cong (lower-extensionality _ _ ext) λ _ →
                                                                         inverse currying) ⟩
      (∀ x (q : ∃ λ y → R y ≡ R x) → f x ≡ f (proj₁ q))              ↝⟨ (∀-cong (lower-extensionality _ _ ext) λ _ →
                                                                         inverse $ drop-⊤-left-Π (lower-extensionality _ _ ext) $
                                                                         _⇔_.to contractible⇔↔⊤ $
                                                                         other-singleton-contractible _) ⟩
      (∀ x (Q : ∃ λ P → R x ≡ P) (q : ∃ λ x → R x ≡ proj₁ Q) →
       f x ≡ f (proj₁ q))                                            ↝⟨ (∀-cong (lower-extensionality _ _ ext) λ _ →
                                                                         currying) ⟩
      (∀ x P → R x ≡ P → (q : ∃ λ x → R x ≡ P) → f x ≡ f (proj₁ q))  ↝⟨ Π-comm ⟩

      (∀ P x → R x ≡ P → (q : ∃ λ x → R x ≡ P) → f x ≡ f (proj₁ q))  ↝⟨ (∀-cong (lower-extensionality _ _ ext) λ _ →
                                                                         inverse currying) ⟩
      (∀ P (p q : ∃ λ x → R x ≡ P) → f (proj₁ p) ≡ f (proj₁ q))      ↝⟨ F.id ⟩

      (∀ P → Constant (uncurry λ x _ → f x))                         ↝⟨ (∀-cong (lower-extensionality _ _ ext) λ _ →
                                                                         ≡⇒↝ _ $ cong Constant $ apply-ext (lower-extensionality _ _ ext) λ _ →
                                                                         sym $ subst-const _) ⟩□
      (∀ P → Constant (uncurry λ x _ → subst (const B) _ (f x)))     □

  -- "Computation rule" for /→set↔relation-respecting.

  proj₁-to-/→set↔relation-respecting :
    (ext : Extensionality (lsuc (lsuc a)) (lsuc (lsuc a)))
    (strong-equivalence : Strong-equivalence R)
    {B : Set a}
    (B-set : Is-set B)
    (f : A / R → B) →
    proj₁ (_↔_.to (/→set↔relation-respecting
                     ext strong-equivalence B-set) f)
      ≡
    f ∘ [_]
  proj₁-to-/→set↔relation-respecting ext _ {B} _ f =
    apply-ext (lower-extensionality _ _ ext) λ x →
      subst (const B) (refl _) (f [ x ])  ≡⟨ subst-refl _ _ ⟩∎
      f [ x ]                             ∎

  -- Recursor (used to eliminate into sets). The recursor uses
  -- extensionality and reflexivity.

  rec :
    Extensionality (lsuc (lsuc a)) (lsuc a) →
    (∀ {x} → R x x) →
    (B : Set a) →
    Is-set B →
    (f : A → B) →
    (∀ {x y} → R x y → f x ≡ f y) →
    A / R → B
  rec ext refl B B-set f R⇒≡ (P , P-is-class) =
    _≃_.to (constant-function≃∥inhabited∥⇒inhabited lzero ext B-set)
      (f′ , f′-constant)
      P-is-class
    where
    f′ : (∃ λ x → R x ≡ P) → B
    f′ (x , _) = f x

    f′-constant : Constant f′
    f′-constant (x₁ , Rx₁≡P) (x₂ , Rx₂≡P) = R⇒≡ (
               $⟨ refl ⟩
      R x₂ x₂  ↝⟨ ≡⇒→ $ cong (λ Q → Q x₂) Rx₂≡P ⟩
      P x₂     ↝⟨ ≡⇒→ $ cong (λ Q → Q x₂) $ sym Rx₁≡P ⟩□
      R x₁ x₂  □)

  private

    -- The recursor's computation rule holds definitionally.

    rec-[] :
      (ext : Extensionality (lsuc (lsuc a)) (lsuc a))
      (refl : ∀ {x} → R x x)
      (B : Set a)
      (B-set : Is-set B)
      (f : A → B)
      (R⇒≡ : ∀ {x y} → R x y → f x ≡ f y)
      (x : A) →
      rec ext refl B B-set f R⇒≡ [ x ] ≡ f x
    rec-[] _ _ _ _ _ _ _ = refl _

  -- Eliminator (used to eliminate into sets). The eliminator uses
  -- extensionality, and the assumption that the relation is a strong
  -- equivalence relation. (The latter assumption could perhaps be
  -- weakened.)

  elim :
    (ext : Extensionality (lsuc (lsuc a)) (lsuc a))
    (strong-equivalence : Strong-equivalence R)
    (B : A / R → Set (lsuc a)) →
    (∀ x → Is-set (B x)) →
    (f : ∀ x → B [ x ]) →
    (∀ {x y} (Rxy : R x y) →
       subst B (_↔_.to (related↔[equal]
                          ext strong-equivalence) Rxy) (f x) ≡
       f y) →
    ∀ x → B x
  elim ext strong-equivalence B B-set f R⇒≡ (P , P-is-class) =
    _≃_.to (constant-function≃∥inhabited∥⇒inhabited
              lzero ext (B-set _))
      (f′ , f′-constant)
      P-is-class
    where
    f′ : (∃ λ x → R x ≡ P) → B (P , P-is-class)
    f′ (x , Rx≡P) =
      subst B
            (_↔_.from (equality-characterisation₁ ext) Rx≡P)
            (f x)

    f′-constant : Constant f′
    f′-constant (x , Rx≡P) (y , Ry≡P) =
      subst B
            (_↔_.from (equality-characterisation₁ ext) Rx≡P)
            (f x)                                                     ≡⟨ cong (subst _ _) $ sym $ R⇒≡ _ ⟩

      subst B
            (_↔_.from (equality-characterisation₁ ext) Rx≡P)
            (subst B (_↔_.to (related↔[equal]
                                ext strong-equivalence) lemma₁)
                   (f y))                                             ≡⟨ subst-subst _ _ _ _ ⟩

      subst B
            (trans (_↔_.to (related↔[equal]
                              ext strong-equivalence) lemma₁)
                   (_↔_.from (equality-characterisation₁ ext) Rx≡P))
            (f y)                                                     ≡⟨ cong (λ eq → subst B eq _) lemma₄ ⟩∎

      subst B
            (_↔_.from (equality-characterisation₁ ext) Ry≡P)
            (f y)                                                     ∎
      where
      lemma₁ = _≃_.from strong-equivalence (
         R y  ≡⟨ Ry≡P ⟩
         P    ≡⟨ sym Rx≡P ⟩∎
         R x  ∎)

      lemma₂ = λ x →
        _↔_.to (equality-characterisation₁ ext) (refl x)  ≡⟨⟩
        proj₁ (Σ-≡,≡←≡ (refl x))                          ≡⟨ proj₁-Σ-≡,≡←≡ _ ⟩
        cong proj₁ (refl x)                               ≡⟨ cong-refl _ ⟩∎
        refl (proj₁ x)                                    ∎

      lemma₃ =
        trans (_≃_.to strong-equivalence lemma₁) Rx≡P                    ≡⟨⟩

        trans (_≃_.to strong-equivalence
                 (_≃_.from strong-equivalence (trans Ry≡P (sym Rx≡P))))
              Rx≡P                                                       ≡⟨ cong (flip trans _) $ _≃_.right-inverse-of strong-equivalence _ ⟩

        trans (trans Ry≡P (sym Rx≡P)) Rx≡P                               ≡⟨ trans-[trans-sym]- _ _ ⟩∎

        Ry≡P                                                             ∎

      lemma₄ =
        trans (_↔_.to (related↔[equal] ext strong-equivalence) lemma₁)
              (_↔_.from (equality-characterisation₁ ext) Rx≡P)          ≡⟨⟩

        trans (_↔_.from (equality-characterisation₁ ext)
                        (_≃_.to strong-equivalence lemma₁))
              (_↔_.from (equality-characterisation₁ ext) Rx≡P)          ≡⟨ Bij.trans-to-to≡to-trans
                                                                             (λ _ _ → inverse $ equality-characterisation₁ ext)
                                                                             lemma₂ ⟩
        _↔_.from (equality-characterisation₁ ext)
                 (trans (_≃_.to strong-equivalence lemma₁) Rx≡P)        ≡⟨ cong (_↔_.from (equality-characterisation₁ ext)) lemma₃ ⟩∎

        _↔_.from (equality-characterisation₁ ext) Ry≡P                  ∎

------------------------------------------------------------------------
-- An example

module ⊤/2 where

  -- What happens if we quotient the unit type by the "binary-valued
  -- trivial relation"?

  ⊤/2 : Set₂
  ⊤/2 = ⊤ / λ _ _ → Fin 2

  -- The type is not a set (assuming extensionality and univalence).

  not-a-set :
    Extensionality (# 2) (# 1) →
    Univalence (# 0) →
    ¬ Is-set ⊤/2
  not-a-set ext univ =
    Is-set ⊤/2                              ↝⟨ F.id ⟩
    ((x y : ⊤/2) → Is-proposition (x ≡ y))  ↝⟨ (λ prop → prop _ _) ⟩
    Is-proposition ([ tt ] ≡ [ tt ])        ↝⟨ H-level.respects-surjection
                                                 (_↔_.surjection $ inverse $
                                                    related↔[equal] ext
                                                      (const-Fin-2-strong-equivalence
                                                         (lower-extensionality _ lzero ext) univ))
                                                 1 ⟩
    Is-proposition (Fin 2)                  ↝⟨ H-level.respects-surjection (_↔_.surjection $ inverse Bool↔Fin2) 1 ⟩
    Is-proposition Bool                     ↝⟨ ¬-Bool-propositional ⟩□
    ⊥                                       □

  -- The type is a groupoid (assuming extensionality and univalence).

  is-groupoid :
    Extensionality (# 2) (# 1) →
    Univalence (# 0) →
    H-level 3 ⊤/2
  is-groupoid ext univ =
    quotient's-h-level-is-1-+-relation's-h-level
      ext univ univ 2 (λ _ _ → Fin-set 2)

  -- Every value in the quotient is merely equal to [ tt ] (assuming
  -- extensionality).

  ∥≡[tt]∥ :
    Extensionality (# 2) (# 1) →
    (x : ⊤/2) → ∥ x ≡ [ tt ] ∥ 1 (# 1)
  ∥≡[tt]∥ ext x =           $⟨ []-surjective ext x ⟩
    ∥ ⊤ × [ tt ] ≡ x ∥ 1 _  ↝⟨ ∥∥-map (sym ∘ proj₂) ⟩□
    ∥ x ≡ [ tt ] ∥ 1 _      □

  -- The type is merely single-valued (assuming extensionality and a
  -- resizing function for the propositional truncation).

  merely-single-valued :
    Extensionality (# 2) (# 2) →
    ({A : Set₂} → ∥ A ∥ 1 (# 1) → ∥ A ∥ 1 (# 2)) →
    (x y : ⊤/2) → ∥ x ≡ y ∥ 1 (# 1)
  merely-single-valued ext resize x y =
    Trunc.rec
      (truncation-has-correct-h-level 1 ext)
      (λ x≡[tt] → ∥∥-map (λ y≡[tt] → x       ≡⟨ x≡[tt] ⟩
                                     [ tt ]  ≡⟨ sym y≡[tt] ⟩∎
                                     y       ∎)
                         (∥≡[tt]∥ ext′ y))
      (resize (∥≡[tt]∥ ext′ x))
    where
    ext′ = lower-extensionality lzero _ ext

  -- Every instance of the type's equality type is merely isomorphic
  -- to Fin 2 (assuming extensionality, univalence, and a resizing
  -- function for the propositional truncation).

  ∥≡↔2∥ :
    Extensionality (# 2) (# 2) →
    Univalence (# 0) →
    ({A : Set₂} → ∥ A ∥ 1 (# 1) → ∥ A ∥ 1 (# 2)) →
    (x y : ⊤/2) → ∥ x ≡ y ↔ Fin 2 ∥ 1 (# 1)
  ∥≡↔2∥ ext univ resize x y =
    Trunc.rec
      (truncation-has-correct-h-level 1 ext)
      (λ x≡[tt] →
         ∥∥-map
           (λ y≡[tt] →
              x ≡ y            ↝⟨ ≡⇒↝ _ $ cong₂ _≡_ x≡[tt] y≡[tt] ⟩
              [ tt ] ≡ [ tt ]  ↝⟨ inverse $
                                  related↔[equal]
                                    (lower-extensionality lzero _ ext)
                                    (const-Fin-2-strong-equivalence
                                       (lower-extensionality _ _ ext) univ) ⟩□
              Fin 2            □)
           (∥≡[tt]∥ (lower-extensionality lzero _ ext) y))
      (resize (∥≡[tt]∥ (lower-extensionality lzero _ ext) x))
