------------------------------------------------------------------------
-- Quotients (set-quotients)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on the presentation of quotients in the HoTT book.
-- Perhaps that presentation is partly based on work by Voevodsky.

open import Equality

module Quotient
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bij using (_↔_)
private
  open module D = Derived-definitions-and-properties eq hiding (elim)
open import Equality.Decidable-UIP eq using (Constant)
import Equality.Groupoid eq as EG
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq as F hiding (_∘_)
open import Groupoid
open import H-level eq as H-level
open import H-level.Closure eq
open import H-level.Truncation eq hiding (rec)
open import Univalence-axiom eq

-- Equivalence classes.

_is-equivalence-class-of_ :
  ∀ {a} {A : Set a} →
  (A → Proposition a) → (A → A → Proposition a) → Set (lsuc (lsuc a))
_is-equivalence-class-of_ {a} P R =
  ∥ (∃ λ x → R x ≡ P) ∥ 1 (lsuc a)

-- Quotients.

infix 5 _/_

_/_ : ∀ {a} (A : Set a) → (A → A → Proposition a) → Set (lsuc (lsuc a))
A / R = ∃ λ (P : A → Proposition _) → P is-equivalence-class-of R

module _ {a} {A : Set a} {R : A → A → Proposition a} where

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
       subst (_is-equivalence-class-of R) eq (proj₂ x) ≡ proj₂ y)  ↝⟨ (drop-⊤-right λ _ → inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                       truncation-has-correct-h-level 1 ext _ _) ⟩□
    proj₁ x ≡ proj₁ y                                              □

  equality-characterisation₂ :
    Extensionality (lsuc (lsuc a)) (lsuc a) →
    {x y : A / R} →
    x ≡ y
      ↔
    (∀ z → proj₁ (proj₁ x z) ≡ proj₁ (proj₁ y z))
  equality-characterisation₂ ext {x} {y} =
    x ≡ y                                                          ↝⟨ equality-characterisation₁ ext ⟩

    proj₁ x ≡ proj₁ y                                              ↔⟨ inverse $ Eq.extensionality-isomorphism
                                                                                  (lower-extensionality _ lzero ext) ⟩
    (∀ z → proj₁ x z ≡ proj₁ y z)                                  ↔⟨ (Eq.∀-preserves (lower-extensionality _ lzero ext) λ z →
                                                                       Eq.↔⇒≃ $ inverse $
                                                                       ignore-propositional-component
                                                                         (H-level-propositional (lower-extensionality _ _ ext) 1)) ⟩□
    (∀ z → proj₁ (proj₁ x z) ≡ proj₁ (proj₁ y z))                  □

  equality-characterisation₃ :
    Extensionality (lsuc (lsuc a)) (lsuc a) →
    Univalence a →
    {x y : A / R} →
    x ≡ y
      ↔
    (∀ z → proj₁ (proj₁ x z) ⇔ proj₁ (proj₁ y z))
  equality-characterisation₃ ext univ {x} {y} =
    x ≡ y                                          ↝⟨ equality-characterisation₂ ext ⟩

    (∀ z → proj₁ (proj₁ x z) ≡ proj₁ (proj₁ y z))  ↔⟨ (Eq.∀-preserves (lower-extensionality _ lzero ext) λ _ →
                                                       ≡≃≃ univ) ⟩
    (∀ z → proj₁ (proj₁ x z) ≃ proj₁ (proj₁ y z))  ↔⟨ (Eq.∀-preserves (lower-extensionality _ _ ext) λ z →
                                                       Eq.↔⇒≃ $ inverse $
                                                       Eq.⇔↔≃ (lower-extensionality _ _ ext)
                                                              (proj₂ (proj₁ x z))
                                                              (proj₂ (proj₁ y z))) ⟩□
    (∀ z → proj₁ (proj₁ x z) ⇔ proj₁ (proj₁ y z))  □

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

  -- The following definitions make use of extensionality and
  -- univalence.

  module _
    (ext  : Extensionality (lsuc (lsuc a)) (lsuc a))
    (univ : Univalence a)
    where

    -- A / R is a set.

    /-is-set : Is-set (A / R)
    /-is-set x y =                                                    $⟨ (λ z → H-level-H-level-≡ˡ
                                                                                  (lower-extensionality _ _ ext) univ 0
                                                                                  (proj₂ (proj₁ x z))) ⟩
      (∀ z → Is-proposition (proj₁ (proj₁ x z) ≡ proj₁ (proj₁ y z)))  ↝⟨ Π-closure (lower-extensionality _ lzero ext) 1 ⟩
      Is-proposition (∀ z → proj₁ (proj₁ x z) ≡ proj₁ (proj₁ y z))    ↝⟨ H-level.respects-surjection
                                                                           (_↔_.surjection (inverse $ equality-characterisation₂ ext))
                                                                           1 ⟩□
      Is-proposition (x ≡ y)                                          □

    -- The following definitions also make use of symmetry and
    -- transitivity.

    module _
      (sym   : ∀ {x y} → proj₁ (R x y) → proj₁ (R y x))
      (trans : ∀ {x y z} →
               proj₁ (R x y) → proj₁ (R y z) → proj₁ (R x z))
      where

      private

        -- A simple lemma.

        simple-lemma :
          ∀ {x} {y} →
          proj₁ (R x y) → ∀ z → proj₁ (R x z) ⇔ proj₁ (R y z)
        simple-lemma {x} {y} Rxy z =
          record { to   = proj₁ (R x z)  ↝⟨ trans (sym Rxy) ⟩□
                          proj₁ (R y z)  □
                 ; from = proj₁ (R y z)  ↝⟨ trans Rxy ⟩□
                          proj₁ (R x z)  □
                 }

      -- [_] maps related values to equal values.

      []-respects-relation :
        ∀ {x y} → proj₁ (R x y) → [ x ] ≡ [ y ]
      []-respects-relation Rxy =
        _↔_.from (equality-characterisation₃ ext univ)
                 (simple-lemma Rxy)

      -- The following definitions also make use of reflexivity.

      module _ (refl : ∀ {x} → proj₁ (R x x)) where

        -- The relation is isomorphic to equality under [_].

        related↔[equal] :
          ∀ {x y} → proj₁ (R x y) ↔ [ x ] ≡ [ y ]
        related↔[equal] {x} {y} =
          proj₁ (R x y)                          ↝⟨ lemma ⟩
          (∀ z → proj₁ (R x z) ⇔ proj₁ (R y z))  ↝⟨ inverse $ equality-characterisation₃ ext univ ⟩□
          [ x ] ≡ [ y ]                          □
          where
          -- Note the similarity with Π≡≃≡-↔-≡.
          lemma = record
            { surjection = record
              { logical-equivalence = record
                { to   = simple-lemma
                ; from = λ Rx⇔Ry →                $⟨ refl ⟩
                                   proj₁ (R y y)  ↝⟨ _⇔_.from (Rx⇔Ry y) ⟩□
                                   proj₁ (R x y)  □
                }
              ; right-inverse-of = λ _ →
                  _⇔_.to propositional⇔irrelevant
                    (Π-closure (lower-extensionality _ _ ext) 1 λ z →
                     H-level.respects-surjection
                       (_↔_.surjection $ inverse $
                        Eq.⇔↔≃ (lower-extensionality _ _ ext)
                               (proj₂ (R x z))
                               (proj₂ (R y z)))
                       1
                       (Eq.left-closure (lower-extensionality _ _ ext)
                                        0 (proj₂ (R x z))))
                    _ _
              }
            ; left-inverse-of = λ _ →
                _⇔_.to propositional⇔irrelevant
                  (proj₂ (R x y))
                  _ _
            }

        -- Eliminator.

        elim :
          (P : A / R → Set (lsuc a)) →
          (∀ x → Is-set (P x)) →
          (f : ∀ x → P [ x ]) →
          (∀ {x y} (Rxy : proj₁ (R x y)) →
             subst P ([]-respects-relation Rxy) (f x) ≡ f y) →
          ∀ x → P x
        elim P P-set f R⇒≡ (Q , Q-is-class) =
          _≃_.to (constant-function≃∥inhabited∥⇒inhabited
                    lzero ext (P-set _))
            (f′ , f′-constant)
            Q-is-class
          where
          f′ : (∃ λ x → R x ≡ Q) → P (Q , Q-is-class)
          f′ (x , Rx≡Q) =
            subst P
                  (_↔_.from (equality-characterisation₁ ext) Rx≡Q)
                  (f x)

          f′-constant : Constant f′
          f′-constant (x₁ , Rx₁≡Q) (x₂ , Rx₂≡Q) =
            subst P
                  (_↔_.from (equality-characterisation₁ ext) Rx₁≡Q)
                  (f x₁)                                                    ≡⟨ cong (subst _ _) $ D.sym $ R⇒≡ _ ⟩

            subst P
                  (_↔_.from (equality-characterisation₁ ext) Rx₁≡Q)
                  (subst P ([]-respects-relation lemma) (f x₂))             ≡⟨ subst-subst _ _ _ _ ⟩

            subst P
                  (D.trans ([]-respects-relation lemma)
                           (_↔_.from (equality-characterisation₁ ext)
                                     Rx₁≡Q))
                  (f x₂)                                                    ≡⟨ cong (λ eq → subst P eq _) $
                                                                               _⇔_.to set⇔UIP /-is-set _ _ ⟩∎
            subst P
                  (_↔_.from (equality-characterisation₁ ext) Rx₂≡Q)
                  (f x₂)                                                    ∎
            where
            lemma =            $⟨ refl ⟩
              proj₁ (R x₁ x₁)  ↝⟨ ≡⇒↝ implication (cong (λ P → proj₁ (P x₁)) Rx₁≡Q) ⟩
              proj₁ (Q x₁)     ↝⟨ ≡⇒↝ implication (cong (λ P → proj₁ (P x₁)) (D.sym Rx₂≡Q)) ⟩□
              proj₁ (R x₂ x₁)  □

  module _
    (ext  : Extensionality (lsuc (lsuc a)) (lsuc a))
    (refl : ∀ {x} → proj₁ (R x x))
    where

    -- Recursor.

    rec :
      (P : Set a) →
      Is-set P →
      (f : A → P) →
      (∀ {x y} → proj₁ (R x y) → f x ≡ f y) →
      A / R → P
    rec P P-set f R⇒≡ (Q , Q-is-class) =
      _≃_.to (constant-function≃∥inhabited∥⇒inhabited lzero ext P-set)
        (f′ , f′-constant)
        Q-is-class
      where
      f′ : (∃ λ x → R x ≡ Q) → P
      f′ (x , _) = f x

      f′-constant : Constant f′
      f′-constant (x₁ , Rx₁≡Q) (x₂ , Rx₂≡Q) = R⇒≡ (
                         $⟨ refl ⟩
        proj₁ (R x₂ x₂)  ↝⟨ ≡⇒→ $ cong (λ P → proj₁ (P x₂)) Rx₂≡Q ⟩
        proj₁ (Q x₂)     ↝⟨ ≡⇒→ $ cong (λ P → proj₁ (P x₂)) $ sym Rx₁≡Q ⟩□
        proj₁ (R x₁ x₂)  □)

    private

      -- The recursor's computation rule holds definitionally.

      rec-[] :
        (P : Set a)
        (P-set : Is-set P)
        (f : A → P)
        (R⇒≡ : ∀ {x y} → proj₁ (R x y) → f x ≡ f y)
        (x : A) →
        rec P P-set f R⇒≡ [ x ] ≡ f x
      rec-[] _ _ _ _ _ = D.refl _
