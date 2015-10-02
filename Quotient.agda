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
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq as F
open import H-level eq as H-level
open import H-level.Closure eq
open import H-level.Truncation eq hiding (rec)
open import Univalence-axiom eq

-- Equivalence classes.

_is-equivalence-class-of_ :
  ∀ {a} {A : Set a} →
  (A → Proposition a) → (A → A → Proposition a) → Set (lsuc a)
_is-equivalence-class-of_ {a} P R =
  ∥ (∃ λ x → ∀ y → proj₁ (R x y) ⇔ proj₁ (P y)) ∥ 1 a

-- Quotients.

infix 5 _/_

_/_ : ∀ {a} (A : Set a) → (A → A → Proposition a) → Set (lsuc a)
A / R = ∃ λ (P : A → Proposition _) → P is-equivalence-class-of R

module _ {a} {A : Set a} {R : A → A → Proposition a} where

  -- Equality characterisation lemmas for the quotient type.

  equality-characterisation₁ :
    Extensionality (lsuc a) (lsuc a) →
    {x y : A / R} →
    x ≡ y
      ↔
    (∀ z → proj₁ (proj₁ x z) ≡ proj₁ (proj₁ y z))
  equality-characterisation₁ ext {x} {y} =
    x ≡ y                                                          ↝⟨ inverse Bij.Σ-≡,≡↔≡ ⟩

    (∃ λ (eq : proj₁ x ≡ proj₁ y) →
       subst (_is-equivalence-class-of R) eq (proj₂ x) ≡ proj₂ y)  ↝⟨ (drop-⊤-right λ _ → inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                       truncation-has-correct-h-level 1
                                                                         (lower-extensionality lzero (lsuc a) ext)
                                                                         _ _) ⟩
    proj₁ x ≡ proj₁ y                                              ↔⟨ inverse $ Eq.extensionality-isomorphism
                                                                                  (lower-extensionality (lsuc a) a ext) ⟩
    (∀ z → proj₁ x z ≡ proj₁ y z)                                  ↔⟨ (Eq.∀-preserves (lower-extensionality (lsuc a) a ext) λ z →
                                                                       Eq.↔⇒≃ $ inverse $
                                                                       ignore-propositional-component
                                                                         (H-level-propositional (lower-extensionality _ _ ext) 1)) ⟩□
    (∀ z → proj₁ (proj₁ x z) ≡ proj₁ (proj₁ y z))                  □

  equality-characterisation₂ :
    Extensionality (lsuc a) (lsuc a) →
    Univalence a →
    {x y : A / R} →
    x ≡ y
      ↔
    (∀ z → proj₁ (proj₁ x z) ⇔ proj₁ (proj₁ y z))
  equality-characterisation₂ ext univ {x} {y} =
    x ≡ y                                          ↝⟨ equality-characterisation₁ ext ⟩

    (∀ z → proj₁ (proj₁ x z) ≡ proj₁ (proj₁ y z))  ↔⟨ (Eq.∀-preserves (lower-extensionality (lsuc a) a ext) λ _ →
                                                       ≡≃≃ univ) ⟩
    (∀ z → proj₁ (proj₁ x z) ≃ proj₁ (proj₁ y z))  ↔⟨ (Eq.∀-preserves (lower-extensionality (lsuc a) _ ext) λ z →
                                                       Eq.↔⇒≃ $ inverse $
                                                       Eq.⇔↔≃ (lower-extensionality _ _ ext)
                                                              (proj₂ (proj₁ x z))
                                                              (proj₂ (proj₁ y z))) ⟩□
    (∀ z → proj₁ (proj₁ x z) ⇔ proj₁ (proj₁ y z))  □

  -- Constructor for the quotient type.

  [_] : A → A / R
  [ a ] = R a , ∣ (a , λ _ → F.id) ∣

  -- The following definitions make use of extensionality and
  -- univalence.

  module _
    (ext  : Extensionality (lsuc a) (lsuc a))
    (univ : Univalence a)
    where

    -- [_] is surjective.

    []-surjective : Surjective a [_]
    []-surjective (P , P-is-class) =
      ∥∥-map
        (Σ-map
           F.id
           (λ {x} Rx⇔P →
              [ x ]             ≡⟨ _↔_.from (equality-characterisation₂ ext univ) Rx⇔P ⟩∎
              (P , P-is-class)  ∎))
        P-is-class

    -- A / R is a set.

    /-is-set : Is-set (A / R)
    /-is-set x y =                                                    $⟨ (λ z → H-level-H-level-≡ˡ
                                                                                  (lower-extensionality _ _ ext) univ 0
                                                                                  (proj₂ (proj₁ x z))) ⟩
      (∀ z → Is-proposition (proj₁ (proj₁ x z) ≡ proj₁ (proj₁ y z)))  ↝⟨ Π-closure (lower-extensionality (lsuc a) a ext) 1 ⟩
      Is-proposition (∀ z → proj₁ (proj₁ x z) ≡ proj₁ (proj₁ y z))    ↝⟨ H-level.respects-surjection
                                                                           (_↔_.surjection (inverse $ equality-characterisation₁ ext))
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
        _↔_.from (equality-characterisation₂ ext univ)
                 (simple-lemma Rxy)

      -- The following definitions also make use of reflexivity.

      module _ (refl : ∀ {x} → proj₁ (R x x)) where

        -- The relation is isomorphic to equality under [_].

        related↔[equal] :
          ∀ {x y} → proj₁ (R x y) ↔ [ x ] ≡ [ y ]
        related↔[equal] {x} {y} =
          proj₁ (R x y)                          ↝⟨ lemma ⟩
          (∀ z → proj₁ (R x z) ⇔ proj₁ (R y z))  ↝⟨ inverse $ equality-characterisation₂ ext univ ⟩□
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
          (P : A / R → Set a) →
          (∀ x → Is-set (P x)) →
          (f : ∀ x → P [ x ]) →
          (∀ {x y} (Rxy : proj₁ (R x y)) →
             subst P ([]-respects-relation Rxy) (f x) ≡ f y) →
          ∀ x → P x
        elim P P-set f R⇒≡ (Q , Q-is-class) =
          _≃_.to (constant-function≃∥inhabited∥⇒inhabited
                    lzero
                    (lower-extensionality lzero _ ext)
                    (P-set _))
            (f′ , f′-constant)
            Q-is-class
          where
          f′ : (∃ λ x → ∀ y → proj₁ (R x y) ⇔ proj₁ (Q y)) →
               P (Q , Q-is-class)
          f′ (x , Rx⇔Q) =
            subst P
                  (_↔_.from (equality-characterisation₂ ext univ) Rx⇔Q)
                  (f x)

          f′-constant : Constant f′
          f′-constant (x₁ , Rx₁⇔Q) (x₂ , Rx₂⇔Q) =
            subst P
                  (_↔_.from (equality-characterisation₂ ext univ) Rx₁⇔Q)
                  (f x₁)                                                    ≡⟨ cong (subst _ _) $ D.sym $ R⇒≡ _ ⟩

            subst P
                  (_↔_.from (equality-characterisation₂ ext univ) Rx₁⇔Q)
                  (subst P ([]-respects-relation lemma) (f x₂))             ≡⟨ subst-subst _ _ _ _ ⟩

            subst P
                  (D.trans ([]-respects-relation lemma)
                           (_↔_.from (equality-characterisation₂ ext univ)
                                     Rx₁⇔Q))
                  (f x₂)                                                    ≡⟨ cong (λ eq → subst P eq _) $
                                                                               _⇔_.to set⇔UIP /-is-set _ _ ⟩∎
            subst P
                  (_↔_.from (equality-characterisation₂ ext univ) Rx₂⇔Q)
                  (f x₂)                                                    ∎
            where
            lemma =            $⟨ refl ⟩
              proj₁ (R x₁ x₁)  ↝⟨ Rx₁⇔Q x₁ ⟩
              proj₁ (Q x₁)     ↝⟨ inverse (Rx₂⇔Q x₁) ⟩□
              proj₁ (R x₂ x₁)  □

  -- Recursor.

  rec :
    Extensionality (lsuc a) a →
    (∀ {x} → proj₁ (R x x)) →
    (P : Set a) →
    Is-set P →
    (f : A → P) →
    (∀ {x y} → proj₁ (R x y) → f x ≡ f y) →
    A / R → P
  rec ext refl P P-set f R⇒≡ (Q , Q-is-class) =
    _≃_.to (constant-function≃∥inhabited∥⇒inhabited lzero ext P-set)
      (f′ , f′-constant)
      Q-is-class
    where
    f′ : (∃ λ x → ∀ y → proj₁ (R x y) ⇔ proj₁ (Q y)) → P
    f′ (x , _) = f x

    f′-constant : Constant f′
    f′-constant (x₁ , Rx₁⇔Q) (x₂ , Rx₂⇔Q) = R⇒≡ (
                       $⟨ refl ⟩
      proj₁ (R x₂ x₂)  ↝⟨ Rx₂⇔Q x₂ ⟩
      proj₁ (Q x₂)     ↝⟨ inverse (Rx₁⇔Q x₂) ⟩□
      proj₁ (R x₁ x₂)  □)

  private

    -- The recursor's computation rule holds definitionally.

    rec-[] :
      (ext : Extensionality (lsuc a) a)
      (refl : ∀ {x} → proj₁ (R x x))
      (P : Set a)
      (P-set : Is-set P)
      (f : A → P)
      (R⇒≡ : ∀ {x y} → proj₁ (R x y) → f x ≡ f y)
      (x : A) →
      rec ext refl P P-set f R⇒≡ [ x ] ≡ f x
    rec-[] _ _ _ _ _ _ _ = D.refl _
