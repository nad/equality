------------------------------------------------------------------------
-- Erased univalence is incompatible with certain features
------------------------------------------------------------------------

-- This module contains some examples taken from (or based on)
-- "Compiling Programs with Erased Univalence" by Abel, Danielsson and
-- Vezzosi.

-- The K rule is turned on in order to enable some of the definitions
-- below. The K rule itself is not needed, but at the time of writing
-- Agda only allows erased matches for identity types if the K rule is
-- turned on.

{-# OPTIONS --with-K --safe #-}

module Univalence-axiom.Incompatible where

open import Equality
import Equality.Decision-procedures
import Equality.Propositional
import Equivalence
import Erased
import Erased.Box-cong-axiomatisation
import Erased.Level-1
import Erased.Stability
import Function-universe
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (swap)
import Univalence-axiom

private variable
  a     : Level
  A     : Type a
  x y p : A
  P     : A → Type p

------------------------------------------------------------------------
-- A variant of subst that takes an erased equality argument is
-- incompatible with erased univalence

module Bad-subst₂
  -- This module uses the standard identity type.
  (open Equality.Propositional)
  (open Univalence-axiom equality-with-J)
  -- Instead of using postulated univalence the code uses a module
  -- parameter.
  (@0 univalence : ∀ {a} → Univalence a)
  where

  open Equality.Decision-procedures equality-with-J
  open Erased.Level-1 equality-with-J
  open Erased.Stability equality-with-J
  open Function-universe equality-with-J

  -- A problematic variant of subst.

  bad-subst₂ : (P : A → Type p) → @0 x ≡ y → P x → P y
  bad-subst₂ P refl p = p

  -- In erased contexts bad-subst₂ is pointwise equal to subst.

  @0 bad-subst₂≡subst :
    (eq : x ≡ y) → bad-subst₂ P eq p ≡ subst P eq p
  bad-subst₂≡subst refl = refl

  -- An equality between Bool and Bool, implemented using univalence
  -- and the not function.

  @0 swap : Bool ≡ Bool
  swap = swap-as-an-equality univalence

  -- A boolean that should be true.

  should-be-true : Bool
  should-be-true = bad-subst₂ (λ A → A) refl true

  -- A boolean that should be false.

  should-be-false : Bool
  should-be-false = bad-subst₂ (λ A → A) swap true

  -- The boolean should-be-true is equal to true.

  is-true : should-be-true ≡ true
  is-true = refl

  -- The boolean should-be-false is equal to false.

  is-false : should-be-false ≡ false
  is-false =
    Dec→Stable (_ Bool.≟ _)
      [ bad-subst₂ (λ A → A) swap true  ≡⟨ bad-subst₂≡subst swap ⟩
        subst (λ A → A) swap true       ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence {A≡B = swap} ⟩
        ≡⇒→ swap true                   ≡⟨ cong (_$ true) $ ≡⇒→-≃⇒≡ equivalence univalence ⟩∎
        false                           ∎
      ]

------------------------------------------------------------------------
-- A variant of subst that takes an erased "motive" is incompatible
-- with erased univalence if []-cong is available

module Bad-subst₁
  -- This module uses the standard identity type.
  (open Equality.Propositional)
  (open Erased.Box-cong-axiomatisation equality-with-J)
  (open Univalence-axiom equality-with-J)
  -- Instead of using postulated univalence the code uses a module
  -- parameter.
  (@0 univalence : ∀ {a} → Univalence a)
  -- It is also assumed that []-cong is available.
  (ax : ∀ {a} → []-cong-axiomatisation a)
  where

  open Equality.Decision-procedures equality-with-J
  open Erased equality-with-J ax
  open Function-universe equality-with-J hiding (id; _∘_)

  -- A problematic variant of subst.

  bad-subst₁ : (@0 P : A → Type p) → x ≡ y → P x → P y
  bad-subst₁ P refl p = p

  -- In erased contexts bad-subst₁ is pointwise equal to subst.

  @0 bad-subst₁≡subst :
    (eq : x ≡ y) → bad-subst₁ P eq p ≡ subst P eq p
  bad-subst₁≡subst refl = refl

  -- An equality between Bool and Bool, implemented using univalence
  -- and the not function.

  @0 swap : Bool ≡ Bool
  swap = swap-as-an-equality univalence

  -- A boolean that should be true.

  should-be-true : Bool
  should-be-true = bad-subst₁ erased ([]-cong [ refl ]) true

  -- A boolean that should be false.

  should-be-false : Bool
  should-be-false = bad-subst₁ erased ([]-cong [ swap ]) true

  -- The boolean should-be-true is equal to true.

  is-true : should-be-true ≡ true
  is-true =
    bad-subst₁ erased ([]-cong [ refl ]) true   ≡⟨ cong (flip (bad-subst₁ erased) _) []-cong-[refl] ⟩
    bad-subst₁ {y = [ Bool ]} erased refl true  ≡⟨⟩
    true                                        ∎

  -- The boolean should-be-false is equal to false.

  is-false : should-be-false ≡ false
  is-false =
    Dec→Stable (_ Bool.≟ _)
      [ bad-subst₁ erased ([]-cong [ swap ]) true  ≡⟨ bad-subst₁≡subst ([]-cong [ swap ]) ⟩
        subst erased ([]-cong [ swap ]) true       ≡⟨ cong (flip (subst _) _) $ []-cong-[]≡cong-[] {x≡y = swap} ⟩
        subst erased (cong [_]→ swap) true         ≡⟨ sym $ subst-∘ _ _ swap ⟩
        subst (erased ∘ [_]→) swap true            ≡⟨⟩
        subst id swap true                         ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence {A≡B = swap} ⟩
        ≡⇒→ swap true                              ≡⟨ cong (_$ true) $ ≡⇒→-≃⇒≡ equivalence univalence ⟩∎
        false                                      ∎
      ]

------------------------------------------------------------------------
-- An identity type with erased arguments

module Bad-Id where

  -- An identity type with erased arguments (except for the universe
  -- level).

  data Id₀ (@0 A : Type a) (@0 x : A) : @0 A → Type a where
    refl : Id₀ A x x

  -- This type is an "equality with J".

  reflexive-relation : ∀ ℓ → Reflexive-relation ℓ
  Reflexive-relation._≡_  (reflexive-relation _) = λ x y → Id₀ _ x y
  Reflexive-relation.refl (reflexive-relation _) = λ _ → refl

  equality-with-J₀ : ∀ {a p} → Equality-with-J₀ a p reflexive-relation
  Equality-with-J₀.elim      equality-with-J₀ _ r refl = r _
  Equality-with-J₀.elim-refl equality-with-J₀ _ _      = refl

  equivalence-relation⁺ : ∀ ℓ → Equivalence-relation⁺ ℓ
  equivalence-relation⁺ _ = J₀⇒Equivalence-relation⁺ equality-with-J₀

  equality-with-J : ∀ {a p} → Equality-with-J a p equivalence-relation⁺
  equality-with-J = J₀⇒J equality-with-J₀

  open Derived-definitions-and-properties equality-with-J public
    hiding (refl; reflexive-relation; equality-with-J₀)

------------------------------------------------------------------------
-- An identity type with erased arguments (except for the universe
-- level) is incompatible with erased univalence, stated for that
-- identity type, if []-cong is available for that identity type

module Bad-id₁
  -- In this module univalence and []-cong are stated for Id₀, and Id₀
  -- is used to state some results.
  (open Bad-Id)
  (open Erased.Box-cong-axiomatisation equality-with-J)
  (open Univalence-axiom equality-with-J)
  -- Instead of using postulated univalence the code uses a module
  -- parameter.
  (@0 univalence : ∀ {a} → Univalence a)
  -- It is also assumed that []-cong is available.
  (ax : ∀ {a} → []-cong-axiomatisation a)
  where

  open Equality.Decision-procedures equality-with-J
  open Erased equality-with-J ax
  open Function-universe equality-with-J

  private variable
    eq : Id₀ _ _ _

  -- An equality between Bool and Bool, implemented using univalence
  -- and the not function.

  @0 swap : Id₀ Type Bool Bool
  swap = swap-as-an-equality univalence

  -- A function that can "resurrect" erased identity proofs.

  resurrect : @0 Id₀ A x y → Id₀ A x y
  resurrect {A} {x} eq =
    subst (λ y → Id₀ A x (erased y)) ([]-cong [ eq ]) refl

  -- The equality resurrect eq is equal to eq.

  resurrect-id : Id₀ (Id₀ A x y) (resurrect eq) eq
  resurrect-id {A} {x} {eq = refl} =
    subst (λ y → Id₀ A x (erased y)) ([]-cong [ refl ]) refl  ≡⟨ cong (flip (subst _) _) []-cong-[refl] ⟩
    subst {y = [ _ ]} (λ y → Id₀ A x (erased y)) refl refl    ≡⟨⟩
    refl                                                      ∎

  -- A boolean that should be true.

  should-be-true : Bool
  should-be-true = subst (λ A → A) (resurrect refl) true

  -- A boolean that should be false.

  should-be-false : Bool
  should-be-false = subst (λ A → A) (resurrect swap) true

  -- The boolean should-be-true is equal to true.

  is-true : Id₀ Bool should-be-true true
  is-true =
    subst (λ A → A) (resurrect refl) true  ≡⟨ cong (flip (subst _) _) resurrect-id ⟩
    subst (λ A → A) refl true              ≡⟨⟩
    true                                   ∎

  -- The boolean should-be-false is equal to false.

  is-false : Id₀ Bool should-be-false false
  is-false =
    Dec→Stable (_ Bool.≟ _)
      [ subst (λ A → A) (resurrect swap) true  ≡⟨ cong (flip (subst _) _) resurrect-id ⟩
        subst (λ A → A) swap true              ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence {A≡B = swap} ⟩
        ≡⇒→ swap true                          ≡⟨ cong (_$ true) $ ≡⇒→-≃⇒≡ equivalence univalence ⟩∎
        false                                  ∎
      ]

------------------------------------------------------------------------
-- An identity type with erased arguments (except for the universe
-- level) is incompatible with erased univalence, stated for the
-- standard identity type, if []-cong is available for the standard
-- identity type

module Bad-id₂
  -- In this module univalence and []-cong are stated for the standard
  -- identity type.
  (open Erased.Box-cong-axiomatisation
          Equality.Propositional.equality-with-J)
  (open Univalence-axiom
          Equality.Propositional.equality-with-J)
  -- Instead of using postulated univalence the code uses a module
  -- parameter.
  (@0 univalence : ∀ {a} → Univalence a)
  -- It is also assumed that []-cong is available.
  (ax : ∀ {a} → []-cong-axiomatisation a)
  where

  open Bad-Id hiding (_≡_; equality-with-J)
  open Equality.Propositional using (_≡_; refl)
  open Equality.Decision-procedures Bad-Id.equality-with-J
  open Equivalence Bad-Id.equality-with-J

  private

    module EP = Equality.Propositional
    module E₁ = Erased EP.equality-with-J ax
    module E₂ = Erased.Level-1 Bad-Id.equality-with-J
    module F₁ = Function-universe EP.equality-with-J
    module F₂ = Function-universe Bad-Id.equality-with-J

    variable
      eq : Id₀ _ _ _

    -- One can convert between Id₀ and the standard identity type.

    Id₀→ : Id₀ A x y → x ≡ y
    Id₀→ refl = refl

    →Id₀ : x ≡ y → Id₀ A x y
    →Id₀ refl = refl

    -- One can define []-cong for Id₀ in terms of []-cong for the
    -- standard identity type.

    ax′ : E₂.[]-cong-axiomatisation a
    ax′ =
      record
        { []-cong = λ eq →
            →Id₀ (E₁.[]-cong E₁.[ Id₀→ (E₁.erased eq) ])
        ; []-cong-[refl] =
            →Id₀ (E₁.[]-cong E₁.[ refl ])  ≡⟨ cong →Id₀ (→Id₀ E₁.[]-cong-[refl]) ⟩
            →Id₀ refl                      ≡⟨⟩
            refl                           ∎
        }

  open Erased Bad-Id.equality-with-J ax′

  -- An equality between Bool and Bool, implemented using univalence
  -- and the not function.

  @0 swap : Bool ≡ Bool
  swap = swap-as-an-equality univalence

  -- A function that can "resurrect" erased identity proofs.

  resurrect : @0 Id₀ A x y → Id₀ A x y
  resurrect {A} {x} eq =
    subst (λ y → Id₀ A x (erased y)) ([]-cong [ eq ]) refl

  -- The equality resurrect eq is equal to eq.

  resurrect-id : Id₀ (Id₀ A x y) (resurrect eq) eq
  resurrect-id {A} {x} {eq = refl} =
    subst (λ y → Id₀ A x (erased y)) ([]-cong [ refl ]) refl  ≡⟨ cong (flip (subst _) _) []-cong-[refl] ⟩
    subst {y = [ _ ]} (λ y → Id₀ A x (erased y)) refl refl    ≡⟨⟩
    refl                                                      ∎

  -- A boolean that should be true.

  should-be-true : Bool
  should-be-true = subst (λ A → A) (resurrect refl) true

  -- A boolean that should be false.

  should-be-false : Bool
  should-be-false = subst (λ A → A) (resurrect (→Id₀ swap)) true

  -- The boolean should-be-true is equal to true.

  is-true : should-be-true ≡ true
  is-true =
    Id₀→
      (subst (λ A → A) (resurrect refl) true  ≡⟨ cong (flip (subst _) _) resurrect-id ⟩
       subst (λ A → A) refl true              ≡⟨⟩
       true                                   ∎)

  -- The boolean should-be-false is equal to false.

  is-false : should-be-false ≡ false
  is-false =
    Id₀→ $ Dec→Stable (_ Bool.≟ _)
      [ subst (λ A → A) (resurrect (→Id₀ swap)) true     ≡⟨ cong (flip (subst _) _) $ resurrect-id {eq = →Id₀ swap} ⟩
        subst (λ A → A) (→Id₀ swap) true                 ≡⟨ F₂.subst-id-in-terms-of-≡⇒↝ F₂.equivalence {A≡B = →Id₀ swap} ⟩
        _≃_.to (F₂.≡⇒↝ F₂.equivalence (→Id₀ swap)) true  ≡⟨ EP.elim¹
                                                              (λ eq → Id₀ _ (_≃_.to (F₂.≡⇒↝ F₂.equivalence (→Id₀ eq)) true) (≡⇒→ eq true))
                                                              refl swap ⟩
        ≡⇒→ swap true                                    ≡⟨ cong (_$ true) $ →Id₀ $ ≡⇒→-≃⇒≡ F₁.equivalence univalence ⟩∎
        false                                            ∎
      ]
