------------------------------------------------------------------------
-- Some results that hold for every empty-modal modality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
import Modality.Basics

module Modality.Empty-modal
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)
  (open Modality.Basics eq)
  {a}
  (M : Modality a)
  (Modal-⊥ : Empty-modal M)
  where

open Derived-definitions-and-properties eq

open Modality M

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Accessibility eq as A using (Acc)
open import Bijection eq as Bijection using (_↔_)
open import Double-negation eq
open import Equality.Decidable-UIP eq
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Path-split eq as PS
  using (Is-∞-extendable-along-[_])
open import Excluded-middle eq
open import Extensionality eq
open import For-iterated-equality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Modality.Identity eq as Identity using (Identity-modality)
open import Univalence-axiom eq

private
  variable
    ℓ         : Level
    A B       : Type ℓ
    k x y _<_ : A

------------------------------------------------------------------------
-- A basic lemma

-- ◯ ⊥ is equivalent to ⊥₀.

◯⊥≃⊥ : ◯ ⊥ ≃ ⊥₀
◯⊥≃⊥ =
  ◯ ⊥  ↝⟨ inverse $ Modal→≃◯ Modal-⊥ ⟩
  ⊥    ↔⟨ ⊥↔⊥ ⟩□
  ⊥₀   □

------------------------------------------------------------------------
-- Some lemmas related to negation

-- ◯ commutes with ¬_ (assuming extensionality).

◯¬≃¬ : ◯ (¬ A) ↝[ a ∣ lzero ] ¬ ◯ A
◯¬≃¬ {A = A} = generalise-ext?
  (record
     { to = λ f x →   $⟨ _≃_.from ◯× (f , x) ⟩
         ◯ (¬ A × A)  →⟨ ◯-map (_↔_.to ⊥↔⊥ ∘ uncurry _$_) ⟩
         ◯ ⊥          ↔⟨ ◯⊥≃⊥ ⟩□
         ⊥₀           □
     ; from = λ hyp → η (hyp ∘ η)
     })
  (λ ext →
       (λ f → apply-ext ext λ x →
          ⊥-elim (f x))
     , ◯-elim
         (λ _ → Separated-◯ _ _)
         (λ f → cong η $ apply-ext ext λ x →
            ⊥-elim (f x)))

-- ◯ can be dropped under ¬_ (assuming extensionality).

¬◯≃¬ : ¬ ◯ A ↝[ a ∣ lzero ] ¬ A
¬◯≃¬ {A = A} =
  generalise-ext?-prop
    (record
       { to   = _∘ η
       ; from = λ f → ⊥-elim ∘ ◯-rec Modal-⊥ (⊥-elim ∘ f)
       })
    ¬-propositional
    ¬-propositional

-- ◯ A implies ¬ ¬ A.

◯→¬¬ : ◯ A → ¬ ¬ A
◯→¬¬ x f = _≃_.to ◯⊥≃⊥ (◯-map (⊥-elim ∘ f) x)

-- Types that are stable for double negation are stable.

¬¬-stable→Stable : (¬ ¬ A → A) → Stable A
¬¬-stable→Stable = _∘ ◯→¬¬

-- The type ¬ A is k-stable (perhaps assuming function
-- extensionality).

Stable-¬ :
  Extensionality? k a lzero →
  Stable-[ k ] (¬ A)
Stable-¬ {A = A} ext =
  ◯ (¬ A)  ↝⟨ ◯¬≃¬ ext ⟩
  ¬ (◯ A)  ↝⟨ ¬◯≃¬ ext ⟩□
  ¬ A      □

-- ¬ A is modal (assuming function extensionality).

Modal-¬ :
  Extensionality a lzero →
  Modal (¬ A)
Modal-¬ {A = A} ext =
  Is-equivalence-η→Modal $
  _≃_.is-equivalence $
  Eq.with-other-function
    (inverse $ Stable-¬ ext)
    η
    (λ empty → cong η $ apply-ext ext (⊥-elim ∘ empty))

------------------------------------------------------------------------
-- Some lemmas related to Dec

-- Dec A implies Dec (◯ A).
--
-- This result appears in (at least one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory" by Rijke, Shulman
-- and Spitters.

Dec→Dec-◯ : Dec A → Dec (◯ A)
Dec→Dec-◯ (yes x)    = yes (η x)
Dec→Dec-◯ (no empty) =
  no (⊥-elim ∘ ◯-rec Modal-⊥ (⊥-elim ∘ empty))

-- Types for which it is known whether or not they are inhabited are
-- stable.

Dec→Stable : Dec A → Stable A
Dec→Stable         (yes x)    = λ _ → x
Dec→Stable {A = A} (no empty) =
  ◯ A    →⟨ ◯→¬¬ ⟩
  ¬ ¬ A  →⟨ _$ empty ⟩
  ⊥      →⟨ ⊥-elim ⟩□
  A      □

------------------------------------------------------------------------
-- Some results related to stability or modality of equality types

-- If equality is decidable for A, then A is separated.

Decidable-equality→Separated :
  Decidable-equality A → Separated A
Decidable-equality→Separated dec x y =
  Stable→Is-proposition→Modal
    (Dec→Stable (dec x y))
    (decidable⇒set dec)

-- If equality is k-stable for A and B, then equality is k-stable
-- for A ⊎ B. (The lemma is more general.)

Stable-≡-⊎ :
  ∀ n →
  For-iterated-equality (1 + n) Stable-[ k ] A →
  For-iterated-equality (1 + n) Stable-[ k ] B →
  For-iterated-equality (1 + n) Stable-[ k ] (A ⊎ B)
Stable-≡-⊎ n sA sB =
  For-iterated-equality-⊎-suc
    n
    lemma
    (Modal→Stable Modal-⊥)
    (For-iterated-equality-↑ _ (1 + n) lemma sA)
    (For-iterated-equality-↑ _ (1 + n) lemma sB)
  where
  lemma : A ↔ B → Stable-[ k ] A → Stable-[ k ] B
  lemma = Stable-respects-≃ ∘ from-isomorphism

-- If A and B are separated, then A ⊎ B is separated. (The lemma is
-- more general.)

Separated-⊎ :
  ∀ n →
  For-iterated-equality (1 + n) Modal A →
  For-iterated-equality (1 + n) Modal B →
  For-iterated-equality (1 + n) Modal (A ⊎ B)
Separated-⊎ n sA sB =
  For-iterated-equality-⊎-suc
    n
    lemma
    Modal-⊥
    (For-iterated-equality-↑ _ (1 + n) lemma sA)
    (For-iterated-equality-↑ _ (1 + n) lemma sB)
  where
  lemma : A ↔ B → Modal A → Modal B
  lemma = Modal-respects-≃ ∘ from-isomorphism

-- If equality is k-stable for A, then it is k-stable for List A.
-- (The lemma is more general.)

Stable-≡-List :
  ∀ n →
  For-iterated-equality (1 + n) Stable-[ k ] A →
  For-iterated-equality (1 + n) Stable-[ k ] (List A)
Stable-≡-List n =
  For-iterated-equality-List-suc
    n
    (Stable-respects-≃ ∘ from-isomorphism)
    (Modal→Stable Modal-⊤)
    (Modal→Stable Modal-⊥)
    Stable-×

-- If A is separated, then List A is separated. (The lemma is more
-- general.)

Separated-List :
  ∀ n →
  For-iterated-equality (1 + n) Modal A →
  For-iterated-equality (1 + n) Modal (List A)
Separated-List n =
  For-iterated-equality-List-suc
    n
    (Modal-respects-≃ ∘ from-isomorphism)
    Modal-⊤
    Modal-⊥
    (λ mA mB → Modal-Σ mA λ _ → mB)

------------------------------------------------------------------------
-- Some results that depend on excluded middle

module Excluded-middle (em : Excluded-middle a) where

  -- Propositions are modal.

  Is-proposition→Modal : Is-proposition A → Modal A
  Is-proposition→Modal prop =
    Stable→Is-proposition→Modal
      (¬¬-stable→Stable
         (Excluded-middle→Double-negation-elimination em prop ∘ wrap))
      prop

  -- If the modality is left exact, then it is cotopological.

  Left-exact→Cotopological :
    Left-exact ◯ → Cotopological ◯
  Left-exact→Cotopological lex =
      lex
    , λ {A = A} A-prop →
        ◯ -Connected A      ↔⟨⟩
        Contractible (◯ A)  →⟨ H-level-cong _ 0 $ inverse $ Modal→≃◯ $ Is-proposition→Modal A-prop ⟩□
        Contractible A      □

  -- The modality is accessibility-modal for stable relations on modal
  -- types (assuming function extensionality).

  Modal→Stable→Accessibility-modal :
    Extensionality a a →
    Modal A →
    ({x y : A} → Stable (x < y)) →
    Accessibility-modal-for _<_
  Modal→Stable→Accessibility-modal ext m s =
      (λ acc → Modal→Acc→Acc-[]◯-η m s acc)
    , Modal→Stable (Is-proposition→Modal (A.Acc-propositional ext))

  ----------------------------------------------------------------------
  -- Some results that hold if the modality is very modal (in addition
  -- to being empty-modal)

  module Very-modal (very-modal : Very-modal M) where

    -- Every type is modal (assuming function extensionality).

    modal : Extensionality a a → Modal A
    modal {A = A} ext =
                   $⟨ very-modal ⟩
      ◯ (Modal A)  →⟨ Modal→Stable $
                      Is-proposition→Modal $
                      Modal-propositional ext ⟩□
      Modal A      □

    private

      -- A lemma used below.

      Modal⇔⊤ :
        Extensionality a a →
        (A : Type a) → Modal A ⇔ ↑ a ⊤
      Modal⇔⊤ ext _ = record { from = λ _ → modal ext }

    -- The modal operator is pointwise equivalent to the identity
    -- function, and the right-to-left direction of the equivalence is
    -- pointwise equal to the modal unit (assuming function
    -- extensionality).

    ◯≃id :
      Extensionality a a →
      ∃ λ (eq : ∀ A → ◯ A ≃ A) → ∀ A → _≃_.from (eq A) ≡ η
    ◯≃id ext =                                                $⟨ Modal⇔Modal≃◯≃◯ ext Identity-modality M _
                                                                   (inverse ∘ Modal⇔⊤ ext) ⟩
      (∃ λ (eq : ∀ A → A ≃ ◯ A) → ∀ A → _≃_.to (eq A) ≡ η)    →⟨ Σ-map (inverse ∘_) id ⟩□
      (∃ λ (eq : ∀ A → ◯ A ≃ A) → ∀ A → _≃_.from (eq A) ≡ η)  □

    -- The modality is equal to one instance of the identity modality
    -- (assuming function extensionality and univalence).

    ≡Identity-modality :
      Extensionality (lsuc a) (lsuc a) →
      Univalence a →
      M ≡ Identity-modality {ℓ = a}
    ≡Identity-modality ext univ =
      _≃_.to (Modal⇔Modal≃≡ ext univ)
        (Modal⇔⊤ (lower-extensionality _ _ ext))

    -- The modality is topological (assuming function extensionality).

    topological : Extensionality a a → Topological M
    topological ext =                                            $⟨ Identity.topological ⟩

      Topological Identity-modality                              ↔⟨⟩

      (∃ λ ((_ , P , _) :
            ∃ λ (I : Type a) → ∃ λ (P : I → Type a) →
              (A : Type a) →
              ↑ a ⊤ ⇔
              ∀ i →
              Is-∞-extendable-along-[ (λ (_ : P i) → lift tt) ]
                (λ (_ : ↑ a ⊤) → A)) →
       ∀ i → Is-proposition (P i))                               →⟨ Σ-map (Σ-map id (Σ-map id ((F._∘ Modal⇔⊤ ext _) ∘_))) id ⟩

      (∃ λ ((_ , P , _) :
            ∃ λ (I : Type a) → ∃ λ (P : I → Type a) →
              (A : Type a) →
              Modal A ⇔
              ∀ i →
              Is-∞-extendable-along-[ (λ (_ : P i) → lift tt) ]
                (λ (_ : ↑ a ⊤) → A)) →
       ∀ i → Is-proposition (P i))                               ↔⟨⟩

      Topological M                                              □

    -- The modality is accessibility-modal (assuming function
    -- extensionality).

    accessibility-modal :
      Extensionality a a →
      Modality.Accessibility-modal M
    accessibility-modal ext =                         $⟨ (λ {_ _} → Identity.accessibility-modal) ⟩

      Modality.Accessibility-modal Identity-modality  ↔⟨⟩

      ({A : Type a} {_<_ : A → A → Type a} →
       (∀ {x} → Acc _<_ x → Acc IM._[ _<_ ]◯_ x) ×
       (∀ {x} → IM.Stable (Acc IM._[ _<_ ]◯_ x)))     →⟨ implicit-∀-cong _ $ implicit-∀-cong _ $
                                                         (implicit-∀-cong _ $ ∀-cong _ λ _ →
                                                          lemma₂ ∘ subst (Acc _) (sym ◯≃-η≡))
                                                           ×-cong
                                                         (implicit-Π-cong-contra _ ◯≃ λ _ →
                                                          →-cong-→ (lemma₁ ∘ _≃_.to ◯≃) lemma₂) ⟩
      ({A : Type a} {_<_ : A → A → Type a} →
       (∀ {x} → Acc _<_ x → Acc _[ _<_ ]◯_ (η x)) ×
       (∀ {x} → Stable (Acc _[ _<_ ]◯_ x)))           ↔⟨⟩

      Modality.Accessibility-modal M                  □
      where
      module IM = Modality Identity-modality

      ◯≃ : ◯ A ≃ A
      ◯≃ {A = A} = proj₁ (◯≃id ext) A

      ◯≃-η≡ : _≃_.to ◯≃ (η x) ≡ x
      ◯≃-η≡ {x = x} =
        _≃_.to ◯≃ (η x)            ≡⟨ cong (λ f → _≃_.to ◯≃ (f x)) $ sym $ proj₂ (◯≃id ext) _ ⟩
        _≃_.to ◯≃ (_≃_.from ◯≃ x)  ≡⟨ _≃_.right-inverse-of ◯≃ _ ⟩∎
        x                          ∎

      η-◯≃≡ : η (_≃_.to ◯≃ x) ≡ x
      η-◯≃≡ {x = x} =
        η (_≃_.to ◯≃ x)            ≡⟨ cong (λ f → f (_≃_.to ◯≃ x)) $ sym $ proj₂ (◯≃id ext) _ ⟩
        _≃_.from ◯≃ (_≃_.to ◯≃ x)  ≡⟨ _≃_.left-inverse-of ◯≃ _ ⟩∎
        x                          ∎

      lemma₁′ : y IM.[ _<_ ]◯ _≃_.to ◯≃ x → _≃_.from ◯≃ y [ _<_ ]◯ x
      lemma₁′ {y = y} {x = x} (y′ , x′ , ≡y′ , ≡x′ , y′<x′) =
        η ( y′
          , x′
          , (_≃_.from ◯≃ y  ≡⟨ _≃_.to-from ◯≃ ◯≃-η≡ ⟩
             η y            ≡⟨ cong η ≡y′ ⟩∎
             η y′           ∎)
          , (x                ≡⟨ sym η-◯≃≡ ⟩
             η (_≃_.to ◯≃ x)  ≡⟨ cong η ≡x′ ⟩∎
             η x′             ∎)
          , y′<x′
          )

      lemma₂′ : y [ _<_ ]◯ x → _≃_.to ◯≃ y IM.[ _<_ ]◯ _≃_.to ◯≃ x
      lemma₂′ {y = y} {x = x} y<x =
        let (y′ , x′ , y≡ , x≡ , y′<x′) = _≃_.to ◯≃ y<x in
          y′
        , x′
        , (_≃_.to ◯≃ y       ≡⟨ cong (_≃_.to ◯≃) y≡ ⟩
           _≃_.to ◯≃ (η y′)  ≡⟨ ◯≃-η≡ ⟩∎
           y′                ∎)
        , (_≃_.to ◯≃ x       ≡⟨ cong (_≃_.to ◯≃) x≡ ⟩
           _≃_.to ◯≃ (η x′)  ≡⟨ ◯≃-η≡ ⟩∎
           x′                ∎)
        , y′<x′

      lemma₁ : Acc _[ _<_ ]◯_ x → Acc IM._[ _<_ ]◯_ (_≃_.to ◯≃ x)
      lemma₁ (A.acc f) =
        A.acc λ y y< →
        subst (Acc _) (_≃_.right-inverse-of ◯≃ _) $
        lemma₁ (f (_≃_.from ◯≃ y) (lemma₁′ y<))

      lemma₂ : Acc IM._[ _<_ ]◯_ (_≃_.to ◯≃ x) → Acc _[ _<_ ]◯_ x
      lemma₂ (A.acc f) =
        A.acc λ y y< →
        lemma₂ (f (_≃_.to ◯≃ y) (lemma₂′ y<))
