------------------------------------------------------------------------
-- Some parts of Erased.Stability that do not require --cubical to be
-- active
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Erased.Stability.Without-K
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open import Embedding eq using (Is-embedding)
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Erased.Without-K eq
open import Function-universe eq hiding (_∘_)
open import H-level.Closure eq
open import Surjection eq using (_↠_; Split-surjective)

private
  variable
    a ℓ p : Level
    A B   : Set a
    P     : A → Set p
    k x   : A

------------------------------------------------------------------------
-- Stability

mutual

  -- A type is stable if Erased A implies A.

  Stable : Set a → Set a
  Stable = Stable-[ implication ]

  -- A generalisation of Stable.

  Stable-[_] : Kind → Set a → Set a
  Stable-[ k ] A = Erased A ↝[ k ] A

-- A special case of Stable-[ equivalence ].

Very-stable : Set a → Set a
Very-stable A = Is-equivalence ([_] {A = A})

-- Variants of the definitions above for equality.

mutual

  Stable-≡ : Set a → Set a
  Stable-≡ A = Stable-≡-[ implication ] A

  Stable-≡-[_] : Kind → Set a → Set a
  Stable-≡-[ k ] A = {x y : A} → Stable-[ k ] (x ≡ y)

Very-stable-≡ : Set a → Set a
Very-stable-≡ A = {x y : A} → Very-stable (x ≡ y)

------------------------------------------------------------------------
-- Some lemmas related to stability

-- If A is very stable, then [_] {A = A} is an embedding.

Very-stable→Is-embedding-[] :
  Very-stable A → Is-embedding ([_] {A = A})
Very-stable→Is-embedding-[] {A = A} s x y =
  _≃_.is-equivalence ≡≃[]≡[]
  where
  A≃Erased-A : A ≃ Erased A
  A≃Erased-A = Eq.⟨ _ , s ⟩

  ≡≃[]≡[] : (x ≡ y) ≃ ([ x ] ≡ [ y ])
  ≡≃[]≡[] = inverse $ Eq.≃-≡ A≃Erased-A

-- If A is very stable, then [_] {A = A} is split surjective.

Very-stable→Split-surjective-[] :
  Very-stable A → Split-surjective ([_] {A = A})
Very-stable→Split-surjective-[] {A = A} =
  Very-stable A         ↔⟨⟩
  Is-equivalence [_]    ↝⟨ (λ hyp → _↠_.split-surjective $ _≃_.surjection $ Eq.⟨ _ , hyp ⟩) ⟩
  Split-surjective [_]  □

-- Very-stable is propositional (assuming extensionality).

Very-stable-propositional :
  {A : Set a} →
  Extensionality a a →
  Is-proposition (Very-stable A)
Very-stable-propositional ext = Eq.propositional ext _

-- Very-stable-≡ is propositional (assuming extensionality).

Very-stable-≡-propositional :
  {A : Set a} →
  Extensionality a a →
  Is-proposition (Very-stable-≡ A)
Very-stable-≡-propositional ext =
  implicit-Π-closure ext 1 λ _ →
  implicit-Π-closure ext 1 λ _ →
  Very-stable-propositional ext

-- Very stable types are stable.

Very-stable→Stable : Very-stable A → Stable-[ k ] A
Very-stable→Stable {A = A} {k = k} =
  Very-stable A             ↝⟨ Eq.⟨ _ ,_⟩ ⟩
  A ≃ Erased A              ↝⟨ inverse ⟩
  Erased A ≃ A              ↔⟨⟩
  Stable-[ equivalence ] A  ↝⟨ from-equivalence ⟩□
  Stable-[ k ] A            □

-- The function obtained from Very-stable→Stable (for k = implication)
-- maps [ x ] to x.
--
-- This seems to imply that (say) the booleans can not be proved to be
-- very stable (assuming that Agda is consistent), because
-- implementing a function that resurrects a boolean, given no
-- information about what the boolean was, is impossible. However, the
-- booleans are stable: this follows from Dec→Stable below. Thus it
-- seems as if one can not prove that all stable types are very
-- stable.

Very-stable→Stable-[]≡id :
  (s : Very-stable A) →
  Very-stable→Stable s [ x ] ≡ x
Very-stable→Stable-[]≡id {x = x} s =
  Very-stable→Stable s [ x ]   ≡⟨⟩
  _≃_.from Eq.⟨ _ , s ⟩ [ x ]  ≡⟨ _≃_.left-inverse-of Eq.⟨ _ , s ⟩ x ⟩∎
  x                            ∎

-- Erased A is very stable.

Very-stable-Erased :
  {@0 A : Set a} → Very-stable (Erased A)
Very-stable-Erased =
  _≃_.is-equivalence (Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { from = λ { [ [ x ] ] → [ x ] }
        }
      ; right-inverse-of = refl
      }
    ; left-inverse-of = refl
    }))

-- In an erased context every type is very stable.
--
-- Presumably "not in an erased context" is not expressible
-- internally, so it seems as if it should not be possible to prove
-- that any type is /not/ very stable (in an empty, non-erased
-- context, assuming that Agda is consistent).

Erased-Very-stable :
  {@0 A : Set a} → Erased (Very-stable A)
Erased-Very-stable {A = A} =
  [ _≃_.is-equivalence (    $⟨ Erased↔ ⟩
      Erased (Erased A ↔ A) ↝⟨ erased ⟩
      Erased A ↔ A          ↝⟨ Eq.↔⇒≃ ∘ inverse ⟩□
      A ≃ Erased A          □)
  ]

-- If A is stable, then A is "logical equivalence stable".

Stable→Stable⇔ :
  {@0 A : Set a} → Stable A → Stable-[ logical-equivalence ] A
Stable→Stable⇔ stable = record
  { from = [_]
  ; to   = stable
  }

-- It is not the case that every very stable type is a proposition.

¬-Very-stable→Is-proposition :
  ¬ ({A : Set a} → Very-stable A → Is-proposition A)
¬-Very-stable→Is-proposition {a = a} hyp =
  not-proposition (hyp very-stable)
  where
  very-stable : Very-stable (Erased (↑ a Bool))
  very-stable = Very-stable-Erased

  not-proposition : ¬ Is-proposition (Erased (↑ a Bool))
  not-proposition =
    Is-proposition (Erased (↑ a Bool))  ↝⟨ (λ prop → prop _ _) ⟩
    [ lift true ] ≡ [ lift false ]      ↝⟨ (λ hyp → [ cong (lower ∘ erased) hyp ]) ⟩
    Erased (true ≡ false)               ↝⟨ Erased-cong-→ Bool.true≢false ⟩
    Erased ⊥                            ↔⟨ Erased-⊥↔⊥ ⟩□
    ⊥                                   □

-- Erased A implies ¬ ¬ A.

Erased→¬¬ : {@0 A : Set a} → Erased A → ¬ ¬ A
Erased→¬¬ [ x ] f = _↔_.to Erased-⊥↔⊥ [ f x ]

-- Types that are stable for double negation are stable for Erased.

¬¬-Stable→Stable : {@0 A : Set a} → (¬ ¬ A → A) → Stable A
¬¬-Stable→Stable ¬¬-Stable x = ¬¬-Stable (Erased→¬¬ x)

-- Types for which it is known whether or not they are inhabited are
-- stable.

Dec→Stable : {@0 A : Set a} → Dec A → Stable A
Dec→Stable (yes x) _ = x
Dec→Stable (no ¬x) x with Erased→¬¬ x ¬x
... | ()

------------------------------------------------------------------------
-- A preservation lemma

-- Stable-[ logical-equivalence ] preserves logical equivalences.

Stable-⇔-cong :
  A ⇔ B →
  Stable-[ logical-equivalence ] A ⇔ Stable-[ logical-equivalence ] B
Stable-⇔-cong {A = A} {B = B} A⇔B =
  Stable-[ logical-equivalence ] A  ↔⟨⟩
  Erased A ⇔ A                      ↝⟨ ⇔-cong-⇔ (Erased-cong-⇔ A⇔B) A⇔B ⟩
  Erased B ⇔ B                      ↔⟨⟩
  Stable-[ logical-equivalence ] B  □

------------------------------------------------------------------------
-- Closure properties

-- ⊤ is very stable.

Very-stable-⊤ : Very-stable ⊤
Very-stable-⊤ = _≃_.is-equivalence $ Eq.↔⇒≃ $ inverse Erased-⊤↔⊤

-- ⊥ is very stable.

Very-stable-⊥ : Very-stable (⊥ {ℓ = ℓ})
Very-stable-⊥ = _≃_.is-equivalence $ Eq.↔⇒≃ $ inverse Erased-⊥↔⊥

-- Stable-[ k ] is closed under Π A (possibly assuming
-- extensionality).

Stable-Π :
  {A : Set a} {P : A → Set p} →
  Extensionality? k a p →
  (∀ x → Stable-[ k ] (P x)) → Stable-[ k ] ((x : A) → P x)
Stable-Π {P = P} ext s =
  Erased (∀ x → P x)    ↔⟨ Erased-Π↔Π ⟩
  (∀ x → Erased (P x))  ↝⟨ ∀-cong ext s ⟩□
  (∀ x → P x)           □

-- Very-stable is closed under Π A (assuming extensionality).

Very-stable-Π :
  {A : Set a} {P : A → Set p} →
  Extensionality a p →
  (∀ x → Very-stable (P x)) →
  Very-stable ((x : A) → P x)
Very-stable-Π ext s = _≃_.is-equivalence $
  inverse $ Stable-Π ext $ λ x → inverse Eq.⟨ _ , s x ⟩

-- Stable is closed under Σ A if A is very stable.

Very-stable-Stable-Σ :
  Very-stable A →
  (∀ x → Stable-[ k ] (P x)) →
  Stable-[ k ] (Σ A P)
Very-stable-Stable-Σ {A = A} {P = P} s s′ =
  Erased (Σ A P)                              ↔⟨ Erased-Σ↔Σ ⟩
  Σ (Erased A) (λ x → Erased (P (erased x)))  ↝⟨ Σ-cong-contra Eq.⟨ _ , s ⟩ s′ ⟩□
  Σ A P                                       □

-- If A is stable and something resembling stability holds for P, then
-- Σ A P is stable.

Stable-Σ :
  {@0 A : Set a} {@0 P : A → Set p}
  (s : Stable A) →
  (∀ x → Erased (P (erased x)) → P (s x)) →
  Stable (Σ A P)
Stable-Σ s₁ s₂ [ p ] =
  s₁ [ proj₁ p ] , s₂ [ proj₁ p ] [ proj₂ p ]

-- Very-stable is closed under Σ.

Very-stable-Σ :
  Very-stable A →
  (∀ x → Very-stable (P x)) →
  Very-stable (Σ A P)
Very-stable-Σ {A = A} {P = P} s s′ = _≃_.is-equivalence (
  Σ A P                                       ↝⟨ Σ-cong Eq.⟨ _ , s ⟩ (λ x → Eq.⟨ _ , s′ x ⟩) ⟩
  Σ (Erased A) (λ x → Erased (P (erased x)))  ↔⟨ inverse Erased-Σ↔Σ ⟩□
  Erased (Σ A P)                              □)

-- Stable-[ k ] is closed under _×_.

Stable-× : Stable-[ k ] A → Stable-[ k ] B → Stable-[ k ] (A × B)
Stable-× {A = A} {B = B} s s′ =
  Erased (A × B)       ↔⟨ Erased-Σ↔Σ ⟩
  Erased A × Erased B  ↝⟨ s ×-cong s′ ⟩□
  A × B                □

-- Very-stable is closed under _×_.

Very-stable-× : Very-stable A → Very-stable B → Very-stable (A × B)
Very-stable-× s s′ = _≃_.is-equivalence $
  inverse $ Stable-× (inverse Eq.⟨ _ , s ⟩) (inverse Eq.⟨ _ , s′ ⟩)

-- Stable-[ k ] is closed under ↑ ℓ.

Stable-↑ : Stable-[ k ] A → Stable-[ k ] (↑ ℓ A)
Stable-↑ {A = A} s =
  Erased (↑ _ A)  ↔⟨ Erased-↑↔↑ ⟩
  ↑ _ (Erased A)  ↝⟨ ↑-cong s ⟩□
  ↑ _ A           □

-- Very-stable is closed under ↑ ℓ.

Very-stable-↑ : Very-stable A → Very-stable (↑ ℓ A)
Very-stable-↑ s = _≃_.is-equivalence $
  inverse $ Stable-↑ $ inverse Eq.⟨ _ , s ⟩
