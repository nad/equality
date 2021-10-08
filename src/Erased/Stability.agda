------------------------------------------------------------------------
-- Properties related to stability for Erased
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Erased.Stability
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_)
open import Double-negation eq as DN
open import Embedding eq using (Embedding; Is-embedding)
open import Embedding.Erased eq as EEmb using (Is-embeddingᴱ)
open import Equality.Decidable-UIP eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages eq as ECP
  using (Contractibleᴱ)
import Equivalence.Half-adjoint eq as HA
open import For-iterated-equality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import Injection eq using (_↣_; Injective)
import List eq as L
import Nat eq as Nat
open import Surjection eq using (_↠_; Split-surjective)
open import Univalence-axiom eq

open import Erased.Level-1 eq as Erased hiding (module []-cong)
import Erased.Level-2

private
  variable
    a b c ℓ p : Level
    A B       : Type a
    P         : A → Type p
    k k′ x y  : A
    n         : ℕ

------------------------------------------------------------------------
-- Some lemmas related to stability

-- If A is very stable, then [_]→ {A = A} is an embedding.

Very-stable→Is-embedding-[] :
  Very-stable A → Is-embedding ([_]→ {A = A})
Very-stable→Is-embedding-[] {A = A} s x y =
  _≃_.is-equivalence ≡≃[]≡[]
  where
  A≃Erased-A : A ≃ Erased A
  A≃Erased-A = Eq.⟨ _ , s ⟩

  ≡≃[]≡[] : (x ≡ y) ≃ ([ x ] ≡ [ y ])
  ≡≃[]≡[] = inverse $ Eq.≃-≡ A≃Erased-A

-- If A is very stable, then [_]→ {A = A} is split surjective.

Very-stable→Split-surjective-[] :
  Very-stable A → Split-surjective ([_]→ {A = A})
Very-stable→Split-surjective-[] {A = A} =
  Very-stable A          ↔⟨⟩
  Is-equivalence [_]→    ↝⟨ (λ hyp → _↠_.split-surjective $ _≃_.surjection $ Eq.⟨ _ , hyp ⟩) ⟩
  Split-surjective [_]→  □

-- Very-stable is propositional (assuming extensionality).

Very-stable-propositional :
  {A : Type a} →
  Extensionality a a →
  Is-proposition (Very-stable A)
Very-stable-propositional ext = Eq.propositional ext _

private

  -- The previous result can be generalised.

  For-iterated-equality-Very-stable-propositional :
    {A : Type a} →
    Extensionality a a →
    ∀ n → Is-proposition (For-iterated-equality n Very-stable A)
  For-iterated-equality-Very-stable-propositional ext n =
    H-level-For-iterated-equality ext 1 n
      (Very-stable-propositional ext)

-- Very-stableᴱ is propositional (in erased contexts, assuming
-- extensionality).

@0 Very-stableᴱ-propositional :
  {A : Type a} →
  Extensionality a a →
  Is-proposition (Very-stableᴱ A)
Very-stableᴱ-propositional ext =
  EEq.Is-equivalenceᴱ-propositional ext _

-- Very stable types are stable.

Very-stable→Stable :
  ∀ n →
  For-iterated-equality n Very-stable A →
  For-iterated-equality n Stable-[ k ] A
Very-stable→Stable {k = k} n =
  For-iterated-equality-cong₁ _ n λ {A} →
    Very-stable A             ↝⟨ Eq.⟨ _ ,_⟩ ⟩
    A ≃ Erased A              ↝⟨ inverse ⟩
    Erased A ≃ A              ↔⟨⟩
    Stable-[ equivalence ] A  ↝⟨ from-equivalence ⟩□
    Stable-[ k ] A            □

-- The function obtained from Very-stable→Stable {k = implication} 0
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
  Very-stable→Stable 0 s [ x ] ≡ x
Very-stable→Stable-[]≡id {x = x} s =
  Very-stable→Stable 0 s [ x ]  ≡⟨⟩
  _≃_.from Eq.⟨ _ , s ⟩ [ x ]   ≡⟨ _≃_.left-inverse-of Eq.⟨ _ , s ⟩ x ⟩∎
  x                             ∎

-- Very stable types are very stable with erased proofs.

Very-stable→Very-stableᴱ :
  ∀ n →
  For-iterated-equality n Very-stable A →
  For-iterated-equality n Very-stableᴱ A
Very-stable→Very-stableᴱ n =
  For-iterated-equality-cong₁ _ n EEq.Is-equivalence→Is-equivalenceᴱ

-- In erased contexts types that are very stable with erased proofs
-- are very stable.

@0 Very-stableᴱ→Very-stable :
  ∀ n →
  For-iterated-equality n Very-stableᴱ A →
  For-iterated-equality n Very-stable A
Very-stableᴱ→Very-stable n =
  For-iterated-equality-cong₁ _ n EEq.Is-equivalenceᴱ→Is-equivalence

-- If A is very stable with erased proofs, then
-- Stable-[ equivalenceᴱ ] A holds.

Very-stableᴱ→Stable-≃ᴱ :
  ∀ n →
  For-iterated-equality n Very-stableᴱ A →
  For-iterated-equality n Stable-[ equivalenceᴱ ] A
Very-stableᴱ→Stable-≃ᴱ n =
  For-iterated-equality-cong₁ _ n λ {A} →
    Very-stableᴱ A             ↝⟨ EEq.⟨ _ ,_⟩ ⟩
    A ≃ᴱ Erased A              ↝⟨ inverse ⟩
    Erased A ≃ᴱ A              ↔⟨⟩
    Stable-[ equivalenceᴱ ] A  □

-- If A is very stable with erased proofs, then A is stable.

Very-stableᴱ→Stable :
  ∀ n →
  For-iterated-equality n Very-stableᴱ A →
  For-iterated-equality n Stable A
Very-stableᴱ→Stable {A = A} n =
  For-iterated-equality n Very-stableᴱ A             ↝⟨ Very-stableᴱ→Stable-≃ᴱ n ⟩
  For-iterated-equality n Stable-[ equivalenceᴱ ] A  ↝⟨ For-iterated-equality-cong₁ _ n _≃ᴱ_.to ⟩□
  For-iterated-equality n Stable A                   □

-- The function obtained from Very-stableᴱ→Stable 0 maps [ x ] to x
-- (in erased contexts).

@0 Very-stableᴱ→Stable-[]≡id :
  (s : Very-stableᴱ A) →
  Very-stableᴱ→Stable 0 s [ x ] ≡ x
Very-stableᴱ→Stable-[]≡id {x = x} s =
  Very-stableᴱ→Stable 0 s [ x ]  ≡⟨⟩
  _≃ᴱ_.from EEq.⟨ _ , s ⟩ [ x ]  ≡⟨ _≃ᴱ_.left-inverse-of EEq.⟨ _ , s ⟩ x ⟩∎
  x                              ∎

-- If one can prove that A is very stable given that Erased A is
-- inhabited, then A is very stable.

[Erased→Very-stable]→Very-stable :
  (Erased A → Very-stable A) → Very-stable A
[Erased→Very-stable]→Very-stable =
  HA.[inhabited→Is-equivalence]→Is-equivalence

-- If one can prove that A is very stable (with erased proofs) given
-- that Erased A is inhabited, then A is very stable (with erased
-- proofs).

[Erased→Very-stableᴱ]→Very-stableᴱ :
  (Erased A → Very-stableᴱ A) → Very-stableᴱ A
[Erased→Very-stableᴱ]→Very-stableᴱ =
  EEq.[inhabited→Is-equivalenceᴱ]→Is-equivalenceᴱ

-- Erased A is very stable.

Very-stable-Erased :
  {@0 A : Type a} → Very-stable (Erased A)
Very-stable-Erased =
  _≃_.is-equivalence (Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { from = λ ([ x ]) → [ erased x ]
        }
      ; right-inverse-of = refl
      }
    ; left-inverse-of = λ x → refl [ erased x ]
    }))

-- In an erased context every type is very stable.
--
-- Presumably "not in an erased context" is not expressible
-- internally, so it seems as if it should not be possible to prove
-- that any type is /not/ very stable (in an empty, non-erased
-- context, assuming that Agda is consistent).

Erased-Very-stable :
  {@0 A : Type a} → Erased (Very-stable A)
Erased-Very-stable {A = A} =
  [ _≃_.is-equivalence (    $⟨ Erased↔ ⟩
      Erased (Erased A ↔ A) ↝⟨ erased ⟩
      Erased A ↔ A          ↝⟨ Eq.↔⇒≃ ∘ inverse ⟩□
      A ≃ Erased A          □)
  ]

-- If Very-stable A is very stable, then A is very stable.
--
-- See also Very-stable-Very-stable≃Very-stable below.

Very-stable-Very-stable→Very-stable :
  Very-stable (Very-stable A) →
  Very-stable A
Very-stable-Very-stable→Very-stable s =
  Very-stable→Stable 0 s Erased-Very-stable

-- If Very-stableᴱ A is very stable with erased proofs, then A is very
-- stable with erased proofs.
--
-- See also Very-stableᴱ-Very-stableᴱ≃ᴱVery-stableᴱ below.

Very-stableᴱ-Very-stableᴱ→Very-stableᴱ :
  Very-stableᴱ (Very-stableᴱ A) →
  Very-stableᴱ A
Very-stableᴱ-Very-stableᴱ→Very-stableᴱ {A = A} s =
                           $⟨ Erased-Very-stable ⟩
  Erased (Very-stable A)   ↝⟨ map (Very-stable→Very-stableᴱ 0) ⟩
  Erased (Very-stableᴱ A)  ↝⟨ Very-stableᴱ→Stable 0 s ⟩□
  Very-stableᴱ A           □

-- It is not the case that every very stable type is a proposition.

¬-Very-stable→Is-proposition :
  ¬ ({A : Type a} → Very-stable A → Is-proposition A)
¬-Very-stable→Is-proposition {a = a} hyp =
  not-proposition (hyp very-stable)
  where
  very-stable : Very-stable (Erased (↑ a Bool))
  very-stable = Very-stable-Erased

  not-proposition : ¬ Is-proposition (Erased (↑ a Bool))
  not-proposition =
    Is-proposition (Erased (↑ a Bool))  ↝⟨ (λ prop → prop _ _) ⟩
    [ lift true ] ≡ [ lift false ]      ↝⟨ (λ hyp → [ cong (lower ∘ erased) hyp ]) ⟩
    Erased (true ≡ false)               ↝⟨ map Bool.true≢false ⟩
    Erased ⊥                            ↔⟨ Erased-⊥↔⊥ ⟩□
    ⊥                                   □

-- Erased A implies ¬ ¬ A.

Erased→¬¬ : {@0 A : Type a} → Erased A → ¬ ¬ A
Erased→¬¬ [ x ] f = _↔_.to Erased-⊥↔⊥ [ f x ]

-- Types that are stable for double negation are stable for Erased.

¬¬-Stable→Stable : {@0 A : Type a} → (¬ ¬ A → A) → Stable A
¬¬-Stable→Stable ¬¬-Stable x = ¬¬-Stable (Erased→¬¬ x)

-- Types for which it is known whether or not they are inhabited are
-- stable.

Dec→Stable : {@0 A : Type a} → Dec A → Stable A
Dec→Stable (yes x) _ = x
Dec→Stable (no ¬x) x with () ← Erased→¬¬ x ¬x

-- Every type is stable in the double negation monad.

¬¬-Stable : {@0 A : Type a} → ¬¬ Stable A
¬¬-Stable = DN.map′ Dec→Stable excluded-middle

-- A kind of map function for Stable.

Stable-map :
  {@0 A : Type a} {@0 B : Type b} →
  (A → B) → @0 (B → A) → Stable A → Stable B
Stable-map A→B B→A s x = A→B (s (map B→A x))

-- A variant of Stable-map.

Stable-map-⇔ : A ⇔ B → Stable A → Stable B
Stable-map-⇔ A⇔B =
  Stable-map (_⇔_.to A⇔B) (_⇔_.from A⇔B)

-- If there is an injective function from A to B, and equality is
-- stable for B, then equality is stable for A.

Injective→Stable-≡→Stable-≡ :
  {@0 A : Type a} {@0 B : Type b} →
  (f : A → B) → Injective f → Stable-≡ B → Stable-≡ A
Injective→Stable-≡→Stable-≡ f inj s x y =
  Stable-map inj (cong f) (s (f x) (f y))

-- If equality is stable for A and B, then A ≃ᴱ B implies A ≃ B.

Stable-≡→≃ᴱ→≃ : Stable-≡ A → Stable-≡ B → A ≃ᴱ B → A ≃ B
Stable-≡→≃ᴱ→≃ sA sB A≃ᴱB = Eq.↔→≃
  (_≃ᴱ_.to   A≃ᴱB)
  (_≃ᴱ_.from A≃ᴱB)
  (λ x → sB _ _ [ _≃ᴱ_.right-inverse-of A≃ᴱB x ])
  (λ x → sA _ _ [ _≃ᴱ_.left-inverse-of  A≃ᴱB x ])

------------------------------------------------------------------------
-- Closure properties

-- ⊤ is very stable.

Very-stable-⊤ : Very-stable ⊤
Very-stable-⊤ = _≃_.is-equivalence $ Eq.↔⇒≃ $ inverse Erased-⊤↔⊤

-- ⊥ is very stable.

Very-stable-⊥ : Very-stable (⊥ {ℓ = ℓ})
Very-stable-⊥ = _≃_.is-equivalence $ Eq.↔⇒≃ $ inverse Erased-⊥↔⊥

-- Stable is closed under Π A.

Stable-Π :
  {@0 A : Type a} {@0 P : A → Type p} →
  (∀ x → Stable (P x)) → Stable ((x : A) → P x)
Stable-Π s [ f ] x = s x [ f x ]

-- A variant of Stable-Π.

Stable-[]-Π :
  {A : Type a} {P : A → Type p} →
  Extensionality? k a p →
  (∀ x → Stable-[ k ] (P x)) → Stable-[ k ] ((x : A) → P x)
Stable-[]-Π {P = P} ext s =
  Erased (∀ x → P x)    ↔⟨ Erased-Π↔Π ⟩
  (∀ x → Erased (P x))  ↝⟨ ∀-cong ext s ⟩□
  (∀ x → P x)           □

-- Very-stable is closed under Π A (assuming extensionality).

Very-stable-Π :
  {A : Type a} {P : A → Type p} →
  Extensionality a p →
  (∀ x → Very-stable (P x)) →
  Very-stable ((x : A) → P x)
Very-stable-Π ext s = _≃_.is-equivalence $
  inverse $ Stable-[]-Π ext $ λ x → inverse Eq.⟨ _ , s x ⟩

-- Very-stableᴱ is closed under Π A (assuming extensionality).

Very-stableᴱ-Π :
  {A : Type a} {P : A → Type p} →
  @0 Extensionality a p →
  (∀ x → Very-stableᴱ (P x)) →
  Very-stableᴱ ((x : A) → P x)
Very-stableᴱ-Π {P = P} ext s =
  _≃ᴱ_.is-equivalence
    ((∀ x → P x)           ↝⟨ (EEq.∀-cong-≃ᴱ ext λ x → EEq.⟨ _ , s x ⟩) ⟩
     (∀ x → Erased (P x))  ↔⟨ inverse Erased-Π↔Π ⟩□
     Erased (∀ x → P x)    □)

-- Stable is closed under Σ A if A is very stable.

Very-stable-Stable-Σ :
  Very-stable A →
  (∀ x → Stable-[ k ] (P x)) →
  Stable-[ k ] (Σ A P)
Very-stable-Stable-Σ {A = A} {P = P} s s′ =
  Erased (Σ A P)                              ↔⟨ Erased-Σ↔Σ ⟩
  Σ (Erased A) (λ x → Erased (P (erased x)))  ↝⟨ Σ-cong-contra Eq.⟨ _ , s ⟩ s′ ⟩□
  Σ A P                                       □

-- If A is stable with a stability proof that is a right inverse of
-- [_]→, and P is pointwise stable, then Σ A P is stable.

Stable-Σ :
  (s : Stable A) →
  (∀ x → [ s x ] ≡ x) →
  (∀ x → Stable (P x)) →
  Stable (Σ A P)
Stable-Σ {A = A} {P = P} s₁ hyp s₂ =
  Erased (Σ A P)                              ↔⟨ Erased-Σ↔Σ ⟩
  Σ (Erased A) (λ x → Erased (P (erased x)))  ↝⟨ Σ-cong-contra-→ surj s₂ ⟩□
  Σ A P                                       □
  where
  surj : A ↠ Erased A
  surj = record
    { logical-equivalence = record
      { to   = [_]→
      ; from = s₁
      }
    ; right-inverse-of = hyp
    }

-- Very-stable is closed under Σ.
--
-- See also Very-stableᴱ-Σ below.

Very-stable-Σ :
  Very-stable A →
  (∀ x → Very-stable (P x)) →
  Very-stable (Σ A P)
Very-stable-Σ {A = A} {P = P} s s′ = _≃_.is-equivalence (
  Σ A P                                       ↝⟨ Σ-cong Eq.⟨ _ , s ⟩ (λ x → Eq.⟨ _ , s′ x ⟩) ⟩
  Σ (Erased A) (λ x → Erased (P (erased x)))  ↔⟨ inverse Erased-Σ↔Σ ⟩□
  Erased (Σ A P)                              □)

-- Stable is closed under _×_.

Stable-× :
  {@0 A : Type a} {@0 B : Type b} →
  Stable A → Stable B → Stable (A × B)
Stable-× s s′ [ x , y ] = s [ x ] , s′ [ y ]

-- Stable-[ k ] is closed under _×_.

Stable-[]-× : Stable-[ k ] A → Stable-[ k ] B → Stable-[ k ] (A × B)
Stable-[]-× {A = A} {B = B} s s′ =
  Erased (A × B)       ↔⟨ Erased-Σ↔Σ ⟩
  Erased A × Erased B  ↝⟨ s ×-cong s′ ⟩□
  A × B                □

-- Very-stable is closed under _×_.

Very-stable-× : Very-stable A → Very-stable B → Very-stable (A × B)
Very-stable-× s s′ = _≃_.is-equivalence $
  inverse $ Stable-[]-× (inverse Eq.⟨ _ , s ⟩) (inverse Eq.⟨ _ , s′ ⟩)

-- Very-stableᴱ is closed under _×_.

Very-stableᴱ-× : Very-stableᴱ A → Very-stableᴱ B → Very-stableᴱ (A × B)
Very-stableᴱ-× s s′ = _≃ᴱ_.is-equivalence $
  inverse $ Stable-[]-× (inverse EEq.⟨ _ , s ⟩) (inverse EEq.⟨ _ , s′ ⟩)

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

-- Very-stableᴱ is closed under ↑ ℓ.

Very-stableᴱ-↑ : Very-stableᴱ A → Very-stableᴱ (↑ ℓ A)
Very-stableᴱ-↑ s = _≃ᴱ_.is-equivalence $
  inverse $ Stable-↑ $ inverse EEq.⟨ _ , s ⟩

-- ¬ A is stable.

Stable-¬ :
  {@0 A : Type a} →
  Stable (¬ A)
Stable-¬ =
  Stable-Π λ _ →
  Very-stable→Stable 0 Very-stable-⊥

-- A variant of the previous result.

Stable-[]-¬ :
  {A : Type a} →
  Extensionality? k a lzero →
  Stable-[ k ] (¬ A)
Stable-[]-¬ ext =
  Stable-[]-Π ext λ _ →
  Very-stable→Stable 0 Very-stable-⊥

-- ¬ A is very stable (assuming extensionality).

Very-stable-¬ :
  {A : Type a} →
  Extensionality a lzero →
  Very-stable (¬ A)
Very-stable-¬ {A = A} ext =
  Very-stable-Π ext λ _ →
  Very-stable-⊥

-- ∃ λ (A : Set a) → Very-stable A is stable.
--
-- This result is based on Theorem 3.11 in "Modalities in Homotopy
-- Type Theory" by Rijke, Shulman and Spitters.

Stable-∃-Very-stable : Stable (∃ λ (A : Type a) → Very-stable A)
Stable-∃-Very-stable [ A ] = Erased (proj₁ A) , Very-stable-Erased

-- ∃ λ (A : Set a) → Very-stable A is stable with erased proofs.
--
-- This result is based on Theorem 3.11 in "Modalities in Homotopy
-- Type Theory" by Rijke, Shulman and Spitters.

Stable-∃-Very-stableᴱ : Stable (∃ λ (A : Type a) → Very-stableᴱ A)
Stable-∃-Very-stableᴱ [ A ] =
  Erased (proj₁ A) , Very-stable→Very-stableᴱ 0 Very-stable-Erased

-- If A is "stable 1 + n levels up", then H-level′ (1 + n) A is
-- stable.

Stable-H-level′ :
  ∀ n →
  For-iterated-equality (1 + n) Stable A →
  Stable (H-level′ (1 + n) A)
Stable-H-level′ {A = A} n =
  For-iterated-equality (1 + n) Stable A           ↝⟨ inverse-ext? (λ ext → For-iterated-equality-For-iterated-equality n 1 ext) _ ⟩
  For-iterated-equality n Stable-≡ A               ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
  For-iterated-equality n (Stable ∘ H-level′ 1) A  ↝⟨ For-iterated-equality-commutes-← _ Stable n Stable-Π ⟩
  Stable (For-iterated-equality n (H-level′ 1) A)  ↝⟨ Stable-map-⇔ (For-iterated-equality-For-iterated-equality n 1 _) ⟩□
  Stable (H-level′ (1 + n) A)                      □
  where
  lemma : ∀ {A} → Stable-≡ A → Stable (H-level′ 1 A)
  lemma s =
    Stable-map-⇔
      (H-level↔H-level′ {n = 1} _)
      (Stable-Π λ _ →
       Stable-Π λ _ →
       s _ _)

-- If A is "stable 1 + n levels up", then H-level (1 + n) A is
-- stable.

Stable-H-level :
  ∀ n →
  For-iterated-equality (1 + n) Stable A →
  Stable (H-level (1 + n) A)
Stable-H-level {A = A} n =
  For-iterated-equality (1 + n) Stable A  ↝⟨ Stable-H-level′ n ⟩
  Stable (H-level′ (1 + n) A)             ↝⟨ Stable-map-⇔ (inverse-ext? H-level↔H-level′ _) ⟩□
  Stable (H-level (1 + n) A)              □

-- If equality is stable for A and B, then it is stable for A ⊎ B.

Stable-≡-⊎ :
  ∀ n →
  For-iterated-equality (1 + n) Stable A →
  For-iterated-equality (1 + n) Stable B →
  For-iterated-equality (1 + n) Stable (A ⊎ B)
Stable-≡-⊎ n sA sB =
  For-iterated-equality-⊎-suc
    n
    lemma
    (Very-stable→Stable 0 Very-stable-⊥)
    (For-iterated-equality-↑ _ (1 + n) lemma sA)
    (For-iterated-equality-↑ _ (1 + n) lemma sB)
  where
  lemma : A ↔ B → Stable A → Stable B
  lemma = Stable-map-⇔ ∘ from-isomorphism

private

  -- An alternative, more direct proof of the "base case" of the
  -- previous result.

  Stable-≡-⊎₀ : Stable-≡ A → Stable-≡ B → Stable-≡ (A ⊎ B)
  Stable-≡-⊎₀ sA sB = λ where
    (inj₁ x) (inj₁ y) →
      Erased (inj₁ x ≡ inj₁ y)  ↝⟨ map (_↔_.from Bijection.≡↔inj₁≡inj₁) ⟩
      Erased (x ≡ y)            ↝⟨ sA _ _ ⟩
      x ≡ y                     ↔⟨ Bijection.≡↔inj₁≡inj₁ ⟩□
      inj₁ x ≡ inj₁ y           □

    (inj₁ x) (inj₂ y) →
      Erased (inj₁ x ≡ inj₂ y)  ↝⟨ map (_↔_.to Bijection.≡↔⊎) ⟩
      Erased ⊥                  ↝⟨ Very-stable→Stable 0 Very-stable-⊥ ⟩
      ⊥                         ↔⟨ inverse Bijection.≡↔⊎ ⟩□
      inj₁ x ≡ inj₂ y           □

    (inj₂ x) (inj₁ y) →
      Erased (inj₂ x ≡ inj₁ y)  ↝⟨ map (_↔_.to Bijection.≡↔⊎) ⟩
      Erased ⊥                  ↝⟨ Very-stable→Stable 0 Very-stable-⊥ ⟩
      ⊥                         ↔⟨ inverse Bijection.≡↔⊎ ⟩□
      inj₂ x ≡ inj₁ y           □

    (inj₂ x) (inj₂ y) →
      Erased (inj₂ x ≡ inj₂ y)  ↝⟨ map (_↔_.from Bijection.≡↔inj₂≡inj₂) ⟩
      Erased (x ≡ y)            ↝⟨ sB _ _ ⟩
      x ≡ y                     ↔⟨ Bijection.≡↔inj₂≡inj₂ ⟩□
      inj₂ x ≡ inj₂ y           □

-- If equality is stable for A, then it is stable for List A.

Stable-≡-List :
  ∀ n →
  For-iterated-equality (1 + n) Stable A →
  For-iterated-equality (1 + n) Stable (List A)
Stable-≡-List n =
  For-iterated-equality-List-suc
    n
    (Stable-map-⇔ ∘ from-isomorphism)
    (Very-stable→Stable 0 $ Very-stable-↑ Very-stable-⊤)
    (Very-stable→Stable 0 Very-stable-⊥)
    Stable-[]-×

------------------------------------------------------------------------
-- Some properties related to "Modalities in Homotopy Type Theory"
-- by Rijke, Shulman and Spitters

-- The following two definitions are taken from Shulman's blog post
-- "Universal properties without function extensionality"
-- (https://homotopytypetheory.org/2014/11/02/universal-properties-without-function-extensionality/).

-- Is-[ n ]-extendable-along-[ f ] P means that P is n-extendable
-- along f.

Is-[_]-extendable-along-[_] :
  {A : Type a} {B : Type b} →
  ℕ → (A → B) → (B → Type c) → Type (a ⊔ b ⊔ c)
Is-[ zero  ]-extendable-along-[ f ] P = ↑ _ ⊤
Is-[ suc n ]-extendable-along-[ f ] P =
  ((g : ∀ x → P (f x)) →
     ∃ λ (h : ∀ x → P x) → ∀ x → h (f x) ≡ g x) ×
  ((g h : ∀ x → P x) →
     Is-[ n ]-extendable-along-[ f ] (λ x → g x ≡ h x))

-- Is-∞-extendable-along-[ f ] P means that P is ∞-extendable along f.

Is-∞-extendable-along-[_] :
  {A : Type a} {B : Type b} →
  (A → B) → (B → Type c) → Type (a ⊔ b ⊔ c)
Is-∞-extendable-along-[ f ] P =
  ∀ n → Is-[ n ]-extendable-along-[ f ] P

-- If f is an equivalence, then n-extendability along f is
-- contractible (assuming extensionality).

Is-extendable-along-contractible-for-equivalences :
  {A : Type a} {B : Type b} {f : A → B} {P : B → Type p} →
  Extensionality (a ⊔ b ⊔ p) (a ⊔ b ⊔ p) →
  Is-equivalence f →
  ∀ n → Contractible (Is-[ n ]-extendable-along-[ f ] P)
Is-extendable-along-contractible-for-equivalences _ _ zero =
  ↑-closure 0 ⊤-contractible

Is-extendable-along-contractible-for-equivalences
  {a = a} {b = b} {p = p} {f = f} {P = P} ext eq (suc n) =

  ×-closure 0
    (Π-closure (lower-extensionality b lzero ext) 0 λ g →
                                                             $⟨ singleton-contractible _ ⟩
       Contractible (∃ λ h → h ≡ subst P (inv _) ∘ g ∘ f⁻¹)  ↝⟨ H-level-cong _ 0 (lemma g) ⦂ (_ → _) ⟩□
       Contractible (∃ λ h → ∀ x → h (f x) ≡ g x)            □)
    (Π-closure (lower-extensionality a lzero ext) 0 λ _ →
     Π-closure (lower-extensionality a lzero ext) 0 λ _ →
     Is-extendable-along-contractible-for-equivalences ext eq n)
  where
  f⁻¹ = _≃_.from Eq.⟨ _ , eq ⟩
  inv = _≃_.left-inverse-of (inverse Eq.⟨ _ , eq ⟩)

  lemma : ∀ _ → _ ≃ _
  lemma g =
    (∃ λ h → h ≡ subst P (inv _) ∘ g ∘ f⁻¹)  ↔⟨ (∃-cong λ h → inverse $
                                                 ∘from≡↔≡∘to′ (lower-extensionality p (a ⊔ b) ext) (inverse Eq.⟨ _ , eq ⟩)) ⟩
    (∃ λ h → h ∘ f ≡ g)                      ↝⟨ (∃-cong λ _ → inverse $
                                                 Eq.extensionality-isomorphism (lower-extensionality (b ⊔ p) (a ⊔ b) ext)) ⟩□
    (∃ λ h → ∀ x → h (f x) ≡ g x)            □

-- If f is an equivalence, then ∞-extendability along f is
-- contractible (assuming extensionality).

Is-∞-extendable-along-contractible-for-equivalences :
  {A : Type a} {B : Type b} {f : A → B} {P : B → Type p} →
  Extensionality (a ⊔ b ⊔ p) (a ⊔ b ⊔ p) →
  Is-equivalence f →
  Contractible (Is-∞-extendable-along-[ f ] P)
Is-∞-extendable-along-contractible-for-equivalences ext eq =
  Π-closure (lower-extensionality _ lzero ext) 0 λ n →
  Is-extendable-along-contractible-for-equivalences ext eq n

-- If we assume that equality is extensional for functions, then
-- λ A → Erased A is the modal operator of a Σ-closed reflective
-- subuniverse with [_]→ as the modal unit and Very-stable as the
-- modality predicate:
--
-- * Very-stable is propositional (assuming extensionality), see
--   Very-stable-propositional.
-- * Erased A is very stable, see Very-stable-Erased.
-- * Very-stable is Σ-closed, see Very-stable-Σ.
-- * Finally precomposition with [_]→ is an equivalence for functions
--   with very stable codomains (assuming extensionality):

∘-[]-equivalence :
  {A : Type a} {B : Type b} →
  Extensionality a b →
  Very-stable B →
  Is-equivalence (λ (f : Erased A → B) → f ∘ [_]→)
∘-[]-equivalence ext s =
  _≃_.is-equivalence (Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { from = λ f x → _≃_.from Eq.⟨ _ , s ⟩ (map f x)
        }
      ; right-inverse-of = λ f → apply-ext ext λ x →
          _≃_.left-inverse-of Eq.⟨ _ , s ⟩ (f x)
      }
    ; left-inverse-of = λ f → apply-ext ext λ x →
        _≃_.left-inverse-of Eq.⟨ _ , s ⟩ (f x)
    }))

-- A variant of ∘-[]-equivalence.

Is-equivalenceᴱ-∘[] :
  {A : Type a} {B : Type b} →
  @0 Extensionality a b →
  Very-stableᴱ B →
  Is-equivalenceᴱ (λ (f : Erased A → B) → f ∘ [_]→)
Is-equivalenceᴱ-∘[] ext s =
  _≃ᴱ_.is-equivalence $
  EEq.↔→≃ᴱ
    _
    (λ f x → _≃ᴱ_.from EEq.⟨ _ , s ⟩ (map f x))
    (λ f → apply-ext ext λ x →
       _≃ᴱ_.left-inverse-of EEq.⟨ _ , s ⟩ (f x))
    (λ f → apply-ext ext λ x →
       _≃ᴱ_.left-inverse-of EEq.⟨ _ , s ⟩ (f x))

-- The Coq code accompanying "Modalities in Homotopy Type Theory" uses
-- a somewhat different definition of reflective subuniverses than the
-- paper:
-- * Instead of defining what a reflective subuniverse is it defines
--   what a family of reflective subuniverses is.
-- * The definition has been adapted to Coq's notion of universe
--   polymorphism. (I'm not sure exactly how universe polymorphism
--   works in Coq, so I'm not sure if or how the code differs from the
--   paper in this respect.)
-- * The proof showing that the modality predicate is propositional is
--   allowed to make use of extensionality for functions.
-- * One extra property is assumed: if A and B are equivalent and A is
--   modal, then B is modal. Such a property is proved below, assuming
--   that the []-cong axioms can be instantiated (Very-stable-cong).
-- * The property corresponding to ∘-[]-equivalence is replaced by a
--   property that is intended to avoid uses of extensionality. This
--   property is stated using Is-∞-extendable-along-[_]. Such a
--   property is proved below, assuming that the []-cong axioms can be
--   instantiated (const-extendable).
--
-- Here is a definition of Σ-closed reflective subuniverses that is
-- based on, but not identical to, the definition of reflective
-- subuniverses in the Coq code of Rijke et al. The main changes are
-- perhaps that this definition defines what a single reflective
-- subuniverse is, not a family of them, and that the code uses a
-- single universe level. Below it is proved that λ A → Erased A, [_]→
-- and Very-stable form a Σ-closed reflective subuniverse of this kind
-- (Erased-Σ-closed-reflective-subuniverse).

record Σ-closed-reflective-subuniverse a : Type (lsuc a) where
  field
    ◯        : Type a → Type a
    η        : A → ◯ A
    Is-modal : Type a → Type a

    Is-modal-propositional :
      Extensionality a a →
      Is-proposition (Is-modal A)

    Is-modal-◯ : Is-modal (◯ A)

    Is-modal-respects-≃ : A ≃ B → Is-modal A → Is-modal B

    extendable-along-η :
      Is-modal B → Is-∞-extendable-along-[ η ] (λ (_ : ◯ A) → B)

    Σ-closed : Is-modal A → (∀ x → Is-modal (P x)) → Is-modal (Σ A P)

------------------------------------------------------------------------
-- Some results that follow if "[]-cong" is an equivalence that maps
-- [ refl x ] to refl [ x ]

module []-cong (ax : ∀ {a} → []-cong-axiomatisation a) where

  open Erased.[]-cong ax
  open Erased.Level-2 eq ax

  ----------------------------------------------------------------------
  -- Some lemmas related to stability

  -- If A is stable, with [_]→ as a right inverse of the proof of
  -- stability, then A is very stable.

  Stable→Left-inverse→Very-stable :
    (s : Stable A) → (∀ x → s [ x ] ≡ x) → Very-stable A
  Stable→Left-inverse→Very-stable s inv =
    _≃_.is-equivalence (Eq.↔⇒≃ (record
      { surjection = record
        { logical-equivalence = record
          { from = s
          }
        ; right-inverse-of = λ ([ x ]) → []-cong [ inv x ]
        }
      ; left-inverse-of = inv
      }))

  -- If A is stable, with an erased proof showing that [_]→ is a right
  -- inverse of the proof of stability, then A is very stable with
  -- erased proofs.

  Stable→Left-inverse→Very-stableᴱ :
    (s : Stable A) → @0 (∀ x → s [ x ] ≡ x) → Very-stableᴱ A
  Stable→Left-inverse→Very-stableᴱ s inv =
    _≃ᴱ_.is-equivalence $
    EEq.↔→≃ᴱ
      _
      s
      (λ ([ x ]) → []-cong [ inv x ])
      inv

  private

    -- A lemma used below.

    H-level-suc→For-iterated-equality-Is-proposition :
      H-level (1 + n) A →
      For-iterated-equality n Is-proposition A
    H-level-suc→For-iterated-equality-Is-proposition {n = n} {A = A} =
      H-level (1 + n) A                         ↝⟨ _⇔_.to H-level⇔H-level′ ⟩
      H-level′ (1 + n) A                        ↝⟨ inverse-ext? (For-iterated-equality-For-iterated-equality n 1) _ ⟩
      For-iterated-equality n (H-level′ 1) A    ↝⟨ For-iterated-equality-cong₁ _ n $
                                                   _⇔_.from (H-level⇔H-level′ {n = 1}) ⟩□
      For-iterated-equality n Is-proposition A  □

  -- If A is a stable proposition, then A is very stable.
  --
  -- Note that it is not the case that every very stable type is a
  -- proposition, see ¬-Very-stable→Is-proposition.

  Stable-proposition→Very-stable :
    Stable A → Is-proposition A → Very-stable A
  Stable-proposition→Very-stable s prop =
    _≃_.is-equivalence $
    Eq.⇔→≃
      prop
      (H-level-Erased 1 prop)
      [_]→
      s

  -- The previous result can be generalised.

  Stable→H-level-suc→Very-stable :
    ∀ n →
    For-iterated-equality n Stable A → H-level (1 + n) A →
    For-iterated-equality n Very-stable A
  Stable→H-level-suc→Very-stable {A = A} n = curry (
    For-iterated-equality n Stable A × H-level (1 + n) A           ↝⟨ (∃-cong λ _ → H-level-suc→For-iterated-equality-Is-proposition) ⟩

    For-iterated-equality n Stable A ×
    For-iterated-equality n Is-proposition A                       ↝⟨ For-iterated-equality-commutes-× n _ ⟩

    For-iterated-equality n (λ A → Stable A × Is-proposition A) A  ↝⟨ For-iterated-equality-cong₁ _ n $
                                                                      uncurry Stable-proposition→Very-stable ⟩
    For-iterated-equality n Very-stable A                          □)

  -- If A is stable, and there is an erased proof showing that A is a
  -- proposition, then A is very stable with erased proofs.

  Stable-proposition→Very-stableᴱ :
    Stable A → @0 Is-proposition A → Very-stableᴱ A
  Stable-proposition→Very-stableᴱ s prop =
    _≃ᴱ_.is-equivalence $
    EEq.⇔→≃ᴱ
      prop
      (H-level-Erased 1 prop)
      [_]→
      s

  -- The previous result can be generalised.

  Stable→H-level-suc→Very-stableᴱ :
    ∀ n →
    For-iterated-equality n Stable A →
    @0 H-level (1 + n) A →
    For-iterated-equality n Very-stableᴱ A
  Stable→H-level-suc→Very-stableᴱ {A = A} n s h =                $⟨ s , [ H-level-suc→For-iterated-equality-Is-proposition h ] ⟩
    For-iterated-equality n Stable A ×
    Erased (For-iterated-equality n Is-proposition A)            ↝⟨ (∃-cong λ _ →
                                                                     For-iterated-equality-commutes _ (λ A → Erased A) n (_↔_.to Erased-Π↔Π)) ⟩
    For-iterated-equality n Stable A ×
    For-iterated-equality n (λ A → Erased (Is-proposition A)) A  ↝⟨ For-iterated-equality-commutes-× n _ ⟩

    For-iterated-equality n
      (λ A → Stable A × Erased (Is-proposition A)) A             ↝⟨ (For-iterated-equality-cong₁ _ n λ (s , [ prop ]) →
                                                                     Stable-proposition→Very-stableᴱ s prop) ⟩
    For-iterated-equality n Very-stableᴱ A                       □

  -- If equality is decidable for A, then equality is very stable for
  -- A.

  Decidable-equality→Very-stable-≡ :
    Decidable-equality A → Very-stable-≡ A
  Decidable-equality→Very-stable-≡ dec =
    Stable→H-level-suc→Very-stable
      1
      (λ x y → Dec→Stable (dec x y))
      (decidable⇒set dec)

  -- Types with h-level n are very stable "n levels up".

  H-level→Very-stable :
    ∀ n → H-level n A → For-iterated-equality n Very-stable A
  H-level→Very-stable {A = A} n =
    H-level n A                            ↝⟨ _⇔_.to H-level⇔H-level′ ⟩
    H-level′ n A                           ↝⟨ For-iterated-equality-cong₁ _ n Contractible→Very-stable ⟩□
    For-iterated-equality n Very-stable A  □
    where
    Contractible→Very-stable :
      ∀ {A} → Contractible A → Very-stable A
    Contractible→Very-stable c =
      Stable-proposition→Very-stable
        (λ _ → proj₁ c)
        (mono₁ 0 c)

  -- Types that are contractible with erased proofs (n levels up) are
  -- very stable with erased proofs (n levels up).

  H-level→Very-stableᴱ :
    ∀ n →
    For-iterated-equality n Contractibleᴱ A →
    For-iterated-equality n Very-stableᴱ A
  H-level→Very-stableᴱ {A = A} n =
    For-iterated-equality n Contractibleᴱ A ↝⟨ For-iterated-equality-cong₁ _ n Contractibleᴱ→Very-stableᴱ ⟩□
    For-iterated-equality n Very-stableᴱ A  □
    where
    Contractibleᴱ→Very-stableᴱ :
      ∀ {A} → Contractibleᴱ A → Very-stableᴱ A
    Contractibleᴱ→Very-stableᴱ c =
      Stable-proposition→Very-stableᴱ
        (λ _ → proj₁ c)
        (mono₁ 0 $ ECP.Contractibleᴱ→Contractible c)

  -- Equality is stable for A if and only if [_]→ is injective for A.

  Stable-≡↔Injective-[] :
    {A : Type a} →
    Stable-≡ A ↝[ a ∣ a ] Injective ([_]→ {A = A})
  Stable-≡↔Injective-[] ext =
    (∀ x y → Erased (x ≡ y) → x ≡ y)    ↝⟨ (∀-cong ext λ _ → from-isomorphism $ inverse Bijection.implicit-Π↔Π) ⟩
    (∀ x {y} → Erased (x ≡ y) → x ≡ y)  ↔⟨ inverse Bijection.implicit-Π↔Π ⟩
    (∀ {x y} → Erased (x ≡ y) → x ≡ y)  ↝⟨ (implicit-∀-cong ext $ implicit-∀-cong ext $
                                            Π-cong ext Erased-≡↔[]≡[] λ _ → F.id) ⟩□
    (∀ {x y} → [ x ] ≡ [ y ] → x ≡ y)   □

  -- Equality is very stable for A if and only if [_]→ is an embedding
  -- for A.

  Very-stable-≡↔Is-embedding-[] :
    {A : Type a} →
    Very-stable-≡ A ↝[ a ∣ a ] Is-embedding ([_]→ {A = A})
  Very-stable-≡↔Is-embedding-[] ext =
    (∀ x y → Is-equivalence ([_]→ {A = x ≡ y}))            ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                               Is-equivalence≃Is-equivalence-∘ˡ []-cong-equivalence ext) ⟩
    (∀ x y → Is-equivalence ([]-cong ∘ [_]→ {A = x ≡ y}))  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Is-equivalence-cong ext λ _ → []-cong-[]≡cong-[]) ⟩□
    (∀ x y → Is-equivalence (cong {x = x} {y = y} [_]→))   □

  private

    -- The previous result can be generalised.

    Very-stable-≡↔Is-embedding-[]→ :
      {A : Type a} →
      ∀ n →
      For-iterated-equality (1 + n) Very-stable A ↝[ a ∣ a ]
      For-iterated-equality n (λ A → Is-embedding ([_]→ {A = A})) A
    Very-stable-≡↔Is-embedding-[]→ {A = A} n ext =
      For-iterated-equality (1 + n) Very-stable A                    ↝⟨ inverse-ext? (For-iterated-equality-For-iterated-equality n 1) ext ⟩
      For-iterated-equality n Very-stable-≡ A                        ↝⟨ For-iterated-equality-cong₁ ext n (Very-stable-≡↔Is-embedding-[] ext) ⟩□
      For-iterated-equality n (λ A → Is-embedding ([_]→ {A = A})) A  □

  -- There is a logical equivalence between "equality for A is very
  -- stable with erased proofs" and "[_]→ for A is an embedding with
  -- erased proofs".

  Very-stableᴱ-≡⇔Is-embeddingᴱ-[] :
    Very-stableᴱ-≡ A ⇔ Is-embeddingᴱ ([_]→ {A = A})
  Very-stableᴱ-≡⇔Is-embeddingᴱ-[] =
    (∀ x y → Is-equivalenceᴱ ([_]→ {A = x ≡ y}))            ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                                EEq.Is-equivalence⇔Is-equivalence-∘ˡ
                                                                  (EEq.Is-equivalence→Is-equivalenceᴱ []-cong-equivalence)) ⟩
    (∀ x y → Is-equivalenceᴱ ([]-cong ∘ [_]→ {A = x ≡ y}))  ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                                EEq.Is-equivalenceᴱ-cong-⇔ λ _ →
                                                                []-cong-[]≡cong-[]) ⟩□
    (∀ x y → Is-equivalenceᴱ (cong {x = x} {y = y} [_]→))   □

  -- There is an equivalence with erased proofs between "equality for
  -- A is very stable with erased proofs" and "[_]→ for A is an
  -- embedding with erased proofs" (assuming extensionality).

  Very-stableᴱ-≡≃ᴱIs-embeddingᴱ-[] :
    {A : Type a} →
    @0 Extensionality a a →
    Very-stableᴱ-≡ A ≃ᴱ Is-embeddingᴱ ([_]→ {A = A})
  Very-stableᴱ-≡≃ᴱIs-embeddingᴱ-[] ext =
    EEq.⇔→≃ᴱ
      (H-level-For-iterated-equality ext 1 1 λ {A} →
       Very-stableᴱ-propositional {A = A} ext)
      (EEmb.Is-embeddingᴱ-propositional ext)
      (_⇔_.to Very-stableᴱ-≡⇔Is-embeddingᴱ-[])
      (_⇔_.from Very-stableᴱ-≡⇔Is-embeddingᴱ-[])

  ----------------------------------------------------------------------
  -- Preservation lemmas

  -- A kind of map function for Stable-[_].

  Stable-[]-map :
    A ↝[ k ] B → @0 B ↝[ k ] A → Stable-[ k ] A → Stable-[ k ] B
  Stable-[]-map {A = A} {B = B} A↝B B↝A s =
    Erased B  ↝⟨ Erased-cong B↝A ⟩
    Erased A  ↝⟨ s ⟩
    A         ↝⟨ A↝B ⟩□
    B         □

  -- Variants of Stable-[]-map.

  Stable-[]-map-⇔ : A ⇔ B → Stable A → Stable B
  Stable-[]-map-⇔ A⇔B = Stable-[]-map (_⇔_.to A⇔B) (_⇔_.from A⇔B)

  Stable-[]-map-↔ : A ↔ B → Stable-[ k ] A → Stable-[ k ] B
  Stable-[]-map-↔ A↔B =
    Stable-[]-map
      (from-isomorphism A↔B)
      (from-isomorphism $ inverse A↔B)

  Stable-[]-map-↝ :
    {A : Type a} {B : Type b} →
    A ↝[ a ∣ b ] B →
    Extensionality? k a b → Stable-[ k ] A → Stable-[ k ] B
  Stable-[]-map-↝ A↝B ext =
    Stable-[]-map (A↝B ext) (inverse-ext? A↝B ext)

  -- Stable preserves some kinds of functions (those that are
  -- "symmetric"), possibly assuming extensionality.

  Stable-cong :
    {A : Type a} {B : Type b} →
    Extensionality? ⌊ k ⌋-sym (a ⊔ b) (a ⊔ b) →
    A ↝[ ⌊ k ⌋-sym ] B → Stable A ↝[ ⌊ k ⌋-sym ] Stable B
  Stable-cong {k = k} {A = A} {B = B} ext A↝B =
    Stable A        ↔⟨⟩
    (Erased A → A)  ↝⟨ →-cong ext (Erased-cong A↝B) A↝B ⟩
    (Erased B → B)  ↔⟨⟩
    Stable B        □

  -- Stable-[ equivalence ] preserves equivalences (assuming
  -- extensionality).

  Stable-≃-cong :
    {A : Type a} {B : Type b} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    A ≃ B → Stable-[ equivalence ] A ↝[ k ] Stable-[ equivalence ] B
  Stable-≃-cong {A = A} {B = B} ext A≃B =
    Stable-[ equivalence ] A  ↔⟨⟩
    Erased A ≃ A              ↝⟨ generalise-ext?
                                   (Eq.≃-preserves-⇔ (Erased-cong A≃B) A≃B)
                                   (λ ext → from-isomorphism $ Eq.≃-preserves ext (Erased-cong A≃B) A≃B)
                                   ext ⟩
    Erased B ≃ B              ↔⟨⟩
    Stable-[ equivalence ] B  □

  -- Stable-[ equivalenceᴱ ] preserves equivalences with erased proofs
  -- (assuming extensionality).

  Stable-≃ᴱ-cong :
    {A : Type a} {B : Type b} →
    @0 Extensionality (a ⊔ b) (a ⊔ b) →
    A ≃ᴱ B → Stable-[ equivalenceᴱ ] A ≃ᴱ Stable-[ equivalenceᴱ ] B
  Stable-≃ᴱ-cong {A = A} {B = B} ext A≃B =
    Stable-[ equivalenceᴱ ] A  ↔⟨⟩
    Erased A ≃ᴱ A              ↝⟨ EEq.≃ᴱ-cong ext (Erased-cong A≃B) A≃B ⟩
    Erased B ≃ᴱ B              ↔⟨⟩
    Stable-[ equivalenceᴱ ] B  □

  -- Very-stable preserves equivalences (assuming extensionality).

  Very-stable-cong :
    {A : Type a} {B : Type b} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    A ≃ B → Very-stable A ↝[ k ] Very-stable B
  Very-stable-cong {a = a} {b = b} ext A≃B =
    generalise-ext?-prop
      (record
         { to   = lemma A≃B
         ; from = lemma (inverse A≃B)
         })
      (Very-stable-propositional ∘ lower-extensionality b b)
      (Very-stable-propositional ∘ lower-extensionality a a)
      ext
    where
    lemma : A ≃ B → Very-stable A → Very-stable B
    lemma {A = A} {B = B} A≃B s = _≃_.is-equivalence $
      Eq.with-other-function
        (B         ↝⟨ inverse A≃B ⟩
         A         ↝⟨ Eq.⟨ [_]→ , s ⟩ ⟩
         Erased A  ↝⟨ Erased-cong A≃B ⟩□
         Erased B  □)
        [_]→
        (λ x →
           [ _≃_.to A≃B (_≃_.from A≃B x) ]  ≡⟨ cong [_]→ (_≃_.right-inverse-of A≃B x) ⟩∎
           [ x ]                            ∎)

  -- If there is a function from A to B, with an erased proof showing
  -- that the function is an equivalence, and A is very stable with
  -- erased proofs, then B is very stable with erased proofs.

  →→Is-equivalence→Very-stableᴱ→Very-stableᴱ :
    (f : A → B) → @0 Is-equivalence f → Very-stableᴱ A → Very-stableᴱ B
  →→Is-equivalence→Very-stableᴱ→Very-stableᴱ {A = A} {B = B} f eq s =
    _≃ᴱ_.is-equivalence $
    EEq.↔→≃ᴱ
      [_]→
      (Erased B  ↝⟨ Erased-cong (_≃_.from Eq.⟨ _ , eq ⟩) ⟩
       Erased A  ↝⟨ _≃ᴱ_.from EEq.⟨ _ , s ⟩ ⟩
       A         ↝⟨ f ⟩□
       B         □)
      (λ ([ x ]) → []-cong [ lemma x ])
      lemma
      where
      @0 lemma : _
      lemma = λ x →
         f (_≃ᴱ_.from EEq.⟨ _ , s ⟩ [ _≃_.from Eq.⟨ _ , eq ⟩ x ])  ≡⟨ cong f $ _≃ᴱ_.left-inverse-of EEq.⟨ _ , s ⟩ _ ⟩
         f (_≃_.from Eq.⟨ _ , eq ⟩ x)                              ≡⟨ _≃_.right-inverse-of Eq.⟨ _ , eq ⟩ _ ⟩∎
         x                                                         ∎

  -- If A is equivalent (with erased proofs) to B, and A is very stable
  -- with erased proofs, then B is very stable with erased proofs.

  ≃ᴱ→Very-stableᴱ→Very-stableᴱ :
    A ≃ᴱ B → Very-stableᴱ A → Very-stableᴱ B
  ≃ᴱ→Very-stableᴱ→Very-stableᴱ A≃ᴱB =
    →→Is-equivalence→Very-stableᴱ→Very-stableᴱ
      _ (_≃_.is-equivalence $ EEq.≃ᴱ→≃ A≃ᴱB)

  -- Very-stableᴱ preserves equivalences with erased proofs (assuming
  -- extensionality).

  Very-stableᴱ-cong :
    {A : Type a} {B : Type b} →
    @0 Extensionality (a ⊔ b) (a ⊔ b) →
    A ≃ᴱ B → Very-stableᴱ A ≃ᴱ Very-stableᴱ B
  Very-stableᴱ-cong {a = a} {b = b} ext A≃ᴱB =
    EEq.⇔→≃ᴱ
      (Very-stableᴱ-propositional (lower-extensionality b b ext))
      (Very-stableᴱ-propositional (lower-extensionality a a ext))
      (≃ᴱ→Very-stableᴱ→Very-stableᴱ A≃ᴱB)
      (≃ᴱ→Very-stableᴱ→Very-stableᴱ (inverse A≃ᴱB))

  ----------------------------------------------------------------------
  -- Some lemmas related to Stable, Very-stable or Very-stableᴱ

  -- All kinds of functions between erased types are stable.

  Stable-Erased↝Erased :
    {@0 A : Type a} {@0 B : Type b} →
    Stable (Erased A ↝[ k ] Erased B)
  Stable-Erased↝Erased {k = k} {A = A} {B = B} =
                                       $⟨ Very-stable-Erased ⟩
    Very-stable (Erased (A ↝[ k ] B))  ↝⟨ Very-stable→Stable 0 ⟩
    Stable (Erased (A ↝[ k ] B))       ↝⟨ Stable-[]-map-⇔ (Erased-↝↝↝ _) ⟩□
    Stable (Erased A ↝[ k ] Erased B)  □

  -- All kinds of functions between erased types are very stable (in
  -- some cases assuming extensionality).

  Very-stable-Erased↝Erased :
    {@0 A : Type a} {@0 B : Type b} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    Very-stable (Erased A ↝[ k ] Erased B)
  Very-stable-Erased↝Erased {k = k} {A = A} {B = B} ext =
                                            $⟨ Very-stable-Erased ⟩
    Very-stable (Erased (A ↝[ k ] B))       ↝⟨ Very-stable-cong _ (from-isomorphism $ Erased-↝↔↝ ext) ⦂ (_ → _) ⟩□
    Very-stable (Erased A ↝[ k ] Erased B)  □

  -- Very-stableᴱ is closed under Σ.

  Very-stableᴱ-Σ :
    Very-stableᴱ A →
    (∀ x → Very-stableᴱ (P x)) →
    Very-stableᴱ (Σ A P)
  Very-stableᴱ-Σ {A = A} {P = P} s s′ = _≃ᴱ_.is-equivalence (
    Σ A P                                       ↝⟨ EEq.[]-cong.Σ-cong-≃ᴱ-Erased ax EEq.⟨ _ , s ⟩ (λ x → EEq.⟨ _ , s′ x ⟩) ⟩
    Σ (Erased A) (λ x → Erased (P (erased x)))  ↔⟨ inverse Erased-Σ↔Σ ⟩□
    Erased (Σ A P)                              □)

  -- If A is very stable, then W A P is very stable (assuming
  -- extensionality).

  Very-stable-W :
    {A : Type a} {P : A → Type p} →
    Extensionality p (a ⊔ p) →
    Very-stable A →
    Very-stable (W A P)
  Very-stable-W {A = A} {P = P} ext s =
    _≃_.is-equivalence $
    Eq.↔⇒≃ (record
      { surjection = record
        { logical-equivalence = record
          { to   = [_]→
          ; from = from
          }
        ; right-inverse-of = []∘from
        }
      ; left-inverse-of = from∘[]
      })
    where
    module E = _≃_ Eq.⟨ _ , s ⟩

    from : Erased (W A P) → W A P
    from [ sup x f ] = sup
      (E.from [ x ])
      (λ y → from [ f (subst P (E.left-inverse-of x) y) ])

    from∘[] : ∀ x → from [ x ] ≡ x
    from∘[] (sup x f) = curry (_↠_.to (W-≡,≡↠≡ ext))
      (E.left-inverse-of x)
      (λ y → from∘[] (f (subst P (E.left-inverse-of x) y)))

    []∘from : ∀ x → [ from x ] ≡ x
    []∘from [ x ] = []-cong [ from∘[] x ]

  -- If A is very stable with erased proofs, then W A P is very stable
  -- with erased proofs (assuming extensionality).

  Very-stableᴱ-W :
    {A : Type a} {P : A → Type p} →
    @0 Extensionality p (a ⊔ p) →
    Very-stableᴱ A →
    Very-stableᴱ (W A P)
  Very-stableᴱ-W {A = A} {P = P} ext s =
    _≃ᴱ_.is-equivalence $
    EEq.↔→≃ᴱ [_]→ from []∘from from∘[]
    where
    module E = _≃ᴱ_ EEq.⟨ _ , s ⟩

    from : Erased (W A P) → W A P
    from [ sup x f ] = sup
      (E.from [ x ])
      (λ y → from [ f (subst P (E.left-inverse-of x) y) ])

    @0 from∘[] : ∀ x → from [ x ] ≡ x
    from∘[] (sup x f) = curry (_↠_.to (W-≡,≡↠≡ ext))
      (E.left-inverse-of x)
      (λ y → from∘[] (f (subst P (E.left-inverse-of x) y)))

    []∘from : ∀ x → [ from x ] ≡ x
    []∘from [ x ] = []-cong [ from∘[] x ]

  -- ∃ λ (A : Set a) → Very-stable A is very stable, assuming
  -- extensionality and univalence.
  --
  -- This result is based on Theorem 3.11 in "Modalities in Homotopy
  -- Type Theory" by Rijke, Shulman and Spitters.

  Very-stable-∃-Very-stable :
    Extensionality a a →
    Univalence a →
    Very-stable (∃ λ (A : Type a) → Very-stable A)
  Very-stable-∃-Very-stable ext univ =
    Stable→Left-inverse→Very-stable Stable-∃-Very-stable inv
    where
    inv : ∀ p → Stable-∃-Very-stable [ p ] ≡ p
    inv (A , s) = Σ-≡,≡→≡
      (Erased A  ≡⟨ ≃⇒≡ univ (Very-stable→Stable 0 s) ⟩∎
       A         ∎)
      (Very-stable-propositional ext _ _)

  -- ∃ λ (A : Set a) → Very-stableᴱ A is very stable (with erased
  -- proofs), assuming extensionality and univalence.
  --
  -- This result is based on Theorem 3.11 in "Modalities in Homotopy
  -- Type Theory" by Rijke, Shulman and Spitters.

  Very-stableᴱ-∃-Very-stableᴱ :
    @0 Extensionality a a →
    @0 Univalence a →
    Very-stableᴱ (∃ λ (A : Type a) → Very-stableᴱ A)
  Very-stableᴱ-∃-Very-stableᴱ ext univ =
    Stable→Left-inverse→Very-stableᴱ Stable-∃-Very-stableᴱ inv
    where
    @0 inv : ∀ p → Stable-∃-Very-stableᴱ [ p ] ≡ p
    inv (A , s) = Σ-≡,≡→≡
      (Erased A  ≡⟨ ≃⇒≡ univ (Very-stable→Stable 0 (Very-stableᴱ→Very-stable 0 s)) ⟩∎
       A         ∎)
      (Very-stableᴱ-propositional ext _ _)

  ----------------------------------------------------------------------
  -- Closure properties related to equality

  -- If A is very stable, then equality is very stable for A.

  Very-stable→Very-stable-≡ :
    ∀ n →
    For-iterated-equality n       Very-stable A →
    For-iterated-equality (1 + n) Very-stable A
  Very-stable→Very-stable-≡ {A = A} n =
    For-iterated-equality n Very-stable A        ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
    For-iterated-equality n Very-stable-≡ A      ↝⟨ For-iterated-equality-For-iterated-equality n 1 _ ⟩□
    For-iterated-equality (1 + n) Very-stable A  □
    where
    lemma : ∀ {A} → Very-stable A → Very-stable-≡ A
    lemma {A = A} =
      Very-stable A                ↝⟨ Very-stable→Is-embedding-[] ⟩
      Is-embedding ([_]→ {A = A})  ↝⟨ inverse-ext? Very-stable-≡↔Is-embedding-[] _ ⟩□
      Very-stable-≡ A              □

  private

    -- Some examples showing how Very-stable→Very-stable-≡ can be
    -- used.

    -- Equalities between erased values are very stable.

    Very-stable-≡₀ :
      {@0 A : Type a} →
      Very-stable-≡ (Erased A)
    Very-stable-≡₀ = Very-stable→Very-stable-≡ 0 Very-stable-Erased

    -- Equalities between equalities between erased values are very
    -- stable.

    Very-stable-≡₁ :
      {@0 A : Type a} →
      For-iterated-equality 2 Very-stable (Erased A)
    Very-stable-≡₁ = Very-stable→Very-stable-≡ 1 Very-stable-≡₀

    -- And so on…

  -- A generalisation of Very-stable→Very-stable-≡.

  Very-stable→Very-stable⁺ :
    ∀ m →
    For-iterated-equality n Very-stable A →
    For-iterated-equality (m + n) Very-stable A
  Very-stable→Very-stable⁺         zero    = id
  Very-stable→Very-stable⁺ {n = n} (suc m) =
    Very-stable→Very-stable-≡ (m + n) ∘
    Very-stable→Very-stable⁺ m

  -- A variant of Very-stable→Very-stable-≡.

  Very-stable→Very-stableⁿ :
    ∀ n →
    Very-stable A →
    For-iterated-equality n Very-stable A
  Very-stable→Very-stableⁿ n =
    subst (λ n → For-iterated-equality n Very-stable _)
      (Nat.+-right-identity {n = n}) ∘
      Very-stable→Very-stable⁺ n

  -- A generalisation of Stable-H-level′.

  Stable-[]-H-level′ :
    {A : Type a} →
    Extensionality? k a a →
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    Stable-[ k ] (H-level′ (1 + n) A)
  Stable-[]-H-level′ {a = a} {k = k} {A = A} ext n =
    For-iterated-equality (1 + n) Stable-[ k ] A           ↝⟨ inverse-ext? (For-iterated-equality-For-iterated-equality n 1) _ ⟩
    For-iterated-equality n Stable-≡-[ k ] A               ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
    For-iterated-equality n (Stable-[ k ] ∘ H-level′ 1) A  ↝⟨ For-iterated-equality-commutes-← _ Stable-[ k ] n (Stable-[]-Π ext) ⟩
    Stable-[ k ] (For-iterated-equality n (H-level′ 1) A)  ↝⟨ Stable-[]-map-↝ (For-iterated-equality-For-iterated-equality n 1) ext ⟩□
    Stable-[ k ] (H-level′ (1 + n) A)                      □
    where
    lemma : ∀ {A} → Stable-≡-[ k ] A → Stable-[ k ] (H-level′ 1 A)
    lemma s =
      Stable-[]-map-↝
        (H-level↔H-level′ {n = 1})
        ext
        (Stable-[]-Π ext λ _ →
         Stable-[]-Π ext λ _ →
         s _ _)

  -- A generalisation of Stable-H-level.

  Stable-[]-H-level :
    {A : Type a} →
    Extensionality? k a a →
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    Stable-[ k ] (H-level (1 + n) A)
  Stable-[]-H-level {k = k} {A = A} ext n =
    For-iterated-equality (1 + n) Stable-[ k ] A  ↝⟨ Stable-[]-H-level′ ext n ⟩
    Stable-[ k ] (H-level′ (1 + n) A)             ↝⟨ Stable-[]-map-↝ (inverse-ext? H-level↔H-level′) ext ⟩□
    Stable-[ k ] (H-level (1 + n) A)              □

  -- If A is "very stable n levels up", then H-level′ n A is very
  -- stable (assuming extensionality).

  Very-stable-H-level′ :
    {A : Type a} →
    Extensionality a a →
    ∀ n →
    For-iterated-equality n Very-stable A →
    Very-stable (H-level′ n A)
  Very-stable-H-level′ {A = A} ext n =
    For-iterated-equality n Very-stable A                   ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
    For-iterated-equality n (Very-stable ∘ Contractible) A  ↝⟨ For-iterated-equality-commutes-← _ Very-stable n (Very-stable-Π ext) ⟩□
    Very-stable (H-level′ n A)                              □
    where
    lemma : ∀ {A} → Very-stable A → Very-stable (Contractible A)
    lemma s =
      Very-stable-Σ s λ _ →
      Very-stable-Π ext λ _ →
      Very-stable→Very-stable-≡ 0 s _ _

  -- If A is "very stable with erased proofs n levels up", then
  -- For-iterated-equality n Contractibleᴱ A is very stable with
  -- erased proofs (assuming extensionality).

  Very-stableᴱ-H-levelᴱ :
    {A : Type a} →
    @0 Extensionality a a →
    ∀ n →
    For-iterated-equality n Very-stableᴱ A →
    Very-stableᴱ (For-iterated-equality n Contractibleᴱ A)
  Very-stableᴱ-H-levelᴱ {A = A} ext n =
    For-iterated-equality n Very-stableᴱ A                    ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
    For-iterated-equality n (Very-stableᴱ ∘ Contractibleᴱ) A  ↝⟨ For-iterated-equality-commutes-← _ Very-stableᴱ n (Very-stableᴱ-Π ext) ⟩□
    Very-stableᴱ (For-iterated-equality n Contractibleᴱ A)    □
    where
    lemma : ∀ {A} → Very-stableᴱ A → Very-stableᴱ (Contractibleᴱ A)
    lemma s =
      Very-stableᴱ-Σ s λ _ →
      Very-stable→Very-stableᴱ 0
      Very-stable-Erased

  -- If A is "very stable n levels up", then H-level n A is very
  -- stable (assuming extensionality).

  Very-stable-H-level :
    {A : Type a} →
    Extensionality a a →
    ∀ n →
    For-iterated-equality n Very-stable A →
    Very-stable (H-level n A)
  Very-stable-H-level {A = A} ext n =
    For-iterated-equality n Very-stable A  ↝⟨ Very-stable-H-level′ ext n ⟩
    Very-stable (H-level′ n A)             ↝⟨ Very-stable-cong _ (inverse $ H-level↔H-level′ ext) ⟩□
    Very-stable (H-level n A)              □

  -- There is an equivalence between Very-stable (Very-stable A) and
  -- Very-stable A (assuming extensionality).

  Very-stable-Very-stable≃Very-stable :
    {A : Type a} →
    Extensionality a a →
    Very-stable (Very-stable A) ≃ Very-stable A
  Very-stable-Very-stable≃Very-stable ext =
    _↠_.from (Eq.≃↠⇔ (Very-stable-propositional ext)
                     (Very-stable-propositional ext))
      (record
         { to   = Very-stable-Very-stable→Very-stable
         ; from = λ s →
             Very-stable-cong _
               (inverse $ Is-equivalence≃Is-equivalence-CP ext) $
             Very-stable-Π ext λ _ →
             Very-stable-H-level ext 0 $
             Very-stable-Σ s (λ _ → Very-stable-≡₀ _ _)
         })

  -- There is an equivalence with erased proofs between
  -- Very-stableᴱ (Very-stableᴱ A) and Very-stableᴱ A (assuming
  -- extensionality).

  Very-stableᴱ-Very-stableᴱ≃ᴱVery-stableᴱ :
    {A : Type a} →
    @0 Extensionality a a →
    Very-stableᴱ (Very-stableᴱ A) ≃ᴱ Very-stableᴱ A
  Very-stableᴱ-Very-stableᴱ≃ᴱVery-stableᴱ ext =
    EEq.⇔→≃ᴱ
      (Very-stableᴱ-propositional ext)
      (Very-stableᴱ-propositional ext)
      Very-stableᴱ-Very-stableᴱ→Very-stableᴱ
      (λ s →
         ≃ᴱ→Very-stableᴱ→Very-stableᴱ
           (inverse $ EEq.Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext) $
         Very-stableᴱ-Π ext λ _ →
         Very-stableᴱ-H-levelᴱ ext 0 $
         Very-stableᴱ-Σ s λ _ →
         Very-stable→Very-stableᴱ 0 $
         Very-stable-Erased)

  -- A generalisation of Stable-≡-⊎.

  Stable-[]-≡-⊎ :
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    For-iterated-equality (1 + n) Stable-[ k ] B →
    For-iterated-equality (1 + n) Stable-[ k ] (A ⊎ B)
  Stable-[]-≡-⊎ n sA sB =
    For-iterated-equality-⊎-suc
      n
      Stable-[]-map-↔
      (Very-stable→Stable 0 Very-stable-⊥)
      (For-iterated-equality-↑ _ (1 + n) Stable-[]-map-↔ sA)
      (For-iterated-equality-↑ _ (1 + n) Stable-[]-map-↔ sB)

  -- If equality is very stable for A and B, then it is very stable
  -- for A ⊎ B.

  Very-stable-≡-⊎ :
    ∀ n →
    For-iterated-equality (1 + n) Very-stable A →
    For-iterated-equality (1 + n) Very-stable B →
    For-iterated-equality (1 + n) Very-stable (A ⊎ B)
  Very-stable-≡-⊎ n sA sB =
    For-iterated-equality-⊎-suc
      n
      lemma
      Very-stable-⊥
      (For-iterated-equality-↑ _ (1 + n) lemma sA)
      (For-iterated-equality-↑ _ (1 + n) lemma sB)
    where
    lemma : A ↔ B → Very-stable A → Very-stable B
    lemma = Very-stable-cong _ ∘ from-isomorphism

  -- If equality is very stable (with erased proofs) for A and B, then
  -- it is very stable (with erased proofs) for A ⊎ B.

  Very-stableᴱ-≡-⊎ :
    ∀ n →
    For-iterated-equality (1 + n) Very-stableᴱ A →
    For-iterated-equality (1 + n) Very-stableᴱ B →
    For-iterated-equality (1 + n) Very-stableᴱ (A ⊎ B)
  Very-stableᴱ-≡-⊎ n sA sB =
    For-iterated-equality-⊎-suc
      n
      lemma
      (Very-stable→Very-stableᴱ 0 Very-stable-⊥)
      (For-iterated-equality-↑ _ (1 + n) lemma sA)
      (For-iterated-equality-↑ _ (1 + n) lemma sB)
    where
    lemma : A ↔ B → Very-stableᴱ A → Very-stableᴱ B
    lemma = ≃ᴱ→Very-stableᴱ→Very-stableᴱ ∘ from-isomorphism

  -- A generalisation of Stable-≡-List.

  Stable-[]-≡-List :
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    For-iterated-equality (1 + n) Stable-[ k ] (List A)
  Stable-[]-≡-List n =
    For-iterated-equality-List-suc
      n
      Stable-[]-map-↔
      (Very-stable→Stable 0 $ Very-stable-↑ Very-stable-⊤)
      (Very-stable→Stable 0 Very-stable-⊥)
      Stable-[]-×

  -- If equality is very stable for A, then it is very stable for
  -- List A.

  Very-stable-≡-List :
    ∀ n →
    For-iterated-equality (1 + n) Very-stable A →
    For-iterated-equality (1 + n) Very-stable (List A)
  Very-stable-≡-List n =
    For-iterated-equality-List-suc
      n
      (Very-stable-cong _ ∘ from-isomorphism)
      (Very-stable-↑ Very-stable-⊤)
      Very-stable-⊥
      Very-stable-×

  -- If equality is very stable (with erased proofs) for A, then it is
  -- very stable (with erased proofs) for List A.

  Very-stableᴱ-≡-List :
    ∀ n →
    For-iterated-equality (1 + n) Very-stableᴱ A →
    For-iterated-equality (1 + n) Very-stableᴱ (List A)
  Very-stableᴱ-≡-List n =
    For-iterated-equality-List-suc
      n
      (≃ᴱ→Very-stableᴱ→Very-stableᴱ ∘ from-isomorphism)
      (Very-stable→Very-stableᴱ 0 $
       Very-stable-↑ Very-stable-⊤)
      (Very-stable→Very-stableᴱ 0 Very-stable-⊥)
      Very-stableᴱ-×

  -- A generalisation of Very-stable-Σ.
  --
  -- Based on a lemma called inO_unsigma, implemented by Mike Shulman
  -- in the file ReflectiveSubuniverse.v in the Coq HoTT library.

  Very-stable-Σ↔Π :
    {A : Type a} {P : A → Type p} →
    Very-stable A →
    Very-stable (Σ A P) ↝[ a ⊔ p ∣ a ⊔ p ] (∀ x → Very-stable (P x))
  Very-stable-Σ↔Π {a = a} {p = p} {A = A} {P = P} s =
    generalise-ext?-prop
      (record
         { from = Very-stable-Σ s
         ; to   = flip λ x →
             Very-stable (Σ A P)                          ↝⟨ flip Very-stable-Σ (λ _ → Very-stable→Very-stable-≡ 0 s _ _) ⟩
             Very-stable (∃ λ ((y , _) : Σ A P) → y ≡ x)  ↝⟨ Very-stable-cong _ $ from-bijection $ inverse Σ-assoc ⟩
             Very-stable (∃ λ (y : A) → P y × y ≡ x)      ↝⟨ Very-stable-cong _ $ from-bijection $ inverse $ ∃-intro _ _ ⟩□
             Very-stable (P x)                            □
         })
      Very-stable-propositional
      (λ ext →
         Π-closure (lower-extensionality p a ext) 1 λ _ →
         Very-stable-propositional (lower-extensionality a a ext))

  -- A variant of Very-stableᴱ-Σ.
  --
  -- Based on a lemma called inO_unsigma, implemented by Mike Shulman
  -- in the file ReflectiveSubuniverse.v in the Coq HoTT library.

  Very-stableᴱ-Σ≃ᴱΠ :
    {A : Type a} {P : A → Type p} →
    @0 Extensionality (a ⊔ p) (a ⊔ p) →
    Very-stableᴱ A →
    Very-stableᴱ-≡ A →
    Very-stableᴱ (Σ A P) ≃ᴱ (∀ x → Very-stableᴱ (P x))
  Very-stableᴱ-Σ≃ᴱΠ {a = a} {p = p} {A = A} {P = P} ext s s-≡ =
    EEq.⇔→≃ᴱ
      (Very-stableᴱ-propositional ext)
      (Π-closure (lower-extensionality p a ext) 1 λ _ →
       Very-stableᴱ-propositional (lower-extensionality a a ext))
      (flip λ x →
       Very-stableᴱ (Σ A P)                          ↝⟨ flip Very-stableᴱ-Σ (λ _ → s-≡ _ _) ⟩
       Very-stableᴱ (∃ λ ((y , _) : Σ A P) → y ≡ x)  ↝⟨ ≃ᴱ→Very-stableᴱ→Very-stableᴱ $ from-bijection $ inverse Σ-assoc ⟩
       Very-stableᴱ (∃ λ (y : A) → P y × y ≡ x)      ↝⟨ ≃ᴱ→Very-stableᴱ→Very-stableᴱ $ from-bijection $ inverse $ ∃-intro _ _ ⟩□
       Very-stableᴱ (P x)                            □)
      (Very-stableᴱ-Σ s)

  ----------------------------------------------------------------------
  -- Simple corollaries or variants of results above

  -- A generalisation of Very-stable-cong.

  Very-stable-congⁿ :
    {A : Type a} {B : Type b} →
    Extensionality? k′ (a ⊔ b) (a ⊔ b) →
    ∀ n →
    A ↔[ k ] B →
    For-iterated-equality n Very-stable A ↝[ k′ ]
    For-iterated-equality n Very-stable B
  Very-stable-congⁿ ext n A↔B =
    For-iterated-equality-cong
      ext
      n
      (Very-stable-cong ext ∘ from-isomorphism)
      (from-isomorphism A↔B)

  -- A variant of Very-stableᴱ-cong.

  Very-stableᴱ-congⁿ :
    {A : Type a} {B : Type b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    ∀ n →
    A ↔[ k ] B →
    For-iterated-equality n Very-stableᴱ A ≃ᴱ
    For-iterated-equality n Very-stableᴱ B
  Very-stableᴱ-congⁿ ext n A↔B =
    For-iterated-equality-cong
      ext
      n
      (Very-stableᴱ-cong ext ∘ from-isomorphism)
      (from-isomorphism A↔B)

  -- A generalisation of Stable-Π.

  Stable-Πⁿ :
    {A : Type a} {P : A → Type p} →
    Extensionality a p →
    ∀ n →
    (∀ x → For-iterated-equality n Stable-[ k ] (P x)) →
    For-iterated-equality n Stable-[ k ] ((x : A) → P x)
  Stable-Πⁿ {k = k} ext n =
    For-iterated-equality-Π
      ext
      n
      Stable-[]-map-↔
      (Stable-[]-Π (forget-ext? k ext))

  -- A generalisation of Very-stable-Π.

  Very-stable-Πⁿ :
    {A : Type a} {P : A → Type p} →
    Extensionality a p →
    ∀ n →
    (∀ x → For-iterated-equality n Very-stable (P x)) →
    For-iterated-equality n Very-stable ((x : A) → P x)
  Very-stable-Πⁿ ext n =
    For-iterated-equality-Π
      ext
      n
      (Very-stable-cong _ ∘ from-isomorphism)
      (Very-stable-Π ext)

  -- A variant of Very-stableᴱ-Π.

  Very-stableᴱ-Πⁿ :
    {A : Type a} {P : A → Type p} →
    Extensionality a p →
    ∀ n →
    (∀ x → For-iterated-equality n Very-stableᴱ (P x)) →
    For-iterated-equality n Very-stableᴱ ((x : A) → P x)
  Very-stableᴱ-Πⁿ ext n =
    For-iterated-equality-Π
      ext
      n
      (≃ᴱ→Very-stableᴱ→Very-stableᴱ ∘ from-isomorphism)
      (Very-stableᴱ-Π ext)

  -- A generalisation of Very-stable-Stable-Σ.

  Very-stable-Stable-Σⁿ :
    ∀ n →
    For-iterated-equality n Very-stable A →
    (∀ x → For-iterated-equality n Stable-[ k ] (P x)) →
    For-iterated-equality n Stable-[ k ] (Σ A P)
  Very-stable-Stable-Σⁿ {k = k} n =
    For-iterated-equality-Σ
      n
      Stable-[]-map-↔
      Very-stable-Stable-Σ

  -- A variant of Stable-Σ for equality.

  Stable-≡-Σ :
    {p q : Σ A P} →
    (s : Stable (proj₁ p ≡ proj₁ q)) →
    (∀ eq → [ s eq ] ≡ eq) →
    (∀ eq → Stable (subst P eq (proj₂ p) ≡ proj₂ q)) →
    Stable (p ≡ q)
  Stable-≡-Σ {P = P} {p = p} {q = q} s₁ hyp s₂ =  $⟨ Stable-Σ s₁ hyp s₂ ⟩

    Stable (∃ λ (eq : proj₁ p ≡ proj₁ q) →
                subst P eq (proj₂ p) ≡ proj₂ q)   ↝⟨ Stable-[]-map-↔ Bijection.Σ-≡,≡↔≡ ⟩□

    Stable (p ≡ q)                                □

  -- A generalisation of Very-stable-Σ.

  Very-stable-Σⁿ :
    ∀ n →
    For-iterated-equality n Very-stable A →
    (∀ x → For-iterated-equality n Very-stable (P x)) →
    For-iterated-equality n Very-stable (Σ A P)
  Very-stable-Σⁿ n =
    For-iterated-equality-Σ
      n
      (Very-stable-cong _ ∘ from-isomorphism)
      Very-stable-Σ

  -- A generalisation of Very-stableᴱ-Σ.

  Very-stableᴱ-Σⁿ :
    ∀ n →
    For-iterated-equality n Very-stableᴱ A →
    (∀ x → For-iterated-equality n Very-stableᴱ (P x)) →
    For-iterated-equality n Very-stableᴱ (Σ A P)
  Very-stableᴱ-Σⁿ n =
    For-iterated-equality-Σ
      n
      (≃ᴱ→Very-stableᴱ→Very-stableᴱ ∘ from-isomorphism)
      Very-stableᴱ-Σ

  -- A generalisation of Stable-[]-×.

  Stable-[]-×ⁿ :
    ∀ n →
    For-iterated-equality n Stable-[ k ] A →
    For-iterated-equality n Stable-[ k ] B →
    For-iterated-equality n Stable-[ k ] (A × B)
  Stable-[]-×ⁿ n =
    For-iterated-equality-×
      n
      Stable-[]-map-↔
      Stable-[]-×

  -- A generalisation of Very-stable-×.

  Very-stable-×ⁿ :
    ∀ n →
    For-iterated-equality n Very-stable A →
    For-iterated-equality n Very-stable B →
    For-iterated-equality n Very-stable (A × B)
  Very-stable-×ⁿ n =
    For-iterated-equality-×
      n
      (Very-stable-cong _ ∘ from-isomorphism)
      Very-stable-×

  -- A generalisation of Very-stableᴱ-×.

  Very-stableᴱ-×ⁿ :
    ∀ n →
    For-iterated-equality n Very-stableᴱ A →
    For-iterated-equality n Very-stableᴱ B →
    For-iterated-equality n Very-stableᴱ (A × B)
  Very-stableᴱ-×ⁿ n =
    For-iterated-equality-×
      n
      (≃ᴱ→Very-stableᴱ→Very-stableᴱ ∘ from-isomorphism)
      Very-stableᴱ-×

  -- A generalisation of Stable-↑.

  Stable-↑ⁿ :
    ∀ n →
    For-iterated-equality n Stable-[ k ] A →
    For-iterated-equality n Stable-[ k ] (↑ ℓ A)
  Stable-↑ⁿ n =
    For-iterated-equality-↑ _ n Stable-[]-map-↔

  -- A generalisation of Very-stable-↑.

  Very-stable-↑ⁿ :
    ∀ n →
    For-iterated-equality n Very-stable A →
    For-iterated-equality n Very-stable (↑ ℓ A)
  Very-stable-↑ⁿ n =
    For-iterated-equality-↑
      _
      n
      (Very-stable-cong _ ∘ from-isomorphism)

  -- A generalisation of Very-stableᴱ-↑.

  Very-stableᴱ-↑ⁿ :
    ∀ n →
    For-iterated-equality n Very-stableᴱ A →
    For-iterated-equality n Very-stableᴱ (↑ ℓ A)
  Very-stableᴱ-↑ⁿ n =
    For-iterated-equality-↑
      _
      n
      (≃ᴱ→Very-stableᴱ→Very-stableᴱ ∘ from-isomorphism)

  -- A generalisation of Very-stable-W.

  Very-stable-Wⁿ :
    {A : Type a} {P : A → Type p} →
    Extensionality p (a ⊔ p) →
    ∀ n →
    For-iterated-equality n Very-stable A →
    For-iterated-equality n Very-stable (W A P)
  Very-stable-Wⁿ {A = A} {P = P} ext n =
    For-iterated-equality-W
      ext
      n
      (Very-stable-cong _ ∘ from-isomorphism)
      (Very-stable-Π ext)
      Very-stable-Σ
      (Very-stable-W ext)

  -- A generalisation of Very-stableᴱ-W.

  Very-stableᴱ-Wⁿ :
    {A : Type a} {P : A → Type p} →
    Extensionality p (a ⊔ p) →
    ∀ n →
    For-iterated-equality n Very-stableᴱ A →
    For-iterated-equality n Very-stableᴱ (W A P)
  Very-stableᴱ-Wⁿ {A = A} {P = P} ext n =
    For-iterated-equality-W
      ext
      n
      (≃ᴱ→Very-stableᴱ→Very-stableᴱ ∘ from-isomorphism)
      (Very-stableᴱ-Π ext)
      Very-stableᴱ-Σ
      (Very-stableᴱ-W ext)

  ----------------------------------------------------------------------
  -- The function λ A → Erased A, [_]→ and Very-stable form a Σ-closed
  -- reflective subuniverse

  -- As a consequence of Very-stable→Very-stable-≡ we get that every
  -- family of very stable types, indexed by Erased A, is ∞-extendable
  -- along [_]→.

  extendable :
    {@0 A : Type a} {P : Erased A → Type b} →
    (∀ x → Very-stable (P x)) →
    Is-∞-extendable-along-[ [_]→ ] P
  extendable s zero    = _
  extendable s (suc n) =
      (λ f →
           (λ x → _≃_.from Eq.⟨ _ , s x ⟩ (map f x))
         , λ x →
             _≃_.from Eq.⟨ _ , s [ x ] ⟩ (map f [ x ])  ≡⟨⟩
             _≃_.from Eq.⟨ _ , s [ x ] ⟩ [ f x ]        ≡⟨ _≃_.left-inverse-of Eq.⟨ _ , s [ x ] ⟩ _ ⟩∎
             f x                                        ∎)
    , λ g h →
        extendable (λ x → Very-stable→Very-stable-≡ 0 (s x) _ _) n

  -- As a special case we get the following property, which is based
  -- on one part of the definition of a reflective subuniverse used in
  -- the Coq code accompanying "Modalities in Homotopy Type Theory" by
  -- Rijke, Shulman and Spitters.

  const-extendable :
    {@0 A : Type a} {B : Type b} →
    Very-stable B →
    Is-∞-extendable-along-[ [_]→ ] (λ (_ : Erased A) → B)
  const-extendable s = extendable (λ _ → s)

  -- The function λ A → Erased A, [_]→ and Very-stable form a Σ-closed
  -- reflective subuniverse.

  Erased-Σ-closed-reflective-subuniverse :
    Σ-closed-reflective-subuniverse a
  Erased-Σ-closed-reflective-subuniverse = λ where
      .◯                      → λ A → Erased A
      .η                      → [_]→
      .Is-modal               → Very-stable
      .Is-modal-propositional → Very-stable-propositional
      .Is-modal-◯             → Very-stable-Erased
      .Is-modal-respects-≃    → Very-stable-cong _
      .extendable-along-η     → const-extendable
      .Σ-closed               → Very-stable-Σ
    where
    open Σ-closed-reflective-subuniverse

  ----------------------------------------------------------------------
  -- Rearrangement lemmas for []-cong, proved using stability

  -- []-cong kind of commutes with trans.

  []-cong-trans :
    {@0 A : Type a} {@0 x y z : A} {@0 p : x ≡ y} {@0 q : y ≡ z} →
    []-cong [ trans p q ] ≡ trans ([]-cong [ p ]) ([]-cong [ q ])
  []-cong-trans =
    Very-stable→Stable 0 (Very-stable-≡₁ _ _ _ _)
      [ elim¹
          (λ p → ∀ (@0 q) → []-cong [ trans p q ] ≡
                            trans ([]-cong [ p ]) ([]-cong [ q ]))
          (λ q →
             []-cong [ trans (refl _) q ]                ≡⟨ cong []-cong ([]-cong [ trans-reflˡ _ ]) ⟩
             []-cong [ q ]                               ≡⟨ sym $ trans-reflˡ _ ⟩
             trans (refl _) ([]-cong [ q ])              ≡⟨ sym $ cong (flip trans _) []-cong-[refl] ⟩∎
             trans ([]-cong [ refl _ ]) ([]-cong [ q ])  ∎)
          _
          _
      ]

  -- []-cong kind of commutes with cong.

  []-cong-cong :
    {@0 A : Type a} {@0 B : Type b}
    {@0 f : A → B} {@0 x y : A} {@0 p : x ≡ y} →
    []-cong [ cong f p ] ≡ cong (map f) ([]-cong [ p ])
  []-cong-cong {f = f} =
    Very-stable→Stable 0 (Very-stable-≡₁ _ _ _ _)
      [ elim¹
          (λ p → []-cong [ cong f p ] ≡ cong (map f) ([]-cong [ p ]))
          ([]-cong [ cong f (refl _) ]        ≡⟨ cong []-cong ([]-cong [ cong-refl _ ]) ⟩
           []-cong [ refl _ ]                 ≡⟨ []-cong-[refl] ⟩
           refl _                             ≡⟨ sym $ cong-refl _ ⟩
           cong (map f) (refl _)              ≡⟨ sym $ cong (cong (map f)) []-cong-[refl] ⟩∎
           cong (map f) ([]-cong [ refl _ ])  ∎)
          _
      ]

  ----------------------------------------------------------------------
  -- Erased (or rather λ A → Erased A) is functorial for all kinds of
  -- functions (in some cases assuming extensionality)

  private

    -- Erased is functorial for equivalences (assuming
    -- extensionality).

    Erased-cong-≃-id :
      {@0 A : Type a} →
      Extensionality a a →
      Erased-cong {k = equivalence} F.id ≡ F.id {A = Erased A}
    Erased-cong-≃-id ext = Eq.lift-equality ext (refl _)

    Erased-cong-≃-∘ :
      {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} →
      Extensionality (a ⊔ c) (a ⊔ c) →
      (@0 f : B ≃ C) (@0 g : A ≃ B) →
      Erased-cong {k = equivalence} (f F.∘ g) ≡
      Erased-cong f F.∘ Erased-cong g
    Erased-cong-≃-∘ ext _ _ = Eq.lift-equality ext (refl _)

    -- Erased is functorial for equivalences with erased proofs
    -- (assuming extensionality).

    Erased-cong-≃ᴱ-id :
      {@0 A : Type a} →
      Extensionality a a →
      Erased-cong {k = equivalenceᴱ} F.id ≡ F.id {A = Erased A}
    Erased-cong-≃ᴱ-id ext =
      EEq.[]-cong.to≡to→≡-Erased ax ext (refl _)

    Erased-cong-≃ᴱ-∘ :
      {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} →
      Extensionality (a ⊔ c) (a ⊔ c) →
      (@0 f : B ≃ᴱ C) (@0 g : A ≃ᴱ B) →
      Erased-cong {k = equivalenceᴱ} (f F.∘ g) ≡
      Erased-cong f F.∘ Erased-cong g
    Erased-cong-≃ᴱ-∘ ext _ _ =
      EEq.[]-cong.to≡to→≡-Erased ax ext (refl _)

    -- Erased is functorial for embeddings (assuming extensionality).

    Erased-cong-Embedding-id :
      {@0 A : Type a} →
      Extensionality a a →
      Erased-cong {k = embedding} F.id ≡ F.id {A = Erased A}
    Erased-cong-Embedding-id ext =
      _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _

    Erased-cong-Embedding-∘ :
      {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} →
      Extensionality (a ⊔ c) (a ⊔ c) →
      (@0 f : Embedding B C) (@0 g : Embedding A B) →
      Erased-cong {k = embedding} (f F.∘ g) ≡
      Erased-cong f F.∘ Erased-cong g
    Erased-cong-Embedding-∘ ext _ _ =
      _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _

    -- A lemma.

    right-inverse-of-cong-∘ :
      ∀ {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} {x} →
      (@0 f : B ↠ C) (@0 g : A ↠ B) →
      _↠_.right-inverse-of (Erased-cong (f F.∘ g)) x ≡
      _↠_.right-inverse-of (Erased-cong f F.∘ Erased-cong g) x
    right-inverse-of-cong-∘ {x = [ x ]} f g =
      []-cong [ trans (cong (_↠_.to f)
                              (_↠_.right-inverse-of g
                                 (_↠_.from f x)))
                           (_↠_.right-inverse-of f x)
              ]                                          ≡⟨ []-cong-trans ⟩

      trans ([]-cong [ cong (_↠_.to f)
                         (_↠_.right-inverse-of g
                            (_↠_.from f x)) ])
        ([]-cong [ _↠_.right-inverse-of f x ])           ≡⟨ cong (λ p → trans p _) []-cong-cong ⟩∎

      trans (cong (map (_↠_.to f))
                    ([]-cong [ _↠_.right-inverse-of g
                                 (_↠_.from f x) ]))
                 ([]-cong [ _↠_.right-inverse-of f x ])  ∎

    -- Erased is functorial for split surjections (assuming
    -- extensionality).

    Erased-cong-↠-id :
      {@0 A : Type a} →
      Extensionality a a →
      Erased-cong {k = surjection} F.id ≡ F.id {A = Erased A}
    Erased-cong-↠-id ext =                              $⟨ lemma ⟩
      _↔_.to ↠↔∃-Split-surjective (Erased-cong F.id) ≡
      _↔_.to ↠↔∃-Split-surjective F.id                  ↝⟨ Eq.≃-≡ (from-isomorphism ↠↔∃-Split-surjective) ⟩□

      Erased-cong F.id ≡ F.id                           □
      where
      lemma :
        (map id , λ x → [ erased x ] , []-cong [ refl _ ]) ≡
        (id , λ x → x , refl _)
      lemma =
        cong (_ ,_) $ apply-ext ext λ _ → cong (_ ,_) []-cong-[refl]

    Erased-cong-↠-∘ :
      {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} →
      Extensionality c (a ⊔ c) →
      (@0 f : B ↠ C) (@0 g : A ↠ B) →
      Erased-cong {k = surjection} (f F.∘ g) ≡
      Erased-cong f F.∘ Erased-cong g
    Erased-cong-↠-∘ ext f g =                                        $⟨ lemma ⟩
      _↔_.to ↠↔∃-Split-surjective (Erased-cong (f F.∘ g)) ≡
      _↔_.to ↠↔∃-Split-surjective (Erased-cong f F.∘ Erased-cong g)  ↝⟨ Eq.≃-≡ (from-isomorphism ↠↔∃-Split-surjective) ⟩□

      Erased-cong (f F.∘ g) ≡ Erased-cong f F.∘ Erased-cong g        □
      where
      lemma :
        ( map (_↠_.to f ∘ _↠_.to g)
        , (λ x →
               [ _↠_.from g (_↠_.from f (erased x)) ]
             , _↠_.right-inverse-of (Erased-cong (f F.∘ g)) x)
        )
        ≡
        ( (λ x → [ _↠_.to f (_↠_.to g (erased x)) ])
        , (λ x →
               [ _↠_.from g (_↠_.from f (erased x)) ]
             , _↠_.right-inverse-of (Erased-cong f F.∘ Erased-cong g) x)
        )
      lemma =
        cong (_ ,_) $ apply-ext ext λ ([ x ]) →
          cong ([ _↠_.from g (_↠_.from f x) ] ,_)
            (right-inverse-of-cong-∘ f g)

    -- Erased is functorial for bijections (assuming extensionality).

    Erased-cong-↔-id :
      {@0 A : Type a} →
      Extensionality a a →
      Erased-cong {k = bijection} F.id ≡ F.id {A = Erased A}
    Erased-cong-↔-id ext =                          $⟨ lemma ⟩
      _↔_.to Bijection.↔-as-Σ (Erased-cong F.id) ≡
      _↔_.to Bijection.↔-as-Σ F.id                  ↝⟨ Eq.≃-≡ (from-isomorphism Bijection.↔-as-Σ) ⟩□

      Erased-cong F.id ≡ F.id                       □
      where
      lemma :
        ( map id
        , map id
        , (λ { [ x ] → []-cong [ refl x ] })
        , (λ { [ x ] → []-cong [ refl x ] })
        ) ≡
        (id , id , refl , refl)
      lemma = cong (λ p → id , id , p) $ cong₂ _,_
        (apply-ext ext λ _ → []-cong-[refl])
        (apply-ext ext λ _ → []-cong-[refl])

    Erased-cong-↔-∘ :
      {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} →
      Extensionality (a ⊔ c) (a ⊔ c) →
      (@0 f : B ↔ C) (@0 g : A ↔ B) →
      Erased-cong {k = bijection} (f F.∘ g) ≡
      Erased-cong f F.∘ Erased-cong g
    Erased-cong-↔-∘ {a = a} {c = c} ext f g =                    $⟨ lemma ⟩
      _↔_.to Bijection.↔-as-Σ (Erased-cong (f F.∘ g)) ≡
      _↔_.to Bijection.↔-as-Σ (Erased-cong f F.∘ Erased-cong g)  ↝⟨ Eq.≃-≡ (from-isomorphism Bijection.↔-as-Σ) ⟩□

      Erased-cong (f F.∘ g) ≡ Erased-cong f F.∘ Erased-cong g    □
      where
      lemma :
        ( map (_↔_.to f ∘ _↔_.to g)
        , map (_↔_.from g ∘ _↔_.from f)
        , _↔_.right-inverse-of (Erased-cong (f F.∘ g))
        , _↔_.left-inverse-of (Erased-cong (f F.∘ g))
        )
        ≡
        ( (λ x → [ _↔_.to f (_↔_.to g (erased x)) ])
        , (λ x → [ _↔_.from g (_↔_.from f (erased x)) ])
        , _↔_.right-inverse-of (Erased-cong f F.∘ Erased-cong g)
        , _↔_.left-inverse-of (Erased-cong f F.∘ Erased-cong g)
        )
      lemma =
        cong (λ p → map (_↔_.to f ∘ _↔_.to g)
                  , map (_↔_.from g ∘ _↔_.from f) , p) $
        cong₂ _,_
          (apply-ext (lower-extensionality a a ext) λ _ →
             right-inverse-of-cong-∘
               (_↔_.surjection f) (_↔_.surjection g))
          (apply-ext (lower-extensionality c c ext) λ _ →
           right-inverse-of-cong-∘
              (_↔_.surjection $ inverse g) (_↔_.surjection $ inverse f))

    -- Erased is functorial for injections (assuming extensionality).

    Erased-cong-↣-id :
      {@0 A : Type a} →
      Extensionality a a →
      Erased-cong {k = injection} F.id ≡ F.id {A = Erased A}
    Erased-cong-↣-id ext =                       $⟨ lemma ⟩
      _↔_.to ↣↔∃-Injective (Erased-cong F.id) ≡
      _↔_.to ↣↔∃-Injective F.id                  ↝⟨ Eq.≃-≡ (from-isomorphism ↣↔∃-Injective) ⟩□

      Erased-cong F.id ≡ F.id                    □
      where
      lemma :
        ( map id
        , λ {_ _} → _↣_.injective (Erased-cong F.id)
        ) ≡
        (id , λ {_ _} → _↣_.injective F.id)
      lemma =
        cong (_ ,_) $
        implicit-extensionality ext λ _ →
        implicit-extensionality ext λ _ →
        apply-ext ext λ eq →
          []-cong ([]-cong⁻¹ eq)  ≡⟨ _↔_.right-inverse-of Erased-≡↔[]≡[] _ ⟩∎
          eq                      ∎

    Erased-cong-↣-∘ :
      {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} →
      Extensionality (a ⊔ c) (a ⊔ c) →
      (@0 f : B ↣ C) (@0 g : A ↣ B) →
      Erased-cong {k = injection} (f F.∘ g) ≡
      Erased-cong f F.∘ Erased-cong g
    Erased-cong-↣-∘ {a = a} {c = c} ext f g =                  $⟨ lemma ⟩
      _↔_.to ↣↔∃-Injective (Erased-cong (f F.∘ g)) ≡
      _↔_.to ↣↔∃-Injective (Erased-cong f F.∘ Erased-cong g)   ↝⟨ Eq.≃-≡ (from-isomorphism ↣↔∃-Injective) ⟩□

      Erased-cong (f F.∘ g) ≡ Erased-cong f F.∘ Erased-cong g  □
      where
      lemma :
        ( map (_↣_.to f ∘ _↣_.to g)
        , λ {_ _} → _↣_.injective (Erased-cong (f F.∘ g))
        )
        ≡
        ( (λ x → [ _↣_.to f (_↣_.to g (erased x)) ])
        , λ {_ _} → _↣_.injective (Erased-cong f F.∘ Erased-cong g)
        )
      lemma =
        cong (_ ,_) $
        implicit-extensionality (lower-extensionality c lzero ext) λ _ →
        implicit-extensionality (lower-extensionality c lzero ext) λ _ →
        apply-ext (lower-extensionality a c ext) λ eq →
          let eq′ = [ _↣_.injective f (erased ([]-cong⁻¹ eq)) ]
          in
          []-cong [ _↣_.injective g (erased eq′) ]                        ≡⟨ cong []-cong $ []-cong [ cong (_↣_.injective g ∘ erased) $ sym $
                                                                             _↔_.left-inverse-of Erased-≡↔[]≡[] _ ] ⟩∎
          []-cong [ _↣_.injective g (erased ([]-cong⁻¹ ([]-cong eq′))) ]  ∎

  -- Erased is functorial for all kinds of functions (in some cases
  -- assuming extensionality).

  Erased-cong-id :
    {@0 A : Type a} →
    Extensionality? k a a →
    Erased-cong F.id ≡ F.id {k = k} {A = Erased A}
  Erased-cong-id {k = implication}         = λ _ → map-id
  Erased-cong-id {k = logical-equivalence} = λ _ → Erased-cong-⇔-id
  Erased-cong-id {k = injection}           = Erased-cong-↣-id
  Erased-cong-id {k = embedding}           = Erased-cong-Embedding-id
  Erased-cong-id {k = surjection}          = Erased-cong-↠-id
  Erased-cong-id {k = bijection}           = Erased-cong-↔-id
  Erased-cong-id {k = equivalence}         = Erased-cong-≃-id
  Erased-cong-id {k = equivalenceᴱ}        = Erased-cong-≃ᴱ-id

  Erased-cong-∘ :
    {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} →
    Extensionality? k (a ⊔ c) (a ⊔ c) →
    (@0 f : B ↝[ k ] C) (@0 g : A  ↝[ k ] B) →
    Erased-cong (f F.∘ g) ≡ Erased-cong f F.∘ Erased-cong g
  Erased-cong-∘         {k = implication}         = λ _ f → map-∘ f
  Erased-cong-∘         {k = logical-equivalence} = λ _ → Erased-cong-⇔-∘
  Erased-cong-∘         {k = injection}           = Erased-cong-↣-∘
  Erased-cong-∘         {k = embedding}           = Erased-cong-Embedding-∘
  Erased-cong-∘ {a = a} {k = surjection}          = λ ext →
                                                      Erased-cong-↠-∘
                                                        (lower-extensionality a lzero ext)
  Erased-cong-∘         {k = bijection}           = Erased-cong-↔-∘
  Erased-cong-∘         {k = equivalence}         = Erased-cong-≃-∘
  Erased-cong-∘         {k = equivalenceᴱ}        = Erased-cong-≃ᴱ-∘

  ----------------------------------------------------------------------
  -- Erased singletons

  -- A variant of the Singleton type family with erased equality proofs.

  Erased-singleton : {A : Type a} → @0 A → Type a
  Erased-singleton x = ∃ λ y → Erased (y ≡ x)

  -- A variant of Other-singleton.

  Erased-other-singleton : {A : Type a} → @0 A → Type a
  Erased-other-singleton x = ∃ λ y → Erased (x ≡ y)

  -- "Inspection" with erased proofs.

  inspectᴱ : (x : A) → Erased-other-singleton x
  inspectᴱ x = x , [ refl x ]

  -- The type of triples consisting of two values of type A, one erased,
  -- and an erased proof of equality of the two values is isomorphic to
  -- A.

  Σ-Erased-Erased-singleton↔ :
    (∃ λ (x : Erased A) → Erased-singleton (erased x)) ↔ A
  Σ-Erased-Erased-singleton↔ {A = A} =
    (∃ λ (x : Erased A) → ∃ λ y → Erased (y ≡ erased x))  ↝⟨ ∃-comm ⟩
    (∃ λ y → ∃ λ (x : Erased A) → Erased (y ≡ erased x))  ↝⟨ (∃-cong λ _ → inverse Erased-Σ↔Σ) ⟩
    (∃ λ y → Erased (∃ λ (x : A) → y ≡ x))                ↝⟨ (∃-cong λ _ → Erased-cong (_⇔_.to contractible⇔↔⊤ (other-singleton-contractible _))) ⟩
    A × Erased ⊤                                          ↝⟨ drop-⊤-right (λ _ → Erased-⊤↔⊤) ⟩□
    A                                                     □

  -- If equality is very stable for A, then Erased-singleton x is
  -- contractible for x : A.

  erased-singleton-contractible :
    {x : A} →
    Very-stable-≡ A →
    Contractible (Erased-singleton x)
  erased-singleton-contractible {x = x} s =
                                       $⟨ singleton-contractible x ⟩
    Contractible (Singleton x)         ↝⟨ H-level-cong _ 0 (∃-cong λ _ → Eq.⟨ _ , s _ _ ⟩) ⦂ (_ → _) ⟩□
    Contractible (Erased-singleton x)  □

  -- Erased-singleton x is contractible with an erased proof.

  Contractibleᴱ-Erased-singleton : Contractibleᴱ (Erased-singleton x)
  Contractibleᴱ-Erased-singleton {x = x} =
                                        $⟨ singleton-contractible x ⟩
    Contractible  (Singleton x)         ↝⟨ ECP.Contractible→Contractibleᴱ ⟩
    Contractibleᴱ (Singleton x)         ↝⟨ ECP.Contractibleᴱ-respects-surjection
                                             (Σ-map id [_]→)
                                             (_≃_.split-surjective $ Eq.↔→≃ _
                                                (Σ-map id erased)
                                                (λ _ → refl _)
                                                (λ _ → refl _)) ⟩□
    Contractibleᴱ (Erased-singleton x)  □

  -- Erased-other-singleton x is contractible with an erased proof.

  Contractibleᴱ-Erased-other-singleton :
    Contractibleᴱ (Erased-other-singleton x)
  Contractibleᴱ-Erased-other-singleton {x = x} =
                                              $⟨ other-singleton-contractible x ⟩
    Contractible  (Other-singleton x)         ↝⟨ ECP.Contractible→Contractibleᴱ ⟩
    Contractibleᴱ (Other-singleton x)         ↝⟨ ECP.Contractibleᴱ-respects-surjection
                                                   (Σ-map id [_]→)
                                                   (_≃_.split-surjective $ Eq.↔→≃ _
                                                      (Σ-map id erased)
                                                      (λ _ → refl _)
                                                      (λ _ → refl _)) ⟩□
    Contractibleᴱ (Erased-other-singleton x)  □

  -- Erased-singleton x is equivalent, with erased proofs, to ⊤.

  Erased-singleton≃ᴱ⊤ : Erased-singleton x ≃ᴱ ⊤
  Erased-singleton≃ᴱ⊤ =
    _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ Contractibleᴱ-Erased-singleton

  -- Erased-other-singleton x is equivalent, with erased proofs, to ⊤.

  Erased-other-singleton≃ᴱ⊤ : Erased-other-singleton x ≃ᴱ ⊤
  Erased-other-singleton≃ᴱ⊤ =
    _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ Contractibleᴱ-Erased-other-singleton

  -- If equality is very stable (with erased proofs) for A, and x : A
  -- is erased, then Erased-singleton x is a proposition.

  erased-singleton-with-erased-center-propositional :
    {@0 x : A} →
    Very-stableᴱ-≡ A →
    Is-proposition (Erased-singleton x)
  erased-singleton-with-erased-center-propositional {x = x} s =
                                                   $⟨ [ erased-singleton-contractible (λ _ _ → erased Erased-Very-stable) ] ⟩
    Erased (Contractible (Erased-singleton x))     ↝⟨ Erased-cong (mono₁ 0) ⟩
    Erased (Is-proposition (Erased-singleton x))   ↝⟨ (Stable-H-level 0 $
                                                       Very-stableᴱ→Stable 1 $
                                                       Very-stableᴱ-Σⁿ 1 s λ _ →
                                                       Very-stable→Very-stableᴱ 1 $
                                                       Very-stable→Very-stable-≡ 0
                                                       Very-stable-Erased) ⟩□
    Is-proposition (Erased-singleton x)            □

  -- If A is very stable, and x : A is erased, then Erased-singleton x
  -- is contractible.

  erased-singleton-with-erased-center-contractible :
    {@0 x : A} →
    Very-stable A →
    Contractible (Erased-singleton x)
  erased-singleton-with-erased-center-contractible {x = x} s =
                                       $⟨ [ (x , [ refl _ ]) ] ⟩
    Erased (Erased-singleton x)        ↝⟨ Very-stable→Stable 0 (Very-stable-Σ s λ _ → Very-stable-Erased) ⟩
    Erased-singleton x                 ↝⟨ propositional⇒inhabited⇒contractible $
                                          erased-singleton-with-erased-center-propositional $
                                          Very-stable→Very-stableᴱ 1 $
                                          Very-stable→Very-stable-≡ 0 s ⟩□
    Contractible (Erased-singleton x)  □
