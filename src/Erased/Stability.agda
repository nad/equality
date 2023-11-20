------------------------------------------------------------------------
-- Properties related to stability for Erased
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Erased.Stability
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence as LE using (_⇔_)
open import Prelude as P

open import Bijection eq as Bijection using (_↔_; Has-quasi-inverse)
open import Double-negation eq as DN
open import Embedding eq as Emb using (Embedding; Is-embedding)
open import Embedding.Erased eq as EEmb using (Is-embeddingᴱ)
open import Equality.Decidable-UIP eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages eq as ECP
  using (Contractibleᴱ)
import Equivalence.Half-adjoint eq as HA
open import Equivalence.Path-split eq as PS
  using (Is-∞-extendable-along-[_]; Is-[_]-extendable-along-[_];
         _-Null_; _-Nullᴱ_)
open import Excluded-middle eq
open import Extensionality eq hiding (module Extensionality)
open import For-iterated-equality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (_↣_; Injective)
import List eq as L
open import Modality.Basics eq
import Modality.Empty-modal eq as EM
open import Modality.Identity eq using (Identity-modality)
import Nat eq as Nat
open import Surjection eq using (_↠_; Split-surjective)
open import Univalence-axiom eq

open import Erased.Level-1 eq as E₁
  hiding (module []-cong; module []-cong₁; module []-cong₂;
          module Extensionality)
import Erased.Level-2
private
  module E₂ = Erased.Level-2 eq

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ p : Level
    A B                : Type a
    P                  : A → Type p
    ext f k k′ r s x y : A
    n                  : ℕ

------------------------------------------------------------------------
-- Some lemmas related to stability

-- If A is very stable, then [_]→ {A = A} is an embedding.

Very-stable→Is-embedding-[] :
  Very-stable A → Is-embedding [ A ∣_]→
Very-stable→Is-embedding-[] {A} s x y =
  _≃_.is-equivalence ≡≃[]≡[]
  where
  A≃Erased-A : A ≃ Erased A
  A≃Erased-A = Eq.⟨ _ , s ⟩

  ≡≃[]≡[] : (x ≡ y) ≃ ([ x ] ≡ [ y ])
  ≡≃[]≡[] = inverse $ Eq.≃-≡ A≃Erased-A

-- If A is very stable, then [_]→ {A = A} is split surjective.

Very-stable→Split-surjective-[] :
  Very-stable A → Split-surjective [ A ∣_]→
Very-stable→Split-surjective-[] {A} =
  Very-stable A          ↔⟨⟩
  Is-equivalence [_]→    ↝⟨ (λ hyp → _↠_.split-surjective $ _≃_.surjection $ Eq.⟨ _ , hyp ⟩) ⟩
  Split-surjective [_]→  □

-- Very-stable is propositional (assuming extensionality).

Very-stable-propositional :
  {A : Type a} →
  Extensionality a a →
  Is-proposition (Very-stable A)
Very-stable-propositional = Is-equivalence-propositional

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

Very-stable→Stable₀ : {@0 A : Type a} → Very-stable A → Stable A
Very-stable→Stable₀ s = Eq._≃₀_.from Eq.⟨ _ , s ⟩

-- A variant of Very-stable→Stable₀.

Very-stable→Stable :
  ∀ n →
  For-iterated-equality n Very-stable A →
  For-iterated-equality n Stable-[ k ] A
Very-stable→Stable {k} n =
  For-iterated-equality-cong₁ _ n λ {A} →
    Very-stable A             ↝⟨ Eq.⟨ _ ,_⟩ ⟩
    A ≃ Erased A              ↝⟨ inverse ⟩
    Erased A ≃ A              ↔⟨⟩
    Stable-[ equivalence ] A  ↝⟨ from-equivalence ⟩□
    Stable-[ k ] A            □

-- Very-stable→Stable₀ s is definitionally equal to
-- Very-stable→Stable 0 s.

_ : Very-stable→Stable₀ s ≡ Very-stable→Stable 0 s
_ = refl _

-- Very-stable→Stable₀ maps [ x ] to x.
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
  Very-stable→Stable₀ s [ x ] ≡ x
Very-stable→Stable-[]≡id {x} s =
  Very-stable→Stable₀ s [ x ]      ≡⟨⟩
  Eq._≃₀_.from Eq.⟨ _ , s ⟩ [ x ]  ≡⟨ _≃_.left-inverse-of Eq.⟨ _ , s ⟩ x ⟩∎
  x                                ∎

-- Very stable types are very stable with erased proofs.

Very-stable→Very-stableᴱ :
  {@0 A : Type a} →
  ∀ n →
  For-iterated-equality n Very-stable A →
  For-iterated-equality n Very-stableᴱ A
Very-stable→Very-stableᴱ n =
  For-iterated-equality-cong₁ᴱ-→ n EEq.Is-equivalence→Is-equivalenceᴱ

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
  {@0 A : Type a} →
  ∀ n →
  For-iterated-equality n Very-stableᴱ A →
  For-iterated-equality n Stable-[ equivalenceᴱ ] A
Very-stableᴱ→Stable-≃ᴱ {A} n =
  For-iterated-equality-cong₁ᴱ-→ n λ {A} →
    Very-stableᴱ A             →⟨ EEq.⟨ _ ,_⟩₀ ⟩
    A ≃ᴱ Erased A              →⟨ EEq.inverse ⟩
    Erased A ≃ᴱ A              →⟨ id ⟩□
    Stable-[ equivalenceᴱ ] A  □

-- If A is very stable with erased proofs, then A is stable.

Very-stableᴱ→Stable :
  {@0 A : Type a} →
  ∀ n →
  For-iterated-equality n Very-stableᴱ A →
  For-iterated-equality n Stable A
Very-stableᴱ→Stable {A} n =
  For-iterated-equality n Very-stableᴱ A             →⟨ Very-stableᴱ→Stable-≃ᴱ n ⟩
  For-iterated-equality n Stable-[ equivalenceᴱ ] A  →⟨ For-iterated-equality-cong₁ᴱ-→ n _≃ᴱ_.to ⟩□
  For-iterated-equality n Stable A                   □

-- The function obtained from Very-stableᴱ→Stable 0 maps [ x ] to x
-- (in erased contexts).

@0 Very-stableᴱ→Stable-[]≡id :
  (s : Very-stableᴱ A) →
  Very-stableᴱ→Stable 0 s [ x ] ≡ x
Very-stableᴱ→Stable-[]≡id {x} s =
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
  {@0 A : Type a} →
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
Erased-Very-stable {A} =
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
  {@0 A : Type a} →
  Very-stableᴱ (Very-stableᴱ A) →
  Very-stableᴱ A
Very-stableᴱ-Very-stableᴱ→Very-stableᴱ {A} s =
                           $⟨ Erased-Very-stable ⟩
  Erased (Very-stable A)   →⟨ map (Very-stable→Very-stableᴱ 0) ⟩
  Erased (Very-stableᴱ A)  →⟨ Very-stableᴱ→Stable 0 s ⟩□
  Very-stableᴱ A           □

-- It is not the case that every very stable type is a proposition.

¬-Very-stable→Is-proposition :
  ¬ ({A : Type a} → Very-stable A → Is-proposition A)
¬-Very-stable→Is-proposition {a} hyp =
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

¬¬-stable→Stable : {@0 A : Type a} → (¬ ¬ A → A) → Stable A
¬¬-stable→Stable ¬¬-Stable x = ¬¬-Stable (Erased→¬¬ x)

-- Types for which it is known whether or not they are inhabited are
-- stable.

Dec→Stable : {@0 A : Type a} → Dec A → Stable A
Dec→Stable (yes x) _ = x
Dec→Stable (no ¬x) x with () ← Erased→¬¬ x ¬x

-- Every type is stable in the double-negation monad.

¬¬-Stable : {@0 A : Type a} → ¬¬ Stable A
¬¬-Stable = DN.map′ Dec→Stable excluded-middle

-- Every type is very stable in the double-negation monad.
--
-- One can prove that the type
--
--   []-cong-axiomatisation ℓ →
--   {A : Type ℓ} →
--   ¬¬ (Extensionality ℓ ℓ → Very-stable A)
--
-- is inhabited by using a lemma,
-- Modality.Empty-modal.¬¬-Empty-modal→Very-modal→Modal, that is
-- similar to one suggested by Felix Cherubini (and I did not state
-- and prove the lemma below until after Felix made that suggestion to
-- me).

¬¬-Very-stable : {@0 A : Type ℓ} → ¬¬ Very-stable A
¬¬-Very-stable {A} =      $⟨ Erased-Very-stable ⟩
  Erased (Very-stable A)  →⟨ wrap ∘ Erased→¬¬ ⟩□
  ¬¬ Very-stable A        □

-- If equality is stable for A and B, then A ≃ᴱ B implies A ≃ B.

Stable-≡→≃ᴱ→≃ : Stable-≡ A → Stable-≡ B → A ≃ᴱ B → A ≃ B
Stable-≡→≃ᴱ→≃ sA sB A≃ᴱB = Eq.↔→≃
  (_≃ᴱ_.to   A≃ᴱB)
  (_≃ᴱ_.from A≃ᴱB)
  (λ x → sB _ _ [ _≃ᴱ_.right-inverse-of A≃ᴱB x ])
  (λ x → sA _ _ [ _≃ᴱ_.left-inverse-of  A≃ᴱB x ])

-- If A is stable, with an erased proof showing that [_]→ is a right
-- inverse of the proof of stability, then A is very stable with
-- erased proofs.

Stable→Left-inverse→Very-stableᴱ :
  {@0 A : Type a} →
  (s : Stable A) → @0 (∀ x → s [ x ] ≡ x) → Very-stableᴱ A
Stable→Left-inverse→Very-stableᴱ s inv =
  _≃ᴱ_.is-equivalence $
  EEq.↔→≃ᴱ
    _
    s
    (λ ([ x ]) → cong [_]→ (inv x))
    inv

private

  -- A lemma used below.

  H-level-suc→For-iterated-equality-Is-proposition :
    H-level (1 + n) A →
    For-iterated-equality n Is-proposition A
  H-level-suc→For-iterated-equality-Is-proposition {n} {A} =
    H-level (1 + n) A                         ↝⟨ _⇔_.to H-level⇔H-level′ ⟩
    H-level′ (1 + n) A                        ↝⟨ inverse-ext? (For-iterated-equality-For-iterated-equality n 1) _ ⟩
    For-iterated-equality n (H-level′ 1) A    ↝⟨ For-iterated-equality-cong₁ _ n $
                                                 _⇔_.from (H-level⇔H-level′ {n = 1}) ⟩□
    For-iterated-equality n Is-proposition A  □

-- If A is stable, and there is an erased proof showing that A is a
-- proposition, then A is very stable with erased proofs.

Stable-proposition→Very-stableᴱ :
  {@0 A : Type a} →
  Stable A → @0 Is-proposition A → Very-stableᴱ A
Stable-proposition→Very-stableᴱ {A} s prop =
  _≃ᴱ_.is-equivalence $
  EEq.⇔→≃ᴱ
    prop
    (                           $⟨ prop ⟩
     Is-proposition A           ↝⟨ H-level-cong _ 1 (inverse $ Erased↔ .erased) ⦂ (_ → _) ⟩□
     Is-proposition (Erased A)  □)
    [_]→
    s

-- The previous result can be generalised.

Stable→H-level-suc→Very-stableᴱ :
  {@0 A : Type a} →
  ∀ n →
  For-iterated-equality n Stable A →
  @0 H-level (1 + n) A →
  For-iterated-equality n Very-stableᴱ A
Stable→H-level-suc→Very-stableᴱ {A} n s h =                    $⟨ s ,′ [ H-level-suc→For-iterated-equality-Is-proposition h ] ⟩
  For-iterated-equality n Stable A ×
  Erased (For-iterated-equality n Is-proposition A)            →⟨ Σ-map id $
                                                                  For-iterated-equality-commutesᴱ-→ (λ A → Erased A) n (λ ([ f ]) x → [ f x ]) ⟩
  For-iterated-equality n Stable A ×
  For-iterated-equality n (λ A → Erased (Is-proposition A)) A  →⟨ For-iterated-equality-commutesᴱ-×-→ n ⟩

  For-iterated-equality n
    (λ A → Stable A × Erased (Is-proposition A)) A             →⟨ (For-iterated-equality-cong₁ᴱ-→ n λ (s , [ prop ]) →
                                                                   Stable-proposition→Very-stableᴱ s prop) ⟩□
  For-iterated-equality n Very-stableᴱ A                       □

-- Types that are contractible with erased proofs (n levels up) are
-- very stable with erased proofs (n levels up).

H-level→Very-stableᴱ :
  {@0 A : Type a} →
  ∀ n →
  For-iterated-equality n Contractibleᴱ A →
  For-iterated-equality n Very-stableᴱ A
H-level→Very-stableᴱ {A} n =
  For-iterated-equality n Contractibleᴱ A  →⟨ For-iterated-equality-cong₁ᴱ-→ n Contractibleᴱ→Very-stableᴱ ⟩□
  For-iterated-equality n Very-stableᴱ A   □
  where
  Contractibleᴱ→Very-stableᴱ :
    ∀ {@0 A} → Contractibleᴱ A → Very-stableᴱ A
  Contractibleᴱ→Very-stableᴱ c =
    Stable-proposition→Very-stableᴱ
      (λ _ → proj₁₀ c)
      (mono₁ 0 $ ECP.Contractibleᴱ→Contractible c)

------------------------------------------------------------------------
-- Preservation lemmas

-- A kind of map function for Stable.

Stable-map :
  {@0 A : Type a} {@0 B : Type b} →
  (A → B) → @0 (B → A) → Stable A → Stable B
Stable-map A→B B→A s x = A→B (s (map B→A x))

-- A variant of Stable-map.

Stable-map-⇔ :
  {@0 A : Type a} {@0 B : Type b} →
  A ⇔ B → Stable A → Stable B
Stable-map-⇔ A⇔B =
  Stable-map (to-implication A⇔B) (_⇔_.from A⇔B)

-- Stable-[ equivalenceᴱ ] preserves equivalences with erased proofs
-- (assuming extensionality).

Stable-≃ᴱ-cong :
  {A : Type ℓ₁} {B : Type ℓ₂} →
  @0 Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
  A ≃ᴱ B → Stable-[ equivalenceᴱ ] A ≃ᴱ Stable-[ equivalenceᴱ ] B
Stable-≃ᴱ-cong {A} {B} ext A≃B =
  Stable-[ equivalenceᴱ ] A  ↔⟨⟩
  Erased A ≃ᴱ A              ↝⟨ EEq.≃ᴱ-cong ext (Erased-cong-≃ᴱ A≃B) A≃B ⟩
  Erased B ≃ᴱ B              ↔⟨⟩
  Stable-[ equivalenceᴱ ] B  □

-- If there is an injective function from A to B, and equality is
-- stable for B, then equality is stable for A.

Injective→Stable-≡→Stable-≡ :
  {@0 A : Type a} {@0 B : Type b} →
  (f : A → B) → Injective f → Stable-≡ B → Stable-≡ A
Injective→Stable-≡→Stable-≡ f inj s x y =
  Stable-map inj (cong f) (s (f x) (f y))

-- If there is a function from A to B, with an erased proof showing
-- that the function is an equivalence, and A is very stable with
-- erased proofs, then B is very stable with erased proofs.

→→Is-equivalence→Very-stableᴱ→Very-stableᴱ :
  {@0 A : Type a} {@0 B : Type b}
  (f : A → B) → @0 Is-equivalence f → Very-stableᴱ A → Very-stableᴱ B
→→Is-equivalence→Very-stableᴱ→Very-stableᴱ {A} {B} f eq s =
  _≃ᴱ_.is-equivalence $
  EEq.↔→≃ᴱ
    [_]→
    (Erased B  →⟨ map (_≃_.from Eq.⟨ _ , eq ⟩) ⟩
     Erased A  →⟨ _≃ᴱ_.from EEq.⟨ _ , s ⟩₀ ⟩
     A         →⟨ f ⟩□
     B         □)
    (λ ([ x ]) → cong [_]→ (lemma x))
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
  {@0 A : Type a} {@0 B : Type b} →
  A ≃ᴱ B → Very-stableᴱ A → Very-stableᴱ B
≃ᴱ→Very-stableᴱ→Very-stableᴱ A≃ᴱB =
  →→Is-equivalence→Very-stableᴱ→Very-stableᴱ
    _ (_≃_.is-equivalence $ EEq.≃ᴱ→≃ A≃ᴱB)

-- Very-stableᴱ preserves equivalences with erased proofs (assuming
-- extensionality).

Very-stableᴱ-cong :
  {@0 A : Type a} {@0 B : Type b} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  A ≃ᴱ B → Very-stableᴱ A ≃ᴱ Very-stableᴱ B
Very-stableᴱ-cong {a} {b} ext A≃ᴱB =
  EEq.⇔→≃ᴱ
    (Very-stableᴱ-propositional (lower-extensionality b b ext))
    (Very-stableᴱ-propositional (lower-extensionality a a ext))
    (≃ᴱ→Very-stableᴱ→Very-stableᴱ A≃ᴱB)
    (≃ᴱ→Very-stableᴱ→Very-stableᴱ (EEq.inverse A≃ᴱB))

-- A variant of Very-stableᴱ-cong.

Very-stableᴱ-congⁿ :
  {A : Type a} {B : Type b} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  ∀ n →
  A ↔[ k ] B →
  For-iterated-equality n Very-stableᴱ A ≃ᴱ
  For-iterated-equality n Very-stableᴱ B
Very-stableᴱ-congⁿ ext n A↔B =
  For-iterated-equality-cong
    [ ext ]
    n
    (Very-stableᴱ-cong ext ∘ from-isomorphism)
    (from-isomorphism A↔B)

------------------------------------------------------------------------
-- Closure properties

-- ⊤ is very stable.

Very-stable-⊤ : Very-stable ⊤
Very-stable-⊤ = _≃_.is-equivalence $ Eq.↔⇒≃ $ inverse Erased-⊤↔⊤

-- ⊥ is very stable.

Very-stable-⊥ : Very-stable (⊥ {ℓ = ℓ})
Very-stable-⊥ = _≃_.is-equivalence $ Eq.↔⇒≃ $ inverse Erased-⊥↔⊥

-- T b is very stable for all b : A ⊎ B.

Very-stable-T : (b : A ⊎ B) → Very-stable (T b)
Very-stable-T = P.[ (λ _ → Very-stable-⊤) , (λ _ → Very-stable-⊥) ]

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
Stable-[]-Π {P} ext s =
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
  {@0 A : Type a} {@0 P : A → Type p} →
  @0 Extensionality a p →
  (∀ x → Very-stableᴱ (P x)) →
  Very-stableᴱ ((x : A) → P x)
Very-stableᴱ-Π {P} ext s =
  _≃ᴱ_.is-equivalence
    ((∀ x → P x)           EEq.≃ᴱ⟨ (EEq.∀-cong-≃ᴱ ext λ x → EEq.⟨ _ , s x ⟩₀) ⟩
     (∀ x → Erased (P x))  EEq.≃ᴱ⟨ EEq.inverse Erased-Π≃ᴱΠ ⟩□
     Erased (∀ x → P x)    □)

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

-- One can sometimes drop Erased from the domain of a Π-type.

Π-Erased≃Π :
  {A : Type a} {P : @0 A → Type p} →
  Extensionality? ⌊ k ⌋-sym a p →
  (∀ (@0 x) → Stable-[ ⌊ k ⌋-sym ] (P x)) →
  ((x : Erased A) → P (erased x)) ↝[ ⌊ k ⌋-sym ] ((x : A) → P x)
Π-Erased≃Π {a} {p} {A} {P} = lemma₂
  where
  lemma₁ lemma₂ :
    Extensionality? ⌊ k ⌋-sym a p →
    (∀ (@0 x) → Stable-[ ⌊ k ⌋-sym ] (P x)) →
    ((x : Erased A) → P (erased x)) ↝[ ⌊ k ⌋-sym ] ((x : A) → P x)

  lemma₁ ext s =
    ((x : Erased A) → P (erased x))           ↝⟨ (∀-cong ext λ x → inverse $ s (erased x)) ⟩
    ((x : Erased A) → Erased (P (erased x)))  ↔⟨ inverse Erased-Π↔Π-Erased ⟩
    Erased ((x : A) → P x)                    ↝⟨ Stable-[]-Π ext (λ x → s x) ⟩□
    ((x : A) → P x)                           □

  lemma₂ {k = equivalence} ext s =
    Eq.with-other-function
      (lemma₁ ext s)
      (_∘ [_]→)
      (λ f → apply-ext ext λ x →
         _≃_.to (s x) (_≃_.from (s x) (f [ x ]))  ≡⟨ _≃_.right-inverse-of (s x) _ ⟩∎
         f [ x ]                                  ∎)
  lemma₂ {k = equivalenceᴱ} ext s =
    EEq.with-other-function
      (lemma₁ ext s)
      (_∘ [_]→)
      (λ f → apply-ext (erased ext) λ x →
         _≃ᴱ_.to (s x) (_≃ᴱ_.from (s x) (f [ x ]))  ≡⟨ _≃ᴱ_.right-inverse-of (s x) _ ⟩∎
         f [ x ]                                    ∎)
  lemma₂ {k = bijection} ext s =
    Bijection.with-other-function
      (lemma₁ ext s)
      (_∘ [_]→)
      (λ f → apply-ext ext λ x →
         _↔_.to (s x) (_↔_.from (s x) (f [ x ]))  ≡⟨ _↔_.right-inverse-of (s x) _ ⟩∎
         f [ x ]                                  ∎)
  lemma₂ {k = logical-equivalence} ext s =
    record (lemma₁ ext s) { to = _∘ [_]→ }

_ : _≃_.to (Π-Erased≃Π ext s) f x ≡ f [ x ]
_ = refl _

_ : _≃ᴱ_.to (Π-Erased≃Π ext s) f x ≡ f [ x ]
_ = refl _

_ : _↔_.to (Π-Erased≃Π ext s) f x ≡ f [ x ]
_ = refl _

_ : _⇔_.to (Π-Erased≃Π ext s) f x ≡ f [ x ]
_ = refl _

-- Stable is closed under Σ A if A is very stable.

Very-stable-Stable-Σ :
  Very-stable A →
  (∀ x → Stable-[ k ] (P x)) →
  Stable-[ k ] (Σ A P)
Very-stable-Stable-Σ {A} {P} s s′ =
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
Stable-Σ {A} {P} s₁ hyp s₂ =
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
Very-stable-Σ {A} {P} s s′ = _≃_.is-equivalence (
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
Stable-[]-× {A} {B} s s′ =
  Erased (A × B)       ↔⟨ Erased-Σ↔Σ ⟩
  Erased A × Erased B  ↝⟨ s ×-cong s′ ⟩□
  A × B                □

-- Very-stable is closed under _×_.

Very-stable-× : Very-stable A → Very-stable B → Very-stable (A × B)
Very-stable-× s s′ = _≃_.is-equivalence $
  inverse $ Stable-[]-× (inverse Eq.⟨ _ , s ⟩) (inverse Eq.⟨ _ , s′ ⟩)

-- Very-stableᴱ is closed under _×_.

Very-stableᴱ-× :
  {@0 A : Type a} {@0 B : Type b} →
  Very-stableᴱ A → Very-stableᴱ B → Very-stableᴱ (A × B)
Very-stableᴱ-× {A} {B} s s′ =
  _≃ᴱ_.is-equivalence
    (A × B                EEq.≃ᴱ⟨ EEq.⟨ _ , s ⟩₀ EEq.×-cong-≃ᴱ EEq.⟨ _ , s′ ⟩₀ ⟩
     Erased A × Erased B  EEq.↔⟨ inverse Erased-Σ↔Σ ⟩□
     Erased (A × B)       □)

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

-- Stable is closed under _⇔_.

Stable-⇔ : Stable A → Stable B → Stable (A ⇔ B)
Stable-⇔ {A} {B} s s′ =
                                   $⟨ (Stable-Π λ _ → s′) , (Stable-Π λ _ → s) ⟩
  Stable (A → B) × Stable (B → A)  →⟨ uncurry Stable-[]-× ⟩
  Stable ((A → B) × (B → A))       →⟨ Stable-map-⇔ (from-bijection $ inverse ⇔↔→×→) ⟩□
  Stable (A ⇔ B)                   □

-- Stable-[ k ] is closed under ↑ ℓ.

Stable-↑ : Stable-[ k ] A → Stable-[ k ] (↑ ℓ A)
Stable-↑ {A} s =
  Erased (↑ _ A)  ↔⟨ Erased-↑↔↑ ⟩
  ↑ _ (Erased A)  ↝⟨ ↑-cong s ⟩□
  ↑ _ A           □

-- Very-stable is closed under ↑ ℓ.

Very-stable-↑ : Very-stable A → Very-stable (↑ ℓ A)
Very-stable-↑ s = _≃_.is-equivalence $
  inverse $ Stable-↑ $ inverse Eq.⟨ _ , s ⟩

-- Very-stableᴱ is closed under ↑ ℓ.

Very-stableᴱ-↑ :
  {@0 A : Type a} →
  Very-stableᴱ A → Very-stableᴱ (↑ ℓ A)
Very-stableᴱ-↑ {A} s =
  _≃ᴱ_.is-equivalence
    (↑ _ A           EEq.≃ᴱ⟨ EEq.↑-cong-≃ᴱ EEq.⟨ _ , s ⟩₀ ⟩
     ↑ _ (Erased A)  EEq.↔⟨ inverse Erased-↑↔↑ ⟩□
     Erased (↑ _ A)  □)

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
Very-stable-¬ {A} ext =
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

-- If A is "stable 1 + n levels up", then H-level′ (1 + n) A is
-- stable.

Stable-H-level′ :
  ∀ n →
  For-iterated-equality (1 + n) Stable A →
  Stable (H-level′ (1 + n) A)
Stable-H-level′ {A} n =
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
Stable-H-level {A} n =
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

------------------------------------------------------------------------
-- Some properties related to "Modalities in Homotopy Type Theory"
-- by Rijke, Shulman and Spitters

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
  {@0 A : Type a} {@0 B : Type b} →
  @0 Extensionality a b →
  Very-stableᴱ B →
  Is-equivalenceᴱ (λ (f : Erased A → B) → f ∘ [_]→)
Is-equivalenceᴱ-∘[] ext s =
  _≃ᴱ_.is-equivalence $
  EEq.↔→≃ᴱ
    _
    (λ f x → _≃ᴱ_.from EEq.⟨ _ , s ⟩₀ (map f x))
    (λ f → apply-ext ext λ x →
       _≃ᴱ_.left-inverse-of EEq.⟨ _ , s ⟩ (f x))
    (λ f → apply-ext ext λ x →
       _≃ᴱ_.left-inverse-of EEq.⟨ _ , s ⟩ (f x))

------------------------------------------------------------------------
-- Erased is accessible and topological (given certain assumptions)

-- A definition of what it means for Erased to be accessible and
-- topological (for a certain universe level).
--
-- This definition is based on (one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory" by Rijke, Shulman
-- and Spitters.

Erased-is-accessible-and-topological′ : (a : Level) → Type (lsuc a)
Erased-is-accessible-and-topological′ a =
  ∃ λ (I : Type a) →
  ∃ λ (P : I → Type a) →
    (∀ i → Is-proposition (P i)) ×
    ((A : Type a) →
     Very-stable A ⇔
     ∀ i →
     Is-∞-extendable-along-[ (λ (_ : P i) → lift tt) ]
       (λ (_ : ↑ a ⊤) → A))

-- A variant of Erased-is-accessible-and-topological′ that does not
-- use Is-∞-extendable-along-[_].

Erased-is-accessible-and-topological : (a : Level) → Type (lsuc a)
Erased-is-accessible-and-topological a =
  ∃ λ (I : Type a) →
  ∃ λ (P : I → Type a) →
    (∀ i → Is-proposition (P i)) ×
    ((A : Type a) → Very-stable A ⇔ P -Null A)

-- Erased-is-accessible-and-topological′ and
-- Erased-is-accessible-and-topological are pointwise equivalent
-- (assuming extensionality).

≃Erased-is-accessible-and-topological :
  Extensionality (lsuc a) a →
  Erased-is-accessible-and-topological′ a ≃
  Erased-is-accessible-and-topological a
≃Erased-is-accessible-and-topological {a} ext =
  ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
  ∀-cong ext λ _ →
  ⇔-cong (lower-extensionality _ lzero ext) Eq.id $
  PS.Π-Is-∞-extendable-along≃Null
    (lower-extensionality _ lzero ext)

-- A variant of Erased-is-accessible-and-topological that uses
-- Very-stableᴱ instead of Very-stable and _-Nullᴱ_ instead of
-- _-Null_, and for which Is-proposition is replaced by
-- Erased ∘ Is-proposition.

Erased-is-accessible-and-topologicalᴱ : (a : Level) → Type (lsuc a)
Erased-is-accessible-and-topologicalᴱ a =
  ∃ λ (I : Type a) →
  ∃ λ (P : I → Type a) →
    (∀ i → Erased (Is-proposition (P i))) ×
    ((A : Type a) → Very-stableᴱ A ⇔ P -Nullᴱ A)

-- In erased contexts Erased is accessible and topological.

@0 erased-is-accessible-and-topological-in-erased-contexts′ :
  Erased-is-accessible-and-topological′ a
erased-is-accessible-and-topological-in-erased-contexts′ {a} =
    ↑ a ⊤
  , (λ _ → ↑ a ⊤)
  , (λ _ → H-level.mono₁ 0 (↑-closure 0 ⊤-contractible))
  , (λ _ → record
       { to   = λ _ _ → PS.∞-extendable-along-id
       ; from = λ _ → Erased-Very-stable .erased
       })

-- In erased contexts Erased is accessible and topological (assuming
-- extensionality).

@0 erased-is-accessible-and-topological-in-erased-contexts :
  Extensionality a a →
  Erased-is-accessible-and-topological a
erased-is-accessible-and-topological-in-erased-contexts {a} ext =
    ↑ a ⊤
  , (λ _ → ↑ a ⊤)
  , (λ _ → H-level.mono₁ 0 $ ↑-closure 0 ⊤-contractible)
  , λ A →
      Very-stable A          ↔⟨ _⇔_.to contractible⇔↔⊤ $
                                propositional⇒inhabited⇒contractible
                                  (Very-stable-propositional ext)
                                  (Erased-Very-stable .erased) ⟩
      ⊤                      ↝⟨ record { to = λ _ _ → _≃_.is-equivalence $ Eq.↔→≃ _ (_$ _) refl refl } ⟩□
      (λ _ → ↑ a ⊤) -Null A  □

-- In the presence of excluded middle Erased is accessible and
-- topological (assuming extensionality).

erased-is-accessible-and-topological :
  Excluded-middle a →
  Extensionality a a →
  Erased-is-accessible-and-topological a
erased-is-accessible-and-topological {a} em ext =                   $⟨ (λ _ →
                                                                          [ erased-is-accessible-and-topological-in-erased-contexts
                                                                              ext .proj₂ .proj₂ .proj₂ _ ]) ⟩
  ((A : Type a) →
   Erased (Very-stable A ⇔ (λ (_ : ↑ a ⊤) → ↑ a ⊤) -Null A))        →⟨ (wrap ∘ Erased→¬¬) ∘_ ⟩

  ((A : Type a) →
   ¬¬ (Very-stable A ⇔ (λ (_ : ↑ a ⊤) → ↑ a ⊤) -Null A))            →⟨ (∀-cong _ λ _ →
                                                                        Excluded-middle→Double-negation-elimination em $
                                                                        ⇔-closure ext 1
                                                                          (Very-stable-propositional ext)
                                                                          (Π-closure ext 1 λ _ →
                                                                           Is-equivalence-propositional ext)) ⟩

  ((A : Type a) → Very-stable A ⇔ (λ (_ : ↑ a ⊤) → ↑ a ⊤) -Null A)  →⟨ (λ hyp →
                                                                            _
                                                                          , _
                                                                          , (λ _ → H-level.mono₁ 0 $ ↑-closure 0 ⊤-contractible)
                                                                          , hyp) ⟩□
  Erased-is-accessible-and-topological a                            □

------------------------------------------------------------------------
-- Some lemmas related to Very-stable/Very-stableᴱ and
-- _-Null_/_-Nullᴱ_

-- Very-stable {a = a} is pointwise equivalent to
-- (λ (A : Type a) → Very-stable A) -Null_ (assuming extensionality).

Very-stable≃Very-stable-Null :
  {A : Type a} →
  Extensionality a a →
  Very-stable A ↝[ lsuc a ∣ a ] (λ (A : Type a) → Very-stable A) -Null A
Very-stable≃Very-stable-Null {A} ext =
  generalise-ext?-prop
    (record { to = to; from = from })
    (λ _ → Very-stable-propositional ext)
    (λ ext′ →
       Π-closure ext′ 1 λ _ →
       Is-equivalence-propositional ext)
  where
  open []-cong-axiomatisation
          (Extensionality→[]-cong-axiomatisation ext)

  to : Very-stable A → Very-stable -Null A
  to sA _ =
    _≃_.is-equivalence $
    Eq.↔→≃
      const
      (λ f → Very-stable→Stable 0 sA [ f sB ])
      (λ f → apply-ext ext λ x →
         const (Very-stable→Stable 0 sA [ f sB ]) x  ≡⟨⟩
         Very-stable→Stable 0 sA [ f sB ]            ≡⟨ cong (Very-stable→Stable 0 sA) $
                                                        []-cong [ cong f $ Very-stable-propositional ext _ _ ] ⟩
         Very-stable→Stable 0 sA [ f x ]             ≡⟨ Very-stable→Stable-[]≡id sA ⟩∎
         f x                                         ∎)
      (λ x →
         Very-stable→Stable 0 sA [ x ]  ≡⟨ Very-stable→Stable-[]≡id sA ⟩∎
         x                              ∎)
    where
    @0 sB : Very-stable B
    sB = Erased-Very-stable .erased

  from : Very-stable -Null A → Very-stable A
  from hyp =
    _≃_.is-equivalence $
    Eq.↔→≃
      [_]→
      (Erased A             →⟨ flip (Very-stable→Stable 0) ⟩
       (Very-stable A → A)  ↔⟨ inverse A≃ ⟩□
       A                    □)
      (λ ([ x ]) → []-cong [ lemma x ])
      lemma
    where
    A≃ : A ≃ (Very-stable A → A)
    A≃ = Eq.⟨ const , hyp A ⟩

    lemma :
      ∀ x →
      _≃_.from A≃ (λ s → Very-stable→Stable 0 s [ x ]) ≡ x
    lemma x =
      _≃_.from A≃ (λ s → Very-stable→Stable 0 s [ x ])  ≡⟨ (cong (_≃_.from A≃) $
                                                            apply-ext ext λ s →
                                                            Very-stable→Stable-[]≡id s) ⟩
      _≃_.from A≃ (const x)                             ≡⟨⟩
      _≃_.from A≃ (_≃_.to A≃ x)                         ≡⟨ _≃_.left-inverse-of A≃ _ ⟩∎
      x                                                 ∎

-- Very-stableᴱ {a = a} is pointwise equivalent to
-- (λ (A : Type a) → Very-stableᴱ A) -Nullᴱ_ (assuming
-- extensionality).

Very-stableᴱ≃Very-stableᴱ-Nullᴱ :
  {A : Type a} →
  @0 Extensionality (lsuc a) a →
  Very-stableᴱ A ≃ᴱ (λ (A : Type a) → Very-stableᴱ A) -Nullᴱ A
Very-stableᴱ≃Very-stableᴱ-Nullᴱ {A} ext =
  EEq.⇔→≃ᴱ
    (Very-stableᴱ-propositional ext′)
    (Π-closure ext 1 λ _ →
     EEq.Is-equivalenceᴱ-propositional ext′ _)
    to
    from
  where
  @0 ext′ : _
  ext′ = lower-extensionality _ lzero ext

  to : Very-stableᴱ A → Very-stableᴱ -Nullᴱ A
  to sA _ =
    _≃ᴱ_.is-equivalence $
    EEq.↔→≃ᴱ
      const
      (λ f → Very-stableᴱ→Stable 0 sA [ f sB ])
      (λ f → apply-ext ext′ λ x →
         const (Very-stableᴱ→Stable 0 sA [ f sB ]) x  ≡⟨⟩
         Very-stableᴱ→Stable 0 sA [ f sB ]            ≡⟨ cong (Very-stableᴱ→Stable 0 sA ∘ [_]→ ∘ f) $
                                                         Very-stableᴱ-propositional ext′ _ _ ⟩
         Very-stableᴱ→Stable 0 sA [ f x ]             ≡⟨ Very-stableᴱ→Stable-[]≡id sA ⟩∎
         f x                                          ∎)
      (λ x →
         Very-stableᴱ→Stable 0 sA [ x ]  ≡⟨ Very-stableᴱ→Stable-[]≡id sA ⟩∎
         x                               ∎)
    where
    @0 sB : Very-stableᴱ B
    sB = Very-stable→Very-stableᴱ 0 (Erased-Very-stable .erased)

  from : Very-stableᴱ -Nullᴱ A → Very-stableᴱ A
  from hyp =
    _≃ᴱ_.is-equivalence $
    EEq.↔→≃ᴱ
      [_]→
      (Erased A              →⟨ flip (Very-stableᴱ→Stable 0) ⟩
       (Very-stableᴱ A → A)  →⟨ _≃ᴱ_.from A≃ ⟩□
       A                     □)
      (cong [_]→ ∘ lemma ∘ erased)
      lemma
    where
    A≃ : A ≃ᴱ (Very-stableᴱ A → A)
    A≃ = EEq.⟨ const , hyp A ⟩

    @0 lemma :
      ∀ x →
      _≃ᴱ_.from A≃ (λ s → Very-stableᴱ→Stable 0 s [ x ]) ≡ x
    lemma x =
      _≃ᴱ_.from A≃ (λ s → Very-stableᴱ→Stable 0 s [ x ])  ≡⟨ (cong (_≃ᴱ_.from A≃) $
                                                              apply-ext ext′ λ s →
                                                              Very-stableᴱ→Stable-[]≡id s) ⟩
      _≃ᴱ_.from A≃ (const x)                              ≡⟨⟩
      _≃ᴱ_.from A≃ (_≃ᴱ_.to A≃ x)                         ≡⟨ _≃ᴱ_.left-inverse-of A≃ _ ⟩∎
      x                                                   ∎

------------------------------------------------------------------------
-- Erased singletons

-- A variant of the Singleton type family with erased equality proofs.

Erased-singleton : {A : Type a} → @0 A → Type a
Erased-singleton x = ∃ λ y → Erased (y ≡ x)

-- A variant of Other-singleton.

Erased-other-singleton : {A : Type a} → @0 A → Type a
Erased-other-singleton x = ∃ λ y → Erased (x ≡ y)

-- "Inspection" with erased proofs.

inspectᴱ :
  {@0 A : Type a}
  (x : A) → Erased-other-singleton x
inspectᴱ x = x , [ refl x ]

-- The type of triples consisting of two values of type A, one erased,
-- and an erased proof of equality of the two values is logically
-- equivalent to A.

Σ-Erased-Erased-singleton⇔ :
  {A : Type ℓ} →
  (∃ λ (x : Erased A) → Erased-singleton (erased x)) ⇔ A
Σ-Erased-Erased-singleton⇔ {A} =
  (∃ λ (x : Erased A) → ∃ λ y → Erased (y ≡ erased x))  ↔⟨ ∃-comm ⟩
  (∃ λ y → ∃ λ (x : Erased A) → Erased (y ≡ erased x))  ↔⟨ (∃-cong λ _ → inverse Erased-Σ↔Σ) ⟩
  (∃ λ y → Erased (∃ λ (x : A) → y ≡ x))                ↝⟨ (∃-cong λ _ → Erased-cong-⇔ (from-isomorphism $ _⇔_.to contractible⇔↔⊤ $
                                                            other-singleton-contractible _)) ⟩
  A × Erased ⊤                                          ↔⟨ drop-⊤-right (λ _ → Erased-⊤↔⊤) ⟩□
  A                                                     □

-- If equality is very stable for A, then Erased-singleton x is
-- contractible for x : A.
--
-- See also Very-stableᴱ-≡→Contractible-Erased-singleton,
-- erased-singleton-with-erased-center-propositional and
-- erased-singleton-with-erased-center-contractible below.

erased-singleton-contractible :
  {x : A} →
  Very-stable-≡ A →
  Contractible (Erased-singleton x)
erased-singleton-contractible {x} s =
                                     $⟨ singleton-contractible x ⟩
  Contractible (Singleton x)         ↝⟨ H-level-cong _ 0 (∃-cong λ _ → Eq.⟨ _ , s _ _ ⟩) ⦂ (_ → _) ⟩□
  Contractible (Erased-singleton x)  □

-- If equality is very stable for A, then Erased-other-singleton x is
-- contractible for x : A.

erased-other-singleton-contractible :
  {x : A} →
  Very-stable-≡ A →
  Contractible (Erased-other-singleton x)
erased-other-singleton-contractible {x} s =
                                           $⟨ other-singleton-contractible x ⟩
  Contractible (Other-singleton x)         ↝⟨ H-level-cong _ 0 (∃-cong λ _ → Eq.⟨ _ , s _ _ ⟩) ⦂ (_ → _) ⟩□
  Contractible (Erased-other-singleton x)  □

-- Erased-singleton x is contractible with an erased proof.

Contractibleᴱ-Erased-singleton :
  {@0 A : Type a} {x : A} →
  Contractibleᴱ (Erased-singleton x)
Contractibleᴱ-Erased-singleton {x} =
    (x , [ proj₂₀ (proj₁₀ contr) .erased ])
  , [ proj₂ contr ]
  where
  @0 contr : Contractible (Erased-singleton x)
  contr =
    erased-singleton-contractible
      (λ _ _ → Erased-Very-stable .erased)

-- Erased-other-singleton x is contractible with an erased proof.

Contractibleᴱ-Erased-other-singleton :
  {@0 A : Type a} {x : A} →
  Contractibleᴱ (Erased-other-singleton x)
Contractibleᴱ-Erased-other-singleton {x} =
    (x , [ proj₂ (proj₁ contr) .erased ])
  , [ proj₂ contr ]
  where
  @0 contr : Contractible (Erased-other-singleton x)
  contr =
    erased-other-singleton-contractible
      (λ _ _ → Erased-Very-stable .erased)

-- Erased-singleton x is equivalent, with erased proofs, to ⊤.

Erased-singleton≃ᴱ⊤ :
  {@0 A : Type a} {x : A} →
  Erased-singleton x ≃ᴱ ⊤
Erased-singleton≃ᴱ⊤ =
  let record { to = to } = EEq.Contractibleᴱ⇔≃ᴱ⊤ in
  to Contractibleᴱ-Erased-singleton

-- Erased-other-singleton x is equivalent, with erased proofs, to ⊤.

Erased-other-singleton≃ᴱ⊤ :
  {@0 A : Type a} {x : A} →
  Erased-other-singleton x ≃ᴱ ⊤
Erased-other-singleton≃ᴱ⊤ =
  let record { to = to } = EEq.Contractibleᴱ⇔≃ᴱ⊤ in
  to Contractibleᴱ-Erased-other-singleton

------------------------------------------------------------------------
-- Results that depend on an instantiation of the []-cong axioms (for
-- two universe levels)

module []-cong₂
  (ax₁ : []-cong-axiomatisation ℓ₁)
  (ax₂ : []-cong-axiomatisation ℓ₂)
  where

  open Erased-cong ax₁ ax₂

  ----------------------------------------------------------------------
  -- Preservation lemmas

  -- Stable-[ equivalence ] preserves equivalences (assuming
  -- extensionality).

  Stable-≃-cong :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    A ≃ B → Stable-[ equivalence ] A ↝[ k ] Stable-[ equivalence ] B
  Stable-≃-cong {A} {B} ext A≃B =
    Stable-[ equivalence ] A  ↔⟨⟩
    Erased A ≃ A              ↝⟨ generalise-ext?
                                   (Eq.≃-preserves-⇔ (Erased-cong-≃ A≃B) A≃B)
                                   (λ ext →
                                      let eq = Eq.≃-preserves ext (Erased-cong-≃ A≃B) A≃B in
                                      _≃_.right-inverse-of eq , _≃_.left-inverse-of eq)
                                   ext ⟩
    Erased B ≃ B              ↔⟨⟩
    Stable-[ equivalence ] B  □

  private

    -- A lemma used to implement Very-stable-map-↠ and
    -- Very-stable-cong.

    Very-stable-map-↠′ :
      {B : Type b} →
      []-cong-axiomatisation b →
      A ↠ B → Very-stable A → Very-stable B
    Very-stable-map-↠′ {A} {B} ax A↠B s =
      _≃_.is-equivalence $
      Eq.↔→≃
        _
        (Erased B  →⟨ map (_↠_.from A↠B) ⟩
         Erased A  →⟨ Very-stable→Stable 0 s ⟩
         A         →⟨ _↠_.to A↠B ⟩□
         B         □)
        (λ x →
           [ _↠_.to A↠B (Very-stable→Stable 0 s (map (_↠_.from A↠B) x)) ]  ≡⟨ []-cong-axiomatisation.[]-cong ax [ lemma (erased x) ] ⟩∎
           x                                                               ∎)
        lemma
      where
      lemma = λ x →
        _↠_.to A↠B (Very-stable→Stable 0 s (map (_↠_.from A↠B) [ x ]))  ≡⟨⟩
        _↠_.to A↠B (Very-stable→Stable 0 s [ _↠_.from A↠B x ])          ≡⟨ cong (_↠_.to A↠B) $ Very-stable→Stable-[]≡id s ⟩
        _↠_.to A↠B (_↠_.from A↠B x)                                     ≡⟨ _↠_.right-inverse-of A↠B _ ⟩∎
        x                                                               ∎

  -- If there is a split surjection from A to B, then Very-stable A
  -- implies Very-stable B.

  Very-stable-map-↠ :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    A ↠ B → Very-stable A → Very-stable B
  Very-stable-map-↠ = Very-stable-map-↠′ ax₂

  -- A generalisation of Very-stable-map-↠.
  --
  -- The case for 1 follows from one part of Remark 2.16 (2) from
  -- "Localization in homotopy type theory" by Christensen, Opie,
  -- Rijke and Scoccola.

  Very-stable-map-↠ⁿ :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    ∀ n →
    A ↠ B →
    For-iterated-equality n Very-stable A →
    For-iterated-equality n Very-stable B
  Very-stable-map-↠ⁿ n A↠B =
    For-iterated-equality-cong-→
      n
      Very-stable-map-↠
      A↠B

  -- Very-stable preserves equivalences (assuming extensionality).

  Very-stable-cong :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    A ≃ B → Very-stable A ↝[ k ] Very-stable B
  Very-stable-cong ext A≃B =
    generalise-ext?-prop
      (record
         { to   = Very-stable-map-↠′ ax₂ (_≃_.surjection A≃B)
         ; from = Very-stable-map-↠′ ax₁ (_≃_.surjection $ inverse A≃B)
         })
      (Very-stable-propositional ∘ lower-extensionality ℓ₂ ℓ₂)
      (Very-stable-propositional ∘ lower-extensionality ℓ₁ ℓ₁)
      ext

  -- A generalisation of Very-stable-cong.

  Very-stable-congⁿ :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    Extensionality? k′ (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
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

  -- If there is an embedding from B to A, and equality is very stable
  -- for A, then equality is very stable for B.
  --
  -- This follows from one part of Remark 2.16 (2) from "Localization
  -- in homotopy type theory" by Christensen, Opie, Rijke and
  -- Scoccola.
  --
  -- I based the proof on that of in_SepO_embedding, implemented by
  -- Mike Shulman in the file Separated.v in (one version of) the Coq
  -- HoTT library.

  Very-stable-≡-map-Embedding :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    Embedding B A → Very-stable-≡ A → Very-stable-≡ B
  Very-stable-≡-map-Embedding B↣A s x y =
                                                           $⟨ s _ _ ⟩
    Very-stable (Embedding.to B↣A x ≡ Embedding.to B↣A y)  →⟨ Very-stable-cong _ (inverse $ Embedding.equivalence B↣A) ⟩□
    Very-stable (x ≡ y)                                    □

------------------------------------------------------------------------
-- Results that depend on an instantiation of the []-cong axioms (for
-- two universe levels as well as their maximum)

module []-cong₂-⊔₁
  (ax₁ : []-cong-axiomatisation ℓ₁)
  (ax₂ : []-cong-axiomatisation ℓ₂)
  (ax  : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
  where

  open []-cong-axiomatisation ax
  open E₂.[]-cong₂-⊔ ax₁ ax₂ ax

  ----------------------------------------------------------------------
  -- Preservation lemmas

  -- A kind of map function for Stable-[_].

  Stable-[]-map :
    {A : Type ℓ₂} {B : Type ℓ₁} →
    A ↝[ k ] B → @0 B ↝[ k ] A → Stable-[ k ] A → Stable-[ k ] B
  Stable-[]-map {A} {B} A↝B B↝A s =
    Erased B  ↝⟨ Erased-cong B↝A ⟩
    Erased A  ↝⟨ s ⟩
    A         ↝⟨ A↝B ⟩□
    B         □

  -- Variants of Stable-[]-map.

  Stable-[]-map-↔ :
    {A : Type ℓ₂} {B : Type ℓ₁} →
    A ↔ B → Stable-[ k ] A → Stable-[ k ] B
  Stable-[]-map-↔ A↔B =
    Stable-[]-map
      (from-isomorphism A↔B)
      (from-isomorphism $ inverse A↔B)

  Stable-[]-map-↝ :
    {A : Type ℓ₂} {B : Type ℓ₁} →
    A ↝[ ℓ₂ ∣ ℓ₁ ] B →
    Extensionality? k ℓ₂ ℓ₁ → Stable-[ k ] A → Stable-[ k ] B
  Stable-[]-map-↝ A↝B ext =
    Stable-[]-map (A↝B ext) (inverse-ext? A↝B ext)

  -- Stable preserves some kinds of functions (those that are
  -- "symmetric"), possibly assuming extensionality.

  Stable-cong :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    Extensionality? ⌊ k ⌋-sym (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    A ↝[ ⌊ k ⌋-sym ] B → Stable A ↝[ ⌊ k ⌋-sym ] Stable B
  Stable-cong {k} {A} {B} ext A↝B =
    Stable A        ↔⟨⟩
    (Erased A → A)  ↝⟨ →-cong ext (Erased-cong A↝B) A↝B ⟩
    (Erased B → B)  ↔⟨⟩
    Stable B        □

  ----------------------------------------------------------------------
  -- Another lemma

  -- All kinds of functions between erased types are stable.

  Stable-Erased↝Erased :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
    Stable (Erased A ↝[ k ] Erased B)
  Stable-Erased↝Erased {k} {A} {B} =   $⟨ Very-stable-Erased ⟩
    Very-stable (Erased (A ↝[ k ] B))  ↝⟨ Very-stable→Stable 0 ⟩
    Stable (Erased (A ↝[ k ] B))       ↝⟨ Stable-map-⇔ (Erased-↝↝↝ _) ⟩□
    Stable (Erased A ↝[ k ] Erased B)  □

------------------------------------------------------------------------
-- Results that depend on an instantiation of the []-cong axioms (for
-- a single universe level)

module []-cong₁ (ax : []-cong-axiomatisation ℓ) where

  open E₁.[]-cong₁ ax
  open []-cong₂ ax ax
  open []-cong₂-⊔₁ ax ax ax

  ----------------------------------------------------------------------
  -- Some lemmas related to stability

  -- If A is stable, with [_]→ as a right inverse of the proof of
  -- stability, then A is very stable.

  Stable→Left-inverse→Very-stable :
    {A : Type ℓ}
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

  -- If A is a stable proposition, then A is very stable.
  --
  -- Note that it is not the case that every very stable type is a
  -- proposition, see ¬-Very-stable→Is-proposition.

  Stable-proposition→Very-stable :
    {A : Type ℓ} →
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
    {A : Type ℓ} →
    ∀ n →
    For-iterated-equality n Stable A → H-level (1 + n) A →
    For-iterated-equality n Very-stable A
  Stable→H-level-suc→Very-stable {A} n = curry (
    For-iterated-equality n Stable A × H-level (1 + n) A           ↝⟨ (∃-cong λ _ → H-level-suc→For-iterated-equality-Is-proposition) ⟩

    For-iterated-equality n Stable A ×
    For-iterated-equality n Is-proposition A                       ↝⟨ For-iterated-equality-commutes-× n _ ⟩

    For-iterated-equality n (λ A → Stable A × Is-proposition A) A  ↝⟨ For-iterated-equality-cong₁ _ n $
                                                                      uncurry Stable-proposition→Very-stable ⟩
    For-iterated-equality n Very-stable A                          □)

  -- If equality is decidable for A, then equality is very stable for
  -- A.

  Decidable-equality→Very-stable-≡ :
    {A : Type ℓ} →
    Decidable-equality A → Very-stable-≡ A
  Decidable-equality→Very-stable-≡ dec =
    Stable→H-level-suc→Very-stable
      1
      (λ x y → Dec→Stable (dec x y))
      (decidable⇒set dec)

  -- Types with h-level n are very stable "n levels up".

  H-level→Very-stable :
    {A : Type ℓ} →
    ∀ n → H-level n A → For-iterated-equality n Very-stable A
  H-level→Very-stable {A} n =
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

  -- Equality is stable for A if and only if [_]→ is injective for A.

  Stable-≡↔Injective-[] :
    {A : Type ℓ} →
    Stable-≡ A ↝[ ℓ ∣ ℓ ] Injective [ A ∣_]→
  Stable-≡↔Injective-[] ext =
    (∀ x y → Erased (x ≡ y) → x ≡ y)    ↝⟨ (∀-cong ext λ _ → from-isomorphism $ inverse Bijection.implicit-Π↔Π) ⟩
    (∀ x {y} → Erased (x ≡ y) → x ≡ y)  ↔⟨ inverse Bijection.implicit-Π↔Π ⟩
    (∀ {x y} → Erased (x ≡ y) → x ≡ y)  ↝⟨ (implicit-∀-cong ext $ implicit-∀-cong ext $
                                            Π-cong ext Erased-≡↔[]≡[] λ _ → F.id) ⟩□
    (∀ {x y} → [ x ] ≡ [ y ] → x ≡ y)   □

  -- Equality is very stable for A if and only if [_]→ is an embedding
  -- for A.

  Very-stable-≡↔Is-embedding-[] :
    {A : Type ℓ} →
    Very-stable-≡ A ↝[ ℓ ∣ ℓ ] Is-embedding [ A ∣_]→
  Very-stable-≡↔Is-embedding-[] ext =
    (∀ x y → Is-equivalence [ x ≡ y ∣_]→)                 ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                              Is-equivalence≃Is-equivalence-∘ˡ []-cong-equivalence ext) ⟩
    (∀ x y → Is-equivalence ([]-cong ∘ [ x ≡ y ∣_]→))     ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Is-equivalence-cong ext λ _ → []-cong-[]≡cong-[]) ⟩□
    (∀ x y → Is-equivalence (cong {x = x} {y = y} [_]→))  □

  private

    -- The previous result can be generalised.

    Very-stable-≡↔Is-embedding-[]→ :
      {A : Type ℓ} →
      ∀ n →
      For-iterated-equality (1 + n) Very-stable A ↝[ ℓ ∣ ℓ ]
      For-iterated-equality n (λ A → Is-embedding [ A ∣_]→) A
    Very-stable-≡↔Is-embedding-[]→ {A} n ext =
      For-iterated-equality (1 + n) Very-stable A              ↝⟨ inverse-ext? (For-iterated-equality-For-iterated-equality n 1) ext ⟩
      For-iterated-equality n Very-stable-≡ A                  ↝⟨ For-iterated-equality-cong₁ ext n (Very-stable-≡↔Is-embedding-[] ext) ⟩□
      For-iterated-equality n (λ A → Is-embedding [ A ∣_]→) A  □

  -- There is a logical equivalence between "equality for A is very
  -- stable with erased proofs" and "[_]→ for A is an embedding with
  -- erased proofs".

  Very-stableᴱ-≡⇔Is-embeddingᴱ-[] :
    {@0 A : Type ℓ} →
    Very-stableᴱ-≡ A ⇔ Is-embeddingᴱ [ A ∣_]→
  Very-stableᴱ-≡⇔Is-embeddingᴱ-[] =
    (∀ x y → Is-equivalenceᴱ [ x ≡ y ∣_]→)                 LE.⇔⟨ (LE.∀-cong λ _ → LE.∀-cong λ _ →
                                                                  EEq.Is-equivalenceᴱ⇔Is-equivalenceᴱ-∘ˡ
                                                                    (EEq.Is-equivalence→Is-equivalenceᴱ []-cong-equivalence)) ⟩
    (∀ x y → Is-equivalenceᴱ ([]-cong ∘ [ x ≡ y ∣_]→))     LE.⇔⟨ (LE.∀-cong λ _ → LE.∀-cong λ _ →
                                                                  EEq.Is-equivalenceᴱ-cong-⇔ λ _ →
                                                                  []-cong-[]≡cong-[]) ⟩□
    (∀ x y → Is-equivalenceᴱ (cong {x = x} {y = y} [_]→))  □

  -- There is an equivalence with erased proofs between "equality for
  -- A is very stable with erased proofs" and "[_]→ for A is an
  -- embedding with erased proofs" (assuming extensionality).

  Very-stableᴱ-≡≃ᴱIs-embeddingᴱ-[] :
    {@0 A : Type ℓ} →
    @0 Extensionality ℓ ℓ →
    Very-stableᴱ-≡ A ≃ᴱ Is-embeddingᴱ [ A ∣_]→
  Very-stableᴱ-≡≃ᴱIs-embeddingᴱ-[] ext =
    let record { to = to; from = from } =
          Very-stableᴱ-≡⇔Is-embeddingᴱ-[]
    in
    EEq.⇔→≃ᴱ
      (H-level-For-iterated-equality ext 1 1 λ {A} →
       Very-stableᴱ-propositional {A = A} ext)
      (EEmb.Is-embeddingᴱ-propositional ext)
      to
      from

  ----------------------------------------------------------------------
  -- Closure properties

  -- Very-stableᴱ is closed under Σ.

  Very-stableᴱ-Σ :
    {@0 A : Type ℓ} {@0 P : A → Type p} →
    Very-stableᴱ A →
    (∀ x → Very-stableᴱ (P x)) →
    Very-stableᴱ (Σ A P)
  Very-stableᴱ-Σ {A} {P} s s′ = _≃ᴱ_.is-equivalence (
    Σ A P                                       EEq.≃ᴱ⟨ EEq.[]-cong₁.Σ-cong-≃ᴱ-Erased ax EEq.⟨ _ , s ⟩₀ (λ x → EEq.⟨ _ , s′ x ⟩₀) ⟩
    Σ (Erased A) (λ x → Erased (P (erased x)))  EEq.↔⟨ inverse Erased-Σ↔Σ ⟩□
    Erased (Σ A P)                              □)

  -- A generalisation of Very-stableᴱ-Σ.

  Very-stableᴱ-Σⁿ :
    {A : Type ℓ} {P : A → Type p} →
    ∀ n →
    For-iterated-equality n Very-stableᴱ A →
    (∀ x → For-iterated-equality n Very-stableᴱ (P x)) →
    For-iterated-equality n Very-stableᴱ (Σ A P)
  Very-stableᴱ-Σⁿ n =
    For-iterated-equality-Σ
      n
      (≃ᴱ→Very-stableᴱ→Very-stableᴱ ∘ from-isomorphism)
      Very-stableᴱ-Σ

  ----------------------------------------------------------------------
  -- Closure properties related to equality

  -- If A is very stable, then equality is very stable for A.

  Very-stable→Very-stable-≡ :
    {A : Type ℓ} →
    ∀ n →
    For-iterated-equality n       Very-stable A →
    For-iterated-equality (1 + n) Very-stable A
  Very-stable→Very-stable-≡ {A} n =
    For-iterated-equality n Very-stable A        ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
    For-iterated-equality n Very-stable-≡ A      ↝⟨ For-iterated-equality-For-iterated-equality n 1 _ ⟩□
    For-iterated-equality (1 + n) Very-stable A  □
    where
    lemma : ∀ {A} → Very-stable A → Very-stable-≡ A
    lemma {A} =
      Very-stable A          ↝⟨ Very-stable→Is-embedding-[] ⟩
      Is-embedding [ A ∣_]→  ↝⟨ inverse-ext? Very-stable-≡↔Is-embedding-[] _ ⟩□
      Very-stable-≡ A        □

  private

    -- Some examples showing how Very-stable→Very-stable-≡ can be
    -- used.

    -- Equalities between erased values are very stable.

    Very-stable-≡₀ :
      {@0 A : Type ℓ} →
      Very-stable-≡ (Erased A)
    Very-stable-≡₀ = Very-stable→Very-stable-≡ 0 Very-stable-Erased

    -- Equalities between equalities between erased values are very
    -- stable.

    Very-stable-≡₁ :
      {@0 A : Type ℓ} →
      For-iterated-equality 2 Very-stable (Erased A)
    Very-stable-≡₁ = Very-stable→Very-stable-≡ 1 Very-stable-≡₀

    -- And so on…

  -- A generalisation of Very-stable→Very-stable-≡.

  Very-stable→Very-stable⁺ :
    {A : Type ℓ} →
    ∀ m →
    For-iterated-equality n Very-stable A →
    For-iterated-equality (m + n) Very-stable A
  Very-stable→Very-stable⁺     zero    = id
  Very-stable→Very-stable⁺ {n} (suc m) =
    Very-stable→Very-stable-≡ (m + n) ∘
    Very-stable→Very-stable⁺ m

  -- A variant of Very-stable→Very-stable-≡.

  Very-stable→Very-stableⁿ :
    {A : Type ℓ} →
    ∀ n →
    Very-stable A →
    For-iterated-equality n Very-stable A
  Very-stable→Very-stableⁿ n =
    subst (λ n → For-iterated-equality n Very-stable _)
      (Nat.+-right-identity {n = n}) ∘
      Very-stable→Very-stable⁺ n

  -- A generalisation of Stable-H-level′.

  Stable-[]-H-level′ :
    {A : Type ℓ} →
    Extensionality? k ℓ ℓ →
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    Stable-[ k ] (H-level′ (1 + n) A)
  Stable-[]-H-level′ {k} {A} ext n =
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
    {A : Type ℓ} →
    Extensionality? k ℓ ℓ →
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    Stable-[ k ] (H-level (1 + n) A)
  Stable-[]-H-level {k} {A} ext n =
    For-iterated-equality (1 + n) Stable-[ k ] A  ↝⟨ Stable-[]-H-level′ ext n ⟩
    Stable-[ k ] (H-level′ (1 + n) A)             ↝⟨ Stable-[]-map-↝ (inverse-ext? H-level↔H-level′) ext ⟩□
    Stable-[ k ] (H-level (1 + n) A)              □

  -- If A is "very stable n levels up", then H-level′ n A is very
  -- stable (assuming extensionality).

  Very-stable-H-level′ :
    {A : Type ℓ} →
    Extensionality ℓ ℓ →
    ∀ n →
    For-iterated-equality n Very-stable A →
    Very-stable (H-level′ n A)
  Very-stable-H-level′ {A} ext n =
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
    {@0 A : Type ℓ} →
    @0 Extensionality ℓ ℓ →
    ∀ n →
    For-iterated-equality n Very-stableᴱ A →
    Very-stableᴱ (For-iterated-equality n Contractibleᴱ A)
  Very-stableᴱ-H-levelᴱ {A} ext n =
    For-iterated-equality n Very-stableᴱ A                    →⟨ For-iterated-equality-cong₁ᴱ-→ n lemma ⟩
    For-iterated-equality n (Very-stableᴱ ∘ Contractibleᴱ) A  →⟨ For-iterated-equality-commutesᴱ-← Very-stableᴱ n (Very-stableᴱ-Π ext) ⟩□
    Very-stableᴱ (For-iterated-equality n Contractibleᴱ A)    □
    where
    lemma : ∀ {@0 A} → Very-stableᴱ A → Very-stableᴱ (Contractibleᴱ A)
    lemma s =
      Very-stableᴱ-Σ s λ _ →
      Very-stable→Very-stableᴱ 0
      Very-stable-Erased

  -- If A is "very stable n levels up", then H-level n A is very
  -- stable (assuming extensionality).

  Very-stable-H-level :
    {A : Type ℓ} →
    Extensionality ℓ ℓ →
    ∀ n →
    For-iterated-equality n Very-stable A →
    Very-stable (H-level n A)
  Very-stable-H-level {A} ext n =
    For-iterated-equality n Very-stable A  ↝⟨ Very-stable-H-level′ ext n ⟩
    Very-stable (H-level′ n A)             ↝⟨ Very-stable-cong _ (inverse $ H-level↔H-level′ ext) ⟩□
    Very-stable (H-level n A)              □

  -- There is an equivalence between Very-stable (Very-stable A) and
  -- Very-stable A (assuming extensionality).

  Very-stable-Very-stable≃Very-stable :
    {A : Type ℓ} →
    Extensionality ℓ ℓ →
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
    {@0 A : Type ℓ} →
    @0 Extensionality ℓ ℓ →
    Very-stableᴱ (Very-stableᴱ A) ≃ᴱ Very-stableᴱ A
  Very-stableᴱ-Very-stableᴱ≃ᴱVery-stableᴱ ext =
    EEq.⇔→≃ᴱ
      (Very-stableᴱ-propositional ext)
      (Very-stableᴱ-propositional ext)
      Very-stableᴱ-Very-stableᴱ→Very-stableᴱ
      (λ s →
         ≃ᴱ→Very-stableᴱ→Very-stableᴱ
           (EEq.inverse $ EEq.Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext) $
         Very-stableᴱ-Π ext λ _ →
         Very-stableᴱ-H-levelᴱ ext 0 $
         Very-stableᴱ-Σ s λ _ →
         Very-stable→Very-stableᴱ 0 $
         Very-stable-Erased)

  -- A generalisation of Stable-≡-List.

  Stable-[]-≡-List :
    {A : Type ℓ} →
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
    {A : Type ℓ} →
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

  ----------------------------------------------------------------------
  -- The function λ A → Erased A, [_]→ and Very-stable form a modality

  -- As a consequence of Very-stable→Very-stable-≡ we get that every
  -- family of very stable types, indexed by Erased A, is ∞-extendable
  -- along [_]→.

  extendable :
    {@0 A : Type a} {P : Erased A → Type ℓ} →
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
  -- (one version of) the Coq code accompanying "Modalities in
  -- Homotopy Type Theory" by Rijke, Shulman and Spitters.

  const-extendable :
    {@0 A : Type a} {B : Type ℓ} →
    Very-stable B →
    Is-∞-extendable-along-[ [_]→ ] (λ (_ : Erased A) → B)
  const-extendable s = extendable (λ _ → s)

  -- The function λ A → Erased A, [_]→ and Very-stable form a Σ-closed
  -- reflective subuniverse.

  Erased-Σ-closed-reflective-subuniverse :
    Σ-closed-reflective-subuniverse ℓ
  Erased-Σ-closed-reflective-subuniverse = λ where
      .◯                   → λ A → Erased A
      .η                   → [_]→
      .Modal               → Very-stable
      .Modal-propositional → Very-stable-propositional
      .Modal-◯             → Very-stable-Erased
      .Modal-respects-≃    → Very-stable-cong _
      .extendable-along-η  → const-extendable
      .Σ-closed            → Very-stable-Σ
    where
    open Σ-closed-reflective-subuniverse

  -- The function λ A → Erased A, [_]→ and Very-stable form a
  -- modality.

  Erased-modality : Modality ℓ
  Erased-modality = λ where
      .◯            → λ A → Erased A
      .η            → [_]→
      .modality-for → λ where
        .Modal               → Very-stable
        .Modal-propositional → Very-stable-propositional
        .Modal-◯             → Very-stable-Erased
        .Modal-respects-≃    → Very-stable-cong _
        .extendable-along-η  → extendable
    where
    open Modality
    open Modality-for

  -- The modality is empty-modal.

  Erased-empty-modal : Empty-modal Erased-modality
  Erased-empty-modal = Very-stable-⊥

  -- The modality is very modal.

  Erased-very-modal : Very-modal Erased-modality
  Erased-very-modal = Erased-Very-stable

  -- The modality is topological in erased contexts.

  @0 Erased-topological-in-erased-contexts :
    Topological Erased-modality
  Erased-topological-in-erased-contexts =
    let I , P , prop , p =
          erased-is-accessible-and-topological-in-erased-contexts′
    in (I , P , p) , prop

  ----------------------------------------------------------------------
  -- Some properties that rely on excluded middle

  module Excluded-middle (em : Excluded-middle ℓ) where

    -- Every type of type Type ℓ is very stable (assuming
    -- extensionality).

    very-stable :
      {A : Type ℓ} →
      Extensionality ℓ ℓ →
      Very-stable A
    very-stable ext =
      EM.Empty-modal.Excluded-middle.Very-modal.modal
        Erased-modality
        Erased-empty-modal
        em
        Erased-very-modal
        ext

    -- The modality is equal to the identity modality (assuming
    -- extensionality and univalence).

    Erased≡Identity-modality :
      Extensionality (lsuc ℓ) (lsuc ℓ) →
      Univalence ℓ →
      Erased-modality ≡ Identity-modality
    Erased≡Identity-modality ext univ =
      EM.Empty-modal.Excluded-middle.Very-modal.≡Identity-modality
        Erased-modality
        Erased-empty-modal
        em
        Erased-very-modal
        ext univ

    -- The modality is topological (assuming extensionality).

    Erased-topological :
      Extensionality ℓ ℓ →
      Topological Erased-modality
    Erased-topological ext =
      EM.Empty-modal.Excluded-middle.Very-modal.topological
        Erased-modality
        Erased-empty-modal
        em
        Erased-very-modal
        ext

    -- The modality is cotopological.

    Erased-cotopological : Cotopological (λ (A : Type ℓ) → Erased A)
    Erased-cotopological =
      EM.Empty-modal.Excluded-middle.Left-exact→Cotopological
        Erased-modality
        Erased-empty-modal
        em
        lex-modality

  ----------------------------------------------------------------------
  -- Erased singletons

  -- The type of triples consisting of two values of type A, one erased,
  -- and an erased proof of equality of the two values is isomorphic to
  -- A.

  Σ-Erased-Erased-singleton↔ :
    {A : Type ℓ} →
    (∃ λ (x : Erased A) → Erased-singleton (erased x)) ↔ A
  Σ-Erased-Erased-singleton↔ {A} =
    (∃ λ (x : Erased A) → ∃ λ y → Erased (y ≡ erased x))  ↝⟨ ∃-comm ⟩
    (∃ λ y → ∃ λ (x : Erased A) → Erased (y ≡ erased x))  ↝⟨ (∃-cong λ _ → inverse Erased-Σ↔Σ) ⟩
    (∃ λ y → Erased (∃ λ (x : A) → y ≡ x))                ↝⟨ (∃-cong λ _ →
                                                              Erased-cong.Erased-cong-↔ ax (lower-[]-cong-axiomatisation _ ax)
                                                                (_⇔_.to contractible⇔↔⊤ (other-singleton-contractible _))) ⟩
    A × Erased ⊤                                          ↝⟨ drop-⊤-right (λ _ → Erased-⊤↔⊤) ⟩□
    A                                                     □

  -- The logical equivalence underlying
  -- Σ-Erased-Erased-singleton↔ {A = A} is definitionally equal to
  -- Σ-Erased-Erased-singleton⇔.

  _ :
    _↔_.logical-equivalence (Σ-Erased-Erased-singleton↔ {A = A}) ≡
    Σ-Erased-Erased-singleton⇔
  _ = refl _

  -- A variant of erased-singleton-contractible.

  Very-stableᴱ-≡→Contractible-Erased-singleton :
    {A : Type ℓ} {x : A} →
    Very-stableᴱ-≡ A →
    Contractible (Erased-singleton x)
  Very-stableᴱ-≡→Contractible-Erased-singleton {x} s =
      (x , [ refl x ])
    , λ (y , [ y≡x ]) →
        Σ-≡,≡→≡
          (_≃ᴱ_.from EEq.⟨ _ , s _ _ ⟩₀ [ sym y≡x ])
          (subst (λ y → Erased (y ≡ x))
             (_≃ᴱ_.from EEq.⟨ _ , s _ _ ⟩₀ [ sym y≡x ])
             [ refl x ]                                          ≡⟨ push-subst-[] ⟩

           [ subst (_≡ x)
               (_≃ᴱ_.from EEq.⟨ _ , s _ _ ⟩₀ [ sym y≡x ])
               (refl x)
           ]                                                     ≡⟨ []-cong [ cong (flip (subst _) _) $
                                                                    _≃ᴱ_.left-inverse-of EEq.⟨ _ , s _ _ ⟩₀ _ ] ⟩

           [ subst (_≡ x) (sym y≡x) (refl x) ]                   ≡⟨ []-cong [ subst-trans _ ] ⟩

           [ trans y≡x (refl x) ]                                ≡⟨ []-cong [ trans-reflʳ _ ] ⟩∎

           [ y≡x ]                                               ∎)

  -- If equality is very stable (with erased proofs) for A, and x : A
  -- is erased, then Erased-singleton x is a proposition.

  erased-singleton-with-erased-center-propositional :
    {A : Type ℓ} {@0 x : A} →
    Very-stableᴱ-≡ A →
    Is-proposition (Erased-singleton x)
  erased-singleton-with-erased-center-propositional {x} s =
                                                   $⟨ [ erased-singleton-contractible (λ _ _ → erased Erased-Very-stable) ] ⟩
    Erased (Contractible (Erased-singleton x))     ↝⟨ map (mono₁ 0) ⟩
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
    {A : Type ℓ} {@0 x : A} →
    Very-stable A →
    Contractible (Erased-singleton x)
  erased-singleton-with-erased-center-contractible {x} s =
                                       $⟨ [ (x , [ refl _ ]) ] ⟩
    Erased (Erased-singleton x)        ↝⟨ Very-stable→Stable 0 (Very-stable-Σ s λ _ → Very-stable-Erased) ⟩
    Erased-singleton x                 ↝⟨ propositional⇒inhabited⇒contractible $
                                          erased-singleton-with-erased-center-propositional $
                                          Very-stable→Very-stableᴱ 1 $
                                          Very-stable→Very-stable-≡ 0 s ⟩□
    Contractible (Erased-singleton x)  □

------------------------------------------------------------------------
-- Results that depend on an axiomatisation of []-cong (for the
-- successor of a universe level)

module []-cong₁-lsuc (ax : []-cong-axiomatisation (lsuc ℓ)) where

  open []-cong₁ ax

  -- ∃ λ (A : Set a) → Very-stable A is very stable, assuming
  -- extensionality and univalence.
  --
  -- This result is based on Theorem 3.11 in "Modalities in Homotopy
  -- Type Theory" by Rijke, Shulman and Spitters.

  Very-stable-∃-Very-stable :
    Extensionality ℓ ℓ →
    Univalence ℓ →
    Very-stable (∃ λ (A : Type ℓ) → Very-stable A)
  Very-stable-∃-Very-stable ext univ =
    Stable→Left-inverse→Very-stable Stable-∃-Very-stable inv
    where
    inv : ∀ p → Stable-∃-Very-stable [ p ] ≡ p
    inv (A , s) = Σ-≡,≡→≡
      (Erased A  ≡⟨ ≃⇒≡ univ (Very-stable→Stable 0 s) ⟩∎
       A         ∎)
      (Very-stable-propositional ext _ _)

------------------------------------------------------------------------
-- More results that depend on an instantiation of the []-cong axioms
-- (for two universe levels as well as their maximum)

module []-cong₂-⊔₂
  (ax₁ : []-cong-axiomatisation ℓ₁)
  (ax₂ : []-cong-axiomatisation ℓ₂)
  (ax  : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
  where

  ----------------------------------------------------------------------
  -- A lemma related to Stable-[_]

  -- Stable-[ k ] is closed under _⇔_ (assuming extensionality).

  Stable-[]-⇔ :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Stable-[ k ] A → Stable-[ k ] B → Stable-[ k ] (A ⇔ B)
  Stable-[]-⇔ {k} {A} {B} ext s s′ =             $⟨ (Stable-[]-Π (lower-extensionality? k ℓ₂ ℓ₁ ext) λ _ → s′)
                                                  , (Stable-[]-Π (lower-extensionality? k ℓ₁ ℓ₂ ext) λ _ → s) ⟩
    Stable-[ k ] (A → B) × Stable-[ k ] (B → A)  →⟨ uncurry Stable-[]-× ⟩
    Stable-[ k ] ((A → B) × (B → A))             →⟨ []-cong₂-⊔₁.Stable-[]-map-↔ ax ax ax (inverse ⇔↔→×→) ⟩□
    Stable-[ k ] (A ⇔ B)                         □

  ----------------------------------------------------------------------
  -- Some lemmas related to Very-stable

  -- Very-stable is closed under _↝[ k ]_ (assuming extensionality).

  Very-stable-↝ :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Very-stable A → Very-stable B → Very-stable (A ↝[ k ] B)
  Very-stable-↝ {k} {A} {B} ext sA sB = lemma k
    where
    ext₁₁ : Extensionality ℓ₁ ℓ₁
    ext₁₁ = lower-extensionality ℓ₂ ℓ₂ ext

    ext₁₂ : Extensionality ℓ₁ ℓ₂
    ext₁₂ = lower-extensionality ℓ₂ ℓ₁ ext

    ext₁₁₂ : Extensionality ℓ₁ (ℓ₁ ⊔ ℓ₂)
    ext₁₁₂ = lower-extensionality ℓ₂ lzero ext

    ext₂₁ : Extensionality ℓ₂ ℓ₁
    ext₂₁ = lower-extensionality ℓ₁ ℓ₂ ext

    ext₂₁₂ : Extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂)
    ext₂₁₂ = lower-extensionality ℓ₁ lzero ext

    ext₂₂ : Extensionality ℓ₂ ℓ₂
    ext₂₂ = lower-extensionality ℓ₁ ℓ₁ ext

    Very-stable-map :
      {A B : Type (ℓ₁ ⊔ ℓ₂)} →
      B ↔ A → Very-stable A → Very-stable B
    Very-stable-map =
      []-cong₂.Very-stable-cong ax ax _ ∘ from-bijection ∘ inverse

    sA→B : Very-stable (A → B)
    sA→B = Very-stable-Π ext₁₂ (λ _ → sB)

    sB→A : Very-stable (B → A)
    sB→A = Very-stable-Π ext₂₁ (λ _ → sA)

    s≡A : ∀ n → For-iterated-equality n Very-stable A
    s≡A n = []-cong₁.Very-stable→Very-stableⁿ ax₁ n sA

    s≡B : ∀ n → For-iterated-equality n Very-stable B
    s≡B n = []-cong₁.Very-stable→Very-stableⁿ ax₂ n sB

    lemma : ∀ k → Very-stable (A ↝[ k ] B)
    lemma implication         = sA→B
    lemma logical-equivalence =        $⟨ Very-stable-× sA→B sB→A ⟩
      Very-stable ((A → B) × (B → A))  →⟨ Very-stable-map ⇔↔→×→ ⟩□
      Very-stable (A ⇔ B)              □
    lemma injection =                                            $⟨ (Very-stable-Σ sA→B λ _ →
                                                                     Very-stable-Π ext₁₁₂ λ _ →
                                                                     Very-stable-Π ext₁₁₂ λ _ →
                                                                     Very-stable-Π ext₂₁ λ _ → s≡A 1 _ _) ⟩
      Very-stable (∃ λ (f : A → B) → ∀ x y → f x ≡ f y → x ≡ y)  →⟨ (Very-stable-map $
                                                                     ∃-cong λ _ →
                                                                     (∀-cong ext₁₁₂ λ _ → Bijection.implicit-Π↔Π) F.∘
                                                                     Bijection.implicit-Π↔Π) ⟩
      Very-stable (∃ λ (f : A → B) → Injective f)                →⟨ Very-stable-map ↣↔∃-Injective ⟩□
      Very-stable (A ↣ B)                                        □
    lemma embedding =                                 $⟨ (Very-stable-Σ sA→B λ _ →
                                                          Very-stable-Π ext₁₁₂ λ _ →
                                                          Very-stable-Π ext₁₁₂ λ _ →
                                                          Very-stable-Σ (Very-stable-Π ext₂₁ λ _ → s≡A 1 _ _) λ _ →
                                                          Very-stable-Σ (Very-stable-Π ext₂₂ λ _ → s≡B 2 _ _ _ _) λ _ →
                                                          Very-stable-Σ (Very-stable-Π ext₁₁ λ _ → s≡A 2 _ _ _ _) λ _ →
                                                          Very-stable-Π ext₁₂ λ _ → s≡B 3 _ _ _ _ _ _) ⟩
      Very-stable (∃ λ (f : A → B) → Is-embedding f)  →⟨ Very-stable-map Emb.Embedding-as-Σ ⟩□
      Very-stable (Embedding A B)                     □
    lemma surjection =                                    $⟨ (Very-stable-Σ sA→B λ _ →
                                                              Very-stable-Π ext₂₁₂ λ _ →
                                                              Very-stable-Σ sA λ _ → s≡B 1 _ _) ⟩
      Very-stable (∃ λ (f : A → B) → Split-surjective f)  →⟨ Very-stable-map ↠↔∃-Split-surjective ⟩□
      Very-stable (A ↠ B)                                 □
    lemma bijection =                                      $⟨ (Very-stable-Σ sA→B λ _ →
                                                               Very-stable-Σ sB→A λ _ →
                                                               Very-stable-×
                                                                 (Very-stable-Π ext₂₂ λ _ → s≡B 1 _ _)
                                                                 (Very-stable-Π ext₁₁ λ _ → s≡A 1 _ _)) ⟩
      Very-stable (∃ λ (f : A → B) → Has-quasi-inverse f)  →⟨ Very-stable-map Bijection.↔-as-Σ ⟩□
      Very-stable (A ↔ B)                                  □
    lemma equivalence =                                 $⟨ (Very-stable-Σ sA→B λ _ →
                                                            Very-stable-Σ sB→A λ _ →
                                                            Very-stable-Σ (Very-stable-Π ext₂₂ λ _ → s≡B 1 _ _) λ _ →
                                                            Very-stable-Σ (Very-stable-Π ext₁₁ λ _ → s≡A 1 _ _) λ _ →
                                                            Very-stable-Π ext₁₂ λ _ → s≡B 2 _ _ _ _) ⟩
      Very-stable (∃ λ (f : A → B) → Is-equivalence f)  →⟨ Very-stable-map Eq.≃-as-Σ ⟩□
      Very-stable (A ≃ B)                               □
    lemma equivalenceᴱ =                                 $⟨ (Very-stable-Σ sA→B λ _ →
                                                             Very-stable-Σ sB→A λ _ →
                                                             Very-stable-Erased) ⟩
      Very-stable (∃ λ (f : A → B) → Is-equivalenceᴱ f)  →⟨ Very-stable-map (from-equivalence EEq.≃ᴱ-as-Σ) ⟩□
      Very-stable (A ≃ᴱ B)                               □

  -- All kinds of functions between erased types are very stable (in
  -- some cases assuming extensionality).

  Very-stable-Erased↝Erased :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
    Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Very-stable (Erased A ↝[ k ] Erased B)
  Very-stable-Erased↝Erased {k} {A} {B} ext =
                                            $⟨ Very-stable-Erased ⟩
    Very-stable (Erased (A ↝[ k ] B))       ↝⟨ []-cong₂.Very-stable-cong ax ax _ (from-isomorphism $ E₂.[]-cong₂-⊔.Erased-↝↔↝ ax₁ ax₂ ax ext)
                                                 ⦂ (_ → _) ⟩□
    Very-stable (Erased A ↝[ k ] Erased B)  □

  -- A generalisation of Very-stable-Σ.
  --
  -- Based on a lemma called inO_unsigma, implemented by Mike Shulman
  -- in the file ReflectiveSubuniverse.v in (one version of) the Coq
  -- HoTT library.

  Very-stable-Σ↔Π :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    Very-stable A →
    Very-stable (Σ A P) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ] (∀ x → Very-stable (P x))
  Very-stable-Σ↔Π {A} {P} s =
    generalise-ext?-prop
      (record
         { from = Very-stable-Σ s
         ; to   = flip λ x →
             Very-stable (Σ A P)                          ↝⟨ flip Very-stable-Σ (λ _ → []-cong₁.Very-stable→Very-stable-≡ ax₁ 0 s _ _) ⟩
             Very-stable (∃ λ ((y , _) : Σ A P) → y ≡ x)  ↝⟨ []-cong₂.Very-stable-cong ax ax  _ $ from-bijection $ inverse Σ-assoc ⟩
             Very-stable (∃ λ (y : A) → P y × y ≡ x)      ↝⟨ []-cong₂.Very-stable-cong ax ax₂ _ $ from-bijection $ inverse $ ∃-intro _ _ ⟩□
             Very-stable (P x)                            □
         })
      Very-stable-propositional
      (λ ext →
         Π-closure (lower-extensionality ℓ₂ ℓ₁ ext) 1 λ _ →
         Very-stable-propositional (lower-extensionality ℓ₁ ℓ₁ ext))

  -- A variant of Very-stableᴱ-Σ.
  --
  -- Based on a lemma called inO_unsigma, implemented by Mike Shulman
  -- in the file ReflectiveSubuniverse.v in (one version of) the Coq
  -- HoTT library.

  Very-stableᴱ-Σ≃ᴱΠ :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    @0 Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Very-stableᴱ A →
    Very-stableᴱ-≡ A →
    Very-stableᴱ (Σ A P) ≃ᴱ (∀ x → Very-stableᴱ (P x))
  Very-stableᴱ-Σ≃ᴱΠ {A} {P} ext s s-≡ =
    EEq.⇔→≃ᴱ
      (Very-stableᴱ-propositional ext)
      (Π-closure (lower-extensionality ℓ₂ ℓ₁ ext) 1 λ _ →
       Very-stableᴱ-propositional (lower-extensionality ℓ₁ ℓ₁ ext))
      (flip λ x →
       Very-stableᴱ (Σ A P)                          ↝⟨ flip ([]-cong₁.Very-stableᴱ-Σ ax) (λ _ → s-≡ _ _) ⟩
       Very-stableᴱ (∃ λ ((y , _) : Σ A P) → y ≡ x)  ↝⟨ ≃ᴱ→Very-stableᴱ→Very-stableᴱ $ from-bijection $ inverse Σ-assoc ⟩
       Very-stableᴱ (∃ λ (y : A) → P y × y ≡ x)      ↝⟨ ≃ᴱ→Very-stableᴱ→Very-stableᴱ $ from-bijection $ inverse $ ∃-intro _ _ ⟩□
       Very-stableᴱ (P x)                            □)
      ([]-cong₁.Very-stableᴱ-Σ ax₁ s)

  ----------------------------------------------------------------------
  -- Closure properties related to equality

  -- A generalisation of Stable-≡-⊎.

  Stable-[]-≡-⊎ :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    For-iterated-equality (1 + n) Stable-[ k ] B →
    For-iterated-equality (1 + n) Stable-[ k ] (A ⊎ B)
  Stable-[]-≡-⊎ n sA sB =
    For-iterated-equality-⊎-suc
      n
      ([]-cong₂-⊔₁.Stable-[]-map-↔ ax ax ax)
      (Very-stable→Stable 0 Very-stable-⊥)
      (For-iterated-equality-↑ _ (1 + n)
         ([]-cong₂-⊔₁.Stable-[]-map-↔ ax ax₁ ax) sA)
      (For-iterated-equality-↑ _ (1 + n)
         ([]-cong₂-⊔₁.Stable-[]-map-↔ ax ax₂ ax) sB)

  -- If equality is very stable for A and B, then it is very stable
  -- for A ⊎ B.

  Very-stable-≡-⊎ :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    ∀ n →
    For-iterated-equality (1 + n) Very-stable A →
    For-iterated-equality (1 + n) Very-stable B →
    For-iterated-equality (1 + n) Very-stable (A ⊎ B)
  Very-stable-≡-⊎ n sA sB =
    For-iterated-equality-⊎-suc
      n
      (lemma ax ax)
      Very-stable-⊥
      (For-iterated-equality-↑ _ (1 + n) (lemma ax₁ ax) sA)
      (For-iterated-equality-↑ _ (1 + n) (lemma ax₂ ax) sB)
    where
    lemma :
      ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} →
      []-cong-axiomatisation ℓ₁ →
      []-cong-axiomatisation ℓ₂ →
      A ↔ B → Very-stable A → Very-stable B
    lemma ax₁ ax₂ =
      []-cong₂.Very-stable-cong ax₁ ax₂ _ ∘
      from-isomorphism

  ----------------------------------------------------------------------
  -- Simple corollaries or variants of results above

  -- A generalisation of Stable-Π.

  Stable-Πⁿ :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    Extensionality ℓ₁ ℓ₂ →
    ∀ n →
    (∀ x → For-iterated-equality n Stable-[ k ] (P x)) →
    For-iterated-equality n Stable-[ k ] ((x : A) → P x)
  Stable-Πⁿ {k} ext n =
    For-iterated-equality-Π
      ext
      n
      ([]-cong₂-⊔₁.Stable-[]-map-↔ ax ax ax)
      (Stable-[]-Π (forget-ext? k ext))

  -- A generalisation of Very-stable-Π.

  Very-stable-Πⁿ :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    Extensionality ℓ₁ ℓ₂ →
    ∀ n →
    (∀ x → For-iterated-equality n Very-stable (P x)) →
    For-iterated-equality n Very-stable ((x : A) → P x)
  Very-stable-Πⁿ ext n =
    For-iterated-equality-Π
      ext
      n
      ([]-cong₂.Very-stable-cong ax ax _ ∘ from-isomorphism)
      (Very-stable-Π ext)

  -- A generalisation of Very-stable-Stable-Σ.

  Very-stable-Stable-Σⁿ :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    ∀ n →
    For-iterated-equality n Very-stable A →
    (∀ x → For-iterated-equality n Stable-[ k ] (P x)) →
    For-iterated-equality n Stable-[ k ] (Σ A P)
  Very-stable-Stable-Σⁿ {k} n =
    For-iterated-equality-Σ
      n
      ([]-cong₂-⊔₁.Stable-[]-map-↔ ax ax ax)
      Very-stable-Stable-Σ

  -- A variant of Stable-Σ for equality.

  Stable-≡-Σ :
    {A : Type ℓ₁} {P : A → Type ℓ₂} {p q : Σ A P} →
    (s : Stable (proj₁ p ≡ proj₁ q)) →
    (∀ eq → [ s eq ] ≡ eq) →
    (∀ eq → Stable (subst P eq (proj₂ p) ≡ proj₂ q)) →
    Stable (p ≡ q)
  Stable-≡-Σ {P} {p} {q} s₁ hyp s₂ =              $⟨ Stable-Σ s₁ hyp s₂ ⟩

    Stable (∃ λ (eq : proj₁ p ≡ proj₁ q) →
                subst P eq (proj₂ p) ≡ proj₂ q)   ↝⟨ []-cong₂-⊔₁.Stable-[]-map-↔ ax ax ax Bijection.Σ-≡,≡↔≡ ⟩□

    Stable (p ≡ q)                                □

  -- A generalisation of Very-stable-Σ.

  Very-stable-Σⁿ :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    ∀ n →
    For-iterated-equality n Very-stable A →
    (∀ x → For-iterated-equality n Very-stable (P x)) →
    For-iterated-equality n Very-stable (Σ A P)
  Very-stable-Σⁿ n =
    For-iterated-equality-Σ
      n
      ([]-cong₂.Very-stable-cong ax ax _ ∘ from-isomorphism)
      Very-stable-Σ

  -- A generalisation of Stable-[]-×.

  Stable-[]-×ⁿ :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    ∀ n →
    For-iterated-equality n Stable-[ k ] A →
    For-iterated-equality n Stable-[ k ] B →
    For-iterated-equality n Stable-[ k ] (A × B)
  Stable-[]-×ⁿ n =
    For-iterated-equality-×
      n
      ([]-cong₂-⊔₁.Stable-[]-map-↔ ax ax ax)
      Stable-[]-×

  -- A generalisation of Very-stable-×.

  Very-stable-×ⁿ :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    ∀ n →
    For-iterated-equality n Very-stable A →
    For-iterated-equality n Very-stable B →
    For-iterated-equality n Very-stable (A × B)
  Very-stable-×ⁿ n =
    For-iterated-equality-×
      n
      ([]-cong₂.Very-stable-cong ax ax _ ∘ from-isomorphism)
      Very-stable-×

  -- A generalisation of Stable-↑.

  Stable-↑ⁿ :
    {A : Type ℓ₂} →
    ∀ n →
    For-iterated-equality n Stable-[ k ] A →
    For-iterated-equality n Stable-[ k ] (↑ ℓ₁ A)
  Stable-↑ⁿ n =
    For-iterated-equality-↑ _ n
      ([]-cong₂-⊔₁.Stable-[]-map-↔ ax ax₂ ax)

  -- A generalisation of Very-stable-↑.

  Very-stable-↑ⁿ :
    {A : Type ℓ₂} →
    ∀ n →
    For-iterated-equality n Very-stable A →
    For-iterated-equality n Very-stable (↑ ℓ₁ A)
  Very-stable-↑ⁿ n =
    For-iterated-equality-↑
      _
      n
      ([]-cong₂.Very-stable-cong ax₂ ax _ ∘ from-isomorphism)

------------------------------------------------------------------------
-- Results that depend on instances of the axiomatisation of []-cong
-- for all universe levels

module []-cong (ax : ∀ {ℓ} → []-cong-axiomatisation ℓ) where

  private
    open module BC₂ {ℓ₁ ℓ₂} =
      []-cong₂ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂})
      public
    open module BC₂₁ {ℓ₁ ℓ₂} =
      []-cong₂-⊔₁ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) ax
      public
    open module BC₁ {ℓ} = []-cong₁ (ax {ℓ = ℓ})
      public
    open module BC₁-lsuc {ℓ} = []-cong₁-lsuc (ax {ℓ = lsuc ℓ})
      public
    open module BC₂₂ {ℓ₁ ℓ₂} =
      []-cong₂-⊔₂ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) ax
      public

------------------------------------------------------------------------
-- Some results that were proved assuming extensionality and also that
-- one or more instances of the []-cong axioms can be implemented,
-- reproved without the latter assumptions

module Extensionality where

  -- If A is "very stable n levels up", then H-level′ n A is very
  -- stable (assuming extensionality).

  Very-stable-H-level′ :
    {A : Type a} →
    Extensionality a a →
    ∀ n →
    For-iterated-equality n Very-stable A →
    Very-stable (H-level′ n A)
  Very-stable-H-level′ ext =
    []-cong₁.Very-stable-H-level′
      (Extensionality→[]-cong-axiomatisation ext) ext

  -- If A is "very stable n levels up", then H-level n A is very
  -- stable (assuming extensionality).

  Very-stable-H-level :
    {A : Type a} →
    Extensionality a a →
    ∀ n →
    For-iterated-equality n Very-stable A →
    Very-stable (H-level n A)
  Very-stable-H-level ext =
    []-cong₁.Very-stable-H-level
      (Extensionality→[]-cong-axiomatisation ext) ext

  -- There is an equivalence between Very-stable (Very-stable A) and
  -- Very-stable A (assuming extensionality).

  Very-stable-Very-stable≃Very-stable :
    {A : Type a} →
    Extensionality a a →
    Very-stable (Very-stable A) ≃ Very-stable A
  Very-stable-Very-stable≃Very-stable ext =
    []-cong₁.Very-stable-Very-stable≃Very-stable
      (Extensionality→[]-cong-axiomatisation ext) ext

  -- The function λ A → Erased A, [_]→ and Very-stable form a modality
  -- (assuming extensionality).

  Erased-modality :
    Extensionality ℓ ℓ →
    Modality ℓ
  Erased-modality ext =
    []-cong₁.Erased-modality
      (Extensionality→[]-cong-axiomatisation ext)

  ----------------------------------------------------------------------
  -- Some properties that rely on excluded middle

  module Excluded-middle (em : Excluded-middle ℓ) where

    -- Every type of type Type ℓ is very stable (assuming
    -- extensionality).

    very-stable :
      {A : Type ℓ} →
      Extensionality ℓ ℓ →
      Very-stable A
    very-stable ext =
      []-cong₁.Excluded-middle.very-stable
        (Extensionality→[]-cong-axiomatisation ext)
        em ext

    -- The modality is equal to the identity modality (assuming
    -- extensionality and univalence).

    Erased≡Identity-modality :
      Extensionality (lsuc ℓ) (lsuc ℓ) →
      (ext : Extensionality ℓ ℓ) →
      Univalence ℓ →
      Erased-modality ext ≡ Identity-modality
    Erased≡Identity-modality ext′ ext univ =
      []-cong₁.Excluded-middle.Erased≡Identity-modality
        (Extensionality→[]-cong-axiomatisation ext)
        em ext′ univ

    -- The modality is topological (assuming extensionality).

    Erased-topological :
      (ext : Extensionality ℓ ℓ) →
      Topological (Erased-modality {ℓ = ℓ} ext)
    Erased-topological ext =
      []-cong₁.Excluded-middle.Erased-topological
        (Extensionality→[]-cong-axiomatisation ext)
        em ext

------------------------------------------------------------------------
-- Some lemmas related to Stable-≡-Erased-axiomatisation

private

  -- The type []-cong-axiomatisation ℓ is logically equivalent to
  -- Stable-≡-Erased-axiomatisation ℓ.

  []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation :
    []-cong-axiomatisation ℓ ⇔ Stable-≡-Erased-axiomatisation ℓ
  []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation {ℓ} = record
    { to   = λ ax →
               let open []-cong₁ ax
                   s : {@0 A : Type ℓ} → Very-stable-≡ (Erased A)
                   s = Very-stable→Very-stable-≡ 0 Very-stable-Erased
               in
                 Very-stable→Stable 1 s
               , (λ {_ x} →
                    Very-stable→Stable 1 s x x [ refl x ]  ≡⟨ _≃_.left-inverse-of Eq.⟨ _ , s x x ⟩ _ ⟩∎
                    refl x                                 ∎)
    ; from = S→B.instance-of-[]-cong-axiomatisation
    }
    where
    module S→B = Stable-≡-Erased-axiomatisation→[]-cong-axiomatisation

-- The type Stable-≡-Erased-axiomatisation ℓ is propositional
-- (assuming extensionality).
--
-- The proof is based on a proof due to Nicolai Kraus that shows that
-- "J + its computation rule" is contractible, see
-- Equality.Instances-related.Equality-with-J-contractible.

Stable-≡-Erased-axiomatisation-propositional :
  Extensionality (lsuc ℓ) ℓ →
  Is-proposition (Stable-≡-Erased-axiomatisation ℓ)
Stable-≡-Erased-axiomatisation-propositional {ℓ} ext =
  [inhabited⇒contractible]⇒propositional λ ax →
  let ax′ = _⇔_.from
              []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation
              ax

      module BC = []-cong-axiomatisation ax′
      module EC = Erased-cong ax′ ax′
  in
  _⇔_.from contractible⇔↔⊤
    (Stable-≡-Erased-axiomatisation ℓ                                  ↔⟨ Eq.↔→≃
                                                                            (λ (Stable-≡-Erased , Stable-≡-Erased-[refl]) _ →
                                                                                 (λ ([ x , y , x≡y ]) →
                                                                                    Stable-≡-Erased [ x ] [ y ] [ x≡y ])
                                                                               , (λ _ → Stable-≡-Erased-[refl]))
                                                                            (λ hyp →
                                                                                 (λ ([ x ]) ([ y ]) ([ x≡y ]) →
                                                                                    hyp _ .proj₁ [ (x , y , x≡y) ])
                                                                               , hyp _ .proj₂ _)
                                                                            refl
                                                                            refl ⟩
     ((([ A ]) : Erased (Type ℓ)) →
      ∃ λ (s : (([ x , y , _ ]) :
                Erased (∃ λ x → ∃ λ y → [ x ] ≡ [ y ])) →
               [ x ] ≡ [ y ]) →
        ((([ x ]) : Erased A) →
         s [ (x , x , refl [ x ]) ] ≡ refl [ x ]))                     ↝⟨ (∀-cong ext λ _ → inverse $
                                                                           Σ-cong
                                                                             (inverse $
                                                                              Π-cong
                                                                                ext′
                                                                                (EC.Erased-cong-≃ (∃-cong λ _ → ∃-cong λ _ → []≡[]≃≡))
                                                                                (λ _ → Eq.id)) λ s →
                                                                           ∀-cong ext′ λ ([ x ]) →
       s [ (x , x , refl x) ] ≡ refl [ x ]                                   ↝⟨ ≡⇒↝ _ $ cong (_≡ _) $
                                                                                cong (λ (([ eq ]) : Erased (x ≡ x)) → s [ (x , x , eq) ]) $
                                                                                BC.[]-cong [ sym $ cong-refl _ ] ⟩□
       s [ (x , x , cong erased (refl [ x ])) ] ≡ refl [ x ]                 □) ⟩

     ((([ A ]) : Erased (Type ℓ)) →
      ∃ λ (s : (([ x , y , _ ]) : Erased (A ²/≡)) → [ x ] ≡ [ y ]) →
        ((([ x ]) : Erased A) → s [ (x , x , refl x) ] ≡ refl [ x ]))  ↝⟨ (∀-cong ext λ _ →
                                                                           Σ-cong
                                                                             (inverse $
                                                                              Π-cong ext′ (inverse $ EC.Erased-cong-↔ -²/≡↔-) (λ _ → Eq.id)) λ _ →
                                                                             F.id) ⟩
     ((([ A ]) : Erased (Type ℓ)) →
      ∃ λ (r : (x : Erased A) → x ≡ x) →
        (x : Erased A) → r x ≡ refl x)                                 ↝⟨ (∀-cong ext λ _ → inverse
                                                                           ΠΣ-comm) ⟩
     ((([ A ]) : Erased (Type ℓ))
      (x : Erased A) →
      ∃ λ (x≡x : x ≡ x) → x≡x ≡ refl x)                                ↝⟨ (_⇔_.to contractible⇔↔⊤ $
                                                                           Π-closure ext  0 λ _ →
                                                                           Π-closure ext′ 0 λ _ →
                                                                           singleton-contractible _) ⟩□
     ⊤                                                                 □)
  where
  ext′ : Extensionality ℓ ℓ
  ext′ = lower-extensionality _ lzero ext

-- The type []-cong-axiomatisation ℓ is equivalent to
-- Stable-≡-Erased-axiomatisation ℓ (assuming extensionality).

[]-cong-axiomatisation≃Stable-≡-Erased-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ ℓ ]
  Stable-≡-Erased-axiomatisation ℓ
[]-cong-axiomatisation≃Stable-≡-Erased-axiomatisation {ℓ} =
  generalise-ext?-prop
    []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation
    []-cong-axiomatisation-propositional
    Stable-≡-Erased-axiomatisation-propositional

------------------------------------------------------------------------
-- Some lemmas related to Stable-≡-Erased-axiomatisation′

private

  -- The type []-cong-axiomatisation ℓ is logically equivalent to
  -- Stable-≡-Erased-axiomatisation′ ℓ.

  []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation′ :
    []-cong-axiomatisation ℓ ⇔ Stable-≡-Erased-axiomatisation′ ℓ
  []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation′ {ℓ} = record
    { to   = []-cong-axiomatisation ℓ           →⟨ _⇔_.to []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation ⟩
             Stable-≡-Erased-axiomatisation ℓ   →⟨ Σ-map (λ f → f) (λ f → f) ⟩□
             Stable-≡-Erased-axiomatisation′ ℓ  □
    ; from = S→B.instance-of-[]-cong-axiomatisation
    }
    where
    module S→B = Stable-≡-Erased-axiomatisation′→[]-cong-axiomatisation

-- The type Stable-≡-Erased-axiomatisation′ ℓ is propositional
-- (assuming extensionality).
--
-- The proof is based on a proof due to Nicolai Kraus that shows that
-- "J + its computation rule" is contractible, see
-- Equality.Instances-related.Equality-with-J-contractible.

Stable-≡-Erased-axiomatisation′-propositional :
  Extensionality (lsuc ℓ) ℓ →
  Is-proposition (Stable-≡-Erased-axiomatisation′ ℓ)
Stable-≡-Erased-axiomatisation′-propositional {ℓ} ext =
  [inhabited⇒contractible]⇒propositional λ ax →
  let ax′ = _⇔_.from
              []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation′
              ax

      module BC = []-cong-axiomatisation ax′
      module EC = Erased-cong ax′ ax′
  in
  _⇔_.from contractible⇔↔⊤
    (Stable-≡-Erased-axiomatisation′ ℓ                                 ↔⟨ Eq.↔→≃
                                                                            (λ (Stable-≡-Erased , Stable-≡-Erased-[refl]) _ →
                                                                                 (λ ([ x , y , x≡y ]) →
                                                                                    Stable-≡-Erased [ x ] [ y ] [ x≡y ])
                                                                               , (λ _ → Stable-≡-Erased-[refl]))
                                                                            (λ hyp →
                                                                                 (λ ([ x ]) ([ y ]) ([ x≡y ]) →
                                                                                    hyp _ .proj₁ [ (x , y , x≡y) ])
                                                                               , hyp _ .proj₂ _)
                                                                            refl
                                                                            refl ⟩
     ((A : Type ℓ) →
      ∃ λ (s : (([ x , y , _ ]) :
                Erased (∃ λ x → ∃ λ y → [ x ] ≡ [ y ])) →
               [ x ] ≡ [ y ]) →
        ((([ x ]) : Erased A) →
         s [ (x , x , refl [ x ]) ] ≡ refl [ x ]))                     ↝⟨ (∀-cong ext λ _ → inverse $
                                                                           Σ-cong
                                                                             (inverse $
                                                                              Π-cong
                                                                                ext′
                                                                                (EC.Erased-cong-≃ (∃-cong λ _ → ∃-cong λ _ → []≡[]≃≡))
                                                                                (λ _ → Eq.id)) λ s →
                                                                           ∀-cong ext′ λ ([ x ]) →
       s [ (x , x , refl x) ] ≡ refl [ x ]                                   ↝⟨ ≡⇒↝ _ $ cong (_≡ _) $
                                                                                cong (λ (([ eq ]) : Erased (x ≡ x)) → s [ (x , x , eq) ]) $
                                                                                BC.[]-cong [ sym $ cong-refl _ ] ⟩□
       s [ (x , x , cong erased (refl [ x ])) ] ≡ refl [ x ]                 □) ⟩

     ((A : Type ℓ) →
      ∃ λ (s : (([ x , y , _ ]) : Erased (A ²/≡)) → [ x ] ≡ [ y ]) →
        ((([ x ]) : Erased A) → s [ (x , x , refl x) ] ≡ refl [ x ]))  ↝⟨ (∀-cong ext λ _ →
                                                                           Σ-cong
                                                                             (inverse $
                                                                              Π-cong ext′ (inverse $ EC.Erased-cong-↔ -²/≡↔-) (λ _ → Eq.id)) λ _ →
                                                                             F.id) ⟩
     ((A : Type ℓ) →
      ∃ λ (r : (x : Erased A) → x ≡ x) →
        (x : Erased A) → r x ≡ refl x)                                 ↝⟨ (∀-cong ext λ _ → inverse
                                                                           ΠΣ-comm) ⟩
     ((A : Type ℓ)
      (x : Erased A) →
      ∃ λ (x≡x : x ≡ x) → x≡x ≡ refl x)                                ↝⟨ (_⇔_.to contractible⇔↔⊤ $
                                                                           Π-closure ext  0 λ _ →
                                                                           Π-closure ext′ 0 λ _ →
                                                                           singleton-contractible _) ⟩□
     ⊤                                                                 □)
  where
  ext′ : Extensionality ℓ ℓ
  ext′ = lower-extensionality _ lzero ext

-- The type []-cong-axiomatisation ℓ is equivalent to
-- Stable-≡-Erased-axiomatisation′ ℓ (assuming extensionality).

[]-cong-axiomatisation≃Stable-≡-Erased-axiomatisation′ :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ ℓ ]
  Stable-≡-Erased-axiomatisation′ ℓ
[]-cong-axiomatisation≃Stable-≡-Erased-axiomatisation′ {ℓ} =
  generalise-ext?-prop
    []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation′
    []-cong-axiomatisation-propositional
    Stable-≡-Erased-axiomatisation′-propositional

------------------------------------------------------------------------
-- Another alternative to []-cong-axiomatisation

-- This axiomatisation states that equality is very stable for
-- Erased A, for every type A in a certain universe.

Very-stable-≡-Erased-axiomatisation : (ℓ : Level) → Type (lsuc ℓ)
Very-stable-≡-Erased-axiomatisation ℓ =
  {A : Type ℓ} → Very-stable-≡ (Erased A)

-- The type Very-stable-≡-Erased-axiomatisation ℓ is propositional
-- (assuming extensionality).

Very-stable-≡-Erased-axiomatisation-propositional :
  Extensionality (lsuc ℓ) ℓ →
  Is-proposition (Very-stable-≡-Erased-axiomatisation ℓ)
Very-stable-≡-Erased-axiomatisation-propositional ext =
  implicit-Π-closure ext 1 λ _ →
  For-iterated-equality-Very-stable-propositional
    (lower-extensionality _ lzero ext)
    1

-- The type Stable-≡-Erased-axiomatisation′ ℓ is equivalent to
-- Very-stable-≡-Erased-axiomatisation ℓ (assuming extensionality).

Stable-≡-Erased-axiomatisation′≃Very-stable-≡-Erased-axiomatisation :
  Stable-≡-Erased-axiomatisation′ ℓ ↝[ lsuc ℓ ∣ ℓ ]
  Very-stable-≡-Erased-axiomatisation ℓ
Stable-≡-Erased-axiomatisation′≃Very-stable-≡-Erased-axiomatisation
  {ℓ} =
  generalise-ext?-prop
    (record { to = to; from = from })
    Stable-≡-Erased-axiomatisation′-propositional
    Very-stable-≡-Erased-axiomatisation-propositional
  where
  to :
    Stable-≡-Erased-axiomatisation′ ℓ →
    Very-stable-≡-Erased-axiomatisation ℓ
  to ax = Very-stable→Very-stable-≡ 0 Very-stable-Erased
    where
    open []-cong₁
           (_⇔_.from
              []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation′
              ax)

  from :
    Very-stable-≡-Erased-axiomatisation ℓ →
    Stable-≡-Erased-axiomatisation′ ℓ
  from Very-stable-≡-Erased =
      Very-stable→Stable 1 Very-stable-≡-Erased
    , (λ {_ x} →
         Very-stable→Stable 1 Very-stable-≡-Erased x x [ refl x ]  ≡⟨ _≃_.left-inverse-of Eq.⟨ _ , Very-stable-≡-Erased x x ⟩ _ ⟩∎
         refl x                                                    ∎)

-- The type []-cong-axiomatisation ℓ is equivalent to
-- Very-stable-≡-Erased-axiomatisation ℓ (assuming extensionality).

[]-cong-axiomatisation≃Very-stable-≡-Erased-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ ℓ ]
  Very-stable-≡-Erased-axiomatisation ℓ
[]-cong-axiomatisation≃Very-stable-≡-Erased-axiomatisation {ℓ} =
  generalise-ext?-prop
    ([]-cong-axiomatisation ℓ               ↝⟨ []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation′ ⟩
     Stable-≡-Erased-axiomatisation′ ℓ      ↝⟨ Stable-≡-Erased-axiomatisation′≃Very-stable-≡-Erased-axiomatisation _ ⟩□
     Very-stable-≡-Erased-axiomatisation ℓ  □)
    []-cong-axiomatisation-propositional
    Very-stable-≡-Erased-axiomatisation-propositional

------------------------------------------------------------------------
-- Two more alternatives to []-cong-axiomatisation

-- This axiomatisation states that, for types A and B in a given
-- universe, if B is very stable, then the constant function from
-- Erased A that returns B is 2-extendable along [_]→.

2-extendable-along-[]→-axiomatisation : (ℓ : Level) → Type (lsuc ℓ)
2-extendable-along-[]→-axiomatisation ℓ =
  {A B : Type ℓ} →
  Very-stable B →
  Is-[ 2 ]-extendable-along-[ [_]→ ] (λ (_ : Erased A) → B)

-- A variant of 2-extendable-along-[]→-axiomatisation which states
-- that, for types A and B in a given universe, the constant function
-- from Erased A that returns Erased B is 2-extendable along [_]→.

2-extendable-along-[]→-Erased-axiomatisation :
  (ℓ : Level) → Type (lsuc ℓ)
2-extendable-along-[]→-Erased-axiomatisation ℓ =
  {A B : Type ℓ} →
  Is-[ 2 ]-extendable-along-[ [_]→ ] (λ (_ : Erased A) → Erased B)

-- The type 2-extendable-along-[]→-axiomatisation ℓ is propositional
-- (assuming extensionality).

2-extendable-along-[]→-axiomatisation-propositional :
  Extensionality (lsuc ℓ) (lsuc ℓ) →
  Is-proposition (2-extendable-along-[]→-axiomatisation ℓ)
2-extendable-along-[]→-axiomatisation-propositional ext =
  implicit-Π-closure ext  1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  Π-closure ext″ 1 λ _ →
  PS.Is-extendable-along-propositional ext″
  where
  ext′ = lower-extensionality lzero _ ext
  ext″ = lower-extensionality _     _ ext

-- The type 2-extendable-along-[]→-Erased-axiomatisation ℓ is
-- propositional (assuming extensionality).

2-extendable-along-[]→-Erased-axiomatisation-propositional :
  Extensionality (lsuc ℓ) (lsuc ℓ) →
  Is-proposition (2-extendable-along-[]→-Erased-axiomatisation ℓ)
2-extendable-along-[]→-Erased-axiomatisation-propositional ext =
  implicit-Π-closure ext  1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  PS.Is-extendable-along-propositional ext″
  where
  ext′ = lower-extensionality lzero _ ext
  ext″ = lower-extensionality _     _ ext

-- The type []-cong-axiomatisation ℓ is equivalent to
-- 2-extendable-along-[]→-Erased-axiomatisation ℓ (assuming
-- extensionality).

[]-cong-axiomatisation≃2-extendable-along-[]→-Erased-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ]
  2-extendable-along-[]→-Erased-axiomatisation ℓ
[]-cong-axiomatisation≃2-extendable-along-[]→-Erased-axiomatisation
  {ℓ} =
  generalise-ext?-prop
    {B = 2-extendable-along-[]→-Erased-axiomatisation ℓ}
    (record
       { to   = λ ax →
                  []-cong₁.extendable ax (λ _ → Very-stable-Erased) 2
       ; from =
           2-extendable-along-[]→-Erased-axiomatisation ℓ  ↝⟨ (λ ext → Stable-≡-Erased ext , Stable-≡-Erased-[refl] ext) ⟩
           Stable-≡-Erased-axiomatisation′ ℓ               ↝⟨ _⇔_.from $ []-cong-axiomatisation≃Stable-≡-Erased-axiomatisation′ _ ⟩□
           []-cong-axiomatisation ℓ                        □
       })
    ([]-cong-axiomatisation-propositional ∘
     lower-extensionality lzero _)
    2-extendable-along-[]→-Erased-axiomatisation-propositional
  where
  module _ (ext : 2-extendable-along-[]→-Erased-axiomatisation ℓ) where

    Stable-≡-Erased : {A : Type ℓ} → Stable-≡ (Erased A)
    Stable-≡-Erased x y =
      ext .proj₂ (λ _ → x) (λ _ → y) .proj₁ id .proj₁

    Stable-≡-Erased-[refl] :
      {A : Type ℓ} {x : Erased A} →
      Stable-≡-Erased x x [ refl x ] ≡ refl x
    Stable-≡-Erased-[refl] {x} =
      ext .proj₂ (λ _ → x) (λ _ → x) .proj₁ id .proj₂ (refl x)

-- The type []-cong-axiomatisation ℓ is equivalent to
-- 2-extendable-along-[]→-axiomatisation ℓ (assuming extensionality).

[]-cong-axiomatisation≃2-extendable-along-[]→-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ]
  2-extendable-along-[]→-axiomatisation ℓ
[]-cong-axiomatisation≃2-extendable-along-[]→-axiomatisation {ℓ} =
  generalise-ext?-prop
    {B = 2-extendable-along-[]→-axiomatisation ℓ}
    (record
       { to   = λ ax s → []-cong₁.extendable ax (λ _ → s) 2
       ; from =
           2-extendable-along-[]→-axiomatisation ℓ         ↝⟨ _$ Very-stable-Erased ⟩
           2-extendable-along-[]→-Erased-axiomatisation ℓ  ↝⟨ _⇔_.from ([]-cong-axiomatisation≃2-extendable-along-[]→-Erased-axiomatisation _) ⟩□
           []-cong-axiomatisation ℓ                        □
       })
    ([]-cong-axiomatisation-propositional ∘
     lower-extensionality lzero _)
    2-extendable-along-[]→-axiomatisation-propositional

------------------------------------------------------------------------
-- Two more alternatives to []-cong-axiomatisation

-- This axiomatisation states that, for types A and B in a given
-- universe, if B is very stable, then the constant function from
-- Erased A that returns B is ∞-extendable along [_]→.

∞-extendable-along-[]→-axiomatisation : (ℓ : Level) → Type (lsuc ℓ)
∞-extendable-along-[]→-axiomatisation ℓ =
  {A B : Type ℓ} →
  Very-stable B → Is-∞-extendable-along-[ [_]→ ] (λ (_ : Erased A) → B)

-- A variant of ∞-extendable-along-[]→-axiomatisation which states
-- that, for types A and B in a given universe, the constant function
-- from Erased A that returns Erased B is ∞-extendable along [_]→.

∞-extendable-along-[]→-Erased-axiomatisation :
  (ℓ : Level) → Type (lsuc ℓ)
∞-extendable-along-[]→-Erased-axiomatisation ℓ =
  {A B : Type ℓ} →
  Is-∞-extendable-along-[ [_]→ ] (λ (_ : Erased A) → Erased B)

-- The type ∞-extendable-along-[]→-axiomatisation ℓ is propositional
-- (assuming extensionality).

∞-extendable-along-[]→-axiomatisation-propositional :
  Extensionality (lsuc ℓ) (lsuc ℓ) →
  Is-proposition (∞-extendable-along-[]→-axiomatisation ℓ)
∞-extendable-along-[]→-axiomatisation-propositional ext =
  implicit-Π-closure ext  1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  Π-closure ext″ 1 λ _ →
  PS.Is-∞-extendable-along-propositional ext″
  where
  ext′ = lower-extensionality lzero _ ext
  ext″ = lower-extensionality _     _ ext

-- The type ∞-extendable-along-[]→-Erased-axiomatisation ℓ is
-- propositional (assuming extensionality).

∞-extendable-along-[]→-Erased-axiomatisation-propositional :
  Extensionality (lsuc ℓ) (lsuc ℓ) →
  Is-proposition (∞-extendable-along-[]→-Erased-axiomatisation ℓ)
∞-extendable-along-[]→-Erased-axiomatisation-propositional ext =
  implicit-Π-closure ext  1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  PS.Is-∞-extendable-along-propositional ext″
  where
  ext′ = lower-extensionality lzero _ ext
  ext″ = lower-extensionality _     _ ext

-- The type []-cong-axiomatisation ℓ is equivalent to
-- ∞-extendable-along-[]→-axiomatisation ℓ (assuming extensionality).

[]-cong-axiomatisation≃∞-extendable-along-[]→-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ]
  ∞-extendable-along-[]→-axiomatisation ℓ
[]-cong-axiomatisation≃∞-extendable-along-[]→-axiomatisation {ℓ} =
  generalise-ext?-prop
    {B = ∞-extendable-along-[]→-axiomatisation ℓ}
    (record
       { to   = λ ax s → []-cong₁.extendable ax (λ _ → s)
       ; from =
           ∞-extendable-along-[]→-axiomatisation ℓ  ↝⟨ (λ ext s → ext s 2) ⟩
           2-extendable-along-[]→-axiomatisation ℓ  ↝⟨ _⇔_.from ([]-cong-axiomatisation≃2-extendable-along-[]→-axiomatisation _) ⟩□
           []-cong-axiomatisation ℓ                 □
       })
    ([]-cong-axiomatisation-propositional ∘
     lower-extensionality lzero _)
    ∞-extendable-along-[]→-axiomatisation-propositional

-- The type []-cong-axiomatisation ℓ is equivalent to
-- ∞-extendable-along-[]→-Erased-axiomatisation ℓ (assuming
-- extensionality).

[]-cong-axiomatisation≃∞-extendable-along-[]→-Erased-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ]
  ∞-extendable-along-[]→-Erased-axiomatisation ℓ
[]-cong-axiomatisation≃∞-extendable-along-[]→-Erased-axiomatisation
  {ℓ} =
  generalise-ext?-prop
    {B = ∞-extendable-along-[]→-Erased-axiomatisation ℓ}
    (record
       { to   = λ ax → []-cong₁.extendable ax (λ _ → Very-stable-Erased)
       ; from =
           ∞-extendable-along-[]→-Erased-axiomatisation ℓ  ↝⟨ (λ ext → ext 2) ⟩
           2-extendable-along-[]→-Erased-axiomatisation ℓ  ↝⟨ _⇔_.from ([]-cong-axiomatisation≃2-extendable-along-[]→-Erased-axiomatisation _) ⟩□
           []-cong-axiomatisation ℓ                        □
       })
    ([]-cong-axiomatisation-propositional ∘
     lower-extensionality lzero _)
    ∞-extendable-along-[]→-Erased-axiomatisation-propositional

------------------------------------------------------------------------
-- Some lemmas related to []-cong-axiomatisation′

-- The type []-cong-axiomatisation′ a is propositional (assuming
-- extensionality).

[]-cong-axiomatisation′-propositional :
  Extensionality (lsuc a) a →
  Is-proposition ([]-cong-axiomatisation′ a)
[]-cong-axiomatisation′-propositional {a} ext =
  [inhabited⇒contractible]⇒propositional λ ax →
  let ax′ = []-cong-axiomatisation′→[]-cong-axiomatisation ax

      module BC = []-cong₁ ax′

      s₁ : {@0 A : Type a} → Very-stable-≡ (Erased A)
      s₁ = BC.Very-stable→Very-stable-≡ 0 Very-stable-Erased

      s₂ : {@0 A : Type a} →
           For-iterated-equality 2 Very-stable (Erased A)
      s₂ = BC.Very-stable→Very-stable-≡ 1 s₁
  in
  _⇔_.from contractible⇔↔⊤
    ([]-cong-axiomatisation′ a                                            ↔⟨ Eq.↔→≃
                                                                               (λ (record { []-cong        = c
                                                                                          ; []-cong-[refl] = r
                                                                                          })
                                                                                  _ →
                                                                                    (λ _ _ ([ x≡y ]) → c [ x≡y ])
                                                                                  , (λ _ → r))
                                                                               (λ f → record
                                                                                  { []-cong        = λ ([ x≡y ]) → f _ .proj₁ _ _ [ x≡y ]
                                                                                  ; []-cong-[refl] = f _ .proj₂ _
                                                                                  })
                                                                               refl
                                                                               refl ⟩
     ((A : Type a) →
      ∃ λ (c : ((x y : A) → Erased (x ≡ y) → [ x ] ≡ [ y ])) →
        ((x : A) → c x x [ refl x ] ≡ refl [ x ]))                        ↝⟨ (∀-cong ext λ _ → inverse $
                                                                              Σ-cong
                                                                                ((Π-Erased≃Π ext′ λ _ →
                                                                                  Very-stable→Stable 0 $
                                                                                  Very-stable-Π ext′ λ _ →
                                                                                  Very-stable-Π ext′ λ _ →
                                                                                  s₁ _ _) Eq.∘
                                                                                 (∀-cong ext′ λ _ →
                                                                                  Π-Erased≃Π ext′ λ _ →
                                                                                  Very-stable→Stable 0 $
                                                                                  Very-stable-Π ext′ λ _ →
                                                                                  s₁ _ _)) λ _ →
                                                                              F.id) ⟩
     ((A : Type a) →
      ∃ λ (c : ((([ x ]) ([ y ]) : Erased A) →
                Erased (x ≡ y) → [ x ] ≡ [ y ])) →
        ((x : A) → c [ x ] [ x ] [ refl x ] ≡ refl [ x ]))                ↝⟨ (∀-cong ext λ _ →
                                                                              Σ-cong
                                                                                (inverse $
                                                                                 (∀-cong ext′ λ _ → currying) F.∘
                                                                                 currying F.∘
                                                                                 (Π-cong ext′ (∃-cong λ _ → Erased-Σ↔Σ) λ _ → F.id) F.∘
                                                                                 (Π-cong ext′ Erased-Σ↔Σ λ _ → F.id)) λ _ →
                                                                              F.id) ⟩
     ((A : Type a) →
      ∃ λ (c : ((([ x , y , _ ]) : Erased (A ²/≡)) → [ x ] ≡ [ y ])) →
        ((x : A) → c [ (x , x , refl x) ] ≡ refl [ x ]))                  ↝⟨ (∀-cong ext λ _ → ∃-cong λ _ →
                                                                              inverse $ Π-Erased≃Π ext′ λ _ →
                                                                              Very-stable→Stable 2 s₂ _ _ _ _) ⟩
     ((A : Type a) →
      ∃ λ (c : ((([ x , y , _ ]) : Erased (A ²/≡)) → [ x ] ≡ [ y ])) →
        ((([ x ]) : Erased A) → c [ (x , x , refl x) ] ≡ refl [ x ]))     ↝⟨ (inverse $ Π-Erased≃Π ext λ A →
                                                                              Very-stable→Stable 0 $
                                                                              Very-stable-Σ
                                                                                (Very-stable-Π ext′ λ _ →
                                                                                 s₁ _ _) λ _ →
                                                                              Very-stable-Π ext′ λ _ →
                                                                              s₂ _ _ _ _) ⟩
     ((([ A ]) : Erased (Type a)) →
      ∃ λ (c : ((([ x , y , _ ]) : Erased (A ²/≡)) → [ x ] ≡ [ y ])) →
        ((([ x ]) : Erased A) → c [ (x , x , refl x) ] ≡ refl [ x ]))     ↔⟨ Eq.↔→≃
                                                                               (λ f → record
                                                                                  { []-cong        = λ ([ x≡y ]) → f _ .proj₁ [ (_ , _ , x≡y) ]
                                                                                  ; []-cong-[refl] = f _ .proj₂ _
                                                                                  })
                                                                               (λ (record { []-cong        = c
                                                                                          ; []-cong-[refl] = r
                                                                                          })
                                                                                  _ →
                                                                                    (λ ([ _ , _ , x≡y ]) → c [ x≡y ])
                                                                                  , (λ _ → r))
                                                                               refl
                                                                               refl ⟩

     []-cong-axiomatisation a                                             ↝⟨ _⇔_.to contractible⇔↔⊤ $
                                                                             []-cong-axiomatisation-contractible ext ⟩□
     ⊤                                                                    □)
  where
  ext′ : Extensionality a a
  ext′ = lower-extensionality _ lzero ext

-- The type []-cong-axiomatisation ℓ is equivalent to
-- []-cong-axiomatisation′ ℓ (assuming extensionality).

[]-cong-axiomatisation≃[]-cong-axiomatisation′ :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ ℓ ]
  []-cong-axiomatisation′ ℓ
[]-cong-axiomatisation≃[]-cong-axiomatisation′ {ℓ} =
  generalise-ext?-prop
    (record
       { from = []-cong-axiomatisation′→[]-cong-axiomatisation
       ; to   = λ ax → let open []-cong-axiomatisation ax in record
         { []-cong        = []-cong
         ; []-cong-[refl] = []-cong-[refl]
         }
       })
    []-cong-axiomatisation-propositional
    []-cong-axiomatisation′-propositional

------------------------------------------------------------------------
-- Some lemmas related to []-cong-axiomatisation

-- It is not the case that []-cong-axiomatisation ℓ does not hold.

¬¬-[]-cong-axiomatisation : ¬¬ []-cong-axiomatisation ℓ
¬¬-[]-cong-axiomatisation =
  DN.wrap (Erased→¬¬ [ erased-instance-of-[]-cong-axiomatisation ])

-- If something follows from []-cong-axiomatisation ℓ, then it is
-- inconsistent to postulate the negation of this thing.

consequences-of-[]-cong-axiomatisation-do-not-not-hold :
  ([]-cong-axiomatisation ℓ → A) → ¬¬ A
consequences-of-[]-cong-axiomatisation-do-not-not-hold f =
  DN.map′ f ¬¬-[]-cong-axiomatisation
