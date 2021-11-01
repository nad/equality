------------------------------------------------------------------------
-- Properties related to stability for Erased
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Erased.Stability
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq
  hiding (module Extensionality)

open import Logical-equivalence as LE using (_⇔_)
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
open import Equivalence.Path-split eq as PS
  using (Is-∞-extendable-along-[_]; _-Null_; _-Nullᴱ_)
open import For-iterated-equality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (_↣_; Injective)
import List eq as L
import Nat eq as Nat
open import Surjection eq using (_↠_; Split-surjective)
open import Univalence-axiom eq

open import Erased.Level-1 eq as E₁
  hiding (module []-cong; module []-cong₁; module Extensionality)
import Erased.Level-2
private
  module E₂ = Erased.Level-2 eq

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ p : Level
    A B                : Type a
    P                  : A → Type p
    k k′ x y           : A
    n                  : ℕ

------------------------------------------------------------------------
-- Some lemmas related to stability

-- If A is very stable, then [_]→ {A = A} is an embedding.

Very-stable→Is-embedding-[] :
  Very-stable A → Is-embedding [ A ∣_]→
Very-stable→Is-embedding-[] {A = A} s x y =
  _≃_.is-equivalence ≡≃[]≡[]
  where
  A≃Erased-A : A ≃ Erased A
  A≃Erased-A = Eq.⟨ _ , s ⟩

  ≡≃[]≡[] : (x ≡ y) ≃ ([ x ] ≡ [ y ])
  ≡≃[]≡[] = inverse $ Eq.≃-≡ A≃Erased-A

-- If A is very stable, then [_]→ {A = A} is split surjective.

Very-stable→Split-surjective-[] :
  Very-stable A → Split-surjective [ A ∣_]→
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
Very-stableᴱ→Stable-≃ᴱ {A = A} n =
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
Very-stableᴱ→Stable {A = A} n =
  For-iterated-equality n Very-stableᴱ A             →⟨ Very-stableᴱ→Stable-≃ᴱ n ⟩
  For-iterated-equality n Stable-[ equivalenceᴱ ] A  →⟨ For-iterated-equality-cong₁ᴱ-→ n _≃ᴱ_.to ⟩□
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
  {@0 A : Type a} →
  Very-stableᴱ (Very-stableᴱ A) →
  Very-stableᴱ A
Very-stableᴱ-Very-stableᴱ→Very-stableᴱ {A = A} s =
                           $⟨ Erased-Very-stable ⟩
  Erased (Very-stable A)   →⟨ map (Very-stable→Very-stableᴱ 0) ⟩
  Erased (Very-stableᴱ A)  →⟨ Very-stableᴱ→Stable 0 s ⟩□
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

¬¬-stable→Stable : {@0 A : Type a} → (¬ ¬ A → A) → Stable A
¬¬-stable→Stable ¬¬-Stable x = ¬¬-Stable (Erased→¬¬ x)

-- Types for which it is known whether or not they are inhabited are
-- stable.

Dec→Stable : {@0 A : Type a} → Dec A → Stable A
Dec→Stable (yes x) _ = x
Dec→Stable (no ¬x) x with () ← Erased→¬¬ x ¬x

-- Every type is stable in the double negation monad.

¬¬-Stable : {@0 A : Type a} → ¬¬ Stable A
¬¬-Stable = DN.map′ Dec→Stable excluded-middle

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
  H-level-suc→For-iterated-equality-Is-proposition {n = n} {A = A} =
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
Stable-proposition→Very-stableᴱ {A = A} s prop =
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
Stable→H-level-suc→Very-stableᴱ {A = A} n s h =                $⟨ s ,′ [ H-level-suc→For-iterated-equality-Is-proposition h ] ⟩
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
H-level→Very-stableᴱ {A = A} n =
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
→→Is-equivalence→Very-stableᴱ→Very-stableᴱ {A = A} {B = B} f eq s =
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
Very-stableᴱ-cong {a = a} {b = b} ext A≃ᴱB =
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
  {@0 A : Type a} {@0 P : A → Type p} →
  @0 Extensionality a p →
  (∀ x → Very-stableᴱ (P x)) →
  Very-stableᴱ ((x : A) → P x)
Very-stableᴱ-Π {P = P} ext s =
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

Very-stableᴱ-× :
  {@0 A : Type a} {@0 B : Type b} →
  Very-stableᴱ A → Very-stableᴱ B → Very-stableᴱ (A × B)
Very-stableᴱ-× {A = A} {B = B} s s′ =
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

Very-stableᴱ-↑ :
  {@0 A : Type a} →
  Very-stableᴱ A → Very-stableᴱ (↑ ℓ A)
Very-stableᴱ-↑ {A = A} s =
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
Very-stable-¬ {A = A} ext =
  Very-stable-Π ext λ _ →
  Very-stable-⊥

-- If A is very stable with erased proofs, then W A P is very stable
-- with erased proofs (assuming extensionality).

Very-stableᴱ-W :
  {@0 A : Type a} {@0 P : A → Type p} →
  @0 Extensionality p (a ⊔ p) →
  Very-stableᴱ A →
  Very-stableᴱ (W A P)
Very-stableᴱ-W {A = A} {P = P} ext s =
  _≃ᴱ_.is-equivalence $
  EEq.↔→≃ᴱ [_]→ from []∘from from∘[]
  where
  A≃ᴱE-A : A ≃ᴱ Erased A
  A≃ᴱE-A = EEq.⟨ _ , s ⟩₀

  from : Erased (W A P) → W A P
  from [ sup x f ] = sup
    (_≃ᴱ_.from A≃ᴱE-A [ x ])
    (λ y → from [ f (subst P (_≃ᴱ_.left-inverse-of A≃ᴱE-A x) y) ])

  @0 from∘[] : ∀ x → from [ x ] ≡ x
  from∘[] (sup x f) = curry (_↠_.to (W-≡,≡↠≡ ext))
    (_≃ᴱ_.left-inverse-of A≃ᴱE-A x)
    (λ y → from∘[] (f (subst P (_≃ᴱ_.left-inverse-of A≃ᴱE-A x) y)))

  @0 []∘from : ∀ x → [ from x ] ≡ x
  []∘from [ x ] = cong [_]→ (from∘[] x)

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

-- The Coq code accompanying "Modalities in Homotopy Type Theory" uses
-- a somewhat different definition of reflective subuniverses than the
-- paper:
-- * The definition has been adapted to Coq's notion of universe
--   polymorphism.
-- * The proof showing that the modality predicate is propositional is
--   allowed to make use of function extensionality for arbitrary
--   universe levels.
-- * One extra property is assumed: if A and B are equivalent and A is
--   modal, then B is modal. Such a property is proved below, assuming
--   that the []-cong axioms can be instantiated (Very-stable-cong).
-- * The property corresponding to ∘-[]-equivalence is replaced by a
--   property that is intended to avoid uses of extensionality. This
--   property is stated using Is-∞-extendable-along-[_]. Such a
--   property is proved below, assuming that the []-cong axioms can be
--   instantiated (const-extendable).
-- (This refers to one version of the code, which seems to have
-- changed since I first looked at it.)
--
-- Here is a definition of Σ-closed reflective subuniverses that is
-- based on the definition of reflective subuniverses in (one version
-- of) the Coq code of Rijke et al. Note that Is-modal-propositional
-- is only given access to function extensionality for a given
-- universe level. Below (Erased-Σ-closed-reflective-subuniverse) it
-- is proved that λ A → Erased A, [_]→ and Very-stable form a Σ-closed
-- reflective subuniverse of this kind (assuming that the []-cong
-- axioms can be instantiated).

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
-- Erased is accessible and topological (assuming extensionality)

-- A definition of what it means for a Σ-closed reflective subuniverse
-- to be accessible (for a certain universe level).
--
-- This definition is based on (one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory" by Rijke, Shulman
-- and Spitters.

Accessible :
  (ℓ : Level) → Σ-closed-reflective-subuniverse a → Type (lsuc (a ⊔ ℓ))
Accessible {a = a} ℓ U =
  ∃ λ (I : Type ℓ) →
  ∃ λ (P : I → Type ℓ) →
    (A : Type a) →
    Is-modal A ⇔
    ∀ i →
    Is-∞-extendable-along-[ (λ (_ : P i) → lift tt) ]
      (λ (_ : ↑ ℓ ⊤) → A)
  where
  open Σ-closed-reflective-subuniverse U

-- A definition of what it means for a Σ-closed reflective subuniverse
-- to be topological (for a certain universe level).
--
-- This definition is based on (one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory" by Rijke, Shulman
-- and Spitters.
--
-- Below it is proved that Erased-Σ-closed-reflective-subuniverse is
-- topological (assuming extensionality and that the []-cong axioms
-- can be instantiated).

Topological :
  (ℓ : Level) → Σ-closed-reflective-subuniverse a → Type (lsuc (a ⊔ ℓ))
Topological {a = a} ℓ U =
  ∃ λ (I : Type ℓ) →
  ∃ λ (P : I → Type ℓ) →
    (∀ i → Is-proposition (P i)) ×
    ((A : Type a) →
     Is-modal A ⇔
     ∀ i →
     Is-∞-extendable-along-[ (λ (_ : P i) → lift tt) ]
       (λ (_ : ↑ ℓ ⊤) → A))
  where
  open Σ-closed-reflective-subuniverse U

-- A definition of what it means for Erased to be accessible and
-- topological (for certain universe levels).
--
-- This definition is based on (one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory" by Rijke, Shulman
-- and Spitters.

Erased-is-accessible-and-topological′ :
  (ℓ a : Level) → Type (lsuc (a ⊔ ℓ))
Erased-is-accessible-and-topological′ ℓ a =
  ∃ λ (I : Type ℓ) →
  ∃ λ (P : I → Type ℓ) →
    (∀ i → Is-proposition (P i)) ×
    ((A : Type a) →
     Very-stable A ⇔
     ∀ i →
     Is-∞-extendable-along-[ (λ (_ : P i) → lift tt) ]
       (λ (_ : ↑ ℓ ⊤) → A))

-- A variant of Erased-is-accessible-and-topological′ that does not
-- use Is-∞-extendable-along-[_].

Erased-is-accessible-and-topological :
  (ℓ a : Level) → Type (lsuc (a ⊔ ℓ))
Erased-is-accessible-and-topological ℓ a =
  ∃ λ (I : Type ℓ) →
  ∃ λ (P : I → Type ℓ) →
    (∀ i → Is-proposition (P i)) ×
    ((A : Type a) → Very-stable A ⇔ P -Null A)

-- Erased-is-accessible-and-topological′ and
-- Erased-is-accessible-and-topological are pointwise equivalent
-- (assuming extensionality).

≃Erased-is-accessible-and-topological :
  Extensionality (lsuc a ⊔ ℓ) (a ⊔ ℓ) →
  Erased-is-accessible-and-topological′ ℓ a ≃
  Erased-is-accessible-and-topological ℓ a
≃Erased-is-accessible-and-topological {a = a} {ℓ = ℓ} ext =
  ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
  ∀-cong (lower-extensionality ℓ lzero ext) λ _ →
  ⇔-cong (lower-extensionality (lsuc a) lzero ext) Eq.id $
  PS.Π-Is-∞-extendable-along≃Null
    (lower-extensionality (lsuc a) lzero ext)

-- A variant of Erased-is-accessible-and-topological that uses
-- Very-stableᴱ instead of Very-stable and _-Nullᴱ_ instead of
-- _-Null_, and for which Is-proposition is replaced by
-- Erased ∘ Is-proposition.

Erased-is-accessible-and-topologicalᴱ : (ℓ a : Level) → Type (lsuc (a ⊔ ℓ))
Erased-is-accessible-and-topologicalᴱ ℓ a =
  ∃ λ (I : Type ℓ) →
  ∃ λ (P : I → Type ℓ) →
    (∀ i → Erased (Is-proposition (P i))) ×
    ((A : Type a) → Very-stableᴱ A ⇔ P -Nullᴱ A)

-- In erased contexts Erased is accessible and topological (assuming
-- extensionality).

@0 erased-is-accessible-and-topological-in-erased-contexts :
  Extensionality (a ⊔ ℓ) (a ⊔ ℓ) →
  Erased-is-accessible-and-topological ℓ a
erased-is-accessible-and-topological-in-erased-contexts
  {a = a} {ℓ = ℓ} ext =
    ↑ ℓ ⊤
  , (λ _ → ↑ ℓ ⊤)
  , (λ _ → H-level.mono₁ 0 $ ↑-closure 0 ⊤-contractible)
  , λ A →
      Very-stable A          ↔⟨ _⇔_.to contractible⇔↔⊤ $
                                propositional⇒inhabited⇒contractible
                                  (Very-stable-propositional (lower-extensionality ℓ ℓ ext))
                                  (Erased-Very-stable .erased) ⟩
      ⊤                      ↝⟨ record { to = λ _ _ → _≃_.is-equivalence $ Eq.↔→≃ _ (_$ _) refl refl } ⟩□
      (λ _ → ↑ ℓ ⊤) -Null A  □

-- Very-stable {a = a} is pointwise equivalent to
-- (λ (A : Type a) → Very-stable A) -Null_ (assuming extensionality).

Very-stable≃Very-stable-Null :
  {A : Type a} →
  Extensionality a a →
  Very-stable A ↝[ lsuc a ∣ a ] (λ (A : Type a) → Very-stable A) -Null A
Very-stable≃Very-stable-Null {A = A} ext =
  generalise-ext?-prop
    (record { to = to; from = from })
    (λ _ → Very-stable-propositional ext)
    (λ ext′ →
       Π-closure ext′ 1 λ _ →
       Eq.propositional ext _)
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
Very-stableᴱ≃Very-stableᴱ-Nullᴱ {A = A} ext′ =
  EEq.⇔→≃ᴱ
    (Very-stableᴱ-propositional ext)
    (Π-closure ext′ 1 λ _ →
     EEq.Is-equivalenceᴱ-propositional ext _)
    to
    from
  where
  @0 ext : _
  ext = lower-extensionality _ lzero ext′

  to : Very-stableᴱ A → Very-stableᴱ -Nullᴱ A
  to sA _ =
    _≃ᴱ_.is-equivalence $
    EEq.↔→≃ᴱ
      const
      (λ f → Very-stableᴱ→Stable 0 sA [ f sB ])
      (λ f → apply-ext ext λ x →
         const (Very-stableᴱ→Stable 0 sA [ f sB ]) x  ≡⟨⟩
         Very-stableᴱ→Stable 0 sA [ f sB ]            ≡⟨ cong (Very-stableᴱ→Stable 0 sA ∘ [_]→ ∘ f) $
                                                         Very-stableᴱ-propositional ext _ _ ⟩
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
                                                              apply-ext ext λ s →
                                                              Very-stableᴱ→Stable-[]≡id s) ⟩
      _≃ᴱ_.from A≃ (const x)                              ≡⟨⟩
      _≃ᴱ_.from A≃ (_≃ᴱ_.to A≃ x)                         ≡⟨ _≃ᴱ_.left-inverse-of A≃ _ ⟩∎
      x                                                   ∎

-- Erased is accessible and topological (for certain universe levels,
-- assuming extensionality).

erased-is-accessible-and-topological :
  ∀ ℓ → Extensionality (lsuc a ⊔ ℓ) (lsuc a ⊔ ℓ) →
  Erased-is-accessible-and-topological (lsuc a ⊔ ℓ) a
erased-is-accessible-and-topological {a = a} ℓ ext =
    ↑ ℓ (Type a)
  , ↑ _ ∘ Very-stable ∘ lower
  , (λ _ → ↑-closure 1 $ Very-stable-propositional ext′)
  , (λ A →
       Very-stable A                        ↝⟨ Very-stable≃Very-stable-Null ext′ _ ⟩

       Very-stable -Null A                  ↝⟨ (inverse $
                                                Π-cong _ Bijection.↑↔ λ B →
                                                Is-equivalence≃Is-equivalence-∘ˡ
                                                  (_≃_.is-equivalence $
                                                   Eq.↔→≃ (_∘ lift) (_∘ lower) refl refl)
                                                  _) ⟩□
       (↑ _ ∘ Very-stable ∘ lower) -Null A  □)
  where
  ext′ = lower-extensionality _ _ ext

-- The property Erased-is-accessible-and-topologicalᴱ holds for
-- certain universe levels (assuming extensionality).

erased-is-accessible-and-topologicalᴱ :
  ∀ ℓ → @0 Extensionality (lsuc a) a →
  Erased-is-accessible-and-topologicalᴱ (lsuc a ⊔ ℓ) a
erased-is-accessible-and-topologicalᴱ {a = a} ℓ ext =
    ↑ ℓ (Type a)
  , ↑ _ ∘ Very-stableᴱ ∘ lower
  , (λ _ →
       [ ↑-closure 1 $
           Very-stableᴱ-propositional
             (lower-extensionality _ lzero ext)
       ])
  , (λ A →
       Very-stableᴱ A                         ↝⟨ _≃ᴱ_.logical-equivalence $
                                                 Very-stableᴱ≃Very-stableᴱ-Nullᴱ ext ⟩
       Very-stableᴱ -Nullᴱ A                  ↝⟨ (inverse $
                                                  Π-cong _ Bijection.↑↔ λ B →
                                                  EEq.Is-equivalenceᴱ⇔Is-equivalenceᴱ-∘ˡ
                                                    (_≃ᴱ_.is-equivalence $
                                                     EEq.↔→≃ᴱ (_∘ lift) (_∘ lower) refl refl)) ⟩□
       (↑ _ ∘ Very-stableᴱ ∘ lower) -Nullᴱ A  □)

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
Σ-Erased-Erased-singleton⇔ {A = A} =
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
erased-singleton-contractible {x = x} s =
                                     $⟨ singleton-contractible x ⟩
  Contractible (Singleton x)         ↝⟨ H-level-cong _ 0 (∃-cong λ _ → Eq.⟨ _ , s _ _ ⟩) ⦂ (_ → _) ⟩□
  Contractible (Erased-singleton x)  □

-- Erased-singleton x is contractible with an erased proof.

Contractibleᴱ-Erased-singleton :
  {@0 A : Type a} {x : A} →
  Contractibleᴱ (Erased-singleton x)
Contractibleᴱ-Erased-singleton {x = x} =
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
Contractibleᴱ-Erased-other-singleton {x = x} =
                                            $⟨ Contractibleᴱ-Erased-singleton ⟩
  Contractibleᴱ (Erased-singleton x)        →⟨ ECP.Contractibleᴱ-respects-surjection
                                                 (Σ-map id (map sym))
                                                 (_≃_.split-surjective $ Eq.↔→≃ _
                                                    (Σ-map id (map sym))
                                                    (λ _ → cong ((_ ,_) ∘ [_]→) $ sym-sym _)
                                                    (λ _ → cong ((_ ,_) ∘ [_]→) $ sym-sym _)) ⟩□
  Contractibleᴱ (Erased-other-singleton x)  □

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
  Stable-[]-map {A = A} {B = B} A↝B B↝A s =
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
  Stable-cong {k = k} {A = A} {B = B} ext A↝B =
    Stable A        ↔⟨⟩
    (Erased A → A)  ↝⟨ →-cong ext (Erased-cong A↝B) A↝B ⟩
    (Erased B → B)  ↔⟨⟩
    Stable B        □

  -- Stable-[ equivalence ] preserves equivalences (assuming
  -- extensionality).

  Stable-≃-cong :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    A ≃ B → Stable-[ equivalence ] A ↝[ k ] Stable-[ equivalence ] B
  Stable-≃-cong {A = A} {B = B} ext A≃B =
    Stable-[ equivalence ] A  ↔⟨⟩
    Erased A ≃ A              ↝⟨ generalise-ext?
                                   (Eq.≃-preserves-⇔ (Erased-cong A≃B) A≃B)
                                   (λ ext →
                                      let eq = Eq.≃-preserves ext (Erased-cong A≃B) A≃B in
                                      _≃_.right-inverse-of eq , _≃_.left-inverse-of eq)
                                   ext ⟩
    Erased B ≃ B              ↔⟨⟩
    Stable-[ equivalence ] B  □

  -- Stable-[ equivalenceᴱ ] preserves equivalences with erased proofs
  -- (assuming extensionality).

  Stable-≃ᴱ-cong :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    @0 Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    A ≃ᴱ B → Stable-[ equivalenceᴱ ] A ≃ᴱ Stable-[ equivalenceᴱ ] B
  Stable-≃ᴱ-cong {A = A} {B = B} ext A≃B =
    Stable-[ equivalenceᴱ ] A  ↔⟨⟩
    Erased A ≃ᴱ A              ↝⟨ EEq.≃ᴱ-cong ext (Erased-cong A≃B) A≃B ⟩
    Erased B ≃ᴱ B              ↔⟨⟩
    Stable-[ equivalenceᴱ ] B  □

  -- Very-stable preserves equivalences (assuming extensionality).

  Very-stable-cong :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    A ≃ B → Very-stable A ↝[ k ] Very-stable B
  Very-stable-cong ext A≃B =
    generalise-ext?-prop
      (record
         { to   = lemma A≃B (Erased-cong A≃B)
                    (λ x → cong [_]→ (_≃_.right-inverse-of A≃B x))
         ; from = lemma (inverse A≃B) (inverse $ Erased-cong A≃B)
                    (λ x → cong [_]→ (_≃_.left-inverse-of A≃B x))
         })
      (Very-stable-propositional ∘ lower-extensionality ℓ₂ ℓ₂)
      (Very-stable-propositional ∘ lower-extensionality ℓ₁ ℓ₁)
      ext
    where
    lemma :
      (A≃B : A ≃ B) (E-A≃E-B : Erased A ≃ Erased B) →
      (∀ x → _≃_.to E-A≃E-B [ _≃_.from A≃B x ] ≡ [ x ]) →
      Very-stable A → Very-stable B
    lemma {A = A} {B = B} A≃B E-A≃E-B hyp s = _≃_.is-equivalence $
      Eq.with-other-function
        (B         ↝⟨ inverse A≃B ⟩
         A         ↝⟨ Eq.⟨ [_]→ , s ⟩ ⟩
         Erased A  ↝⟨ E-A≃E-B ⟩□
         Erased B  □)
        [_]→
        (λ x →
           _≃_.to E-A≃E-B [ _≃_.from A≃B x ]  ≡⟨ hyp x ⟩∎
           [ x ]                              ∎)

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

  ----------------------------------------------------------------------
  -- More lemmas

  -- All kinds of functions between erased types are stable.

  Stable-Erased↝Erased :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
    Stable (Erased A ↝[ k ] Erased B)
  Stable-Erased↝Erased {k = k} {A = A} {B = B} =
                                       $⟨ Very-stable-Erased ⟩
    Very-stable (Erased (A ↝[ k ] B))  ↝⟨ Very-stable→Stable 0 ⟩
    Stable (Erased (A ↝[ k ] B))       ↝⟨ Stable-map-⇔ (Erased-↝↝↝ _) ⟩□
    Stable (Erased A ↝[ k ] Erased B)  □

  -- If A is very stable, then W A P is very stable (assuming
  -- extensionality).

  Very-stable-W :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    Extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) →
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

------------------------------------------------------------------------
-- Results that depend on an instantiation of the []-cong axioms (for
-- a single universe level)

module []-cong₁ (ax : []-cong-axiomatisation ℓ) where

  open E₁.[]-cong₁ ax
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
  Stable→H-level-suc→Very-stable {A = A} n = curry (
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
    Very-stable-≡↔Is-embedding-[]→ {A = A} n ext =
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
  Very-stableᴱ-Σ {A = A} {P = P} s s′ = _≃ᴱ_.is-equivalence (
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

  -- A generalisation of Very-stableᴱ-W.

  Very-stableᴱ-Wⁿ :
    {A : Type ℓ} {P : A → Type p} →
    Extensionality p (ℓ ⊔ p) →
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
  -- Closure properties related to equality

  -- If A is very stable, then equality is very stable for A.

  Very-stable→Very-stable-≡ :
    {A : Type ℓ} →
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
  Very-stable→Very-stable⁺         zero    = id
  Very-stable→Very-stable⁺ {n = n} (suc m) =
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
  Stable-[]-H-level′ {k = k} {A = A} ext n =
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
  Stable-[]-H-level {k = k} {A = A} ext n =
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
    {@0 A : Type ℓ} →
    @0 Extensionality ℓ ℓ →
    ∀ n →
    For-iterated-equality n Very-stableᴱ A →
    Very-stableᴱ (For-iterated-equality n Contractibleᴱ A)
  Very-stableᴱ-H-levelᴱ {A = A} ext n =
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
  Very-stable-H-level {A = A} ext n =
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
  -- The function λ A → Erased A, [_]→ and Very-stable form a Σ-closed
  -- reflective subuniverse

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

  -- This Σ-closed reflective subuniverse is topological (for certain
  -- universe levels, assuming extensionality).

  Erased-topological :
    ∀ ℓ′ →
    Extensionality (lsuc ℓ ⊔ ℓ′) (lsuc ℓ ⊔ ℓ′) →
    Topological (lsuc ℓ ⊔ ℓ′) Erased-Σ-closed-reflective-subuniverse
  Erased-topological ℓ′ ext =                              $⟨ erased-is-accessible-and-topological ℓ′ ext ⟩
    Erased-is-accessible-and-topological (lsuc ℓ ⊔ ℓ′) ℓ   ↝⟨ inverse $ ≃Erased-is-accessible-and-topological ext ⟩□
    Erased-is-accessible-and-topological′ (lsuc ℓ ⊔ ℓ′) ℓ  □

  ----------------------------------------------------------------------
  -- Erased singletons

  -- The type of triples consisting of two values of type A, one erased,
  -- and an erased proof of equality of the two values is isomorphic to
  -- A.

  Σ-Erased-Erased-singleton↔ :
    {A : Type ℓ} →
    (∃ λ (x : Erased A) → Erased-singleton (erased x)) ↔ A
  Σ-Erased-Erased-singleton↔ {A = A} =
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
  Very-stableᴱ-≡→Contractible-Erased-singleton {x = x} s =
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
  erased-singleton-with-erased-center-propositional {x = x} s =
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
  erased-singleton-with-erased-center-contractible {x = x} s =
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
  -- Some lemmas related to Very-stable

  -- All kinds of functions between erased types are very stable (in
  -- some cases assuming extensionality).

  Very-stable-Erased↝Erased :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
    Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Very-stable (Erased A ↝[ k ] Erased B)
  Very-stable-Erased↝Erased {k = k} {A = A} {B = B} ext =
                                            $⟨ Very-stable-Erased ⟩
    Very-stable (Erased (A ↝[ k ] B))       ↝⟨ []-cong₂-⊔₁.Very-stable-cong ax ax ax _ (from-isomorphism $ E₂.[]-cong₂-⊔.Erased-↝↔↝ ax₁ ax₂ ax ext)
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
  Very-stable-Σ↔Π {A = A} {P = P} s =
    generalise-ext?-prop
      (record
         { from = Very-stable-Σ s
         ; to   = flip λ x →
             Very-stable (Σ A P)                          ↝⟨ flip Very-stable-Σ (λ _ → []-cong₁.Very-stable→Very-stable-≡ ax₁ 0 s _ _) ⟩
             Very-stable (∃ λ ((y , _) : Σ A P) → y ≡ x)  ↝⟨ []-cong₂-⊔₁.Very-stable-cong ax ax  ax _ $ from-bijection $ inverse Σ-assoc ⟩
             Very-stable (∃ λ (y : A) → P y × y ≡ x)      ↝⟨ []-cong₂-⊔₁.Very-stable-cong ax ax₂ ax _ $ from-bijection $ inverse $ ∃-intro _ _ ⟩□
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
  Very-stableᴱ-Σ≃ᴱΠ {A = A} {P = P} ext s s-≡ =
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
      (lemma ax ax ax)
      Very-stable-⊥
      (For-iterated-equality-↑ _ (1 + n) (lemma ax₁ ax ax) sA)
      (For-iterated-equality-↑ _ (1 + n) (lemma ax₂ ax ax) sB)
    where
    lemma :
      ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} →
      []-cong-axiomatisation ℓ₁ →
      []-cong-axiomatisation ℓ₂ →
      []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂) →
      A ↔ B → Very-stable A → Very-stable B
    lemma ax₁ ax₂ ax =
      []-cong₂-⊔₁.Very-stable-cong ax₁ ax₂ ax _ ∘
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
  Stable-Πⁿ {k = k} ext n =
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
      ([]-cong₂-⊔₁.Very-stable-cong ax ax ax _ ∘ from-isomorphism)
      (Very-stable-Π ext)

  -- A generalisation of Very-stable-Stable-Σ.

  Very-stable-Stable-Σⁿ :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    ∀ n →
    For-iterated-equality n Very-stable A →
    (∀ x → For-iterated-equality n Stable-[ k ] (P x)) →
    For-iterated-equality n Stable-[ k ] (Σ A P)
  Very-stable-Stable-Σⁿ {k = k} n =
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
  Stable-≡-Σ {P = P} {p = p} {q = q} s₁ hyp s₂ =  $⟨ Stable-Σ s₁ hyp s₂ ⟩

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
      ([]-cong₂-⊔₁.Very-stable-cong ax ax ax _ ∘ from-isomorphism)
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
      ([]-cong₂-⊔₁.Very-stable-cong ax ax ax _ ∘ from-isomorphism)
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
      ([]-cong₂-⊔₁.Very-stable-cong ax₂ ax ax _ ∘ from-isomorphism)

  -- A generalisation of Very-stable-W.

  Very-stable-Wⁿ :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    Extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) →
    ∀ n →
    For-iterated-equality n Very-stable A →
    For-iterated-equality n Very-stable (W A P)
  Very-stable-Wⁿ {A = A} {P = P} ext n =
    For-iterated-equality-W
      ext
      n
      ([]-cong₂-⊔₁.Very-stable-cong ax ax ax _ ∘ from-isomorphism)
      (Very-stable-Π ext)
      Very-stable-Σ
      ([]-cong₂-⊔₁.Very-stable-W ax₁ ax₂ ax ext)

------------------------------------------------------------------------
-- Results that depend on instances of the axiomatisation of []-cong
-- for all universe levels

module []-cong (ax : ∀ {ℓ} → []-cong-axiomatisation ℓ) where

  private
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

  -- The function λ A → Erased A, [_]→ and Very-stable form a Σ-closed
  -- reflective subuniverse (assuming extensionality).

  Erased-Σ-closed-reflective-subuniverse :
    Extensionality ℓ ℓ →
    Σ-closed-reflective-subuniverse ℓ
  Erased-Σ-closed-reflective-subuniverse ext =
    []-cong₁.Erased-Σ-closed-reflective-subuniverse
      (Extensionality→[]-cong-axiomatisation ext)

  -- This Σ-closed reflective subuniverse is topological (for certain
  -- universe levels, assuming extensionality).

  Erased-topological :
    ∀ ℓ′ (ext : Extensionality (lsuc ℓ ⊔ ℓ′) (lsuc ℓ ⊔ ℓ′)) →
    Topological (lsuc ℓ ⊔ ℓ′)
      (Erased-Σ-closed-reflective-subuniverse {ℓ = ℓ}
         (lower-extensionality _ _ ext))
  Erased-topological ℓ′ ext =
    []-cong₁.Erased-topological
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality _ _ ext))
      ℓ′
      ext

------------------------------------------------------------------------
-- Some lemmas related to Stable-≡-Erased-axiomatisation

private

  -- The type []-cong-axiomatisation ℓ is logically equivalent to
  -- Stable-≡-Erased-axiomatisation ℓ.

  []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation :
    []-cong-axiomatisation ℓ ⇔ Stable-≡-Erased-axiomatisation ℓ
  []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation {ℓ = ℓ} = record
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
Stable-≡-Erased-axiomatisation-propositional {ℓ = ℓ} ext =
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
[]-cong-axiomatisation≃Stable-≡-Erased-axiomatisation {ℓ = ℓ} =
  generalise-ext?-prop
    []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation
    []-cong-axiomatisation-propositional
    Stable-≡-Erased-axiomatisation-propositional

------------------------------------------------------------------------
-- Another alternative to []-cong-axiomatisation

-- This axiomatisation states that equality is very stable for
-- Erased A, for every (erased) type A in a certain universe.

Very-stable-≡-Erased-axiomatisation : (ℓ : Level) → Type (lsuc ℓ)
Very-stable-≡-Erased-axiomatisation ℓ =
  {@0 A : Type ℓ} → Very-stable-≡ (Erased A)

-- The type Very-stable-≡-Erased-axiomatisation ℓ is propositional
-- (assuming extensionality).

Very-stable-≡-Erased-axiomatisation-propositional :
  Extensionality (lsuc ℓ) ℓ →
  Is-proposition (Very-stable-≡-Erased-axiomatisation ℓ)
Very-stable-≡-Erased-axiomatisation-propositional ext =
  implicit-Πᴱ-closure ext 1 λ _ →
  For-iterated-equality-Very-stable-propositional
    (lower-extensionality _ lzero ext)
    1

-- The type Stable-≡-Erased-axiomatisation ℓ is equivalent to
-- Very-stable-≡-Erased-axiomatisation ℓ (assuming extensionality).

Stable-≡-Erased-axiomatisation≃Very-stable-≡-Erased-axiomatisation :
  Stable-≡-Erased-axiomatisation ℓ ↝[ lsuc ℓ ∣ ℓ ]
  Very-stable-≡-Erased-axiomatisation ℓ
Stable-≡-Erased-axiomatisation≃Very-stable-≡-Erased-axiomatisation
  {ℓ = ℓ} =
  generalise-ext?-prop
    (record { to = to; from = from })
    Stable-≡-Erased-axiomatisation-propositional
    Very-stable-≡-Erased-axiomatisation-propositional
  where
  to :
    Stable-≡-Erased-axiomatisation ℓ →
    Very-stable-≡-Erased-axiomatisation ℓ
  to ax = Very-stable→Very-stable-≡ 0 Very-stable-Erased
    where
    open []-cong₁
           (_⇔_.from
              []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation
              ax)

  from :
    Very-stable-≡-Erased-axiomatisation ℓ →
    Stable-≡-Erased-axiomatisation ℓ
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
[]-cong-axiomatisation≃Very-stable-≡-Erased-axiomatisation {ℓ = ℓ} =
  generalise-ext?-prop
    ([]-cong-axiomatisation ℓ               ↝⟨ []-cong-axiomatisation⇔Stable-≡-Erased-axiomatisation ⟩
     Stable-≡-Erased-axiomatisation ℓ       ↝⟨ Stable-≡-Erased-axiomatisation≃Very-stable-≡-Erased-axiomatisation _ ⟩□
     Very-stable-≡-Erased-axiomatisation ℓ  □)
    []-cong-axiomatisation-propositional
    Very-stable-≡-Erased-axiomatisation-propositional
