------------------------------------------------------------------------
-- Squashing
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --prop --safe #-}

open import Equality

module Squash {e⁺} (eq-J : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq-J

open import Logical-equivalence using (_⇔_)
import Modality.Empty-modal
open import Prelude

open import Bijection eq-J using (_↔_)
open import Equality.Decidable-UIP eq-J
open import Double-negation eq-J as DN using (¬¬_)
open import Embedding eq-J using (Embedding; Is-embedding)
open import Equality.Decision-procedures eq-J
open import Equivalence eq-J as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased eq-J using (_≃ᴱ_)
open import Equivalence.Path-split eq-J
  using (Is-∞-extendable-along-[_])
open import Extensionality eq-J
open import For-iterated-equality eq-J
open import Function-universe eq-J hiding (id; _∘_)
open import H-level eq-J as H-level
open import H-level.Closure eq-J
open import Injection eq-J using (_↣_)
open import Modality.Basics eq-J
import Modality.Very-modal eq-J as VM
open import Monad eq-J
open import Surjection eq-J using (_↠_; Split-surjective)

private
  variable
    a b ℓ p : Level
    A B     : Type a
    P       : A → Type p
    k x y   : A
    n       : ℕ

------------------------------------------------------------------------
-- The squash type

-- Any two elements of type Squash′ A are definitionally equal.

data Squash′ (A : Type a) : Prop a where
  squash′ : A → Squash′ A

-- However, Squash′ A does not have type Type a. The following wrapper
-- makes it possible to use squashed types in, say, lists.

record Squash (A : Type a) : Type a where
  constructor squash
  field
    squashed : Squash′ A

pattern [_] x = squash (squash′ x)

private

  -- A unit test.

  test : [ 4 ] ∷ [ 5 ] ∷ [] ≡ [ 3 ] ∷ [ 9 ] ∷ []
  test = refl _

-- Squashed types are propositions.

Squash-propositional : Is-proposition (Squash A)
Squash-propositional = λ _ _ → refl _

------------------------------------------------------------------------
-- Squash is a monad

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : Squash A → (A → Squash B) → Squash B
_>>=′_ {A} {B} (squash x) f = squash (lemma x)
  where
  lemma : Squash′ A → Squash′ B
  lemma (squash′ x) = Squash.squashed (f x)

instance

  -- Squash is a monad.

  raw-monad : Raw-monad {c = ℓ} Squash
  Raw-monad.return raw-monad = [_]
  Raw-monad._>>=_  raw-monad = _>>=′_

  monad : Monad {c = ℓ} Squash
  Monad.raw-monad      monad = raw-monad
  Monad.left-identity  monad = λ _ _ → refl _
  Monad.right-identity monad = λ _ → refl _
  Monad.associativity  monad = λ _ _ _ → refl _

------------------------------------------------------------------------
-- Stability

-- A type A is stable if Squash A implies A.

Stable : Type a → Type a
Stable A = Squash A → A

-- A type A is very stable if Squash A is equivalent to A.

Very-stable : Type a → Type a
Very-stable A = Squash A ≃ A

-- Variants of the definitions above for equality.

Stable-≡ : Type a → Type a
Stable-≡ = For-iterated-equality 1 Stable

Very-stable-≡ : Type a → Type a
Very-stable-≡ = For-iterated-equality 1 Very-stable

------------------------------------------------------------------------
-- Squash is a modality

-- Squash is a modality with [_] as the unit. A type is modal if it is
-- a stable proposition.

modality : Modality ℓ
modality {ℓ} = λ where
    .Modality.◯                   → Squash
    .Modality.η                   → [_]
    .Modality.Modal               → Modal
    .Modality.Modal-propositional → prop
    .Modality.Modal-◯             → Modal-Squash
    .Modality.Modal-respects-≃    → resp
    .Modality.extendable-along-η  → extendable
  where
  Modal : Type ℓ → Type ℓ
  Modal A = Stable A × Is-proposition A

  Modal-Squash : Modal (Squash A)
  Modal-Squash = _>>= id , Squash-propositional

  prop :
    {A : Type ℓ} →
    Extensionality ℓ ℓ →
    Is-proposition (Stable A × Is-proposition A)
  prop ext =
    [inhabited⇒+]⇒+ 0 λ (_ , prop) →
    ×-closure 1
      (Π-closure ext 1 λ _ → prop)
      (H-level-propositional ext 1)

  resp : A ≃ B → Modal A → Modal B
  resp {A} {B} A≃B =
    Stable A × Is-proposition A  →⟨ →-cong-→ (_>>= [_] ∘ _≃_.from A≃B) (_≃_.to A≃B)
                                      ×-cong
                                    H-level-cong _ 1 A≃B ⟩□
    Stable B × Is-proposition B  □

  Modal→Separated : {x y : A} → Modal A → Modal (x ≡ y)
  Modal→Separated {A} {x} {y} (s , prop) =
      (Squash (x ≡ y)        →⟨ const prop ⟩
       Is-proposition A      →⟨ +⇒≡ ⟩
       Contractible (x ≡ y)  →⟨ proj₁ ⟩□
       x ≡ y                 □)
    , ⇒≡ 1 prop

  extendable :
    {A : Type ℓ} {P : Squash A → Type ℓ} →
    (∀ x → Modal (P x)) →
    Is-∞-extendable-along-[ [_] ] P
  extendable         _ zero    = _
  extendable {A} {P} m (suc n) =
      (λ f → (λ x → m x .proj₁ (lemma x f))
           , (λ x →
                m [ x ] .proj₁ (lemma [ x ] f)  ≡⟨ m [ x ] .proj₂ _ _ ⟩∎
                f x                             ∎))
    , (λ _ _ → extendable (Modal→Separated ∘ m) n)
    where
    lemma : (x : Squash A) → ((x : A) → P [ x ]) → Squash (P x)
    lemma (squash x) f = squash (lemma′ x)
      where
      lemma′ : (x : Squash′ A) → Squash′ (P (squash x))
      lemma′ (squash′ x) = squash′ (f x)

-- The squash modality is empty-modal.

empty-modal : Empty-modal (modality {ℓ = ℓ})
empty-modal =
    (λ x → ⊥-in-prop→⊥ (Squash-⊥→⊥-in-prop x))
  , ⊥-propositional
  where

  -- An empty type in Prop.

  data ⊥-in-prop : Prop where

  -- Squash ⊥ implies ⊥-in-prop.

  Squash-⊥→⊥-in-prop : Squash (⊥ {ℓ = ℓ}) → ⊥-in-prop
  Squash-⊥→⊥-in-prop [ () ]

  -- ⊥-in-prop implies ⊥.

  ⊥-in-prop→⊥ : ⊥-in-prop → ⊥ {ℓ = ℓ}
  ⊥-in-prop→⊥ ()

private
  module EM {ℓ} =
    Modality.Empty-modal.Empty-modal eq-J (modality {ℓ = ℓ}) empty-modal

-- Squash commutes with Σ.

Squash-Σ≃Σ-Squash-Squash : Squash (Σ A (P ∘ [_])) ≃ Σ (Squash A) (Squash ∘ P)
Squash-Σ≃Σ-Squash-Squash {A} {P} =
  Eq.↔→≃
    to
    from
    (λ _ → refl _)
    (λ _ → refl _)
  where
  to₁ : Squash′ (Σ A (P ∘ [_])) → Squash′ A
  to₁ (squash′ (x , y)) = squash′ x

  to₂ : (x : Squash′ (Σ A (P ∘ [_]))) → Squash′ (P (squash (to₁ x)))
  to₂ (squash′ (x , y)) = squash′ y

  to : Squash (Σ A (P ∘ [_])) → Σ (Squash A) (Squash ∘ P)
  to (squash x) = squash (to₁ x) , squash (to₂ x)

  from′ :
    (x : Squash′ A) → Squash′ (P (squash x)) → Squash′ (Σ A (P ∘ [_]))
  from′ (squash′ x) (squash′ y) = squash′ (x , y)

  from : Σ (Squash A) (Squash ∘ P) → Squash (Σ A (P ∘ [_]))
  from (squash x , squash y) = squash (from′ x y)

-- The squash modality commutes with Σ.

commutes-with-Σ : Modality.Commutes-with-Σ (modality {ℓ = ℓ})
commutes-with-Σ = _≃_.is-equivalence Squash-Σ≃Σ-Squash-Squash

-- The squash modality is not left exact.

not-left-exact : ¬ Left-exact (Squash {a = a})
not-left-exact =
  Empty-modal→Is-proposition-◯→¬-Left-exact
    empty-modal Squash-propositional
  where
  open Modality modality

-- The squash modality is not very modal.

not-very-modal : ¬ Very-modal (modality {ℓ = ℓ})
not-very-modal =
  Very-modal modality  →⟨ VM.left-exact modality ⟩
  Left-exact Squash    →⟨ not-left-exact ⟩□
  ⊥                    □

-- The squash modality is not accessibility-modal.

not-accessibility-modal :
  ¬ Modality.Accessibility-modal (modality {ℓ = ℓ})
not-accessibility-modal =
  Is-proposition-◯→¬-Accessibility-modal Squash-propositional
  where
  open Modality modality

------------------------------------------------------------------------
-- Squash preserves all kinds of functions

private

  -- Squash preserves functions.

  Squash-cong-→ : (A → B) → Squash A → Squash B
  Squash-cong-→ A→B x = x >>=′ return ∘ A→B

-- If A and B are logically equivalent, then Squash A and Squash B are
-- equivalent.

Squash-cong-⇔ : A ⇔ B → Squash A ≃ Squash B
Squash-cong-⇔ A⇔B = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = Squash-cong-→ (_⇔_.to   A⇔B)
      ; from = Squash-cong-→ (_⇔_.from A⇔B)
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  })

-- If there is a split surjection from A to B, then Squash A and
-- Squash B are equivalent.

Squash-cong-↠ : A ↠ B → Squash A ≃ Squash B
Squash-cong-↠ = Squash-cong-⇔ ∘ _↠_.logical-equivalence

private

  -- Some lemmas used in Squash-cong.

  Squash-cong-↔ : A ↔ B → Squash A ↔ Squash B
  Squash-cong-↔ =
    from-isomorphism ∘ Squash-cong-⇔ ∘ _↔_.logical-equivalence

  Squash-cong-≃ : A ≃ B → Squash A ≃ Squash B
  Squash-cong-≃ = Squash-cong-⇔ ∘ _≃_.logical-equivalence

  Squash-cong-≃ᴱ : A ≃ᴱ B → Squash A ≃ᴱ Squash B
  Squash-cong-≃ᴱ =
    from-isomorphism ∘ Squash-cong-⇔ ∘ _≃ᴱ_.logical-equivalence

  Squash-cong-↣ : A ↣ B → Squash A ↣ Squash B
  Squash-cong-↣ A↣B = record
    { to        = Squash-cong-→ (_↣_.to A↣B)
    ; injective = λ _ → refl _
    }

  Squash-cong-Embedding :
    Embedding A B → Embedding (Squash A) (Squash B)
  Squash-cong-Embedding A↣B = record
    { to           = Squash-cong-→ (Embedding.to A↣B)
    ; is-embedding = λ x y →
        _≃_.is-equivalence $
        _↠_.from (Eq.≃↠⇔ (⇒≡ 1 Squash-propositional)
                         (⇒≡ 1 Squash-propositional))
          (record { from = λ _ → refl _ })
    }

-- Squash preserves all kinds of functions.

Squash-cong : A ↝[ k ] B → Squash A ↝[ k ] Squash B
Squash-cong {k = implication}         = Squash-cong-→
Squash-cong {k = logical-equivalence} = from-isomorphism ∘ Squash-cong-⇔
Squash-cong {k = injection}           = Squash-cong-↣
Squash-cong {k = embedding}           = Squash-cong-Embedding
Squash-cong {k = surjection}          = from-isomorphism ∘ Squash-cong-↠
Squash-cong {k = bijection}           = Squash-cong-↔
Squash-cong {k = equivalence}         = Squash-cong-≃
Squash-cong {k = equivalenceᴱ}        = Squash-cong-≃ᴱ

------------------------------------------------------------------------
-- Some isomorphisms

-- Squash ⊤ is isomorphic to ⊤.

Squash-⊤↔⊤ : Squash ⊤ ↔ ⊤
Squash-⊤↔⊤ = record
  { surjection = record
    { logical-equivalence = record
      { from = λ _ → [ _ ]
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

-- Squash ⊥ is isomorphic to ⊥.

Squash-⊥↔⊥ : Squash (⊥ {ℓ = ℓ}) ↔ ⊥ {ℓ = ℓ}
Squash-⊥↔⊥ = record
  { surjection = record
    { logical-equivalence = record
      { to   = empty-modal .proj₁
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ _ → refl _
  }

-- Squash commutes with _×_.
--
-- This lemma was suggested by Jesper Cockx.

Squash-×↔× : Squash (A × B) ↔ Squash A × Squash B
Squash-×↔× = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ p → Squash-cong proj₁ p , Squash-cong proj₂ p
      ; from = λ (x , y) → x >>=′ λ x → y >>=′ λ y → return (x , y)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- Squash commutes with ↑ ℓ.

Squash-↑↔↑ : Squash (↑ ℓ A) ↔ ↑ ℓ (Squash A)
Squash-↑↔↑ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { x .lower → Squash-cong lower x }
      ; from = λ (lift x) → Squash-cong lift x
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

------------------------------------------------------------------------
-- Some properties

-- Squash A implies ¬ ¬ A.

Squash→¬¬ : Squash A → ¬ ¬ A
Squash→¬¬ {A} = curry (
  Squash A × ¬ A  ↝⟨ uncurry (flip Squash-cong) ⟩
  Squash ⊥        ↔⟨ Squash-⊥↔⊥ ⟩□
  ⊥               □)

-- It is not in general the case that [ x ] ≡ [ y ] implies
-- Squash (x ≡ y).

¬-[]≡[]→Squash-≡ :
  ¬ ({A : Type a} {x y : A} → [ x ] ≡ [ y ] → Squash (x ≡ y))
¬-[]≡[]→Squash-≡ {a} =
  ({A : Type a} {x y : A} → [ x ] ≡ [ y ] → Squash (x ≡ y))  ↝⟨ _$ refl _ ⟩
  Squash (lift true ≡ lift false)                            ↝⟨ Squash-cong (cong lower) ⟩
  Squash (true ≡ false)                                      ↝⟨ Squash-cong Bool.true≢false ⟩
  Squash ⊥                                                   ↔⟨ Squash-⊥↔⊥ ⟩□
  ⊥                                                          □

-- [_] is split surjective for decided types.

Split-surjective-[] : Dec A → Split-surjective {A = A} [_]
Split-surjective-[] (yes x) _ = x , refl _
Split-surjective-[] (no ¬x) x =
  ⊥-elim (_↔_.to Squash-⊥↔⊥ (Squash-cong ¬x x))

------------------------------------------------------------------------
-- Some lemmas related to stability

-- Very stable types are stable.

Very-stable→Stable :
  ∀ n →
  For-iterated-equality n Very-stable A →
  For-iterated-equality n Stable A
Very-stable→Stable n =
  For-iterated-equality-cong₁ _ n _≃_.to

-- Very-stable is propositional (assuming extensionality).

Very-stable-propositional :
  {A : Type a} →
  Extensionality a a →
  Is-proposition (Very-stable A)
Very-stable-propositional ext =
  Eq.left-closure ext 0 Squash-propositional

private

  -- The previous result can be generalised.

  For-iterated-equality-Very-stable-propositional :
    {A : Type a} →
    Extensionality a a →
    ∀ n → Is-proposition (For-iterated-equality n Very-stable A)
  For-iterated-equality-Very-stable-propositional ext n =
    H-level-For-iterated-equality ext 1 n
      (Very-stable-propositional ext)

-- A type is very stable if and only if [_] is an equivalence for that
-- type.

Very-stable↔Is-equivalence-[] :
  {A : Type a} →
  Very-stable A ↝[ a ∣ a ] Is-equivalence {A = A} [_]
Very-stable↔Is-equivalence-[] =
  generalise-ext?-prop
    (record { from = inverse ∘ Eq.⟨ _ ,_⟩
            ; to   = λ s →
                _≃_.is-equivalence $
                Eq.with-other-function
                  (inverse s)
                  [_]
                  (λ _ → refl _)
            })
    Very-stable-propositional
    Is-equivalence-propositional

-- A type is very stable if and only if it is a stable proposition.

Very-stable↔Stable×Is-proposition :
  {A : Type a} →
  Very-stable A ↝[ a ∣ a ] Stable A × Is-proposition A
Very-stable↔Stable×Is-proposition {A} ext =
  Very-stable A               ↝⟨ Very-stable↔Is-equivalence-[] ext ⟩
  Is-equivalence {A = A} [_]  ↝⟨ inverse-ext? Modal≃Is-equivalence-η ext ⟩□
  Modal A                     □
  where
  open Modality modality

-- If A has h-level 1 + n and is stable "n levels up", then A is very
-- stable "n levels up".

Stable→H-level-suc→Very-stable :
  ∀ n →
  For-iterated-equality n Stable A → H-level (suc n) A →
  For-iterated-equality n Very-stable A
Stable→H-level-suc→Very-stable {A} n = curry (
  For-iterated-equality n Stable A × H-level (suc n) A            ↝⟨ (∃-cong λ _ → lemma) ⟩

  For-iterated-equality n Stable A ×
  For-iterated-equality n Is-proposition A                        ↝⟨ For-iterated-equality-commutes-× n _ ⟩

  For-iterated-equality n (λ A → Stable A × Is-proposition A) A   ↝⟨ For-iterated-equality-cong₁ _ n $
                                                                     uncurry (curry $ _⇔_.from (Very-stable↔Stable×Is-proposition _)) ⟩
  For-iterated-equality n Very-stable A                           □)
  where
  lemma =
    H-level (suc n) A                         ↝⟨ _⇔_.to H-level⇔H-level′ ⟩
    H-level′ (suc n) A                        ↝⟨ inverse-ext? (For-iterated-equality-For-iterated-equality n 1) _ ⟩
    For-iterated-equality n (H-level′ 1) A    ↝⟨ For-iterated-equality-cong₁ _ n $
                                                 _⇔_.from (H-level⇔H-level′ {n = 1}) ⟩□
    For-iterated-equality n Is-proposition A  □

-- Types with h-level n are very stable "n levels up".

H-level→Very-stable :
  ∀ n → H-level n A → For-iterated-equality n Very-stable A
H-level→Very-stable {A} n =
  H-level n A                            ↝⟨ _⇔_.to H-level⇔H-level′ ⟩
  H-level′ n A                           ↝⟨ For-iterated-equality-cong₁ _ n Contractible→Very-stable ⟩□
  For-iterated-equality n Very-stable A  □
  where
  Contractible→Very-stable :
    ∀ {A} → Contractible A → Very-stable A
  Contractible→Very-stable c =
    _⇔_.from (Very-stable↔Stable×Is-proposition _)
      ( (λ _ → proj₁ c)
      , mono₁ 0 c
      )

-- If A is very stable, then [_] {A = A} is an embedding.

Very-stable→Is-embedding-[] :
  Very-stable A → Is-embedding {A = A} [_]
Very-stable→Is-embedding-[] {A} =
  Very-stable A             →⟨ _⇔_.to (Very-stable↔Stable×Is-proposition _) ⟩
  Modal A                   →⟨ Modal→Is-embedding-η ⟩□
  Is-embedding {A = A} [_]  □
  where
  open Modality modality

-- If A is very stable, then [_] {A = A} is split surjective.

Very-stable→Split-surjective-[] :
  Very-stable A → Split-surjective {A = A} [_]
Very-stable→Split-surjective-[] {A} =
  Very-stable A         ↝⟨ Very-stable↔Is-equivalence-[] _ ⟩
  Is-equivalence [_]    ↝⟨ (λ hyp → _↠_.split-surjective $ _≃_.surjection $ Eq.⟨ _ , hyp ⟩) ⟩
  Split-surjective [_]  □

-- Types that are stable for double negation are stable for Squash.

¬¬-Stable→Stable : (¬ ¬ A → A) → Stable A
¬¬-Stable→Stable = EM.¬¬-stable→Stable

-- Types for which it is known whether or not they are inhabited are
-- stable.

Dec→Stable : Dec A → Stable A
Dec→Stable = EM.Dec→Stable

-- Every type is stable in the double negation monad.

¬¬-Stable : ¬¬ Stable A
¬¬-Stable = DN.map′ Dec→Stable DN.excluded-middle

-- Bool is not very stable. (But it is stable, see Dec→Stable above.)

¬-Very-stable-Bool : ¬ Very-stable Bool
¬-Very-stable-Bool =
  Very-stable Bool     ↝⟨ proj₂ ∘ Very-stable↔Stable×Is-proposition _ ⟩
  Is-proposition Bool  ↝⟨ ¬-Bool-propositional ⟩□
  ⊥                    □

-- If equality is decidable for A, then equality is very stable for A.

Decidable-equality→Very-stable-≡ :
  Decidable-equality A → Very-stable-≡ A
Decidable-equality→Very-stable-≡ {A} =
  Decidable-equality A  →⟨ EM.Decidable-equality→Separated ⟩
  Separated A           →⟨ (λ hyp x y → _⇔_.from (Very-stable↔Stable×Is-proposition _) (hyp x y)) ⟩□
  Very-stable-≡ A       □
  where
  open Modality modality

----------------------------------------------------------------------
-- Preservation lemmas

-- Stable preserves some kinds of functions (those that are
-- "symmetric"), possibly assuming extensionality.

Stable-cong :
  {A : Type a} {B : Type b} →
  Extensionality? ⌊ k ⌋-sym (a ⊔ b) (a ⊔ b) →
  A ↝[ ⌊ k ⌋-sym ] B → Stable A ↝[ ⌊ k ⌋-sym ] Stable B
Stable-cong {k} {A} {B} ext A↝B =
  Stable A        ↔⟨⟩
  (Squash A → A)  ↝⟨ →-cong ext (Squash-cong A↝B) A↝B ⟩
  (Squash B → B)  ↔⟨⟩
  Stable B        □

-- A kind of map function for Stable.

Stable-map : A ⇔ B → Stable A → Stable B
Stable-map = _⇔_.to ∘ Stable-cong _

-- A kind of map function for Very-stable.

Very-stable-map :
  A ↠ B → Very-stable A → Very-stable B
Very-stable-map {A} {B} A↠B s =
  _↠_.from (Eq.≃↠⇔ Squash-propositional B-prop)
    (record { from = [_]
            ; to   = Squash B  ↝⟨ Squash-cong (_↠_.from A↠B) ⟩
                     Squash A  ↔⟨ s ⟩
                     A         ↝⟨ _↠_.to A↠B ⟩□
                     B         □
            })
  where
  A-prop : Is-proposition A
  A-prop = proj₂ $ Very-stable↔Stable×Is-proposition _ s

  B-prop : Is-proposition B
  B-prop = H-level.respects-surjection A↠B 1 A-prop

-- Very-stable preserves equivalences (assuming extensionality).

Very-stable-cong :
  {A : Type a} {B : Type b} →
  Extensionality? k (a ⊔ b) (a ⊔ b) →
  A ≃ B → Very-stable A ↝[ k ] Very-stable B
Very-stable-cong {A} {B} ext A≃B =
  Very-stable A  ↔⟨⟩
  Squash A ≃ A   ↝⟨ generalise-ext?
                      (Eq.≃-preserves-⇔ (Squash-cong A≃B) A≃B)
                      (λ ext →
                         let eq = Eq.≃-preserves ext (Squash-cong-≃ A≃B) A≃B in
                         _≃_.right-inverse-of eq , _≃_.left-inverse-of eq)
                      ext ⟩
  Squash B ≃ B   ↔⟨⟩
  Very-stable B  □

------------------------------------------------------------------------
-- Closure properties

-- Squash A is very stable.

Very-stable-Squash : Very-stable (Squash A)
Very-stable-Squash {A} =  $⟨ Modal-◯ ⟩
  Modal (Squash A)        →⟨ _⇔_.from (Very-stable↔Stable×Is-proposition _) ⟩□
  Very-stable (Squash A)  □
  where
  open Modality modality

-- ⊤ is very stable.

Very-stable-⊤ : Very-stable ⊤
Very-stable-⊤ = Eq.↔⇒≃ Squash-⊤↔⊤

-- ⊥ is very stable.

Very-stable-⊥ : Very-stable (⊥ {ℓ = ℓ})
Very-stable-⊥ = Eq.↔⇒≃ Squash-⊥↔⊥

-- Stable is closed under Π A.

Stable-Π :
  (∀ x → Stable (P x)) →
  Stable ((x : A) → P x)
Stable-Π {P} s =
  Squash (∀ x → P x)    ↝⟨ (λ s x → Squash-cong (_$ x) s) ⟩
  (∀ x → Squash (P x))  ↝⟨ ∀-cong _ s ⟩□
  (∀ x → P x)           □

-- Very-stable is closed under Π A (assuming extensionality).

Very-stable-Π :
  {A : Type a} {P : A → Type p} →
  Extensionality a p →
  (∀ x → Very-stable (P x)) →
  Very-stable ((x : A) → P x)
Very-stable-Π {P} ext s =
  _⇔_.from (Very-stable↔Stable×Is-proposition _)
    ( Stable-Π (Very-stable→Stable 0 ∘ s)
    , (Π-closure ext 1 λ x →
       H-level-cong _ 1 (s x) Squash-propositional)
    )

-- Stable is closed under _×_.

Stable-× : Stable A → Stable B → Stable (A × B)
Stable-× {A} {B} s₁ s₂ =
  Squash (A × B)       ↔⟨ Squash-×↔× ⟩
  Squash A × Squash B  ↝⟨ s₁ ×-cong s₂ ⟩□
  A × B                □

-- Very-stable is closed under _×_.

Very-stable-× : Very-stable A → Very-stable B → Very-stable (A × B)
Very-stable-× s₁ s₂ =
  _⇔_.from (Very-stable↔Stable×Is-proposition _)
    ( Stable-× (Very-stable→Stable 0 s₁) (Very-stable→Stable 0 s₂)
    , ×-closure 1 (H-level-cong _ 1 s₁ Squash-propositional)
                  (H-level-cong _ 1 s₂ Squash-propositional)
    )

-- Stable is closed under ↑ ℓ.

Stable-↑ : Stable A → Stable (↑ ℓ A)
Stable-↑ {A} s =
  Squash (↑ _ A)  ↔⟨ Squash-↑↔↑ ⟩
  ↑ _ (Squash A)  ↝⟨ ↑-cong s ⟩□
  ↑ _ A           □

-- Very-stable is closed under ↑ ℓ.

Very-stable-↑ : Very-stable A → Very-stable (↑ ℓ A)
Very-stable-↑ {A} s =
  Squash (↑ _ A)  ↔⟨ Squash-↑↔↑ ⟩
  ↑ _ (Squash A)  ↝⟨ ↑-cong s ⟩□
  ↑ _ A           □

-- If A is very stable, then equality is very stable for A.

Very-stable→Very-stable-≡ :
  ∀ n →
  For-iterated-equality n       Very-stable A →
  For-iterated-equality (suc n) Very-stable A
Very-stable→Very-stable-≡ {A} n =
  For-iterated-equality n Very-stable A        →⟨ For-iterated-equality-cong₁ _ n $
                                                  _⇔_.to (Very-stable↔Stable×Is-proposition _) ⟩
  For-iterated-equality n Modal A              →⟨ Modalⁿ→Modal¹⁺ⁿ n ⟩
  For-iterated-equality (suc n) Modal A        →⟨ For-iterated-equality-cong₁ _ (suc n) $
                                                  _⇔_.from (Very-stable↔Stable×Is-proposition _) ⟩□
  For-iterated-equality (suc n) Very-stable A  □
  where
  open Modality modality

private

  -- Some examples showing how Very-stable→Very-stable-≡ can be
  -- used.

  -- Equalities between erased values are very stable.

  Very-stable-≡₀ : Very-stable-≡ (Squash A)
  Very-stable-≡₀ = Very-stable→Very-stable-≡ 0 Very-stable-Squash

  -- Equalities between equalities between erased values are very
  -- stable.

  Very-stable-≡₁ : For-iterated-equality 2 Very-stable (Squash A)
  Very-stable-≡₁ = Very-stable→Very-stable-≡ 1 Very-stable-≡₀

  -- And so on…

private

  -- A lemma.

  For-iterated-equality-Is-proposition↔H-level′-suc :
    {A : Type a} →
    ∀ n →
    For-iterated-equality n Is-proposition A ↝[ a ∣ a ]
    H-level′ (suc n) A
  For-iterated-equality-Is-proposition↔H-level′-suc {A} n ext =
    For-iterated-equality n Is-proposition A  ↝⟨ For-iterated-equality-cong₁ ext n (H-level↔H-level′ {n = 1} ext) ⟩
    For-iterated-equality n (H-level′ 1) A    ↝⟨ For-iterated-equality-For-iterated-equality n 1 ext ⟩□
    H-level′ (suc n) A                        □

-- If A is "stable 1 + n levels up", then H-level′ (suc n) A is
-- stable.

Stable-H-level′ :
  ∀ n →
  For-iterated-equality (suc n) Stable A →
  Stable (H-level′ (suc n) A)
Stable-H-level′ {A} n =
  For-iterated-equality (suc n) Stable A               ↝⟨ inverse-ext? (For-iterated-equality-For-iterated-equality n 1) _ ⟩
  For-iterated-equality n Stable-≡ A                   ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
  For-iterated-equality n (Stable ∘ Is-proposition) A  ↝⟨ For-iterated-equality-commutes-← _ Stable n Stable-Π ⟩
  Stable (For-iterated-equality n Is-proposition A)    ↝⟨ Stable-map (For-iterated-equality-Is-proposition↔H-level′-suc n _) ⟩□
  Stable (H-level′ (suc n) A)                          □
  where
  lemma : ∀ {A} → Stable-≡ A → Stable (Is-proposition A)
  lemma s =
    Stable-Π λ _ →
    Stable-Π λ _ →
    s _ _

-- If A is "stable 1 + n levels up", then H-level (suc n) A is
-- stable.

Stable-H-level :
  ∀ n →
  For-iterated-equality (suc n) Stable A →
  Stable (H-level (suc n) A)
Stable-H-level {A} n =
  For-iterated-equality (suc n) Stable A  ↝⟨ Stable-H-level′ n ⟩
  Stable (H-level′ (suc n) A)             ↝⟨ Stable-map (record { to = inverse-ext? H-level↔H-level′ _; from = H-level↔H-level′ _ }) ⟩□
  Stable (H-level (suc n) A)              □

-- If A is "very stable n levels up", then H-level′ n A is very stable
-- (assuming extensionality).

Very-stable-H-level′ :
  {A : Type a} →
  Extensionality a a →
  ∀ n →
  For-iterated-equality n Very-stable A →
  Very-stable (H-level′ n A)
Very-stable-H-level′ {A} ext n =
  For-iterated-equality n Very-stable A  →⟨ For-iterated-equality-cong₁ _ n $
                                            _⇔_.to (Very-stable↔Stable×Is-proposition _) ⟩
  For-iterated-equality n Modal A        →⟨ Modal-H-level′ ext n ⟩
  Modal (H-level′ n A)                   →⟨ _⇔_.from (Very-stable↔Stable×Is-proposition _) ⟩□
  Very-stable (H-level′ n A)             □
  where
  open Modality modality

-- If A is "very stable n levels up", then H-level n A is very stable
-- (assuming extensionality).

Very-stable-H-level :
  {A : Type a} →
  Extensionality a a →
  ∀ n →
  For-iterated-equality n Very-stable A →
  Very-stable (H-level n A)
Very-stable-H-level {A} ext n =
  For-iterated-equality n Very-stable A  →⟨ For-iterated-equality-cong₁ _ n $
                                            _⇔_.to (Very-stable↔Stable×Is-proposition _) ⟩
  For-iterated-equality n Modal A        →⟨ Modal-H-level ext n ⟩
  Modal (H-level n A)                    →⟨ _⇔_.from (Very-stable↔Stable×Is-proposition _) ⟩□
  Very-stable (H-level n A)              □
  where
  open Modality modality

-- If equality is stable for A and B, then it is stable for A ⊎ B.

Stable-≡-⊎ :
  ∀ n →
  For-iterated-equality (suc n) Stable A →
  For-iterated-equality (suc n) Stable B →
  For-iterated-equality (suc n) Stable (A ⊎ B)
Stable-≡-⊎ n sA sB =
  For-iterated-equality-⊎-suc
    n
    (Stable-map ∘ from-isomorphism)
    (Very-stable→Stable 0 Very-stable-⊥)
    (For-iterated-equality-↑ _ (suc n) (Stable-map ∘ from-isomorphism) sA)
    (For-iterated-equality-↑ _ (suc n) (Stable-map ∘ from-isomorphism) sB)

-- If equality is very stable for A and B, then it is very stable
-- for A ⊎ B.

Very-stable-≡-⊎ :
  ∀ n →
  For-iterated-equality (suc n) Very-stable A →
  For-iterated-equality (suc n) Very-stable B →
  For-iterated-equality (suc n) Very-stable (A ⊎ B)
Very-stable-≡-⊎ n sA sB =
  For-iterated-equality-⊎-suc
    n
    lemma
    Very-stable-⊥
    (For-iterated-equality-↑ _ (suc n) lemma sA)
    (For-iterated-equality-↑ _ (suc n) lemma sB)
  where
  lemma : A ↔ B → Very-stable A → Very-stable B
  lemma = Very-stable-cong _ ∘ from-isomorphism

-- If equality is stable for A, then it is stable for List A.

Stable-≡-List :
  ∀ n →
  For-iterated-equality (suc n) Stable A →
  For-iterated-equality (suc n) Stable (List A)
Stable-≡-List = EM.Stable-≡-List

-- If equality is very stable for A, then it is very stable for
-- List A.

Very-stable-≡-List :
  ∀ n →
  For-iterated-equality (suc n) Very-stable A →
  For-iterated-equality (suc n) Very-stable (List A)
Very-stable-≡-List {A} n =
  For-iterated-equality (suc n) Very-stable A         →⟨ For-iterated-equality-cong₁ _ (suc n) $
                                                         _⇔_.to (Very-stable↔Stable×Is-proposition _) ⟩
  For-iterated-equality (suc n) Modal A               →⟨ EM.Separated-List n ⟩
  For-iterated-equality (suc n) Modal (List A)        →⟨ For-iterated-equality-cong₁ _ (suc n) $
                                                         _⇔_.from (Very-stable↔Stable×Is-proposition _) ⟩□
  For-iterated-equality (suc n) Very-stable (List A)  □
  where
  open Modality modality

----------------------------------------------------------------------
-- Simple corollaries or variants of results above

-- A generalisation of Stable-Π.

Stable-Πⁿ :
  {A : Type a} {P : A → Type p} →
  Extensionality a p →
  ∀ n →
  (∀ x → For-iterated-equality n Stable (P x)) →
  For-iterated-equality n Stable ((x : A) → P x)
Stable-Πⁿ ext n =
  For-iterated-equality-Π
    ext
    n
    (Stable-map ∘ from-isomorphism)
    Stable-Π

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

-- A generalisation of Stable-×.

Stable-×ⁿ :
  ∀ n →
  For-iterated-equality n Stable A →
  For-iterated-equality n Stable B →
  For-iterated-equality n Stable (A × B)
Stable-×ⁿ n =
  For-iterated-equality-×
    n
    (Stable-map ∘ from-isomorphism)
    Stable-×

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

-- A generalisation of Stable-↑.

Stable-↑ⁿ :
  ∀ n →
  For-iterated-equality n Stable A →
  For-iterated-equality n Stable (↑ ℓ A)
Stable-↑ⁿ n =
  For-iterated-equality-↑ _ n (Stable-map ∘ from-isomorphism)

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
