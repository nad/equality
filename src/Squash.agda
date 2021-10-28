------------------------------------------------------------------------
-- Squashing
------------------------------------------------------------------------

{-# OPTIONS --cubical --prop --safe #-}

import Equality.Path as P

module Squash {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Double-negation equality-with-J as DN using (¬¬_)
open import Embedding equality-with-J using (Embedding; Is-embedding)
open import Equality.Decision-procedures equality-with-J
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased equality-with-J using (_≃ᴱ_)
open import For-iterated-equality equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as Trunc using (∥_∥)
open import Injection equality-with-J using (_↣_)
open import Monad equality-with-J
open import Surjection equality-with-J using (_↠_; Split-surjective)

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
_>>=′_ {A = A} {B = B} (squash x) f = squash (lemma x)
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
      { to   = λ x → ⊥-in-prop→⊥ (Squash-⊥→⊥-in-prop x)
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ _ → refl _
  }
  where

  -- An empty type in Prop.

  data ⊥-in-prop : Prop where

  -- Squash ⊥ implies ⊥-in-prop.

  Squash-⊥→⊥-in-prop : Squash (⊥ {ℓ = ℓ}) → ⊥-in-prop
  Squash-⊥→⊥-in-prop [ () ]

  -- ⊥-in-prop implies ⊥.

  ⊥-in-prop→⊥ : ⊥-in-prop → ⊥ {ℓ = ℓ}
  ⊥-in-prop→⊥ ()

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

-- ∥ A ∥ implies Squash A.

∥∥→Squash : ∥ A ∥ → Squash A
∥∥→Squash = Trunc.rec Squash-propositional [_]

-- Squash A implies ¬ ¬ A.

Squash→¬¬ : Squash A → ¬ ¬ A
Squash→¬¬ {A = A} = curry (
  Squash A × ¬ A  ↝⟨ uncurry (flip Squash-cong) ⟩
  Squash ⊥        ↔⟨ Squash-⊥↔⊥ ⟩□
  ⊥               □)

-- It is not in general the case that [ x ] ≡ [ y ] implies
-- Squash (x ≡ y).

¬-[]≡[]→Squash-≡ :
  ¬ ({A : Type a} {x y : A} → [ x ] ≡ [ y ] → Squash (x ≡ y))
¬-[]≡[]→Squash-≡ {a = a} =
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
    (λ ext → Eq.propositional ext _)

-- A type is very stable if and only if it is a stable proposition.

Very-stable↔Stable×Is-proposition :
  {A : Type a} →
  Very-stable A ↝[ a ∣ a ] Stable A × Is-proposition A
Very-stable↔Stable×Is-proposition =
  generalise-ext?-prop
    (record { to   = λ s → _≃_.to s
                         , H-level-cong _ 1 s Squash-propositional
            ; from = λ (s , prop) →
                _↠_.from (Eq.≃↠⇔ Squash-propositional prop)
                  (record { to = s; from = [_] })
            })
    Very-stable-propositional
    (λ ext →
       [inhabited⇒+]⇒+ 0 λ (_ , prop) →
       ×-closure 1
         (Π-closure ext 1 (λ _ → prop))
         (H-level-propositional ext 1))

-- If A has h-level 1 + n and is stable "n levels up", then A is very
-- stable "n levels up".

Stable→H-level-suc→Very-stable :
  ∀ n →
  For-iterated-equality n Stable A → H-level (suc n) A →
  For-iterated-equality n Very-stable A
Stable→H-level-suc→Very-stable {A = A} n = curry (
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
H-level→Very-stable {A = A} n =
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
Very-stable→Is-embedding-[] s x y =
  _≃_.is-equivalence (
    x ≡ y          ↝⟨ inverse $ Eq.≃-≡ $ Eq.⟨ _ , Very-stable↔Is-equivalence-[] _ s ⟩ ⟩□
    [ x ] ≡ [ y ]  □)

-- If A is very stable, then [_] {A = A} is split surjective.

Very-stable→Split-surjective-[] :
  Very-stable A → Split-surjective {A = A} [_]
Very-stable→Split-surjective-[] {A = A} =
  Very-stable A         ↝⟨ Very-stable↔Is-equivalence-[] _ ⟩
  Is-equivalence [_]    ↝⟨ (λ hyp → _↠_.split-surjective $ _≃_.surjection $ Eq.⟨ _ , hyp ⟩) ⟩
  Split-surjective [_]  □

-- Types that are stable for double negation are stable for Squash.

¬¬-Stable→Stable : (¬ ¬ A → A) → Stable A
¬¬-Stable→Stable ¬¬-Stable x = ¬¬-Stable (Squash→¬¬ x)

-- Types for which it is known whether or not they are inhabited are
-- stable.

Dec→Stable : Dec A → Stable A
Dec→Stable (yes x) _ = x
Dec→Stable (no ¬x) x with () ← Squash→¬¬ x ¬x

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
Decidable-equality→Very-stable-≡ dec _ _ =
  _⇔_.from (Very-stable↔Stable×Is-proposition _)
    ( Dec→Stable (dec _ _)
    , decidable⇒set dec
    )

----------------------------------------------------------------------
-- Preservation lemmas

-- Stable preserves some kinds of functions (those that are
-- "symmetric"), possibly assuming extensionality.

Stable-cong :
  {A : Type a} {B : Type b} →
  Extensionality? ⌊ k ⌋-sym (a ⊔ b) (a ⊔ b) →
  A ↝[ ⌊ k ⌋-sym ] B → Stable A ↝[ ⌊ k ⌋-sym ] Stable B
Stable-cong {k = k} {A = A} {B = B} ext A↝B =
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
Very-stable-map {A = A} {B = B} A↠B s =
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
Very-stable-cong {A = A} {B = B} ext A≃B =
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
Very-stable-Squash =
  _⇔_.from (Very-stable↔Stable×Is-proposition _)
    ( _>>= id
    , Squash-propositional
    )

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
Stable-Π {P = P} s =
  Squash (∀ x → P x)    ↝⟨ (λ s x → Squash-cong (_$ x) s) ⟩
  (∀ x → Squash (P x))  ↝⟨ ∀-cong _ s ⟩□
  (∀ x → P x)           □

-- Very-stable is closed under Π A (assuming extensionality).

Very-stable-Π :
  {A : Type a} {P : A → Type p} →
  Extensionality a p →
  (∀ x → Very-stable (P x)) →
  Very-stable ((x : A) → P x)
Very-stable-Π {P = P} ext s =
  _⇔_.from (Very-stable↔Stable×Is-proposition _)
    ( Stable-Π (Very-stable→Stable 0 ∘ s)
    , (Π-closure ext 1 λ x →
       H-level-cong _ 1 (s x) Squash-propositional)
    )

-- Stable is closed under _×_.

Stable-× : Stable A → Stable B → Stable (A × B)
Stable-× {A = A} {B = B} s₁ s₂ =
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
Stable-↑ {A = A} s =
  Squash (↑ _ A)  ↔⟨ Squash-↑↔↑ ⟩
  ↑ _ (Squash A)  ↝⟨ ↑-cong s ⟩□
  ↑ _ A           □

-- Very-stable is closed under ↑ ℓ.

Very-stable-↑ : Very-stable A → Very-stable (↑ ℓ A)
Very-stable-↑ {A = A} s =
  Squash (↑ _ A)  ↔⟨ Squash-↑↔↑ ⟩
  ↑ _ (Squash A)  ↝⟨ ↑-cong s ⟩□
  ↑ _ A           □

-- If A is very stable, then equality is very stable for A.

Very-stable→Very-stable-≡ :
  ∀ n →
  For-iterated-equality n       Very-stable A →
  For-iterated-equality (suc n) Very-stable A
Very-stable→Very-stable-≡ {A = A} n =
  For-iterated-equality n Very-stable A        ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
  For-iterated-equality n Very-stable-≡ A      ↝⟨ For-iterated-equality-For-iterated-equality n 1 _ ⟩□
  For-iterated-equality (suc n) Very-stable A  □
  where
  lemma : ∀ {A} → Very-stable A → Very-stable-≡ A
  lemma {A = A} s x y =
    _⇔_.from (Very-stable↔Stable×Is-proposition _)
      ( (Squash (x ≡ y)        ↝⟨ const prop ⟩
         Is-proposition A      ↝⟨ +⇒≡ ⟩
         Contractible (x ≡ y)  ↝⟨ proj₁ ⟩□
         x ≡ y                 □)
      , ⇒≡ 1 prop
      )
    where
    prop : Is-proposition A
    prop = proj₂ $ _⇔_.to (Very-stable↔Stable×Is-proposition _) s

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
  For-iterated-equality-Is-proposition↔H-level′-suc {A = A} n ext =
    For-iterated-equality n Is-proposition A  ↝⟨ For-iterated-equality-cong₁ ext n (H-level↔H-level′ {n = 1} ext) ⟩
    For-iterated-equality n (H-level′ 1) A    ↝⟨ For-iterated-equality-For-iterated-equality n 1 ext ⟩□
    H-level′ (suc n) A                        □

-- If A is "stable 1 + n levels up", then H-level′ (suc n) A is
-- stable.

Stable-H-level′ :
  ∀ n →
  For-iterated-equality (suc n) Stable A →
  Stable (H-level′ (suc n) A)
Stable-H-level′ {A = A} n =
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
Stable-H-level {A = A} n =
  For-iterated-equality (suc n) Stable A  ↝⟨ Stable-H-level′ n ⟩
  Stable (H-level′ (suc n) A)             ↝⟨ Stable-map (record { to = inverse-ext? H-level↔H-level′ _; from = H-level↔H-level′ _ }) ⟩□
  Stable (H-level (suc n) A)              □

-- If A is "very stable 1 + n levels up", then H-level′ (suc n) A is
-- very stable (assuming extensionality).

Very-stable-H-level′ :
  {A : Type a} →
  Extensionality a a →
  ∀ n →
  For-iterated-equality (suc n) Very-stable A →
  Very-stable (H-level′ (suc n) A)
Very-stable-H-level′ {A = A} ext n =
  For-iterated-equality (suc n) Very-stable A               ↝⟨ inverse-ext? (For-iterated-equality-For-iterated-equality n 1) _ ⟩
  For-iterated-equality n Very-stable-≡ A                   ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
  For-iterated-equality n (Very-stable ∘ Is-proposition) A  ↝⟨ For-iterated-equality-commutes-← _ Very-stable n (Very-stable-Π ext) ⟩
  Very-stable (For-iterated-equality n Is-proposition A)    ↝⟨ Very-stable-map (For-iterated-equality-Is-proposition↔H-level′-suc n ext) ⟩□
  Very-stable (H-level′ (suc n) A)                          □
  where
  lemma : ∀ {A} → Very-stable-≡ A → Very-stable (Is-proposition A)
  lemma s =
    Very-stable-Π ext λ _ →
    Very-stable-Π ext λ _ →
    s _ _

-- If A is "very stable 1 + n levels up", then H-level (suc n) A is
-- very stable (assuming extensionality).

Very-stable-H-level :
  {A : Type a} →
  Extensionality a a →
  ∀ n →
  For-iterated-equality (suc n) Very-stable A →
  Very-stable (H-level (suc n) A)
Very-stable-H-level {A = A} ext n =
  For-iterated-equality (suc n) Very-stable A  ↝⟨ Very-stable-H-level′ ext n ⟩
  Very-stable (H-level′ (suc n) A)             ↝⟨ Very-stable-cong _ (inverse $ H-level↔H-level′ ext) ⟩□
  Very-stable (H-level (suc n) A)              □

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
Stable-≡-List n =
  For-iterated-equality-List-suc
    n
    (Stable-map ∘ from-isomorphism)
    (Very-stable→Stable 0 $ Very-stable-↑ Very-stable-⊤)
    (Very-stable→Stable 0 Very-stable-⊥)
    Stable-×

-- If equality is very stable for A, then it is very stable for
-- List A.

Very-stable-≡-List :
  ∀ n →
  For-iterated-equality (suc n) Very-stable A →
  For-iterated-equality (suc n) Very-stable (List A)
Very-stable-≡-List n =
  For-iterated-equality-List-suc
    n
    (Very-stable-cong _ ∘ from-isomorphism)
    (Very-stable-↑ Very-stable-⊤)
    Very-stable-⊥
    Very-stable-×

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
