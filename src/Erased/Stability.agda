------------------------------------------------------------------------
-- Stability for Erased
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality

module Erased.Stability
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

import Equality.Path as P
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_)
open import Embedding eq using (Is-embedding)
open import Equality.Decidable-UIP eq
open import Equality.Decision-procedures eq
open import Equality.Path.Isomorphisms eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
import Equivalence P.equality-with-J as PEq
open import Erased eq
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
  using (Surjective)
import List eq as L
import Nat eq as Nat
open import Surjection eq using (_↠_; Split-surjective)

private
  variable
    a ℓ p : Level
    A B   : Set a
    P     : A → Set p
    k x y : A
    n     : ℕ

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

-- Very-stable is propositional.

Very-stable-propositional : Is-proposition (Very-stable A)
Very-stable-propositional = Eq.propositional ext _

-- Very-stable-≡ is propositional.

Very-stable-≡-propositional : Is-proposition (Very-stable-≡ A)
Very-stable-≡-propositional =
  implicit-Π-closure ext 1 λ _ →
  implicit-Π-closure ext 1 λ _ →
  Very-stable-propositional

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

-- If A is very stable, then [_] {A = A} is split surjective.

Very-stable→Split-surjective-[] :
  Very-stable A → Split-surjective ([_] {A = A})
Very-stable→Split-surjective-[] s x =
    Very-stable→Stable s x
  , ([ Very-stable→Stable s x ]  ≡⟨ []-cong [ Very-stable→Stable-[]≡id s ] ⟩∎
     x                           ∎)

-- If A is very stable, then [_] {A = A} is an embedding.

Very-stable→Is-embedding-[] :
  Very-stable A → Is-embedding ([_] {A = A})
Very-stable→Is-embedding-[] {A = A} =
  Very-stable A                      ↔⟨ inverse Trunc.surjective×embedding≃equivalence ⟩
  Surjective [_] × Is-embedding [_]  ↝⟨ proj₂ ⟩□
  Is-embedding [_]                   □

-- Erased A is very stable.

Very-stable-Erased :
  {@0 A : Set a} → Very-stable (Erased A)
Very-stable-Erased {A = A} =
  _≃_.is-equivalence (            $⟨ Erased↔ ⟩
    Erased (Erased A ↔ A)         ↝⟨ (λ hyp → Erased-cong (erased hyp)) ⟩
    Erased (Erased A) ↔ Erased A  ↝⟨ Eq.↔⇒≃ ∘ inverse ⟩□
    Erased A ≃ Erased (Erased A)  □)

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

-- If A is a stable proposition, then A is very stable.

Stable-proposition→Very-stable :
  Stable A → Is-proposition A → Very-stable A
Stable-proposition→Very-stable {A = A} s prop =
  _≃_.is-equivalence (inverse lemma)
  where
  lemma =                             $⟨ s ⟩
    Stable A                          ↝⟨ Stable→Stable⇔ ⟩
    Stable-[ logical-equivalence ] A  ↝⟨ _↠_.from (Eq.≃↠⇔ (H-level-Erased 1 prop) prop) ⟩□
    Stable-[ equivalence ] A          □

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
    Is-proposition (Erased (↑ a Bool))  ↝⟨ H-level-cong _ 1 (Erased-cong Bijection.↑↔) ⟩
    Is-proposition (Erased Bool)        ↔⟨ inverse (Erased-H-level↔H-level {n = 1}) ⟩
    Erased (Is-proposition Bool)        ↝⟨ Erased-cong ¬-Bool-propositional ⟩
    Erased ⊥                            ↔⟨ Erased-⊥↔⊥ ⟩□
    ⊥                                   □

-- Contractible types are very stable.

Contractible→Very-stable :
  Contractible A → Very-stable A
Contractible→Very-stable c =
  Stable-proposition→Very-stable
    (λ _ → proj₁ c)
    (mono₁ 0 c)

-- Equality is very stable for propositions.

Is-proposition→Very-stable-≡ :
  Is-proposition A → Very-stable-≡ A
Is-proposition→Very-stable-≡ prop =
  Contractible→Very-stable (+⇒≡ prop)

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

-- If equality is decidable for A, then equality is very stable for A.

Decidable-equality→Very-stable-≡ :
  Decidable-equality A → Very-stable-≡ A
Decidable-equality→Very-stable-≡ dec =
  Stable-proposition→Very-stable
    (Dec→Stable (dec _ _))
    (decidable⇒set dec)

------------------------------------------------------------------------
-- Preservation lemmas

-- A kind of map function for Stable-[_].

Stable-map :
  A ↝[ k ] B → @0 B ↝[ k ] A → Stable-[ k ] A → Stable-[ k ] B
Stable-map {A = A} {B = B} A↝B B↝A s =
  Erased B  ↝⟨ Erased-cong B↝A ⟩
  Erased A  ↝⟨ s ⟩
  A         ↝⟨ A↝B ⟩□
  B         □

-- A variant of Stable-map.

Stable-map-↔ : A ↔ B → Stable-[ k ] A → Stable-[ k ] B
Stable-map-↔ A↔B =
  Stable-map (from-isomorphism A↔B) (from-isomorphism $ inverse A↔B)

-- Stable preserves some kinds of functions (those that are
-- "symmetric").

Stable-cong : A ↝[ ⌊ k ⌋-sym ] B → Stable A ↝[ ⌊ k ⌋-sym ] Stable B
Stable-cong {A = A} {k = k} {B = B} A↝B =
  Stable A        ↔⟨⟩
  (Erased A → A)  ↝⟨ →-cong (forget-ext? ⌊ k ⌋-sym ext) (Erased-cong A↝B) A↝B ⟩
  (Erased B → B)  ↔⟨⟩
  Stable B        □

-- Stable-[ logical-equivalence ] preserves logical equivalences.

Stable-⇔-cong :
  A ⇔ B →
  Stable-[ logical-equivalence ] A ⇔ Stable-[ logical-equivalence ] B
Stable-⇔-cong {A = A} {B = B} A⇔B =
  Stable-[ logical-equivalence ] A  ↔⟨⟩
  Erased A ⇔ A                      ↝⟨ ⇔-cong-⇔ (Erased-cong A⇔B) A⇔B ⟩
  Erased B ⇔ B                      ↔⟨⟩
  Stable-[ logical-equivalence ] B  □

-- Stable-[ equivalence ] preserves equivalences.

Stable-≃-cong :
  A ≃ B → Stable-[ equivalence ] A ≃ Stable-[ equivalence ] B
Stable-≃-cong {A = A} {B = B} A≃B =
  Stable-[ equivalence ] A  ↔⟨⟩
  Erased A ≃ A              ↝⟨ Eq.≃-preserves ext (Erased-cong A≃B) A≃B ⟩
  Erased B ≃ B              ↔⟨⟩
  Stable-[ equivalence ] B  □

-- Very-stable preserves equivalences.

Very-stable-cong : A ≃ B → Very-stable A ≃ Very-stable B
Very-stable-cong A≃B =
  _↠_.from (Eq.≃↠⇔ (Eq.propositional ext _)
                   (Eq.propositional ext _))
    (record
       { to   = lemma A≃B
       ; from = lemma (inverse A≃B)
       })
  where
  lemma : A ≃ B → Very-stable A → Very-stable B
  lemma {A = A} {B = B} A≃B s = _≃_.is-equivalence $
    Eq.with-other-function
      (B         ↝⟨ inverse A≃B ⟩
       A         ↝⟨ Eq.⟨ [_] , s ⟩ ⟩
       Erased A  ↝⟨ Erased-cong A≃B ⟩□
       Erased B  □)
      [_]
      (λ x →
         [ _≃_.to A≃B (_≃_.from A≃B x) ]  ≡⟨ cong [_] (_≃_.right-inverse-of A≃B x) ⟩∎
         [ x ]                            ∎)

------------------------------------------------------------------------
-- Closure properties

-- ⊤ is very stable.

Very-stable-⊤ : Very-stable ⊤
Very-stable-⊤ =
  Stable-proposition→Very-stable
    (Dec→Stable (yes tt))
    (mono₁ 0 ⊤-contractible)

-- ⊥ is very stable.

Very-stable-⊥ : Very-stable (⊥ {ℓ = ℓ})
Very-stable-⊥ =
  Stable-proposition→Very-stable
    (Dec→Stable (no λ ()))
    ⊥-propositional

-- Stable-[ k ] is closed under Π A.

Stable-Π : (∀ x → Stable-[ k ] (P x)) → Stable-[ k ] ((x : A) → P x)
Stable-Π {k = k} {P = P} s =
  Erased (∀ x → P x)    ↔⟨ Erased-Π↔Π ⟩
  (∀ x → Erased (P x))  ↝⟨ ∀-cong (forget-ext? k ext) s ⟩□
  (∀ x → P x)           □

-- Very-stable is closed under Π A.

Very-stable-Π : (∀ x → Very-stable (P x)) → Very-stable ((x : A) → P x)
Very-stable-Π s = _≃_.is-equivalence $
  inverse $ Stable-Π $ λ x → inverse Eq.⟨ _ , s x ⟩

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

-- Very-stable is closed under W. In fact, W A P is very stable if A
-- is very stable, P does not need to be (pointwise) very stable.

Very-stable-W : Very-stable A → Very-stable (W A P)
Very-stable-W {A = A} {P = P} s =
  _≃_.is-equivalence $
  Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = [_]
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
-- Closure properties related to equality

-- A closure property for _≡_.

Stable→Stable-≡ :
  (s : Stable A) →
  (∀ x → s [ x ] ≡ x) →
  Stable-≡ A
Stable→Stable-≡ s hyp {x = x} {y = y} =
  Erased (x ≡ y)     ↔⟨ Erased-≡↔[]≡[] ⟩
  [ x ] ≡ [ y ]      ↝⟨ cong s ⟩
  s [ x ] ≡ s [ y ]  ↝⟨ (λ eq → trans (sym (hyp x)) (trans eq (hyp y))) ⟩□
  x ≡ y              □

private

  -- If A is very stable, then the types of paths between values of
  -- type A are very stable.

  Very-stable→Very-stable-Path :
    {x y : A} → Very-stable A → Very-stable (x P.≡ y)
  Very-stable→Very-stable-Path {x = x} {y = y} s = _≃_.is-equivalence (
    x P.≡ y           ↝⟨ inverse $ _↔_.from ≃↔≃ $ PEq.≃-≡ $ _↔_.to ≃↔≃ $ Eq.⟨ _ , s ⟩ ⟩
    [ x ] P.≡ [ y ]   ↔⟨ inverse Erased-Path↔Path-[]-[] ⟩□
    Erased (x P.≡ y)  □)

-- If A is very stable, then the types of equalities between values of
-- type A are very stable.

Very-stable→Very-stable-≡ : Very-stable A → Very-stable-≡ A
Very-stable→Very-stable-≡ s {x = x} {y = y} =
  _≃_.is-equivalence $
  Eq.with-other-function
    (x ≡ y             ↔⟨ ≡↔≡ ⟩
     x P.≡ y           ↝⟨ inverse $ Very-stable→Stable (Very-stable→Very-stable-Path s) ⟩
     Erased (x P.≡ y)  ↔⟨ Erased-cong (inverse ≡↔≡) ⟩□
     Erased (x ≡ y)    □)
    [_]
    (λ eq →
      [ _↔_.from ≡↔≡ (_↔_.to ≡↔≡ eq) ]  ≡⟨ cong [_] (_↔_.left-inverse-of ≡↔≡ eq) ⟩∎
      [ eq ]                            ∎)

private

  -- Some examples showing how Very-stable→Very-stable-≡ can be used.

  -- Equalities between erased values are very stable.

  Very-stable-≡₀ : {@0 A : Set a} → Very-stable-≡ (Erased A)
  Very-stable-≡₀ = Very-stable→Very-stable-≡ Very-stable-Erased

  -- Equalities between equalities between erased values are very
  -- stable.

  Very-stable-≡₁ :
    {@0 A : Set a} {x y : Erased A} →
    Very-stable-≡ (x ≡ y)
  Very-stable-≡₁ = Very-stable→Very-stable-≡ Very-stable-≡₀

  -- And so on…

-- If A is very stable, then H-level′ n A is very stable.

Very-stable-H-level′ :
  Very-stable A → Very-stable (H-level′ n A)
Very-stable-H-level′ {n = zero} s =
  Very-stable-Σ s λ _ →
  Very-stable-Π λ _ →
  Very-stable→Very-stable-≡ s
Very-stable-H-level′ {n = suc n} s =
  Very-stable-Π λ _ →
  Very-stable-Π λ _ →
  Very-stable-H-level′ (Very-stable→Very-stable-≡ s)

-- If A is very stable, then H-level n A is very stable.

Very-stable-H-level :
  Very-stable A → Very-stable (H-level n A)
Very-stable-H-level {A = A} {n = n} =
  Very-stable A               ↝⟨ Very-stable-H-level′ ⟩
  Very-stable (H-level′ n A)  ↔⟨ inverse $ Very-stable-cong (H-level↔H-level′ ext) ⟩□
  Very-stable (H-level n A)   □

-- A variant of Stable-Π for equality.

Stable-≡-Π :
  {f g : (x : A) → P x} →
  (∀ x → Stable-[ k ] (f x ≡ g x)) →
  Stable-[ k ] (f ≡ g)
Stable-≡-Π {k = k} {f = f} {g = g} =
  (∀ x → Stable-[ k ] (f x ≡ g x))  ↝⟨ Stable-Π ⟩
  Stable-[ k ] (∀ x → f x ≡ g x)    ↝⟨ Stable-map-↔ (_≃_.bijection $ Eq.extensionality-isomorphism ext) ⟩□
  Stable-[ k ] (f ≡ g)              □

-- A variant of Very-stable-Π for equality.

Very-stable-≡-Π :
  {f g : (x : A) → P x} →
  (∀ x → Very-stable (f x ≡ g x)) →
  Very-stable (f ≡ g)
Very-stable-≡-Π {f = f} {g = g} =
  (∀ x → Very-stable (f x ≡ g x))  ↝⟨ Very-stable-Π ⟩
  Very-stable (∀ x → f x ≡ g x)    ↔⟨ Very-stable-cong (Eq.extensionality-isomorphism ext) ⟩□
  Very-stable (f ≡ g)              □

-- A variant of Very-stable-Stable-Σ for equality.

Very-stable-Stable-≡-Σ :
  {p q : Σ A P} →
  Very-stable (proj₁ p ≡ proj₁ q) →
  (∀ eq → Stable-[ k ] (subst P eq (proj₂ p) ≡ proj₂ q)) →
  Stable-[ k ] (p ≡ q)
Very-stable-Stable-≡-Σ {P = P} {k = k} {p = p} {q = q} = curry (
  Very-stable (proj₁ p ≡ proj₁ q) ×
  (∀ eq → Stable-[ k ] (subst P eq (proj₂ p) ≡ proj₂ q))  ↝⟨ uncurry Very-stable-Stable-Σ ⟩

  Stable-[ k ] (∃ λ (eq : proj₁ p ≡ proj₁ q) →
                    subst P eq (proj₂ p) ≡ proj₂ q)       ↝⟨ Stable-map-↔ Bijection.Σ-≡,≡↔≡ ⟩□

  Stable-[ k ] (p ≡ q)                                    □)

-- A variant of Stable-Σ for equality.

Stable-≡-Σ :
  {p q : Σ A P} →
  (s : Stable (proj₁ p ≡ proj₁ q)) →
  (∀ eq →
   Erased (subst P (erased eq) (proj₂ p) ≡ proj₂ q) →
   subst P (s eq) (proj₂ p) ≡ proj₂ q) →
  Stable (p ≡ q)
Stable-≡-Σ {P = P} {p = p} {q = q} = curry (
  (∃ λ (s : Stable (proj₁ p ≡ proj₁ q)) →
     ∀ eq → Erased (subst P (erased eq) (proj₂ p) ≡ proj₂ q) →
            subst P (s eq) (proj₂ p) ≡ proj₂ q)                 ↝⟨ uncurry Stable-Σ ⟩

  Stable (∃ λ (eq : proj₁ p ≡ proj₁ q) →
              subst P eq (proj₂ p) ≡ proj₂ q)                   ↝⟨ Stable-map-↔ Bijection.Σ-≡,≡↔≡ ⟩□

  Stable (p ≡ q)                                                □)

-- A variant of Very-stable-Σ for equality.

Very-stable-≡-Σ :
  {p q : Σ A P} →
  Very-stable (proj₁ p ≡ proj₁ q) →
  (∀ eq → Very-stable (subst P eq (proj₂ p) ≡ proj₂ q)) →
  Very-stable (p ≡ q)
Very-stable-≡-Σ {P = P} {p = p} {q = q} = curry (
  Very-stable (proj₁ p ≡ proj₁ q) ×
  (∀ eq → Very-stable (subst P eq (proj₂ p) ≡ proj₂ q))  ↝⟨ uncurry Very-stable-Σ ⟩

  Very-stable (∃ λ (eq : proj₁ p ≡ proj₁ q) →
                   subst P eq (proj₂ p) ≡ proj₂ q)       ↔⟨ Very-stable-cong $ Eq.↔⇒≃ Bijection.Σ-≡,≡↔≡ ⟩□

  Very-stable (p ≡ q)                                    □)

-- A variant of Stable-× for equality.

Stable-≡-× :
  {p q : A × B} →
  Stable-[ k ] (proj₁ p ≡ proj₁ q) →
  Stable-[ k ] (proj₂ p ≡ proj₂ q) →
  Stable-[ k ] (p ≡ q)
Stable-≡-× {k = k} {p = p} {q = q} = curry (
  Stable-[ k ] (proj₁ p ≡ proj₁ q) × Stable-[ k ] (proj₂ p ≡ proj₂ q)  ↝⟨ uncurry Stable-× ⟩
  Stable-[ k ] (proj₁ p ≡ proj₁ q × proj₂ p ≡ proj₂ q)                 ↝⟨ Stable-map-↔ ≡×≡↔≡ ⟩□
  Stable-[ k ] (p ≡ q)                                                 □)

-- A variant of Very-stable-× for equality.

Very-stable-≡-× :
  {p q : A × B} →
  Very-stable (proj₁ p ≡ proj₁ q) →
  Very-stable (proj₂ p ≡ proj₂ q) →
  Very-stable (p ≡ q)
Very-stable-≡-× {p = p} {q = q} = curry (
  Very-stable (proj₁ p ≡ proj₁ q) × Very-stable (proj₂ p ≡ proj₂ q)  ↝⟨ uncurry Very-stable-× ⟩
  Very-stable (proj₁ p ≡ proj₁ q × proj₂ p ≡ proj₂ q)                ↔⟨ Very-stable-cong $ Eq.↔⇒≃ ≡×≡↔≡ ⟩□
  Very-stable (p ≡ q)                                                □)

-- A variant of Stable-↑ for equality.

Stable-≡-↑ :
  Stable-[ k ] (lower {ℓ = ℓ} x ≡ lower y) →
  Stable-[ k ] (x ≡ y)
Stable-≡-↑ {k = k} {x = x} {y = y} =
  Stable-[ k ] (lower x ≡ lower y)  ↝⟨ Stable-map-↔ (_≃_.bijection $ Eq.≃-≡ $ Eq.↔⇒≃ $ Bijection.↑↔) ⟩□
  Stable-[ k ] (x ≡ y)              □

-- A variant of Very-stable-↑ for equality.

Very-stable-≡-↑ :
  Very-stable (lower {ℓ = ℓ} x ≡ lower y) →
  Very-stable (x ≡ y)
Very-stable-≡-↑ {x = x} {y = y} =
  Very-stable (lower x ≡ lower y)  ↔⟨ Very-stable-cong (Eq.≃-≡ $ Eq.↔⇒≃ $ Bijection.↑↔) ⟩□
  Very-stable (x ≡ y)              □

-- A variant of Very-stable-W for equality.

Very-stable-≡-W :
  Very-stable-≡ A →
  Very-stable-≡ (W A P)
Very-stable-≡-W {P = P} s {x = sup x f} {y = sup y g} =          $⟨ s , (λ _ → Very-stable-Π λ _ → Very-stable-≡-W s) ⟩
  Very-stable (x ≡ y) ×
  (∀ eq → Very-stable (∀ i → f i ≡ g (subst P eq i)))            ↝⟨ uncurry Very-stable-Σ ⟩

  Very-stable (∃ λ (eq : x ≡ y) → ∀ i → f i ≡ g (subst P eq i))  ↔⟨ Very-stable-cong $ Eq.W-≡,≡≃≡ ext ⟩□

  Very-stable (sup x f ≡ sup y g)                                □

-- If equality is stable for A and B, then it is stable for A ⊎ B.

Stable-≡-⊎ :
  Stable-≡-[ k ] A →
  Stable-≡-[ k ] B →
  Stable-≡-[ k ] (A ⊎ B)
Stable-≡-⊎ s₁ s₂ {x = inj₁ x} {y = inj₁ y} =
  Erased (inj₁ x ≡ inj₁ y)  ↔⟨ Erased-cong $ inverse Bijection.≡↔inj₁≡inj₁ ⟩
  Erased (x ≡ y)            ↝⟨ s₁ ⟩
  x ≡ y                     ↔⟨ Bijection.≡↔inj₁≡inj₁ ⟩□
  inj₁ x ≡ inj₁ y           □

Stable-≡-⊎ s₁ s₂ {x = inj₁ x} {y = inj₂ y} =
  Erased (inj₁ x ≡ inj₂ y)  ↔⟨ Erased-cong Bijection.≡↔⊎ ⟩
  Erased ⊥                  ↝⟨ Very-stable→Stable Very-stable-⊥ ⟩
  ⊥                         ↔⟨ inverse Bijection.≡↔⊎ ⟩□
  inj₁ x ≡ inj₂ y           □

Stable-≡-⊎ s₁ s₂ {x = inj₂ x} {y = inj₁ y} =
  Erased (inj₂ x ≡ inj₁ y)  ↔⟨ Erased-cong Bijection.≡↔⊎ ⟩
  Erased ⊥                  ↝⟨ Very-stable→Stable Very-stable-⊥ ⟩
  ⊥                         ↔⟨ inverse Bijection.≡↔⊎ ⟩□
  inj₂ x ≡ inj₁ y           □

Stable-≡-⊎ s₁ s₂ {x = inj₂ x} {y = inj₂ y} =
  Erased (inj₂ x ≡ inj₂ y)  ↔⟨ Erased-cong $ inverse Bijection.≡↔inj₂≡inj₂ ⟩
  Erased (x ≡ y)            ↝⟨ s₂ ⟩
  x ≡ y                     ↔⟨ Bijection.≡↔inj₂≡inj₂ ⟩□
  inj₂ x ≡ inj₂ y           □

-- If equality is very stable for A and B, then it is very stable for
-- A ⊎ B.

Very-stable-≡-⊎ :
  Very-stable-≡ A →
  Very-stable-≡ B →
  Very-stable-≡ (A ⊎ B)
Very-stable-≡-⊎ s₁ s₂ =
  _≃_.is-equivalence $
  Eq.with-other-function
    (inverse $ Stable-≡-⊎ (inverse Eq.⟨ _ , s₁ ⟩)
                          (inverse Eq.⟨ _ , s₂ ⟩))
    [_]
    (lemma _ _)
  where
  lemma :
    ∀ x y (eq : x ≡ y) →
    _≃_.from (Stable-≡-⊎ (inverse Eq.⟨ _ , s₁ ⟩)
                         (inverse Eq.⟨ _ , s₂ ⟩)) eq ≡
    [ eq ]
  lemma (inj₁ _) (inj₁ _) eq =
    [ cong inj₁ (⊎.cancel-inj₁ eq) ]  ≡⟨ cong [_] $ _↔_.right-inverse-of Bijection.≡↔inj₁≡inj₁ eq ⟩∎
    [ eq ]                            ∎
  lemma (inj₁ _) (inj₂ _) eq = ⊥-elim (⊎.inj₁≢inj₂ eq)
  lemma (inj₂ _) (inj₁ _) eq = ⊥-elim (⊎.inj₁≢inj₂ (sym eq))
  lemma (inj₂ _) (inj₂ _) eq =
    [ cong inj₂ (⊎.cancel-inj₂ eq) ]  ≡⟨ cong [_] $ _↔_.right-inverse-of Bijection.≡↔inj₂≡inj₂ eq ⟩∎
    [ eq ]                            ∎

-- If equality is stable for A, then it is stable for List A.

Stable-≡-List :
  Stable-≡-[ k ] A →
  Stable-≡-[ k ] (List A)
Stable-≡-List {k = k} s {x = []} {y = []} =
  Erased ([] ≡ [])            ↔⟨ Erased-cong $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩
  Erased (inj₁ tt ≡ inj₁ tt)  ↔⟨ Erased-cong $ inverse Bijection.≡↔inj₁≡inj₁ ⟩
  Erased (tt ≡ tt)            ↝⟨ Very-stable→Stable $ Very-stable→Very-stable-≡ Very-stable-⊤ ⟩
  tt ≡ tt                     ↔⟨ Bijection.≡↔inj₁≡inj₁ ⟩
  inj₁ tt ≡ inj₁ tt           ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩□
  [] ≡ []                     □

Stable-≡-List s {x = []} {y = y ∷ ys} =
  Erased ([] ≡ y ∷ ys)              ↔⟨ Erased-cong $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩
  Erased (inj₁ tt ≡ inj₂ (y , ys))  ↔⟨ Erased-cong Bijection.≡↔⊎ ⟩
  Erased ⊥                          ↝⟨ Very-stable→Stable Very-stable-⊥ ⟩
  ⊥                                 ↔⟨ inverse Bijection.≡↔⊎ ⟩
  inj₁ tt ≡ inj₂ (y , ys)           ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩□
  [] ≡ y ∷ ys                       □

Stable-≡-List s {x = x ∷ xs} {y = []} =
  Erased (x ∷ xs ≡ [])              ↔⟨ Erased-cong $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩
  Erased (inj₂ (x , xs) ≡ inj₁ tt)  ↔⟨ Erased-cong Bijection.≡↔⊎ ⟩
  Erased ⊥                          ↝⟨ Very-stable→Stable Very-stable-⊥ ⟩
  ⊥                                 ↔⟨ inverse Bijection.≡↔⊎ ⟩
  inj₂ (x , xs) ≡ inj₁ tt           ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩□
  x ∷ xs ≡ []                       □

Stable-≡-List s {x = x ∷ xs} {y = y ∷ ys} =
  Erased (x ∷ xs ≡ y ∷ ys)                ↔⟨ Erased-cong $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩
  Erased (inj₂ (x , xs) ≡ inj₂ (y , ys))  ↔⟨ Erased-cong $ inverse Bijection.≡↔inj₂≡inj₂ ⟩
  Erased ((x , xs) ≡ (y , ys))            ↝⟨ Stable-≡-× s (Stable-≡-List s) ⟩
  (x , xs) ≡ (y , ys)                     ↔⟨ Bijection.≡↔inj₂≡inj₂ ⟩
  inj₂ (x , xs) ≡ inj₂ (y , ys)           ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩□
  x ∷ xs ≡ y ∷ ys                         □

-- If equality is very stable for A, then it is very stable for
-- List A.

Very-stable-≡-List :
  Very-stable-≡ A →
  Very-stable-≡ (List A)
Very-stable-≡-List {A = A} s =
  _≃_.is-equivalence $
  Eq.with-other-function
    (inverse s′)
    [_]
    (lemma _ _)
  where
  s′ : Stable-≡-[ equivalence ] (List A)
  s′ = Stable-≡-List (inverse Eq.⟨ _ , s ⟩)

  lemma :
    ∀ xs ys (eq : xs ≡ ys) →
    _≃_.from s′ eq ≡ [ eq ]
  lemma [] [] _ = cong [_] (prop _ _)
    where
    prop : Is-proposition ([] ≡ [])
    prop =                                $⟨ mono (Nat.zero≤ 2) ⊤-contractible ⟩
      Is-proposition (tt ≡ tt)            ↝⟨ H-level-cong _ 1 Bijection.≡↔inj₁≡inj₁ ⟩
      Is-proposition (inj₁ tt ≡ inj₁ tt)  ↝⟨ H-level-cong _ 1 (Eq.≃-≡ (Eq.↔⇒≃ L.List↔Maybe[×List])) ⦂ (_ → _) ⟩□
      Is-proposition ([] ≡ [])            □

  lemma [] (_ ∷ _) = ⊥-elim ∘ List.[]≢∷

  lemma (_ ∷ _) [] = ⊥-elim ∘ List.[]≢∷ ∘ sym

  lemma (_ ∷ xs) (_ ∷ ys) eq = []-cong [
    _≃_.to iso₁ (_↔_.to iso₂ (_↔_.to iso₃
      (Σ-map id (erased ∘ _≃_.from s′)
         (_↔_.from iso₃ (_↔_.from iso₂ (_≃_.from iso₁ eq))))))    ≡⟨ cong (λ f → _≃_.to iso₁ (_↔_.to iso₂ (_↔_.to iso₃
                                                                                 (Σ-map id (erased ∘ f)
                                                                                    (_↔_.from iso₃ (_↔_.from iso₂ (_≃_.from iso₁ eq))))))) $
                                                                     ⟨ext⟩ (lemma xs ys) ⟩
    _≃_.to iso₁ (_↔_.to iso₂ (_↔_.to iso₃
      (_↔_.from iso₃ (_↔_.from iso₂ (_≃_.from iso₁ eq)))))
                                                                  ≡⟨ cong (λ eq → _≃_.to iso₁ (_↔_.to iso₂ eq)) $
                                                                     _↔_.right-inverse-of iso₃ _ ⟩

    _≃_.to iso₁ (_↔_.to iso₂ (_↔_.from iso₂ (_≃_.from iso₁ eq)))  ≡⟨ cong (_≃_.to iso₁) $ _↔_.right-inverse-of iso₂ _ ⟩

    _≃_.to iso₁ (_≃_.from iso₁ eq)                                ≡⟨ _≃_.right-inverse-of iso₁ _ ⟩∎

    eq                                                            ∎ ]
    where
    iso₁ = Eq.≃-≡ (Eq.↔⇒≃ L.List↔Maybe[×List])
    iso₂ = Bijection.≡↔inj₂≡inj₂
    iso₃ = ≡×≡↔≡
