------------------------------------------------------------------------
-- Stability for Erased
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Erased.Stability
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_)
open import Double-negation eq as DN
open import Embedding eq using (Is-embedding)
open import Equality.Decidable-UIP eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Erased eq
open import For-iterated-equality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import Injection eq using (Injective)
import List eq as L
import Nat eq as Nat
open import Surjection eq using (_↠_; Split-surjective)

private
  variable
    a b ℓ p : Level
    A B     : Set a
    P       : A → Set p
    k x y   : A
    n       : ℕ

------------------------------------------------------------------------
-- Stability

mutual

  -- A type A is stable if Erased A implies A.

  Stable : Set a → Set a
  Stable = Stable-[ implication ]

  -- A generalisation of Stable.

  Stable-[_] : Kind → Set a → Set a
  Stable-[ k ] A = Erased A ↝[ k ] A

-- A special case of Stable-[ equivalence ].

Very-stable : Set a → Set a
Very-stable A = Is-equivalence ([_] {A = A})

-- Variants of the definitions above for equality.

Stable-≡ : Set a → Set a
Stable-≡ = For-iterated-equality 1 Stable

Stable-≡-[_] : Kind → Set a → Set a
Stable-≡-[ k ] = For-iterated-equality 1 Stable-[ k ]

Very-stable-≡ : Set a → Set a
Very-stable-≡ = For-iterated-equality 1 Very-stable

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

private

  -- The previous result can be generalised.

  For-iterated-equality-Very-stable-propositional :
    {A : Set a} →
    Extensionality a a →
    ∀ n → Is-proposition (For-iterated-equality n Very-stable A)
  For-iterated-equality-Very-stable-propositional ext n =
    H-level-For-iterated-equality ext 1 n
      (Very-stable-propositional ext)

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

-- Erased A is very stable.

Very-stable-Erased :
  {@0 A : Set a} → Very-stable (Erased A)
Very-stable-Erased =
  _≃_.is-equivalence (Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { from = λ ([ [ x ] ]) → [ x ]
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
Dec→Stable (no ¬x) x with () ← Erased→¬¬ x ¬x

-- Every type is stable in the double negation monad.

¬¬-Stable : {@0 A : Set a} → ¬¬ Stable A
¬¬-Stable = DN.map′ Dec→Stable excluded-middle

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

------------------------------------------------------------------------
-- Some results that follow if "[]-cong" is an equivalence that maps
-- [ refl x ] to refl [ x ]

module []-cong
  ([]-cong :
     ∀ {a} {@0 A : Set a} {@0 x y : A} →
     Erased (x ≡ y) → [ x ] ≡ [ y ])
  ([]-cong-equivalence :
     ∀ {a} {@0 A : Set a} {@0 x y : A} →
     Is-equivalence ([]-cong {x = x} {y = y}))
  ([]-cong-[refl]′ :
    ∀ {a} {A : Set a} {x : A} →
    []-cong [ refl x ] ≡ refl [ x ])
  where

  open []-cong₃ []-cong []-cong-equivalence []-cong-[refl]′

  ----------------------------------------------------------------------
  -- Some lemmas related to stability

  -- If A is stable, with [_] as a right inverse of the proof of
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

  -- If A is a stable proposition, then A is very stable.
  --
  -- Note that it is not the case that every very stable type is a
  -- proposition, see ¬-Very-stable→Is-proposition.

  Stable-proposition→Very-stable :
    Stable A → Is-proposition A → Very-stable A
  Stable-proposition→Very-stable s prop =
    _≃_.is-equivalence $
    _↠_.from (Eq.≃↠⇔ prop (H-level-Erased 1 prop))
      (record { to = [_]; from = s })

  -- The previous result can be generalised.

  Stable→H-level-suc→Very-stable :
    ∀ n →
    For-iterated-equality n Stable A → H-level (1 + n) A →
    For-iterated-equality n Very-stable A
  Stable→H-level-suc→Very-stable {A = A} n = curry (
    For-iterated-equality n Stable A × H-level (1 + n) A            ↝⟨ (∃-cong λ _ → lemma) ⟩

    For-iterated-equality n Stable A ×
    For-iterated-equality n Is-proposition A                        ↝⟨ For-iterated-equality-commutes-× _ n ⟩

    For-iterated-equality n (λ A → Stable A × Is-proposition A) A   ↝⟨ For-iterated-equality-cong₁ _ n $
                                                                       uncurry Stable-proposition→Very-stable ⟩
    For-iterated-equality n Very-stable A                           □)
    where
    lemma =
      H-level (1 + n) A                         ↝⟨ _⇔_.to H-level⇔H-level′ ⟩
      H-level′ (1 + n) A                        ↝⟨ (flip inverse-ext? _ λ ext →
                                                    For-iterated-equality-For-iterated-equality ext n 1) ⟩
      For-iterated-equality n (H-level′ 1) A    ↝⟨ For-iterated-equality-cong₁ _ n $
                                                   _⇔_.from (H-level⇔H-level′ {n = 1}) ⟩□
      For-iterated-equality n Is-proposition A  □

  -- If equality is decidable for A, then equality is very stable for A.

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

  -- Equality is stable for A if and only if [_] is injective for A.

  Stable-≡↔Injective-[] :
    {A : Set a} →
    Extensionality? k a a →
    Stable-≡ A ↝[ k ] Injective ([_] {A = A})
  Stable-≡↔Injective-[] ext =
    (∀ x y → Erased (x ≡ y) → x ≡ y)    ↝⟨ (∀-cong ext λ _ → from-isomorphism $ inverse Bijection.implicit-Π↔Π) ⟩
    (∀ x {y} → Erased (x ≡ y) → x ≡ y)  ↔⟨ inverse Bijection.implicit-Π↔Π ⟩
    (∀ {x y} → Erased (x ≡ y) → x ≡ y)  ↝⟨ (implicit-∀-cong ext $ implicit-∀-cong ext $
                                            Π-cong ext Erased-≡↔[]≡[] λ _ → F.id) ⟩□
    (∀ {x y} → [ x ] ≡ [ y ] → x ≡ y)   □

  -- Equality is very stable for A if and only if [_] is an embedding
  -- for A.

  Very-stable-≡↔Is-embedding-[] :
    {A : Set a} →
    Extensionality? k a a →
    Very-stable-≡ A ↝[ k ] Is-embedding ([_] {A = A})
  Very-stable-≡↔Is-embedding-[] ext =
    (∀ x y → Is-equivalence ([_] {A = x ≡ y}))            ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                              generalise-ext?-prop
                                                                (record { to = to; from = from })
                                                                (λ ext → Eq.propositional ext _)
                                                                (λ ext → Eq.propositional ext _)
                                                                ext) ⟩
    (∀ x y → Is-equivalence ([]-cong ∘ [_] {A = x ≡ y}))  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Is-equivalence-cong ext λ _ →
                                                              to-Erased-≡↔[]≡[]) ⟩□
    (∀ x y → Is-equivalence (cong {x = x} {y = y} [_]))   □
    where
    to :
      Is-equivalence ([_] {A = x ≡ y}) →
      Is-equivalence ([]-cong ∘ [_] {A = x ≡ y})
    to hyp = Eq.Two-out-of-three.f-g
      (Eq.two-out-of-three _ _)
      hyp
      []-cong-equivalence

    from :
      Is-equivalence ([]-cong ∘ [_] {A = x ≡ y}) →
      Is-equivalence ([_] {A = x ≡ y})
    from = Eq.Two-out-of-three.g-g∘f
      (Eq.two-out-of-three _ _)
      []-cong-equivalence

  private

    -- The previous result can be generalised.

    Very-stable-≡↔Is-embedding-[]′ :
      {A : Set a} →
      Extensionality? k a a →
      ∀ n →
      For-iterated-equality (1 + n) Very-stable A ↝[ k ]
      For-iterated-equality n (λ A → Is-embedding ([_] {A = A})) A
    Very-stable-≡↔Is-embedding-[]′ {A = A} ext n =
      For-iterated-equality (1 + n) Very-stable A                   ↝⟨ (flip inverse-ext? ext λ ext →
                                                                        For-iterated-equality-For-iterated-equality ext n 1) ⟩
      For-iterated-equality n Very-stable-≡ A                       ↝⟨ For-iterated-equality-cong₁ ext n (Very-stable-≡↔Is-embedding-[] ext) ⟩□
      For-iterated-equality n (λ A → Is-embedding ([_] {A = A})) A  □

  ----------------------------------------------------------------------
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
  -- "symmetric"), possibly assuming extensionality.

  Stable-cong :
    {A : Set a} {B : Set b} →
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
    {A : Set a} {B : Set b} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    A ≃ B → Stable-[ equivalence ] A ↝[ k ] Stable-[ equivalence ] B
  Stable-≃-cong {A = A} {B = B} ext A≃B =
    Stable-[ equivalence ] A  ↔⟨⟩
    Erased A ≃ A              ↝⟨ generalise-ext?
                                   (Eq.≃-preserves-⇔ (Erased-cong-≃ A≃B) A≃B)
                                   (λ ext → from-isomorphism $ Eq.≃-preserves ext (Erased-cong-≃ A≃B) A≃B)
                                   ext ⟩
    Erased B ≃ B              ↔⟨⟩
    Stable-[ equivalence ] B  □

  -- Very-stable preserves equivalences (assuming extensionality).

  Very-stable-cong :
    {A : Set a} {B : Set b} →
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
         A         ↝⟨ Eq.⟨ [_] , s ⟩ ⟩
         Erased A  ↝⟨ Erased-cong-≃ A≃B ⟩□
         Erased B  □)
        [_]
        (λ x →
           [ _≃_.to A≃B (_≃_.from A≃B x) ]  ≡⟨ cong [_] (_≃_.right-inverse-of A≃B x) ⟩∎
           [ x ]                            ∎)

  ----------------------------------------------------------------------
  -- A closure property

  -- If A is very stable, then W A P is very stable (assuming
  -- extensionality).

  Very-stable-W :
    {A : Set a} {P : A → Set p} →
    Extensionality p (a ⊔ p) →
    ∀ n →
    For-iterated-equality n Very-stable A →
    For-iterated-equality n Very-stable (W A P)
  Very-stable-W {A = A} {P = P} ext n =
    For-iterated-equality-W
      ext
      n
      (Very-stable-cong _ ∘ from-isomorphism)
      (Very-stable-Π ext)
      Very-stable-Σ
      lemma
    where
    lemma : Very-stable A → Very-stable (W A P)
    lemma s =
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

  ----------------------------------------------------------------------
  -- Closure properties related to equality

  -- If A is very stable, then equality is very stable for A.

  Very-stable→Very-stable-≡ :
    ∀ n →
    For-iterated-equality n       Very-stable A →
    For-iterated-equality (1 + n) Very-stable A
  Very-stable→Very-stable-≡ {A = A} n =
    For-iterated-equality n Very-stable A        ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
    For-iterated-equality n Very-stable-≡ A      ↝⟨ For-iterated-equality-For-iterated-equality _ n 1 ⟩□
    For-iterated-equality (1 + n) Very-stable A  □
    where
    lemma : ∀ {A} → Very-stable A → Very-stable-≡ A
    lemma {A = A} =
      Very-stable A               ↝⟨ Very-stable→Is-embedding-[] ⟩
      Is-embedding ([_] {A = A})  ↝⟨ inverse-ext? Very-stable-≡↔Is-embedding-[] _ ⟩□
      Very-stable-≡ A             □

  private

    -- Some examples showing how Very-stable→Very-stable-≡ can be
    -- used.

    -- Equalities between erased values are very stable.

    Very-stable-≡₀ :
      {@0 A : Set a} →
      Very-stable-≡ (Erased A)
    Very-stable-≡₀ = Very-stable→Very-stable-≡ 0 Very-stable-Erased

    -- Equalities between equalities between erased values are very
    -- stable.

    Very-stable-≡₁ :
      {@0 A : Set a} →
      For-iterated-equality 2 Very-stable (Erased A)
    Very-stable-≡₁ = Very-stable→Very-stable-≡ 1 Very-stable-≡₀

    -- And so on…

  -- If A is "stable 1 + n levels up", then H-level′ (1 + n) A is
  -- stable.

  Stable-H-level′ :
    {A : Set a} →
    Extensionality? k a a →
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    Stable-[ k ] (H-level′ (1 + n) A)
  Stable-H-level′ {a = a} {k = k} {A = A} ext n =
    For-iterated-equality (1 + n) Stable-[ k ] A               ↝⟨ inverse-ext? (λ ext → For-iterated-equality-For-iterated-equality ext n 1) _ ⟩
    For-iterated-equality n Stable-≡-[ k ] A                   ↝⟨ For-iterated-equality-cong₁ _ n lemma₁ ⟩
    For-iterated-equality n (Stable-[ k ] ∘ Is-proposition) A  ↝⟨ For-iterated-equality-commutes-← _ Stable-[ k ] n (Stable-Π ext) ⟩
    Stable-[ k ] (For-iterated-equality n Is-proposition A)    ↝⟨ Stable-map (lemma₂ ext) (inverse-ext? lemma₂ ext) ⟩□
    Stable-[ k ] (H-level′ (1 + n) A)                          □
    where
    lemma₁ : ∀ {A} → Stable-≡-[ k ] A → Stable-[ k ] (Is-proposition A)
    lemma₁ s =
      Stable-Π ext λ _ →
      Stable-Π ext λ _ →
      s _ _

    lemma₂ :
      ∀ {k} →
      Extensionality? k a a →
      For-iterated-equality n Is-proposition A ↝[ k ]
      H-level′ (1 + n) A
    lemma₂ ext =
      For-iterated-equality n Is-proposition A  ↝⟨ For-iterated-equality-cong₁ ext n (H-level↔H-level′ {n = 1} ext) ⟩
      For-iterated-equality n (H-level′ 1) A    ↝⟨ For-iterated-equality-For-iterated-equality ext n 1 ⟩□
      H-level′ (1 + n) A                        □

  -- If A is "stable 1 + n levels up", then H-level (1 + n) A is
  -- stable.

  Stable-H-level :
    {A : Set a} →
    Extensionality? k a a →
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    Stable-[ k ] (H-level (1 + n) A)
  Stable-H-level {k = k} {A = A} ext n =
    For-iterated-equality (1 + n) Stable-[ k ] A  ↝⟨ Stable-H-level′ ext n ⟩
    Stable-[ k ] (H-level′ (1 + n) A)             ↝⟨ Stable-map (inverse-ext? H-level↔H-level′ ext) (H-level↔H-level′ ext) ⟩□
    Stable-[ k ] (H-level (1 + n) A)              □

  -- If A is "very stable n levels up", then H-level′ n A is very
  -- stable (assuming extensionality).

  Very-stable-H-level′ :
    {A : Set a} →
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

  -- If A is "very stable n levels up", then H-level n A is very
  -- stable (assuming extensionality).

  Very-stable-H-level :
    {A : Set a} →
    Extensionality a a →
    ∀ n →
    For-iterated-equality n Very-stable A →
    Very-stable (H-level n A)
  Very-stable-H-level {A = A} ext n =
    For-iterated-equality n Very-stable A  ↝⟨ Very-stable-H-level′ ext n ⟩
    Very-stable (H-level′ n A)             ↝⟨ Very-stable-cong _ (inverse $ H-level↔H-level′ ext) ⟩□
    Very-stable (H-level n A)              □

  -- If equality is stable for A and B, then it is stable for A ⊎ B.

  Stable-≡-⊎ :
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    For-iterated-equality (1 + n) Stable-[ k ] B →
    For-iterated-equality (1 + n) Stable-[ k ] (A ⊎ B)
  Stable-≡-⊎ n sA sB =
    For-iterated-equality-⊎-suc
      n
      Stable-map-↔
      (Very-stable→Stable 0 Very-stable-⊥)
      (For-iterated-equality-↑ _ (1 + n) Stable-map-↔ sA)
      (For-iterated-equality-↑ _ (1 + n) Stable-map-↔ sB)

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

  -- If equality is stable for A, then it is stable for List A.

  Stable-≡-List :
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    For-iterated-equality (1 + n) Stable-[ k ] (List A)
  Stable-≡-List n =
    For-iterated-equality-List-suc
      n
      Stable-map-↔
      (Very-stable→Stable 0 $ Very-stable-↑ Very-stable-⊤)
      (Very-stable→Stable 0 Very-stable-⊥)
      Stable-×

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

  ----------------------------------------------------------------------
  -- Simple corollaries or variants of results above

  -- A generalisation of Stable-Π.

  Stable-Πⁿ :
    {A : Set a} {P : A → Set p} →
    Extensionality a p →
    ∀ n →
    (∀ x → For-iterated-equality n Stable-[ k ] (P x)) →
    For-iterated-equality n Stable-[ k ] ((x : A) → P x)
  Stable-Πⁿ {k = k} ext n =
    For-iterated-equality-Π
      ext
      n
      Stable-map-↔
      (Stable-Π (forget-ext? k ext))

  -- A generalisation of Very-stable-Π.

  Very-stable-Πⁿ :
    {A : Set a} {P : A → Set p} →
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

  -- A generalisation of Very-stable-Stable-Σ.

  Very-stable-Stable-Σⁿ :
    ∀ n →
    For-iterated-equality n Very-stable A →
    (∀ x → For-iterated-equality n Stable-[ k ] (P x)) →
    For-iterated-equality n Stable-[ k ] (Σ A P)
  Very-stable-Stable-Σⁿ {k = k} n =
    For-iterated-equality-Σ
      n
      Stable-map-↔
      Very-stable-Stable-Σ

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

  -- A generalisation of Stable-×.

  Stable-×ⁿ :
    ∀ n →
    For-iterated-equality n Stable-[ k ] A →
    For-iterated-equality n Stable-[ k ] B →
    For-iterated-equality n Stable-[ k ] (A × B)
  Stable-×ⁿ n =
    For-iterated-equality-×
      n
      Stable-map-↔
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
    For-iterated-equality n Stable-[ k ] A →
    For-iterated-equality n Stable-[ k ] (↑ ℓ A)
  Stable-↑ⁿ n =
    For-iterated-equality-↑ _ n Stable-map-↔

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
