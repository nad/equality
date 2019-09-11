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
open import Embedding eq using (Is-embedding)
open import Equality.Decidable-UIP eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Erased eq
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
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

------------------------------------------------------------------------
-- Some results that follow if "Erased-≡↔[]≡[]" can be defined in a
-- certain way and very stable types have very stable equality

module Very-stable→Very-stable-≡
  (Erased-≡↔[]≡[] :
    ∀ {a} {@0 A : Set a} {@0 x y : A} →
    Erased (x ≡ y) ↔ [ x ] ≡ [ y ])
  (to-Erased-≡↔[]≡[]-[refl] :
    ∀ {a} {A : Set a} {x : A} →
    _↔_.to Erased-≡↔[]≡[] [ refl x ] ≡ refl [ x ])
  (Very-stable→Very-stable-≡ :
     ∀ {a} {A : Set a} →
     Very-stable A → Very-stable-≡ A)
  where

  open Erased-≡↔[]≡[]₂ Erased-≡↔[]≡[] to-Erased-≡↔[]≡[]-[refl]

  ----------------------------------------------------------------------
  -- Some lemmas related to stability

  -- If A is a stable proposition, then A is very stable.
  --
  -- Note that it is not the case that every very stable type is a
  -- proposition, see ¬-Very-stable→Is-proposition.

  Stable-proposition→Very-stable :
    Stable A → Is-proposition A → Very-stable A
  Stable-proposition→Very-stable {A = A} s prop =
    _≃_.is-equivalence (inverse lemma)
    where
    lemma =                             $⟨ s ⟩
      Stable A                          ↝⟨ Stable→Stable⇔ ⟩
      Stable-[ logical-equivalence ] A  ↝⟨ _↠_.from (Eq.≃↠⇔ (H-level-Erased 1 prop) prop) ⟩□
      Stable-[ equivalence ] A          □

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

  -- If equality is decidable for A, then equality is very stable for A.

  Decidable-equality→Very-stable-≡ :
    Decidable-equality A → Very-stable-≡ A
  Decidable-equality→Very-stable-≡ dec =
    Stable-proposition→Very-stable
      (Dec→Stable (dec _ _))
      (decidable⇒set dec)

  ----------------------------------------------------------------------
  -- Preservation lemmas

  -- See also Stable-⇔-cong above.

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
    Very-stable A → Very-stable (W A P)
  Very-stable-W {A = A} {P = P} ext s =
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

  -- If A is very stable, then H-level′ n A is very stable (assuming
  -- extensionality).

  Very-stable-H-level′ :
    {A : Set a} →
    Extensionality a a →
    Very-stable A → Very-stable (H-level′ n A)
  Very-stable-H-level′ {n = zero} ext s =
    Very-stable-Σ s λ _ →
    Very-stable-Π ext λ _ →
    Very-stable→Very-stable-≡ s
  Very-stable-H-level′ {n = suc n} ext s =
    Very-stable-Π ext λ _ →
    Very-stable-Π ext λ _ →
    Very-stable-H-level′ ext (Very-stable→Very-stable-≡ s)

  -- If A is very stable, then H-level n A is very stable (assuming
  -- extensionality).

  Very-stable-H-level :
    {A : Set a} →
    Extensionality a a →
    Very-stable A → Very-stable (H-level n A)
  Very-stable-H-level {n = n} {A = A} ext =
    Very-stable A               ↝⟨ Very-stable-H-level′ ext ⟩
    Very-stable (H-level′ n A)  ↝⟨ Very-stable-cong _ (inverse $ H-level↔H-level′ ext) ⟩□
    Very-stable (H-level n A)   □

  -- A variant of Stable-Π for equality.

  Stable-≡-Π :
    {A : Set a} {P : A → Set p} {f g : (x : A) → P x} →
    Extensionality a p →
    (∀ x → Stable-[ k ] (f x ≡ g x)) →
    Stable-[ k ] (f ≡ g)
  Stable-≡-Π {k = k} {f = f} {g = g} ext =
    (∀ x → Stable-[ k ] (f x ≡ g x))  ↝⟨ Stable-Π (forget-ext? k ext) ⟩
    Stable-[ k ] (∀ x → f x ≡ g x)    ↝⟨ Stable-map-↔ (_≃_.bijection $ Eq.extensionality-isomorphism ext) ⟩□
    Stable-[ k ] (f ≡ g)              □

  -- A variant of Very-stable-Π for equality.

  Very-stable-≡-Π :
    {A : Set a} {P : A → Set p} {f g : (x : A) → P x} →
    Extensionality a p →
    (∀ x → Very-stable (f x ≡ g x)) →
    Very-stable (f ≡ g)
  Very-stable-≡-Π {f = f} {g = g} ext =
    (∀ x → Very-stable (f x ≡ g x))  ↝⟨ Very-stable-Π ext ⟩
    Very-stable (∀ x → f x ≡ g x)    ↝⟨ Very-stable-cong _ (Eq.extensionality-isomorphism ext) ⟩□
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
                     subst P eq (proj₂ p) ≡ proj₂ q)       ↝⟨ Very-stable-cong _ $ Eq.↔⇒≃ Bijection.Σ-≡,≡↔≡ ⟩□

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
    Very-stable (proj₁ p ≡ proj₁ q × proj₂ p ≡ proj₂ q)                ↝⟨ Very-stable-cong _ $ Eq.↔⇒≃ ≡×≡↔≡ ⟩□
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
    Very-stable (lower x ≡ lower y)  ↝⟨ Very-stable-cong _ (Eq.≃-≡ $ Eq.↔⇒≃ $ Bijection.↑↔) ⟩□
    Very-stable (x ≡ y)              □

  -- A variant of Very-stable-W for equality.

  Very-stable-≡-W :
    {A : Set a} {P : A → Set p} →
    Extensionality p (a ⊔ p) →
    Very-stable-≡ A →
    Very-stable-≡ (W A P)
  Very-stable-≡-W {P = P} ext s {x = sup x f} {y = sup y g} =      $⟨ s , (λ _ → Very-stable-Π ext λ _ → Very-stable-≡-W ext s) ⟩
    Very-stable (x ≡ y) ×
    (∀ eq → Very-stable (∀ i → f i ≡ g (subst P eq i)))            ↝⟨ uncurry Very-stable-Σ ⟩

    Very-stable (∃ λ (eq : x ≡ y) → ∀ i → f i ≡ g (subst P eq i))  ↝⟨ Very-stable-cong _ $ Eq.W-≡,≡≃≡ ext ⟩□

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

  -- If equality is very stable for A and B, then it is very stable
  -- for A ⊎ B.

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

  Very-stable-≡-List : Very-stable-≡ A → Very-stable-≡ (List A)
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
           (_↔_.from iso₃ (_↔_.from iso₂ (_≃_.from iso₁ eq))))))    ≡⟨ cong (λ x → _≃_.to iso₁ (_↔_.to iso₂ (_↔_.to iso₃
                                                                                     (proj₁ (_↔_.from iso₃ (_↔_.from iso₂ _)) , erased x)))) $
                                                                       lemma xs ys _ ⟩
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
