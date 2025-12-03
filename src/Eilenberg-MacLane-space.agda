------------------------------------------------------------------------
-- The Eilenberg-MacLane space K(G, 1)
------------------------------------------------------------------------

{-# OPTIONS --cubical=no-glue --safe #-}

-- The module is parametrised by a notion of equality. The higher
-- constructors of the HIT defining K(G, 1) use path equality, but the
-- supplied notion of equality is used for many other things.

import Equality.Path as P

module Eilenberg-MacLane-space
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as B using (_↔_)
open import Embedding equality-with-J using (Embedding; Is-embedding)
import Equality.Groupoid equality-with-J as EG
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
import Equivalence P.equality-with-J as PEq
open import Extensionality equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import Group equality-with-J
open import H-level equality-with-J as H-level
import H-level P.equality-with-J as PH
open import H-level.Closure equality-with-J
open import H-level.Truncation eq as T using (∥_∥[1+_]; ∣_∣)
open import H-level.Truncation.Propositional eq as TP using (Surjective)
open import Pointed-type equality-with-J
open import Pointed-type.Connected eq
open import Pointed-type.Homotopy-group eq
open import Univalence-axiom equality-with-J

private
  variable
    a p     : Level
    A       : Type a
    P       : A → Type p
    e g x y : A
    G G₁ G₂ : Group g

------------------------------------------------------------------------
-- The type

-- The Eilenberg-MacLane space K(G, 1).
--
-- This definition is taken from "Eilenberg-MacLane Spaces in Homotopy
-- Type Theory" by Licata and Finster.

data K[_]1 (G : Group g) : Type g where
  base        : K[ G ]1
  loopᴾ        : Group.Carrier G → base P.≡ base
  loop-idᴾ     : loopᴾ (Group.id G) P.≡ P.refl
  loop-∘ᴾ      : loopᴾ (Group._∘_ G x y) P.≡ P.htransˡ (loopᴾ x) (loopᴾ y)
  is-groupoidᴾ : PH.H-level 3 K[ G ]1

-- Variants of the higher constructors.

loop : Group.Carrier G → base ≡ base
loop {G} = _↔_.from ≡↔≡ ⊚ loopᴾ {G = G}

loop-id : loop {G = G} (Group.id G) ≡ refl base
loop-id {G} =
  loop id              ≡⟨ _≃_.from (Eq.≃-≡ (Eq.↔⇒≃ (inverse ≡↔≡))) (_↔_.from ≡↔≡ loop-idᴾ) ⟩
  _↔_.from ≡↔≡ P.refl  ≡⟨ from-≡↔≡-refl ⟩∎
  refl base            ∎
  where
  open Group G

loop-∘ : loop {G = G} (Group._∘_ G x y) ≡ trans (loop x) (loop y)
loop-∘ {G} {x} {y} =
  loop (Group._∘_ G x y)                      ≡⟨ _≃_.from (Eq.≃-≡ (Eq.↔⇒≃ (inverse ≡↔≡))) (_↔_.from ≡↔≡ loop-∘ᴾ) ⟩
  _↔_.from ≡↔≡ (P.trans (loopᴾ x) (loopᴾ y))  ≡⟨ sym trans≡trans ⟩∎
  trans (loop x) (loop y)                     ∎

is-groupoid : H-level 3 K[ G ]1
is-groupoid = _↔_.from (H-level↔H-level 3) is-groupoidᴾ

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.
--
-- This eliminator is based on one from "Eilenberg-MacLane Spaces in
-- Homotopy Type Theory" by Licata and Finster.

record Elimᴾ {G : Group g} (P : K[ G ]1 → Type p) : Type (g ⊔ p) where
  no-eta-equality
  open Group G
  field
    baseʳ        : P base
    loopʳ        : ∀ g → P.[ (λ i → P (loopᴾ g i)) ] baseʳ ≡ baseʳ
    loop-idʳ     : P.[ (λ i → P.[ (λ j → P (loop-idᴾ i j)) ]
                                baseʳ ≡ baseʳ) ]
                     loopʳ id ≡ P.refl {x = baseʳ}
    loop-∘ʳ      : P.[ (λ i →
                          P.[ (λ j → P (loop-∘ᴾ {x = x} {y = y} i j)) ]
                            baseʳ ≡ baseʳ) ]
                     loopʳ (x ∘ y) ≡ P.htrans P (loopʳ x) (loopʳ y)
    is-groupoidʳ : ∀ x → PH.H-level 3 (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : K[ G ]1) → P x
elimᴾ {G} {P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : K[ G ]1) → P x
  helper base                     = E.baseʳ
  helper (loopᴾ x i)              = E.loopʳ x i
  helper (loop-idᴾ i j)           = E.loop-idʳ i j
  helper (loop-∘ᴾ i j)            = E.loop-∘ʳ i j
  helper (is-groupoidᴾ p q i j k) =
    P.heterogeneous-UIP₃ E.is-groupoidʳ (is-groupoidᴾ p q)
      (λ j k → helper (p j k)) (λ j k → helper (q j k)) i j k

-- A non-dependent eliminator, expressed using paths.
--
-- This eliminator is based on one from "Eilenberg-MacLane Spaces in
-- Homotopy Type Theory" by Licata and Finster.

record Recᴾ (G : Group g) (A : Type a) : Type (g ⊔ a) where
  no-eta-equality
  open Group G
  field
    baseʳ        : A
    loopʳ        : Carrier → baseʳ P.≡ baseʳ
    loop-idʳ     : loopʳ id P.≡ P.refl
    loop-∘ʳ      : loopʳ (x ∘ y) P.≡ P.trans (loopʳ x) (loopʳ y)
    is-groupoidʳ : PH.H-level 3 A

open Recᴾ public

recᴾ : Recᴾ G A → K[ G ]1 → A
recᴾ {G} {A} r = elimᴾ λ where
    .is-groupoidʳ _  → R.is-groupoidʳ
    .baseʳ           → R.baseʳ
    .loopʳ           → R.loopʳ
    .loop-idʳ        → R.loop-idʳ
    .loop-∘ʳ {x} {y} →
      R.loopʳ (x ∘ y)                                             P.≡⟨ R.loop-∘ʳ ⟩

      P.trans (R.loopʳ x) (R.loopʳ y)                             P.≡⟨ P.sym $ P.htrans-const (loopᴾ {G = G} x) (loopᴾ y) (R.loopʳ x) ⟩∎

      P.htrans {x≡y = loopᴾ {G = G} x} {y≡z = loopᴾ y} (const A)
        (R.loopʳ x) (R.loopʳ y)                                   ∎
  where
  open Group G
  module R = Recᴾ r

-- A non-dependent eliminator.
--
-- This eliminator is based on one from "Eilenberg-MacLane Spaces in
-- Homotopy Type Theory" by Licata and Finster.

record Rec (G : Group g) (A : Type a) : Type (g ⊔ a) where
  no-eta-equality
  open Group G
  field
    baseʳ        : A
    loopʳ        : Carrier → baseʳ ≡ baseʳ
    loop-idʳ     : loopʳ id ≡ refl baseʳ
    loop-∘ʳ      : loopʳ (x ∘ y) ≡ trans (loopʳ x) (loopʳ y)
    is-groupoidʳ : H-level 3 A

open Rec public

rec : Rec G A → K[ G ]1 → A
rec {G} {A} r = recᴾ λ where
    .is-groupoidʳ → _↔_.to (H-level↔H-level 3) R.is-groupoidʳ
    .baseʳ        → R.baseʳ
    .loopʳ        → _↔_.to ≡↔≡ ⊚ R.loopʳ
    .loop-idʳ     →
      _↔_.to ≡↔≡ (R.loopʳ id)    P.≡⟨ P.cong (_↔_.to ≡↔≡) $ _↔_.to ≡↔≡ R.loop-idʳ ⟩
      _↔_.to ≡↔≡ (refl R.baseʳ)  P.≡⟨ _↔_.to ≡↔≡ to-≡↔≡-refl ⟩∎
      P.refl                     ∎
    .loop-∘ʳ {x} {y} →
      _↔_.to ≡↔≡ (R.loopʳ (x ∘ y))                                 P.≡⟨ P.cong (_↔_.to ≡↔≡) $ _↔_.to ≡↔≡ R.loop-∘ʳ ⟩

      _↔_.to ≡↔≡ (trans (R.loopʳ x) (R.loopʳ y))                   P.≡⟨ _↔_.to ≡↔≡ $ sym $ cong₂ (λ p q → _↔_.to ≡↔≡ (trans p q))
                                                                          (_↔_.left-inverse-of ≡↔≡ _)
                                                                          (_↔_.left-inverse-of ≡↔≡ _) ⟩
      _↔_.to ≡↔≡ (trans (_↔_.from ≡↔≡ (_↔_.to ≡↔≡ (R.loopʳ x)))
                        (_↔_.from ≡↔≡ (_↔_.to ≡↔≡ (R.loopʳ y))))   P.≡⟨ P.cong (_↔_.to ≡↔≡) $ _↔_.to ≡↔≡ trans≡trans ⟩

      (_↔_.to ≡↔≡ $ _↔_.from ≡↔≡ $
       P.trans (_↔_.to ≡↔≡ (R.loopʳ x)) (_↔_.to ≡↔≡ (R.loopʳ y)))  P.≡⟨ _↔_.to ≡↔≡ $ _↔_.right-inverse-of ≡↔≡ _ ⟩∎

      P.trans (_↔_.to ≡↔≡ (R.loopʳ x)) (_↔_.to ≡↔≡ (R.loopʳ y))    ∎
  where
  open Group G
  module R = Rec r

-- A "computation" rule.

rec-loop : cong (rec e) (loop g) ≡ e .loopʳ g
rec-loop = cong-≡↔≡ (refl _)

-- A dependent eliminator that can be used when eliminating into sets,
-- expressed using paths.

record Elim-setᴾ {G : Group g}
                 (P : K[ G ]1 → Type p) : Type (g ⊔ p) where
  no-eta-equality
  open Group G
  field
    baseʳ   : P base
    loopʳ   : ∀ g → P.[ (λ i → P (loopᴾ g i)) ] baseʳ ≡ baseʳ
    is-setʳ : ∀ x → P.Is-set (P x)

open Elim-setᴾ public

elim-setᴾ : Elim-setᴾ P → (x : K[ G ]1) → P x
elim-setᴾ e = elimᴾ λ where
    .baseʳ        → E.baseʳ
    .loopʳ        → E.loopʳ
    .loop-idʳ     → P.heterogeneous-UIP E.is-setʳ _ _ _
    .loop-∘ʳ      → P.heterogeneous-UIP E.is-setʳ _ _ _
    .is-groupoidʳ → PH.mono₁ 2 ⊚ E.is-setʳ
  where
  module E = Elim-setᴾ e

-- A dependent eliminator that can be used when eliminating into sets.

record Elim-set {G : Group g}
                (P : K[ G ]1 → Type p) : Type (g ⊔ p) where
  no-eta-equality
  open Group G
  field
    baseʳ   : P base
    loopʳ   : ∀ g → subst P (loop g) baseʳ ≡ baseʳ
    is-setʳ : ∀ x → Is-set (P x)

open Elim-set public

elim-set : Elim-set P → (x : K[ G ]1) → P x
elim-set e = elim-setᴾ λ where
    .baseʳ   → E.baseʳ
    .loopʳ   → subst≡→[]≡ ⊚ E.loopʳ
    .is-setʳ → _↔_.to (H-level↔H-level 2) ⊚ E.is-setʳ
  where
  module E = Elim-set e

-- A "computation" rule.

elim-set-loop : dcong (elim-set e) (loop g) ≡ e .loopʳ g
elim-set-loop = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator that can be used when eliminating into
-- sets, expressed using paths.

record Rec-setᴾ (G : Group g) (A : Type a) : Type (g ⊔ a) where
  no-eta-equality
  open Group G
  field
    baseʳ   : A
    loopʳ   : Carrier → baseʳ P.≡ baseʳ
    is-setʳ : P.Is-set A

open Rec-setᴾ public

rec-setᴾ : Rec-setᴾ G A → K[ G ]1 → A
rec-setᴾ r = elim-setᴾ λ where
    .baseʳ     → R.baseʳ
    .loopʳ     → R.loopʳ
    .is-setʳ _ → R.is-setʳ
  where
  module R = Rec-setᴾ r

-- A non-dependent eliminator that can be used when eliminating into
-- sets.

record Rec-set (G : Group g) (A : Type a) : Type (g ⊔ a) where
  no-eta-equality
  open Group G
  field
    baseʳ   : A
    loopʳ   : Carrier → baseʳ ≡ baseʳ
    is-setʳ : Is-set A

open Rec-set public

rec-set : Rec-set G A → K[ G ]1 → A
rec-set r = rec-setᴾ λ where
    .baseʳ   → R.baseʳ
    .loopʳ   → _↔_.to ≡↔≡ ⊚ R.loopʳ
    .is-setʳ → _↔_.to (H-level↔H-level 2) R.is-setʳ
  where
  module R = Rec-set r

-- A "computation" rule.

rec-set-loop : cong (rec-set e) (loop g) ≡ e .loopʳ g
rec-set-loop = cong-≡↔≡ (refl _)

-- A dependent eliminator that can be used when eliminating into
-- propositions.

record Elim-prop {G : Group g} (P : K[ G ]1 → Type p) :
                 Type (g ⊔ p) where
  no-eta-equality
  field
    baseʳ           : P base
    is-propositionʳ : ∀ x → Is-proposition (P x)

open Elim-prop public

elim-prop : Elim-prop P → (x : K[ G ]1) → P x
elim-prop e = elim-set λ where
    .baseʳ   → E.baseʳ
    .loopʳ _ → E.is-propositionʳ _ _ _
    .is-setʳ → mono₁ 1 ⊚ E.is-propositionʳ
  where
  module E = Elim-prop e

------------------------------------------------------------------------
-- Universal properties

-- A dependent universal property, restricted to families of sets.
--
-- This property is expressed using P.[_]_≡_.

universal-property-Π-setᴾ :
  (∀ x → P.Is-set (P x)) →
  ((x : K[ G ]1) → P x) ≃
  (∃ λ (x : P base) → ∀ g → P.[ (λ i → P (loopᴾ g i)) ] x ≡ x)
universal-property-Π-setᴾ {G} {P} P-set =
  _↔_.from ≃↔≃ $
  PEq.↔→≃
    (λ f → f base , P.hcong f ⊚ loopᴾ)
    (λ (x , f) → elim-setᴾ λ where
       .baseʳ   → x
       .loopʳ   → f
       .is-setʳ → P-set)
    (λ _ → P.refl)
    (λ f → P.⟨ext⟩ $ elim-setᴾ λ where
       .baseʳ     → P.refl
       .loopʳ _ _ → P.refl
       .is-setʳ _ → PH.mono₁ 2 (P-set _))

-- A variant of the dependent universal property, restricted to
-- families of sets.
--
-- This property is expressed using subst.

universal-property-Π-set :
  (∀ x → Is-set (P x)) →
  ((x : K[ G ]1) → P x) ≃
  (∃ λ (x : P base) → ∀ g → subst P (loop g) x ≡ x)
universal-property-Π-set {G} {P} P-set =
  ((x : K[ G ]1) → P x)                                         ↝⟨ universal-property-Π-setᴾ (_↔_.to (H-level↔H-level 2) ⊚ P-set) ⟩
  (∃ λ (x : P base) → ∀ g → P.[ (λ i → P (loopᴾ g i)) ] x ≡ x)  ↔⟨ (∃-cong λ _ → ∀-cong ext λ _ → inverse subst≡↔[]≡) ⟩□
  (∃ λ (x : P base) → ∀ g → subst P (loop g) x ≡ x)             □

-- A non-dependent universal property, restricted to sets.

universal-property-set :
  Is-set A →
  (K[ G ]1 → A) ≃ (∃ λ (x : A) → Group.Carrier G → x ≡ x)
universal-property-set {A} {G} A-set =
  (K[ G ]1 → A)                      ↝⟨ universal-property-Π-setᴾ (λ _ → _↔_.to (H-level↔H-level 2) A-set) ⟩
  (∃ λ (x : A) → Carrier → x P.≡ x)  ↔⟨ (∃-cong λ _ → ∀-cong ext λ _ → inverse ≡↔≡) ⟩□
  (∃ λ (x : A) → Carrier → x ≡ x)    □
  where
  open Group G

------------------------------------------------------------------------
-- Some conversion functions

-- A map function.
--
-- The existence of such a function was suggested to me by Christian
-- Sattler.

map : G₁ →ᴳ G₂ → K[ G₁ ]1 → K[ G₂ ]1
map {G₁} {G₂} h = rec λ where
    .is-groupoidʳ → is-groupoid
    .baseʳ        → base
    .loopʳ x      → loop (to x)
    .loop-idʳ     →
      loop (to G₁.id)  ≡⟨ cong loop (→ᴳ-id h) ⟩
      loop G₂.id       ≡⟨ loop-id ⟩∎
      refl _           ∎
    .loop-∘ʳ {x} {y} →
      loop (to (x G₁.∘ y))               ≡⟨ cong loop (h .homomorphic x y) ⟩
      loop (to x G₂.∘ to y)              ≡⟨ loop-∘ ⟩∎
      trans (loop (to x)) (loop (to y))  ∎
  where
  module G₁ = Group G₁
  module G₂ = Group G₂
  open Homomorphic h using (to)

-- If G₁ and G₂ are isomorphic groups, then K[ G₁ ]1 and K[ G₂ ]1 are
-- equivalent.

cong-≃ : G₁ ≃ᴳ G₂ → K[ G₁ ]1 ≃ K[ G₂ ]1
cong-≃ G₁≃G₂ = Eq.↔→≃
  (map (↝ᴳ→→ᴳ G₁≃G₂))
  (map (↝ᴳ→→ᴳ (≃ᴳ-sym G₁≃G₂)))
  (lemma (↝ᴳ→→ᴳ G₁≃G₂) (↝ᴳ→→ᴳ (≃ᴳ-sym G₁≃G₂))
     (_≃_.right-inverse-of (related G₁≃G₂)))
  (lemma (↝ᴳ→→ᴳ (≃ᴳ-sym G₁≃G₂)) (↝ᴳ→→ᴳ G₁≃G₂)
     (_≃_.left-inverse-of (related G₁≃G₂)))
  where
  open Homomorphic using (to)

  lemma :
    (f₁ : G₁ →ᴳ G₂) (f₂ : G₂ →ᴳ G₁) →
    (∀ x → to f₁ (to f₂ x) ≡ x) →
    ∀ x → map f₁ (map f₂ x) ≡ x
  lemma f₁ f₂ hyp = elim-set λ where
    .is-setʳ _ → is-groupoid
    .baseʳ     → refl _
    .loopʳ g   →
      subst (λ x → map f₁ (map f₂ x) ≡ x) (loop g) (refl _)          ≡⟨ subst-in-terms-of-trans-and-cong ⟩

      trans (sym $ cong (map f₁ ⊚ map f₂) (loop g))
        (trans (refl _) (cong P.id (loop g)))                        ≡⟨ cong₂ (trans ⊚ sym)
                                                                          (sym $ cong-∘ _ _ _)
                                                                          (trans (trans-reflˡ _) $
                                                                           sym $ cong-id _) ⟩

      trans (sym $ cong (map f₁) $ cong (map f₂) (loop g)) (loop g)  ≡⟨ cong (flip trans (loop g) ⊚ sym) $
                                                                        trans (cong (cong _) rec-loop)
                                                                        rec-loop ⟩

      trans (sym $ loop (to f₁ (to f₂ g))) (loop g)                  ≡⟨ cong (flip trans _ ⊚ sym ⊚ loop) $ hyp _ ⟩

      trans (sym $ loop g) (loop g)                                  ≡⟨ trans-symˡ _ ⟩∎

      refl _                                                         ∎

------------------------------------------------------------------------
-- A lemma

-- The pointed type (K[ G ]1 , base) is connected.
--
-- This result was pointed out to me by Christian Sattler.

connected : Connected (K[ G ]1 , base)
connected = elim-prop λ where
  .is-propositionʳ _ → TP.truncation-is-proposition
  .baseʳ             → TP.∣ refl _ ∣

------------------------------------------------------------------------
-- Some lemmas related to the fundamental group of (K[ G ]1 , base)

-- A variant of the fundamental group of (K[ G ]1 , base) is
-- isomorphic to G (assuming univalence).
--
-- The proof is based on the one given in "Eilenberg-MacLane Spaces in
-- Homotopy Type Theory" by Licata and Finster.

Fundamental-group′[K1]≃ᴳ :
  {G : Group g} →
  Univalence g →
  (s : Is-set (proj₁ (Ω (K[ G ]1 , base)))) →
  Fundamental-group′ (K[ G ]1 , base) s ≃ᴳ G
Fundamental-group′[K1]≃ᴳ {g} {G} univ _ = λ where
    .related     → equiv
    .homomorphic → hom
  where
  module FG = Group (Fundamental-group′ (K[ G ]1 , base) is-groupoid)
  open Group G

  -- Postcomposition is an equivalence.

  to-≃ : Carrier → Carrier ≃ Carrier
  to-≃ x = Eq.↔→≃
    (_∘ x)
    (_∘ x ⁻¹)
    (λ y →
       (y ∘ x ⁻¹) ∘ x  ≡⟨ sym $ assoc _ _ _ ⟩
       y ∘ (x ⁻¹ ∘ x)  ≡⟨ cong (y ∘_) $ left-inverse _ ⟩
       y ∘ id          ≡⟨ right-identity _ ⟩∎
       y               ∎)
    (λ y →
       (y ∘ x) ∘ x ⁻¹  ≡⟨ sym $ assoc _ _ _ ⟩
       y ∘ (x ∘ x ⁻¹)  ≡⟨ cong (y ∘_) $ right-inverse _ ⟩
       y ∘ id          ≡⟨ right-identity _ ⟩∎
       y               ∎)

  -- A family of codes.

  Code : K[ G ]1 → Set g
  Code = rec λ where
    .is-groupoidʳ → ∃-H-level-H-level-1+ ext univ 2
    .baseʳ        → Carrier , Carrier-is-set
    .loopʳ x      → Σ-≡,≡→≡ (≃⇒≡ univ (to-≃ x))
                      (H-level-propositional ext 2 _ _)
    .loop-idʳ     →
      Σ-≡,≡→≡ (≃⇒≡ univ (to-≃ id)) _     ≡⟨ _≃_.from (Eq.≃-≡ $ Eq.↔⇒≃ B.Σ-≡,≡↔≡) $
                                            Σ-≡,≡→≡
                                              (
          ≃⇒≡ univ (to-≃ id)                   ≡⟨ cong (≃⇒≡ univ) $ Eq.lift-equality ext $ ⟨ext⟩
                                                  right-identity ⟩
          ≃⇒≡ univ Eq.id                       ≡⟨ ≃⇒≡-id univ ⟩∎
          refl _                               ∎)
                                              (H-level.⇒≡ 1 (H-level-propositional ext 2) _ _) ⟩

      Σ-≡,≡→≡ (refl _) (subst-refl _ _)  ≡⟨ Σ-≡,≡→≡-refl-subst-refl ⟩∎

      refl _                             ∎
    .loop-∘ʳ {x} {y} →
      Σ-≡,≡→≡ (≃⇒≡ univ (to-≃ (x ∘ y))) _                        ≡⟨ _≃_.from (Eq.≃-≡ $ Eq.↔⇒≃ B.Σ-≡,≡↔≡) $
                                                                    Σ-≡,≡→≡
                                                                      (
          ≃⇒≡ univ (to-≃ (x ∘ y))                                      ≡⟨ (cong (≃⇒≡ univ) $ Eq.lift-equality ext $ ⟨ext⟩ λ _ →
                                                                           assoc _ _ _) ⟩
          ≃⇒≡ univ (to-≃ y Eq.∘ to-≃ x)                                ≡⟨ ≃⇒≡-∘ univ ext _ _ ⟩∎
          trans (≃⇒≡ univ (to-≃ x)) (≃⇒≡ univ (to-≃ y))                ∎)
                                                                      (H-level.⇒≡ 1 (H-level-propositional ext 2) _ _) ⟩

      Σ-≡,≡→≡ (trans (≃⇒≡ univ (to-≃ x)) (≃⇒≡ univ (to-≃ y))) _  ≡⟨ sym $ trans-Σ-≡,≡→≡ _ _ _ _ ⟩∎

      trans (Σ-≡,≡→≡ (≃⇒≡ univ (to-≃ x)) _)
        (Σ-≡,≡→≡ (≃⇒≡ univ (to-≃ y)) _)                          ∎

  -- Some "computation" rules.

  ≡⇒≃-cong-Code-loop :
    ≡⇒≃ (cong (proj₁ ⊚ Code) (loop x)) ≡ to-≃ x
  ≡⇒≃-cong-Code-loop {x} =
    ≡⇒≃ (cong (proj₁ ⊚ Code) (loop x))         ≡⟨ cong ≡⇒≃ $ sym $ cong-∘ proj₁ Code (loop x) ⟩

    ≡⇒≃ (cong proj₁ (cong Code (loop x)))      ≡⟨ cong (≡⇒≃ ⊚ cong proj₁) rec-loop ⟩

    ≡⇒≃ (cong proj₁ $
         Σ-≡,≡→≡ (≃⇒≡ univ (to-≃ x))
           (H-level-propositional ext 2 _ _))  ≡⟨ cong ≡⇒≃ $ proj₁-Σ-≡,≡→≡ _ _ ⟩

    ≡⇒≃ (≃⇒≡ univ (to-≃ x))                    ≡⟨ _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎

    to-≃ x                                     ∎

  subst-Code-loop :
    subst (proj₁ ⊚ Code) (loop x) ≡ _∘ x
  subst-Code-loop {x} = ⟨ext⟩ λ y →
    subst (proj₁ ⊚ Code) (loop x) y                ≡⟨ subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
    _≃_.to (≡⇒≃ (cong (proj₁ ⊚ Code) (loop x))) y  ≡⟨ cong (λ eq → _≃_.to eq y) ≡⇒≃-cong-Code-loop ⟩∎
    _≃_.to (to-≃ x) y                              ∎

  subst-Code-sym-loop :
    subst (proj₁ ⊚ Code) (sym (loop x)) ≡ _∘ x ⁻¹
  subst-Code-sym-loop {x} = ⟨ext⟩ λ y →
    subst (proj₁ ⊚ Code) (sym (loop x)) y            ≡⟨ subst-in-terms-of-inverse∘≡⇒↝ equivalence _ _ _ ⟩
    _≃_.from (≡⇒≃ (cong (proj₁ ⊚ Code) (loop x))) y  ≡⟨ cong (λ eq → _≃_.from eq y) ≡⇒≃-cong-Code-loop ⟩∎
    _≃_.from (to-≃ x) y                              ∎

  -- An equivalence.

  to : base ≡ x → proj₁ (Code x)
  to eq = subst (proj₁ ⊚ Code) eq id

  from : ∀ x → proj₁ (Code x) → base ≡ x
  from = elim-set λ where
    .is-setʳ _ → Π-closure ext 2 λ _ →
                 is-groupoid
    .baseʳ     → loop
    .loopʳ x   → ⟨ext⟩ λ y →
      subst (λ x → proj₁ (Code x) → base ≡ x) (loop x) loop y        ≡⟨ subst-→ ⟩

      subst (base ≡_) (loop x)
        (loop (subst (proj₁ ⊚ Code) (sym (loop x)) y))               ≡⟨ sym trans-subst ⟩

      trans (loop (subst (proj₁ ⊚ Code) (sym (loop x)) y)) (loop x)  ≡⟨ cong (flip trans (loop x) ⊚ loop ⊚ (_$ y))
                                                                        subst-Code-sym-loop ⟩

      trans (loop (y ∘ x ⁻¹)) (loop x)                               ≡⟨ cong (flip trans _) loop-∘ ⟩

      trans (trans (loop y) (loop (x ⁻¹))) (loop x)                  ≡⟨ trans-assoc _ _ _ ⟩

      trans (loop y) (trans (loop (x ⁻¹)) (loop x))                  ≡⟨ cong (trans _) $ sym loop-∘ ⟩

      trans (loop y) (loop (x ⁻¹ ∘ x))                               ≡⟨ cong (trans (loop y) ⊚ loop) $ left-inverse _ ⟩

      trans (loop y) (loop id)                                       ≡⟨ cong (trans _) loop-id ⟩

      trans (loop y) (refl base)                                     ≡⟨ trans-reflʳ _ ⟩∎

      loop y                                                         ∎

  to-loop : ∀ x → to (loop x) ≡ x
  to-loop x =
    subst (proj₁ ⊚ Code) (loop x) id  ≡⟨ cong (_$ id) subst-Code-loop ⟩
    id ∘ x                            ≡⟨ left-identity _ ⟩∎
    x                                 ∎

  from-to : ∀ eq → from x (to eq) ≡ eq
  from-to = elim¹ (λ {x} eq → from x (to eq) ≡ eq)
    (loop (subst (proj₁ ⊚ Code) (refl base) id)  ≡⟨ cong loop $ subst-refl _ _ ⟩
     loop id                                     ≡⟨ loop-id ⟩∎
     refl base                                   ∎)

  equiv : proj₁ (Ω (K[ G ]1 , base)) ≃ Carrier
  equiv =
    base ≡ base  ↝⟨ Eq.↔→≃ to loop to-loop from-to ⟩□
    Carrier      □

  -- The equivalence is homomorphic.

  hom′ :
    ∀ x y →
    _≃_.from equiv (x ∘ y) ≡
    _≃_.from equiv x FG.∘ _≃_.from equiv y
  hom′ x y =
    loop (x ∘ y)             ≡⟨ loop-∘ ⟩∎
    trans (loop x) (loop y)  ∎

  hom :
    ∀ p q →
    _≃_.to equiv (p FG.∘ q) ≡
    _≃_.to equiv p ∘ _≃_.to equiv q
  hom p q = _≃_.from-to equiv
    (_≃_.from equiv (_≃_.to equiv p ∘ _≃_.to equiv q)  ≡⟨ hom′ _ _ ⟩

     _≃_.from equiv (_≃_.to equiv p) FG.∘
     _≃_.from equiv (_≃_.to equiv q)                   ≡⟨ cong₂ FG._∘_
                                                            (_≃_.left-inverse-of equiv p)
                                                            (_≃_.left-inverse-of equiv q) ⟩∎
     p FG.∘ q                                          ∎)

-- The right-to-left direction of Fundamental-group′[K1]≃ᴳ is loop.

_ :
  {G : Group g} {univ : Univalence g} {s : Is-set _} →
  _≃_.from (Fundamental-group′[K1]≃ᴳ {G = G} univ s .related) ≡
  loop
_ = refl _

-- The fundamental group of (K[ G ]1 , base) is isomorphic to G
-- (assuming univalence).
--
-- The proof is based on the one given in "Eilenberg-MacLane Spaces in
-- Homotopy Type Theory" by Licata and Finster.

Fundamental-group[K1]≃ᴳ :
  {G : Group g} →
  Univalence g →
  Fundamental-group (K[ G ]1 , base) ≃ᴳ G
Fundamental-group[K1]≃ᴳ univ =
  ↝ᴳ-trans (≃ᴳ-sym Homotopy-group-[1+]′≃ᴳHomotopy-group-[1+])
    (Fundamental-group′[K1]≃ᴳ univ is-groupoid)

-- If G is abelian, then the fundamental group of (K[ G ]1 , base) is
-- abelian.

Abelian→Abelian-Fundamental-group′ :
  Abelian G → Abelian (Fundamental-group′ (K[ G ]1 , base) is-groupoid)
Abelian→Abelian-Fundamental-group′ {G} abelian =
  flip $ EG.Transitivity-commutative.commutative base _∙_ ∙-base base-∙
  where
  open Group G

  lemma : Carrier → (x : K[ G ]1) → x ≡ x
  lemma g₁ = elim-set λ where
    .is-setʳ  → λ _ → is-groupoid
    .baseʳ    → loop g₁
    .loopʳ g₂ → ≡⇒↝ _ (sym [subst≡]≡[trans≡trans])
      (trans (loop g₁) (loop g₂)  ≡⟨ sym loop-∘ ⟩
       loop (g₁ ∘ g₂)             ≡⟨ cong loop (abelian g₁ g₂) ⟩
       loop (g₂ ∘ g₁)             ≡⟨ loop-∘ ⟩∎
       trans (loop g₂) (loop g₁)  ∎)

  lemma-id : ∀ x → lemma id x ≡ refl x
  lemma-id = elim-prop λ where
    .is-propositionʳ _ → is-groupoid
    .baseʳ →
      loop id    ≡⟨ loop-id ⟩∎
      refl base  ∎

  lemma-∘ :
    ∀ g₁ g₂ x → lemma (g₁ ∘ g₂) x ≡ trans (lemma g₁ x) (lemma g₂ x)
  lemma-∘ g₁ g₂ = elim-prop λ where
    .is-propositionʳ _ → is-groupoid
    .baseʳ →
      loop (g₁ ∘ g₂)             ≡⟨ loop-∘ ⟩∎
      trans (loop g₁) (loop g₂)  ∎

  _∙_ : K[ G ]1 → K[ G ]1 → K[ G ]1
  _∙_ x = rec λ where
    .is-groupoidʳ → is-groupoid
    .baseʳ    → x
    .loopʳ g  → lemma g x
    .loop-idʳ → lemma-id x
    .loop-∘ʳ  → lemma-∘ _ _ x

  base-∙ : ∀ x → x ∙ base ≡ x
  base-∙ _ = refl _

  ∙-base : ∀ y → base ∙ y ≡ y
  ∙-base = elim-set λ where
    .is-setʳ _ → is-groupoid
    .baseʳ     → refl _
    .loopʳ y   →
      subst (λ y → base ∙ y ≡ y) (loop y) (refl _)    ≡⟨ subst-in-terms-of-trans-and-cong ⟩

      trans (sym (cong (base ∙_) (loop y)))
        (trans (refl _) (cong P.id (loop y)))         ≡⟨ cong (trans _) $
                                                         trans (trans-reflˡ _) $
                                                         sym $ cong-id _ ⟩

      trans (sym (cong (base ∙_) (loop y))) (loop y)  ≡⟨ cong (flip trans (loop y) ⊚ sym) $
                                                         rec-loop ⟩

      trans (sym (loop y)) (loop y)                   ≡⟨ trans-symˡ _ ⟩∎

      refl _                                          ∎

-- If P is a groupoid, then there is a based embedding from
-- (K[ Fundamental-group′ P s ]1 , base) to P (assuming univalence).
--
-- Christian Sattler showed me a similar proof of this result.

K[Fundamental-group′]1↣ᴮ :
  {P : Pointed-type p} {s : Is-set (proj₁ (Ω P))} →
  Univalence p →
  H-level 3 (proj₁ P) →
  (K[ Fundamental-group′ P s ]1 , base) ↝[ embedding ]ᴮ P
K[Fundamental-group′]1↣ᴮ {P = P@(A , a)} {s} univ g =
  record { to = to; is-embedding = emb } , refl _
  where
  to : K[ Fundamental-group′ P s ]1 → A
  to = rec λ where
    .baseʳ        → a
    .loopʳ        → P.id
    .loop-idʳ     → refl _
    .loop-∘ʳ      → refl _
    .is-groupoidʳ → g

  iso :
    Fundamental-group′ P s ≃ᴳ
    Fundamental-group′ (K[ Fundamental-group′ P s ]1 , base) is-groupoid
  iso = ≃ᴳ-sym $ Fundamental-group′[K1]≃ᴳ univ is-groupoid

  cong-to-iso : cong to ⊚ Homomorphic.to iso ≡ P.id
  cong-to-iso = ⟨ext⟩ λ eq →
    cong to (loop eq)  ≡⟨ rec-loop ⟩∎
    eq                 ∎

  cong-to-equivalence :
    Eq.Is-equivalence (cong {x = base} {y = base} to)
  cong-to-equivalence = Eq.Two-out-of-three.g∘f-f
    (Eq.two-out-of-three _ _)
    (Is-equivalence-cong _ (ext⁻¹ (sym cong-to-iso))
       (_≃_.is-equivalence Eq.id))
    (_≃_.is-equivalence (iso .related))

  emb : Is-embedding to
  emb = elim-prop λ where
    .is-propositionʳ _ →
      Π-closure ext 1 λ _ →
      Is-equivalence-propositional ext
    .baseʳ → elim-prop λ where
      .is-propositionʳ _ → Is-equivalence-propositional ext
      .baseʳ             → cong-to-equivalence

-- If P is a connected groupoid, then there is a based equivalence
-- from (K[ Fundamental-group′ P s ]1 , base) to P (assuming
-- univalence).
--
-- Christian Sattler showed me a similar proof of this result.

K[Fundamental-group′]1≃ᴮ :
  {P : Pointed-type p} {s : Is-set (proj₁ (Ω P))} →
  Univalence p →
  H-level 3 (proj₁ P) →
  Connected P →
  (K[ Fundamental-group′ P s ]1 , base) ≃ᴮ P
K[Fundamental-group′]1≃ᴮ {P = P@(A , a)} {s} univ g conn =
    Eq.⟨ Embedding.to (proj₁ f)
       , _≃_.to TP.surjective×embedding≃equivalence
           (surj , Embedding.is-embedding (proj₁ f)) ⟩
  , proj₂ f
  where
  f = K[Fundamental-group′]1↣ᴮ univ g

  surj : Surjective (Embedding.to (proj₁ f))
  surj x = flip TP.∥∥-map (conn x) λ a≡x →
      base
    , (Embedding.to (proj₁ f) base  ≡⟨⟩
       a                            ≡⟨ a≡x ⟩∎
       x                            ∎)

------------------------------------------------------------------------
-- Another result related to a fundamental group

-- If G is abelian, then the fundamental group of
-- (K[ G ]1 ≃ K[ G ]1 , Eq.id) is isomorphic to G (assuming
-- univalence).
--
-- I was informed of a related result by Christian Sattler.

Fundamental-group′[K1≃K1]≃ᴳ :
  {G : Group g} {s : Is-set _} →
  Univalence g →
  Abelian G →
  Fundamental-group′ ((K[ G ]1 ≃ K[ G ]1) , Eq.id) s ≃ᴳ G
Fundamental-group′[K1≃K1]≃ᴳ {G} univ abelian = λ where
    .related →
      _≡_ {A = K[ G ]1 ≃ K[ G ]1} Eq.id Eq.id  ↝⟨ inverse $ ≃-to-≡≃≡ ext ext ⟩
      ((x : K[ G ]1) → x ≡ x)                  ↝⟨ Eq.↔→≃ to from to-from from-to ⟩□
      Carrier                                  □
    .homomorphic p q →
      Homomorphic.to iso (cong (λ eq → _≃_.to eq base) (trans p q))  ≡⟨ cong (Homomorphic.to iso) $
                                                                        cong-trans _ _ _ ⟩
      Homomorphic.to iso
        (trans (cong (λ eq → _≃_.to eq base) p)
               (cong (λ eq → _≃_.to eq base) q))                     ≡⟨ Homomorphic.homomorphic iso _ _ ⟩∎

      Homomorphic.to iso (cong (λ eq → _≃_.to eq base) p) ∘
      Homomorphic.to iso (cong (λ eq → _≃_.to eq base) q)            ∎
  where
  open Group G

  iso = Fundamental-group′[K1]≃ᴳ {G = G} univ is-groupoid

  to : ((x : K[ G ]1) → x ≡ x) → Carrier
  to f = Homomorphic.to iso (f base)

  from : Carrier → (x : K[ G ]1) → x ≡ x
  from x = elim-set λ where
    .is-setʳ _ → is-groupoid
    .baseʳ     → loop x
    .loopʳ y   → ≡⇒↝ _ (sym [subst≡]≡[trans≡trans])
      (trans (loop x) (loop y)  ≡⟨ sym loop-∘ ⟩
       loop (x ∘ y)             ≡⟨ cong loop $ abelian x y ⟩
       loop (y ∘ x)             ≡⟨ loop-∘ ⟩∎
       trans (loop y) (loop x)  ∎)

  to-from : ∀ p → to (from p) ≡ p
  to-from x =
    Homomorphic.to iso (loop x)  ≡⟨ _≃_.right-inverse-of (Homomorphic.related iso) _ ⟩∎
    x                            ∎

  from-to : ∀ f → from (to f) ≡ f
  from-to f = ⟨ext⟩ $ elim-prop λ where
    .is-propositionʳ _ → is-groupoid
    .baseʳ             →
      loop (Homomorphic.to iso (f base))  ≡⟨ _≃_.left-inverse-of (Homomorphic.related iso) _ ⟩∎
      f base                              ∎
