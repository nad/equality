------------------------------------------------------------------------
-- Paths, extensionality and univalence
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Equality.Path where

open import Agda.Builtin.Cubical.Glue as Glue hiding (_≃_)

import Bijection
open import Equality hiding (module Derived-definitions-and-properties)
open import Equality.Instances-related
import Equivalence
import Function-universe
import H-level
open import Logical-equivalence using (_⇔_)
import Preimage
open import Prelude
import Univalence-axiom

------------------------------------------------------------------------
-- The interval

open import Agda.Primitive.Cubical public
  using (I; Partial; PartialP)
  renaming (i0 to 0̲; i1 to 1̲;
            IsOne to Is-one; itIsOne to is-one;
            primINeg to -_; primIMin to min; primIMax to max;
            primComp to comp; primHComp to hcomp;
            primTransp to transport)

open import Agda.Builtin.Cubical.Sub public
  renaming (Sub to _[_↦_]; inc to inˢ; primSubOut to outˢ)

------------------------------------------------------------------------
-- Some local generalisable variables

private
  variable
    a b c p q ℓ : Level
    A           : Set a
    B           : A → Set b
    P           : I → Set p
    x y z       : A
    f g h       : (x : A) → B x
    i j         : I
    n           : ℕ

------------------------------------------------------------------------
-- Equality

-- Homogeneous equality.

open import Agda.Builtin.Cubical.Path public using (_≡_)

-- Heterogeneous equality.

infix 4 [_]_≡_

[_]_≡_ : (P : I → Set p) → P 0̲ → P 1̲ → Set p
[_]_≡_ = Agda.Builtin.Cubical.Path.PathP

------------------------------------------------------------------------
-- Filling

-- The code in this section is based on code in the cubical library
-- written by Anders Mörtberg.

-- Filling for homogenous composition.

hfill :
  {φ : I} (u : I → Partial φ A) (u₀ : A [ φ ↦ u 0̲ ]) →
  outˢ u₀ ≡ hcomp u (outˢ u₀)
hfill {φ = φ} u u₀ = λ i →
  hcomp (λ j → λ { (φ = 1̲) → u (min i j) is-one
                 ; (i = 0̲) → outˢ u₀
                 })
        (outˢ u₀)

-- Filling for heterogeneous composition.
--
-- Note that if p had been a constant level, then the final line of
-- the type signature could have been replaced by
-- [ P ] outˢ u₀ ≡ comp P u u₀.

fill :
  {p : I → Level}
  (P : ∀ i → Set (p i)) {φ : I}
  (u : ∀ i → Partial φ (P i))
  (u₀ : P 0̲ [ φ ↦ u 0̲ ]) →
  ∀ i → P i
fill P {φ} u u₀ i =
  comp (λ j → P (min i j))
       (λ j → λ { (φ = 1̲) → u (min i j) is-one
                ; (i = 0̲) → outˢ u₀
                })
       (outˢ u₀)

-- Filling for transport.

transport-fill :
  (A : Set ℓ)
  (φ : I)
  (P : (i : I) → Set ℓ [ φ ↦ (λ _ → A) ])
  (u₀ : outˢ (P 0̲)) →
  [ (λ i → outˢ (P i)) ]
    u₀ ≡ transport (λ i → outˢ (P i)) φ u₀
transport-fill _ φ P u₀ i =
  transport (λ j → outˢ (P (min i j))) (max (- i) φ) u₀

------------------------------------------------------------------------
-- Path equality satisfies the axioms of Equality-with-J

-- Reflexivity.

refl : x ≡ x
refl {x = x} = λ _ → x

-- A family of instantiations of Reflexive-relation.

reflexive-relation : ∀ ℓ → Reflexive-relation ℓ
Reflexive-relation._≡_  (reflexive-relation _) = _≡_
Reflexive-relation.refl (reflexive-relation _) = λ _ → refl

-- Symmetry.

hsym : [ P ] x ≡ y → [ (λ i → P (- i)) ] y ≡ x
hsym x≡y = λ i → x≡y (- i)

-- Transitivity.
--
-- The proof htransʳ-reflʳ is based on code in Agda's reference manual
-- written by Anders Mörtberg.
--
-- The proof htrans is suggested in the HoTT book (first version,
-- Exercise 6.1).

htransʳ : [ P ] x ≡ y → y ≡ z → [ P ] x ≡ z
htransʳ {x = x} x≡y y≡z = λ i →
  hcomp (λ { _ (i = 0̲) → x
           ; j (i = 1̲) → y≡z j
           })
        (x≡y i)

htransˡ : x ≡ y → [ P ] y ≡ z → [ P ] x ≡ z
htransˡ x≡y y≡z = hsym (htransʳ (hsym y≡z) (hsym x≡y))

htransʳ-reflʳ : (x≡y : [ P ] x ≡ y) → htransʳ x≡y refl ≡ x≡y
htransʳ-reflʳ {x = x} {y = y} x≡y = λ i j →
  hfill (λ { _ (j = 0̲) → x
           ; _ (j = 1̲) → y
           })
        (inˢ (x≡y j))
        (- i)

htransˡ-reflˡ : (x≡y : [ P ] x ≡ y) → htransˡ refl x≡y ≡ x≡y
htransˡ-reflˡ = htransʳ-reflʳ

htrans :
  {x≡y : x ≡ y} {y≡z : y ≡ z}
  (P : A → Set p) {p : P x} {q : P y} {r : P z} →
  [ (λ i → P (x≡y i)) ] p ≡ q →
  [ (λ i → P (y≡z i)) ] q ≡ r →
  [ (λ i → P (htransˡ x≡y y≡z i)) ] p ≡ r
htrans {z = z} {x≡y = x≡y} {y≡z = y≡z} P {r = r} p≡q q≡r = λ i →
  comp (λ j → P (eq j i))
       (λ { j (i = 0̲) → p≡q (- j)
          ; j (i = 1̲) → r
          })
       (q≡r i)
  where
  eq : [ (λ i → x≡y (- i) ≡ z) ] y≡z ≡ htransˡ x≡y y≡z
  eq = λ i j →
    hfill (λ { i (j = 0̲) → x≡y (- i)
             ; _ (j = 1̲) → z
             })
          (inˢ (y≡z j))
          i

-- Some equational reasoning combinators.

infix  -1 finally finally-h
infixr -2 step-≡ step-≡h step-≡hh _≡⟨⟩_

step-≡ : ∀ x → [ P ] y ≡ z → x ≡ y → [ P ] x ≡ z
step-≡ _ = flip htransˡ

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

step-≡h : ∀ x → y ≡ z → [ P ] x ≡ y → [ P ] x ≡ z
step-≡h _ = flip htransʳ

syntax step-≡h x y≡z x≡y = x ≡⟨ x≡y ⟩h y≡z

step-≡hh :
  {x≡y : x ≡ y} {y≡z : y ≡ z}
  (P : A → Set p) (p : P x) {q : P y} {r : P z} →
  [ (λ i → P (y≡z i)) ] q ≡ r →
  [ (λ i → P (x≡y i)) ] p ≡ q →
  [ (λ i → P (htransˡ x≡y y≡z i)) ] p ≡ r
step-≡hh P _ = flip (htrans P)

syntax step-≡hh P p q≡r p≡q = p ≡⟨ p≡q ⟩[ P ] q≡r

_≡⟨⟩_ : ∀ x → [ P ] x ≡ y → [ P ] x ≡ y
_ ≡⟨⟩ x≡y = x≡y

finally : (x y : A) → x ≡ y → x ≡ y
finally _ _ x≡y = x≡y

syntax finally x y x≡y = x ≡⟨ x≡y ⟩∎ y ∎

finally-h : ∀ x y → [ P ] x ≡ y → [ P ] x ≡ y
finally-h _ _ x≡y = x≡y

syntax finally-h x y x≡y = x ≡⟨ x≡y ⟩∎h y ∎

-- The J rule.

elim :
  (P : {x y : A} → x ≡ y → Set p) →
  (∀ x → P (refl {x = x})) →
  (x≡y : x ≡ y) → P x≡y
elim {x = x} P p x≡y =
  transport (λ i → P (λ j → x≡y (min i j))) 0̲ (p x)

-- Substitutivity.

hsubst :
  ∀ (Q : ∀ {i} → P i → Set q) →
  [ P ] x ≡ y → Q x → Q y
hsubst Q x≡y p = transport (λ i → Q (x≡y i)) 0̲ p

subst : (P : A → Set p) → x ≡ y → P x → P y
subst P = hsubst P

-- Congruence.
--
-- The heterogeneous variant is based on code in the cubical library
-- written by Anders Mörtberg.

hcong :
  (f : (x : A) → B x) (x≡y : x ≡ y) →
  [ (λ i → B (x≡y i)) ] f x ≡ f y
hcong f x≡y = λ i → f (x≡y i)

cong : {B : Set b} (f : A → B) → x ≡ y → f x ≡ f y
cong f = hcong f

dcong :
  (f : (x : A) → B x) (x≡y : x ≡ y) →
  subst B x≡y (f x) ≡ f y
dcong {B = B} f x≡y = λ i →
  transport (λ j → B (x≡y (max i j))) i (f (x≡y i))

-- Transporting along reflexivity amounts to doing nothing.
--
-- This definition is based on code in Agda's reference manual written
-- by Anders Mörtberg.

transport-refl : ∀ i → transport (λ i → refl {x = A} i) i ≡ id
transport-refl {A = A} i = λ j → transport (λ _ → A) (max i j)

-- A family of instantiations of Equivalence-relation⁺.
--
-- Note that htransˡ is used to implement trans. The reason htransˡ is
-- used, rather than htransʳ, is that htransˡ is also used to
-- implement the commonly used equational reasoning combinator step-≡,
-- and I'd like this combinator to match trans.

equivalence-relation⁺ : ∀ ℓ → Equivalence-relation⁺ ℓ
equivalence-relation⁺ _ = λ where
  .Equivalence-relation⁺.reflexive-relation → reflexive-relation _
  .Equivalence-relation⁺.sym                → hsym
  .Equivalence-relation⁺.sym-refl           → refl
  .Equivalence-relation⁺.trans              → htransˡ
  .Equivalence-relation⁺.trans-refl-refl    → htransˡ-reflˡ _

-- A family of instantiations of Equality-with-J₀.

equality-with-J₀ : Equality-with-J₀ a p reflexive-relation
Equality-with-J₀.elim      equality-with-J₀ = elim
Equality-with-J₀.elim-refl equality-with-J₀ = λ _ r →
  cong (_$ r _) $ transport-refl 0̲

private
 module Temporarily-local where

  -- A family of instantiations of Equality-with-J.

  equality-with-J : Equality-with-J a p equivalence-relation⁺
  equality-with-J = λ where
    .Equality-with-J.equality-with-J₀ → equality-with-J₀
    .Equality-with-J.cong             → cong
    .Equality-with-J.cong-refl        → λ _ → refl
    .Equality-with-J.subst            → subst
    .Equality-with-J.subst-refl       → λ _ p →
                                          cong (_$ p) $ transport-refl 0̲
    .Equality-with-J.dcong            → dcong
    .Equality-with-J.dcong-refl       → λ _ → refl

-- Various derived definitions and properties.

open Equality.Derived-definitions-and-properties
       Temporarily-local.equality-with-J public
  hiding (_≡_; refl; elim; subst; cong; dcong;
          step-≡; _≡⟨⟩_; finally;
          reflexive-relation; equality-with-J₀)

------------------------------------------------------------------------
-- An extended variant of Equality-with-J

-- The following variant of Equality-with-J includes functions mapping
-- equalities to and from paths. The purpose of this definition is to
-- make it possible to instantiate these functions with identity
-- functions when paths are used as equalities (see
-- equality-with-paths below).

record Equality-with-paths
         a b (e⁺ : ∀ ℓ → Equivalence-relation⁺ ℓ) :
         Set (lsuc (a ⊔ b)) where

  field
    equality-with-J : Equality-with-J a b e⁺

  private
    module R =
      Reflexive-relation
        (Equivalence-relation⁺.reflexive-relation (e⁺ a))

  field

    -- A bijection between equality at level a and paths.

    to-path           : x R.≡ y → x ≡ y
    from-path         : x ≡ y → x R.≡ y
    to-path∘from-path : (x≡y : x ≡ y) → to-path (from-path x≡y) R.≡ x≡y
    from-path∘to-path :
      (x≡y : x R.≡ y) → from-path (to-path x≡y) R.≡ x≡y

    -- The bijection maps reflexivity to reflexivity.

    to-path-refl   : to-path (R.refl x) R.≡ refl
    from-path-refl : from-path refl R.≡ R.refl x

-- A family of instantiations of Equality-with-paths.

equality-with-paths :
  Equality-with-paths a p equivalence-relation⁺
equality-with-paths = λ where
    .E.equality-with-J   → Temporarily-local.equality-with-J
    .E.to-path           → id
    .E.from-path         → id
    .E.to-path∘from-path → λ _ → refl
    .E.from-path∘to-path → λ _ → refl
    .E.to-path-refl      → refl
    .E.from-path-refl    → refl
  where
  module E = Equality-with-paths

-- Equality-with-paths (for arbitrary universe levels) can be derived
-- from Equality-with-J (for arbitrary universe levels).

Equality-with-J⇒Equality-with-paths :
  ∀ {e⁺} →
  (∀ {a p} → Equality-with-J a p e⁺) →
  (∀ {a p} → Equality-with-paths a p e⁺)
Equality-with-J⇒Equality-with-paths eq = λ where
    .E.equality-with-J   → eq
    .E.to-path           → B._↔_.to (proj₁ ≡↔≡′)
    .E.from-path         → B._↔_.from (proj₁ ≡↔≡′)
    .E.to-path∘from-path → B._↔_.right-inverse-of (proj₁ ≡↔≡′)
    .E.from-path∘to-path → B._↔_.left-inverse-of (proj₁ ≡↔≡′)
    .E.to-path-refl      → B._↔_.from (proj₁ ≡↔≡′) (proj₁ (proj₂ ≡↔≡′))
    .E.from-path-refl    → proj₂ (proj₂ ≡↔≡′)
  where
  module E = Equality-with-paths
  module B = Bijection eq

  ≡↔≡′ =
    all-equality-types-isomorphic eq Temporarily-local.equality-with-J

-- Equality-with-paths (for arbitrary universe levels) can be derived
-- from Equality-with-J₀ (for arbitrary universe levels).

Equality-with-J₀⇒Equality-with-paths :
  ∀ {reflexive} →
  (eq : ∀ {a p} → Equality-with-J₀ a p reflexive) →
  ∀ {a p} → Equality-with-paths a p (λ _ → J₀⇒Equivalence-relation⁺ eq)
Equality-with-J₀⇒Equality-with-paths eq =
  Equality-with-J⇒Equality-with-paths (J₀⇒J eq)

module Derived-definitions-and-properties
  {e⁺}
  (equality-with-paths : ∀ {a p} → Equality-with-paths a p e⁺)
  where

  private
    module EP {a} {p} =
      Equality-with-paths (equality-with-paths {a = a} {p = p})

  open EP public using (equality-with-J)

  private
    module E =
      Equality.Derived-definitions-and-properties
        equality-with-J

  open Bijection equality-with-J

  ≡↔≡ : {A : Set a} {x y : A} → x E.≡ y ↔ x ≡ y
  ≡↔≡ {a = a} = record
    { surjection = record
      { logical-equivalence = record
        { to   = EP.to-path {p = a}
        ; from = EP.from-path
        }
      ; right-inverse-of = EP.to-path∘from-path
      }
    ; left-inverse-of = EP.from-path∘to-path
    }

  -- The isomorphism maps reflexivity to reflexivity.

  to-≡↔≡-refl : _↔_.to ≡↔≡ (E.refl x) E.≡ refl
  to-≡↔≡-refl = EP.to-path-refl

  from-≡↔≡-refl : _↔_.from ≡↔≡ refl E.≡ E.refl x
  from-≡↔≡-refl = EP.from-path-refl

  open E public

open Temporarily-local public

------------------------------------------------------------------------
-- Extensionality

open Equivalence equality-with-J using (Is-equivalence)

-- Extensionality.

ext : Extensionality a b
apply-ext ext f≡g = λ i x → f≡g x i

⟨ext⟩ : Extensionality′ A B
⟨ext⟩ = apply-ext ext

-- The function ⟨ext⟩ is an equivalence.

ext-is-equivalence : Is-equivalence {A = ∀ x → f x ≡ g x} ⟨ext⟩
ext-is-equivalence f≡g =
    ( (λ x → cong (_$ x) f≡g)
    , refl
    )
  , λ { (f≡g′ , ⟨ext⟩f≡g′≡f≡g) i →
          (λ x → cong (_$ x) (sym ⟨ext⟩f≡g′≡f≡g i))
        , (λ j → ⟨ext⟩f≡g′≡f≡g (max (- i) j))
      }

private

  -- Equality rearrangement lemmas for ⟨ext⟩. All of these lemmas hold
  -- definitionally.

  ext-refl : ⟨ext⟩ (λ x → refl {x = f x}) ≡ refl
  ext-refl = refl

  cong-ext :
    (f≡g : ∀ x → f x ≡ g x) →
    cong (_$ x) (⟨ext⟩ f≡g) ≡ f≡g x
  cong-ext _ = refl

  subst-ext :
    ∀ {p} (f≡g : ∀ x → f x ≡ g x) →
    subst (λ f → B (f x)) (⟨ext⟩ f≡g) p ≡ subst B (f≡g x) p
  subst-ext _ = refl

  elim-ext :
    {f g : (x : A) → B x}
    (P : B x → B x → Set p)
    (p : (y : B x) → P y y)
    (f≡g : ∀ x → f x ≡ g x) →
    elim (λ {f g} _ → P (f x) (g x)) (p ∘ (_$ x)) (⟨ext⟩ f≡g) ≡
    elim (λ {x y} _ → P x y) p (f≡g x)
  elim-ext _ _ _ = refl

  -- I based the statements of the following three lemmas on code in
  -- the Lean Homotopy Type Theory Library with Jakob von Raumer and
  -- Floris van Doorn listed as authors. The file was claimed to have
  -- been ported from the Coq HoTT library. (The third lemma has later
  -- been generalised.)

  ext-sym :
    (f≡g : ∀ x → f x ≡ g x) →
    ⟨ext⟩ (sym ∘ f≡g) ≡ sym (⟨ext⟩ f≡g)
  ext-sym _ = refl

  ext-trans :
    (f≡g : ∀ x → f x ≡ g x) (g≡h : ∀ x → g x ≡ h x) →
    ⟨ext⟩ (λ x → trans (f≡g x) (g≡h x)) ≡
    trans (⟨ext⟩ f≡g) (⟨ext⟩ g≡h)
  ext-trans _ _ = refl

  cong-post-∘-ext :
    {B : A → Set b} {C : A → Set c} {f g : (x : A) → B x}
    {h : ∀ {x} → B x → C x}
    (f≡g : ∀ x → f x ≡ g x) →
    cong (h ∘_) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (cong h ∘ f≡g)
  cong-post-∘-ext _ = refl

  cong-pre-∘-ext :
    {B : Set b} {C : B → Set c} {f g : (x : B) → C x} {h : A → B}
    (f≡g : ∀ x → f x ≡ g x) →
    cong (_∘ h) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (f≡g ∘ h)
  cong-pre-∘-ext _ = refl

------------------------------------------------------------------------
-- The univalence axiom

-- The code in this section is based on code by Anders Mörtberg from
-- Agda's reference manual or the cubical library.

open Preimage equality-with-J using (_⁻¹_)
open Univalence-axiom equality-with-J hiding (≃⇒≡; ≃⇒≡-id)

private
  open module Eq = Equivalence equality-with-J using (_≃_)

private

  -- Simple conversion functions.

  ≃⇒≃ : {B : Set b} → A ≃ B → A Glue.≃ B
  ≃⇒≃ A≃B = _≃_.to A≃B
          , record { equiv-proof = _≃_.is-equivalence A≃B }

  ≃⇒≃⁻¹ : {B : Set b} → A Glue.≃ B → A ≃ B
  ≃⇒≃⁻¹ (f , f-equiv) = record
    { to             = f
    ; is-equivalence = equiv-proof f-equiv
    }

-- Equivalences can be converted to equalities (if the two types live
-- in the same universe).

≃⇒≡ : {A B : Set ℓ} → A ≃ B → A ≡ B
≃⇒≡ {A = A} {B} A≃B = λ i → primGlue B
  (λ { (i = 0̲) → A
     ; (i = 1̲) → B
  })
  (λ { (i = 0̲) → ≃⇒≃ A≃B
     ; (i = 1̲) → ≃⇒≃ Eq.id
  })

-- If ≃⇒≡ is applied to the identity equivalence, then the result is
-- equal to reflexivity.

≃⇒≡-id : ≃⇒≡ Eq.id ≡ refl {x = A}
≃⇒≡-id {A = A} = λ i j → primGlue A
  {φ = max i (max j (- j))}
  (λ _ → A)
  (λ _ → ≃⇒≃ Eq.id)

-- ≃⇒≡ is a left inverse of ≡⇒≃.

≃⇒≡∘≡⇒≃ : {A B : Set ℓ} (A≡B : A ≡ B) →
          ≃⇒≡ (≡⇒≃ A≡B) ≡ A≡B
≃⇒≡∘≡⇒≃ = elim
  (λ A≡B → ≃⇒≡ (≡⇒≃ A≡B) ≡ A≡B)
  (λ A →
     ≃⇒≡ (≡⇒≃ refl)  ≡⟨ cong ≃⇒≡ ≡⇒≃-refl ⟩
     ≃⇒≡ Eq.id       ≡⟨ ≃⇒≡-id ⟩∎
     refl            ∎)

-- ≃⇒≡ is a right inverse of ≡⇒≃.

≡⇒≃∘≃⇒≡ : {A B : Set ℓ} (A≃B : A ≃ B) →
          ≡⇒≃ (≃⇒≡ A≃B) ≡ A≃B
≡⇒≃∘≃⇒≡ {A = A} {B} A≃B = Eq.lift-equality ext (
  ≡⇒→ (≃⇒≡ A≃B)                                     ≡⟨⟩
  _≃_.to (transport (λ i → A ≃ ≃⇒≡ A≃B i) 0̲ Eq.id)  ≡⟨⟩
  transport (λ i → A → ≃⇒≡ A≃B i) 0̲ id              ≡⟨⟩
  transport (λ _ → A → B) 0̲ (_≃_.to A≃B)            ≡⟨ cong (_$ _≃_.to A≃B) $ transport-refl 0̲ ⟩∎
  _≃_.to A≃B                                        ∎)

-- Univalence.

univ : ∀ {ℓ} → Univalence ℓ
univ = _≃_.is-equivalence $ Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { from = ≃⇒≡
      }
    ; right-inverse-of = ≡⇒≃∘≃⇒≡
    }
  ; left-inverse-of = ≃⇒≡∘≡⇒≃
  })

private

  -- The type primGlue A B f is equivalent to A.

  primGlue≃ :
    (φ : I)
    (B : Partial φ (Set ℓ))
    (f : PartialP φ (λ x → B x Glue.≃ A)) →
    primGlue A B f ≃ A
  primGlue≃ {A = A} φ B f = record
    { to             = prim^unglue {φ = φ}
    ; is-equivalence = λ x →
          ( prim^glue (λ p → _≃_.from (f′ p) x) (hcomp (lemma₁ x) x)
          , (hcomp (lemma₁ x) x  ≡⟨ sym $ hfill (lemma₁ x) (inˢ x) ⟩∎
             x                   ∎)
          )
        , λ y i →
              prim^glue (λ { (φ = 1̲) → proj₁ (lemma₂ is-one y i) })
                        (hcomp (lemma₃ y i) x)
            , (hcomp (lemma₃ y i) x  ≡⟨ sym $ hfill (lemma₃ y i) (inˢ x) ⟩∎
               x                     ∎)
    }
    where
    f′ : PartialP φ (λ x → B x ≃ A)
    f′ p = ≃⇒≃⁻¹ (f p)

    lemma₁ : A → ∀ i → Partial φ A
    lemma₁ x i (φ = 1̲) = (
      x                                  ≡⟨ sym (_≃_.right-inverse-of (f′ is-one) x) ⟩∎
      _≃_.to (f′ _) (_≃_.from (f′ _) x)  ∎) i

    lemma₂ : ∀ {x} p (y : _≃_.to (f′ p) ⁻¹ x) →
             (_≃_.from (f′ p) x , _≃_.right-inverse-of (f′ p) x) ≡ y
    lemma₂ {x} p = _≃_.irrelevance (f′ p) x

    lemma₃ : ∀ {x} → prim^unglue {e = f} ⁻¹ x →
             ∀ i → I → Partial (max φ (max i (- i))) A
    lemma₃     y i j (φ = 1̲) = sym (proj₂ (lemma₂ is-one y i)) j
    lemma₃ {x} _ i j (i = 0̲) = hfill (lemma₁ x) (inˢ x) j
    lemma₃     y i j (i = 1̲) = sym (proj₂ y) j

-- An alternative formulation of univalence.

other-univ : Other-univalence ℓ
other-univ {ℓ = ℓ} {B = B} =
    (B , Eq.id)
  , λ { (A , A≃B) i →
          let C : ∀ i → Partial (max i (- i)) (Set ℓ)
              C = λ { i (i = 0̲) → B
                    ; i (i = 1̲) → A
                    }

              f : ∀ i → PartialP (max i (- i)) (λ j → C i j Glue.≃ B)
              f = λ { i (i = 0̲) → ≃⇒≃ Eq.id
                    ; i (i = 1̲) → ≃⇒≃ A≃B
                    }
          in
            primGlue  _ _ (f i)
          , primGlue≃ _ _ (f i)
      }

------------------------------------------------------------------------
-- Some properties

open Bijection equality-with-J using (_↔_)
open Function-universe equality-with-J hiding (id; _∘_)
open H-level equality-with-J

-- There is a dependent path from reflexivity for x to any dependent
-- path starting in x.

refl≡ :
  (x≡y : [ P ] x ≡ y) →
  [ (λ i → [ (λ j → P (min i j)) ] x ≡ x≡y i) ] refl {x = x} ≡ x≡y
refl≡ x≡y = λ i j → x≡y (min i j)

-- Transporting in one direction and then back amounts to doing
-- nothing.

transport∘transport :
  ∀ {p : I → Level} (P : ∀ i → Set (p i)) {p} →
  transport (λ i → P (- i)) 0̲ (transport P 0̲ p) ≡ p
transport∘transport P {p} = hsym λ i →
  comp (λ j → P (min i (- j)))
       (λ j → λ { (i = 0̲) → p
                ; (i = 1̲) → transport (λ k → P (- min j k)) (- j)
                              (transport P 0̲ p)
                })
       (transport (λ j → P (min i j)) (- i) p)

-- The following two lemmas are due to Anders Mörtberg.
--
-- Previously Andrea Vezzosi and I had each proved the second lemma in
-- much more convoluted ways (starting from a logical equivalence
-- proved by Anders; I had also gotten some useful hints from Andrea
-- for my proof).

-- Heterogeneous equality can be expressed in terms of homogeneous
-- equality.

heterogeneous≡homogeneous :
  {P : I → Set p} {p : P 0̲} {q : P 1̲} →
  ([ P ] p ≡ q) ≡ (transport P 0̲ p ≡ q)
heterogeneous≡homogeneous {P = P} {p = p} {q = q} = λ i →
  [ (λ j → P (max i j)) ] transport (λ j → P (min i j)) (- i) p ≡ q

-- A variant of the previous lemma.

heterogeneous↔homogeneous :
  (P : I → Set p) {p : P 0̲} {q : P 1̲} →
  ([ P ] p ≡ q) ↔ transport P 0̲ p ≡ q
heterogeneous↔homogeneous P =
  subst
    ([ P ] _ ≡ _ ↔_)
    heterogeneous≡homogeneous
    (Bijection.id equality-with-J)

-- The function dcong is pointwise definitionally equal to an
-- expression involving hcong.

dcong≡hcong :
  {x≡y : x ≡ y} (f : (x : A) → B x) →
  dcong f x≡y ≡
  _↔_.to (heterogeneous↔homogeneous (λ i → B (x≡y i))) (hcong f x≡y)
dcong≡hcong {B = B} {x≡y = x≡y} f = elim
  (λ x≡y →
     dcong f x≡y ≡
     _↔_.to (heterogeneous↔homogeneous (λ i → B (x≡y i))) (hcong f x≡y))

  (λ x →
     dcong f (refl {x = x})                                            ≡⟨⟩

     (λ i → transport (λ _ → B x) i (f x))                             ≡⟨ (λ i → comp
                                                                             (λ j → transport (λ _ → B x) (- j) (f x) ≡ f x)
                                                                             (λ { j (i = 0̲) → (λ k → transport (λ _ → B x) (max k (- j)) (f x))
                                                                                ; j (i = 1̲) → transport
                                                                                                (λ k → transport (λ _ → B x) (- min k j) (f x) ≡ f x)
                                                                                                0̲ refl
                                                                                })
                                                                             (transport (λ _ → f x ≡ f x) (- i) refl)) ⟩

     transport (λ i → transport (λ _ → B x) (- i) (f x) ≡ f x) 0̲ refl  ≡⟨ cong (transport (λ i → transport (λ _ → B x) (- i) (f x) ≡ f x) 0̲ ∘
                                                                                (_$ refl)) $ sym $
                                                                          transport-refl 0̲ ⟩
     transport (λ i → transport (λ _ → B x) (- i) (f x) ≡ f x) 0̲
       (transport (λ _ → f x ≡ f x) 0̲ refl)                            ≡⟨⟩

     _↔_.to (heterogeneous↔homogeneous (λ i → B (refl {x = x} i)))
       (hcong f (refl {x = x}))                                        ∎)

  x≡y

-- All instances of an interval-indexed family are equal.

index-irrelevant : (P : I → Set p) → P i ≡ P j
index-irrelevant {i = i} {j = j} P =
  λ k → P (max (min i (- k)) (min j k))

-- Positive h-levels of P i can be expressed in terms of the h-levels
-- of dependent paths over P.

H-level-suc↔H-level[]≡ :
  {P : I → Set p} →
  H-level (suc n) (P i) ↔ (∀ x y → H-level n ([ P ] x ≡ y))
H-level-suc↔H-level[]≡ {n = n} {i = i} {P = P} =
  H-level (suc n) (P i)                                            ↝⟨ H-level-cong ext _ (≡⇒≃ $ index-irrelevant P) ⟩

  H-level (suc n) (P 1̲)                                            ↝⟨ inverse $ ≡↔+ _ ext ⟩

  ((x y : P 1̲) → H-level n (x ≡ y))                                ↝⟨ (Π-cong ext (≡⇒≃ $ index-irrelevant P) λ x → ∀-cong ext λ _ →
                                                                       ≡⇒↝ _ $ cong (λ x → H-level _ (x ≡ _)) (
      x                                                                  ≡⟨ sym $ transport∘transport (λ i → P (- i)) ⟩

      transport P 0̲ (transport (λ i → P (- i)) 0̲ x)                      ≡⟨ cong (λ f → transport P 0̲ (transport (λ i → P (- i)) 0̲ (f x))) $ sym $
                                                                            transport-refl 0̲ ⟩∎
      transport P 0̲
        (transport (λ i → P (- i)) 0̲ (transport (λ _ → P 1̲) 0̲ x))        ∎)) ⟩

  ((x : P 0̲) (y : P 1̲) → H-level n (transport P 0̲ x ≡ y))          ↝⟨ (∀-cong ext λ x → ∀-cong ext λ y → H-level-cong ext n $ inverse $
                                                                       heterogeneous↔homogeneous P) ⟩□
  ((x : P 0̲) (y : P 1̲) → H-level n ([ P ] x ≡ y))                  □

private

  -- A simple lemma used below.

  H-level-suc→H-level[]≡ :
    ∀ n → H-level (1 + n) (P 0̲) → H-level n ([ P ] x ≡ y)
  H-level-suc→H-level[]≡ {P = P} {x = x} {y = y} n =
    H-level (1 + n) (P 0̲)              ↔⟨ H-level-suc↔H-level[]≡ ⟩
    (∀ x y → H-level n ([ P ] x ≡ y))  ↝⟨ (λ f → f _ _) ⟩□
    H-level n ([ P ] x ≡ y)            □

-- A form of proof irrelevance for paths that are propositional at one
-- end-point.

heterogeneous-irrelevance₀ :
  Is-proposition (P 0̲) → [ P ] x ≡ y
heterogeneous-irrelevance₀ {P = P} {x = x} {y = y} =
  Is-proposition (P 0̲)        ↝⟨ H-level-suc→H-level[]≡ _ ⟩
  Contractible ([ P ] x ≡ y)  ↝⟨ proj₁ ⟩□
  [ P ] x ≡ y                 □

-- A form of UIP for squares that are sets on one corner.

heterogeneous-UIP₀₀ :
  {P : I → I → Set p}
  {x : ∀ i → P i 0̲} {y : ∀ i → P i 1̲}
  {p : [ (λ j → P 0̲ j) ] x 0̲ ≡ y 0̲}
  {q : [ (λ j → P 1̲ j) ] x 1̲ ≡ y 1̲} →
  Is-set (P 0̲ 0̲) →
  [ (λ i → [ (λ j → P i j) ] x i ≡ y i) ] p ≡ q
heterogeneous-UIP₀₀ {P = P} {x = x} {y = y} {p = p} {q = q} =
  Is-set (P 0̲ 0̲)                                                ↝⟨ H-level-suc→H-level[]≡ 1 ⟩
  Is-proposition ([ (λ j → P 0̲ j) ] x 0̲ ≡ y 0̲)                  ↝⟨ H-level-suc→H-level[]≡ _ ⟩
  Contractible ([ (λ i → [ (λ j → P i j) ] x i ≡ y i) ] p ≡ q)  ↝⟨ proj₁ ⟩□
  [ (λ i → [ (λ j → P i j) ] x i ≡ y i) ] p ≡ q                 □

-- The following two lemmas can be used to implement the truncation
-- cases of (at least some) eliminators for (at least some) HITs. For
-- some examples, see H-level.Truncation.Propositional and
-- Quotient.HIT.

-- A variant of heterogeneous-irrelevance₀.

heterogeneous-irrelevance :
  {P : A → Set p} →
  (∀ x → Is-proposition (P x)) →
  {x≡y : x ≡ y} {p₁ : P x} {p₂ : P y} →
  [ (λ i → P (x≡y i)) ] p₁ ≡ p₂
heterogeneous-irrelevance {x = x} {P = P} P-prop {x≡y} {p₁} {p₂} =
                                 $⟨ P-prop ⟩
  (∀ x → Is-proposition (P x))   ↝⟨ _$ _ ⟩
  Is-proposition (P x)           ↝⟨ heterogeneous-irrelevance₀ ⟩□
  [ (λ i → P (x≡y i)) ] p₁ ≡ p₂  □

-- A variant of heterogeneous-UIP₀₀.
--
-- The cubical library contains (or used to contain) a lemma with
-- basically the same type, but with a seemingly rather different
-- proof, implemented by Zesen Qian.

heterogeneous-UIP :
  {P : A → Set p} →
  (∀ x → Is-set (P x)) →
  {eq₁ eq₂ : x ≡ y} (eq₃ : eq₁ ≡ eq₂) {p₁ : P x} {p₂ : P y}
  (eq₄ : [ (λ j → P (eq₁ j)) ] p₁ ≡ p₂)
  (eq₅ : [ (λ j → P (eq₂ j)) ] p₁ ≡ p₂) →
  [ (λ i → [ (λ j → P (eq₃ i j)) ] p₁ ≡ p₂) ] eq₄ ≡ eq₅
heterogeneous-UIP {x = x} {P = P} P-set eq₃ {p₁} {p₂} eq₄ eq₅ =
                                                         $⟨ P-set ⟩
  (∀ x → Is-set (P x))                                   ↝⟨ _$ _ ⟩
  Is-set (P x)                                           ↝⟨ heterogeneous-UIP₀₀ ⟩□
  [ (λ i → [ (λ j → P (eq₃ i j)) ] p₁ ≡ p₂) ] eq₄ ≡ eq₅  □
