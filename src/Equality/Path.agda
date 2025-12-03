------------------------------------------------------------------------
-- Paths and extensionality
------------------------------------------------------------------------

{-# OPTIONS --cubical=no-glue --safe #-}

module Equality.Path where

import Bijection
open import Equality hiding (module Derived-definitions-and-properties)
open import Equality.Instances-related
import Equivalence
import Equivalence.Contractible-preimages
import Equivalence.Half-adjoint
import Extensionality
import Function-universe
import H-level
import H-level.Closure
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
  renaming (Sub to _[_↦_]; inS to inˢ; primSubOut to outˢ)

------------------------------------------------------------------------
-- Some local generalisable variables

private
  variable
    a b c p q ℓ : Level
    A           : Type a
    B           : A → Type b
    P           : I → Type p
    u v w x y z : A
    f g h       : (x : A) → B x
    i j         : I
    n           : ℕ

------------------------------------------------------------------------
-- Equality

-- Homogeneous and heterogeneous equality.

open import Agda.Builtin.Cubical.Path public
  using (_≡_)
  renaming (PathP to infix 4 [_]_≡_)

------------------------------------------------------------------------
-- Filling

-- The code in this section is based on code in the cubical library
-- written by Anders Mörtberg.

-- Filling for homogenous composition.

hfill :
  {φ : I} (u : I → Partial φ A) (u₀ : A [ φ ↦ u 0̲ ]) →
  outˢ u₀ ≡ hcomp u (outˢ u₀)
hfill {φ} u u₀ = λ i →
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
  (P : ∀ i → Type (p i)) {φ : I}
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
  (A : Type ℓ)
  (φ : I)
  (P : (i : I) → Type ℓ [ φ ↦ (λ _ → A) ])
  (u₀ : outˢ (P 0̲)) →
  [ (λ i → outˢ (P i)) ]
    u₀ ≡ transport (λ i → outˢ (P i)) φ u₀
transport-fill _ φ P u₀ i =
  transport (λ j → outˢ (P (min i j))) (max (- i) φ) u₀

------------------------------------------------------------------------
-- Path equality satisfies the axioms of Equality-with-J

-- Reflexivity.

refl : {@0 A : Type a} {x : A} → x ≡ x
refl {x} = λ _ → x

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
htransʳ {x} x≡y y≡z = λ i →
  hcomp (λ { _ (i = 0̲) → x
           ; j (i = 1̲) → y≡z j
           })
        (x≡y i)

htransˡ : x ≡ y → [ P ] y ≡ z → [ P ] x ≡ z
htransˡ x≡y y≡z = hsym (htransʳ (hsym y≡z) (hsym x≡y))

htransʳ-reflʳ : (x≡y : [ P ] x ≡ y) → htransʳ x≡y refl ≡ x≡y
htransʳ-reflʳ {x} {y} x≡y = λ i j →
  hfill (λ { _ (j = 0̲) → x
           ; _ (j = 1̲) → y
           })
        (inˢ (x≡y j))
        (- i)

htransˡ-reflˡ : (x≡y : [ P ] x ≡ y) → htransˡ refl x≡y ≡ x≡y
htransˡ-reflˡ = htransʳ-reflʳ

htrans :
  {x≡y : x ≡ y} {y≡z : y ≡ z}
  (P : A → Type p) {p : P x} {q : P y} {r : P z} →
  [ (λ i → P (x≡y i)) ] p ≡ q →
  [ (λ i → P (y≡z i)) ] q ≡ r →
  [ (λ i → P (htransˡ x≡y y≡z i)) ] p ≡ r
htrans {z} {x≡y} {y≡z} P {r} p≡q q≡r = λ i →
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
  (P : A → Type p) (p : P x) {q : P y} {r : P z} →
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
  ∀ {@0 a} {@0 A : Type a} {x y : A}
  (P : {x y : A} → x ≡ y → Type p) →
  (∀ x → P (refl {x = x})) →
  (x≡y : x ≡ y) → P x≡y
elim {x} P p x≡y =
  transport (λ i → P (λ j → x≡y (min i j))) 0̲ (p x)

-- A variant of elim.

elim₀ :
  ∀ {@0 a} {@0 A : Type a} {@0 x y : A}
  (P : {@0 x y : A} → @0 x ≡ y → Type p) →
  (∀ (@0 x) → P (refl {x = x})) →
  (@0 x≡y : x ≡ y) → P x≡y
elim₀ {x} P p x≡y =
  transport (λ i → P (λ j → x≡y (min i j))) 0̲ (p x)

-- Substitutivity.

hsubst :
  ∀ (Q : ∀ {i} → P i → Type q) →
  [ P ] x ≡ y → Q x → Q y
hsubst Q x≡y p = transport (λ i → Q (x≡y i)) 0̲ p

subst : (P : A → Type p) → x ≡ y → P x → P y
subst P = hsubst P

-- Congruence.
--
-- The heterogeneous variant is based on code in the cubical library
-- written by Anders Mörtberg.

hcong :
  (f : (x : A) → B x) (x≡y : x ≡ y) →
  [ (λ i → B (x≡y i)) ] f x ≡ f y
hcong f x≡y = λ i → f (x≡y i)

cong : {B : Type b} (f : A → B) → x ≡ y → f x ≡ f y
cong f = hcong f

dcong :
  (f : (x : A) → B x) (x≡y : x ≡ y) →
  subst B x≡y (f x) ≡ f y
dcong {B} f x≡y = λ i →
  transport (λ j → B (x≡y (max i j))) i (f (x≡y i))

-- Transporting along reflexivity amounts to doing nothing.
--
-- This definition is based on code in Agda's reference manual written
-- by Anders Mörtberg.

transport-refl : ∀ i → transport (λ i → refl {x = A} i) i ≡ id
transport-refl {A} i = λ j → transport (λ _ → A) (max i j)

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
         Type (lsuc (a ⊔ b)) where

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

  ≡↔≡ : {A : Type a} {x y : A} → x E.≡ y ↔ x ≡ y
  ≡↔≡ {a} = record
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
private
  open module Ext = Extensionality equality-with-J
    using (Extensionality; Function-extensionality)

-- Extensionality.

⟨ext⟩ : Function-extensionality a p
⟨ext⟩ f≡g = λ i x → f≡g x i

ext : Extensionality a p
ext = _⇔_.from Ext.Extensionality⇔Function-extensionality ⟨ext⟩

-- The function ⟨ext⟩ is an equivalence.

ext-is-equivalence : Is-equivalence {A = ∀ x → f x ≡ g x} ⟨ext⟩
ext-is-equivalence =
    Ext.ext⁻¹
  , (λ _ → refl)
  , (λ _ → refl)
  , (λ _ → refl)

private

  -- Equality rearrangement lemmas for ⟨ext⟩. All of these lemmas hold
  -- definitionally.

  ext-refl : ⟨ext⟩ (λ x → refl {x = f x}) ≡ refl
  ext-refl = refl

  ext-const :
    (x≡y : x ≡ y) →
    ⟨ext⟩ (const {B = A} x≡y) ≡ cong const x≡y
  ext-const _ = refl

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
    (P : B x → B x → Type p)
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
    {B : A → Type b} {C : A → Type c} {f g : (x : A) → B x}
    {h : ∀ {x} → B x → C x}
    (f≡g : ∀ x → f x ≡ g x) →
    cong (h ∘_) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (cong h ∘ f≡g)
  cong-post-∘-ext _ = refl

  cong-pre-∘-ext :
    {B : Type b} {C : B → Type c} {f g : (x : B) → C x} {h : A → B}
    (f≡g : ∀ x → f x ≡ g x) →
    cong (_∘ h) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (f≡g ∘ h)
  cong-pre-∘-ext _ = refl

------------------------------------------------------------------------
-- Some properties

open Bijection equality-with-J using (_↔_)
open Function-universe equality-with-J hiding (id; _∘_)
open H-level equality-with-J
open Univalence-axiom equality-with-J

-- There is a dependent path from reflexivity for x to any dependent
-- path starting in x.

refl≡ :
  (x≡y : [ P ] x ≡ y) →
  [ (λ i → [ (λ j → P (min i j)) ] x ≡ x≡y i) ] refl {x = x} ≡ x≡y
refl≡ x≡y = λ i j → x≡y (min i j)

-- Transporting in one direction and then back amounts to doing
-- nothing.

transport∘transport :
  ∀ {p : I → Level} (P : ∀ i → Type (p i)) {p} →
  transport (λ i → P (- i)) 0̲ (transport P 0̲ p) ≡ p
transport∘transport P {p} = hsym λ i →
  comp (λ j → P (min i (- j)))
       (λ j → λ { (i = 0̲) → p
                ; (i = 1̲) → transport (λ k → P (- min j k)) (- j)
                              (transport P 0̲ p)
                })
       (transport (λ j → P (min i j)) (- i) p)

-- One form of transporting can be expressed using trans and sym.

transport-≡ :
  {p : x ≡ y} {q : u ≡ v} (r : x ≡ u) →
  transport (λ i → p i ≡ q i) 0̲ r ≡
  trans (sym p) (trans r q)
transport-≡ {x} {p} {q} r = elim¹
  (λ p → transport (λ i → p i ≡ q i) 0̲ r ≡
         trans (sym p) (trans r q))
  (transport (λ i → x ≡ q i) 0̲ r  ≡⟨⟩
   subst (x ≡_) q r               ≡⟨ sym trans-subst ⟩
   trans r q                      ≡⟨ sym $ trans-reflˡ _ ⟩
   trans refl (trans r q)         ≡⟨⟩
   trans (sym refl) (trans r q)   ∎)
  p

-- The function htrans {x≡y = x≡y} {y≡z = y≡z} (const A) is pointwise
-- equal to trans.
--
-- Andrea Vezzosi helped me with this proof.

htrans-const :
  (x≡y : x ≡ y) (y≡z : y ≡ z) (p : u ≡ v) {q : v ≡ w} →
  htrans {x≡y = x≡y} {y≡z = y≡z} (const A) p q ≡ trans p q
htrans-const {A} {w} _ _ p {q} =
  (λ i → comp (λ _ → A) (s i) (q i))                  ≡⟨⟩

  (λ i →
     hcomp (λ j x → transport (λ _ → A) j (s i j x))
       (transport (λ _ → A) 0̲ (q i)))                 ≡⟨ (λ k i → hcomp (λ j x → cong (_$ s i j x) (transport-refl j) k)
                                                                    (cong (_$ q i) (transport-refl 0̲) k)) ⟩∎
  (λ i → hcomp (s i) (q i))                           ∎
  where
  s : ∀ i j → Partial (max i (- i)) A
  s i = λ where
    j (i = 0̲) → p (- j)
    _ (i = 1̲) → w

-- The following two lemmas are due to Anders Mörtberg.
--
-- Previously Andrea Vezzosi and I had each proved the second lemma in
-- much more convoluted ways (starting from a logical equivalence
-- proved by Anders; I had also gotten some useful hints from Andrea
-- for my proof).

-- Heterogeneous equality can be expressed in terms of homogeneous
-- equality.

heterogeneous≡homogeneous :
  {P : I → Type p} {p : P 0̲} {q : P 1̲} →
  ([ P ] p ≡ q) ≡ (transport P 0̲ p ≡ q)
heterogeneous≡homogeneous {P} {p} {q} = λ i →
  [ (λ j → P (max i j)) ] transport (λ j → P (min i j)) (- i) p ≡ q

-- A variant of the previous lemma.

heterogeneous↔homogeneous :
  (P : I → Type p) {p : P 0̲} {q : P 1̲} →
  ([ P ] p ≡ q) ↔ transport P 0̲ p ≡ q
heterogeneous↔homogeneous P =
  subst
    ([ P ] _ ≡ _ ↔_)
    heterogeneous≡homogeneous
    (Bijection.id equality-with-J)

-- The function dcong is pointwise equal to an expression involving
-- hcong.

dcong≡hcong :
  {B : A → Type b} {x≡y : x ≡ y} (f : (x : A) → B x) →
  dcong f x≡y ≡
  _↔_.to (heterogeneous↔homogeneous (λ i → B (x≡y i))) (hcong f x≡y)
dcong≡hcong {B} {x≡y} f = elim
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

-- A "computation" rule.

from-heterogeneous↔homogeneous-const-refl :
  (B : A → Type b) {x : A} {y : B x} →
  _↔_.from (heterogeneous↔homogeneous λ _ → B x) refl ≡
  sym (subst-refl B y)
from-heterogeneous↔homogeneous-const-refl B {x} {y} =
  transport (λ _ → y ≡ transport (λ _ → B x) 0̲ y) 0̲
    (transport
       (λ i → transport (λ _ → B x) i y ≡ transport (λ _ → B x) 0̲ y) 0̲
       (λ _ → transport (λ _ → B x) 0̲ y))                               ≡⟨ cong (_$ transport
                                                                                      (λ i → transport (λ _ → B x) i y ≡
                                                                                             transport (λ _ → B x) 0̲ y) 0̲
                                                                                      (λ _ → transport (λ _ → B x) 0̲ y)) $
                                                                           transport-refl 0̲ ⟩
  transport
    (λ i → transport (λ _ → B x) i y ≡ transport (λ _ → B x) 0̲ y) 0̲
    (λ _ → transport (λ _ → B x) 0̲ y)                                   ≡⟨ transport-≡ (λ _ → transport (λ _ → B x) 0̲ y) ⟩

  trans (λ i → transport (λ _ → B x) (- i) y)
    (trans (λ _ → transport (λ _ → B x) 0̲ y)
       (λ _ → transport (λ _ → B x) 0̲ y))                               ≡⟨ cong (trans (λ i → transport (λ _ → B x) (- i) y)) $
                                                                           trans-symʳ (λ _ → transport (λ _ → B x) 0̲ y) ⟩

  trans (λ i → transport (λ _ → B x) (- i) y) refl                      ≡⟨ trans-reflʳ _ ⟩∎

  (λ i → transport (λ _ → B x) (- i) y)                                 ∎

-- A direct proof of something with the same type as Σ-≡,≡→≡.

Σ-≡,≡→≡′ :
  {p₁ p₂ : Σ A B} →
  (p : proj₁ p₁ ≡ proj₁ p₂) →
  subst B p (proj₂ p₁) ≡ proj₂ p₂ →
  p₁ ≡ p₂
Σ-≡,≡→≡′ {B} {p₁ = _ , y₁} {p₂ = _ , y₂} p q i =
  p i , lemma i
  where
  lemma : [ (λ i → B (p i)) ] y₁ ≡ y₂
  lemma = _↔_.from (heterogeneous↔homogeneous _) q

-- Σ-≡,≡→≡ is pointwise equal to Σ-≡,≡→≡′.

Σ-≡,≡→≡≡Σ-≡,≡→≡′ :
  {B : A → Type b}
  {p₁ p₂ : Σ A B}
  {p : proj₁ p₁ ≡ proj₁ p₂}
  {q : subst B p (proj₂ p₁) ≡ proj₂ p₂} →
  Σ-≡,≡→≡ {B = B} p q ≡ Σ-≡,≡→≡′ p q
Σ-≡,≡→≡≡Σ-≡,≡→≡′ {B} {p₁} {p₂} {p} {q} =
  elim₁
    (λ p →
       ∀ {p₁₂} (q : subst B p p₁₂ ≡ proj₂ p₂) →
       Σ-≡,≡→≡ p q ≡ Σ-≡,≡→≡′ p q)
    (λ q →
       Σ-≡,≡→≡ refl q                                          ≡⟨ Σ-≡,≡→≡-reflˡ q ⟩
       cong (_ ,_) (trans (sym $ subst-refl B _) q)            ≡⟨ cong (cong (_ ,_)) $
                                                                  elim¹
                                                                    (λ q →
                                                                       trans (sym $ subst-refl B _) q ≡
                                                                       _↔_.from (heterogeneous↔homogeneous _) q)
                                                                    (
           trans (sym $ subst-refl B _) refl                         ≡⟨ trans-reflʳ _ ⟩
           sym (subst-refl B _)                                      ≡⟨ sym $ from-heterogeneous↔homogeneous-const-refl B ⟩∎
           _↔_.from (heterogeneous↔homogeneous _) refl               ∎)
                                                                    q ⟩
       cong (_ ,_) (_↔_.from (heterogeneous↔homogeneous _) q)  ≡⟨⟩
       Σ-≡,≡→≡′ refl q                                         ∎)
    p q

-- All instances of an interval-indexed family are equal.

index-irrelevant : (P : I → Type p) → P i ≡ P j
index-irrelevant {i} {j} P =
  λ k → P (max (min i (- k)) (min j k))

-- Positive h-levels of P i can be expressed in terms of the h-levels
-- of dependent paths over P.

H-level-suc↔H-level[]≡ :
  {P : I → Type p} →
  H-level (suc n) (P i) ↔ (∀ x y → H-level n ([ P ] x ≡ y))
H-level-suc↔H-level[]≡ {n} {i} {P} =
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
  H-level-suc→H-level[]≡ {P} {x} {y} n =
    H-level (1 + n) (P 0̲)              ↔⟨ H-level-suc↔H-level[]≡ ⟩
    (∀ x y → H-level n ([ P ] x ≡ y))  ↝⟨ (λ f → f _ _) ⟩□
    H-level n ([ P ] x ≡ y)            □

-- A form of proof irrelevance for paths that are propositional at one
-- end-point.

heterogeneous-irrelevance₀ :
  Is-proposition (P 0̲) → [ P ] x ≡ y
heterogeneous-irrelevance₀ {P} {x} {y} =
  Is-proposition (P 0̲)        ↝⟨ H-level-suc→H-level[]≡ _ ⟩
  Contractible ([ P ] x ≡ y)  ↝⟨ proj₁ ⟩□
  [ P ] x ≡ y                 □

-- A form of UIP for squares that are sets on one corner.

heterogeneous-UIP₀₀ :
  {P : I → I → Type p}
  {x : ∀ i → P i 0̲} {y : ∀ i → P i 1̲}
  {p : [ (λ j → P 0̲ j) ] x 0̲ ≡ y 0̲}
  {q : [ (λ j → P 1̲ j) ] x 1̲ ≡ y 1̲} →
  Is-set (P 0̲ 0̲) →
  [ (λ i → [ (λ j → P i j) ] x i ≡ y i) ] p ≡ q
heterogeneous-UIP₀₀ {P} {x} {y} {p} {q} =
  Is-set (P 0̲ 0̲)                                                ↝⟨ H-level-suc→H-level[]≡ 1 ⟩
  Is-proposition ([ (λ j → P 0̲ j) ] x 0̲ ≡ y 0̲)                  ↝⟨ H-level-suc→H-level[]≡ _ ⟩
  Contractible ([ (λ i → [ (λ j → P i j) ] x i ≡ y i) ] p ≡ q)  ↝⟨ proj₁ ⟩□
  [ (λ i → [ (λ j → P i j) ] x i ≡ y i) ] p ≡ q                 □

-- A variant of heterogeneous-UIP₀₀, "one level up".

heterogeneous-UIP₃₀₀ :
  {P : I → I → I → Type p}
  {x : ∀ i j → P i j 0̲} {y : ∀ i j → P i j 1̲}
  {p : ∀ i → [ (λ k → P i 0̲ k) ] x i 0̲ ≡ y i 0̲}
  {q : ∀ i → [ (λ k → P i 1̲ k) ] x i 1̲ ≡ y i 1̲}
  {r : [ (λ j → [ (λ k → P 0̲ j k) ] x 0̲ j ≡ y 0̲ j) ] p 0̲ ≡ q 0̲}
  {s : [ (λ j → [ (λ k → P 1̲ j k) ] x 1̲ j ≡ y 1̲ j) ] p 1̲ ≡ q 1̲} →
  H-level 3 (P 0̲ 0̲ 0̲) →
  [ (λ i → [ (λ j → [ (λ k → P i j k) ] x i j ≡ y i j) ] p i ≡ q i) ]
    r ≡ s
heterogeneous-UIP₃₀₀ {P} {x} {y} {p} {q} {r} {s} =
  H-level 3 (P 0̲ 0̲ 0̲)                                                     ↝⟨ H-level-suc→H-level[]≡ 2 ⟩

  Is-set ([ (λ k → P 0̲ 0̲ k) ] x 0̲ 0̲ ≡ y 0̲ 0̲)                              ↝⟨ H-level-suc→H-level[]≡ 1 ⟩

  Is-proposition
    ([ (λ j → [ (λ k → P 0̲ j k) ] x 0̲ j ≡ y 0̲ j) ] p 0̲ ≡ q 0̲)             ↝⟨ H-level-suc→H-level[]≡ _ ⟩

  Contractible
    ([ (λ i → [ (λ j → [ (λ k → P i j k) ] x i j ≡ y i j) ] p i ≡ q i) ]
       r ≡ s)                                                             ↝⟨ proj₁ ⟩□

  [ (λ i → [ (λ j → [ (λ k → P i j k) ] x i j ≡ y i j) ] p i ≡ q i) ]
    r ≡ s                                                                 □

-- The following three lemmas can be used to implement the truncation
-- cases of (at least some) eliminators for (at least some) HITs. For
-- some examples, see H-level.Truncation.Propositional, Quotient and
-- Eilenberg-MacLane-space.

-- A variant of heterogeneous-irrelevance₀.

heterogeneous-irrelevance :
  {P : A → Type p} →
  (∀ x → Is-proposition (P x)) →
  {x≡y : x ≡ y} {p₁ : P x} {p₂ : P y} →
  [ (λ i → P (x≡y i)) ] p₁ ≡ p₂
heterogeneous-irrelevance {x} {P} P-prop {x≡y} {p₁} {p₂} =
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
  {P : A → Type p} →
  (∀ x → Is-set (P x)) →
  {eq₁ eq₂ : x ≡ y} (eq₃ : eq₁ ≡ eq₂) {p₁ : P x} {p₂ : P y}
  (eq₄ : [ (λ j → P (eq₁ j)) ] p₁ ≡ p₂)
  (eq₅ : [ (λ j → P (eq₂ j)) ] p₁ ≡ p₂) →
  [ (λ i → [ (λ j → P (eq₃ i j)) ] p₁ ≡ p₂) ] eq₄ ≡ eq₅
heterogeneous-UIP {x} {P} P-set eq₃ {p₁} {p₂} eq₄ eq₅ =  $⟨ P-set ⟩
  (∀ x → Is-set (P x))                                   ↝⟨ _$ _ ⟩
  Is-set (P x)                                           ↝⟨ heterogeneous-UIP₀₀ ⟩□
  [ (λ i → [ (λ j → P (eq₃ i j)) ] p₁ ≡ p₂) ] eq₄ ≡ eq₅  □

-- A variant of heterogeneous-UIP, "one level up".

heterogeneous-UIP₃ :
  {P : A → Type p} →
  (∀ x → H-level 3 (P x)) →
  {eq₁ eq₂ : x ≡ y} {eq₃ eq₄ : eq₁ ≡ eq₂}
  (eq₅ : eq₃ ≡ eq₄)
  {p₁ : P x} {p₂ : P y}
  {eq₆ : [ (λ k → P (eq₁ k)) ] p₁ ≡ p₂}
  {eq₇ : [ (λ k → P (eq₂ k)) ] p₁ ≡ p₂}
  (eq₈ : [ (λ j → [ (λ k → P (eq₃ j k)) ] p₁ ≡ p₂) ] eq₆ ≡ eq₇)
  (eq₉ : [ (λ j → [ (λ k → P (eq₄ j k)) ] p₁ ≡ p₂) ] eq₆ ≡ eq₇) →
  [ (λ i → [ (λ j → [ (λ k → P (eq₅ i j k)) ] p₁ ≡ p₂) ] eq₆ ≡ eq₇) ]
    eq₈ ≡ eq₉
heterogeneous-UIP₃
  {x} {P} P-groupoid eq₅ {p₁} {p₂} {eq₆} {eq₇} eq₈ eq₉ =
                                                                       $⟨ P-groupoid ⟩
  (∀ x → H-level 3 (P x))                                              ↝⟨ _$ _ ⟩
  H-level 3 (P x)                                                      ↝⟨ heterogeneous-UIP₃₀₀ ⟩□
  [ (λ i → [ (λ j → [ (λ k → P (eq₅ i j k)) ] p₁ ≡ p₂) ] eq₆ ≡ eq₇) ]
    eq₈ ≡ eq₉                                                          □
