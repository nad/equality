------------------------------------------------------------------------
-- Paths, extensionality and univalence
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Equality.Path where

open import Agda.Builtin.Cubical.Glue as Glue hiding (_≃_)

open import Equality
import Equivalence
open import Logical-equivalence using (_⇔_)
import Preimage
open import Prelude
import Univalence-axiom

private
  variable
    a b c p q ℓ : Level
    A           : Set a
    B           : A → Set b
    P           : A → Set p
    x y z       : A
    f g h       : (x : A) → B x

------------------------------------------------------------------------
-- The interval

open import Agda.Primitive.Cubical public
  using (I; Partial; PartialP)
  renaming (i0 to 0̲; i1 to 1̲;
            IsOne to Is-one; itIsOne to 1̲-is-one;
            primINeg to -̲_; primIMin to _⊓̲_; primIMax to _⊔̲_;
            primHComp to hcomp; primTransp to transport)

open import Agda.Builtin.Cubical.Sub public
  renaming (Sub to _[_↦_]; inc to as-sub; primSubOut to forget-sub)

------------------------------------------------------------------------
-- Equality

-- Homogeneous equality.

open import Agda.Builtin.Cubical.Path public using (_≡_)

-- Heterogeneous equality.

infix 4 [_]_≡_

[_]_≡_ : (P : I → Set p) → P 0̲ → P 1̲ → Set p
[_]_≡_ = Agda.Builtin.Cubical.Path.PathP

------------------------------------------------------------------------
-- Some derived operations

-- The code in this section is based on code in the cubical library
-- written by Anders Mörtberg.

-- Heterogeneous composition.

comp :
  {p : I → Level}
  (P : ∀ i → Set (p i))
  {φ : I}
  (u : ∀ i → Partial φ (P i)) →
  P 0̲ [ φ ↦ u 0̲ ] → P 1̲
comp P {φ = φ} u u₀ =
  hcomp (λ i → λ { (φ = 1̲) →
           transport (λ j → P (i ⊔̲ j)) i (u i 1̲-is-one) })
        (transport P 0̲ (forget-sub u₀))

-- Filling for homogenous composition.

hfill :
  {φ : I} (u : I → Partial φ A) (u₀ : A [ φ ↦ u 0̲ ]) →
  forget-sub u₀ ≡ hcomp u (forget-sub u₀)
hfill {φ = φ} u u₀ = λ i →
  hcomp (λ j → λ { (φ = 1̲) → u (i ⊓̲ j) 1̲-is-one
                 ; (i = 0̲) → forget-sub u₀
                 })
        (forget-sub u₀)

-- Filling for heterogeneous composition.
--
-- Note that if p had been a constant level, then the final line of
-- the type signature could have been replaced by
-- [ P ] forget-sub u₀ ≡ comp P u u₀.

fill :
  {p : I → Level}
  (P : ∀ i → Set (p i)) {φ : I}
  (u : ∀ i → Partial φ (P i))
  (u₀ : P 0̲ [ φ ↦ u 0̲ ]) →
  ∀ i → P i
fill P {φ} u u₀ i =
  comp (λ j → P (i ⊓̲ j))
       (λ j → λ { (φ = 1̲) → u (i ⊓̲ j) 1̲-is-one
                ; (i = 0̲) → forget-sub u₀
                })
       (as-sub (forget-sub u₀))

-- Filling for transport.

transport-fill :
  (φ : I)
  (P : (i : I) → Set p [ φ ↦ (λ _ → A) ])
  (u₀ : forget-sub (P 0̲)) →
  [ (λ i → forget-sub (P i)) ]
    u₀ ≡ transport (λ i → forget-sub (P i)) φ u₀
transport-fill φ P u₀ i =
  transport (λ j → forget-sub (P (i ⊓̲ j))) (-̲ i ⊔̲ φ) u₀

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

hsym : ∀ {P : I → Set p} {x y} →
       [ P ] x ≡ y → [ (λ i → P (-̲ i)) ] y ≡ x
hsym x≡y = λ i → x≡y (-̲ i)

-- Transitivity.
--
-- The proof htransʳ-reflʳ is based on code in Agda's reference manual
-- written by Anders Mörtberg.

htransʳ :
  ∀ {P : I → Set p} {x y z} →
  [ P ] x ≡ y → y ≡ z → [ P ] x ≡ z
htransʳ {x = x} x≡y y≡z = λ i →
  hcomp (λ { _ (i = 0̲) → x
           ; j (i = 1̲) → y≡z j
           })
        (x≡y i)

htransˡ :
  ∀ {P : I → Set p} {x y z} →
  x ≡ y → [ P ] y ≡ z → [ P ] x ≡ z
htransˡ x≡y y≡z = hsym (htransʳ (hsym y≡z) (hsym x≡y))

htransʳ-reflʳ :
  ∀ {P : I → Set p} {x y}
  (x≡y : [ P ] x ≡ y) → htransʳ x≡y refl ≡ x≡y
htransʳ-reflʳ {x = x} {y = y} x≡y = λ i j →
  hfill (λ { _ (j = 0̲) → x
           ; _ (j = 1̲) → y
           })
        (as-sub (x≡y j))
        (-̲ i)

htransˡ-reflˡ :
  ∀ {P : I → Set p} {x y}
  (x≡y : [ P ] x ≡ y) → htransˡ refl x≡y ≡ x≡y
htransˡ-reflˡ = htransʳ-reflʳ

-- Some equational reasoning combinators.

infix  -1 finally
infixr -2 step-≡ step-≡h _≡⟨⟩_

step-≡ : ∀ {P : I → Set p} x {y z} → [ P ] y ≡ z → x ≡ y → [ P ] x ≡ z
step-≡ _ = flip htransˡ

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

step-≡h : ∀ {P : I → Set p} x {y z} → y ≡ z → [ P ] x ≡ y → [ P ] x ≡ z
step-≡h _ = flip htransʳ

syntax step-≡h x y≡z x≡y = x ≡⟨ x≡y ⟩h y≡z

_≡⟨⟩_ : ∀ {P : I → Set p} x {y} → [ P ] x ≡ y → [ P ] x ≡ y
_ ≡⟨⟩ x≡y = x≡y

finally : ∀ {P : I → Set p} x y → [ P ] x ≡ y → [ P ] x ≡ y
finally _ _ x≡y = x≡y

syntax finally x y x≡y = x ≡⟨ x≡y ⟩∎ y ∎

-- The J rule.

elim :
  (P : {x y : A} → x ≡ y → Set p) →
  (∀ x → P (refl {x = x})) →
  ∀ {x y} (x≡y : x ≡ y) → P x≡y
elim P p {x} x≡y =
  transport (λ i → P (λ j → x≡y (i ⊓̲ j))) 0̲ (p x)

-- Substitutivity.

hsubst :
  ∀ {P : I → Set p} (Q : ∀ {i} → P i → Set q) {x y} →
  [ P ] x ≡ y → Q x → Q y
hsubst Q x≡y p = transport (λ i → Q (x≡y i)) 0̲ p

subst : ∀ (P : A → Set p) {x y} → x ≡ y → P x → P y
subst P = hsubst P

-- Congruence.
--
-- The heterogeneous variant is based on code in the cubical library
-- written by Anders Mörtberg.

hcong :
  ∀ {B : A → Set b} (f : (x : A) → B x) {x y} →
  (x≡y : x ≡ y) → [ (λ i → B (x≡y i)) ] f x ≡ f y
hcong f x≡y = λ i → f (x≡y i)

cong : ∀ {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f = hcong f

dependent-cong :
  ∀ (f : (x : A) → B x) {x y} (x≡y : x ≡ y) →
  subst B x≡y (f x) ≡ f y
dependent-cong {B = B} f {x} {y} x≡y = λ i →
  transport (λ j → B (x≡y (i ⊔̲ j))) i (f (x≡y i))

-- Transporting along reflexivity amounts to doing nothing.
--
-- This definition is based on code in Agda's reference manual written
-- by Anders Mörtberg.

transport-refl : ∀ i → transport (λ i → refl {x = A} i) i ≡ id
transport-refl {A = A} i = λ j → transport (λ _ → A) (i ⊔̲ j)

-- A family of instantiations of Congruence⁺.

congruence⁺ : ∀ ℓ → Congruence⁺ ℓ
Congruence⁺.reflexive-relation (congruence⁺ _) = reflexive-relation _
Congruence⁺.sym                (congruence⁺ _) = hsym
Congruence⁺.sym-refl           (congruence⁺ _) = refl
Congruence⁺.trans              (congruence⁺ _) = htransʳ
Congruence⁺.trans-refl-refl    (congruence⁺ _) = htransʳ-reflʳ _
Congruence⁺.hcong              (congruence⁺ _) = cong
Congruence⁺.hcong-refl         (congruence⁺ _) = λ _ → refl

-- A family of instantiations of Equality-with-J₀.

equality-with-J₀ : ∀ {a p} → Equality-with-J₀ a p reflexive-relation
Equality-with-J₀.elim      equality-with-J₀ = elim
Equality-with-J₀.elim-refl equality-with-J₀ = λ _ r →
  cong (_$ r _) $ transport-refl 0̲

-- A family of instantiations of Equality-with-J.

equality-with-J : ∀ {a p} → Equality-with-J a p congruence⁺
Equality-with-J.equality-with-J₀          equality-with-J = equality-with-J₀
Equality-with-J.cong                      equality-with-J = cong
Equality-with-J.cong-refl                 equality-with-J = λ _ → refl
Equality-with-J.subst                     equality-with-J = subst
Equality-with-J.subst-refl≡id             equality-with-J = λ _ → transport-refl 0̲
Equality-with-J.dependent-cong            equality-with-J = dependent-cong
Equality-with-J.dependent-cong-refl-hcong equality-with-J = λ _ → refl

-- Various derived definitions and properties.

open Derived-definitions-and-properties equality-with-J public
  hiding (_≡_; refl; elim; subst; cong; hcong; dependent-cong;
          step-≡; _≡⟨⟩_; finally;
          reflexive-relation; equality-with-J₀)

------------------------------------------------------------------------
-- A property

-- Heterogeneous equality can be expressed in terms of homogeneous
-- equality, at least up to logical equivalence.
--
-- TODO: Figure out if this property can be strengthened to an
-- equivalence.
--
-- This code is based on code from the cubical library written by
-- Anders Mörtberg.

heterogeneous⇔homogeneous :
  ∀ (P : I → Set p) {p q} →
  ([ P ] p ≡ q) ⇔ transport P 0̲ p ≡ q
heterogeneous⇔homogeneous P {p} {q} = record
  { to   = λ p≡q i → transport (λ j → P (i ⊔̲ j)) i (p≡q i)
  ; from = λ p≡q → htransʳ (λ i → transport (λ j → P (i ⊓̲ j)) (-̲ i) p)
                           p≡q
  }

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
        , (λ j → ⟨ext⟩f≡g′≡f≡g (-̲ i ⊔̲ j))
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
    subst (λ f → P (f x)) (⟨ext⟩ f≡g) p ≡ subst P (f≡g x) p
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
  {φ = i ⊔̲ j ⊔̲ -̲ j}
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
          , (hcomp (lemma₁ x) x  ≡⟨ sym $ hfill (lemma₁ x) (as-sub x) ⟩∎
             x                   ∎)
          )
        , λ y i →
              prim^glue (λ { (φ = 1̲) → proj₁ (lemma₂ 1̲-is-one y i) })
                        (hcomp (lemma₃ y i) x)
            , (hcomp (lemma₃ y i) x  ≡⟨ sym $ hfill (lemma₃ y i) (as-sub x) ⟩∎
               x                     ∎)
    }
    where
    f′ : PartialP φ (λ x → B x ≃ A)
    f′ p = ≃⇒≃⁻¹ (f p)

    lemma₁ : A → ∀ i → Partial φ A
    lemma₁ x i (φ = 1̲) = (
      x                                  ≡⟨ sym (_≃_.right-inverse-of (f′ 1̲-is-one) x) ⟩∎
      _≃_.to (f′ _) (_≃_.from (f′ _) x)  ∎) i

    lemma₂ : ∀ {x} p (y : _≃_.to (f′ p) ⁻¹ x) →
             (_≃_.from (f′ p) x , _≃_.right-inverse-of (f′ p) x) ≡ y
    lemma₂ {x} p = _≃_.irrelevance (f′ p) x

    lemma₃ : ∀ {x} → prim^unglue {e = f} ⁻¹ x →
             ∀ i → I → Partial (φ ⊔̲ i ⊔̲ -̲ i) A
    lemma₃     y i j (φ = 1̲) = sym (proj₂ (lemma₂ 1̲-is-one y i)) j
    lemma₃ {x} _ i j (i = 0̲) = hfill (lemma₁ x) (as-sub x) j
    lemma₃     y i j (i = 1̲) = sym (proj₂ y) j

-- An alternative formulation of univalence.

other-univ : Other-univalence ℓ
other-univ {ℓ = ℓ} {B = B} =
    (B , Eq.id)
  , λ { (A , A≃B) i →
          let C : ∀ i → Partial (i ⊔̲ -̲ i) (Set ℓ)
              C = λ { i (i = 0̲) → B
                    ; i (i = 1̲) → A
                    }

              f : ∀ i → PartialP (i ⊔̲ -̲ i) (λ j → C i j Glue.≃ B)
              f = λ { i (i = 0̲) → ≃⇒≃ Eq.id
                    ; i (i = 1̲) → ≃⇒≃ A≃B
                    }
          in
            primGlue  _ _ (f i)
          , primGlue≃ _ _ (f i)
      }
