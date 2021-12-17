------------------------------------------------------------------------
-- Equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module Equivalence
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection using (_↔_)
open Derived-definitions-and-properties eq
open import Equality.Decidable-UIP eq using (propositional-identity⇒set)
import Equivalence.Half-adjoint eq as HA
open import Groupoid eq
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (_↣_; Injective)
open import Logical-equivalence as L-eq using (_⇔_)
import Nat eq as Nat
open import Preimage eq as Preimage using (_⁻¹_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
open import Surjection eq as Surjection using (_↠_)

------------------------------------------------------------------------
-- Is-equivalence

open HA public using
  (Is-equivalence;
   propositional;
   sometimes-contractible;
   respects-extensional-equality;
   function-between-contractible-types-is-equivalence;
   drop-Σ-map-id;
   inverse-drop-Σ-map-id;
   ext⁻¹-is-equivalence)

------------------------------------------------------------------------
-- _≃_

private
 module Dummy where

  -- Equivalences.

  infix 4 _≃_

  record _≃_ {a b} (A : Type a) (B : Type b) : Type (a ⊔ b) where
    constructor ⟨_,_⟩
    field
      to             : A → B
      is-equivalence : Is-equivalence to

open Dummy public using (_≃_; ⟨_,_⟩) hiding (module _≃_)

-- Some definitions with erased type arguments.

module _≃₀_ {a b} {@0 A : Type a} {@0 B : Type b} (A≃B : A ≃ B) where

  -- The forward direction of the equivalence.

  to : A → B
  to = Dummy._≃_.to A≃B

  -- The function to is an equivalence.

  is-equivalence : Is-equivalence to
  is-equivalence = Dummy._≃_.is-equivalence A≃B

  -- Equivalent types are isomorphic.

  from : B → A
  from = HA.inverse is-equivalence

  right-inverse-of : ∀ x → to (from x) ≡ x
  right-inverse-of = HA.right-inverse-of is-equivalence

  left-inverse-of : ∀ x → from (to x) ≡ x
  left-inverse-of = HA.left-inverse-of is-equivalence

  bijection : A ↔ B
  bijection = record
    { surjection = record
      { logical-equivalence = record
        { to   = to
        ; from = from
        }
      ; right-inverse-of = right-inverse-of
      }
    ; left-inverse-of = left-inverse-of
    }

module _≃_ {a b} {A : Type a} {B : Type b} (A≃B : A ≃ B) where

  open _≃₀_ A≃B public

  open _↔_ bijection public
    hiding (from; to; right-inverse-of; left-inverse-of)

  -- All preimages of an element under the equivalence are equal.

  irrelevance : ∀ y (p : to ⁻¹ y) → (from y , right-inverse-of y) ≡ p
  irrelevance = HA.irrelevance is-equivalence

  -- The two proofs left-inverse-of and right-inverse-of are
  -- related.

  left-right-lemma :
    ∀ x → cong to (left-inverse-of x) ≡ right-inverse-of (to x)
  left-right-lemma = proj₂ (proj₂ (proj₂ is-equivalence))

  right-left-lemma :
    ∀ x → cong from (right-inverse-of x) ≡ left-inverse-of (from x)
  right-left-lemma =
    proj₂ (proj₂ (proj₂ (HA.inverse-equivalence is-equivalence)))

-- Equivalences are isomorphic to pairs.

≃-as-Σ : ∀ {a b} {A : Type a} {B : Type b} →
         A ≃ B ↔ ∃ λ (f : A → B) → Is-equivalence f
≃-as-Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { ⟨ f , is ⟩ → f , is }
      ; from = uncurry ⟨_,_⟩
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- Bijections are equivalences.
--
-- Note that the right inverse proof is preserved unchanged.

↔⇒≃ : ∀ {a b} {A : Type a} {B : Type b} → A ↔ B → A ≃ B
↔⇒≃ A↔B = record
  { to             = _↔_.to A↔B
  ; is-equivalence = HA.↔→Is-equivalenceʳ A↔B
  }

_ :
  ∀ {a b} {A : Type a} {B : Type b} {A↔B : A ↔ B} →
  _≃_.right-inverse-of (↔⇒≃ A↔B) ≡ _↔_.right-inverse-of A↔B
_ = refl _

-- A variant of the previous result.
--
-- Note that the right inverse proof is preserved unchanged.

↔→≃ :
  ∀ {a b} {A : Type a} {B : Type b} →
  (f : A → B) (g : B → A) →
  (∀ x → f (g x) ≡ x) →
  (∀ x → g (f x) ≡ x) →
  A ≃ B
↔→≃ f g f∘g g∘f = ↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = f
      ; from = g
      }
    ; right-inverse-of = f∘g
    }
  ; left-inverse-of = g∘f
  })

_ :
  ∀ {a b} {A : Type a} {B : Type b} {f : A → B} {g : B → A}
    {f-g : ∀ x → f (g x) ≡ x} {g-f : ∀ x → g (f x) ≡ x} →
  _≃_.right-inverse-of (↔→≃ f g f-g g-f) ≡ f-g
_ = refl _

-- There is a logical equivalence between A ↔ B and A ≃ B.

↔⇔≃ :
  ∀ {a b} {A : Type a} {B : Type b} →
  (A ↔ B) ⇔ (A ≃ B)
↔⇔≃ = record
  { to   = ↔⇒≃
  ; from = _≃_.bijection
  }

-- The function subst is an equivalence family.

subst-as-equivalence :
  ∀ {a p} {A : Type a} (P : A → Type p) {x y : A} (x≡y : x ≡ y) →
  P x ≃ P y
subst-as-equivalence P {y = y} x≡y = ↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = subst P x≡y
      ; from = subst P (sym x≡y)
      }
    ; right-inverse-of = subst-subst-sym P x≡y
    }
  ; left-inverse-of = λ p →
      subst P (sym x≡y) (subst P x≡y p)              ≡⟨ cong (λ eq → subst P (sym x≡y) (subst P eq _)) $ sym $ sym-sym _ ⟩
      subst P (sym x≡y) (subst P (sym (sym x≡y)) p)  ≡⟨ subst-subst-sym P _ _ ⟩∎
      p                                              ∎
  })

abstract

  subst-is-equivalence :
    ∀ {a p} {A : Type a} (P : A → Type p) {x y : A} (x≡y : x ≡ y) →
    Is-equivalence (subst P x≡y)
  subst-is-equivalence P x≡y =
    _≃_.is-equivalence (subst-as-equivalence P x≡y)

------------------------------------------------------------------------
-- Equivalence

-- Equivalences are equivalence relations.

id : ∀ {a} {A : Type a} → A ≃ A
id = ⟨ P.id , HA.id-equivalence ⟩

inverse : ∀ {a b} {A : Type a} {B : Type b} → A ≃ B → B ≃ A
inverse A≃B =
  ⟨ HA.inverse             (_≃_.is-equivalence A≃B)
  , HA.inverse-equivalence (_≃_.is-equivalence A≃B)
  ⟩

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
      B ≃ C → A ≃ B → A ≃ C
f ∘ g =
  ⟨ _≃_.to f ⊚ _≃_.to g
  , HA.composition-equivalence
      (_≃_.is-equivalence f)
      (_≃_.is-equivalence g)
  ⟩

-- Equational reasoning combinators.

infix  -1 finally-≃
infixr -2 step-≃

-- For an explanation of why step-≃ is defined in this way, see
-- Equality.step-≡.

step-≃ : ∀ {a b c} (A : Type a) {B : Type b} {C : Type c} →
         B ≃ C → A ≃ B → A ≃ C
step-≃ _ = _∘_

syntax step-≃ A B≃C A≃B = A ≃⟨ A≃B ⟩ B≃C

finally-≃ : ∀ {a b} (A : Type a) (B : Type b) → A ≃ B → A ≃ B
finally-≃ _ _ A≃B = A≃B

syntax finally-≃ A B A≃B = A ≃⟨ A≃B ⟩□ B □

-- Some simplification lemmas.

right-inverse-of-id :
  ∀ {a} {A : Type a} {x : A} →
  _≃_.right-inverse-of id x ≡ refl x
right-inverse-of-id {x = x} = refl (refl x)

left-inverse-of-id :
  ∀ {a} {A : Type a} {x : A} →
  _≃_.left-inverse-of id x ≡ refl x
left-inverse-of-id {x = x} = refl (refl x)

right-inverse-of∘inverse :
  ∀ {a b} {A : Type a} {B : Type b} →
  ∀ (A≃B : A ≃ B) {x} →
  _≃_.right-inverse-of (inverse A≃B) x ≡
  _≃_.left-inverse-of A≃B x
right-inverse-of∘inverse _ = refl _

left-inverse-of∘inverse :
  ∀ {a b} {A : Type a} {B : Type b} →
  ∀ (A≃B : A ≃ B) {x} →
  _≃_.left-inverse-of (inverse A≃B) x ≡
  _≃_.right-inverse-of A≃B x
left-inverse-of∘inverse _ = refl _

------------------------------------------------------------------------
-- One can replace either of the functions with an extensionally equal
-- function

with-other-function :
  ∀ {a b} {A : Type a} {B : Type b}
  (A≃B : A ≃ B) (f : A → B) →
  (∀ x → _≃_.to A≃B x ≡ f x) →
  A ≃ B
with-other-function ⟨ g , is-equivalence ⟩ f g≡f =
  ⟨ f , respects-extensional-equality g≡f is-equivalence ⟩

with-other-inverse :
  ∀ {a b} {A : Type a} {B : Type b}
  (A≃B : A ≃ B) (f : B → A) →
  (∀ x → _≃_.from A≃B x ≡ f x) →
  A ≃ B
with-other-inverse A≃B f from≡f =
  inverse $ with-other-function (inverse A≃B) f from≡f

private

  -- The two functions above compute in the right way.

  to∘with-other-function :
    ∀ {a b} {A : Type a} {B : Type b}
    (A≃B : A ≃ B) (f : A → B)
    (to≡f : ∀ x → _≃_.to A≃B x ≡ f x) →
    _≃_.to (with-other-function A≃B f to≡f) ≡ f
  to∘with-other-function _ _ _ = refl _

  from∘with-other-function :
    ∀ {a b} {A : Type a} {B : Type b}
    (A≃B : A ≃ B) (f : A → B)
    (to≡f : ∀ x → _≃_.to A≃B x ≡ f x) →
    _≃_.from (with-other-function A≃B f to≡f) ≡ _≃_.from A≃B
  from∘with-other-function _ _ _ = refl _

  to∘with-other-inverse :
    ∀ {a b} {A : Type a} {B : Type b}
    (A≃B : A ≃ B) (g : B → A)
    (from≡g : ∀ x → _≃_.from A≃B x ≡ g x) →
    _≃_.to (with-other-inverse A≃B g from≡g) ≡ _≃_.to A≃B
  to∘with-other-inverse _ _ _ = refl _

  from∘with-other-inverse :
    ∀ {a b} {A : Type a} {B : Type b}
    (A≃B : A ≃ B) (g : B → A)
    (from≡g : ∀ x → _≃_.from A≃B x ≡ g x) →
    _≃_.from (with-other-inverse A≃B g from≡g) ≡ g
  from∘with-other-inverse _ _ _ = refl _

------------------------------------------------------------------------
-- The two-out-of-three property

-- If two out of three of f, g and g ∘ f are equivalences, then the
-- third one is also an equivalence.

record Two-out-of-three
         {a b c} {A : Type a} {B : Type b} {C : Type c}
         (f : A → B) (g : B → C) : Type (a ⊔ b ⊔ c) where
  field
    f-g   : Is-equivalence f → Is-equivalence g → Is-equivalence (g ⊚ f)
    g-g∘f : Is-equivalence g → Is-equivalence (g ⊚ f) → Is-equivalence f
    g∘f-f : Is-equivalence (g ⊚ f) → Is-equivalence f → Is-equivalence g

two-out-of-three :
  ∀ {a b c} {A : Type a} {B : Type b} {C : Type c}
  (f : A → B) (g : B → C) → Two-out-of-three f g
two-out-of-three f g = record
  { f-g   = λ f-eq g-eq →
              _≃_.is-equivalence (⟨ g , g-eq ⟩ ∘ ⟨ f , f-eq ⟩)
  ; g-g∘f = λ g-eq g∘f-eq →
              respects-extensional-equality
                (λ x → let g⁻¹ = _≃_.from ⟨ g , g-eq ⟩ in
                   g⁻¹ (g (f x))  ≡⟨ _≃_.left-inverse-of ⟨ g , g-eq ⟩ (f x) ⟩∎
                   f x            ∎)
                (_≃_.is-equivalence
                   (inverse ⟨ g , g-eq ⟩ ∘ ⟨ _ , g∘f-eq ⟩))
  ; g∘f-f = λ g∘f-eq f-eq →
              respects-extensional-equality
                (λ x → let f⁻¹ = _≃_.from ⟨ f , f-eq ⟩ in
                   g (f (f⁻¹ x))  ≡⟨ cong g (_≃_.right-inverse-of ⟨ f , f-eq ⟩ x) ⟩∎
                   g x            ∎)
                (_≃_.is-equivalence
                   (⟨ _ , g∘f-eq ⟩ ∘ inverse ⟨ f , f-eq ⟩))
  }

------------------------------------------------------------------------
-- Extensionality

-- f ≡ g and ∀ x → f x ≡ g x are isomorphic (assuming extensionality).

extensionality-isomorphism :
  ∀ {a b} →
  Extensionality a b →
  {A : Type a} {B : A → Type b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) ≃ (f ≡ g)
extensionality-isomorphism ext =
  inverse ⟨ _ , ext⁻¹-is-equivalence (apply-ext ext) ⟩

-- Note that the isomorphism gives us a really well-behaved notion of
-- extensionality.

good-ext : ∀ {a b} → Extensionality a b → Extensionality a b
apply-ext (good-ext ext) = _≃_.to (extensionality-isomorphism ext)

abstract

  good-ext-is-equivalence :
    ∀ {a b} (ext : Extensionality a b) →
    {A : Type a} {B : A → Type b} {f g : (x : A) → B x} →
    Is-equivalence {A = ∀ x → f x ≡ g x} (apply-ext (good-ext ext))
  good-ext-is-equivalence ext =
    _≃_.is-equivalence (extensionality-isomorphism ext)

  good-ext-refl :
    ∀ {a b} (ext : Extensionality a b)
    {A : Type a} {B : A → Type b} (f : (x : A) → B x) →
    apply-ext (good-ext ext) (λ x → refl (f x)) ≡ refl f
  good-ext-refl ext f =
    _≃_.to (extensionality-isomorphism ext) (λ x → refl (f x))  ≡⟨ cong (_≃_.to (extensionality-isomorphism ext)) $ sym $
                                                                        apply-ext ext (λ _ → ext⁻¹-refl f) ⟩
    _≃_.to (extensionality-isomorphism ext) (ext⁻¹ (refl f))    ≡⟨ _≃_.right-inverse-of (extensionality-isomorphism ext) _ ⟩∎
    refl f                                                      ∎

  good-ext-const :
    ∀ {a b} (ext : Extensionality a b)
    {A : Type a} {B : Type b} {x y : B}
    (x≡y : x ≡ y) →
    apply-ext (good-ext ext) (const {B = A} x≡y) ≡
    cong const x≡y
  good-ext-const ext x≡y =
    apply-ext (good-ext ext) (const x≡y)                        ≡⟨ cong (apply-ext (good-ext ext) ⊚ const) $ cong-id _ ⟩
    apply-ext (good-ext ext) (const (cong P.id x≡y))            ≡⟨⟩
    apply-ext (good-ext ext) (λ z → cong ((_$ z) ⊚ const) x≡y)  ≡⟨ cong (apply-ext (good-ext ext)) $
                                                                   apply-ext (good-ext ext) (λ _ → sym $ cong-∘ _ _ _) ⟩
    apply-ext (good-ext ext) (ext⁻¹ (cong const x≡y))           ≡⟨ _≃_.right-inverse-of (extensionality-isomorphism ext) _ ⟩∎
    cong const x≡y                                              ∎

  cong-good-ext :
    ∀ {a b} (ext : Extensionality a b)
    {A : Type a} {B : A → Type b} {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) {x} →
    cong (_$ x) (apply-ext (good-ext ext) f≡g) ≡ f≡g x
  cong-good-ext ext f≡g {x} =
    cong (_$ x) (apply-ext (good-ext ext) f≡g)  ≡⟨⟩
    ext⁻¹ (apply-ext (good-ext ext) f≡g) x      ≡⟨ cong (_$ x) $ _≃_.left-inverse-of (extensionality-isomorphism ext) f≡g ⟩∎
    f≡g x                                       ∎

  good-ext-cong :
    ∀ {a b c} (ext : Extensionality b c)
    {A : Type a} {B : Type b} {C : B → Type c}
    {f : A → (x : B) → C x} {x y : A} {x≡y : x ≡ y} →
    apply-ext (good-ext ext) (λ z → cong (flip f z) x≡y) ≡
    cong f x≡y
  good-ext-cong ext {f = f} {x≡y = x≡y} =
    apply-ext (good-ext ext) (λ z → cong (flip f z) x≡y)       ≡⟨ (cong (apply-ext (good-ext ext)) $ apply-ext ext λ _ → sym $ cong-∘ _ _ _) ⟩
    apply-ext (good-ext ext) (λ z → cong (_$ z) (cong f x≡y))  ≡⟨⟩
    apply-ext (good-ext ext) (ext⁻¹ (cong f x≡y))              ≡⟨ _≃_.right-inverse-of (extensionality-isomorphism ext) _ ⟩∎
    cong f x≡y                                                 ∎

  subst-good-ext :
    ∀ {a b p} (ext : Extensionality a b)
    {A : Type a} {B : A → Type b} {f g : (x : A) → B x} {x}
    (P : B x → Type p) {p}
    (f≡g : ∀ x → f x ≡ g x) →
    subst (λ f → P (f x)) (apply-ext (good-ext ext) f≡g) p ≡
    subst P (f≡g x) p
  subst-good-ext ext {f = f} {g} {x} P {p} f≡g =
    subst (λ f → P (f x)) (apply-ext (good-ext ext) f≡g) p  ≡⟨ subst-∘ P (_$ x) _ ⟩
    subst P (cong (_$ x) (apply-ext (good-ext ext) f≡g)) p  ≡⟨ cong (λ eq → subst P eq p) (cong-good-ext ext f≡g) ⟩∎
    subst P (f≡g x) p                                       ∎

  elim-good-ext :
    ∀ {a b p}
    (ext : Extensionality a b)
    {A : Type a} {B : A → Type b} {x : A}
    (P : B x → B x → Type p)
    (p : (y : B x) → P y y)
    {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) →
    elim (λ {f g} _ → P (f x) (g x)) (p ⊚ (_$ x))
         (apply-ext (good-ext ext) f≡g) ≡
    elim (λ {x y} _ → P x y) p (f≡g x)
  elim-good-ext ext {x = x} P p f≡g =
    elim (λ {f g} _ → P (f x) (g x)) (p ⊚ (_$ x)) (apply-ext (good-ext ext) f≡g)  ≡⟨ sym $ elim-cong _ _ _ ⟩
    elim (λ {x y} _ → P x y) p (cong (_$ x) (apply-ext (good-ext ext) f≡g))       ≡⟨ cong (elim (λ {x y} _ → P x y) p) (cong-good-ext ext f≡g) ⟩
    elim (λ {x y} _ → P x y) p (f≡g x)                                            ∎

  -- I based the statements of the following three lemmas on code in
  -- the Lean Homotopy Type Theory Library with Jakob von Raumer and
  -- Floris van Doorn listed as authors. The file was claimed to have
  -- been ported from the Coq HoTT library. (The third lemma has later
  -- been generalised.)

  good-ext-sym :
    ∀ {a b} (ext : Extensionality a b)
    {A : Type a} {B : A → Type b} {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) →
    apply-ext (good-ext ext) (sym ⊚ f≡g) ≡
    sym (apply-ext (good-ext ext) f≡g)
  good-ext-sym ext f≡g =
    apply-ext (good-ext ext) (sym ⊚ f≡g)                 ≡⟨ cong (apply-ext (good-ext ext) ⊚ (sym ⊚_)) $ sym $
                                                              _≃_.left-inverse-of (extensionality-isomorphism ext) _ ⟩
    apply-ext (good-ext ext)
      (sym ⊚ ext⁻¹ (apply-ext (good-ext ext) f≡g))       ≡⟨⟩

    apply-ext (good-ext ext) (λ x →
      sym $ cong (_$ x) (apply-ext (good-ext ext) f≡g))  ≡⟨ cong (apply-ext (good-ext ext)) $
                                                              apply-ext ext (λ _ → sym $ cong-sym _ _) ⟩
    apply-ext (good-ext ext) (λ x →
      cong (_$ x) (sym $ apply-ext (good-ext ext) f≡g))  ≡⟨⟩

    apply-ext (good-ext ext)
      (ext⁻¹ (sym $ apply-ext (good-ext ext) f≡g))       ≡⟨ _≃_.right-inverse-of (extensionality-isomorphism ext) _ ⟩∎

    sym (apply-ext (good-ext ext) f≡g)                   ∎

  good-ext-trans :
    ∀ {a b} (ext : Extensionality a b)
    {A : Type a} {B : A → Type b} {f g h : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) (g≡h : ∀ x → g x ≡ h x) →
    apply-ext (good-ext ext) (λ x → trans (f≡g x) (g≡h x)) ≡
    trans (apply-ext (good-ext ext) f≡g) (apply-ext (good-ext ext) g≡h)
  good-ext-trans ext f≡g g≡h =
    apply-ext (good-ext ext) (λ x → trans (f≡g x) (g≡h x))  ≡⟨ sym $ cong₂ (λ f g → apply-ext (good-ext ext) (λ x → trans (f x) (g x)))
                                                                           (_≃_.left-inverse-of (extensionality-isomorphism ext) _)
                                                                           (_≃_.left-inverse-of (extensionality-isomorphism ext) _) ⟩
    apply-ext (good-ext ext) (λ x →
      trans (ext⁻¹ (apply-ext (good-ext ext) f≡g) x)
            (ext⁻¹ (apply-ext (good-ext ext) g≡h) x))       ≡⟨⟩

    apply-ext (good-ext ext) (λ x →
      trans (cong (_$ x) (apply-ext (good-ext ext) f≡g))
            (cong (_$ x) (apply-ext (good-ext ext) g≡h)))   ≡⟨ cong (apply-ext (good-ext ext)) $ apply-ext ext (λ _ → sym $
                                                                 cong-trans _ _ _) ⟩
    apply-ext (good-ext ext) (λ x →
      cong (_$ x) (trans (apply-ext (good-ext ext) f≡g)
                         (apply-ext (good-ext ext) g≡h)))   ≡⟨⟩

    apply-ext (good-ext ext)
      (ext⁻¹ (trans (apply-ext (good-ext ext) f≡g)
                    (apply-ext (good-ext ext) g≡h)))        ≡⟨ _≃_.right-inverse-of (extensionality-isomorphism ext) _ ⟩∎

    trans (apply-ext (good-ext ext) f≡g)
          (apply-ext (good-ext ext) g≡h)                    ∎

  cong-post-∘-good-ext :
    ∀ {a b c} {A : Type a} {B : A → Type b} {C : A → Type c}
      {f g : (x : A) → B x} {h : ∀ {x} → B x → C x}
    (ext₁ : Extensionality a b)
    (ext₂ : Extensionality a c)
    (f≡g : ∀ x → f x ≡ g x) →
    cong (h ⊚_) (apply-ext (good-ext ext₁) f≡g) ≡
    apply-ext (good-ext ext₂) (cong h ⊚ f≡g)
  cong-post-∘-good-ext {f = f} {g} {h} ext₁ ext₂ f≡g =
    cong (h ⊚_) (apply-ext (good-ext ext₁) f≡g)                   ≡⟨ sym $ _≃_.right-inverse-of (extensionality-isomorphism ext₂) _ ⟩

    apply-ext (good-ext ext₂)
      (ext⁻¹ (cong (h ⊚_) (apply-ext (good-ext ext₁) f≡g)))       ≡⟨⟩

    apply-ext (good-ext ext₂) (λ x →
      cong (_$ x) (cong (h ⊚_) (apply-ext (good-ext ext₁) f≡g)))  ≡⟨ cong (apply-ext (good-ext ext₂)) $ apply-ext ext₂ (λ _ →
                                                                       cong-∘ _ _ _) ⟩
    apply-ext (good-ext ext₂) (λ x →
      cong (λ f → h (f x)) (apply-ext (good-ext ext₁) f≡g))       ≡⟨ cong (apply-ext (good-ext ext₂)) $ apply-ext ext₂ (λ _ → sym $
                                                                       cong-∘ _ _ _) ⟩
    apply-ext (good-ext ext₂) (λ x →
      cong h (cong (_$ x) (apply-ext (good-ext ext₁) f≡g)))       ≡⟨⟩

    apply-ext (good-ext ext₂)
      (cong h ⊚ ext⁻¹ (apply-ext (good-ext ext₁) f≡g))            ≡⟨ cong (apply-ext (good-ext ext₂) ⊚ (cong h ⊚_)) $
                                                                       _≃_.left-inverse-of (extensionality-isomorphism ext₁) _ ⟩∎
    apply-ext (good-ext ext₂) (cong h ⊚ f≡g)                      ∎

  cong-pre-∘-good-ext :
    ∀ {a b c} {A : Type a} {B : Type b} {C : B → Type c}
      {f g : (x : B) → C x} {h : A → B}
    (ext₁ : Extensionality a c)
    (ext₂ : Extensionality b c)
    (f≡g : ∀ x → f x ≡ g x) →
    cong (_⊚ h) (apply-ext (good-ext ext₂) f≡g) ≡ apply-ext (good-ext ext₁) (f≡g ⊚ h)
  cong-pre-∘-good-ext {f = f} {g} {h} ext₁ ext₂ f≡g =
    cong (_⊚ h) (apply-ext (good-ext ext₂) f≡g)                   ≡⟨ sym $ _≃_.right-inverse-of (extensionality-isomorphism ext₁) _ ⟩

    apply-ext (good-ext ext₁)
      (ext⁻¹ (cong (_⊚ h) (apply-ext (good-ext ext₂) f≡g)))       ≡⟨⟩

    apply-ext (good-ext ext₁) (λ x →
      cong (_$ x) (cong (_⊚ h) (apply-ext (good-ext ext₂) f≡g)))  ≡⟨ cong (apply-ext (good-ext ext₁)) $ apply-ext ext₁ (λ _ →
                                                                       cong-∘ _ _ _) ⟩
    apply-ext (good-ext ext₁) (λ x →
      cong (_$ h x) (apply-ext (good-ext ext₂) f≡g))              ≡⟨ cong (apply-ext (good-ext ext₁)) $ apply-ext ext₁ (λ _ →
                                                                       cong-good-ext ext₂ _) ⟩
    apply-ext (good-ext ext₁) (λ x → f≡g (h x))                   ≡⟨⟩

    apply-ext (good-ext ext₁) (f≡g ⊚ h)                           ∎

  cong-∘-good-ext :
    ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} {f g : B → C}
    (ext₁ : Extensionality b c)
    (ext₂ : Extensionality (a ⊔ b) (a ⊔ c))
    (ext₃ : Extensionality a c)
    (f≡g : ∀ x → f x ≡ g x) →
    cong {B = (A → B) → (A → C)}
         (λ f → f ⊚_) (apply-ext (good-ext ext₁) f≡g) ≡
    apply-ext (good-ext ext₂) λ h → apply-ext (good-ext ext₃) λ x →
    f≡g (h x)
  cong-∘-good-ext ext₁ ext₂ ext₃ f≡g =
    cong (λ f → f ⊚_) (apply-ext (good-ext ext₁) f≡g)                  ≡⟨ sym $ _≃_.right-inverse-of (extensionality-isomorphism ext₂) _ ⟩

    (apply-ext (good-ext ext₂) λ h →
     cong (_$ h) (cong (λ f → f ⊚_) (apply-ext (good-ext ext₁) f≡g)))  ≡⟨ (cong (apply-ext (good-ext ext₂)) $ apply-ext ext₂ λ _ →
                                                                           cong-∘ _ _ _) ⟩

    (apply-ext (good-ext ext₂) λ h →
     cong (_⊚ h) (apply-ext (good-ext ext₁) f≡g))                      ≡⟨ (cong (apply-ext (good-ext ext₂)) $ apply-ext ext₂ λ _ → cong-pre-∘-good-ext ext₃ ext₁ _) ⟩∎

    (apply-ext (good-ext ext₂) λ h → apply-ext (good-ext ext₃) λ x →
     f≡g (h x))                                                        ∎

------------------------------------------------------------------------
-- Groupoid

abstract

  -- Two proofs of equivalence are equal if the function components
  -- are equal (assuming extensionality).
  --
  -- See also Function-universe.≃-to-≡↔≡.

  lift-equality :
    ∀ {a b} → Extensionality (a ⊔ b) (a ⊔ b) →
    {A : Type a} {B : Type b} {p q : A ≃ B} →
    _≃_.to p ≡ _≃_.to q → p ≡ q
  lift-equality {a} {b} ext {p = ⟨ f , f-eq ⟩} {q = ⟨ g , g-eq ⟩} f≡g =
    elim (λ {f g} f≡g → ∀ f-eq g-eq → ⟨ f , f-eq ⟩ ≡ ⟨ g , g-eq ⟩)
         (λ f f-eq g-eq →
            cong (⟨_,_⟩ f) (propositional ext f f-eq g-eq))
         f≡g f-eq g-eq

  -- A computation rule for lift-equality.

  lift-equality-refl :
    ∀ {a b} {A : Type a} {B : Type b}
      {p : A ≃ B} {q : Is-equivalence (_≃_.to p)}
    (ext : Extensionality (a ⊔ b) (a ⊔ b)) →
    lift-equality ext (refl (_≃_.to p)) ≡
    cong ⟨ _≃_.to p ,_⟩
      (propositional ext (_≃_.to p) (_≃_.is-equivalence p) q)
  lift-equality-refl ext =
    cong (λ f → f _ _) $
    elim-refl
      (λ {f g} f≡g → ∀ f-eq g-eq → ⟨ f , f-eq ⟩ ≡ ⟨ g , g-eq ⟩)
      _

  -- Two proofs of equivalence are equal if the /inverses/ of the
  -- function components are equal (assuming extensionality).
  --
  -- See also Function-universe.≃-from-≡↔≡.

  lift-equality-inverse :
    ∀ {a b} → Extensionality (a ⊔ b) (a ⊔ b) →
    {A : Type a} {B : Type b} {p q : A ≃ B} →
    _≃_.from p ≡ _≃_.from q → p ≡ q
  lift-equality-inverse ext {p = p} {q = q} f≡g =
    p                    ≡⟨ lift-equality ext (refl _) ⟩
    inverse (inverse p)  ≡⟨ cong inverse $
                            lift-equality ext {p = inverse p} {q = inverse q} f≡g ⟩
    inverse (inverse q)  ≡⟨ lift-equality ext (refl _) ⟩∎
    q                    ∎

  -- An equality rearrangement lemma.

  cong-to-from-lift-equality :
    ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} {eq₁ eq₂ : A ≃ B}
      {f : (A → B) → (B → A) → C}
      {eq : _≃_.to eq₁ ≡ _≃_.to eq₂} →
    (ext₁ : Extensionality (a ⊔ b) (a ⊔ b))
    (ext₂ : Extensionality b a) →
    cong (λ eq → f (_≃_.to eq) (_≃_.from eq))
      (lift-equality ext₁ {p = eq₁} {q = eq₂} eq) ≡
    cong₂ f
      eq
      (apply-ext (good-ext ext₂) λ b →

       _≃_.from eq₁ b                              ≡⟨ cong (_≃_.from eq₁) $ sym $ _≃_.right-inverse-of eq₂ b ⟩
       _≃_.from eq₁ (_≃_.to eq₂ (_≃_.from eq₂ b))  ≡⟨ cong (_≃_.from eq₁) $ cong (_$ _≃_.from eq₂ b) $ sym eq ⟩
       _≃_.from eq₁ (_≃_.to eq₁ (_≃_.from eq₂ b))  ≡⟨ _≃_.left-inverse-of eq₁ (_≃_.from eq₂ b) ⟩∎
       _≃_.from eq₂ b                              ∎)
  cong-to-from-lift-equality {eq₂ = eq₂} {f = f} {eq = eq} ext₁ ext₂ =
    elim₁
      (λ {g} eq →
         (is-eq : Is-equivalence g) →
         let eq₁ = ⟨ g , is-eq ⟩ in
         cong (λ eq → f (_≃_.to eq) (_≃_.from eq))
           (lift-equality ext₁ {p = eq₁} {q = eq₂} eq) ≡
         cong₂ f
           eq
           (apply-ext (good-ext ext₂) λ b →
            trans (cong (_≃_.from eq₁) $ sym $
                   _≃_.right-inverse-of eq₂ b) $
            trans (cong (_≃_.from eq₁) $
                   cong (_$ _≃_.from eq₂ b) $ sym eq) $
            _≃_.left-inverse-of eq₁ (_≃_.from eq₂ b)))
      (λ is-eq →
         let eq₁ = ⟨ _≃_.to eq₂ , is-eq ⟩ in

         cong (λ eq → f (_≃_.to eq) (_≃_.from eq))
           (lift-equality ext₁ (refl _))                                   ≡⟨ cong (cong _) $ lift-equality-refl ext₁ ⟩

         cong (λ eq → f (_≃_.to eq) (_≃_.from eq))
           (cong ⟨ _≃_.to eq₂ ,_⟩
              (propositional ext₁ (_≃_.to eq₂) _ _))                       ≡⟨ cong-∘ _ _ _ ⟩

         cong (λ is-eq → f (_≃_.to eq₂) (_≃_.from ⟨ _ , is-eq ⟩))
           (propositional ext₁ (_≃_.to eq₂) _ _)                           ≡⟨ sym $ cong-∘ _ _ _ ⟩

         cong (f (_≃_.to eq₂))
           (cong (λ is-eq → _≃_.from ⟨ _ , is-eq ⟩)
              (propositional ext₁ (_≃_.to eq₂) _ _))                       ≡⟨ cong (cong _) $
                                                                              elim₁
                                                                                (λ {is-eq} eq →
                                                                                   let eq₁ = ⟨ _≃_.to eq₂ , is-eq ⟩ in
                                                                                   cong (λ is-eq → _≃_.from ⟨ _ , is-eq ⟩) eq ≡
                                                                                   apply-ext (good-ext ext₂) λ b →
                                                                                   trans (cong (_≃_.from eq₁) $ sym $
                                                                                          _≃_.right-inverse-of eq₂ b) $
                                                                                   _≃_.left-inverse-of eq₁ (_≃_.from eq₂ b))
                                                                                (
             cong (λ is-eq → _≃_.from ⟨ _ , is-eq ⟩) (refl _)                    ≡⟨ cong-refl _ ⟩

             refl _                                                              ≡⟨ sym (good-ext-refl ext₂ _) ⟩

             (apply-ext (good-ext ext₂) λ _ → refl _)                            ≡⟨ (cong (apply-ext (good-ext ext₂)) $ apply-ext ext₂ λ _ → sym $
                                                                                     trans-symˡ _) ⟩
             (apply-ext (good-ext ext₂) λ b →
              trans (sym $ cong (_≃_.from eq₂) $
                     _≃_.right-inverse-of eq₂ b) $
              cong (_≃_.from eq₂) $ _≃_.right-inverse-of eq₂ b)                  ≡⟨ (cong (apply-ext (good-ext ext₂)) $ apply-ext ext₂ λ _ →
                                                                                     cong₂ trans
                                                                                       (sym $ cong-sym _ _)
                                                                                       (_≃_.right-left-lemma eq₂ _)) ⟩∎
             (apply-ext (good-ext ext₂) λ b →
              trans (cong (_≃_.from eq₂) $ sym $
                     _≃_.right-inverse-of eq₂ b) $
              _≃_.left-inverse-of eq₂ (_≃_.from eq₂ b))                          ∎)
                                                                                (propositional ext₁ (_≃_.to eq₂) _ _) ⟩
         cong (f (_≃_.to eq₂))
           (apply-ext (good-ext ext₂) λ b →
            trans (cong (_≃_.from eq₁) $ sym $
                   _≃_.right-inverse-of eq₂ b) $
            _≃_.left-inverse-of eq₁ (_≃_.from eq₂ b))                      ≡⟨ (cong (cong _) $
                                                                               cong (apply-ext (good-ext ext₂)) $ apply-ext ext₂ λ _ →
                                                                               cong (trans _) $ sym $
                                                                               trans (cong (flip trans _) $
                                                                                      trans (cong (cong _) $
                                                                                             trans (cong (cong _) sym-refl) $
                                                                                             cong-refl _) $
                                                                                      cong-refl _) $
                                                                               trans-reflˡ _) ⟩
         cong (f (_≃_.to eq₂))
           (apply-ext (good-ext ext₂) λ b →
            trans (cong (_≃_.from eq₁) $ sym $
                   _≃_.right-inverse-of eq₂ b) $
            trans (cong (_≃_.from eq₁) $ cong (_$ _≃_.from eq₂ b) $ sym $
                   refl (_≃_.to eq₂)) $
            _≃_.left-inverse-of eq₁ (_≃_.from eq₂ b))                      ≡⟨ sym $ cong₂-reflˡ _ ⟩∎

         cong₂ f
           (refl _)
           (apply-ext (good-ext ext₂) λ b →
            trans (cong (_≃_.from eq₁) $ sym $
                   _≃_.right-inverse-of eq₂ b) $
            trans (cong (_≃_.from eq₁) $ cong (_$ _≃_.from eq₂ b) $ sym $
                   refl (_≃_.to eq₂)) $
            _≃_.left-inverse-of eq₁ (_≃_.from eq₂ b))                      ∎)
      eq
      _

-- _≃_ comes with a groupoid structure (assuming extensionality).

groupoid : ∀ {ℓ} → Extensionality ℓ ℓ → Groupoid (lsuc ℓ) ℓ
groupoid {ℓ} ext = record
  { Object         = Type ℓ
  ; _∼_            = _≃_
  ; id             = id
  ; _∘_            = _∘_
  ; _⁻¹            = inverse
  ; left-identity  = left-identity
  ; right-identity = right-identity
  ; assoc          = assoc
  ; left-inverse   = left-inverse
  ; right-inverse  = right-inverse
  }
  where
  abstract
    left-identity : {X Y : Type ℓ} (p : X ≃ Y) → id ∘ p ≡ p
    left-identity _ = lift-equality ext (refl _)

    right-identity : {X Y : Type ℓ} (p : X ≃ Y) → p ∘ id ≡ p
    right-identity _ = lift-equality ext (refl _)

    assoc : {W X Y Z : Type ℓ} (p : Y ≃ Z) (q : X ≃ Y) (r : W ≃ X) →
            p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
    assoc _ _ _ = lift-equality ext (refl _)

    left-inverse : {X Y : Type ℓ} (p : X ≃ Y) → inverse p ∘ p ≡ id
    left-inverse p =
      lift-equality ext (apply-ext ext $ _≃_.left-inverse-of p)

    right-inverse : {X Y : Type ℓ} (p : X ≃ Y) → p ∘ inverse p ≡ id
    right-inverse p =
      lift-equality ext (apply-ext ext $ _≃_.right-inverse-of p)

-- Inverse is involutive (assuming extensionality).
--
-- This property is more general than
-- Groupoid.involutive (groupoid …), because A and B do not have to
-- have the same size.

inverse-involutive :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  (p : A ≃ B) →
  inverse (inverse p) ≡ p
inverse-involutive ext p = lift-equality ext (refl _)

-- Inverse is a logical equivalence.

inverse-logical-equivalence :
  ∀ {a b} {A : Type a} {B : Type b} →
  A ≃ B ⇔ B ≃ A
inverse-logical-equivalence = record
  { to   = inverse
  ; from = inverse
  }

-- Inverse is an isomorphism (assuming extensionality).
--
-- This property is more general than
-- Groupoid.⁻¹-bijection (groupoid …), because A and B do not have to
-- have the same size.

inverse-isomorphism :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  A ≃ B ↔ B ≃ A
inverse-isomorphism ext = record
  { surjection = record
    { logical-equivalence = inverse-logical-equivalence
    ; right-inverse-of    = inverse-involutive ext
    }
  ; left-inverse-of = inverse-involutive ext
  }

------------------------------------------------------------------------
-- A surjection from A ↔ B to A ≃ B, and related results

private
 abstract

  -- ↔⇒≃ is a left inverse of _≃_.bijection (assuming extensionality).

  ↔⇒≃-left-inverse :
    ∀ {a b} {A : Type a} {B : Type b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    (A≃B : A ≃ B) →
    ↔⇒≃ (_≃_.bijection A≃B) ≡ A≃B
  ↔⇒≃-left-inverse ext _ = lift-equality ext (refl _)

  -- When sets are used ↔⇒≃ is a right inverse of _≃_.bijection
  -- (assuming extensionality).

  ↔⇒≃-right-inverse :
    ∀ {a b} {A : Type a} {B : Type b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    Is-set A → (A↔B : A ↔ B) →
    _≃_.bijection (↔⇒≃ A↔B) ≡ A↔B
  ↔⇒≃-right-inverse {a} {b} {B = B} ext A-set A↔B =
    cong₂ (λ l r → record
             { surjection = record
               { logical-equivalence = _↔_.logical-equivalence A↔B
               ; right-inverse-of    = r
               }
             ; left-inverse-of = l
             })
          (apply-ext (lower-extensionality b b ext) λ _ → A-set _ _)
          (apply-ext (lower-extensionality a a ext) λ _ → B-set _ _)
    where
    B-set : Is-set B
    B-set = respects-surjection (_↔_.surjection A↔B) 2 A-set

-- There is a surjection from A ↔ B to A ≃ B (assuming
-- extensionality).

↔↠≃ :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  (A ↔ B) ↠ (A ≃ B)
↔↠≃ ext = record
  { logical-equivalence = ↔⇔≃
  ; right-inverse-of    = ↔⇒≃-left-inverse ext
  }

-- When A is a set A ↔ B and A ≃ B are isomorphic (assuming
-- extensionality).

↔↔≃ :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-set A → (A ↔ B) ↔ (A ≃ B)
↔↔≃ ext A-set = record
  { surjection      = ↔↠≃ ext
  ; left-inverse-of = ↔⇒≃-right-inverse ext A-set
  }

-- When B is a set A ↔ B and A ≃ B are isomorphic (assuming
-- extensionality).

↔↔≃′ :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-set B → (A ↔ B) ↔ (A ≃ B)
↔↔≃′ ext B-set = record
  { surjection      = ↔↠≃ ext
  ; left-inverse-of = λ A↔B →
      ↔⇒≃-right-inverse
        ext
        (H-level.respects-surjection
           (_↔_.surjection $ Bijection.inverse A↔B) 2 B-set)
        A↔B
  }

-- For propositional types there is a split surjection from
-- equivalence to logical equivalence.

≃↠⇔ : ∀ {a b} {A : Type a} {B : Type b} →
      Is-proposition A → Is-proposition B → (A ≃ B) ↠ (A ⇔ B)
≃↠⇔ {A = A} {B} A-prop B-prop = record
  { logical-equivalence = record
    { to   = _≃_.logical-equivalence
    ; from = ⇔→≃
    }
  ; right-inverse-of = refl
  }
  where
  ⇔→≃ : A ⇔ B → A ≃ B
  ⇔→≃ A⇔B = ↔⇒≃ record
    { surjection = record
      { logical-equivalence = A⇔B
      ; right-inverse-of    = to∘from
      }
    ; left-inverse-of = from∘to
    }
    where
    open _⇔_ A⇔B

    abstract

      to∘from : ∀ x → to (from x) ≡ x
      to∘from _ = B-prop _ _

      from∘to : ∀ x → from (to x) ≡ x
      from∘to _ = A-prop _ _

-- A corollary.

⇔→≃ :
  ∀ {a b} {A : Type a} {B : Type b} →
  Is-proposition A → Is-proposition B →
  (A → B) → (B → A) →
  A ≃ B
⇔→≃ A-prop B-prop to from =
  _↠_.from (≃↠⇔ A-prop B-prop)
    (record { to = to; from = from })

-- For propositional types logical equivalence is isomorphic to
-- equivalence (assuming extensionality).

⇔↔≃ : ∀ {a b} → Extensionality (a ⊔ b) (a ⊔ b) →
      {A : Type a} {B : Type b} →
      Is-proposition A → Is-proposition B → (A ⇔ B) ↔ (A ≃ B)
⇔↔≃ ext {A} {B} A-prop B-prop = record
  { surjection = record
    { logical-equivalence = L-eq.inverse $ _↠_.logical-equivalence $
                              ≃↠⇔ A-prop B-prop
    ; right-inverse-of    = λ _ → lift-equality ext (refl _)
    }
  ; left-inverse-of = refl
  }

-- If there is a propositional, reflexive relation on A, and related
-- elements are equal, then A is a set, and (assuming extensionality)
-- the relation is equivalent to equality.
--
-- (This is more or less Theorem 7.2.2 from "Homotopy Type Theory:
-- Univalent Foundations of Mathematics" (first edition).)

propositional-identity≃≡ :
  ∀ {a b} {A : Type a}
  (B : A → A → Type b) →
  (∀ x y → Is-proposition (B x y)) →
  (∀ x → B x x) →
  (∀ x y → B x y → x ≡ y) →
  Is-set A ×
  (Extensionality (a ⊔ b) (a ⊔ b) → ∀ {x y} → B x y ≃ (x ≡ y))
propositional-identity≃≡ B B-prop B-refl f =
    A-set
  , λ ext →
      _↔_.to (⇔↔≃ ext (B-prop _ _) A-set)
        (record
           { to   = f _ _
           ; from = λ x≡y → subst (B _) x≡y (B-refl _)
           })
  where
  A-set = propositional-identity⇒set B B-prop B-refl f

------------------------------------------------------------------------
-- Closure, preservation

abstract

  -- All h-levels are closed under the equivalence operator (assuming
  -- extensionality).

  h-level-closure :
    ∀ {a b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    ∀ {A : Type a} {B : Type b} n →
    H-level n A → H-level n B → H-level n (A ≃ B)
  h-level-closure {a} {b} ext {A = A} {B} n hA hB =
    H-level.respects-surjection
      (_↔_.surjection $ Bijection.inverse ≃-as-Σ) n lemma₂
    where
    lemma₁ : ∀ n {to : A → B} →
             H-level n A → H-level n B →
             H-level n (Is-equivalence to)
    lemma₁ zero    cA cB = sometimes-contractible ext cA (mono₁ 0 cB)
    lemma₁ (suc n) _  _  = mono (Nat.m≤m+n 1 n) (propositional ext _)

    lemma₂ : H-level n (∃ λ (to : A → B) → Is-equivalence to)
    lemma₂ = Σ-closure n
              (Π-closure (lower-extensionality b a ext) n (λ _ → hB))
              (λ _ → lemma₁ n hA hB)

  -- For positive h-levels it is enough if one of the sides has the
  -- given h-level.

  left-closure :
    ∀ {a b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    ∀ {A : Type a} {B : Type b} n →
    H-level (1 + n) A → H-level (1 + n) (A ≃ B)
  left-closure ext {A = A} {B} n hA =
    H-level.[inhabited⇒+]⇒+ n λ (A≃B : A ≃ B) →
      h-level-closure ext (1 + n) hA $
        H-level.respects-surjection (_≃_.surjection A≃B) (1 + n) hA

  right-closure :
    ∀ {a b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    ∀ {A : Type a} {B : Type b} n →
    H-level (1 + n) B → H-level (1 + n) (A ≃ B)
  right-closure ext {A = A} {B} n hB =
    H-level.[inhabited⇒+]⇒+ n λ (A≃B : A ≃ B) →
      left-closure ext n $
        H-level.respects-surjection
          (_≃_.surjection (inverse A≃B)) (1 + n) hB

  -- This is not enough for level 0.

  ¬-left-closure :
    ∀ {a b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    ∃ λ (A : Type a) → ∃ λ (B : Type b) →
      Contractible A × Is-proposition B × ¬ Contractible (A ≃ B)
  ¬-left-closure ext =
    ↑ _ ⊤ ,
    ⊥ ,
    ↑-closure 0 ⊤-contractible ,
    ⊥-propositional ,
    λ c → ⊥-elim (_≃_.to (proj₁ c) _)

  ¬-right-closure :
    ∀ {a b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    ∃ λ (A : Type a) → ∃ λ (B : Type b) →
      Is-proposition A × Contractible B × ¬ Contractible (A ≃ B)
  ¬-right-closure ext =
    ⊥ ,
    ↑ _ ⊤ ,
    ⊥-propositional ,
    ↑-closure 0 ⊤-contractible ,
    λ c → ⊥-elim (_≃_.from (proj₁ c) _)

  -- ⊥ ≃ ⊥ is contractible (assuming extensionality).

  ⊥≃⊥-contractible :
    ∀ {ℓ₁ ℓ₂} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Contractible (⊥ {ℓ = ℓ₁} ≃ ⊥ {ℓ = ℓ₂})
  ⊥≃⊥-contractible {ℓ₁} {ℓ₂} ext =
    ↔⇒≃ ⊥↔⊥ , λ ⊥↔⊥′ →
      lift-equality ext $
        apply-ext (lower-extensionality ℓ₂ ℓ₁ ext) λ x → ⊥-elim x
    where
    ⊥↔⊥ : ⊥ {ℓ = ℓ₁} ↔ ⊥ {ℓ = ℓ₂}
    ⊥↔⊥ = record
      { surjection = record
        { logical-equivalence = record
          { to   = ⊥-elim
          ; from = ⊥-elim
          }
        ; right-inverse-of = λ x → ⊥-elim x
        }
      ; left-inverse-of = λ x → ⊥-elim x
      }

-- Equalities are closed, in a strong sense, under applications of
-- equivalences.

≃-≡ : ∀ {a b} {A : Type a} {B : Type b} (A≃B : A ≃ B) {x y : A} →
      let open _≃_ A≃B in
      (to x ≡ to y) ≃ (x ≡ y)
≃-≡ A≃B {x} {y} = ↔⇒≃ record
  { surjection      = surjection′
  ; left-inverse-of = left-inverse-of′
  }
  where
  open _≃_ A≃B

  surjection′ : (to x ≡ to y) ↠ (x ≡ y)
  surjection′ =
    Surjection.↠-≡ $
    _↔_.surjection $
    Bijection.inverse $
    _≃_.bijection A≃B

  abstract
    left-inverse-of′ :
      ∀ p → _↠_.from surjection′ (_↠_.to surjection′ p) ≡ p
    left-inverse-of′ = λ to-x≡to-y →
      cong to (
        trans (sym (left-inverse-of x)) $
        trans (cong from to-x≡to-y) $
        left-inverse-of y)                         ≡⟨ cong-trans to _ _ ⟩
      trans (cong to (sym (left-inverse-of x))) (
        cong to (trans (cong from to-x≡to-y) (
                 left-inverse-of y)))              ≡⟨ cong₂ trans (cong-sym to _) (cong-trans to _ _) ⟩
      trans (sym (cong to (left-inverse-of x))) (
        trans (cong to (cong from to-x≡to-y)) (
        cong to (left-inverse-of y)))              ≡⟨ cong₂ (λ eq₁ eq₂ → trans (sym eq₁) $
                                                                         trans (cong to (cong from to-x≡to-y)) $
                                                                         eq₂)
                                                           (left-right-lemma x)
                                                           (left-right-lemma y) ⟩
      trans (sym (right-inverse-of (to x))) (
        trans (cong to (cong from to-x≡to-y)) (
        right-inverse-of (to y)))                  ≡⟨ _↠_.right-inverse-of (Surjection.↠-≡ $ _≃_.surjection A≃B) to-x≡to-y ⟩∎
      to-x≡to-y                                    ∎

-- A "computation rule" for ≃-≡.

to-≃-≡-refl :
  ∀ {a b} {A : Type a} {B : Type b} (A≃B : A ≃ B) {x : A} →
  _≃_.to (≃-≡ A≃B) (refl (_≃_.to A≃B x)) ≡ refl x
to-≃-≡-refl A≃B =
  Surjection.to-↠-≡-refl
    (_↔_.surjection $ Bijection.inverse $ _≃_.bijection A≃B)

-- ∃ preserves equivalences.

∃-cong :
  ∀ {a b₁ b₂} {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
  (∀ x → B₁ x ≃ B₂ x) → ∃ B₁ ≃ ∃ B₂
∃-cong B₁≃B₂ = ↔⇒≃ (record
  { surjection      = Surjection.∃-cong (_≃_.surjection ⊚ B₁≃B₂)
  ; left-inverse-of = uncurry λ x y →
      cong (_,_ x) (_≃_.left-inverse-of (B₁≃B₂ x) y)
  })

abstract
  private

    -- We can push subst through certain function applications.

    push-subst :
      ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
        (B₁ : A₁ → Type b₁) {B₂ : A₂ → Type b₂}
        {f : A₂ → A₁} {x₁ x₂ : A₂} {y : B₁ (f x₁)}
      (g : ∀ x → B₁ (f x) → B₂ x) (eq : x₁ ≡ x₂) →
      subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ (cong f eq) y)
    push-subst B₁ {B₂} {f} g eq = elim
      (λ {x₁ x₂} eq → ∀ y → subst B₂ eq (g x₁ y) ≡
                            g x₂ (subst B₁ (cong f eq) y))
      (λ x y → subst B₂ (refl x) (g x y)           ≡⟨ subst-refl B₂ _ ⟩
               g x y                               ≡⟨ sym $ cong (g x) $ subst-refl B₁ _ ⟩
               g x (subst B₁ (refl (f x)) y)       ≡⟨ cong (λ eq → g x (subst B₁ eq y)) (sym $ cong-refl f) ⟩∎
               g x (subst B₁ (cong f (refl x)) y)  ∎)
      eq _

    push-subst′ :
      ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
      (A₁≃A₂ : A₁ ≃ A₂) (B₁ : A₁ → Type b₁) (B₂ : A₂ → Type b₂) →
      let open _≃_ A₁≃A₂ in {x₁ x₂ : A₁} {y : B₁ (from (to x₁))}
      (g : ∀ x → B₁ (from (to x)) → B₂ (to x)) (eq : to x₁ ≡ to x₂) →
      subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ (cong from eq) y)
    push-subst′ A₁≃A₂ B₁ B₂ {x₁} {x₂} {y} g eq =
      subst B₂ eq (g x₁ y)                    ≡⟨ cong (subst B₂ eq) $ sym $ g′-lemma _ _ ⟩
      subst B₂ eq (g′ (to x₁) y)              ≡⟨ push-subst B₁ g′ eq ⟩
      g′ (to x₂) (subst B₁ (cong from eq) y)  ≡⟨ g′-lemma _ _ ⟩∎
      g x₂ (subst B₁ (cong from eq) y)        ∎
      where
      open _≃_ A₁≃A₂

      g′ : ∀ x′ → B₁ (from x′) → B₂ x′
      g′ x′ y = subst B₂ (right-inverse-of x′) $
                g (from x′) $
                subst B₁ (sym $ cong from $ right-inverse-of x′) y

      g′-lemma : ∀ x y → g′ (to x) y ≡ g x y
      g′-lemma x y =
        let lemma = λ y →
              let gy = g (from (to x)) $
                         subst B₁
                           (sym $ cong from $ cong to (refl _)) y in
              subst B₂ (cong to (refl _)) gy             ≡⟨ cong (λ p → subst B₂ p gy) $ cong-refl to ⟩
              subst B₂ (refl _) gy                       ≡⟨ subst-refl B₂ gy ⟩
              gy                                         ≡⟨ cong (λ p → g (from (to x)) $ subst B₁ (sym $ cong from p) y) $ cong-refl to ⟩
              g (from (to x))
                (subst B₁ (sym $ cong from (refl _)) y)  ≡⟨ cong (λ p → g (from (to x)) $ subst B₁ (sym p) y) $ cong-refl from ⟩
              g (from (to x))
                (subst B₁ (sym (refl _)) y)              ≡⟨ cong (λ p → g (from (to x)) $ subst B₁ p y) sym-refl ⟩
              g (from (to x)) (subst B₁ (refl _) y)      ≡⟨ cong (g (from (to x))) $ subst-refl B₁ y ⟩∎
              g (from (to x)) y                          ∎
        in
        subst B₂ (right-inverse-of (to x))
          (g (from (to x)) $
           subst B₁ (sym $ cong from $
                       right-inverse-of (to x)) y)  ≡⟨ cong (λ p → subst B₂ p (g (from (to x)) $ subst B₁ (sym $ cong from p) y)) $
                                                         sym $ left-right-lemma x ⟩
        subst B₂ (cong to $ left-inverse-of x)
          (g (from (to x)) $
           subst B₁ (sym $ cong from $ cong to $
                       left-inverse-of x) y)        ≡⟨ elim¹
                                                         (λ {x′} eq →
                                                            (y : B₁ (from (to x′))) →
                                                            subst B₂ (cong to eq)
                                                              (g (from (to x)) $ subst B₁ (sym $ cong from $ cong to eq) y) ≡
                                                            g x′ y)
                                                         lemma
                                                         (left-inverse-of x) y ⟩∎
        g x y                                       ∎

-- If the first component is instantiated to the identity, then the
-- following lemmas state that ∃ preserves injections and bijections.

∃-preserves-injections :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂}
  (A₁≃A₂ : A₁ ≃ A₂) → (∀ x → B₁ x ↣ B₂ (_≃_.to A₁≃A₂ x)) →
  Σ A₁ B₁ ↣ Σ A₂ B₂
∃-preserves-injections {A₁ = A₁} {A₂} {B₁} {B₂} A₁≃A₂ B₁↣B₂ = record
  { to        = to′
  ; injective = injective′
  }
  where
  open _↣_

  to′ : Σ A₁ B₁ → Σ A₂ B₂
  to′ = Σ-map (_≃_.to A₁≃A₂) (_↣_.to (B₁↣B₂ _))

  abstract
    injective′ : Injective to′
    injective′ {x = (x₁ , x₂)} {y = (y₁ , y₂)} =
      _↔_.to Bijection.Σ-≡,≡↔≡ ⊚
      Σ-map (_≃_.injective A₁≃A₂) (λ {eq₁} eq₂ →
        let lemma =
              to (B₁↣B₂ y₁) (subst B₁ (_≃_.injective A₁≃A₂ eq₁) x₂)      ≡⟨ refl _ ⟩
              to (B₁↣B₂ y₁)
                (subst B₁ (trans (sym (_≃_.left-inverse-of A₁≃A₂ x₁)) $
                           trans (cong (_≃_.from A₁≃A₂) eq₁)
                                 (_≃_.left-inverse-of A₁≃A₂ y₁))
                          x₂)                                            ≡⟨ cong (to (B₁↣B₂ y₁)) $ sym $ subst-subst B₁ _ _ _ ⟩
              to (B₁↣B₂ y₁)
                 (subst B₁ (trans (cong (_≃_.from A₁≃A₂) eq₁)
                                  (_≃_.left-inverse-of A₁≃A₂ y₁)) $
                  subst B₁ (sym (_≃_.left-inverse-of A₁≃A₂ x₁))
                           x₂)                                           ≡⟨ cong (to (B₁↣B₂ y₁)) $ sym $ subst-subst B₁ _ _ _ ⟩
              to (B₁↣B₂ y₁)
                 (subst B₁ (_≃_.left-inverse-of A₁≃A₂ y₁) $
                  subst B₁ (cong (_≃_.from A₁≃A₂) eq₁) $
                  subst B₁ (sym (_≃_.left-inverse-of A₁≃A₂ x₁)) x₂)      ≡⟨ sym $ push-subst′ A₁≃A₂ B₁ B₂
                                                                              (λ x y → to (B₁↣B₂ x)
                                                                                          (subst B₁ (_≃_.left-inverse-of A₁≃A₂ x) y))
                                                                              eq₁ ⟩
              subst B₂ eq₁
                (to (B₁↣B₂ x₁) $
                 subst B₁ (_≃_.left-inverse-of A₁≃A₂ x₁) $
                 subst B₁ (sym (_≃_.left-inverse-of A₁≃A₂ x₁)) x₂)       ≡⟨ cong (subst B₂ eq₁ ⊚ to (B₁↣B₂ x₁)) $ subst-subst B₁ _ _ _ ⟩
              subst B₂ eq₁
                (to (B₁↣B₂ x₁) $
                 subst B₁ (trans (sym (_≃_.left-inverse-of A₁≃A₂ x₁))
                                 (_≃_.left-inverse-of A₁≃A₂ x₁))
                          x₂)                                            ≡⟨ cong (λ p → subst B₂ eq₁ (to (B₁↣B₂ x₁) (subst B₁ p x₂))) $
                                                                                 trans-symˡ _ ⟩
              subst B₂ eq₁ (to (B₁↣B₂ x₁) $ subst B₁ (refl _) x₂)        ≡⟨ cong (subst B₂ eq₁ ⊚ to (B₁↣B₂ x₁)) $
                                                                                 subst-refl B₁ x₂ ⟩
              subst B₂ eq₁ (to (B₁↣B₂ x₁) x₂)                            ≡⟨ eq₂ ⟩∎
              to (B₁↣B₂ y₁) y₂                                           ∎
        in
        subst B₁ (_≃_.injective A₁≃A₂ eq₁) x₂  ≡⟨ _↣_.injective (B₁↣B₂ y₁) lemma ⟩∎
        y₂                                     ∎) ⊚
      Σ-≡,≡←≡

∃-preserves-bijections :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂}
  (A₁≃A₂ : A₁ ≃ A₂) → (∀ x → B₁ x ↔ B₂ (_≃_.to A₁≃A₂ x)) →
  Σ A₁ B₁ ↔ Σ A₂ B₂
∃-preserves-bijections {A₁ = A₁} {A₂} {B₁} {B₂} A₁≃A₂ B₁↔B₂ = record
  { surjection      = surjection′
  ; left-inverse-of = left-inverse-of′
  }
  where
  open _↔_

  surjection′ : Σ A₁ B₁ ↠ Σ A₂ B₂
  surjection′ =
    Surjection.Σ-cong (_≃_.surjection A₁≃A₂) (surjection ⊚ B₁↔B₂)

  abstract
    left-inverse-of′ :
      ∀ p → _↠_.from surjection′ (_↠_.to surjection′ p) ≡ p
    left-inverse-of′ = λ p → Σ-≡,≡→≡
      (_≃_.left-inverse-of A₁≃A₂ (proj₁ p))
      (subst B₁ (_≃_.left-inverse-of A₁≃A₂ (proj₁ p))
         (from (B₁↔B₂ _)
            (subst B₂ (sym (_≃_.right-inverse-of A₁≃A₂
                              (_≃_.to A₁≃A₂ (proj₁ p))))
               (to (B₁↔B₂ _) (proj₂ p))))                        ≡⟨ push-subst B₂ (λ x → from (B₁↔B₂ x))
                                                                      (_≃_.left-inverse-of A₁≃A₂ (proj₁ p)) ⟩
       from (B₁↔B₂ _)
         (subst B₂ (cong (_≃_.to A₁≃A₂)
                         (_≃_.left-inverse-of A₁≃A₂ (proj₁ p)))
            (subst B₂ (sym (_≃_.right-inverse-of A₁≃A₂
                              (_≃_.to A₁≃A₂ (proj₁ p))))
               (to (B₁↔B₂ _) (proj₂ p))))                        ≡⟨ cong (λ eq → from (B₁↔B₂ _)
                                                                                   (subst B₂ eq
                                                                                      (subst B₂ (sym (_≃_.right-inverse-of A₁≃A₂ _))
                                                                                         (to (B₁↔B₂ _) (proj₂ p))))) $
                                                                         _≃_.left-right-lemma A₁≃A₂ _ ⟩
       from (B₁↔B₂ _)
         (subst B₂ (_≃_.right-inverse-of A₁≃A₂
                      (_≃_.to A₁≃A₂ (proj₁ p)))
            (subst B₂ (sym (_≃_.right-inverse-of A₁≃A₂
                              (_≃_.to A₁≃A₂ (proj₁ p))))
               (to (B₁↔B₂ _) (proj₂ p))))                        ≡⟨ cong (from (B₁↔B₂ _)) $ subst-subst-sym B₂ _ _ ⟩
       from (B₁↔B₂ _) (to (B₁↔B₂ _) (proj₂ p))                   ≡⟨ left-inverse-of (B₁↔B₂ _) _ ⟩∎
       proj₂ p                                                   ∎)

-- Σ preserves equivalence.

Σ-preserves : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
                {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂}
              (A₁≃A₂ : A₁ ≃ A₂) → (∀ x → B₁ x ≃ B₂ (_≃_.to A₁≃A₂ x)) →
              Σ A₁ B₁ ≃ Σ A₂ B₂
Σ-preserves A₁≃A₂ B₁≃B₂ = ↔⇒≃ $
  ∃-preserves-bijections A₁≃A₂ (_≃_.bijection ⊚ B₁≃B₂)

-- A part of the implementation of ≃-preserves (see below) that does
-- not depend on extensionality.

≃-preserves-⇔ :
  ∀ {a₁ a₂ b₁ b₂}
    {A₁ : Type a₁} {A₂ : Type a₂} {B₁ : Type b₁} {B₂ : Type b₂} →
  A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ ≃ B₁) ⇔ (A₂ ≃ B₂)
≃-preserves-⇔ A₁≃A₂ B₁≃B₂ = record
  { to   = λ A₁≃B₁ → B₁≃B₂ ∘ A₁≃B₁ ∘ inverse A₁≃A₂
  ; from = λ A₂≃B₂ → inverse B₁≃B₂ ∘ A₂≃B₂ ∘ A₁≃A₂
  }

-- Equivalence preserves equivalences (assuming extensionality).

≃-preserves :
  ∀ {a₁ a₂ b₁ b₂} →
  Extensionality (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂) (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂) →
  {A₁ : Type a₁} {A₂ : Type a₂} {B₁ : Type b₁} {B₂ : Type b₂} →
  A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ ≃ B₁) ≃ (A₂ ≃ B₂)
≃-preserves {a₁} {a₂} {b₁} {b₂} ext {A₁} {A₂} {B₁} {B₂} A₁≃A₂ B₁≃B₂ =
  ↔⇒≃ (record
    { surjection = record
      { logical-equivalence = ≃-preserves-⇔ A₁≃A₂ B₁≃B₂
      ; right-inverse-of    = to∘from
      }
    ; left-inverse-of = from∘to
    })
  where
  open _≃_

  ext₁ = lower-extensionality (a₁ ⊔ b₁) (a₁ ⊔ b₁) ext
  ext₂ = lower-extensionality (a₂ ⊔ b₂) (a₂ ⊔ b₂) ext

  abstract
    to∘from :
      (A₂≃B₂ : A₂ ≃ B₂) →
      B₁≃B₂ ∘ (inverse B₁≃B₂ ∘ A₂≃B₂ ∘ A₁≃A₂) ∘ inverse A₁≃A₂ ≡ A₂≃B₂
    to∘from A₂≃B₂ =
      lift-equality ext₁ $
      apply-ext (lower-extensionality b₂ a₂ ext₁) λ x →
        to B₁≃B₂ (from B₁≃B₂ (to A₂≃B₂ (to A₁≃A₂ (from A₁≃A₂ x))))  ≡⟨ right-inverse-of B₁≃B₂ _ ⟩
        to A₂≃B₂ (to A₁≃A₂ (from A₁≃A₂ x))                          ≡⟨ cong (to A₂≃B₂) $ right-inverse-of A₁≃A₂ _ ⟩∎
        to A₂≃B₂ x                                                  ∎

    from∘to :
      (A₁≃B₁ : A₁ ≃ B₁) →
      inverse B₁≃B₂ ∘ (B₁≃B₂ ∘ A₁≃B₁ ∘ inverse A₁≃A₂) ∘ A₁≃A₂ ≡ A₁≃B₁
    from∘to A₁≃B₁ =
      lift-equality ext₂ $
      apply-ext (lower-extensionality b₁ a₁ ext₂) λ x →
        from B₁≃B₂ (to B₁≃B₂ (to A₁≃B₁ (from A₁≃A₂ (to A₁≃A₂ x))))  ≡⟨ left-inverse-of B₁≃B₂ _ ⟩
        to A₁≃B₁ (from A₁≃A₂ (to A₁≃A₂ x))                          ≡⟨ cong (to A₁≃B₁) $ left-inverse-of A₁≃A₂ _ ⟩∎
        to A₁≃B₁ x                                                  ∎

-- Equivalence preserves bijections (assuming extensionality).

≃-preserves-bijections :
  ∀ {a₁ a₂ b₁ b₂} →
  Extensionality (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂) (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂) →
  {A₁ : Type a₁} {A₂ : Type a₂} {B₁ : Type b₁} {B₂ : Type b₂} →
  A₁ ↔ A₂ → B₁ ↔ B₂ → (A₁ ≃ B₁) ↔ (A₂ ≃ B₂)
≃-preserves-bijections ext A₁↔A₂ B₁↔B₂ =
  _≃_.bijection $ ≃-preserves ext (↔⇒≃ A₁↔A₂) (↔⇒≃ B₁↔B₂)

------------------------------------------------------------------------
-- More lemmas

abstract

  -- As a consequence of extensionality-isomorphism and ≃-≡ we get a
  -- strengthening of W-≡,≡↠≡.

  W-≡,≡≃≡ : ∀ {a b} {A : Type a} {B : A → Type b} →
            Extensionality b (a ⊔ b) →
            ∀ {x y} {f : B x → W A B} {g : B y → W A B} →
            (∃ λ (p : x ≡ y) → ∀ i → f i ≡ g (subst B p i)) ≃
            (sup x f ≡ sup y g)
  W-≡,≡≃≡ {a} {A = A} {B} ext {x} {y} {f} {g} =
    (∃ λ p → ∀ i → f i ≡ g (subst B p i))        ≃⟨ Σ-preserves id lemma ⟩
    (∃ λ p → subst (λ x → B x → W A B) p f ≡ g)  ≃⟨ ↔⇒≃ Bijection.Σ-≡,≡↔≡ ⟩
    ((x , f) ≡ (y , g))                          ≃⟨ ≃-≡ (↔⇒≃ W-unfolding) ⟩□
    (sup x f ≡ sup y g)                          □
    where
    lemma : (p : x ≡ y) →
            (∀ i → f i ≡ g (subst B p i)) ≃
            (subst (λ x → B x → W A B) p f ≡ g)
    lemma p = elim
      (λ {x y} p → (f : B x → W A B) (g : B y → W A B) →
                   (∀ i → f i ≡ g (subst B p i)) ≃
                   (subst (λ x → B x → W A B) p f ≡ g))
      (λ x f g →
         (∀ i → f i ≡ g (subst B (refl x) i))        ≃⟨ subst (λ h → (∀ i → f i ≡ g (h i)) ≃ (∀ i → f i ≡ g i))
                                                              (sym (apply-ext (lower-extensionality lzero a ext) (subst-refl B)))
                                                              id ⟩
         (∀ i → f i ≡ g i)                           ≃⟨ extensionality-isomorphism ext ⟩
         (f ≡ g)                                     ≃⟨ subst (λ h → (f ≡ g) ≃ (h ≡ g))
                                                              (sym $ subst-refl (λ x' → B x' → W A B) f)
                                                              id ⟩□
         (subst (λ x → B x → W A B) (refl x) f ≡ g)  □)
      p f g

  -- Some rearrangement lemmas.

  to-subst :
    ∀ {a p q} {A : Type a} {P : A → Type p} {Q : A → Type q}
      {x y : A} {eq : x ≡ y} {f : P x ≃ Q x} →
    _≃_.to (subst (λ x → P x ≃ Q x) eq f) ≡
    subst (λ x → P x → Q x) eq (_≃_.to f)
  to-subst {P = P} {Q = Q} {eq = eq} {f = f} = elim¹
    (λ eq →
       _≃_.to (subst (λ x → P x ≃ Q x) eq f) ≡
       subst (λ x → P x → Q x) eq (_≃_.to f))
    (_≃_.to (subst (λ x → P x ≃ Q x) (refl _) f)  ≡⟨ cong _≃_.to $ subst-refl (λ _ → _ ≃ _) _ ⟩
     _≃_.to f                                     ≡⟨ sym $ subst-refl _ _ ⟩∎
     subst (λ x → P x → Q x) (refl _) (_≃_.to f)  ∎)
    eq

  from-subst :
    ∀ {a p q} {A : Type a} {P : A → Type p} {Q : A → Type q}
      {x y : A} {eq : x ≡ y} {f : P x ≃ Q x} →
    _≃_.from (subst (λ x → P x ≃ Q x) eq f) ≡
    subst (λ x → Q x → P x) eq (_≃_.from f)
  from-subst {P = P} {Q = Q} {eq = eq} {f = f} = elim¹
    (λ eq →
       _≃_.from (subst (λ x → P x ≃ Q x) eq f) ≡
       subst (λ x → Q x → P x) eq (_≃_.from f))
    (_≃_.from (subst (λ x → P x ≃ Q x) (refl _) f)  ≡⟨ cong _≃_.from $ subst-refl (λ _ → _ ≃ _) _ ⟩
     _≃_.from f                                     ≡⟨ sym $ subst-refl _ _ ⟩∎
     subst (λ x → Q x → P x) (refl _) (_≃_.from f)  ∎)
    eq

-- If P is pointwise equivalent to x ≡_, then every function of type
-- {y : A} → x ≡ y → P y is an equivalence (pointwise).
--
-- Andrea Vezzosi showed me a similar result, that he thought that
-- Thierry Coquand had informed him about.

≡≃→≡→→Is-equivalence :
  ∀ {a p} {A : Type a} {x : A}
  (P : A → Type p) →
  ({y : A} → (x ≡ y) ≃ P y) →
  (f : {y : A} → x ≡ y → P y) →
  {y : A} → Is-equivalence (f {y = y})
≡≃→≡→→Is-equivalence {x = x} P ≡≃P f {y = y} =
  drop-Σ-map-id f equiv₂ y
  where
  equiv₁ : (∃ λ y → x ≡ y) ≃ ∃ P
  equiv₁ = ∃-cong λ _ → ≡≃P

  contr : Contractible (∃ P)
  contr =
    H-level.respects-surjection
      (_≃_.surjection equiv₁)
      0
      (other-singleton-contractible _)

  equiv₂ : Is-equivalence (Σ-map P.id f)
  equiv₂ =
    _≃_.is-equivalence $
    with-other-function
      equiv₁
      _
      (λ _ → mono₁ 0 contr _ _)
