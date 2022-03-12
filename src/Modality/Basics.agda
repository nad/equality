------------------------------------------------------------------------
-- Idempotent monadic modalities
------------------------------------------------------------------------

-- Unless otherwise noted this code is based on "Modalities in
-- Homotopy Type Theory" by Rijke, Shulman and Spitters, and/or (some
-- version of) the corresponding Coq code. (Details may differ, and
-- perhaps there are some "obvious" results that do not have direct
-- counterparts in the work of Rijke, Shulman and Spitters, even
-- though there is no note about this.)

-- The definitions in this module are reexported from Modality.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Modality.Basics
  {c⁺} (eq-J : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq-J

open import Erased.Basics as E using (Erased)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Accessibility eq-J as A using (Acc; Well-founded; _<W_)
open import Bijection eq-J as Bijection using (_↔_; Has-quasi-inverse)
open import Embedding eq-J as Emb using (Embedding; Is-embedding)
open import Equality.Decision-procedures eq-J
open import Equivalence eq-J as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased.Basics eq-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages.Basics eq-J
  using (Contractibleᴱ; _⁻¹ᴱ_)
import Equivalence.Half-adjoint eq-J as HA
open import Equivalence.List eq-J
open import Equivalence.Path-split eq-J as PS
  using (_-Null_; Is-∞-extendable-along-[_])
open import Erased.Box-cong-axiomatisation eq-J
  using ([]-cong-axiomatisation)
open import Extensionality eq-J
open import For-iterated-equality eq-J
open import Function-universe eq-J as F hiding (id; _∘_)
open import H-level eq-J as H-level
open import H-level.Closure eq-J
open import Preimage eq-J as Preimage using (_⁻¹_)
open import Surjection eq-J using (_↠_; Split-surjective)
open import Univalence-axiom eq-J
open import Vec.Dependent eq-J as Vec using (Vec)

private
  variable
    a c d                                    : Level
    A B B₁ B₂ C                              : Type a
    eq f g i k m m₁ m₂ n p s x y z z₁ z₂ _<_ : A
    P Q                                      : A → Type p

------------------------------------------------------------------------
-- Modalities

private
 module Dummy where

  -- The following is a definition of "modality" based on that in (one
  -- version of) the Coq code accompanying "Modalities in Homotopy
  -- Type Theory".
  --
  -- One difference is that in the Coq code the proof showing that the
  -- modality predicate is propositional is allowed to make use of
  -- function extensionality for arbitrary universe levels.

  record Modality-record a : Type (lsuc a) where
    field
      -- The modal operator.
      ◯ : Type a → Type a

      -- The modal unit.
      η : A → ◯ A

      -- A type A is modal if Modal A is inhabited.
      Modal : Type a → Type a

      -- Modal A is propositional (assuming function extensionality).
      Modal-propositional :
        Extensionality a a →
        Is-proposition (Modal A)

      -- ◯ A is modal.
      Modal-◯ : Modal (◯ A)

      -- Modal respects equivalences.
      Modal-respects-≃ : A ≃ B → Modal A → Modal B

      -- Pointwise modal families of type ◯ A → Type a are
      -- ∞-extendable along η.
      extendable-along-η :
        {P : ◯ A → Type a} →
        (∀ x → Modal (P x)) →
        Is-∞-extendable-along-[ η ] P

open Dummy public
  using (module Modality-record)
  renaming (Modality-record to Modality)

------------------------------------------------------------------------
-- Uniquely eliminating modalities

-- The following is a definition of "uniquely eliminating modality"
-- based on that in "Modalities in Homotopy Type Theory".

record Uniquely-eliminating-modality a : Type (lsuc a) where
  field
    ◯                    : Type a → Type a
    η                    : A → ◯ A
    uniquely-eliminating :
      Is-equivalence (λ (f : (x : ◯ A) → ◯ (P x)) → f ∘ η)

  ----------------------------------------------------------------------
  -- Some definitions and lemmas

  -- A type is modal if η is an equivalence for this type.

  Modal : Type a → Type a
  Modal A = Is-equivalence (η {A = A})

  -- If A is modal, then A is equivalent to ◯ A.

  Modal→≃◯ : Modal A → A ≃ ◯ A
  Modal→≃◯ m = Eq.⟨ _ , m ⟩

  -- The type (x : ◯ A) → ◯ (P x) is equivalent to
  -- (x : A) → ◯ (P (η x)).

  Π◯◯≃Π◯η : ((x : ◯ A) → ◯ (P x)) ≃ ((x : A) → ◯ (P (η x)))
  Π◯◯≃Π◯η = Eq.⟨ _ , uniquely-eliminating ⟩

  -- A type is stable if ◯ A implies A.

  Stable : Type a → Type a
  Stable A = ◯ A → A

  -- If A is stable, and the stability proof is a left inverse of η,
  -- then A is modal.

  Stable→left-inverse→Modal :
    (s : Stable A) → s ∘ η ≡ id → Modal A
  Stable→left-inverse→Modal {A = A} s s-η =
    _≃_.is-equivalence $
    Eq.↔→≃ η s
      (λ x → cong (_$ x) η-s)
      (λ x → cong (_$ x) s-η)
    where
    contr : Contractible ((λ (f : ◯ A → ◯ A) → f ∘ η) ⁻¹ η)
    contr = Preimage.bijection⁻¹-contractible (_≃_.bijection Π◯◯≃Π◯η) _

    η-s : η ∘ s ≡ id
    η-s =
      η ∘ s               ≡⟨ cong proj₁ $ sym $ contr .proj₂ (η ∘ s , (

        η ∘ s ∘ η              ≡⟨ cong (η ∘_) s-η ⟩
        η ∘ id                 ≡⟨⟩
        η                      ∎)) ⟩

      _≃_.from Π◯◯≃Π◯η η  ≡⟨ cong proj₁ $ contr .proj₂ (id , refl η) ⟩∎
      id                  ∎

  -- The type ◯ A is modal.

  Modal-◯ : Modal (◯ A)
  Modal-◯ {A = A} = Stable→left-inverse→Modal η⁻¹ η⁻¹-η
    where
    η⁻¹ : ◯ (◯ A) → ◯ A
    η⁻¹ = _≃_.from Π◯◯≃Π◯η id

    η⁻¹-η : η⁻¹ ∘ η ≡ id
    η⁻¹-η =
      _≃_.from Π◯◯≃Π◯η id ∘ η       ≡⟨⟩
      (_∘ η) (_≃_.from Π◯◯≃Π◯η id)  ≡⟨ _≃_.right-inverse-of Π◯◯≃Π◯η _ ⟩∎
      id                            ∎

  -- If P : ◯ A → Type a is pointwise modal, then it is ∞-extendable
  -- along η (assuming function extensionality).

  extendable-along-η :
    {P : ◯ A → Type a} →
    Extensionality a a →
    (∀ x → Modal (P x)) →
    Is-∞-extendable-along-[ η ] P
  extendable-along-η {A = A} {P = P} ext m =          $⟨ equiv ⟩
    Is-equivalence (λ (f : (x : ◯ A) → P x) → f ∘ η)  ↝⟨ inverse $ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩□
    Is-∞-extendable-along-[ η ] P                     □
    where
    equiv : Is-equivalence (λ (f : (x : ◯ A) → P x) → f ∘ η)
    equiv =
      _≃_.is-equivalence $
      Eq.with-other-function
        (((x : ◯ A) → P x)        ↝⟨ ∀-cong ext (Modal→≃◯ ∘ m) ⟩
         ((x : ◯ A) → ◯ (P x))    ↝⟨ Π◯◯≃Π◯η ⟩
         ((x : A) → ◯ (P (η x)))  ↝⟨ ∀-cong ext (inverse ∘ Modal→≃◯ ∘ m ∘ η) ⟩□
         ((x : A) → P (η x))      □)
        (_∘ η)
        (λ f → apply-ext ext λ x →
           _≃_.from (Modal→≃◯ (m (η x))) (η (f (η x)))  ≡⟨ _≃_.left-inverse-of (Modal→≃◯ (m (η x))) _ ⟩∎
           f (η x)                                      ∎)

  ----------------------------------------------------------------------
  -- Eliminators

  -- A dependent eliminator for ◯.

  ◯-elim :
    {P : ◯ A → Type a} →
    (∀ x → Modal (P x)) →
    ((x : A) → P (η x)) →
    ((x : ◯ A) → P x)
  ◯-elim {A = A} {P = P} m =
    ((x : A) → P (η x))      →⟨ η ∘_ ⟩
    ((x : A) → ◯ (P (η x)))  ↔⟨ inverse Π◯◯≃Π◯η ⟩
    ((x : ◯ A) → ◯ (P x))    →⟨ _≃_.from (Modal→≃◯ (m _)) ∘_ ⟩□
    ((x : ◯ A) → P x)        □

  -- A "computation rule" for ◯-elim.

  ◯-elim-η :
    {P : ◯ A → Type a} {f : (x : A) → P (η x)}
    (m : ∀ x → Modal (P x)) →
    ◯-elim m f (η x) ≡ f x
  ◯-elim-η {x = x} {P = P} {f = f} m =
    _≃_.from (Modal→≃◯ (m _))
      (_≃_.from (Π◯◯≃Π◯η {P = P}) (η ∘ f) (η x))         ≡⟨⟩

    _≃_.from (Modal→≃◯ (m _))
      (((_∘ η) (_≃_.from (Π◯◯≃Π◯η {P = P}) (η ∘ f))) x)  ≡⟨ cong (_≃_.from (Modal→≃◯ (m _))) $ cong (_$ x) $
                                                            _≃_.right-inverse-of Π◯◯≃Π◯η _ ⟩

    _≃_.from (Modal→≃◯ (m _)) (η (f x))                  ≡⟨ _≃_.left-inverse-of (Modal→≃◯ (m _)) _ ⟩∎

    f x                                                  ∎

  -- A non-dependent eliminator for ◯.

  ◯-rec : Modal B → (A → B) → (◯ A → B)
  ◯-rec m = ◯-elim (λ _ → m)

  -- A "computation rule" for ◯-rec.

  ◯-rec-η : ∀ m → ◯-rec m f (η x) ≡ f x
  ◯-rec-η m = ◯-elim-η (λ _ → m)

  ----------------------------------------------------------------------
  -- More lemmas

  -- A map function for ◯.

  ◯-map : (A → B) → ◯ A → ◯ B
  ◯-map f = ◯-rec Modal-◯ (η ∘ f)

  -- A "computation rule" for ◯-map.

  ◯-map-η : ◯-map f (η x) ≡ η (f x)
  ◯-map-η = ◯-rec-η Modal-◯

  -- Modal respects equivalences (assuming function extensionality).

  Modal-respects-≃ :
    Extensionality a a →
    A ≃ B → Modal A → Modal B
  Modal-respects-≃ {A = A} {B = B} ext A≃B m =
    Stable→left-inverse→Modal
      (◯ B  →⟨ ◯-map (_≃_.from A≃B) ⟩
       ◯ A  →⟨ _≃_.from $ Modal→≃◯ m ⟩
       A    →⟨ _≃_.to A≃B ⟩□
       B    □)
      (apply-ext ext λ x →

       _≃_.to A≃B (_≃_.from (Modal→≃◯ m) (◯-map (_≃_.from A≃B) (η x)))  ≡⟨ cong (_≃_.to A≃B ∘ _≃_.from (Modal→≃◯ m)) ◯-map-η ⟩
       _≃_.to A≃B (_≃_.from (Modal→≃◯ m) (η (_≃_.from A≃B x)))          ≡⟨ cong (_≃_.to A≃B) $ _≃_.left-inverse-of (Modal→≃◯ m) _ ⟩
       _≃_.to A≃B (_≃_.from A≃B x)                                      ≡⟨ _≃_.right-inverse-of A≃B _ ⟩∎
       x                                                                ∎)

  -- A uniquely eliminating modality is a modality (assuming function
  -- extensionality).
  --
  -- See also Modality.uniquely-eliminating below.

  modality :
    Extensionality a a →
    Modality a
  modality ext = λ where
    .Modality-record.◯ → ◯

    .Modality-record.η → η

    .Modality-record.Modal → Modal

    .Modality-record.Modal-propositional →
      Is-equivalence-propositional

    .Modality-record.Modal-◯ → Modal-◯

    .Modality-record.Modal-respects-≃ → Modal-respects-≃ ext

    .Modality-record.extendable-along-η → extendable-along-η ext

------------------------------------------------------------------------
-- Σ-closed reflective subuniverses

-- The Coq code accompanying "Modalities in Homotopy Type Theory" uses
-- a somewhat different definition of reflective subuniverses than the
-- paper:
-- * The definition has been adapted to Coq's notion of universe
--   polymorphism.
-- * The proof showing that the modality predicate is propositional is
--   allowed to make use of function extensionality for arbitrary
--   universe levels.
-- * One extra property is assumed: if A and B are equivalent and A is
--   modal, then B is modal.
-- * The property stating that λ (f : ◯ A → B) → f ∘ η is an
--   equivalence for all types A and modal types B is replaced by a
--   property that is intended to avoid uses of extensionality. This
--   property is stated using Is-∞-extendable-along-[_].
-- (This refers to one version of the code, which seems to have
-- changed since I first looked at it.)
--
-- Here is a definition of Σ-closed reflective subuniverses that is
-- based on the definition of reflective subuniverses in (one version
-- of) the Coq code of Rijke et al. Note that Modal-propositional is
-- only given access to function extensionality for a given universe
-- level.

record Σ-closed-reflective-subuniverse a : Type (lsuc a) where
  field
    ◯     : Type a → Type a
    η     : A → ◯ A
    Modal : Type a → Type a

    Modal-propositional :
      Extensionality a a →
      Is-proposition (Modal A)

    Modal-◯ : Modal (◯ A)

    Modal-respects-≃ : A ≃ B → Modal A → Modal B

    extendable-along-η :
      Modal B → Is-∞-extendable-along-[ η ] (λ (_ : ◯ A) → B)

    Σ-closed : Modal A → (∀ x → Modal (P x)) → Modal (Σ A P)

  ----------------------------------------------------------------------
  -- Eliminators

  -- A non-dependent eliminator for ◯.

  ◯-rec : Modal B → (A → B) → (◯ A → B)
  ◯-rec m f = extendable-along-η m 1 .proj₁ f .proj₁

  -- A "computation rule" for ◯-rec.

  ◯-rec-η : ◯-rec m f (η x) ≡ f x
  ◯-rec-η = extendable-along-η _ 1 .proj₁ _ .proj₂ _

  -- If f and g have type ◯ A → B, where B is modal, and f ∘ η and
  -- g ∘ η are pointwise equal, then f and g are pointwise equal.

  ∘η≡∘η→≡ :
    {f g : ◯ A → B} →
    Modal B →
    (∀ x → f (η x) ≡ g (η x)) →
    ∀ x → f x ≡ g x
  ∘η≡∘η→≡ m p =
    extendable-along-η m 2 .proj₂ _ _ .proj₁ p .proj₁

  -- A "computation rule" for ∘η≡∘η→≡.

  ∘η≡∘η→≡-η : ∘η≡∘η→≡ m p (η x) ≡ p x
  ∘η≡∘η→≡-η =
    extendable-along-η _ 2 .proj₂ _ _ .proj₁ _ .proj₂ _

  -- A dependent eliminator for ◯.

  ◯-elim :
    {P : ◯ A → Type a} →
    (∀ x → Modal (P x)) →
    ((x : A) → P (η x)) →
    ((x : ◯ A) → P x)
  ◯-elim {A = A} {P = P} m f x =
    subst P (lemma x) (f′ x .proj₂)
    where
    f′ : ◯ A → Σ (◯ A) P
    f′ = ◯-rec (Σ-closed Modal-◯ m) (λ x → η x , f x)

    lemma : ∀ x → f′ x .proj₁ ≡ x
    lemma = ∘η≡∘η→≡ Modal-◯ λ x →
      ◯-rec (Σ-closed Modal-◯ m) (λ x → η x , f x) (η x) .proj₁  ≡⟨ cong proj₁ ◯-rec-η ⟩∎
      η x                                                        ∎

  -- A "computation rule" for ◯-elim.

  ◯-elim-η :
    {P : ◯ A → Type a}
    {m : ∀ x → Modal (P x)}
    {f : (x : A) → P (η x)} →
    ◯-elim m f (η x) ≡ f x
  ◯-elim-η {x = x} {P = P} {m = m} {f = f} =
    subst P (∘η≡∘η→≡ Modal-◯ (λ _ → cong proj₁ ◯-rec-η) (η x))
      (◯-rec (Σ-closed Modal-◯ m) (λ x → η x , f x) (η x) .proj₂)  ≡⟨ cong (flip (subst P) _) ∘η≡∘η→≡-η ⟩

    subst P (cong proj₁ ◯-rec-η)
      (◯-rec (Σ-closed Modal-◯ m) (λ x → η x , f x) (η x) .proj₂)  ≡⟨ sym $ subst-∘ _ _ _ ⟩

    subst (P ∘ proj₁) ◯-rec-η
      (◯-rec (Σ-closed Modal-◯ m) (λ x → η x , f x) (η x) .proj₂)  ≡⟨ elim₁
                                                                        (λ {y} eq → subst (P ∘ proj₁) eq (y .proj₂) ≡ f x)
                                                                        (subst-refl _ _)
                                                                        _ ⟩∎
    f x                                                            ∎

  ----------------------------------------------------------------------
  -- Some basic definitions and lemmas

  -- If η is an equivalence for A, then A is modal.

  Is-equivalence-η→Modal :
    Is-equivalence (η {A = A}) → Modal A
  Is-equivalence-η→Modal {A = A} =
    Is-equivalence (η {A = A})  →⟨ Eq.⟨ _ ,_⟩ ⟩
    A ≃ ◯ A                     →⟨ Modal-respects-≃ ∘ inverse ⟩
    (Modal (◯ A) → Modal A)     →⟨ _$ Modal-◯ ⟩□
    Modal A                     □

  -- A type is stable if ◯ A implies A.

  Stable : Type a → Type a
  Stable A = ◯ A → A

  -- If A is stable, and the stability proof is a left inverse of η,
  -- then A is modal.

  Stable→left-inverse→Modal :
    (s : Stable A) → (∀ x → s (η x) ≡ x) → Modal A
  Stable→left-inverse→Modal s eq =
    Is-equivalence-η→Modal $
    _≃_.is-equivalence $
    Eq.↔→≃
      _
      s
      (∘η≡∘η→≡ Modal-◯ (cong η ∘ eq))
      eq

  -- A type is separated if equality is modal for this type.
  --
  -- This definition is taken from "Localization in homotopy type
  -- theory" by Christensen, Opie, Rijke and Scoccola.

  Separated : Type a → Type a
  Separated = For-iterated-equality 1 Modal

  -- If a type is modal, then it is separated.

  Modal→Separated : Modal A → Separated A
  Modal→Separated m x y =
    Stable→left-inverse→Modal
      (◯ (x ≡ y)  →⟨ ∘η≡∘η→≡
                       {f = λ (_ : ◯ (x ≡ y)) → x}
                       {g = λ (_ : ◯ (x ≡ y)) → y}
                       m
                       id ⟩□
       x ≡ y      □)
      (λ _ → ∘η≡∘η→≡-η)

  -- One can strengthen extendable-along-η.

  stronger-extendable-along-η :
    {P : ◯ A → Type a} →
    (∀ x → Modal (P x)) →
    Is-∞-extendable-along-[ η ] P
  stronger-extendable-along-η m zero    = _
  stronger-extendable-along-η m (suc n) =
      (λ f → ◯-elim m f , λ _ → ◯-elim-η)
    , λ _ _ →
        stronger-extendable-along-η
          (λ x → Modal→Separated (m x) _ _) n

  -- A Σ-closed reflective subuniverse is a modality.
  --
  -- See also Modality.Σ-closed below.

  modality : Modality a
  modality = λ where
    .Modality-record.◯                   → ◯
    .Modality-record.η                   → η
    .Modality-record.Modal               → Modal
    .Modality-record.Modal-propositional → Modal-propositional
    .Modality-record.Modal-◯             → Modal-◯
    .Modality-record.Modal-respects-≃    → Modal-respects-≃
    .Modality-record.extendable-along-η  → stronger-extendable-along-η

------------------------------------------------------------------------
-- Connectedness

-- ◯ -Connected A means that A is ◯-connected.

_-Connected_ : (Type a → Type a) → Type a → Type a
◯ -Connected A = Contractible (◯ A)

-- ◯ -Connected-→ f means that f is ◯-connected.

_-Connected-→_ :
  {A B : Type a} →
  (Type a → Type a) → (A → B) → Type a
◯ -Connected-→ f = ∀ y → ◯ -Connected (f ⁻¹ y)

-- ◯ -Connected A is propositional (assuming function extensionality).

Connected-propositional :
  Extensionality a a →
  (◯ : Type a → Type a) →
  Is-proposition (◯ -Connected A)
Connected-propositional ext _ = H-level-propositional ext 0

-- ◯ -Connected-→ f is propositional (assuming function
-- extensionality).

Connected-→-propositional :
  Extensionality a a →
  (◯ : Type a → Type a) →
  Is-proposition (◯ -Connected-→ f)
Connected-→-propositional ext ◯ =
  Π-closure ext 1 λ _ →
  Connected-propositional ext ◯

-- I did not take the remaining definitions in this section from
-- "Modalities in Homotopy Type Theory" or the corresponding Coq code.

-- _-Connectedᴱ_ is a variant of _-Connected_ that uses Contractibleᴱ
-- instead of Contractible.
--
-- See also Modality.Connectedᴱ-propositional.

_-Connectedᴱ_ : (Type a → Type a) → Type a → Type a
◯ -Connectedᴱ A = Contractibleᴱ (◯ A)

-- _-Connected-→ᴱ_ is a variant of _-Connected→_ that uses
-- _-Connectedᴱ_ instead of _-Connected_ and _⁻¹ᴱ_ instead of _⁻¹_.
--
-- See also Modality.Connected-→ᴱ-propositional.

_-Connected-→ᴱ_ :
  {A B : Type a} →
  (Type a → Type a) → (A → B) → Type a
◯ -Connected-→ᴱ f = ∀ y → ◯ -Connectedᴱ (f ⁻¹ᴱ y)

------------------------------------------------------------------------
-- Some definitions

-- A definition of what it means for a modality to be left exact,
-- based on Theorem 3.1 (i) in "Modalities in Homotopy Type Theory".

Left-exact : (Type a → Type a) → Type (lsuc a)
Left-exact {a = a} ◯ =
  {A : Type a} {x y : A} →
  ◯ -Connected A → ◯ -Connected (x ≡ y)

-- Left-exact ◯ is propositional (assuming function extensionality).

Left-exact-propositional :
  {◯ : Type a → Type a} →
  Extensionality (lsuc a) a →
  Is-proposition (Left-exact ◯)
Left-exact-propositional {◯ = ◯} ext =
  implicit-Π-closure ext  1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  Π-closure ext′ 1 λ _ →
  Connected-propositional ext′ ◯
  where
  ext′ = lower-extensionality _ lzero ext

-- A definition of what it means for a modality to be accessible.
--
-- This definition is based on (one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory". Originally I had
-- allowed I and P to target a different, possibly larger universe,
-- because I had missed that the two universe levels occurring in the
-- Coq code were not unconstrained. However, it was pointed out to me
-- by Felix Cherubini and Christian Sattler (and perhaps someone else)
-- that my definition was not correct.

Accessible : Modality a → Type (lsuc a)
Accessible {a = a} M =
  ∃ λ (I : Type a) →
  ∃ λ (P : I → Type a) →
    (A : Type a) →
    Modal A ⇔
    ∀ i →
    Is-∞-extendable-along-[ (λ (_ : P i) → lift tt) ]
      (λ (_ : ↑ a ⊤) → A)
  where
  open Modality-record M

-- A definition of what it means for a modality to be topological.
--
-- This definition is based on (one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory".

Topological : Modality a → Type (lsuc a)
Topological M =
  ∃ λ ((_ , P , _) : Accessible M) →
    ∀ i → Is-proposition (P i)

-- A definition of what it means for a modality to be cotopological.

Cotopological : (Type a → Type a) → Type (lsuc a)
Cotopological {a = a} ◯ =
  Left-exact ◯ ×
  ({A : Type a} → Is-proposition A → ◯ -Connected A → Contractible A)

-- Cotopological ◯ is propositional (assuming function extensionality).

Cotopological-propositional :
  {◯ : Type a → Type a} →
  Extensionality (lsuc a) a →
  Is-proposition (Cotopological ◯)
Cotopological-propositional {◯ = ◯} ext =
  ×-closure 1 (Left-exact-propositional ext) $
  implicit-Π-closure ext  1 λ _ →
  Π-closure          ext′ 1 λ _ →
  Π-closure          ext′ 1 λ _ →
  H-level-propositional ext′ 0
  where
  ext′ = lower-extensionality _ lzero ext

-- I did not take the remaining definitions in this section from
-- "Modalities in Homotopy Type Theory" or the corresponding Coq code
-- (but "Modal ⊥" is used in the Coq code).

-- A modality is called empty-modal if the empty type is modal.

Empty-modal : Modality a → Type a
Empty-modal M = Modal ⊥
  where
  open Modality-record M

-- Empty-modal M is propositional (assuming function extensionality).

Empty-modal-propositional :
  {M : Modality a} →
  Extensionality a a →
  Is-proposition (Empty-modal M)
Empty-modal-propositional {M = M} ext =
  Modal-propositional ext
  where
  open Modality-record M

-- A modality is called "very modal" if ◯ (Modal A) always holds.
--
-- I did not take this definition from "Modalities in Homotopy Type
-- Theory" or the corresponding Coq code.
--
-- See also Modality.Very-modal-propositional.

Very-modal : Modality a → Type (lsuc a)
Very-modal {a = a} M = {A : Type a} → ◯ (Modal A)
  where
  open Modality-record M

-- A modality of type Modality a is W-modal if W A P is modal whenever
-- A is modal (for any A : Type a and P : A → Type a).

W-modal : Modality a → Type (lsuc a)
W-modal {a = a} M =
  {A : Type a} {P : A → Type a} →
  Modal A → Modal (W A P)
  where
  open Modality-record M

-- W-modal M is propositional (assuming function extensionality).

W-modal-propositional :
  {M : Modality a} →
  Extensionality (lsuc a) (lsuc a) →
  Is-proposition (W-modal M)
W-modal-propositional {M = M} ext =
  implicit-Π-closure ext 1 λ _ →
  implicit-Π-closure (lower-extensionality lzero _ ext) 1 λ _ →
  Π-closure (lower-extensionality _ _ ext) 1 λ _ →
  Modal-propositional (lower-extensionality _ _ ext)
  where
  open Modality-record M

------------------------------------------------------------------------
-- Some results that hold for every modality

module Modality (M : Modality a) where

  open Dummy.Modality-record M public

  ----------------------------------------------------------------------
  -- Eliminators

  -- The eliminators are abstract in order to make types printed by
  -- Agda potentially easier to read.

  abstract

    -- An eliminator for ◯.

    ◯-elim :
      {P : ◯ A → Type a} →
      (∀ x → Modal (P x)) →
      ((x : A) → P (η x)) →
      ((x : ◯ A) → P x)
    ◯-elim m f = extendable-along-η m 1 .proj₁ f .proj₁

    -- A "computation rule" for ◯-elim.

    ◯-elim-η : ◯-elim m f (η x) ≡ f x
    ◯-elim-η {m = m} {f = f} {x = x} =
      extendable-along-η m 1 .proj₁ f .proj₂ x

    -- A non-dependent eliminator for ◯.

    ◯-rec : Modal B → (A → B) → (◯ A → B)
    ◯-rec m = ◯-elim (λ _ → m)

    -- A "computation rule" for ◯-rec.

    ◯-rec-η : ◯-rec m f (η x) ≡ f x
    ◯-rec-η = ◯-elim-η

    -- If f and g have type (x : ◯ A) → P x, where P x is modal for
    -- all x, and f ∘ η and g ∘ η are pointwise equal, then f and g
    -- are pointwise equal.

    ∘η≡∘η→≡ :
      {f g : (x : ◯ A) → P x} →
      (∀ x → Modal (P x)) →
      (∀ x → f (η x) ≡ g (η x)) →
      ∀ x → f x ≡ g x
    ∘η≡∘η→≡ m p =
      extendable-along-η m 2 .proj₂ _ _ .proj₁ p .proj₁

    -- A "computation rule" for ∘η≡∘η→≡.

    ∘η≡∘η→≡-η : ∘η≡∘η→≡ m p (η x) ≡ p x
    ∘η≡∘η→≡-η {m = m} {p = p} =
      extendable-along-η m 2 .proj₂ _ _ .proj₁ p .proj₂ _

  ----------------------------------------------------------------------
  -- Some basic definitions and lemmas

  -- If η is an equivalence for A, then A is modal.

  Is-equivalence-η→Modal :
    Is-equivalence (η {A = A}) → Modal A
  Is-equivalence-η→Modal {A = A} =
    Is-equivalence (η {A = A})  →⟨ Eq.⟨ _ ,_⟩ ⟩
    A ≃ ◯ A                     →⟨ Modal-respects-≃ ∘ inverse ⟩
    (Modal (◯ A) → Modal A)     →⟨ _$ Modal-◯ ⟩□
    Modal A                     □

  -- A type is stable if ◯ A implies A.

  Stable : Type a → Type a
  Stable A = ◯ A → A

  -- If A is stable, and the stability proof is a left inverse of η,
  -- then A is modal.

  Stable→left-inverse→Modal :
    (s : Stable A) → (∀ x → s (η x) ≡ x) → Modal A
  Stable→left-inverse→Modal s eq =
    Is-equivalence-η→Modal $
    _≃_.is-equivalence $
    Eq.↔→≃
      _
      s
      (∘η≡∘η→≡ (λ _ → Modal-◯) (cong η ∘ eq))
      eq

  -- Stable propositions are modal.

  Stable→Is-proposition→Modal :
    Stable A → Is-proposition A → Modal A
  Stable→Is-proposition→Modal s prop =
    Stable→left-inverse→Modal s (λ _ → prop _ _)

  -- A type is separated if equality is modal for this type.
  --
  -- This definition is taken from "Localization in homotopy type
  -- theory" by Christensen, Opie, Rijke and Scoccola.

  Separated : Type a → Type a
  Separated = For-iterated-equality 1 Modal

  -- If a type is modal, then it is separated.

  Modal→Separated : Modal A → Separated A
  Modal→Separated m x y =
    Stable→left-inverse→Modal
      (◯ (x ≡ y)  →⟨ ∘η≡∘η→≡
                       {f = λ (_ : ◯ (x ≡ y)) → x}
                       {g = λ (_ : ◯ (x ≡ y)) → y}
                       (λ _ → m)
                       id ⟩□
       x ≡ y      □)
      (λ _ → ∘η≡∘η→≡-η)

  -- The type ◯ A is separated.

  Separated-◯ : Separated (◯ A)
  Separated-◯ = Modal→Separated Modal-◯

  -- If ◯ (x ≡ y) holds, then η x is equal to η y.

  η-cong : ◯ (x ≡ y) → η x ≡ η y
  η-cong = ◯-rec (Separated-◯ _ _) (cong η)

  -- A "computation rule" for η-cong.

  η-cong-η : η-cong (η p) ≡ cong η p
  η-cong-η = ◯-rec-η

  -- A is modal if and only if η is an equivalence for A.

  Modal≃Is-equivalence-η :
    Modal A ↝[ a ∣ a ] Is-equivalence (η {A = A})
  Modal≃Is-equivalence-η =
    generalise-ext?-prop
      (record
         { to = λ m →
             _≃_.is-equivalence $
             Eq.↔→≃
               _
               (◯-rec m id)
               (◯-elim
                  (λ _ → Separated-◯ _ _)
                  (λ _ → cong η ◯-rec-η))
               (λ _ → ◯-rec-η)
         ; from = Is-equivalence-η→Modal
         })
      Modal-propositional
      Is-equivalence-propositional

  -- If A is modal, then A is equivalent to ◯ A.

  Modal→≃◯ : Modal A → A ≃ ◯ A
  Modal→≃◯ m = Eq.⟨ _ , Modal≃Is-equivalence-η _ m ⟩

  -- If A is modal, then η is an embedding for A.

  Modal→Is-embedding-η :
    Modal A → Is-embedding (η ⦂ (A → ◯ A))
  Modal→Is-embedding-η m =
    Emb.Is-equivalence→Is-embedding
      (Modal≃Is-equivalence-η _ m)

  -- For modal types the function η has an inverse.

  η⁻¹ : Modal A → ◯ A → A
  η⁻¹ m = _≃_.from (Modal→≃◯ m)

  η-η⁻¹ : η (η⁻¹ m x) ≡ x
  η-η⁻¹ = _≃_.right-inverse-of (Modal→≃◯ _) _

  η⁻¹-η : η⁻¹ m (η x) ≡ x
  η⁻¹-η = _≃_.left-inverse-of (Modal→≃◯ _) _

  -- When proving that A is modal one can assume that ◯ A is
  -- inhabited.

  [◯→Modal]→Modal : (◯ A → Modal A) → Modal A
  [◯→Modal]→Modal m =
    Is-equivalence-η→Modal $
    HA.[inhabited→Is-equivalence]→Is-equivalence $
    Modal≃Is-equivalence-η _ ∘ m

  -- The function subst can sometimes be "pushed" through η.

  subst-η : subst (◯ ∘ P) eq (η p) ≡ η (subst P eq p)
  subst-η {P = P} {eq = eq} {p = p} =
    elim¹
      (λ eq → ∀ p → subst (◯ ∘ P) eq (η p) ≡ η (subst P eq p))
      (λ p →
         subst (◯ ∘ P) (refl _) (η p)  ≡⟨ subst-refl _ _ ⟩
         η p                           ≡⟨ cong η $ sym $ subst-refl _ _ ⟩∎
         η (subst P (refl _) p)        ∎)
      eq p

  ----------------------------------------------------------------------
  -- Some closure properties related to Modal

  -- The unit type (lifted) is modal.

  Modal-⊤ : Modal (↑ a ⊤)
  Modal-⊤ = Stable→left-inverse→Modal _ refl

  -- Modal is closed under "Π A" (assuming function
  -- extensionality).

  Modal-Π :
    {A : Type a} {P : A → Type a} →
    Extensionality a a →
    (∀ x → Modal (P x)) → Modal ((x : A) → P x)
  Modal-Π ext m =
    Stable→left-inverse→Modal
      (λ f x → ◯-rec (m x) (_$ x) f)
      (λ f → apply-ext ext λ x →
         ◯-rec (m x) (_$ x) (η f)  ≡⟨ ◯-rec-η ⟩∎
         f x                       ∎)

  -- Modal is closed under Σ.

  Modal-Σ : Modal A → (∀ x → Modal (P x)) → Modal (Σ A P)
  Modal-Σ {P = P} mA mP =
    Stable→left-inverse→Modal
      (λ p →
           ◯-rec mA proj₁ p
         , ◯-elim
             (mP ∘ ◯-rec mA proj₁)
             (subst P (sym ◯-rec-η) ∘ proj₂)
             p)
      (λ (x , y) →
         Σ-≡,≡→≡
           ◯-rec-η
           (subst P ◯-rec-η
              (◯-elim
                 (mP ∘ ◯-rec mA proj₁)
                 (subst P (sym ◯-rec-η) ∘ proj₂)
                 (η (x , y)))                          ≡⟨ cong (subst P ◯-rec-η) ◯-elim-η ⟩

            subst P ◯-rec-η (subst P (sym ◯-rec-η) y)  ≡⟨ subst-subst-sym _ _ _ ⟩∎

            y                                          ∎))

  -- A generalisation of Modal-Σ.

  Modal-Σ≃Π-Modal :
    Modal A →
    Modal (Σ A P) ↝[ a ∣ a ] (∀ x → Modal (P x))
  Modal-Σ≃Π-Modal {A = A} {P = P} m =
    generalise-ext?-prop
      (record
         { from = Modal-Σ m
         ; to   = flip λ x →
             Modal (Σ A P)                          ↝⟨ flip Modal-Σ (λ _ → Modal→Separated m _ _) ⟩
             Modal (∃ λ ((y , _) : Σ A P) → y ≡ x)  ↝⟨ Modal-respects-≃ $ from-bijection $ inverse Σ-assoc ⟩
             Modal (∃ λ (y : A) → P y × y ≡ x)      ↝⟨ Modal-respects-≃ $ from-bijection $ inverse $ ∃-intro _ _ ⟩□
             Modal (P x)                            □
         })
      Modal-propositional
      (λ ext →
         Π-closure ext 1 λ _ →
         Modal-propositional ext)

  -- If A is modal, then Contractible A is modal (assuming function
  -- extensionality).

  Modal-Contractible :
    Extensionality a a →
    Modal A → Modal (Contractible A)
  Modal-Contractible ext m =
    Modal-Σ m λ _ →
    Modal-Π ext λ _ →
    Modal→Separated m _ _

  -- If f has type A → B, where A is modal and B is separated, then
  -- f ⁻¹ y is modal.

  Modal-⁻¹ :
    {f : A → B} →
    Modal A →
    Separated B →
    Modal (f ⁻¹ y)
  Modal-⁻¹ m s = Modal-Σ m λ _ → s _ _

  -- If f has type A → B, where A and B are separated, then
  -- HA.Proofs f g is modal (assuming function extensionality).

  Modal-Half-adjoint-proofs :
    {f : A → B} →
    Extensionality a a →
    Separated A →
    Separated B →
    Modal (HA.Proofs f g)
  Modal-Half-adjoint-proofs ext sA sB =
    Modal-Σ (Modal-Π ext λ _ → sB _ _) λ _ →
    Modal-Σ (Modal-Π ext λ _ → sA _ _) λ _ →
    Modal-Π ext λ _ → Modal→Separated (sB _ _) _ _

  -- If f has type A → B, where A is modal and B is separated, then
  -- Is-equivalence f is modal (assuming function extensionality).

  Modal-Is-equivalence :
    {f : A → B} →
    Extensionality a a →
    Modal A →
    Separated B →
    Modal (Is-equivalence f)
  Modal-Is-equivalence ext m s =
    Modal-Σ (Modal-Π ext λ _ → m) λ _ →
    Modal-Half-adjoint-proofs ext (Modal→Separated m) s

  -- If A and B are modal, then A ≃ B is modal (assuming function
  -- extensionality).

  Modal-≃ :
    Extensionality a a →
    Modal A → Modal B → Modal (A ≃ B)
  Modal-≃ ext mA mB =
    Modal-respects-≃ (inverse $ Eq.↔⇒≃ Eq.≃-as-Σ) $
    Modal-Σ (Modal-Π ext λ _ → mB) λ _ →
    Modal-Is-equivalence ext mA (Modal→Separated mB)

  -- I did not take the remaining results in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code (but that does not mean that one cannot find something
  -- similar in those places).

  -- If A is "modal n levels up", then H-level′ n A is modal (assuming
  -- function extensionality).

  Modal-H-level′ :
    Extensionality a a →
    ∀ n →
    For-iterated-equality n Modal A →
    Modal (H-level′ n A)
  Modal-H-level′ {A = A} ext n =
    For-iterated-equality n Modal A                   ↝⟨ For-iterated-equality-cong₁ _ n (Modal-Contractible ext) ⟩
    For-iterated-equality n (Modal ∘ Contractible) A  ↝⟨ For-iterated-equality-commutes-← _ Modal n (Modal-Π ext) ⟩□
    Modal (H-level′ n A)                              □

  -- If A is "modal n levels up", then H-level n A is modal (assuming
  -- function extensionality).

  Modal-H-level :
    Extensionality a a →
    ∀ n →
    For-iterated-equality n Modal A →
    Modal (H-level n A)
  Modal-H-level {A = A} ext n =
    For-iterated-equality n Modal A  ↝⟨ Modal-H-level′ ext n ⟩
    Modal (H-level′ n A)             ↝⟨ Modal-respects-≃ (inverse $ H-level↔H-level′ ext) ⟩□
    Modal (H-level n A)              □

  -- Some generalisations of Modal→Separated.

  Modalⁿ→Modal¹⁺ⁿ :
    ∀ n →
    For-iterated-equality n       Modal A →
    For-iterated-equality (1 + n) Modal A
  Modalⁿ→Modal¹⁺ⁿ {A = A} n =
    For-iterated-equality n Modal A        →⟨ For-iterated-equality-cong₁ _ n Modal→Separated ⟩
    For-iterated-equality n Separated A    →⟨ For-iterated-equality-For-iterated-equality n 1 _ ⟩□
    For-iterated-equality (1 + n) Modal A  □

  Modal→Modalⁿ :
    ∀ n →
    Modal A →
    For-iterated-equality n Modal A
  Modal→Modalⁿ zero = id
  Modal→Modalⁿ {A = A} (suc n) =
    Modal A                                →⟨ Modal→Modalⁿ n ⟩
    For-iterated-equality n Modal A        →⟨ Modalⁿ→Modal¹⁺ⁿ n ⟩□
    For-iterated-equality (suc n) Modal A  □

  ----------------------------------------------------------------------
  -- The function ◯-map

  -- The function ◯-map is abstract in order to make types printed by
  -- Agda potentially easier to read.

  abstract

    -- A map function for ◯.

    ◯-map : (A → B) → ◯ A → ◯ B
    ◯-map f = ◯-rec Modal-◯ (η ∘ f)

    -- A "computation rule" for ◯-map.

    ◯-map-η : ◯-map f (η x) ≡ η (f x)
    ◯-map-η = ◯-rec-η

  -- ◯-map id is pointwise equal to id.

  ◯-map-id : {x : ◯ A} → ◯-map id x ≡ id x
  ◯-map-id =
    ◯-elim
      {P = λ x → ◯-map id x ≡ x}
      (λ _ → Separated-◯ _ _)
      (λ x →
         ◯-map id (η x)  ≡⟨ ◯-map-η ⟩∎
         η x             ∎)
      _

  -- ◯-map commutes with composition (pointwise).

  ◯-map-∘ :
    {f : B → C} {g : A → B} →
    ◯-map (f ∘ g) x ≡ (◯-map f ∘ ◯-map g) x
  ◯-map-∘ {f = f} {g = g} =
    ◯-elim
      {P = λ x → ◯-map (f ∘ g) x ≡ ◯-map f (◯-map g x)}
      (λ _ → Separated-◯ _ _)
      (λ x →
         ◯-map (f ∘ g) (η x)      ≡⟨ ◯-map-η ⟩
         η (f (g x))              ≡⟨ sym ◯-map-η ⟩
         ◯-map f (η (g x))        ≡⟨ cong (◯-map f) $ sym ◯-map-η ⟩∎
         ◯-map f (◯-map g (η x))  ∎)
      _

  -- ◯-map (const x) is pointwise equal to const (η x).

  ◯-map-const : ◯-map (const x) y ≡ const (η x) y
  ◯-map-const {x = x} {y = y} =
    ◯-elim
      {P = λ y → ◯-map (const x) y ≡ η x}
      (λ _ → Separated-◯ _ _)
      (λ y →
         ◯-map (const x) (η y)  ≡⟨ ◯-map-η ⟩
         η x                    ∎)
      y

  -- ◯-map respects pointwise equality.

  ◯-map-cong : (∀ x → f x ≡ g x) → ◯-map f x ≡ ◯-map g x
  ◯-map-cong {f = f} {g = g} {x = x} p =
    ∘η≡∘η→≡
      {f = ◯-map f}
      {g = ◯-map g}
      (λ _ → Modal-◯)
      (λ x →
         ◯-map f (η x)  ≡⟨ ◯-map-η ⟩
         η (f x)        ≡⟨ cong η (p x) ⟩
         η (g x)        ≡⟨ sym ◯-map-η ⟩∎
         ◯-map g (η x)  ∎)
      x

  -- I did not take the remaining lemmas in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code.

  -- A fusion lemma for ◯-elim and ◯-map.

  ◯-elim-◯-map :
    {g : A → B} →
    ◯-elim {P = P} m f (◯-map g x) ≡
    ◯-elim
      {P = P ∘ ◯-map g}
      (m ∘ ◯-map g)
      (subst P (sym ◯-map-η) ∘ f ∘ g)
      x
  ◯-elim-◯-map {P = P} {m = m} {f = f} {x = x} {g = g} =
    ◯-elim
      {P = λ x →
             ◯-elim {P = P} m f (◯-map g x) ≡
             ◯-elim
               {P = P ∘ ◯-map g}
               (m ∘ ◯-map g)
               (subst P (sym ◯-map-η) ∘ f ∘ g)
               x}
      (λ x → Modal→Separated (m (◯-map g x)) _ _)
      (λ x →
         ◯-elim m f (◯-map g (η x))                                  ≡⟨ elim¹
                                                                          (λ {y} eq → ◯-elim m f y ≡ subst P eq (f (g x)))
                                                                          (
           ◯-elim m f (η (g x))                                            ≡⟨ ◯-elim-η ⟩
           f (g x)                                                         ≡⟨ sym $ subst-refl _ _ ⟩∎
           subst P (refl (η (g x))) (f (g x))                              ∎)
                                                                          _ ⟩
         subst P (sym ◯-map-η) (f (g x))                             ≡⟨ sym ◯-elim-η ⟩∎
         ◯-elim (m ∘ ◯-map g) (subst P (sym ◯-map-η) ∘ f ∘ g) (η x)  ∎)
      x

  -- A fusion lemma for ◯-rec and ◯-map.

  ◯-rec-◯-map : ◯-rec m f (◯-map g x) ≡ ◯-rec m (f ∘ g) x
  ◯-rec-◯-map {m = m} {f = f} {g = g} {x = x} =
    ◯-elim
      {P = λ x → ◯-rec m f (◯-map g x) ≡ ◯-rec m (f ∘ g) x}
      (λ _ → Modal→Separated m _ _)
      (λ x →
         ◯-rec m f (◯-map g (η x))  ≡⟨ cong (◯-rec m f) ◯-map-η ⟩
         ◯-rec m f (η (g x))        ≡⟨ ◯-rec-η ⟩
         f (g x)                    ≡⟨ sym ◯-rec-η ⟩∎
         ◯-rec m (f ∘ g) (η x)      ∎)
      x

  ----------------------------------------------------------------------
  -- Some preservation lemmas

  -- I did not take the results in this section from "Modalities in
  -- Homotopy Type Theory" or the corresponding Coq code (but perhaps
  -- something resembling at least some of these results can be found
  -- there).

  -- ◯ preserves logical equivalences.

  ◯-cong-⇔ : A ⇔ B → ◯ A ⇔ ◯ B
  ◯-cong-⇔ A⇔B = record
    { to   = ◯-map (_⇔_.to   A⇔B)
    ; from = ◯-map (_⇔_.from A⇔B)
    }

  -- ◯ preserves split surjections.

  ◯-cong-↠ : A ↠ B → ◯ A ↠ ◯ B
  ◯-cong-↠ A↠B = record
    { logical-equivalence = ◯-cong-⇔ (_↠_.logical-equivalence A↠B)
    ; right-inverse-of    = ◯-elim
        (λ _ → Separated-◯ _ _)
        (λ y →
           ◯-map (_↠_.to A↠B) (◯-map (_↠_.from A↠B) (η y))  ≡⟨ cong (◯-map (_↠_.to A↠B)) ◯-map-η ⟩
           ◯-map (_↠_.to A↠B) (η (_↠_.from A↠B y))          ≡⟨ ◯-map-η ⟩
           η (_↠_.to A↠B (_↠_.from A↠B y))                  ≡⟨ cong η $ _↠_.right-inverse-of A↠B _ ⟩∎
           η y                                              ∎)
    }

  -- ◯ preserves bijections.

  ◯-cong-↔ : A ↔ B → ◯ A ↔ ◯ B
  ◯-cong-↔ A↔B = record
    { surjection      = ◯-cong-↠ (_↔_.surjection A↔B)
    ; left-inverse-of = ◯-elim
        (λ _ → Separated-◯ _ _)
        (λ x →
           ◯-map (_↔_.from A↔B) (◯-map (_↔_.to A↔B) (η x))  ≡⟨ cong (◯-map (_↔_.from A↔B)) ◯-map-η ⟩
           ◯-map (_↔_.from A↔B) (η (_↔_.to A↔B x))          ≡⟨ ◯-map-η ⟩
           η (_↔_.from A↔B (_↔_.to A↔B x))                  ≡⟨ cong η $ _↔_.left-inverse-of A↔B _ ⟩∎
           η x                                              ∎)
    }

  -- ◯ preserves equivalences.

  ◯-cong-≃ : A ≃ B → ◯ A ≃ ◯ B
  ◯-cong-≃ = from-isomorphism ∘ ◯-cong-↔ ∘ from-isomorphism

  -- ◯ preserves equivalences with erased proofs.

  ◯-cong-≃ᴱ : A ≃ᴱ B → ◯ A ≃ᴱ ◯ B
  ◯-cong-≃ᴱ A≃ᴱB =
    EEq.[≃]→≃ᴱ (EEq.[proofs] (◯-cong-≃ (EEq.≃ᴱ→≃ A≃ᴱB)))

  mutual

    -- If A ↝[ c ∣ d ] B holds, then ◯ A ↝[ k ] ◯ B holds for all k for
    -- which Extensionality? k c d holds.

    ◯-cong-↝ :
      Extensionality? k c d →
      A ↝[ c ∣ d ] B →
      ◯ A ↝[ k ] ◯ B
    ◯-cong-↝ {k = implication} _   hyp = ◯-map (hyp _)
    ◯-cong-↝                   ext hyp = ◯-cong-↝-sym ext hyp

    -- A variant of ◯-cong-↝.

    ◯-cong-↝-sym :
      Extensionality? k c d →
      (∀ {k} → Extensionality? ⌊ k ⌋-sym c d → A ↝[ ⌊ k ⌋-sym ] B) →
      ◯ A ↝[ k ] ◯ B
    ◯-cong-↝-sym ext hyp = generalise-ext?′
      (◯-cong-⇔ (hyp _))
      (λ ext → _≃_.bijection $ ◯-cong-≃ (hyp ext))
      (λ ext → ◯-cong-≃ᴱ (hyp E.[ ext ]))
      ext

  mutual

    -- A variant of ◯-cong-↝-sym.

    ◯-cong-↝ᴱ :
      @0 Extensionality? k c d →
      A ↝[ c ∣ d ]ᴱ B →
      ◯ A ↝[ k ] ◯ B
    ◯-cong-↝ᴱ {k = implication} _   hyp = ◯-map (hyp _)
    ◯-cong-↝ᴱ                   ext hyp = ◯-cong-↝-symᴱ ext hyp

    -- A variant of ◯-cong-↝-sym.

    ◯-cong-↝-symᴱ :
      @0 Extensionality? k c d →
      (∀ {k} → @0 Extensionality? ⌊ k ⌋-sym c d → A ↝[ ⌊ k ⌋-sym ] B) →
      ◯ A ↝[ k ] ◯ B
    ◯-cong-↝-symᴱ ext hyp = generalise-erased-ext?
      (◯-cong-⇔ (hyp _))
      (λ ext → _≃_.bijection $ ◯-cong-≃ (hyp ext))
      ext

  ----------------------------------------------------------------------
  -- Some equivalences and related results

  -- If A and B are equivalent, then Modal A and Modal B are
  -- equivalent (assuming function extensionality).

  Modal-cong :
    Extensionality? k a a →
    A ≃ B → Modal A ↝[ k ] Modal B
  Modal-cong {A = A} {B = B} ext A≃B =
    generalise-ext?-prop
      (record
         { to   = Modal-respects-≃ A≃B
         ; from = Modal-respects-≃ (inverse A≃B)
         })
      Modal-propositional
      Modal-propositional
      ext

  -- The type (x : ◯ A) → ◯ (P x) is inhabited if and only if
  -- (x : A) → ◯ (P (η x)) is.

  Π◯◯≃Π◯η :
    ((x : ◯ A) → ◯ (P x)) ↝[ a ∣ a ] ((x : A) → ◯ (P (η x)))
  Π◯◯≃Π◯η =
    generalise-ext?
      (record { to = _∘ η; from = ◯-elim (λ _ → Modal-◯) })
      (λ ext →
           (λ f → apply-ext ext λ x →
              ◯-elim (λ _ → Modal-◯) f (η x)  ≡⟨ ◯-elim-η ⟩∎
              f x                             ∎)
         , (λ f → apply-ext ext (◯-elim (λ _ → Separated-◯ _ _) λ x →
              ◯-elim (λ _ → Modal-◯) (f ∘ η) (η x)  ≡⟨ ◯-elim-η ⟩∎
              f (η x)                               ∎)))

  -- ◯ (↑ a ⊤) is equivalent to ⊤.

  ◯-⊤ : ◯ (↑ a ⊤) ≃ ⊤
  ◯-⊤ =
    ◯ (↑ a ⊤)  ↝⟨ inverse Eq.⟨ _ , Modal≃Is-equivalence-η _ Modal-⊤ ⟩ ⟩
    ↑ a ⊤      ↔⟨ Bijection.↑↔ ⟩□
    ⊤          □

  private module Abstract where abstract

    -- ◯ commutes with _×_.

    ◯× : ◯ (A × B) ≃ (◯ A × ◯ B)
    ◯× {A = A} {B = B} = Eq.↔→≃
      (◯-rec m′ (Σ-map η η))
      (uncurry λ x → ◯-rec Modal-◯ λ y → ◯-map (_, y) x)
      (λ (x , y) →
         ◯-rec m′ (Σ-map η η) (◯-rec Modal-◯ (λ y → ◯-map (_, y) x) y)  ≡⟨ ◯-elim
                                                                             {P = λ y →
                                                                                    ◯-rec m′ (Σ-map η η)
                                                                                      (◯-rec Modal-◯ (λ y → ◯-map (_, y) x) y) ≡
                                                                                    (x , y)}
                                                                             (λ _ → Modal→Separated m′ _ _)
                                                                             (λ y →
           ◯-rec m′ (Σ-map η η)
             (◯-rec Modal-◯ (λ y → ◯-map (_, y) x) (η y))                       ≡⟨ cong (◯-rec _ _)
                                                                                   ◯-rec-η ⟩

           ◯-rec m′ (Σ-map η η) (◯-map (_, y) x)                                ≡⟨ ◯-elim
                                                                                     (λ _ → Modal→Separated m′ _ _)
                                                                                     (λ x →
             ◯-rec m′ (Σ-map η η) (◯-map (_, y) (η x))                                  ≡⟨ cong (◯-rec _ _)
                                                                                           ◯-map-η ⟩

             ◯-rec m′ (Σ-map η η) (η (x , y))                                           ≡⟨ ◯-rec-η ⟩∎

             (η x , η y)                                                                ∎)
                                                                                     x ⟩∎
           (x , η y)                                                            ∎)
                                                                             _ ⟩∎
         (x , y)                                                        ∎)
      (◯-elim
         (λ _ → Separated-◯ _ _)
         (λ (x , y) →
            uncurry (λ x → ◯-rec Modal-◯ λ y → ◯-map (_, y) x)
              (◯-rec m′ (Σ-map η η) (η (x , y)))                ≡⟨ cong (uncurry λ x → ◯-rec Modal-◯ λ y → ◯-map (_, y) x)
                                                                   ◯-rec-η ⟩
            uncurry (λ x → ◯-rec Modal-◯ λ y → ◯-map (_, y) x)
              (η x , η y)                                       ≡⟨⟩

            ◯-rec Modal-◯ (λ y → ◯-map (_, y) (η x)) (η y)      ≡⟨ ◯-rec-η ⟩


            ◯-map (_, y) (η x)                                  ≡⟨ ◯-map-η ⟩∎

            η (x , y)                                           ∎))
      where
      m′ : Modal (◯ A × ◯ B)
      m′ = Modal-Σ Modal-◯ λ _ → Modal-◯

    -- Four "computation rules" for ◯×.

    ◯×-η : _≃_.to ◯× (η (x , y)) ≡ (η x , η y)
    ◯×-η = ◯-rec-η

    ◯×⁻¹-ηʳ : {y : B} → _≃_.from ◯× (x , η y) ≡ ◯-map (_, y) x
    ◯×⁻¹-ηʳ {x = x} {y = y} =
      ◯-rec Modal-◯ (λ y → ◯-map (_, y) x) (η y)  ≡⟨ ◯-rec-η ⟩∎
      ◯-map (_, y) x                              ∎

    ◯×⁻¹-η : {y : B} → _≃_.from ◯× (η x , η y) ≡ η (x , y)
    ◯×⁻¹-η {x = x} {y = y} =
      _≃_.from ◯× (η x , η y)  ≡⟨ ◯×⁻¹-ηʳ ⟩
      ◯-map (_, y) (η x)       ≡⟨ ◯-map-η ⟩∎
      η (x , y)                ∎

    ◯×⁻¹-ηˡ : {y : ◯ B} → _≃_.from ◯× (η x , y) ≡ ◯-map (x ,_) y
    ◯×⁻¹-ηˡ {x = x} {y = y} =
      ◯-elim
        {P = λ y → _≃_.from ◯× (η x , y) ≡ ◯-map (x ,_) y}
        (λ _ → Separated-◯ _ _)
        (λ y →
           _≃_.from ◯× (η x , η y)  ≡⟨ ◯×⁻¹-η ⟩
           η (x , y)                ≡⟨ sym ◯-map-η ⟩∎
           ◯-map (x ,_) (η y)       ∎)
        y

  open Abstract public

  -- I did not take the remaining results and definitions in this
  -- section from "Modalities in Homotopy Type Theory" or the
  -- corresponding Coq code (but that does not mean that one cannot
  -- find something similar in those places).

  -- ◯ commutes with Vec n (in a certain sense).

  ◯-Vec : ◯ (Vec n P) ≃ Vec n (◯ ∘ P)
  ◯-Vec {n = zero} =
    ◯ (↑ a ⊤)  ↝⟨ ◯-⊤ ⟩
    ⊤          ↔⟨ inverse Bijection.↑↔ ⟩□
    ↑ a ⊤      □
  ◯-Vec {n = suc n} {P = P} =
    ◯ (P fzero × Vec n (P ∘ fsuc))      ↝⟨ ◯× ⟩
    ◯ (P fzero) × ◯ (Vec n (P ∘ fsuc))  ↝⟨ (∃-cong λ _ → ◯-Vec) ⟩□
    ◯ (P fzero) × Vec n (◯ ∘ P ∘ fsuc)  □

  -- A "computation rule" for ◯-Vec.

  ◯-Vec-η :
    {xs : Vec n P} →
    _≃_.to ◯-Vec (η xs) ≡ Vec.map η xs
  ◯-Vec-η {n = zero}                = refl _
  ◯-Vec-η {n = suc _} {xs = x , xs} =
    Σ-map id (_≃_.to ◯-Vec) (_≃_.to ◯× (η (x , xs)))  ≡⟨ cong (Σ-map id (_≃_.to ◯-Vec)) ◯×-η ⟩
    Σ-map id (_≃_.to ◯-Vec) (η x , η xs)              ≡⟨ cong (_ ,_) ◯-Vec-η ⟩∎
    η x , Vec.map η xs                                ∎

  -- A lemma relating Vec.index and ◯-Vec.

  index-◯-Vec :
    {xs : Vec n (◯ ∘ P)} →
    ◯-map (λ xs → Vec.index xs i) (_≃_.from ◯-Vec xs) ≡
    Vec.index xs i
  index-◯-Vec {n = suc _} {i = fzero} {xs = x , xs} =
    ◯-elim
      {P = λ x → ◯-map proj₁ (_≃_.from ◯× (x , _≃_.from ◯-Vec xs)) ≡ x}
      (λ _ → Separated-◯ _ _)
      (λ x →
         ◯-map proj₁ (_≃_.from ◯× (η x , _≃_.from ◯-Vec xs))  ≡⟨ cong (◯-map _) ◯×⁻¹-ηˡ ⟩
         ◯-map proj₁ (◯-map (x ,_) (_≃_.from ◯-Vec xs))       ≡⟨ sym ◯-map-∘ ⟩
         ◯-map (const x) (_≃_.from ◯-Vec xs)                  ≡⟨ ◯-map-const ⟩∎
         η x                                                  ∎)
      x
  index-◯-Vec {n = suc _} {i = fsuc i} {xs = x , xs} =
    ◯-map (λ (_ , xs) → Vec.index xs i)
      (_≃_.from ◯× (x , _≃_.from ◯-Vec xs))                ≡⟨ ◯-map-∘ ⟩

    ◯-map (λ xs → Vec.index xs i)
      (◯-map proj₂ (_≃_.from ◯× (x , _≃_.from ◯-Vec xs)))  ≡⟨ cong (◯-map _) $
                                                              ◯-elim
                                                                {P = λ xs → ◯-map proj₂ (_≃_.from ◯× (x , xs)) ≡ xs}
                                                                (λ _ → Separated-◯ _ _)
                                                                (λ xs →
      ◯-map proj₂ (_≃_.from ◯× (x , η xs))                         ≡⟨ cong (◯-map _) ◯×⁻¹-ηʳ ⟩
      ◯-map proj₂ (◯-map (_, xs) x)                                ≡⟨ sym ◯-map-∘ ⟩
      ◯-map (const xs) x                                           ≡⟨ ◯-map-const ⟩∎
      η xs                                                         ∎)
                                                                _ ⟩

    ◯-map (λ xs → Vec.index xs i) (_≃_.from ◯-Vec xs)      ≡⟨ index-◯-Vec ⟩∎

    Vec.index xs i                                         ∎

  -- A lemma relating ◯-Vec and Vec.tabulate.

  ◯-Vec-tabulate-η :
    {f : (i : Fin n) → P i} →
    _≃_.from ◯-Vec (Vec.tabulate (η ∘ f)) ≡
    η (Vec.tabulate f)
  ◯-Vec-tabulate-η {n = zero}          = refl _
  ◯-Vec-tabulate-η {n = suc n} {f = f} =
    _≃_.from ◯×
      (η (f fzero) , _≃_.from ◯-Vec (Vec.tabulate (η ∘ f ∘ fsuc)))  ≡⟨ cong (_≃_.from ◯× ∘ (_ ,_)) ◯-Vec-tabulate-η ⟩

    _≃_.from ◯× (η (f fzero) , η (Vec.tabulate (f ∘ fsuc)))         ≡⟨ ◯×⁻¹-η ⟩∎

    η (f fzero , Vec.tabulate (f ∘ fsuc))                           ∎

  -- The inverse of a choice principle (that may or may not hold).

  ◯Π→Π◯ :
    {A : Type a} {P : A → Type a} →
    ◯ ((x : A) → P x) → ((x : A) → ◯ (P x))
  ◯Π→Π◯ = flip (◯-map ∘ flip _$_)

  -- A "computation rule" for ◯Π→Π◯.

  ◯Π→Π◯-η :
    Extensionality a a →
    ◯Π→Π◯ (η f) ≡ η ∘ f
  ◯Π→Π◯-η ext = apply-ext ext λ _ → ◯-map-η

  -- ◯Π→Π◯ commutes with ◯-map in a certain way.

  ◯Π→Π◯-◯-map :
    {f : ∀ {x} → P x → Q x} {g : ◯ ((x : A) → P x)} →
    ◯Π→Π◯ (◯-map (f ∘_) g) x ≡ ◯-map f (◯Π→Π◯ g x)
  ◯Π→Π◯-◯-map {x = x} {f = f} {g = g} =
    ◯-elim
      {P = λ g → ◯Π→Π◯ (◯-map (f ∘_) g) x ≡ ◯-map f (◯Π→Π◯ g x)}
      (λ _ → Separated-◯ _ _)
      (λ g →
         ◯Π→Π◯ (◯-map (f ∘_) (η g)) x  ≡⟨ cong (flip ◯Π→Π◯ _) ◯-map-η ⟩
         ◯Π→Π◯ (η (f ∘ g)) x           ≡⟨ ◯-map-η ⟩
         η (f (g x))                   ≡⟨ sym ◯-map-η ⟩
         ◯-map f (η (g x))             ≡⟨ cong (◯-map _) $ sym ◯-map-η ⟩∎
         ◯-map f (◯Π→Π◯ (η g) x)       ∎)
      g

  -- A definition of what it means for the modality to "have choice
  -- for A".
  --
  -- The definition is a little convoluted. In the presence of
  -- function extensionality it can be simplified, see
  -- Has-choice-for≃Is-equivalence-◯Π→Π◯. With the present formulation
  -- one can prove certain things without assuming function
  -- extensionality:
  -- * One can prove that modalities with choice satisfy certain
  --   properties (see Modality.Has-choice).
  -- * One can prove that very modal modalities have choice (see
  --   Modality.Very-modal.has-choice).

  Has-choice-for : Type a → Type (lsuc a)
  Has-choice-for A =
    {P : A → Type a} →
    ∃ λ (Π◯→◯Π : (∀ x → ◯ (P x)) → ◯ (∀ x → P x)) →
    ∃ λ (◯Π→Π◯-Π◯→◯Π : ∀ f x → ◯Π→Π◯ (Π◯→◯Π f) x ≡ f x) →
    Extensionality a a →
    ∃ λ (equiv : Is-equivalence (◯Π→Π◯ {P = P})) →
    let eq = Eq.⟨ _ , equiv ⟩ in
    ∃ λ (Π◯→◯Π≡ : Π◯→◯Π ≡ _≃_.from eq) →
    ∀ f x →
    ◯Π→Π◯-Π◯→◯Π f x ≡
    (◯Π→Π◯ (Π◯→◯Π f) x            ≡⟨ cong (λ g → ◯Π→Π◯ (g f) x) Π◯→◯Π≡ ⟩
     _≃_.to eq (_≃_.from eq f) x  ≡⟨ ext⁻¹ (_≃_.right-inverse-of eq f) x ⟩∎
     f x                          ∎)

  -- In the presence of function extensionality Has-choice-for A is
  -- equivalent to {P : A → Type a} → Is-equivalence (◯Π→Π◯ {P = P}).

  Has-choice-for≃Is-equivalence-◯Π→Π◯ :
    Extensionality (lsuc a) (lsuc a) →
    Has-choice-for A ≃
    ({P : A → Type a} → Is-equivalence (◯Π→Π◯ {P = P}))
  Has-choice-for≃Is-equivalence-◯Π→Π◯ ext =
    implicit-∀-cong ext λ {P} →

    (∃ λ (Π◯→◯Π : (∀ x → ◯ (P x)) → ◯ (∀ x → P x)) →
     ∃ λ (◯Π→Π◯-Π◯→◯Π : ∀ f x → ◯Π→Π◯ (Π◯→◯Π f) x ≡ f x) →
     Extensionality a a →
     ∃ λ (equiv : Is-equivalence (◯Π→Π◯ {P = P})) →
     let eq = Eq.⟨ _ , equiv ⟩ in
     ∃ λ (Π◯→◯Π≡ : Π◯→◯Π ≡ _≃_.from eq) →
     ∀ f x →
     ◯Π→Π◯-Π◯→◯Π f x ≡
     trans (cong (λ g → ◯Π→Π◯ (g f) x) Π◯→◯Π≡)
       (ext⁻¹ (_≃_.right-inverse-of eq f) x))                     ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                      drop-⊤-left-Π (lower-extensionality lzero _ ext) $
                                                                      _⇔_.to contractible⇔↔⊤ $
                                                                      propositional⇒inhabited⇒contractible
                                                                        (Extensionality-propositional ext)
                                                                        ext′) ⟩
    (∃ λ (Π◯→◯Π : (∀ x → ◯ (P x)) → ◯ (∀ x → P x)) →
     ∃ λ (◯Π→Π◯-Π◯→◯Π : ∀ f x → ◯Π→Π◯ (Π◯→◯Π f) x ≡ f x) →
     ∃ λ (equiv : Is-equivalence (◯Π→Π◯ {P = P})) →
     let eq = Eq.⟨ _ , equiv ⟩ in
     ∃ λ (Π◯→◯Π≡ : Π◯→◯Π ≡ _≃_.from eq) →
     ∀ f x →
     ◯Π→Π◯-Π◯→◯Π f x ≡
     trans (cong (λ g → ◯Π→Π◯ (g f) x) Π◯→◯Π≡)
       (ext⁻¹ (_≃_.right-inverse-of eq f) x))                     ↔⟨ Σ-assoc F.∘
                                                                     (∃-cong λ _ → Σ-assoc) F.∘
                                                                     ∃-comm F.∘
                                                                     (∃-cong λ _ →
                                                                      inverse Σ-assoc F.∘
                                                                      ∃-comm F.∘
                                                                      (∃-cong λ _ → Σ-assoc)) ⟩
    (∃ λ ((equiv , Π◯→◯Π , Π◯→◯Π≡) :
          ∃ λ (equiv : Is-equivalence (◯Π→Π◯ {P = P})) →
          ∃ λ (Π◯→◯Π : (∀ x → ◯ (P x)) → ◯ (∀ x → P x)) →
          Π◯→◯Π ≡ _≃_.from Eq.⟨ _ , equiv ⟩) →
     ∃ λ (◯Π→Π◯-Π◯→◯Π : ∀ f x → ◯Π→Π◯ (Π◯→◯Π f) x ≡ f x) →
     ∀ f x →
     ◯Π→Π◯-Π◯→◯Π f x ≡
     trans (cong (λ g → ◯Π→Π◯ (g f) x) Π◯→◯Π≡)
       (ext⁻¹ (_≃_.right-inverse-of Eq.⟨ _ , equiv ⟩ f) x))       ↝⟨ (Σ-cong-contra
                                                                        (inverse $
                                                                         drop-⊤-right λ _ →
                                                                         _⇔_.to contractible⇔↔⊤ $
                                                                         singleton-contractible _) λ _ →
                                                                      F.id) ⟩
    (∃ λ (equiv : Is-equivalence (◯Π→Π◯ {P = P})) →
     let eq = Eq.⟨ _ , equiv ⟩ in
     ∃ λ (◯Π→Π◯-Π◯→◯Π : ∀ f x → ◯Π→Π◯ (_≃_.from eq f) x ≡ f x) →
     ∀ f x →
     ◯Π→Π◯-Π◯→◯Π f x ≡
     trans (cong (λ g → ◯Π→Π◯ (g f) x) (refl (_≃_.from eq)))
       (ext⁻¹ (_≃_.right-inverse-of eq f) x))                     ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                      ∀-cong ext′ λ _ → ∀-cong ext′ λ _ →
                                                                      ≡⇒↝ _ $ cong (_ ≡_) $
                                                                      trans (cong (flip trans _) $
                                                                             cong-refl _) $
                                                                      trans-reflˡ _) ⟩
    (∃ λ (equiv : Is-equivalence (◯Π→Π◯ {P = P})) →
     let eq = Eq.⟨ _ , equiv ⟩ in
     ∃ λ (◯Π→Π◯-Π◯→◯Π : ∀ f x → ◯Π→Π◯ (_≃_.from eq f) x ≡ f x) →
     ∀ f x →
     ◯Π→Π◯-Π◯→◯Π f x ≡ ext⁻¹ (_≃_.right-inverse-of eq f) x)       ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                      Eq.extensionality-isomorphism ext′ F.∘
                                                                      (∀-cong ext′ λ _ → Eq.extensionality-isomorphism ext′)) ⟩
    (∃ λ (equiv : Is-equivalence (◯Π→Π◯ {P = P})) →
     let eq = Eq.⟨ _ , equiv ⟩ in
     ∃ λ (◯Π→Π◯-Π◯→◯Π : ∀ f x → ◯Π→Π◯ (_≃_.from eq f) x ≡ f x) →
     ◯Π→Π◯-Π◯→◯Π ≡ ext⁻¹ ∘ _≃_.right-inverse-of eq)               ↔⟨ (drop-⊤-right λ _ →
                                                                      _⇔_.to contractible⇔↔⊤ $
                                                                      singleton-contractible _) ⟩□
    Is-equivalence (◯Π→Π◯ {P = P})                                □
    where
    ext′ : Extensionality a a
    ext′ = lower-extensionality _ _ ext

  -- A definition of what it means for the modality to "have choice",
  -- or to be a "modality with choice".

  Has-choice : Type (lsuc a)
  Has-choice = {A : Type a} → Has-choice-for A

  -- Has-choice-for P is a proposition (assuming function
  -- extensionality).

  Has-choice-for-propositional :
    Extensionality (lsuc a) (lsuc a) →
    Is-proposition (Has-choice-for A)
  Has-choice-for-propositional {A = A} ext =
                                                              $⟨ (implicit-Π-closure (lower-extensionality lzero _ ext) 1 λ _ →
                                                                  Is-equivalence-propositional (lower-extensionality _ _ ext)) ⟩
    Is-proposition ({P : A → Type a} → Is-equivalence ◯Π→Π◯)  →⟨ H-level-cong _ 1 (inverse $ Has-choice-for≃Is-equivalence-◯Π→Π◯ ext) ⟩□
    Is-proposition (Has-choice-for A)                         □

  -- Has-choice is a proposition (assuming function extensionality).

  Has-choice-propositional :
    Extensionality (lsuc a) (lsuc a) →
    Is-proposition Has-choice
  Has-choice-propositional ext =
    implicit-Π-closure ext 1 λ _ →
    Has-choice-for-propositional ext

  -- Has-choice-for preserves equivalences (assuming function
  -- extensionality).

  Has-choice-for-cong-≃ :
    Extensionality (lsuc a) (lsuc a) →
    A ≃ B → Has-choice-for A ≃ Has-choice-for B
  Has-choice-for-cong-≃ {A = A} {B = B} ext A≃B =
    Has-choice-for A                                       ↝⟨ Has-choice-for≃Is-equivalence-◯Π→Π◯ ext ⟩

    ({P : A → Type a} → Is-equivalence (◯Π→Π◯ {P = P}))    ↝⟨ (implicit-Π-cong ext⁺₀ (Π-cong-contra ext₀⁺ (inverse A≃B) (λ _ → Eq.id)) λ P →

      Is-equivalence
        (◯Π→Π◯ ⦂ (◯ ((x : A) → P x) → (x : A) → ◯ (P x)))        ↝⟨ Is-equivalence≃Is-equivalence-∘ˡ
                                                                      (_≃_.is-equivalence $
                                                                       Π-cong-contra ext₀₀ (inverse A≃B) (λ _ → F.id))
                                                                      ext₀₀ F.∘
                                                                    Is-equivalence≃Is-equivalence-∘ʳ
                                                                      (_≃_.is-equivalence $
                                                                       ◯-cong-≃ $ Π-cong ext₀₀ (inverse A≃B) (λ _ → F.id))
                                                                      ext₀₀ ⟩
      Is-equivalence
        (Π-cong-contra-→ (_≃_.from A≃B) (λ _ → id) ∘
         ◯Π→Π◯ {P = P} ∘
         ◯-map (Π-cong _ (inverse A≃B) (λ _ → id)) ⦂
         (◯ ((x : B) → P (_≃_.from A≃B x)) →
          (x : B) → ◯ (P (_≃_.from A≃B x))))                     ↝⟨ Is-equivalence-cong ext₀₀ $
                                                                    ◯-elim
                                                                      (λ _ → Modal→Separated (Modal-Π ext₀₀ λ _ → Modal-◯) _ _)
                                                                      (lemma P) ⟩□
      Is-equivalence
        (◯Π→Π◯ ⦂
         (◯ ((x : B) → P (_≃_.from A≃B x)) →
          (x : B) → ◯ (P (_≃_.from A≃B x))))                     □) ⟩

    ({P : B → Type a} → Is-equivalence (◯Π→Π◯ {P = P}))    ↝⟨ inverse $ Has-choice-for≃Is-equivalence-◯Π→Π◯ ext ⟩□

    Has-choice-for B                                       □
    where
    ext⁺₀ = lower-extensionality lzero _ ext
    ext₀⁺ = lower-extensionality _ lzero ext
    ext₀₀ = lower-extensionality _ _ ext

    lemma = λ P f → apply-ext ext₀₀ λ x →
      ◯-map (_$ _≃_.from A≃B x) $
      ◯-map
        (λ f x →
           subst P (_≃_.left-inverse-of A≃B x)
             (f (_≃_.to A≃B x))) $
      η f                                                ≡⟨ sym ◯-map-∘ ⟩

      ◯-map
        (λ f →
           subst P
             (_≃_.left-inverse-of A≃B (_≃_.from A≃B x))
             (f (_≃_.to A≃B (_≃_.from A≃B x)))) $
      η f                                                ≡⟨ (cong (flip ◯-map _) $ apply-ext ext₀₀ λ f →

        subst P
          (_≃_.left-inverse-of A≃B (_≃_.from A≃B x))
          (f (_≃_.to A≃B (_≃_.from A≃B x)))                    ≡⟨ cong (flip (subst P) _) $ sym $
                                                                  _≃_.right-left-lemma A≃B _ ⟩
        subst P
          (cong (_≃_.from A≃B) $
           _≃_.right-inverse-of A≃B x)
          (f (_≃_.to A≃B (_≃_.from A≃B x)))                    ≡⟨ elim₁
                                                                    (λ {y} eq →
                                                                       subst P (cong (_≃_.from A≃B) eq) (f y) ≡ f x)
                                                                    (trans (cong (flip (subst P) _) $ cong-refl _) $
                                                                     subst-refl _ _)
                                                                    _ ⟩∎

        f x                                                    ∎) ⟩∎

      ◯-map (_$ x) (η f)                                 ∎

  -- The modality has choice for Fin n (lifted).

  Has-choice-for-Fin : Has-choice-for (↑ a (Fin n))
  Has-choice-for-Fin =
      Π◯→◯Π
    , ◯Π→Π◯-Π◯→◯Π
    , (λ ext →
           _≃_.is-equivalence
             (Eq.↔→≃ _ _
                (apply-ext ext ∘ ◯Π→Π◯-Π◯→◯Π)
                (λ _ → Π◯→◯Π-◯Π→Π◯ (lower-extensionality _ lzero ext)))
         , refl _
         , (λ f i →
              ◯Π→Π◯-Π◯→◯Π f i                                  ≡⟨ cong (_$ i) $ sym $ ext⁻¹-ext ext ⟩

              ext⁻¹ (apply-ext ext $ ◯Π→Π◯-Π◯→◯Π f) i          ≡⟨ trans (sym $ trans-reflˡ _) $
                                                                  cong (flip trans _) $ sym $ cong-refl _ ⟩∎
              trans (cong (λ g → ◯Π→Π◯ (g f) i) (refl Π◯→◯Π))
                (ext⁻¹ (apply-ext ext $ ◯Π→Π◯-Π◯→◯Π f) i)      ∎))
    where
    Π◯→◯Π : ((x : ↑ a (Fin n)) → ◯ (P x)) → ◯ ((x : ↑ a (Fin n)) → P x)
    Π◯→◯Π {n = n} {P = P} =
      ((x : ↑ a (Fin n)) → ◯ (P x))   →⟨ _∘ lift ⟩
      ((x : Fin n) → ◯ (P (lift x)))  →⟨ Vec.tabulate ⟩
      Vec n (◯ ∘ P ∘ lift)            ↔⟨ inverse ◯-Vec ⟩
      ◯ (Vec n (P ∘ lift))            →⟨ ◯-map Vec.index ⟩
      ◯ ((x : Fin n) → P (lift x))    →⟨ ◯-map (_∘ lower) ⟩□
      ◯ ((x : ↑ a (Fin n)) → P x)     □

    abstract

      ◯Π→Π◯-Π◯→◯Π :
        ∀ (f : (x : ↑ a (Fin n)) → ◯ (P x)) i →
        ◯Π→Π◯ (Π◯→◯Π f) i ≡ f i
      ◯Π→Π◯-Π◯→◯Π {n = n} {P = P} f (lift i) =
        ◯-map (_$ lift i) $
        ◯-map (_∘ lower) $
        ◯-map Vec.index $
        _≃_.from ◯-Vec $
        Vec.tabulate (f ∘ lift)                ≡⟨ sym (trans ◯-map-∘ ◯-map-∘) ⟩

        ◯-map (λ xs → Vec.index xs i) $
        _≃_.from ◯-Vec $
        Vec.tabulate (f ∘ lift)                ≡⟨ index-◯-Vec ⟩

        Vec.index (Vec.tabulate (f ∘ lift)) i  ≡⟨ Vec.index-tabulate n _ ⟩∎

        f (lift i)                             ∎

      Π◯→◯Π-◯Π→Π◯ :
        {f : ◯ ((x : ↑ a (Fin n)) → P x)} →
        Extensionality lzero a →
        Π◯→◯Π (◯Π→Π◯ f) ≡ f
      Π◯→◯Π-◯Π→Π◯ {n = n} {P = P} {f = f} ext =
        ◯-elim
          {P = λ f → Π◯→◯Π (◯Π→Π◯ f) ≡ f}
          (λ _ → Separated-◯ _ _)
          (λ f →
             ◯-map (_∘ lower) $
             ◯-map Vec.index $
             _≃_.from ◯-Vec $
             Vec.tabulate (λ i → ◯-map (_$ lift i) (η f))     ≡⟨ sym ◯-map-∘ ⟩

             ◯-map (λ xs → Vec.index xs ∘ lower) $
             _≃_.from ◯-Vec $
             Vec.tabulate (λ i → ◯-map (_$ lift i) (η f))     ≡⟨ (cong (◯-map _) $ cong (_≃_.from ◯-Vec) $ cong Vec.tabulate $ apply-ext ext λ _ →
                                                                  ◯-map-η) ⟩
             ◯-map (λ xs → Vec.index xs ∘ lower) $
             _≃_.from ◯-Vec $
             Vec.tabulate (η ∘ f ∘ lift)                      ≡⟨ cong (◯-map _)
                                                                 ◯-Vec-tabulate-η ⟩
             ◯-map (λ xs → Vec.index xs ∘ lower) $
             η (Vec.tabulate (f ∘ lift))                      ≡⟨ ◯-map-η ⟩

             η (Vec.index (Vec.tabulate (f ∘ lift)) ∘ lower)  ≡⟨ (cong (η ∘ (_∘ lower)) $
                                                                  apply-ext ext $
                                                                  Vec.index-tabulate n) ⟩∎
             η f                                              ∎)
          f

  -- If A is modal, then ◯ (Σ A P) is equivalent to Σ A (◯ ∘ P).

  Modal→◯Σ≃Σ◯ :
    Modal A →
    ◯ (Σ A P) ≃ Σ A (◯ ∘ P)
  Modal→◯Σ≃Σ◯ {A = A} {P = P} m = Eq.↔→≃
    (◯-rec m′ (Σ-map id η))
    (λ (x , y) → ◯-map (x ,_) y)
    (uncurry λ x →
       ◯-elim (λ _ → Modal→Separated m′ _ _) λ y →
         ◯-rec m′ (Σ-map id η) (◯-map (x ,_) (η y))  ≡⟨ cong (◯-rec m′ (Σ-map id η)) ◯-map-η ⟩
         ◯-rec m′ (Σ-map id η) (η (x , y))           ≡⟨ ◯-rec-η ⟩∎
         (x , η y)                                   ∎)
    (◯-elim
       (λ _ → Separated-◯ _ _)
       (λ (x , y) →
          (let x′ , y′ = ◯-rec m′ (Σ-map id η) (η (x , y)) in
           ◯-map (x′ ,_) y′)                                   ≡⟨ cong (λ (p : Σ A (◯ ∘ P)) → let x′ , y′ = p in ◯-map (x′ ,_) y′)
                                                                  ◯-rec-η ⟩

          ◯-map (x ,_) (η y)                                   ≡⟨ ◯-map-η ⟩∎

          η (x , y)                                            ∎))
    where
    m′ = Modal-Σ m λ _ → Modal-◯

  ----------------------------------------------------------------------
  -- Some conversions

  -- Modalities are Σ-closed reflective subuniverses.

  Σ-closed : Σ-closed-reflective-subuniverse a
  Σ-closed = λ where
      .M.◯                    → ◯
      .M.η                    → η
      .M.Modal                → Modal
      .M.Modal-propositional  → Modal-propositional
      .M.Modal-◯              → Modal-◯
      .M.Modal-respects-≃     → Modal-respects-≃
      .M.extendable-along-η m → extendable-along-η (λ _ → m)
      .M.Σ-closed             → Modal-Σ
    where
    module M = Σ-closed-reflective-subuniverse

  -- Modalities are uniquely eliminating modalities (assuming function
  -- extensionality).

  uniquely-eliminating :
    Extensionality a a →
    Uniquely-eliminating-modality a
  uniquely-eliminating ext = λ where
      .M.◯                    → ◯
      .M.η                    → η
      .M.uniquely-eliminating → _≃_.is-equivalence (Π◯◯≃Π◯η ext)
    where
    module M = Uniquely-eliminating-modality

  ----------------------------------------------------------------------
  -- Stability

  -- I did not take the definitions or results in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code (but perhaps something resembling at least some of these
  -- results can be found there).

  -- A generalised form of stability.

  Stable-[_] : Kind → Type a → Type a
  Stable-[ k ] A = ◯ A ↝[ k ] A

  -- Modal types are k-stable for all k.

  Modal→Stable : Modal A → Stable-[ k ] A
  Modal→Stable {A = A} {k = k} =
    Modal A         →⟨ Modal→≃◯ ⟩
    (A ≃ ◯ A)       →⟨ inverse ⟩
    (◯ A ≃ A)       →⟨ from-equivalence ⟩□
    Stable-[ k ] A  □

  -- A "computation rule" for Modal→Stable.

  Modal→Stable-η : Modal→Stable m (η x) ≡ x
  Modal→Stable-η = η⁻¹-η

  -- A simplification lemma for Modal→Stable and
  -- Stable→left-inverse→Modal.

  Modal→Stable-Stable→left-inverse→Modal :
    Modal→Stable (Stable→left-inverse→Modal s p) x ≡ s x
  Modal→Stable-Stable→left-inverse→Modal {s = s} {p = p} {x = x} =
    ◯-elim
      {P = λ x → Modal→Stable m′ x ≡ s x}
      (λ x → Modal→Separated m′ _ _)
      (λ x →
         Modal→Stable m′ (η x)  ≡⟨ Modal→Stable-η ⟩
         x                      ≡⟨ sym $ p x ⟩∎
         s (η x)                ∎)
      x
    where
    m′ = Stable→left-inverse→Modal s p

  -- A simplification lemma for Modal→Stable and ◯-map.

  Modal→Stable-◯-map :
    Modal→Stable m₁ (◯-map f x) ≡ f (Modal→Stable m₂ x)
  Modal→Stable-◯-map {m₁ = m₁} {f = f} {x = x} {m₂ = m₂} =
    ◯-elim
      {P = λ x →
             Modal→Stable m₁ (◯-map f x) ≡
             f (Modal→Stable m₂ x)}
      (λ _ → Modal→Separated m₁ _ _)
      (λ x →
         Modal→Stable m₁ (◯-map f (η x))  ≡⟨ cong (Modal→Stable m₁) ◯-map-η ⟩
         Modal→Stable m₁ (η (f x))        ≡⟨ Modal→Stable-η ⟩
         f x                              ≡⟨ cong f $ sym Modal→Stable-η ⟩∎
         f (Modal→Stable m₂ (η x))        ∎)
      x

  -- Stable types are logical-equivalence-stable.

  Stable→Stable-⇔ : Stable A → Stable-[ logical-equivalence ] A
  Stable→Stable-⇔ s = record { to = s; from = η }

  -- Stability is closed under Π-types.

  Stable-Π :
    {A : Type a} {P : A → Type a} →
    (∀ x → Stable (P x)) →
    Stable ((x : A) → P x)
  Stable-Π {A = A} {P = P} hyp =
    ◯ ((x : A) → P x)    →⟨ ◯Π→Π◯ ⟩
    ((x : A) → ◯ (P x))  →⟨ ∀-cong _ hyp ⟩□
    ((x : A) → P x)      □

  -- A lemma relating Stable-Π and Modal-Π.

  Stable-Π-Modal-Π :
    {m : ∀ x → Modal (P x)}
    (ext : Extensionality a a) →
    Stable-Π (λ x → Modal→Stable (m x)) ≡
    Modal→Stable (Modal-Π ext m)
  Stable-Π-Modal-Π {m = m} ext =
    apply-ext ext λ f →
      (λ x → ◯-rec (m x) id (◯-map (_$ x) f))  ≡⟨ (apply-ext ext λ _ → ◯-rec-◯-map) ⟩
      (λ x → ◯-rec (m x) (_$ x) f)             ≡⟨ sym Modal→Stable-Stable→left-inverse→Modal ⟩∎
      Modal→Stable (Modal-Π ext m) f           ∎

  -- Stability is closed under implicit Π-types.

  Stable-implicit-Π :
    {A : Type a} {P : A → Type a} →
    (∀ x → Stable (P x)) →
    Stable ({x : A} → P x)
  Stable-implicit-Π {A = A} {P = P} hyp =
    ◯ ({x : A} → P x)  →⟨ ◯-map (λ f _ → f) ⟩
    ◯ ((x : A) → P x)  →⟨ Stable-Π hyp ⟩
    ((x : A) → P x)    →⟨ (λ f → f _) ⟩□
    ({x : A} → P x)    □

  abstract

    -- If A is modal, and P x is k-stable for all x, then Σ A P is
    -- k-stable.

    Stable-Σ :
      {P : A → Type a} →
      Modal A →
      (∀ x → Stable-[ k ] (P x)) →
      Stable-[ k ] (Σ A P)
    Stable-Σ {A = A} {P = P} m s =
      ◯ (Σ A P)    ↔⟨ Modal→◯Σ≃Σ◯ m ⟩
      Σ A (◯ ∘ P)  ↝⟨ ∃-cong s ⟩□
      Σ A P        □

    -- A lemma relating Stable-Σ and Modal-Σ.

    Stable-Σ-Modal-Σ :
      (m₂ : ∀ x → Modal (P x)) →
      Stable-Σ m₁ (λ x → Modal→Stable (m₂ x)) x ≡
      Modal→Stable (Modal-Σ m₁ m₂) x
    Stable-Σ-Modal-Σ {m₁ = m₁} {x = x} m₂ =
      ◯-elim
        {P = λ x →
               Stable-Σ m₁ (λ x → Modal→Stable (m₂ x)) x ≡
               Modal→Stable (Modal-Σ m₁ m₂) x}
        (λ _ → Modal→Separated (Modal-Σ m₁ m₂) _ _)
        (λ (x , y) →
           Σ-map id (Modal→Stable (m₂ _))
             (◯-rec _ (Σ-map id η) (η (x , y)))      ≡⟨ cong (Σ-map id (Modal→Stable (m₂ _))) ◯-rec-η ⟩

           (x , Modal→Stable (m₂ _) (η y))           ≡⟨ cong (_ ,_) Modal→Stable-η ⟩

           (x , y)                                   ≡⟨ sym Modal→Stable-η ⟩∎

           Modal→Stable (Modal-Σ m₁ m₂) (η (x , y))  ∎)
        x

  -- If A and B are k-stable, then A × B is k-stable.

  Stable-× : Stable-[ k ] A → Stable-[ k ] B → Stable-[ k ] (A × B)
  Stable-× {A = A} {B = B} sA sB =
    ◯ (A × B)  ↔⟨ ◯× ⟩
    ◯ A × ◯ B  ↝⟨ sA ×-cong sB ⟩□
    A × B      □

  -- If A and B are stable, then A ⇔ B is stable.

  Stable-⇔ : Stable A → Stable B → Stable (A ⇔ B)
  Stable-⇔ {A = A} {B = B} sA sB =
    ◯ (A ⇔ B)              ↔⟨ ◯-cong-↔ ⇔↔→×→ ⟩
    ◯ ((A → B) × (B → A))  ↝⟨ Stable-× (Stable-Π λ _ → sB) (Stable-Π λ _ → sA) ⟩
    (A → B) × (B → A)      ↔⟨ inverse ⇔↔→×→ ⟩□
    A ⇔ B                  □

  -- Stable respects logical equivalences.

  Stable-respects-⇔ :
    A ⇔ B → Stable A → Stable B
  Stable-respects-⇔ {A = A} {B = B} A⇔B s =
    ◯ B  →⟨ ◯-map $ _⇔_.from A⇔B ⟩
    ◯ A  →⟨ s ⟩
    A    →⟨ _⇔_.to A⇔B ⟩□
    B    □

  -- Stable-[ k ] respects equivalences.

  Stable-respects-≃ :
    A ≃ B → Stable-[ k ] A → Stable-[ k ] B
  Stable-respects-≃ {A = A} {B = B} A≃B s =
    ◯ B  ↔⟨ ◯-cong-≃ $ inverse A≃B ⟩
    ◯ A  ↝⟨ s ⟩
    A    ↔⟨ A≃B ⟩□
    B    □

  -- A variant of Stable-respects-≃.

  Stable-respects-↝ :
    Extensionality? k c d →
    A ↝[ c ∣ d ] B →
    Stable-[ k ] A → Stable-[ k ] B
  Stable-respects-↝ {A = A} {B = B} ext A↝B s =
    ◯ B  ↝⟨ ◯-cong-↝ ext $ inverse-ext? A↝B ⟩
    ◯ A  ↝⟨ s ⟩
    A    ↝⟨ A↝B ext ⟩□
    B    □

  -- If f has type A → B, where A is modal and B is separated, then
  -- Is-equivalence f is stable.

  Modal→Stable-Is-equivalence :
    {f : A → B} →
    Modal A → Separated B →
    Stable (Is-equivalence f)
  Modal→Stable-Is-equivalence {f = f} m s =
                                          $⟨ s′ ⟩
    Stable (∀ y → Contractible (f ⁻¹ y))  →⟨ Stable-respects-⇔ $ inverse $
                                             Is-equivalence≃Is-equivalence-CP _ ⟩□
    Stable (Is-equivalence f)             □
    where
    s′ =
      Stable-Π λ y →
      let m′ : Modal (f ⁻¹ y)
          m′ = Modal-Σ m (λ _ → s _ _) in
      Stable-Σ m′ λ _ →
      Stable-Π λ _ →
      Modal→Stable (Modal→Separated m′ _ _)

  -- If A is "modal n levels up", then H-level′ n A is stable.

  Stable-H-level′ :
    ∀ n →
    For-iterated-equality n Modal A →
    Stable (H-level′ n A)
  Stable-H-level′ {A = A} zero =
    Modal A                  →⟨ (λ m →
                                   Stable-Σ m λ _ →
                                   Stable-Π λ _ →
                                   Modal→Stable $ Modal→Separated m _ _) ⟩□
    Stable (Contractible A)  □
  Stable-H-level′ {A = A} (suc n) =
    For-iterated-equality (suc n) Modal A    →⟨ (λ m →
                                                   Stable-Π λ _ →
                                                   Stable-Π λ _ →
                                                   Stable-H-level′ n $
                                                   m _ _) ⟩□
    Stable ((x y : A) → H-level′ n (x ≡ y))  □

  -- If A is "modal n levels up", then H-level n A is stable.

  Stable-H-level :
    ∀ n →
    For-iterated-equality n Modal A →
    Stable (H-level n A)
  Stable-H-level {A = A} n m =
    ◯ (H-level n A)   →⟨ ◯-map $ H-level↔H-level′ _ ⟩
    ◯ (H-level′ n A)  →⟨ Stable-H-level′ n m ⟩
    H-level′ n A      →⟨ _⇔_.from $ H-level↔H-level′ _ ⟩□
    H-level n A       □

  ----------------------------------------------------------------------
  -- Some definitions related to Erased

  -- I did not take the definitions in this section from "Modalities
  -- in Homotopy Type Theory" or the corresponding Coq code.

  -- ◯ (Erased A) implies Erased (◯ A).

  ◯-Erased→Erased-◯ :
    {@0 A : Type a} →
    @0 ◯ (Erased A) → Erased (◯ A)
  ◯-Erased→Erased-◯ x = E.[ ◯-map E.erased x ]

  -- A definition of what it means for the modality to "commute with
  -- Erased".

  Commutes-with-Erased : Type (lsuc a)
  Commutes-with-Erased =
    {A : Type a} →
    Is-equivalence (λ (x : ◯ (Erased A)) → ◯-Erased→Erased-◯ x)

  -- Commutes-with-Erased is a proposition (assuming function
  -- extensionality).

  Commutes-with-Erased-propositional :
    Extensionality (lsuc a) a →
    Is-proposition Commutes-with-Erased
  Commutes-with-Erased-propositional ext =
    implicit-Π-closure ext 1 λ _ →
    Is-equivalence-propositional
      (lower-extensionality _ lzero ext)

  -- If A is stable, then Erased A is stable.

  Stable-Erased : {@0 A : Type a} → @0 Stable A → Stable (Erased A)
  Stable-Erased {A = A} s =
    ◯ (Erased A)  →⟨ (λ x → ◯-Erased→Erased-◯ x) ⟩
    Erased (◯ A)  →⟨ E.map s ⟩□
    Erased A      □

  -- If A is modal, then Contractibleᴱ A is stable.

  Stable-Contractibleᴱ :
    Modal A →
    Stable (Contractibleᴱ A)
  Stable-Contractibleᴱ m =
    Stable-Σ m λ _ →
    Stable-Erased (
    Stable-Π λ _ →
    Modal→Stable (Modal→Separated m _ _))

  -- If f has type A → B, A is modal, and equality is stable for B,
  -- then f ⁻¹ᴱ y is stable.

  Stable-⁻¹ᴱ :
    {A B : Type a} {f : A → B} {y : B} →
    Modal A →
    @0 For-iterated-equality 1 Stable B →
    Stable (f ⁻¹ᴱ y)
  Stable-⁻¹ᴱ m s =
    Stable-Σ m λ _ →
    Stable-Erased (s _ _)

  ----------------------------------------------------------------------
  -- Some variants of the eliminators

  -- I did not take the definitions in this section from "Modalities
  -- in Homotopy Type Theory" or the corresponding Coq code (but
  -- perhaps something similar can be found there).

  abstract

    -- A variant of ◯-elim that uses Stable instead of Modal.

    ◯-elim′ :
      (∀ x → Stable (P x)) →
      ((x : A) → P (η x)) →
      ((x : ◯ A) → P x)
    ◯-elim′ {A = A} {P = P} s =
      ((x : A) → P (η x))      →⟨ η ∘_ ⟩
      ((x : A) → ◯ (P (η x)))  →⟨ _⇔_.from $ Π◯◯≃Π◯η _ ⟩
      ((x : ◯ A) → ◯ (P x))    →⟨ (λ f x → s x (f x)) ⟩□
      ((x : ◯ A) → P x)        □

    -- Three "computation rules" for ◯-elim′.

    ◯-elim′-η :
      {s : ∀ x → Stable (P x)} →
      ◯-elim′ s f (η x) ≡ s (η x) (η (f x))
    ◯-elim′-η {P = P} {f = f} {x = x} {s = s} =
      ◯-elim′ s f (η x)                                         ≡⟨⟩
      s (η x) (◯-elim (λ x → Modal-◯ {A = P x}) (η ∘ f) (η x))  ≡⟨ cong (s (η x)) ◯-elim-η ⟩∎
      s (η x) (η (f x))                                         ∎

    ◯-elim′-η′ :
      s (η x) (η (f x)) ≡ f x →
      ◯-elim′ s f (η x) ≡ f x
    ◯-elim′-η′ {s = s} {x = x} {f = f} hyp =
      ◯-elim′ s f (η x)  ≡⟨ ◯-elim′-η {s = s} ⟩
      s (η x) (η (f x))  ≡⟨ hyp ⟩∎
      f x                ∎

    ◯-elim′-Modal→Stable-η :
      ◯-elim′ (Modal→Stable ∘ m) f (η x) ≡ f x
    ◯-elim′-Modal→Stable-η {m = m} {f = f} {x = x} =
      ◯-elim′-η′ {s = Modal→Stable ∘ m}
        (Modal→Stable (m (η x)) (η (f x))  ≡⟨ Modal→Stable-η ⟩∎
         f x                               ∎)

    -- A variant of ◯-rec that uses Stable instead of Modal.

    ◯-rec′ : Stable B → (A → B) → (◯ A → B)
    ◯-rec′ s = ◯-elim′ (λ _ → s)

    -- Three "computation rules" for ◯-rec′.

    ◯-rec′-η : ◯-rec′ s f (η x) ≡ s (η (f x))
    ◯-rec′-η {s = s} = ◯-elim′-η {s = λ _ → s}

    ◯-rec′-η′ :
      s (η (f x)) ≡ f x →
      ◯-rec′ s f (η x) ≡ f x
    ◯-rec′-η′ {s = s} = ◯-elim′-η′ {s = λ _ → s}

    ◯-rec′-Modal→Stable-η :
      ◯-rec′ (Modal→Stable m) f (η x) ≡ f x
    ◯-rec′-Modal→Stable-η {m = m} =
      ◯-elim′-Modal→Stable-η {m = λ _ → m}

  -- If s : Stable B and a certain "computation rule" holds for ◯-rec′
  -- and s, then B is modal.

  ◯-rec′-η→Modal :
    (s : Stable B) →
    (∀ {A} {f : A → B} {x : A} → ◯-rec′ s f (η x) ≡ f x) →
    Modal B
  ◯-rec′-η→Modal s ◯-rec′-η′ =
    Stable→left-inverse→Modal
      s
      (λ x →
         s (η x)            ≡⟨ sym ◯-rec′-η ⟩
         ◯-rec′ s id (η x)  ≡⟨ ◯-rec′-η′ ⟩∎
         x                  ∎)

  abstract

    -- A binary variant of ◯-elim.

    ◯-elim₂ :
      {P : ◯ A → ◯ B → Type a} →
      (∀ x y → Modal (P x y)) →
      ((x : A) (y : B) → P (η x) (η y)) →
      ((x : ◯ A) (y : ◯ B) → P x y)
    ◯-elim₂ {P = P} m f x y =                      $⟨ ◯-elim
                                                        {P = uncurry P ∘ _≃_.to ◯×}
                                                        (uncurry m ∘ _≃_.to ◯×)
                                                        (λ (x , y) → subst (uncurry P) (sym ◯×-η) (f x y))
                                                        (_≃_.from ◯× (x , y)) ⟩
      uncurry P (_≃_.to ◯× (_≃_.from ◯× (x , y)))  →⟨ subst (uncurry P) (_≃_.right-inverse-of ◯× _) ⟩□
      P x y                                        □

    -- A "computation rule" for ◯-elim₂.

    ◯-elim₂-η :
      Extensionality a a →
      ◯-elim₂ m f (η x) (η y) ≡ f x y
    ◯-elim₂-η {m = m} {f = f} {x = x} {y = y} ext =
      let P = _ in

      subst (uncurry P) (_≃_.right-inverse-of ◯× (η x , η y))
        (◯-elim
           (uncurry m ∘ _≃_.to ◯×)
           (λ (x , y) → subst (uncurry P) (sym ◯×-η) (f x y))
           (_≃_.from ◯× (η x , η y)))                              ≡⟨ (cong (subst _ _) $
                                                                       cong (flip (◯-elim (uncurry m ∘ _≃_.to ◯×)) _) $
                                                                       apply-ext ext λ p →
                                                                       cong (flip (subst _) _) $ cong sym $ cong (_$ p) $ sym $
                                                                       _≃_.left-inverse-of (Eq.extensionality-isomorphism ext) _) ⟩
      subst (uncurry P) (_≃_.right-inverse-of ◯× (η x , η y))
        (◯-elim
           (uncurry m ∘ _≃_.to ◯×)
           (subst (uncurry P) (sym (ext⁻¹ ◯×-η′ _)) ∘ uncurry f)
           (_≃_.from ◯× (η x , η y)))                              ≡⟨ elim¹
                                                                        (λ {g} (eq : _≃_.to ◯× ∘ η ≡ g) →
                                                                           (f : ∀ p → uncurry P (g p)) →
                                                                           subst (uncurry P) (_≃_.right-inverse-of ◯× (g (x , y)))
                                                                             (◯-elim
                                                                                (uncurry m ∘ _≃_.to ◯×)
                                                                                (subst (uncurry P) (sym (ext⁻¹ {f = _≃_.to ◯× ∘ η} eq _)) ∘ f)
                                                                                (_≃_.from ◯× (g (x , y)))) ≡
                                                                           f (x , y))
                                                                        (λ f →
        subst (uncurry P)
          (_≃_.right-inverse-of ◯× (_≃_.to ◯× (η (x , y))))
          (◯-elim
             (uncurry m ∘ _≃_.to ◯×)
             (subst (uncurry P)
                (sym (ext⁻¹ {f = _≃_.to ◯× ∘ η} (refl _) _)) ∘
              f)
             (_≃_.from ◯× (_≃_.to ◯× (η (x , y)))))                        ≡⟨ (cong (subst _ _) $ cong (flip (◯-elim _) _) $
                                                                               apply-ext ext λ _ →
                                                                               trans (cong (flip (subst _) _) $
                                                                                      trans (cong sym $ ext⁻¹-refl _)
                                                                                      sym-refl) $
                                                                               subst-refl _ _) ⟩
        subst (uncurry P)
          (_≃_.right-inverse-of ◯× (_≃_.to ◯× (η (x , y))))
          (◯-elim
             (uncurry m ∘ _≃_.to ◯×)
             f
             (_≃_.from ◯× (_≃_.to ◯× (η (x , y)))))                        ≡⟨ cong (flip (subst _) _) $ sym $
                                                                              _≃_.left-right-lemma ◯× _ ⟩
        subst (uncurry P)
          (cong (_≃_.to ◯×) (_≃_.left-inverse-of ◯× (η (x , y))))
          (◯-elim
             (uncurry m ∘ _≃_.to ◯×)
             f
             (_≃_.from ◯× (_≃_.to ◯× (η (x , y)))))                        ≡⟨ elim₁
                                                                                (λ {p} (eq : p ≡ η (x , y)) →
                                                                                   subst (uncurry P)
                                                                                     (cong (_≃_.to ◯×) eq)
                                                                                     (◯-elim (uncurry m ∘ _≃_.to ◯×) f p) ≡
                                                                                   f (x , y))
                                                                                (
          subst (uncurry P)
            (cong (_≃_.to ◯×) (refl _))
            (◯-elim (uncurry m ∘ _≃_.to ◯×) f (η (x , y)))                       ≡⟨ trans (cong (flip (subst _) _) $
                                                                                           cong-refl _) $
                                                                                    subst-refl _ _ ⟩

          ◯-elim (uncurry m ∘ _≃_.to ◯×) f (η (x , y))                           ≡⟨ ◯-elim-η ⟩∎

          f (x , y)                                                              ∎)
                                                                                _ ⟩∎
        f (x , y)                                                          ∎)
                                                                        _ _ ⟩∎
      f x y                                                        ∎
      where
      ◯×-η′ : _≃_.to (◯× {A = A} {B = B}) ∘ η ≡ Σ-map η η
      ◯×-η′ = apply-ext ext λ _ → ◯×-η

    -- A binary variant of ◯-rec.

    ◯-rec₂ : Modal C → (A → B → C) → (◯ A → ◯ B → C)
    ◯-rec₂ m f x y = ◯-rec m (uncurry f) (_≃_.from ◯× (x , y))

    -- A "computation rule" for ◯-rec₂.

    ◯-rec₂-η : ◯-rec₂ m f (η x) (η y) ≡ f x y
    ◯-rec₂-η {m = m} {f = f} {x = x} {y = y} =
      ◯-rec m (uncurry f) (_≃_.from ◯× (η x , η y))  ≡⟨ cong (◯-rec _ _) ◯×⁻¹-η ⟩
      ◯-rec m (uncurry f) (η (x , y))                ≡⟨ ◯-rec-η ⟩∎
      f x y                                          ∎

  ----------------------------------------------------------------------
  -- A lemma related to h-levels

  -- If A is a proposition, then ◯ A is a proposition.
  --
  -- See also Contractible→Connected below.

  Is-proposition→Is-proposition-◯ :
    Is-proposition A → Is-proposition (◯ A)
  Is-proposition→Is-proposition-◯ {A = A} prop =
    ◯-elim₂
      (λ _ _ → Separated-◯ _ _)
      (λ x y →
         η x  ≡⟨ cong η $ prop x y ⟩∎
         η y  ∎)

  ----------------------------------------------------------------------
  -- Commuting with Σ

  -- I did not take the definitions and lemmas in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code.

  private abstract

    -- A lemma used in the implementation of ◯Ση≃Σ◯◯.

    Modal-Σ◯◯ : Modal (Σ (◯ A) (◯ ∘ P))
    Modal-Σ◯◯ = Modal-Σ Modal-◯ λ _ → Modal-◯

  -- ◯ commutes with Σ in a certain way (assuming function
  -- extensionality).
  --
  -- This lemma is due to Felix Cherubini.
  --
  -- See also Modality.Very-modal.◯Ση≃Σ◯◯.

  ◯Ση≃Σ◯◯ : ◯ (Σ A (P ∘ η)) ↝[ a ∣ a ] Σ (◯ A) (◯ ∘ P)
  ◯Ση≃Σ◯◯ {A = A} {P = P} =
    generalise-ext?
      (record { to = to; from = from })
      (λ ext → to-from ext , from-to ext)
    where
    abstract
      s′ : (x : ◯ A) → Stable ((y : P x) → ◯ (Σ A (P ∘ η)))
      s′ _ = Stable-Π λ _ → Modal→Stable Modal-◯

      m″ :
        Extensionality a a →
        (x : ◯ A) → Modal ((y : P x) → ◯ (Σ A (P ∘ η)))
      m″ ext _ = Modal-Π ext λ _ → Modal-◯

      s′-≡ : ∀ ext → s′ ≡ Modal→Stable ∘ m″ ext
      s′-≡ ext =
        apply-ext ext λ _ →
        Stable-Π (λ _ → Modal→Stable Modal-◯)     ≡⟨ Stable-Π-Modal-Π ext ⟩∎
        Modal→Stable (Modal-Π ext λ _ → Modal-◯)  ∎

    to : ◯ (Σ A (P ∘ η)) → Σ (◯ A) (◯ ∘ P)
    to = ◯-rec Modal-Σ◯◯ (Σ-map η η)

    from : Σ (◯ A) (◯ ∘ P) → ◯ (Σ A (P ∘ η))
    from =
      Σ (◯ A) (◯ ∘ P)  →⟨ (λ (x , y) → ◯-map (x ,_) y) ⟩
      ◯ (Σ (◯ A) P)    →⟨ ◯-rec Modal-◯ (uncurry $ ◯-elim′ s′ $ curry η) ⟩□
      ◯ (Σ A (P ∘ η))  □

    to-from :
      Extensionality a a →
      ∀ x → to (from x) ≡ x
    to-from ext = uncurry $
      ◯-elim
        (λ _ → Modal-Π ext λ _ →
               Modal→Separated Modal-Σ◯◯ _ _)
        (λ x →
           ◯-elim
             (λ _ → Modal→Separated Modal-Σ◯◯ _ _)
             (λ y →
                to
                  (◯-rec Modal-◯ (uncurry $ ◯-elim′ s′ $ curry η)
                     (◯-map (η x ,_) (η y)))                            ≡⟨ cong to $ cong (◯-rec _ _) ◯-map-η ⟩

                to
                  (◯-rec Modal-◯ (uncurry $ ◯-elim′ s′ $ curry η)
                     (η (η x , y)))                                     ≡⟨ cong to ◯-rec-η ⟩

                to (◯-elim′ s′ (curry η) (η x) y)                       ≡⟨ cong (λ s → to (◯-elim′ s (curry η) (η x) y)) $
                                                                           s′-≡ ext ⟩

                to (◯-elim′ (Modal→Stable ∘ m″ ext) (curry η) (η x) y)  ≡⟨ cong to $ cong (_$ y) ◯-elim′-Modal→Stable-η ⟩

                to (η (x , y))                                          ≡⟨⟩

                ◯-rec Modal-Σ◯◯ (Σ-map η η) (η (x , y))                 ≡⟨ ◯-rec-η ⟩∎

                (η x , η y)                                             ∎))

    from-to :
      Extensionality a a →
      ∀ x → from (to x) ≡ x
    from-to ext =
      ◯-elim
        (λ _ → Separated-◯ _ _)
        (λ (x , y) →
           let f = λ (x , y) → ◯-map (x ,_) y in

           ◯-rec Modal-◯ (uncurry $ ◯-elim′ s′ $ curry η)
             (f (◯-rec Modal-Σ◯◯ (Σ-map η η) (η (x , y))))               ≡⟨ cong (◯-rec _ _) $ cong f ◯-rec-η ⟩

           ◯-rec Modal-◯ (uncurry $ ◯-elim′ s′ $ curry η)
             (◯-map (η x ,_) (η y))                                      ≡⟨ cong (◯-rec _ _) ◯-map-η ⟩

           ◯-rec Modal-◯ (uncurry $ ◯-elim′ s′ $ curry η) (η (η x , y))  ≡⟨ ◯-rec-η ⟩

           ◯-elim′ s′ (curry η) (η x) y                                  ≡⟨ cong (λ s → ◯-elim′ s (curry η) (η x) y) $ s′-≡ ext ⟩

           ◯-elim′ (Modal→Stable ∘ m″ ext) (curry η) (η x) y             ≡⟨ cong (_$ y) ◯-elim′-Modal→Stable-η ⟩∎

           η (x , y)                                                     ∎)

  -- A definition of what it means for the modality to "commute with
  -- Σ".

  Commutes-with-Σ : Type (lsuc a)
  Commutes-with-Σ =
    {A : Type a} {P : ◯ A → Type a} →
    Is-equivalence (◯Ση≃Σ◯◯ {A = A} {P = P} _)

  -- If function extensionality holds, then the modality commutes with
  -- Σ.
  --
  -- See also Modality.Very-modal.commutes-with-Σ.

  commutes-with-Σ :
    Extensionality a a →
    Commutes-with-Σ
  commutes-with-Σ ext = _≃_.is-equivalence $ ◯Ση≃Σ◯◯ ext

  -- Commutes-with-Σ is a proposition (assuming function
  -- extensionality).

  Commutes-with-Σ-propositional :
    Extensionality (lsuc a) (lsuc a) →
    Is-proposition Commutes-with-Σ
  Commutes-with-Σ-propositional ext =
    implicit-Π-closure ext 1 λ _ →
    implicit-Π-closure (lower-extensionality lzero _ ext) 1 λ _ →
    Is-equivalence-propositional (lower-extensionality _ _ ext)

  ----------------------------------------------------------------------
  -- Some variants of Π◯◯≃Π◯η

  -- I did not take the lemmas in this section from "Modalities in
  -- Homotopy Type Theory" or the corresponding Coq code.

  -- Some variants of Π◯◯≃Π◯η, stated using stability.

  Π◯≃Πη :
    Extensionality? ⌊ k ⌋-sym a a →
    (∀ x → Stable-[ ⌊ k ⌋-sym ] (P x)) →
    ((x : ◯ A) → P x) ↝[ ⌊ k ⌋-sym ] ((x : A) → P (η x))
  Π◯≃Πη {A = A} {P = P} ext s =
    ((x : ◯ A) → P x)        ↝⟨ ∀-cong ext (inverse ∘ s) ⟩
    ((x : ◯ A) → ◯ (P x))    ↝⟨ Π◯◯≃Π◯η ext ⟩
    ((x : A) → ◯ (P (η x)))  ↝⟨ ∀-cong ext (s ∘ η) ⟩□
    ((x : A) → P (η x))      □

  Π◯↝Πη :
    (∀ {k} → Extensionality? k a a → ∀ x → Stable-[ k ] (P x)) →
    ((x : ◯ A) → P x) ↝[ a ∣ a ] ((x : A) → P (η x))
  Π◯↝Πη s = generalise-ext?′
    (Π◯≃Πη _ (s _))
    (λ ext → Π◯≃Πη ext (s ext))
    (λ ext → Π◯≃Πη E.[ ext ] (s E.[ ext ]))

  Π◯⇔Πη :
    (∀ x → Stable (P x)) →
    ((x : ◯ A) → P x) ⇔ ((x : A) → P (η x))
  Π◯⇔Πη s = Π◯≃Πη _ (Stable→Stable-⇔ ∘ s)

  -- Two simplification rules for Π◯≃Πη.

  Π◯≃Πη-η :
    ∀ ext s (f : ∀ x → P x) →
    _≃_.to (Π◯≃Πη ext s) f x ≡ f (η x)
  Π◯≃Πη-η {x = x} ext s f =
    _≃_.to (Π◯≃Πη ext s) f x                         ≡⟨⟩
    _≃_.to (s (η x)) (_≃_.from (s (η x)) (f (η x)))  ≡⟨ _≃_.right-inverse-of (s (η x)) _ ⟩∎
    f (η x)                                          ∎

  Π◯≃Πη⁻¹-η :
    ∀ ext (s : ∀ x → Stable-[ equivalence ] (P x)) →
    _≃_.from (Π◯≃Πη {P = P} ext s) f (η x) ≡ f x
  Π◯≃Πη⁻¹-η {P = P} {f = f} {x = x} ext s =
    _≃_.from (Π◯≃Πη ext s) f (η x)               ≡⟨⟩

    _≃_.to (s (η x))
      (◯-elim
         {P = ◯ ∘ P}
         (λ _ → Modal-◯)
         (λ x → _≃_.from (s (η x)) (f x))
         (η x))                                  ≡⟨ cong (_≃_.to (s (η x))) ◯-elim-η ⟩

    _≃_.to (s (η x)) (_≃_.from (s (η x)) (f x))  ≡⟨ _≃_.right-inverse-of (s (η x)) _ ⟩∎

    f x                                          ∎

  ----------------------------------------------------------------------
  -- Map-like lemmas for Modal and Separated

  -- If there is an embedding from B to A, and A is separated, then B
  -- is separated.
  --
  -- This follows from one part of Remark 2.16 (2) from "Localization
  -- in homotopy type theory" by Christensen, Opie, Rijke and
  -- Scoccola.
  --
  -- I based the proof on that of in_SepO_embedding, implemented by
  -- Mike Shulman in the file Separated.v in (one version of) the Coq
  -- HoTT library.

  Embedding→Separated→Separated :
    Embedding B A → Separated A → Separated B
  Embedding→Separated→Separated B↣A s x y =
                                                     $⟨ s _ _ ⟩
    Modal (Embedding.to B↣A x ≡ Embedding.to B↣A y)  →⟨ Modal-respects-≃ (inverse $ Embedding.equivalence B↣A) ⟩□
    Modal (x ≡ y)                                    □

  -- I did not take the remaining results in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code.

  -- Modal respects split surjections.

  Modal-respects-↠ : A ↠ B → Modal A → Modal B
  Modal-respects-↠ {A = A} {B = B} A↠B m =
    Stable→left-inverse→Modal
      (◯ B  →⟨ ◯-map (_↠_.from A↠B) ⟩
       ◯ A  →⟨ η⁻¹ m ⟩
       A    →⟨ _↠_.to A↠B ⟩□
       B    □)
      (λ x →
         _↠_.to A↠B (η⁻¹ m (◯-map (_↠_.from A↠B) (η x)))  ≡⟨ cong (_↠_.to A↠B ∘ η⁻¹ _) ◯-map-η ⟩
         _↠_.to A↠B (η⁻¹ m (η (_↠_.from A↠B x)))          ≡⟨ cong (_↠_.to A↠B) η⁻¹-η ⟩
         _↠_.to A↠B (_↠_.from A↠B x)                      ≡⟨ _↠_.right-inverse-of A↠B x ⟩∎
         x                                                ∎)

  -- A generalisation of Modal-respects-↠.
  --
  -- The case for 1 is one part of Remark 2.16 (2) from "Localization
  -- in homotopy type theory" by Christensen, Opie, Rijke and
  -- Scoccola.

  Modal-respects-↠ⁿ :
    ∀ n →
    A ↠ B →
    For-iterated-equality n Modal A →
    For-iterated-equality n Modal B
  Modal-respects-↠ⁿ n =
    For-iterated-equality-cong-→ n Modal-respects-↠

  ----------------------------------------------------------------------
  -- Lemmas related to Separated

  -- I did not take the lemmas in this section from "Modalities in
  -- Homotopy Type Theory" or the corresponding Coq code (but perhaps
  -- something similar can be found there).

  -- Propositions are separated.
  --
  -- This is Remark 2.16 (3) from "Localization in homotopy type
  -- theory" by Christensen, Opie, Rijke and Scoccola.

  Is-proposition→Separated : Is-proposition A → Separated A
  Is-proposition→Separated {A = A} prop =
    Embedding→Separated→Separated
      emb
      (Modal→Separated Modal-⊤)
    where
    emb : Embedding A (↑ a ⊤)
    emb = record
      { to           = _
      ; is-embedding = λ x y →
          _≃_.is-equivalence $
          Eq.↔→≃
            _
            (λ _ → prop x y)
            (λ _ → H-level.mono₁ 1
                     (H-level.mono₁ 0 (↑-closure 0 ⊤-contractible))
                     _ _)
            (λ _ → H-level.mono₁ 1 prop _ _)
      }

  -- If A is separated, then W A P is separated (assuming function
  -- extensionality).

  Separated-W :
    {P : A → Type a} →
    Extensionality a a →
    Separated A →
    Separated (W A P)
  Separated-W {A = A} {P = P} ext s = λ x y →
    Stable→left-inverse→Modal
      (Stable-≡-W   x y)
      (Stable-≡-W-η x y)
    where
    head-lemma : sup x f ≡ sup y g → x ≡ y
    head-lemma = proj₁ ∘ Σ-≡,≡←≡ ∘ cong (_↔_.to W-unfolding)

    tail-lemma :
      (eq : sup x f ≡ sup y g) →
      subst (λ x → P x → W A P) (head-lemma eq) f ≡ g
    tail-lemma = proj₂ ∘ Σ-≡,≡←≡ ∘ cong (_↔_.to W-unfolding)

    heads : ◯ (_≡_ {A = W A P} (sup x f) (sup y g)) → x ≡ y
    heads {x = x} {f = f} {y = y} {g = g} =
      ◯ (sup x f ≡ sup y g)  →⟨ ◯-map head-lemma ⟩
      ◯ (x ≡ y)              →⟨ Modal→Stable (s _ _) ⟩□
      x ≡ y                  □

    heads-η : heads (η eq) ≡ head-lemma eq
    heads-η =
      trans (cong (Modal→Stable _) ◯-map-η) $
      Modal→Stable-η

    tails :
      (eq : ◯ (sup x f ≡ sup y g)) →
      ◯ (subst (λ x → P x → W A P) (heads eq) f z ≡
         g z)
    tails {f = f} {g = g} {z = z} =
      ◯-elim
        (λ _ → Modal-◯)
        (λ eq → η (cong (_$ z) (
           subst (λ x → P x → W A P) (heads (η eq)) f   ≡⟨ cong (λ eq → subst (λ x → P x → W A P) eq f) heads-η ⟩
           subst (λ x → P x → W A P) (head-lemma eq) f  ≡⟨ tail-lemma eq ⟩∎
           g                                            ∎)))

    tails-η :
      (eq : sup x f ≡ sup y g) →
      tails {z = z} (η eq) ≡
      η (cong (_$ z) $
         trans (cong (λ eq → subst (λ x → P x → W A P) eq f) heads-η) $
         tail-lemma eq)
    tails-η _ = ◯-elim-η

    Stable-≡-W : For-iterated-equality 1 Stable (W A P)
    Stable-≡-W (sup x f) (sup y g) eq =
      cong (uncurry sup) $
      Σ-≡,≡→≡
        (heads eq)
        (apply-ext ext λ z →
           subst (λ x → P x → W A P) (heads eq) f z  ≡⟨ Stable-≡-W _ (g z) (tails eq) ⟩∎
           g z                                       ∎)

    Stable-≡-W-η :
      (x y : W A P) (eq : x ≡ y) →
      Stable-≡-W x y (η eq) ≡ eq
    Stable-≡-W-η (sup x f) (sup y g) eq =
      cong (uncurry sup)
        (Σ-≡,≡→≡ (heads (η eq))
           (apply-ext ext λ z →
            Stable-≡-W _ (g z) (tails (η eq))))                        ≡⟨ (cong (λ f →
                                                                                   cong (uncurry sup)
                                                                                     (Σ-≡,≡→≡ (heads (η eq))
                                                                                        (apply-ext ext f))) $
                                                                           apply-ext ext λ _ →
                                                                           cong (Stable-≡-W _ (g _)) $
                                                                           tails-η eq) ⟩
      cong (uncurry sup)
        (Σ-≡,≡→≡ (heads (η eq))
           (apply-ext ext λ z →
            Stable-≡-W _ (g z)
              (η (cong (_$ z) $
                  trans (cong (λ eq → subst (λ x → P x → W A P) eq f)
                           heads-η) $
                  tail-lemma eq))))                                    ≡⟨ (cong (λ f →
                                                                                   cong (uncurry sup)
                                                                                     (Σ-≡,≡→≡ (heads (η eq))
                                                                                        (apply-ext ext f))) $
                                                                           apply-ext ext λ z →
                                                                           Stable-≡-W-η _ (g z) _) ⟩
      cong (uncurry sup)
        (Σ-≡,≡→≡ (heads (η eq))
           (apply-ext ext λ z →
            cong (_$ z) $
            trans (cong (λ eq → subst (λ x → P x → W A P) eq f)
                     heads-η) $
            tail-lemma eq))                                            ≡⟨ cong (cong (uncurry sup) ∘ Σ-≡,≡→≡ (heads (η eq))) $
                                                                          trans (ext-cong ext) $
                                                                          sym $ cong-id _ ⟩
      cong (uncurry sup)
        (Σ-≡,≡→≡ (heads (η eq))
           (trans (cong (λ eq → subst (λ x → P x → W A P) eq f)
                     heads-η) $
            tail-lemma eq))                                            ≡⟨ elim₁
                                                                            (λ {p} eq′ →
                                                                               cong (uncurry sup)
                                                                                 (Σ-≡,≡→≡ p
                                                                                    (trans (cong (λ eq → subst (λ x → P x → W A P) eq f) eq′) $
                                                                                     tail-lemma eq)) ≡
                                                                               cong (uncurry sup) (Σ-≡,≡→≡ (head-lemma eq) (tail-lemma eq)))
                                                                            (cong (cong (uncurry sup) ∘ Σ-≡,≡→≡ (head-lemma eq)) $
                                                                             trans (cong (flip trans _) $ cong-refl _) $
                                                                             trans-reflˡ _)
                                                                            _ ⟩

      cong (uncurry sup) (Σ-≡,≡→≡ (head-lemma eq) (tail-lemma eq))     ≡⟨ cong (cong (uncurry sup)) $
                                                                          _↔_.right-inverse-of Bijection.Σ-≡,≡↔≡ _ ⟩

      cong (uncurry sup) (cong (_↔_.to W-unfolding) eq)                ≡⟨⟩

      cong (_↔_.from W-unfolding) (cong (_↔_.to W-unfolding) eq)       ≡⟨ cong-∘ _ _ _ ⟩

      cong (_↔_.from W-unfolding ∘ _↔_.to W-unfolding) eq              ≡⟨ sym $
                                                                          trans-[trans]-sym _ _ ⟩
      trans
        (trans (cong (_↔_.from W-unfolding ∘ _↔_.to W-unfolding) eq)
           (_↔_.left-inverse-of W-unfolding (sup y g)))
        (sym (_↔_.left-inverse-of W-unfolding (sup y g)))              ≡⟨ cong (flip trans _) $
                                                                          naturality (_↔_.left-inverse-of W-unfolding) ⟩
      trans
        (trans (_↔_.left-inverse-of W-unfolding (sup x f))
           (cong id eq))
        (sym (_↔_.left-inverse-of W-unfolding (sup y g)))              ≡⟨⟩

      trans (trans (refl _) (cong id eq)) (sym (refl _))               ≡⟨ trans (cong₂ trans
                                                                                   (trans (trans-reflˡ _) $
                                                                                    sym $ cong-id _)
                                                                                   sym-refl) $
                                                                          trans-reflʳ _ ⟩∎
      eq                                                               ∎

  ----------------------------------------------------------------------
  -- Flattening lemmas

  -- Some flattening lemmas.
  --
  -- I did not take these lemmas from "Modalities in Homotopy Type
  -- Theory" or the corresponding Coq code.

  flatten-→ :
    (F : (Type a → Type a) → Type a) →
    (F ◯ → ◯ (F id)) →
    ◯ (F ◯) → ◯ (F id)
  flatten-→ _ f = ◯-rec Modal-◯ f

  flatten-⇔ :
    (F : (Type a → Type a) → Type a) →
    (∀ {G H} → (∀ {A} → G A → H A) → F G → F H) →
    (F ◯ → ◯ (F id)) →
    ◯ (F ◯) ⇔ ◯ (F id)
  flatten-⇔ F map f = record
    { to   = flatten-→ F f
    ; from = ◯-map (map η)
    }

  private

    module Flatten
      {F : (Type a → Type a) → Type a}
      (map : ∀ {G H} → (∀ {A} → G A → H A) → F G → F H)
      {f : F ◯ → ◯ (F id)}
      where

      open _⇔_ (flatten-⇔ F map f)

      to-from :
        (∀ x → f (map η x) ≡ η x) →
        ∀ x → to (from x) ≡ x
      to-from f-map =
         ◯-elim
           (λ _ → Separated-◯ _ _)
           (λ x →
              ◯-rec Modal-◯ f (◯-map (map η) (η x))  ≡⟨ cong (◯-rec Modal-◯ f) ◯-map-η ⟩
              ◯-rec Modal-◯ f (η (map η x))          ≡⟨ ◯-rec-η ⟩
              f (map η x)                            ≡⟨ f-map x ⟩∎
              η x                                    ∎)

      from-to :
        (∀ x → ◯-map (map η) (f x) ≡ η x) →
        ∀ x → from (to x) ≡ x
      from-to map-f =
        ◯-elim
          (λ _ → Separated-◯ _ _)
          (λ x →
             ◯-map (map η) (◯-rec Modal-◯ f (η x))  ≡⟨ cong (◯-map (map η)) ◯-rec-η ⟩
             ◯-map (map η) (f x)                    ≡⟨ map-f x ⟩∎
             η x                                    ∎)

  flatten-≃ :
    (F : (Type a → Type a) → Type a) →
    (map : ∀ {G H} → (∀ {A} → G A → H A) → F G → F H) →
    (f : F ◯ → ◯ (F id)) →
    (∀ x → f (map η x) ≡ η x) →
    (∀ x → ◯-map (map η) (f x) ≡ η x) →
    ◯ (F ◯) ≃ ◯ (F id)
  flatten-≃ _ map f f-map map-f = Eq.↔→≃
    (_⇔_.to equiv)
    (_⇔_.from equiv)
    (Flatten.to-from map f-map)
    (Flatten.from-to map map-f)
    where
    equiv = flatten-⇔ _ map f

  flatten-↝ :
    (F : (Type a → Type a) → Type a) →
    (map : ∀ {G H} → (∀ {A} → G A → H A) → F G → F H) →
    (f : F ◯ → ◯ (F id)) →
    (Extensionality a a →
     (∀ x → f (map η x) ≡ η x) ×
     (∀ x → ◯-map (map η) (f x) ≡ η x)) →
    ◯ (F ◯) ↝[ a ∣ a ] ◯ (F id)
  flatten-↝ _ map f hyp = generalise-ext?
    (flatten-⇔ _ map f)
    (λ ext →
         Flatten.to-from map (hyp ext .proj₁)
       , Flatten.from-to map (hyp ext .proj₂))

  -- ◯ A is equivalent to ◯ (◯ A).

  ◯≃◯◯ : ◯ A ≃ ◯ (◯ A)
  ◯≃◯◯ {A = A} = Eq.↔→≃
    η
    (◯-rec Modal-◯ id)
    (◯-elim
       (λ _ → Separated-◯ _ _)
       (λ x →
          η (◯-rec Modal-◯ id (η x))  ≡⟨ cong η ◯-rec-η ⟩∎
          η x                         ∎))
    (λ _ → ◯-rec-η)

  -- ◯ (Σ A (◯ ∘ P)) is equivalent to ◯ (Σ A P).

  ◯Σ◯≃◯Σ :
    {A : Type a} {P : A → Type a} →
    ◯ (Σ A (◯ ∘ P)) ≃ ◯ (Σ A P)
  ◯Σ◯≃◯Σ {A = A} {P = P} =
    flatten-≃
      (λ F → Σ A (F ∘ P))
      (λ f → Σ-map id f)
      (λ (x , y) → ◯-map (x ,_) y)
      (λ _ → ◯-map-η)
      (uncurry λ x →
       ◯-elim
         (λ _ → Separated-◯ _ _)
         (λ y →
            ◯-map (Σ-map id η) (◯-map (x ,_) (η y))  ≡⟨ cong (◯-map (Σ-map id η)) ◯-map-η ⟩
            ◯-map (Σ-map id η) (η (x , y))           ≡⟨ ◯-map-η ⟩∎
            η (x , η y)                              ∎))

  -- I did not take the remaining definitions in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code.

  mutual

    -- If ◯ (∀ x → Modal (P x)) holds, then ◯ ((x : A) → ◯ (P x)) is
    -- equivalent to ◯ ((x : A) → P x) (assuming function
    -- extensionality).

    ◯Π◯≃◯Π :
      {A : Type a} {P : A → Type a} →
      ◯ (∀ x → Modal (P x)) →
      ◯ ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ ((x : A) → P x)
    ◯Π◯≃◯Π m = ◯Π◯≃◯Π′ (◯-map (Modal→Stable ∘_) m) (λ _ → m , refl _)

    -- A variant of ◯Π◯≃◯Π.

    ◯Π◯≃◯Π′ :
      {A : Type a} {P : A → Type a}
      (s : ◯ (∀ x → Stable (P x))) →
      (Extensionality a a →
       ∃ λ (m : ◯ (∀ x → Modal (P x))) →
         ◯-map (Modal→Stable ∘_) m ≡ s) →
      ◯ ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ ((x : A) → P x)
    ◯Π◯≃◯Π′ {A = A} {P = P} s m =
      flatten-↝
        (λ F → (x : A) → F (P x))
        (λ f g x → f (g x))
        (λ f → ◯-map (λ s x → s x (f x)) s)
        (λ ext →
             (λ f →
                ◯-elim₂
                  {P = λ s (m : ◯ (∀ x → Modal (P x))) →
                         ◯-map (Modal→Stable ∘_) m ≡ s →
                         ◯-map (λ s x → s x (η (f x))) s ≡ η f}
                  (λ _ _ →
                     Modal-Π ext λ _ →
                     Separated-◯ _ _)
                  (λ s m eq →
                     ◯-map (λ s x → s x (η (f x))) (η s)     ≡⟨ cong (◯-map _) $ sym
                                                                eq ⟩
                     ◯-map (λ s x → s x (η (f x)))
                       (◯-map (Modal→Stable ∘_) (η m))       ≡⟨ trans (cong (◯-map _) ◯-map-η) $
                                                                ◯-map-η ⟩

                     η (λ x → Modal→Stable (m x) (η (f x)))  ≡⟨ (cong η $ apply-ext ext λ _ →
                                                                 Modal→Stable-η) ⟩∎
                     η f                                     ∎)
                  _ (m ext .proj₁) (m ext .proj₂))
           , (λ f →
                ◯-map (λ g x → η (g x)) (◯-map (λ s x → s x (f x)) s)  ≡⟨ sym ◯-map-∘ ⟩

                ◯-map (λ s x → η (s x (f x))) s                        ≡⟨ ◯-elim₂
                                                                            {P = λ s (m : ◯ (∀ x → Modal (P x))) →
                                                                                   ◯-map (Modal→Stable ∘_) m ≡ s →
                                                                                   ◯-map (λ s x → η (s x (f x))) s ≡ η f}
                                                                            (λ _ _ →
                                                                               Modal-Π ext λ _ →
                                                                               Separated-◯ _ _)
                                                                            (λ s m eq →
                  ◯-map (λ s x → η (s x (f x))) (η s)                          ≡⟨ cong (◯-map _) $ sym
                                                                                  eq ⟩
                  ◯-map (λ s x → η (s x (f x)))
                    (◯-map (Modal→Stable ∘_) (η m))                            ≡⟨ trans (cong (◯-map _) ◯-map-η) $
                                                                                  ◯-map-η ⟩

                  η (λ x → η (Modal→Stable (m x) (f x)))                       ≡⟨ (cong η $ apply-ext ext λ x →
                                                                                   _≃_.right-inverse-of (Modal→≃◯ (m x)) _) ⟩∎
                  η f                                                          ∎)
                                                                            _ (m ext .proj₁) (m ext .proj₂) ⟩∎
                η f                                                    ∎))

  -- Two "computation rules" for ◯Π◯≃◯Π′.

  ◯Π◯≃◯Π′-η :
    (m : Extensionality a a →
         ∃ λ (m : ◯ (∀ x → Modal (P x))) →
           ◯-map (Modal→Stable ∘_) m ≡ η s) →
    ◯Π◯≃◯Π′ (η s) m _ (η f) ≡ η (λ x → s x (f x))
  ◯Π◯≃◯Π′-η {s = s} {f = f} m =
    ◯Π◯≃◯Π′ (η s) m _ (η f)                                      ≡⟨⟩
    ◯-rec Modal-◯ (λ f → ◯-map (λ s x → s x (f x)) (η s)) (η f)  ≡⟨ ◯-rec-η ⟩
    ◯-map (λ s x → s x (f x)) (η s)                              ≡⟨ ◯-map-η ⟩∎
    η (λ x → s x (f x))                                          ∎

  ◯Π◯≃◯Π′⁻¹-η :
    (m : Extensionality a a →
         ∃ λ (m : ◯ (∀ x → Modal (P x))) →
           ◯-map (Modal→Stable ∘_) m ≡ s) →
    _⇔_.from (◯Π◯≃◯Π′ s m _) (η f) ≡ η (η ∘ f)
  ◯Π◯≃◯Π′⁻¹-η {s = s} {f = f} m =
    _⇔_.from (◯Π◯≃◯Π′ s m _) (η f)  ≡⟨⟩
    ◯-map (λ g x → η (g x)) (η f)   ≡⟨ ◯-map-η ⟩∎
    η (η ∘ f)                       ∎

  -- Two "computation rules" for ◯Π◯≃◯Π.

  ◯Π◯≃◯Π-η :
    ◯Π◯≃◯Π (η m) _ (η f) ≡ η (λ x → Modal→Stable (m x) (f x))
  ◯Π◯≃◯Π-η {m = m} {f = f} =
    ◯Π◯≃◯Π (η m) _ (η f)                                                  ≡⟨⟩
    ◯Π◯≃◯Π′ (◯-map (Modal→Stable ∘_) (η m)) (λ _ → η m , refl _) _ (η f)  ≡⟨ elim¹
                                                                               (λ {x} eq →
                                                                                  ◯Π◯≃◯Π′ (◯-map (Modal→Stable ∘_) (η m))
                                                                                    (λ _ → η m , refl _) _ (η f) ≡
                                                                                  ◯Π◯≃◯Π′ x (λ _ → η m , eq) _ (η f))
                                                                               (refl _)
                                                                               ◯-map-η ⟩
    ◯Π◯≃◯Π′ (η (Modal→Stable ∘ m)) (λ _ → η m , ◯-map-η) _ (η f)          ≡⟨ ◯Π◯≃◯Π′-η (λ _ → η m , ◯-map-η) ⟩∎
    η (λ x → Modal→Stable (m x) (f x))                                    ∎

  ◯Π◯≃◯Π⁻¹-η :
    (m : ◯ (∀ x → Modal (P x))) →
    _⇔_.from (◯Π◯≃◯Π m _) (η f) ≡ η (η ∘ f)
  ◯Π◯≃◯Π⁻¹-η m = ◯Π◯≃◯Π′⁻¹-η (λ _ → m , refl _)

  ----------------------------------------------------------------------
  -- Some results related to connectedness

  -- ◯ -Connected_ respects split surjections.

  Connected-map : A ↠ B → ◯ -Connected A → ◯ -Connected B
  Connected-map {A = A} {B = B} A↠B =
    Contractible (◯ A)  ↝⟨ H-level.respects-surjection (◯-cong-↠ A↠B) 0 ⟩□
    Contractible (◯ B)  □

  -- ◯ -Connected_ preserves equivalences (assuming function
  -- extensionality).

  Connected-cong :
    Extensionality? k a a →
    A ≃ B → ◯ -Connected A ↝[ k ] ◯ -Connected B
  Connected-cong {A = A} {B = B} ext A≃B =
    Contractible (◯ A)  ↝⟨ H-level-cong ext 0 $ ◯-cong-≃ A≃B ⟩□
    Contractible (◯ B)  □

  -- If f and g are pointwise equal, then ◯ -Connected-→ f and
  -- ◯ -Connected-→ g are equivalent (assuming function
  -- extensionality).

  Connected-→-cong :
    Extensionality? k a a →
    (∀ x → f x ≡ g x) →
    ◯ -Connected-→ f ↝[ k ] ◯ -Connected-→ g
  Connected-→-cong {f = f} {g = g} ext f≡g =
    (∀ y → ◯ -Connected (f ⁻¹ y))  ↝⟨ (∀-cong ext λ _ → Connected-cong ext $ Eq.↔⇒≃ $ Preimage.respects-extensional-equality f≡g) ⟩□
    (∀ y → ◯ -Connected (g ⁻¹ y))  □

  -- Contractible types are ◯-connected.

  Contractible→Connected : Contractible A → ◯ -Connected A
  Contractible→Connected (x , x≡) =
      η x
    , ◯-elim
        (λ _ → Separated-◯ _ _)
        (λ y →
           η x  ≡⟨ cong η (x≡ y) ⟩∎
           η y  ∎)

  -- If f is ◯-connected, then ◯-map f is an equivalence.

  Connected→Is-equivalence-◯-map :
    ◯ -Connected-→ f → Is-equivalence (◯-map f)
  Connected→Is-equivalence-◯-map {f = f} c =
    _≃_.is-equivalence $
    Eq.↔→≃
      _
      (◯-rec Modal-◯ λ y → ◯-map proj₁ (c y .proj₁))
      (◯-elim
         (λ _ → Separated-◯ _ _)
         (λ y →
            ◯-map f
              (◯-rec Modal-◯ (λ y → ◯-map proj₁ (c y .proj₁)) (η y))  ≡⟨ cong (◯-map f) ◯-rec-η ⟩

            ◯-map f (◯-map proj₁ (c y .proj₁))                        ≡⟨ sym ◯-map-∘ ⟩

            ◯-map (f ∘ proj₁) (c y .proj₁)                            ≡⟨⟩

            ◯-map (λ ((x , _) : f ⁻¹ y) → f x) (c y .proj₁)           ≡⟨ ◯-map-cong proj₂ ⟩

            ◯-map (λ _ → y) (c y .proj₁)                              ≡⟨ ◯-map-const ⟩∎

            η y                                                       ∎))
      (◯-elim
         (λ _ → Separated-◯ _ _)
         (λ x →
            ◯-rec Modal-◯ (λ y → ◯-map proj₁ (c y .proj₁))
              (◯-map f (η x))                                         ≡⟨ cong (◯-rec _ _) ◯-map-η ⟩

            ◯-rec Modal-◯ (λ y → ◯-map proj₁ (c y .proj₁)) (η (f x))  ≡⟨ ◯-rec-η ⟩

            ◯-map proj₁ (c (f x) .proj₁)                              ≡⟨ cong (◯-map _) $ c (f x) .proj₂ (η (x , refl _)) ⟩

            ◯-map proj₁ (η (x , refl (f x)))                          ≡⟨ ◯-map-η ⟩∎

            η x                                                       ∎))

  -- The identity function is ◯-connected for each type A.

  Connected-→-id : ◯ -Connected-→ (id {A = A})
  Connected-→-id {A = A} y =
      η (y , refl y)
    , ◯-elim
        (λ _ → Separated-◯ _ _)
        (λ (z , z≡y) →
           η (y , refl y)                     ≡⟨ cong η $
                                                 Σ-≡,≡→≡ (sym z≡y) (
             subst (_≡ y) (sym z≡y) (refl y)       ≡⟨ subst-trans _ ⟩
             trans z≡y (refl y)                    ≡⟨ trans-reflʳ _ ⟩∎
             z≡y                                   ∎) ⟩∎

           η (z , z≡y)                        ∎)

  -- The function η is ◯-connected for each type A.

  Connected-→-η : ◯ -Connected-→ (η {A = A})
  Connected-→-η {A = A} y =
      ◯η⁻¹ y
    , ◯-elim
        (λ _ → Modal→Separated Modal-◯ _ _)
        (lemma y)
    where
    ◯η⁻¹ : ∀ y → ◯ (η ⁻¹ y)
    ◯η⁻¹ = ◯-elim
      (λ _ → Modal-◯)
      (λ x → η (x , refl (η x)))

    lemma =                                                   $⟨ (λ _ → ◯-elim-η) ⟩

      ((x : A) → ◯η⁻¹ (η x) ≡ η (x , refl (η x)))             →⟨ (∀-cong _ λ _ →
                                                                  _⇔_.from $ drop-⊤-left-Π _ $
                                                                  _⇔_.to contractible⇔↔⊤ $
                                                                  other-singleton-contractible _) ⟩
      ((x : A) (p : ∃ λ (y : ◯ A) → η x ≡ y) →
       ◯η⁻¹ (p .proj₁) ≡ η (x , p .proj₂))                    →⟨ (∀-cong _ λ _ → curry) ⟩

      ((x : A) (y : ◯ A) (p : η x ≡ y) → ◯η⁻¹ y ≡ η (x , p))  ↔⟨ Π-comm ⟩

      ((y : ◯ A) (x : A) (p : η x ≡ y) → ◯η⁻¹ y ≡ η (x , p))  →⟨ (∀-cong _ λ _ → uncurry) ⟩□

      ((y : ◯ A) (p : η ⁻¹ y) → ◯η⁻¹ y ≡ η p)                 □

  -- If f is an equivalence and g is ◯-connected, then f ∘ g is
  -- ◯-connected.

  Is-equivalence→Connected-→→Connected-→-∘ :
    Is-equivalence f → ◯ -Connected-→ g → ◯ -Connected-→ (f ∘ g)
  Is-equivalence→Connected-→→Connected-→-∘ {f = f} {g = g} eq =
    (∀ x → ◯ -Connected (g ⁻¹ x))                 →⟨ _∘ _≃_.from equiv ⟩
    (∀ x → ◯ -Connected (g ⁻¹ _≃_.from equiv x))  →⟨ (∀-cong _ λ _ → Connected-cong _ (inverse (to-∘-⁻¹-≃-⁻¹-from equiv))) ⟩□
    (∀ x → ◯ -Connected (f ∘ g ⁻¹ x))             □
    where
    equiv = Eq.⟨ _ , eq ⟩

  -- If m : Modal B, then a function f to B is ◯-connected if and only
  -- if ◯-rec m f is an equivalence.

  Connected-→≃Is-equivalence-◯-rec :
    {f : A → B} →
    (m : Modal B) →
    ◯ -Connected-→ f ↝[ a ∣ a ] Is-equivalence (◯-rec m f)
  Connected-→≃Is-equivalence-◯-rec {f = f} m =
    generalise-ext?-prop
      (record { to = to; from = from })
      (λ ext → Connected-→-propositional ext ◯)
      Is-equivalence-propositional
    where
    to : ◯ -Connected-→ f → Is-equivalence (◯-rec m f)
    to =
      ◯ -Connected-→ f                →⟨ Connected→Is-equivalence-◯-map ⟩

      Is-equivalence (◯-map f)        →⟨ Eq.respects-extensional-equality $
                                         ◯-elim
                                           (λ _ → Separated-◯ _ _)
                                           (λ x →
        ◯-map f (η x)                         ≡⟨ ◯-map-η ⟩
        η (f x)                               ≡⟨ cong η $ sym ◯-rec-η ⟩∎
        η (◯-rec m f (η x))                   ∎) ⟩

      Is-equivalence (η ∘ ◯-rec m f)  →⟨ _⇔_.from (Is-equivalence≃Is-equivalence-∘ˡ (Modal≃Is-equivalence-η _ m) _) ⟩□

      Is-equivalence (◯-rec m f)      □

    from : Is-equivalence (◯-rec m f) → ◯ -Connected-→ f
    from =
      Is-equivalence (◯-rec m f)      →⟨ flip Is-equivalence→Connected-→→Connected-→-∘ Connected-→-η ⟩
      ◯ -Connected-→ (◯-rec m f ∘ η)  →⟨ (Connected-→-cong _ λ _ → ◯-rec-η) ⟩□
      ◯ -Connected-→ f                □

  -- A function between modal types is ◯-connected if and only if it
  -- is an equivalence.

  Connected-→≃Is-equivalence :
    {f : A → B} →
    Modal A → Modal B →
    ◯ -Connected-→ f ↝[ a ∣ a ] Is-equivalence f
  Connected-→≃Is-equivalence {f = f} mA mB ext =
    ◯ -Connected-→ f                 ↝⟨ Connected-→≃Is-equivalence-◯-rec mB ext ⟩
    Is-equivalence (◯-rec mB f)      ↝⟨ Is-equivalence≃Is-equivalence-∘ʳ (Modal≃Is-equivalence-η _ mA) ext ⟩
    Is-equivalence (◯-rec mB f ∘ η)  ↝⟨ (Is-equivalence-cong ext λ _ → ◯-rec-η) ⟩□
    Is-equivalence f                 □

  -- The function η ∘ f is ◯-connected if and only if ◯-map f is an
  -- equivalence.

  Connected-→-η-∘-≃Is-equivalence-◯-map :
    {f : A → B} →
    ◯ -Connected-→ (η ∘ f) ↝[ a ∣ a ] Is-equivalence (◯-map f)
  Connected-→-η-∘-≃Is-equivalence-◯-map {f = f} ext =
    ◯ -Connected-→ (η ∘ f)                  ↝⟨ Connected-→≃Is-equivalence-◯-rec Modal-◯ ext ⟩

    Is-equivalence (◯-rec Modal-◯ (η ∘ f))  ↝⟨ (Is-equivalence-cong ext $
                                                ◯-elim (λ _ → Separated-◯ _ _) λ x →
      ◯-rec Modal-◯ (η ∘ f) (η x)                 ≡⟨ ◯-rec-η ⟩
      η (f x)                                     ≡⟨ sym ◯-map-η ⟩∎
      ◯-map f (η x)                               ∎) ⟩□

    Is-equivalence (◯-map f)                □

  -- If A is ◯-connected, and P x is ◯-connected for all x, then Σ A P
  -- is ◯-connected.

  Connected-Σ :
    ◯ -Connected A → (∀ x → ◯ -Connected (P x)) → ◯ -Connected (Σ A P)
  Connected-Σ {A = A} {P = P} = curry
    (Contractible (◯ A) × ((x : A) → Contractible (◯ (P x)))  ↝⟨ (λ (cA , cP) →
                                                                    Connected-cong _
                                                                      (inverse $ Eq.↔⇒≃ $ drop-⊤-right λ _ →
                                                                       _⇔_.to contractible⇔↔⊤ (cP _))
                                                                      cA) ⟩
     Contractible (◯ (Σ A (◯ ∘ P)))                           ↝⟨ H-level-cong _ 0 ◯Σ◯≃◯Σ ⟩□
     Contractible (◯ (Σ A P))                                 □)

  -- If g is ◯-connected, then f is ◯-connected if and only if f ∘ g
  -- is ◯-connected.

  Connected-→→Connected-→≃Connected-→-∘ :
    ◯ -Connected-→ g →
    ◯ -Connected-→ f ↝[ a ∣ a ] ◯ -Connected-→ (f ∘ g)
  Connected-→→Connected-→≃Connected-→-∘ {g = g} {f = f} c-g ext =
    (∀ z → Contractible (◯ (f ⁻¹ z)))      ↝⟨ (∀-cong ext λ z → H-level-cong ext 0 $ lemma z) ⟩□
    (∀ z → Contractible (◯ (f ∘ g ⁻¹ z)))  □
    where
    lemma = λ z →
      ◯ (f ⁻¹ z)                               ↝⟨ (◯-cong-≃ $ inverse $ Eq.↔⇒≃ $
                                                   drop-⊤-right λ _ →
                                                   _⇔_.to contractible⇔↔⊤ $
                                                   c-g _) ⟩
      ◯ (∃ λ ((y , _) : f ⁻¹ z) → ◯ (g ⁻¹ y))  ↝⟨ ◯Σ◯≃◯Σ ⟩
      ◯ (∃ λ ((y , _) : f ⁻¹ z) → g ⁻¹ y)      ↝⟨ ◯-cong-≃ $ inverse $ ∘⁻¹≃ _ _ ⟩□
      ◯ (f ∘ g ⁻¹ z)                           □

  private

    -- A lemma used in the following two definitions.

    ◯-Σ-map-⁻¹≃◯⁻¹ :
      ∀ {A B : Type a} {P : A → Type a} {Q : B → Type a}
        {f : A → B} {g : ∀ x → P x → Q (f x)} {x y} →
      (∀ x → ◯ -Connected-→ g x) →
      ◯ (Σ-map f (λ {x} → g x) ⁻¹ (x , y)) ≃ ◯ (f ⁻¹ x)
    ◯-Σ-map-⁻¹≃◯⁻¹ {Q = Q} {f = f} {g = g} {x = x} {y = y} c-g =
      ◯ (Σ-map f (λ {x} → g x) ⁻¹ (x , y))                                ↔⟨⟩
      ◯ (∃ λ (x′ , y′) → (f x′ , g x′ y′) ≡ (x , y))                      ↔⟨ ◯-cong-↔ $ inverse Σ-assoc ⟩
      ◯ (∃ λ x′ → ∃ λ y′ → (f x′ , g x′ y′) ≡ (x , y))                    ↔⟨ (◯-cong-↔ $ ∃-cong λ _ → ∃-cong λ _ → inverse
                                                                              Bijection.Σ-≡,≡↔≡) ⟩
      ◯ (∃ λ x′ → ∃ λ y′ → ∃ λ (p : f x′ ≡ x) → subst Q p (g x′ y′) ≡ y)  ↔⟨ ◯-cong-↔ $ Σ-assoc F.∘ (∃-cong λ _ → ∃-comm) ⟩
      ◯ (∃ λ ((x′ , p) : f ⁻¹ x) → subst Q p ∘ g x′ ⁻¹ y)                 ↝⟨ (◯-cong-≃ $ ∃-cong λ _ →
                                                                              to-∘-⁻¹-≃-⁻¹-from (Eq.subst-as-equivalence Q _)) ⟩
      ◯ (∃ λ ((x′ , p) : f ⁻¹ x) → g x′ ⁻¹ subst Q (sym p) y)             ↝⟨ inverse ◯Σ◯≃◯Σ ⟩
      ◯ (∃ λ ((x′ , p) : f ⁻¹ x) → ◯ (g x′ ⁻¹ subst Q (sym p) y))         ↔⟨ (◯-cong-↔ $ drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ $ c-g _ _) ⟩□
      ◯ (f ⁻¹ x)                                                          □

  -- If f is ◯-connected, and g : ∀ x → P x → Q (f x) is pointwise
  -- ◯-connected, then Σ-map {Q = Q} f (λ {x} → g x) is ◯-connected.

  Connected-→-Σ-map :
    {g : ∀ x → P x → Q (f x)} →
    ◯ -Connected-→ f → (∀ x → ◯ -Connected-→ g x) →
    ◯ -Connected-→ Σ-map {Q = Q} f (λ {x} → g x)
  Connected-→-Σ-map {f = f} {g = g} c-f c-g (x , y) =
                                                         $⟨ c-f x ⟩
    Contractible (◯ (f ⁻¹ x))                            →⟨ H-level-cong _ 0 (inverse $ ◯-Σ-map-⁻¹≃◯⁻¹ c-g) ⟩□
    Contractible (◯ (Σ-map f (λ {x} → g x) ⁻¹ (x , y)))  □

  -- If Q x is inhabited for each x, g : ∀ x → P x → Q (f x) is
  -- pointwise ◯-connected, and Σ-map f (λ {x} → g x) is ◯-connected,
  -- then f is ◯-connected.
  --
  -- In Cubical Agda it would have sufficed for Q x to be merely
  -- inhabited for each x, but this module does not use Cubical Agda.

  Connected-→-Σ-map→Connected-→ :
    {g : ∀ x → P x → Q (f x)} →
    (∀ x → Q x) →
    (∀ x → ◯ -Connected-→ g x) →
    ◯ -Connected-→ Σ-map f (λ {x} → g x) →
    ◯ -Connected-→ f
  Connected-→-Σ-map→Connected-→ {f = f} {g = g} q c-g c-f-g x =
                                                           $⟨ c-f-g (x , q x) ⟩
    Contractible (◯ (Σ-map f (λ {x} → g x) ⁻¹ (x , q x)))  →⟨ H-level-cong _ 0 (◯-Σ-map-⁻¹≃◯⁻¹ c-g) ⟩□
    Contractible (◯ (f ⁻¹ x))                              □

  -- Σ-map id (λ {x} → f x) is ◯-connected (for f : ∀ x → P x → Q x)
  -- if and only if f x is ◯-connected for each x.

  Connected-→-Σ-map≃Connected-→ :
    {A : Type a} {P Q : A → Type a} {f : ∀ x → P x → Q x} →
    ◯ -Connected-→ Σ-map id (λ {x} → f x) ↝[ a ∣ a ]
    (∀ x → ◯ -Connected-→ f x)
  Connected-→-Σ-map≃Connected-→ {f = f} ext =
    ◯ -Connected-→ Σ-map id (λ {x} → f x)               ↔⟨⟩
    (∀ p → ◯ -Connected (Σ-map id (λ {x} → f x) ⁻¹ p))  ↝⟨ (∀-cong ext λ _ → Connected-cong ext Σ-map-id-⁻¹≃⁻¹) ⟩
    (∀ p → ◯ -Connected (f (proj₁ p) ⁻¹ proj₂ p))       ↔⟨ currying ⟩
    (∀ x y → ◯ -Connected (f x ⁻¹ y))                   ↔⟨⟩
    (∀ x → ◯ -Connected-→ f x)                          □

  -- If _∘ f is split surjective at certain types, then f is
  -- ◯-connected.

  Split-surjective-∘→Connected-→ :
    {f : A → B} →
    ((P : B → Type a) → (∀ y → Modal (P y)) →
     Split-surjective (_∘ f ⦂ ((∀ y → P y) → (∀ x → P (f x))))) →
    ◯ -Connected-→ f
  Split-surjective-∘→Connected-→ {B = B} {f = f} hyp =
    λ y → inh y , lemma y
    where
    P′ : B → Type a
    P′ y = ◯ (f ⁻¹ y)

    surj :
      Split-surjective
        (_∘ f ⦂ ((∀ y → ◯ (f ⁻¹ y)) → (∀ x → ◯ (f ⁻¹ f x))))
    surj = hyp P′ (λ _ → Modal-◯)

    inh : ∀ y → ◯ (f ⁻¹ y)
    inh = surj (λ x → η (x , refl (f x))) .proj₁

    lemma : ∀ y (p : ◯ (f ⁻¹ y)) → inh y ≡ p
    lemma y =
      ◯-elim
        (λ _ → Separated-◯ _ _)
        (uncurry λ x →
           elim¹
             (λ {y} fx≡y →
                surj (λ x → η (x , refl (f x))) .proj₁ y ≡
                η (x , fx≡y))
             (surj (λ x → η (x , refl (f x))) .proj₁ (f x)  ≡⟨ ext⁻¹ (surj (λ x → η (x , refl (f x))) .proj₂) x ⟩∎
              η (x , refl (f x))                            ∎))

  -- One can express ◯ -Connected-→ f in several equivalent ways
  -- (assuming function extensionality).

  Equivalent-Connected-→ :
    {f : A → B} →
    Extensionality a a →
    Equivalent? (lsuc a) a
      ( ◯ -Connected-→ f

      , ((P : B → Type a) → (∀ y → Modal (P y)) →
         Is-equivalence (_∘ f ⦂ ((∀ y → P y) → (∀ x → P (f x)))))

      , ((P : B → Type a) → (∀ y → Modal (P y)) →
         Split-surjective (_∘ f ⦂ ((∀ y → P y) → (∀ x → P (f x)))))
      )
  Equivalent-Connected-→ {B = B} {f = f} ext =
      l-equiv
    , (λ ext′ →
           Connected-→-propositional ext ◯
         , (Π-closure ext′ 1 λ _ →
            Π-closure ext  1 λ _ →
            Is-equivalence-propositional ext)
         , prop ext′
         , _)
    where
    step₁ :
      ◯ -Connected-→ f →
      (P : B → Type a) → (∀ y → Modal (P y)) →
      Is-equivalence (_∘ f ⦂ ((∀ y → P y) → (∀ x → P (f x))))
    step₁ c P m =
      _≃_.is-equivalence $
      Eq.with-other-function
        ((∀ y → P y)                              ↝⟨ (∀-cong ext λ _ → inverse $
                                                      drop-⊤-left-Π ext $
                                                      _⇔_.to contractible⇔↔⊤ (c _)) ⟩
         (∀ y → ◯ (f ⁻¹ y) → P y)                 ↝⟨ (∀-cong ext λ _ →
                                                      Π◯≃Πη ext λ _ → Modal→Stable (m _)) ⟩
         (∀ y → f ⁻¹ y → P y)                     ↔⟨ (∀-cong ext λ _ → currying) ⟩
         (∀ y x → f x ≡ y → P y)                  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ fx≡y →
                                                      ≡⇒↝ _ $ cong P $ sym fx≡y) ⟩
         (∀ y x → f x ≡ y → P (f x))              ↔⟨ Π-comm ⟩
         (∀ x y → f x ≡ y → P (f x))              ↔⟨ (∀-cong ext λ _ → inverse currying) ⟩
         (∀ x → Other-singleton (f x) → P (f x))  ↝⟨ (∀-cong ext λ _ →
                                                      drop-⊤-left-Π ext $
                                                      _⇔_.to contractible⇔↔⊤ $
                                                      other-singleton-contractible _) ⟩□
         (∀ x → P (f x))                          □)
        (_∘ f)
        (λ g → apply-ext ext λ x →
           ≡⇒→ (cong P (sym (refl _)))
             (◯-rec (m (f x)) id
                (η (subst (λ _ → P (f x))
                      (proj₂ (c (f x)) (η (x , refl _)))
                      (g (f x)))))                        ≡⟨ (let y = _ in
                                                              trans (cong (λ eq → ≡⇒→ eq y) $
                                                                     trans (cong (cong P) sym-refl) $
                                                                     cong-refl _) $
                                                              ext⁻¹ ≡⇒→-refl _) ⟩
           ◯-rec (m (f x)) id
             (η (subst (λ _ → P (f x))
                   (proj₂ (c (f x)) (η (x , refl _)))
                   (g (f x))))                            ≡⟨ ◯-rec-η ⟩

           subst (λ _ → P (f x))
             (proj₂ (c (f x)) (η (x , refl _)))
             (g (f x))                                    ≡⟨ subst-const _ ⟩∎

           g (f x)                                        ∎)

    l-equiv : Logically-equivalent _
    l-equiv =
        (◯ -Connected-→ f                                             →⟨ step₁ ⟩⇔

         ((P : B → Type a) → (∀ y → Modal (P y)) →
          Is-equivalence (_∘ f ⦂ ((∀ y → P y) → (∀ x → P (f x)))))    →⟨ (λ hyp P m →
                                                                            _≃_.split-surjective $ Eq.⟨ _ , hyp P m ⟩) ⟩⇔□)
      , (((P : B → Type a) → (∀ y → Modal (P y)) →
          Split-surjective (_∘ f ⦂ ((∀ y → P y) → (∀ x → P (f x)))))  →⟨ Split-surjective-∘→Connected-→ ⟩□

         ◯ -Connected-→ f                                             □)

    prop :
      Extensionality (lsuc a) a →
      Is-proposition
        ((P : B → Type a) → (∀ y → Modal (P y)) →
         Split-surjective (_∘ f ⦂ ((∀ y → P y) → (∀ x → P (f x)))))
    prop ext′ =
      [inhabited⇒+]⇒+ 0 λ surj →
      Π-closure ext′ 1 λ P →
      Π-closure ext  1 λ m →                                           $⟨ _⇔_.to
                                                                            (logically-equivalent
                                                                               l-equiv
                                                                               (inj₂ (inj₂ (inj₁ F.id)))
                                                                               (inj₂ (inj₁ F.id)))
                                                                            surj P m ⟩

        Is-equivalence (_∘ f)                                          →⟨ (λ eq → _≃_.is-equivalence $ →-cong ext F.id Eq.⟨ _ , eq ⟩) ⟩

        Is-equivalence ((_∘ f) ∘_)                                     →⟨ Emb.Is-equivalence→Is-embedding ⟩

        Is-embedding ((_∘ f) ∘_)                                       →⟨ (λ emb → Emb.embedding→⁻¹-propositional emb _) ⟩

        Is-proposition (((_∘ f) ∘_) ⁻¹ id)                             →⟨ H-level-cong _ 1 $ equiv P ⟩□

        Is-proposition
          (Split-surjective (_∘ f ⦂ ((∀ y → P y) → (∀ x → P (f x)))))  □
      where
      equiv : ∀ _ → _
      equiv _ =
        ((_∘ f) ∘_) ⁻¹ id               ↔⟨⟩
        (∃ λ g → (λ h → g h ∘ f) ≡ id)  ↝⟨ (∃-cong λ _ → inverse $ Eq.extensionality-isomorphism ext) ⟩
        (∃ λ g → ∀ h → g h ∘ f ≡ h)     ↔⟨ inverse ΠΣ-comm ⟩□
        Split-surjective (_∘ f)         □

  -- "◯-connected" can be expressed in another way (assuming function
  -- extensionality).

  Connected≃Modal→Is-equivalence-const :
    Extensionality a a →
    ◯ -Connected A ↝[ lsuc a ∣ a ]
    ({B : Type a} →
     Modal B →
     Is-equivalence (const ⦂ (B → A → B)))
  Connected≃Modal→Is-equivalence-const {A = A} ext =
    generalise-ext?-prop
      (◯ -Connected A                                               ↝⟨ (Connected-cong _ $ inverse $
                                                                        drop-⊤-right λ _ → Eq.↔⇒≃ $
                                                                        _⇔_.to contractible⇔↔⊤ $
                                                                        H-level.⇒≡ 0 $ ↑-closure 0 ⊤-contractible) ⟩

       ◯ -Connected (const {B = A} (lift tt) ⁻¹ lift tt)            ↝⟨ inverse $ drop-⊤-left-Π _ Bijection.↑↔ ⟩

       ◯ -Connected-→ const {B = A} (lift tt)                       ↝⟨ logically-equivalent
                                                                         (Equivalent-Connected-→ ext .proj₁)
                                                                         (inj₁ F.id) (inj₂ (inj₁ F.id)) ⟩
       ((P : ↑ a ⊤ → Type a) → (∀ y → Modal (P y)) →
        Is-equivalence (_∘ const _ ⦂ ((↑ a ⊤ → P _) → (A → P _))))  ↝⟨ record
                                                                         { to   = λ hyp {_} m → hyp _ (const m)
                                                                         ; from = λ hyp _ m → hyp (m _)
                                                                         } ⟩
       ({B : Type a} → Modal B →
        Is-equivalence (_∘ const _ ⦂ ((↑ a ⊤ → B) → (A → B))))      ↝⟨ (implicit-∀-cong _ λ {B} → ∀-cong _ λ m →
                                                                        Is-equivalence≃Is-equivalence-∘ʳ
                                                                          (_≃_.is-equivalence $
                                                                           Eq.with-other-function
                                                                             (inverse $ drop-⊤-left-Π ext Bijection.↑↔)
                                                                             const
                                                                             (λ y → apply-ext ext λ _ →
         subst (λ _ → B) (refl _) y                                             ≡⟨ subst-refl _ _ ⟩∎
         y                                                                      ∎))
                                                                          _) ⟩□
       ({B : Type a} → Modal B →
        Is-equivalence (const ⦂ (B → A → B)))                       □)
      (λ _ → Connected-propositional ext ◯)
      (λ ext′ →
         implicit-Π-closure ext′ 1 λ _ →
         Π-closure ext 1 λ _ →
         Is-equivalence-propositional ext)

  -- If ◯ (P x) is P-null, then P x is ◯-connected.

  Null→Connected : P -Null ◯ (P x) → ◯ -Connected (P x)
  Null→Connected {P = P} {x = x} null =
    propositional⇒inhabited⇒contractible
      (◯-elim₂
         (λ _ _ → Separated-◯ _ _)
         (λ y z →
            η y                              ≡⟨ cong (_$ y) $ sym $ _≃_.right-inverse-of ◯≃→◯ _ ⟩
            _≃_.to ◯≃→◯ (_≃_.from ◯≃→◯ η) y  ≡⟨⟩
            _≃_.from ◯≃→◯ η                  ≡⟨⟩
            _≃_.to ◯≃→◯ (_≃_.from ◯≃→◯ η) z  ≡⟨ cong (_$ z) $ _≃_.right-inverse-of ◯≃→◯ _ ⟩∎
            η z                              ∎))
      (_≃_.from ◯≃→◯ η)
    where
    ◯≃→◯ : ◯ (P x) ≃ (P x → ◯ (P x))
    ◯≃→◯ = Eq.⟨ const , null x ⟩

  -- If (_ , P , _) is a witness of the modality's accessibility, then
  -- P x is ◯-connected for each x (assuming function extensionality).

  Accessible→Connected :
    Extensionality a a →
    ((A , P , _) : Accessible M) →
    {x : A} → ◯ -Connected (P x)
  Accessible→Connected ext (_ , P , acc) {x = x} =
    Null→Connected
      (                                                    $⟨ _⇔_.to (acc (◯ (P x))) Modal-◯ ⟩
       (∀ i →
        Is-∞-extendable-along-[ (λ (_ : P i) → lift tt) ]
          (λ (_ : ↑ a ⊤) → ◯ (P x)))                       ↝⟨ PS.Π-Is-∞-extendable-along≃Null ext ⟩□

       P -Null ◯ (P x)                                     □)

  -- I did not take the remaining lemmas in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code.

  -- If A is separated and B is ◯-connected, then const : A → B → A is
  -- an embedding (assuming function extensionality).

  Separated→Connected→Is-embedding-const :
    Extensionality a a →
    Separated A →
    ◯ -Connected B →
    Is-embedding (const ⦂ (A → B → A))
  Separated→Connected→Is-embedding-const {B = B} ext s c x y =
    _≃_.is-equivalence $
    Eq.with-other-function
      (x ≡ y                          ↝⟨ Eq.⟨ _ , _⇔_.to (Connected≃Modal→Is-equivalence-const ext _) c (s _ _) ⟩ ⟩
       (B → x ≡ y)                    ↔⟨⟩
       (∀ z → const x z ≡ const y z)  ↝⟨ Eq.extensionality-isomorphism ext ⟩□
       const x ≡ const y              □)
      (cong const)
      (λ eq →
         apply-ext ext (λ _ → eq)  ≡⟨ ext-const ext ⟩∎
         cong const eq             ∎)

  -- If A is ◯-connected, then const : ∃ Modal → A → ∃ Modal is an
  -- embedding (assuming function extensionality and univalence).

  Connected→Is-embedding-const-Σ-Modal :
    Extensionality a (lsuc a) →
    Univalence a →
    ◯ -Connected A →
    Is-embedding (const ⦂ (∃ Modal → A → ∃ Modal))
  Connected→Is-embedding-const-Σ-Modal
    {A = A} ext univ c Bm@(B , mB) Cm@(C , mC) =
    _≃_.is-equivalence $
    Eq.with-other-function
      (Bm ≡ Cm                          ↔⟨ inverse $ ignore-propositional-component prop ⟩
       B ≡ C                            ↝⟨ ≡≃≃ univ ⟩
       B ≃ C                            ↝⟨ Eq.⟨ _ , _⇔_.to (Connected≃Modal→Is-equivalence-const ext′ _) c (Modal-≃ ext′ mB mC) ⟩ ⟩
       (A → B ≃ C)                      ↔⟨⟩
       (∀ x → const B x ≃ const C x)    ↝⟨ (∀-cong ext λ _ → inverse $ ≡≃≃ univ) ⟩
       (∀ x → const B x ≡ const C x)    ↔⟨ (∀-cong ext λ _ → ignore-propositional-component prop) ⟩
       (∀ x → const Bm x ≡ const Cm x)  ↝⟨ Eq.extensionality-isomorphism ext ⟩□
       const Bm ≡ const Cm              □)
      (cong const)
      (λ eq →
         (apply-ext ext λ _ →
          _↔_.to (ignore-propositional-component prop) $
          ≃⇒≡ univ $ ≡⇒≃ $
          _↔_.from (ignore-propositional-component prop) eq)  ≡⟨ (cong (apply-ext ext) $ apply-ext ext λ _ →
                                                                  cong (_↔_.to (ignore-propositional-component prop)) $
                                                                  _≃_.left-inverse-of (≡≃≃ univ) _) ⟩
         (apply-ext ext λ _ →
          _↔_.to (ignore-propositional-component prop) $
          _↔_.from (ignore-propositional-component prop) eq)  ≡⟨ (cong (apply-ext ext) $ apply-ext ext λ _ →
                                                                  _↔_.right-inverse-of (ignore-propositional-component prop) _) ⟩

         (apply-ext ext λ _ → eq)                             ≡⟨ ext-const ext ⟩∎

         cong const eq                                        ∎)
    where
    ext′ = lower-extensionality lzero _ ext
    prop = Modal-propositional ext′

  ----------------------------------------------------------------------
  -- Accessible modalities

  -- A simple consequence of the definition of accessibility.

  Accessible→Modal≃Null :
    Extensionality a a →
    ((_ , P , _) : Accessible M) →
    Modal A ≃ P -Null A
  Accessible→Modal≃Null {A = A} ext (_ , P , acc) =
    Modal A                                               ↝⟨ _↠_.from
                                                               (Eq.≃↠⇔
                                                                  (Modal-propositional ext)
                                                                  (Π-closure ext 1 λ _ →
                                                                   PS.Is-∞-extendable-along-propositional ext))
                                                               (acc A) ⟩
    (∀ x →
       Is-∞-extendable-along-[ (λ (_ : P x) → lift tt) ]
         (λ (_ : ↑ a ⊤) → A))                             ↝⟨ PS.Π-Is-∞-extendable-along≃Null ext ⟩□

    P -Null A                                             □

  ----------------------------------------------------------------------
  -- Some definitions and lemmas related to left exactness

  -- For more properties that hold for left exact modalities, see
  -- Modality.Left-exact and other modules.

  -- An alternative definition of what it means for the modality to be
  -- left exact.

  Left-exact-η-cong : Type (lsuc a)
  Left-exact-η-cong =
    {A : Type a} {x y : A} →
    Is-equivalence (η-cong {x = x} {y = y})

  -- Left-exact-η-cong is propositional (assuming function
  -- extensionality).

  Left-exact-η-cong-propositional :
    Extensionality (lsuc a) a →
    Is-proposition Left-exact-η-cong
  Left-exact-η-cong-propositional ext =
    implicit-Π-closure ext  1 λ _ →
    implicit-Π-closure ext′ 1 λ _ →
    implicit-Π-closure ext′ 1 λ _ →
    Is-equivalence-propositional ext′
    where
    ext′ = lower-extensionality _ lzero ext

  mutual

    -- The two definitions of "left exact" given above are equivalent
    -- (assuming function extensionality).

    Left-exact≃Left-exact-η-cong :
      Left-exact ◯ ↝[ lsuc a ∣ a ] Left-exact-η-cong
    Left-exact≃Left-exact-η-cong = generalise-ext?-prop
      (logically-equivalent
         (Equivalent-Left-exact .proj₁)
         (inj₁ F.id)
         (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ F.id))))))))
      Left-exact-propositional
      Left-exact-η-cong-propositional

    -- In fact, a number of definitions of "left exact" are logically
    -- equivalent (and equivalent assuming function extensionality).

    Equivalent-Left-exact :
      Equivalent? (lsuc a) (lsuc a)
        (Left-exact ◯ ,

         ({A B : Type a} {f : A → B} →
          ◯ -Connected A → ◯ -Connected B → ◯ -Connected-→ f) ,

         ({A B₁ B₂ C : Type a}
          {f₁ : A → B₂} {f₂ : B₂ → C} {g₁ : A → B₁} {g₂ : B₁ → C}
          (p : ∀ x → g₂ (g₁ x) ≡ f₂ (f₁ x)) →
          ◯ -Connected-→ f₂ → ◯ -Connected-→ g₁ →
          ∀ y → ◯ -Connected-→ (⁻¹-map p ⦂ (f₁ ⁻¹ y → g₂ ⁻¹ f₂ y))) ,

         ({A B : Type a} {f : A → B} {y : B} →
          ◯ -Connected-→
            (⁻¹-map {f₂ = η} (λ _ → ◯-map-η) ⦂
             (f ⁻¹ y → ◯-map f ⁻¹ η y))) ,

         ({A : Type a} {x y : A} →
          ◯ -Connected-→
            (⁻¹-map (λ _ → ◯-map-η {x = lift tt}) ⦂
               (const {B = ↑ a ⊤} x ⁻¹ y → ◯-map (const x) ⁻¹ η y))) ,

         ({A : Type a} {x y : A} →
          ◯ -Connected-→ (cong η ⦂ (x ≡ y → η x ≡ η y))) ,

         Left-exact-η-cong ,

         ({A B C : Type a} {f : A → B} {g : B → C} →
          ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) →
          ◯ -Connected-→ f) ,

         ({A B : Type a} {f : A → B} →
          Is-equivalence (◯-map f) → ◯ -Connected-→ f))
    Equivalent-Left-exact =
        Logically-equivalent-Append
          (inj₂ (inj₁ F.id))
          (inj₁ F.id)
          ( (({A : Type a} {x y : A} →
              ◯ -Connected A → ◯ -Connected (x ≡ y))                      →⟨ (λ lex → step₁ lex) ⟩⇔

             ({A B : Type a} {f : A → B} →
              ◯ -Connected A → ◯ -Connected B → ◯ -Connected-→ f)         →⟨ (λ lex → step₂ lex) ⟩⇔

             ({A B₁ B₂ C : Type a}
              {f₁ : A → B₂} {f₂ : B₂ → C} {g₁ : A → B₁} {g₂ : B₁ → C}
              (p : ∀ x → g₂ (g₁ x) ≡ f₂ (f₁ x)) →
              ◯ -Connected-→ f₂ → ◯ -Connected-→ g₁ →
              ∀ y → ◯ -Connected-→ (⁻¹-map p ⦂ (f₁ ⁻¹ y → g₂ ⁻¹ f₂ y)))   →⟨ (λ lex → lex (λ _ → ◯-map-η) Connected-→-η Connected-→-η _) ⟩⇔

             ({A B : Type a} {f : A → B} {y : B} →
              ◯ -Connected-→
                (⁻¹-map {f₂ = η} (λ _ → ◯-map-η) ⦂
                 (f ⁻¹ y → ◯-map f ⁻¹ η y)))                              →⟨ (λ lex → lex) ⟩⇔

             ({A : Type a} {x y : A} →
              ◯ -Connected-→
                (⁻¹-map (λ _ → ◯-map-η {x = lift tt}) ⦂
                   (const {B = ↑ a ⊤} x ⁻¹ y → ◯-map (const x) ⁻¹ η y)))  →⟨ (λ lex → step₅ lex) ⟩⇔

             ({A : Type a} {x y : A} →
              ◯ -Connected-→ (cong η ⦂ (x ≡ y → η x ≡ η y)))              →⟨ (λ lex {_ _ _} → Connected-→≃Is-equivalence-◯-rec _ _ lex) ⟩⇔□)

          , (({A : Type a} {x y : A} →
              Is-equivalence
                (◯-rec (Separated-◯ _ _) (cong η) ⦂
                 (◯ (x ≡ y) → η x ≡ η y)))                                ↔⟨⟩

             ({A : Type a} {x y : A} →
              Is-equivalence (η-cong ⦂ (◯ (x ≡ y) → η x ≡ η y)))          →⟨ step₇ ⟩□

             ({A : Type a} {x y : A} →
              ◯ -Connected A → ◯ -Connected (x ≡ y))                      □)
          )
          (Logically-equivalent-Append
             (inj₂ (inj₁ F.id))
             (inj₁ F.id)
             ( (({A B : Type a} {f : A → B} →
                 ◯ -Connected A → ◯ -Connected B → ◯ -Connected-→ f)  →⟨ (λ lex {_ _ _ _ _} → step₈ lex) ⟩⇔□)

             , (({A B C : Type a} {f : A → B} {g : B → C} →
                 ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) →
                 ◯ -Connected-→ f)                                    →⟨ (λ lex → step₉ lex) ⟩□

                ({A B : Type a} {f : A → B} →
                 ◯ -Connected A → ◯ -Connected B → ◯ -Connected-→ f)  □)
             )
             ( (({A B C : Type a} {f : A → B} {g : B → C} →
                 ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) →
                 ◯ -Connected-→ f)                                    →⟨ (λ lex {_ _ _} → step₁₀ lex) ⟩⇔□)

             , (({A B : Type a} {f : A → B} →
                 Is-equivalence (◯-map f) → ◯ -Connected-→ f)         →⟨ (λ lex → step₁₁ lex) ⟩□

                ({A B C : Type a} {f : A → B} {g : B → C} →
                 ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) →
                 ◯ -Connected-→ f)                                    □)
             ))
      , (λ ext →
           let ext′ : Extensionality (lsuc a) a
               ext′ = lower-extensionality lzero _ ext

               ext″ : Extensionality a a
               ext″ = lower-extensionality _ _ ext
           in
             Left-exact-propositional ext′
           , (implicit-Π-closure ext  1 λ _ →
              implicit-Π-closure ext′ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              Π-closure ext″ 1 λ _ →
              Π-closure ext″ 1 λ _ →
              Connected-→-propositional ext″ ◯)
           , (implicit-Π-closure ext  1 λ _ →
              implicit-Π-closure ext  1 λ _ →
              implicit-Π-closure ext  1 λ _ →
              implicit-Π-closure ext′ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              Π-closure ext″ 1 λ _ →
              Π-closure ext″ 1 λ _ →
              Π-closure ext″ 1 λ _ →
              Π-closure ext″ 1 λ _ →
              Connected-→-propositional ext″ ◯)
           , (implicit-Π-closure ext  1 λ _ →
              implicit-Π-closure ext′ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              Connected-→-propositional ext″ ◯)
           , (implicit-Π-closure ext′ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              Connected-→-propositional ext″ ◯)
           , (implicit-Π-closure ext′ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              Connected-→-propositional ext″ ◯)
           , Left-exact-η-cong-propositional ext′
           , (implicit-Π-closure ext  1 λ _ →
              implicit-Π-closure ext  1 λ _ →
              implicit-Π-closure ext′ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              Π-closure ext″ 1 λ _ →
              Π-closure ext″ 1 λ _ →
              Connected-→-propositional ext″ ◯)
           , (implicit-Π-closure ext  1 λ _ →
              implicit-Π-closure ext′ 1 λ _ →
              implicit-Π-closure ext″ 1 λ _ →
              Π-closure ext″ 1 λ _ →
              Connected-→-propositional ext″ ◯)
           , _)
      where
      step₁ :
        {f : A → B} →
        Left-exact ◯ →
        ◯ -Connected A → ◯ -Connected B → ◯ -Connected-→ f
      step₁ lex cA cB _ = Connected-Σ cA λ _ → lex cB

      step₂ :
        {f₁ : A → B₂} {f₂ : B₂ → C} {g₁ : A → B₁} {g₂ : B₁ → C} →
        ({A B : Type a} {f : A → B} →
         ◯ -Connected A → ◯ -Connected B → ◯ -Connected-→ f) →
        (p : ∀ x → g₂ (g₁ x) ≡ f₂ (f₁ x)) →
        ◯ -Connected-→ f₂ → ◯ -Connected-→ g₁ →
        ∀ y → ◯ -Connected-→ (⁻¹-map p ⦂ (f₁ ⁻¹ y → g₂ ⁻¹ f₂ y))
      step₂ lex p c-f₂ c-g₁ y =                                         $⟨ (λ _ → lex (c-g₁ _) (c-f₂ _) _) ⟩
        (∀ q → ◯ -Connected (⁻¹-map (sym ∘ p) ⁻¹ (y , sym (proj₂ q))))  →⟨ (∀-cong _ λ _ → Connected-cong _ $ inverse 3×3-⁻¹) ⟩□
        (∀ q → ◯ -Connected (⁻¹-map p ⁻¹ q))                            □

      step₅ :
        {x y : A} →
        ◯ -Connected-→
          (⁻¹-map (λ _ → ◯-map-η {x = lift tt}) ⦂
             (const {B = ↑ a ⊤} x ⁻¹ y → ◯-map (const x) ⁻¹ η y)) →
        ◯ -Connected-→ (cong η ⦂ (x ≡ y → η x ≡ η y))
      step₅ {x = x} {y = y} =
        ◯ -Connected-→
          (λ (_ , x≡y) → η _ , trans ◯-map-η (cong η x≡y))                →⟨ Connected-→→Connected-→≃Connected-→-∘ lemma₁ _ ⟩

        ◯ -Connected-→ (λ x≡y → η _ , trans ◯-map-η (cong η x≡y))         →⟨ Is-equivalence→Connected-→→Connected-→-∘ $
                                                                             _≃_.is-equivalence drop-proj₁ ⟩
        ◯ -Connected-→
          (λ x≡y → _≃_.to drop-proj₁ (η _ , trans ◯-map-η (cong η x≡y)))  →⟨ (Connected-→-cong _ λ x≡y →

          _≃_.to drop-proj₁ (η _ , trans ◯-map-η (cong η x≡y))                  ≡⟨⟩

          subst
            (λ z → ◯-map (const x) z ≡ η y)
            (sym $ _≃_.left-inverse-of ◯-⊤ _)
            (trans ◯-map-η (cong η x≡y))                                        ≡⟨ cong (flip (subst _) _) $
                                                                                   H-level.⇒≡ 1
                                                                                     (H-level.mono₁ 0 $ _⇔_.from contractible⇔↔⊤ $
                                                                                      from-equivalence ◯-⊤)
                                                                                     _ _ ⟩
          subst
            (λ z → ◯-map (const x) z ≡ η y)
            (refl _)
            (trans ◯-map-η (cong η x≡y))                                        ≡⟨ subst-refl _ _ ⟩∎

          trans ◯-map-η (cong η x≡y)                                            ∎) ⟩

        ◯ -Connected-→ (λ x≡y → trans ◯-map-η (cong η x≡y))               →⟨ Is-equivalence→Connected-→→Connected-→-∘ lemma₂ ⟩

        ◯ -Connected-→
          (λ x≡y → trans (sym (◯-map-η {f = const x}))
                     (trans ◯-map-η (cong η x≡y)))                        →⟨ (Connected-→-cong _ λ _ → trans-sym-[trans] _ _) ⟩□

        ◯ -Connected-→ (cong η ⦂ (x ≡ y → η x ≡ η y))                     □
        where
        lemma₁ : ◯ -Connected-→ (lift {ℓ = a} tt ,_)
        lemma₁ (lift tt , x≡y) =                            $⟨ ⊤-contractible ⟩
          Contractible ⊤                                    →⟨ H-level-cong _ 0 $ inverse ◯-⊤ ⟩
          Contractible (◯ (↑ a ⊤))                          ↔⟨⟩
          ◯ -Connected (↑ a ⊤)                              →⟨ Connected-cong _ (

            ↑ a ⊤                                                ↔⟨ Bijection.↑↔ ⟩
            ⊤                                                    ↔⟨ inverse $ _⇔_.to contractible⇔↔⊤ $
                                                                    Preimage.bijection⁻¹-contractible
                                                                      (inverse $ drop-⊤-left-× λ _ → Bijection.↑↔)
                                                                      _ ⟩□
            (lift tt ,_) ⁻¹ (lift tt , x≡y)                      □) ⟩

          ◯ -Connected (((lift tt ,_) ⁻¹ (lift tt , x≡y)))  □

        drop-proj₁ : (∃ λ (x : ◯ (↑ a ⊤)) → P x) ≃ P (η _)
        drop-proj₁ =
          from-bijection $ drop-⊤-left-Σ $ from-equivalence ◯-⊤

        lemma₂ :
          Is-equivalence
            (trans {z = η y}
               (sym (◯-map-η {f = const x} {x = lift tt})))
        lemma₂ = _≃_.is-equivalence $ Eq.↔→≃
          _
          (trans ◯-map-η)
          (λ _ → trans-sym-[trans] _ _)
          (λ _ → trans--[trans-sym] _ _)

      step₇ : Left-exact-η-cong → Left-exact ◯
      step₇ lex {A = A} {x = x} {y = y} =
        Contractible (◯ A)        →⟨ H-level.⇒≡ 0 ⟩
        Contractible (η x ≡ η y)  →⟨ H-level-cong _ 0 $ inverse Eq.⟨ _ , lex ⟩ ⟩□
        Contractible (◯ (x ≡ y))  □

      step₈ :
        ({A B : Type a} {f : A → B} →
         ◯ -Connected A → ◯ -Connected B → ◯ -Connected-→ f) →
        ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) → ◯ -Connected-→ f
      step₈ {g = g} {f = f} lex c-g c-g∘f =                $⟨ (λ _ → lex (c-g∘f _) (c-g _) _) ⟩
        (∀ y → ◯ -Connected (∘⁻¹→⁻¹ ⁻¹ (y , refl (g y))))  →⟨ (∀-cong _ λ y → Connected-cong _ Σ-map--id-⁻¹≃⁻¹) ⟩□
        (∀ y → ◯ -Connected (f ⁻¹ y))                      □
        where
        ∘⁻¹→⁻¹ : g ∘ f ⁻¹ g y → g ⁻¹ g y
        ∘⁻¹→⁻¹ = Σ-map f id

      step₁₀ :
        ({A B C : Type a} {f : A → B} {g : B → C} →
         ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) → ◯ -Connected-→ f) →
        Is-equivalence (◯-map f) → ◯ -Connected-→ f
      step₁₀ {f = f} lex =
        Is-equivalence (◯-map f)  →⟨ _⇔_.from (Connected-→-η-∘-≃Is-equivalence-◯-map _) ⟩
        ◯ -Connected-→ (η ∘ f)    →⟨ lex Connected-→-η ⟩□
        ◯ -Connected-→ f          □

      step₉ :
        {f : A → B} →
        ({A B C : Type a} {f : A → B} {g : B → C} →
         ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) → ◯ -Connected-→ f) →
        ◯ -Connected A → ◯ -Connected B → ◯ -Connected-→ f
      step₉ {f = f} lex c-A c-B =
                                  $⟨ Eq.function-between-contractible-types-is-equivalence _ c-A c-B ⟩
        Is-equivalence (◯-map f)  →⟨ step₁₀ lex ⟩□
        ◯ -Connected-→ f          □

      step₁₁ :
        ({A B : Type a} {f : A → B} →
         Is-equivalence (◯-map f) → ◯ -Connected-→ f) →
        ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) → ◯ -Connected-→ f
      step₁₁ {g = g} {f = f} lex = curry
        (◯ -Connected-→ g × ◯ -Connected-→ (g ∘ f)                      →⟨ Σ-map
                                                                             Connected→Is-equivalence-◯-map
                                                                             Connected→Is-equivalence-◯-map ⟩
         Is-equivalence (◯-map g) × Is-equivalence (◯-map (g ∘ f))      →⟨ (∃-cong λ _ →
                                                                            Is-equivalence-cong _ λ _ →
                                                                            ◯-map-∘) ⟩
         Is-equivalence (◯-map g) × Is-equivalence (◯-map g ∘ ◯-map f)  →⟨ uncurry (Eq.Two-out-of-three.g-g∘f $ Eq.two-out-of-three _ _) ⟩
         Is-equivalence (◯-map f)                                       →⟨ lex ⟩□
         ◯ -Connected-→ f                                               □)

  -- If the modality is left exact, A is ◯-connected, and
  -- P : A → Type a is pointwise modal, then there is some modal type
  -- B : Type a for which P x ≃ B holds for each x.

  Left-exact→Connected→Modal→≃ :
    {P : A → Type a} →
    Left-exact ◯ →
    ◯ -Connected A → (∀ x → Modal (P x)) →
    ∃ λ (B : Type a) → Modal B × ∀ x → P x ≃ B
  Left-exact→Connected→Modal→≃ {A = A} {P = P} =
    Left-exact ◯                                                    →⟨ _⇔_.to
                                                                         (logically-equivalent
                                                                            (Equivalent-Left-exact .proj₁)
                                                                            (inj₁ F.id)
                                                                            (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ F.id))))))))) ⟩
    ({A B C : Type a} {f : A → B} {g : B → C} →
     ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) → ◯ -Connected-→ f)  →⟨ step₂ ⟩□

    (◯ -Connected A → (∀ x → Modal (P x)) →
     ∃ λ (B : Type a) → Modal B × ∀ x → P x ≃ B)                    □
    where
    step₂ :
      ({A B C : Type a} {f : A → B} {g : B → C} →
       ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) → ◯ -Connected-→ f) →
      ◯ -Connected A → (∀ x → Modal (P x)) →
      ∃ λ (B : Type a) → Modal B × ∀ x → P x ≃ B
    step₂ lex c m =
        ◯ (∃ P)
      , Modal-◯
      , (λ x →
           P x      ↝⟨ Eq.⟨ f′ x , f′-eq x ⟩ ⟩□
           ◯ (∃ P)  □)
      where
      f′ : ∀ x → P x → ◯ (∃ P)
      f′ x y = η (x , y)

      c′ : ◯ -Connected-→ proj₂ {B = λ (_ : A) → ◯ (∃ P)}
      c′ y =                                  $⟨ c ⟩
        ◯ -Connected A                        →⟨ (Connected-cong _ $ from-bijection $
                                                  Σ-assoc F.∘
                                                  (inverse $ drop-⊤-right λ _ →
                                                   _⇔_.to contractible⇔↔⊤ $ singleton-contractible _)) ⟩
        ◯ -Connected (∃ λ (x , y′) → y′ ≡ y)  ↔⟨⟩
        ◯ -Connected (proj₂ ⁻¹ y)             □

      f′-eq : ∀ x → Is-equivalence (f′ x)
      f′-eq x =                                   $⟨ lex c′ Connected-→-η ⟩
        ◯ -Connected-→ (Σ-map id (λ {x} → f′ x))  →⟨ Connected-→-Σ-map≃Connected-→ _ ⟩
        (∀ x → ◯ -Connected-→ f′ x)               →⟨ _$ x ⟩
        ◯ -Connected-→ f′ x                       →⟨ Connected-→≃Is-equivalence (m x) Modal-◯ _ ⟩□
        Is-equivalence (f′ x)                     □

  -- If the type of fibres of const : ∃ Modal → A → ∃ Modal over P is
  -- inhabited (for A : Type a), then a certain type of triples is
  -- inhabited.

  const⁻¹→ :
    {A : Type a} {P : A → ∃ Modal} →
    (const ⦂ (∃ Modal → A → ∃ Modal)) ⁻¹ P →
    ∃ λ B → Modal B × (∀ y → proj₁ (P y) ≃ B)
  const⁻¹→ {A = A} {P = P} =
    const ⁻¹ P                                         ↔⟨⟩
    (∃ λ (B : ∃ Modal) → const B ≡ P)                  ↔⟨ inverse Σ-assoc ⟩
    (∃ λ B → ∃ λ (m : Modal B) → const (B , m) ≡ P)    →⟨ (∃-cong λ _ → ∃-cong λ _ → ext⁻¹) ⟩
    (∃ λ B → ∃ λ (m : Modal B) → ∀ y → (B , m) ≡ P y)  →⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong _ λ _ → proj₁ ∘ Σ-≡,≡←≡) ⟩
    (∃ λ B → Modal B × (∀ y → B ≡ proj₁ (P y)))        →⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong _ λ _ → sym) ⟩
    (∃ λ B → Modal B × (∀ y → proj₁ (P y) ≡ B))        →⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong _ λ _ → ≡⇒≃) ⟩□
    (∃ λ B → Modal B × (∀ y → proj₁ (P y) ≃ B))        □

  -- The function const⁻¹→ can be turned into an equivalence (assuming
  -- function extensionality and univalence).

  const⁻¹≃ :
    {A : Type a} {P : A → ∃ Modal} →
    Extensionality a (lsuc a) →
    Univalence a →
    (const ⦂ (∃ Modal → A → ∃ Modal)) ⁻¹ P ≃
    (∃ λ B → Modal B × (∀ y → proj₁ (P y) ≃ B))
  const⁻¹≃ {A = A} {P = P} ext univ =
    const ⁻¹ P                                         ↔⟨⟩

    (∃ λ (B : ∃ Modal) → const B ≡ P)                  ↔⟨ inverse
                                                          Σ-assoc ⟩
    (∃ λ B → ∃ λ (m : Modal B) → const (B , m) ≡ P)    ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse $
                                                           Eq.extensionality-isomorphism ext) ⟩
    (∃ λ B → ∃ λ (m : Modal B) → ∀ y → (B , m) ≡ P y)  ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → inverse $
                                                           ignore-propositional-component
                                                             (Modal-propositional (lower-extensionality lzero _ ext))) ⟩
    (∃ λ B → Modal B × (∀ y → B ≡ proj₁ (P y)))        ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                           ≡-comm) ⟩
    (∃ λ B → Modal B × (∀ y → proj₁ (P y) ≡ B))        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                           ≡≃≃ univ) ⟩□
    (∃ λ B → Modal B × (∀ y → proj₁ (P y) ≃ B))        □

  _ :
    {A : Type a} {P : A → ∃ Modal}
    {ext : Extensionality a (lsuc a)}
    {univ : Univalence a} →
    _≃_.to (const⁻¹≃ {P = P} ext univ) ≡ const⁻¹→
  _ = refl _

  -- In the presence of univalence and function extensionality
  -- Left-exact→Connected→Modal→≃ can be strengthened.

  Left-exact≃Connected→Modal→≃ :
    Extensionality (lsuc a) (lsuc a) →
    Univalence a →
    Left-exact ◯ ≃
    ({A : Type a} {P : A → Type a} →
     ◯ -Connected A → (∀ x → Modal (P x)) →
     ∃ λ (B : Type a) → Modal B × ∀ x → P x ≃ B)
  Left-exact≃Connected→Modal→≃ ext univ =
    Eq.⇔→≃
      (Left-exact-propositional ext′)
      (implicit-Π-closure ext 1 λ _ →
       implicit-Π-closure ext 1 λ _ →
       Π-closure ext″ 1 λ c →
       Π-closure ext″ 1 λ m →
       prop c m)
      (λ lex → Left-exact→Connected→Modal→≃ lex)
      (λ lex → from lex)
    where
    ext′ : Extensionality (lsuc a) a
    ext′ = lower-extensionality lzero _ ext

    ext″ : Extensionality a (lsuc a)
    ext″ = lower-extensionality _ lzero ext

    ext‴ : Extensionality a a
    ext‴ = lower-extensionality _ _ ext

    from :
      {x y : A} →
      ({A : Type a} {P : A → Type a} →
       ◯ -Connected A → (∀ x → Modal (P x)) →
       ∃ λ (B : Type a) → Modal B × ∀ x → P x ≃ B) →
      ◯ -Connected A → ◯ -Connected (x ≡ y)
    from {A = A} {x = x} {y = y} lex c = c′
      where
      P′ : A → Type a
      P′ z = ◯ (x ≡ z)

      lemma : ∃ λ (B : Type a) → Modal B × ∀ z → P′ z ≃ B
      lemma = lex c (λ _ → Modal-◯)

      B′ : Type a
      B′ = lemma .proj₁

      m′ : Modal B′
      m′ = lemma .proj₂ .proj₁

      P′-constant : ∀ z → P′ z ≃ B′
      P′-constant = lemma .proj₂ .proj₂

      subst-P′-const :
        (p q : z₁ ≡ z₂) (r : ◯ (x ≡ z₁)) →
        subst P′ p r ≡ subst P′ q r
      subst-P′-const {z₁ = z₁} {z₂ = z₂} p q =
        subst
          (λ P → (r : P z₁) → subst P p r ≡ subst P q r)
          (apply-ext ext″ λ z →
           ≃⇒≡ univ $ inverse $ P′-constant z)
          (λ r →
             subst (const B′) p r  ≡⟨ subst-const _ ⟩
             r                     ≡⟨ sym $ subst-const _ ⟩∎
             subst (const B′) q r  ∎)

      subst-η-refl≡η : (p : x ≡ z) → subst P′ p (η (refl x)) ≡ η p
      subst-η-refl≡η =
        elim¹
          (λ {z} (p : x ≡ z) → subst P′ p (η (refl x)) ≡ η p)
          (subst-refl _ _)

      η≡η : (p q : x ≡ z) → η p ≡ η q
      η≡η p q =
        η p                      ≡⟨ sym $ subst-η-refl≡η _ ⟩
        subst P′ p (η (refl x))  ≡⟨ subst-P′-const _ _ _ ⟩
        subst P′ q (η (refl x))  ≡⟨ subst-η-refl≡η _ ⟩∎
        η q                      ∎

      prop : Is-proposition (◯ (x ≡ y))
      prop =
        ◯-elim₂
          (λ _ _ → Separated-◯ _ _)
          (λ p q →
             η p  ≡⟨ η≡η p q ⟩∎
             η q  ∎)

      inh : ◯ (x ≡ y)
      inh =        $⟨ η (refl _) ⟩
        ◯ (x ≡ x)  ↝⟨ P′-constant x ⟩
        B′         ↝⟨ inverse $ P′-constant y ⟩□
        ◯ (x ≡ y)  □

      c′ : Contractible (◯ (x ≡ y))
      c′ = propositional⇒inhabited⇒contractible prop inh

    prop :
      {A : Type a} {P : A → Type a} →
      ◯ -Connected A → (∀ x → Modal (P x)) →
      Is-proposition (∃ λ (B : Type a) → Modal B × ∀ x → P x ≃ B)
    prop {A = A} {P = P} c m =                                     $⟨ Emb.embedding→⁻¹-propositional
                                                                        (Connected→Is-embedding-const-Σ-Modal ext″ univ c) _ ⟩
      Is-proposition
        ((const ⦂ (∃ Modal → A → ∃ Modal)) ⁻¹ (λ x → P x , m x))   →⟨ H-level-cong _ 1 $ const⁻¹≃ ext″ univ ⟩□

      Is-proposition (∃ λ (B : Type a) → Modal B × ∀ x → P x ≃ B)  □

  -- I did not take the remaining results in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code.

  -- If the modality is empty-modal and ◯ (↑ a Bool) is a proposition,
  -- then the modality is not left exact.

  Empty-modal→Is-proposition-◯→¬-Left-exact :
    Empty-modal M →
    Is-proposition (◯ (↑ a Bool)) →
    ¬ Left-exact ◯
  Empty-modal→Is-proposition-◯→¬-Left-exact Modal-⊥ prop =
    Left-exact ◯                                                         →⟨ Left-exact≃Left-exact-η-cong _ ⟩

    Left-exact-η-cong                                                    →⟨ (λ lex → lex) ⟩

    Is-equivalence
      (η-cong ⦂
         (◯ (lift true ≡ lift false) → η (lift true) ≡ η (lift false)))  →⟨ Eq.⟨ _ ,_⟩ ⟩

    ◯ (lift true ≡ lift false) ≃ (η (lift true) ≡ η (lift false))        →⟨ (λ eq → _≃_.from eq (prop _ _)) ⟩

    ◯ (lift true ≡ lift false)                                           →⟨ ◯-map (⊥-elim ∘ Bool.true≢false ∘ cong lower) ⟩

    ◯ ⊥                                                                  →⟨ ⊥-elim ∘ Modal→Stable Modal-⊥ ⟩□

    ⊥                                                                    □

  -- If ◯ (Modal A) holds, then the function η-cong {x = x} {y = y} is
  -- an equivalence for all x and y of type A.

  ◯-Modal→Is-equivalence-η-cong :
    ◯ (Modal A) →
    (x y : A) → Is-equivalence (η-cong ⦂ (◯ (x ≡ y) → η x ≡ η y))
  ◯-Modal→Is-equivalence-η-cong {A = A} = λ m x y →
    let m′ = Separated-◯ _ _ in
    _≃_.is-equivalence $
    Eq.↔→≃
      _
      (η x ≡ η y                    →⟨ η ⟩
       ◯ (η x ≡ η y)                →⟨ m ,_ ⟩
       ◯ (Modal A) × ◯ (η x ≡ η y)  →⟨ _≃_.from ◯× ⟩
       ◯ (Modal A × η x ≡ η y)      →⟨ ◯-map lemma ⟩□
       ◯ (x ≡ y)                    □)
      (λ p →
         ◯-elim
           {P = λ m →
                  ◯-rec m′ (cong η)
                    (◯-map lemma (_≃_.from ◯× (m , η p))) ≡
                  p}
           (λ _ → Modal→Separated m′ _ _)
           (λ m →
              ◯-rec m′ (cong η)
                (◯-map lemma (_≃_.from ◯× (η m , η p)))    ≡⟨ cong (◯-rec m′ (cong η) ∘ ◯-map _) ◯×⁻¹-η ⟩

              ◯-rec m′ (cong η) (◯-map lemma (η (m , p)))  ≡⟨ cong (◯-rec m′ (cong η)) ◯-map-η ⟩

              ◯-rec m′ (cong η) (η (lemma (m , p)))        ≡⟨ ◯-rec-η ⟩

              cong η (lemma (m , p))                       ≡⟨ _≃_.right-inverse-of (≡≃η≡η m) _ ⟩∎

              p                                            ∎)
           m)
      (◯-elim
         (λ _ → Separated-◯ _ _)
         (λ p →
            ◯-elim
              {P = λ m →
                     ◯-map lemma
                       (_≃_.from ◯×
                          (m , η (◯-rec m′ (cong η) (η p)))) ≡
                     η p}
              (λ _ → Separated-◯ _ _)
              (λ m →
                 ◯-map lemma
                   (_≃_.from ◯× (η m , η (◯-rec m′ (cong η) (η p))))  ≡⟨ cong (◯-map lemma) ◯×⁻¹-η ⟩

                 ◯-map lemma (η (m , ◯-rec m′ (cong η) (η p)))        ≡⟨ ◯-map-η ⟩

                 η (lemma (m , ◯-rec m′ (cong η) (η p)))              ≡⟨ cong (η ∘ lemma ∘ (m ,_)) ◯-rec-η ⟩

                 η (lemma (m , cong η p))                             ≡⟨ cong η $ _≃_.left-inverse-of (≡≃η≡η m) _ ⟩∎

                 η p                                                  ∎)
              m))
    where
    lemma : {x y : A} → Modal A × η x ≡ η y → x ≡ y
    lemma {x = x} {y = y} (m , p) =
      x            ≡⟨ sym η⁻¹-η ⟩
      η⁻¹ m (η x)  ≡⟨ cong (η⁻¹ m) p ⟩
      η⁻¹ m (η y)  ≡⟨ η⁻¹-η ⟩∎
      y            ∎

    ≡≃η≡η : {x y : A} → Modal A → (x ≡ y) ≃ (η x ≡ η y)
    ≡≃η≡η m =
      Embedding.equivalence $
      record
        { is-embedding = Modal→Is-embedding-η m
        }

    _ : _≃_.to (≡≃η≡η m) p ≡ cong η p
    _ = refl _

    _ : _≃_.from (≡≃η≡η m) p ≡ lemma (m , p)
    _ = refl _

  ----------------------------------------------------------------------
  -- Accessibility-modal modalities

  -- I did not take the definitions or lemmas in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code.

  -- The operator _[_]◯_ lifts a relation from A to ◯ A.

  infix 4 _[_]◯_

  _[_]◯_ : ◯ A → (A → A → Type a) → ◯ A → Type a
  x [ _<_ ]◯ y =
    ◯ (∃ λ x′ → ∃ λ y′ → x ≡ η x′ × y ≡ η y′ × (x′ < y′))

  -- If ◯ (x < y) is inhabited, then η x [ _<_ ]◯ η y holds.
  --
  -- See also Modality.Left-exact.η-[]◯-η≃◯.

  ◯→η-[]◯-η : ◯ (x < y) → η x [ _<_ ]◯ η y
  ◯→η-[]◯-η = ◯-map (λ x<y → _ , _ , refl _ , refl _ , x<y)

  -- If A is modal and _<_ has type A → A → Type a, then
  -- η x [ _<_ ]◯ η y is equivalent to ◯ (x < y).
  --
  -- See also Modality.Left-exact.⇔[]◯ and Modality.Left-exact.≃[]◯.

  η-[]◯-η≃◯ :
    {_<_ : A → A → Type a} →
    Modal A →
    (η x [ _<_ ]◯ η y) ≃ ◯ (x < y)
  η-[]◯-η≃◯ {x = x} {y = y} {_<_ = _<_} m =
    η x [ _<_ ]◯ η y                                           ↔⟨⟩

    ◯ (∃ λ x′ → ∃ λ y′ → η x ≡ η x′ × η y ≡ η y′ × (x′ < y′))  ↝⟨ (∃-cong λ _ →
                                                                   (∃-cong λ _ →
                                                                    (∃-cong λ _ →
                                                                     Modal→◯Σ≃Σ◯ (Separated-◯ _ _)) F.∘
                                                                    Modal→◯Σ≃Σ◯ (Separated-◯ _ _)) F.∘
                                                                   Modal→◯Σ≃Σ◯ m) F.∘
                                                                  Modal→◯Σ≃Σ◯ m ⟩

    (∃ λ x′ → ∃ λ y′ → η x ≡ η x′ × η y ≡ η y′ × ◯ (x′ < y′))  ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                   Eq.≃-≡ (Modal→≃◯ m)
                                                                     ×-cong
                                                                   ×-cong₁ λ _ → Eq.≃-≡ (Modal→≃◯ m)) ⟩

    (∃ λ x′ → ∃ λ y′ → x ≡ x′ × y ≡ y′ × ◯ (x′ < y′))          ↔⟨ (∃-cong λ _ → Σ-assoc) F.∘
                                                                  Σ-assoc F.∘
                                                                  (∃-cong λ _ → ∃-comm) ⟩
    (∃ λ ((x′ , _) : ∃ λ x′ → x ≡ x′) →
     ∃ λ ((y′ , _) : ∃ λ y′ → y ≡ y′) →
     ◯ (x′ < y′))                                              ↔⟨ drop-⊤-left-Σ $
                                                                  _⇔_.to contractible⇔↔⊤ $
                                                                  other-singleton-contractible _ ⟩

    (∃ λ ((y′ , _) : ∃ λ y′ → y ≡ y′) → ◯ (x < y′))            ↔⟨ drop-⊤-left-Σ $
                                                                  _⇔_.to contractible⇔↔⊤ $
                                                                  other-singleton-contractible _ ⟩□
    ◯ (x < y)                                                  □

  -- If A is modal, _<_ is pointwise stable, and x : A is accessible
  -- with respect to _<_, then η x is accessible with respect to
  -- _[ _<_ ]◯_.

  Modal→Acc→Acc-[]◯-η :
    {@0 A : Type a} {@0 _<_ : A → A → Type a} {@0 x : A} →
    @0 Modal A →
    @0 ({x y : A} → Stable (x < y)) →
    @0 Acc _<_ x → Acc _[ _<_ ]◯_ (η x)
  Modal→Acc→Acc-[]◯-η {_<_ = _<_} {x = x} m s a =
    A.Acc-erasure-stable
      E.[                           $⟨ a ⟩
          Acc _<_ x                 →⟨ subst (Acc _<_) (sym η⁻¹-η) ⟩
          Acc _<_ (η⁻¹ m (η x))     →⟨ (λ acc → A.Acc-on acc) ⟩
          Acc (_<_ on η⁻¹ m) (η x)  →⟨ (λ acc → A.Acc-map lemma acc) ⟩□
          Acc _[ _<_ ]◯_ (η x)      □
        ]
    where
    @0 lemma : y [ _<_ ]◯ z → η⁻¹ m y < η⁻¹ m z
    lemma {y = y} {z = z} =
      y [ _<_ ]◯ z                      →⟨ subst (uncurry _[ _<_ ]◯_) (sym $ cong₂ _,_ η-η⁻¹ η-η⁻¹) ⟩
      η (η⁻¹ m y) [ _<_ ]◯ η (η⁻¹ m z)  ↔⟨ η-[]◯-η≃◯ m ⟩
      ◯ (η⁻¹ m y < η⁻¹ m z)             →⟨ s ⟩□
      η⁻¹ m y < η⁻¹ m z                 □

  -- If A is modal and _<_ is pointwise stable and well-founded, then
  -- _[ _<_ ]◯_ is well-founded.

  Modal→Well-founded→Well-founded-[]◯ :
    {@0 A : Type a} {@0 _<_ : A → A → Type a} →
    @0 Modal A →
    @0 ({x y : A} → Stable (x < y)) →
    @0 Well-founded _<_ → Well-founded _[ _<_ ]◯_
  Modal→Well-founded→Well-founded-[]◯ {_<_ = _<_} m s wf =
    A.Well-founded-erasure-stable
      E.[                                       $⟨ wf ⟩
          (∀ x → Acc _<_ x)                     →⟨ ((λ acc → Modal→Acc→Acc-[]◯-η m s acc) ∘_) ∘ (_∘ η⁻¹ m) ⟩
          (∀ x → Acc _[ _<_ ]◯_ (η (η⁻¹ m x)))  →⟨ subst (Acc _) η-η⁻¹ ∘_ ⟩□
          (∀ x → Acc _[ _<_ ]◯_ x)              □
        ]

  -- A definition of what it means to be accessibility-modal for a
  -- given type and relation.

  Accessibility-modal-for : {A : Type a} → (A → A → Type a) → Type a
  Accessibility-modal-for _<_ =
    (∀ {x} → Acc _<_ x → Acc _[ _<_ ]◯_ (η x)) ×
    (∀ {x} → Stable (Acc _[ _<_ ]◯_ x))

  -- A definition of what it means to be accessibility-modal.
  --
  -- The erasure modality is both very modal and accessibility-modal,
  -- and the zero modality is very modal but not accessibility-modal.
  -- TODO: Is there some accessibility-modal modality that is not very
  -- modal?

  Accessibility-modal : Type (lsuc a)
  Accessibility-modal =
    {A : Type a} {_<_ : A → A → Type a} →
    Accessibility-modal-for _<_

  -- If the modality is accessibility-modal for _<_, then
  -- Acc _[ _<_ ]◯_ x is stable.

  Stable-Acc-[]◯ :
    Accessibility-modal-for _<_ →
    Stable (Acc _[ _<_ ]◯_ x)
  Stable-Acc-[]◯ acc = acc .proj₂

  -- If the modality is accessibility-modal for _<_, then
  -- Acc _[ _<_ ]◯_ x is modal (assuming function extensionality).

  Modal-Acc-[]◯ :
    Extensionality a a →
    Accessibility-modal-for _<_ →
    Modal (Acc _[ _<_ ]◯_ x)
  Modal-Acc-[]◯ ext acc =
    Stable→left-inverse→Modal
      (Stable-Acc-[]◯ acc)
      (λ _ → A.Acc-propositional ext _ _)

  -- If the modality is accessibility-modal for _<_ and x is
  -- accessible with respect to _<_, then η x is accessible with
  -- respect to _[ _<_ ]◯_.

  Acc-[]◯-η :
    Accessibility-modal-for _<_ →
    Acc _<_ x → Acc _[ _<_ ]◯_ (η x)
  Acc-[]◯-η acc = acc .proj₁

  -- If the modality is accessibility-modal for _<_, then Acc _<_ x is
  -- stable.

  Stable-Acc :
    {_<_ : A → A → Type a} →
    Accessibility-modal-for _<_ →
    Stable (Acc _<_ x)
  Stable-Acc {x = x} {_<_ = _<_} acc =
    ◯ (Acc _<_ x)             →⟨ ◯-map (Acc-[]◯-η acc) ⟩
    ◯ (Acc _[ _<_ ]◯_ (η x))  →⟨ Stable-Acc-[]◯ acc ⟩
    Acc _[ _<_ ]◯_ (η x)      →⟨ lemma ⟩□
    Acc _<_ x                 □
    where
    lemma : ∀ {x} → Acc _[ _<_ ]◯_ (η x) → Acc _<_ x
    lemma (A.acc f) =
      A.acc λ y y<x → lemma (f (η y) (◯→η-[]◯-η (η y<x)))

  -- If the modality is accessibility-modal for _<_, then Acc _<_ x is
  -- modal (assuming function extensionality).

  Modal-Acc :
    Extensionality a a →
    Accessibility-modal-for _<_ →
    Modal (Acc _<_ x)
  Modal-Acc ext acc =
    Stable→left-inverse→Modal
      (Stable-Acc acc)
      (λ _ → A.Acc-propositional ext _ _)

  -- If the modality is accessibility-modal for _<_ and _<_ is
  -- well-founded, then _[ _<_ ]◯_ is well-founded.

  Well-founded-[]◯ :
    Accessibility-modal-for _<_ →
    Well-founded _<_ → Well-founded _[ _<_ ]◯_
  Well-founded-[]◯ {_<_ = _<_} acc wf =
    ◯-elim′
      (λ _ → Stable-Acc-[]◯ acc)
      (λ x →                   $⟨ wf x ⟩
         Acc _<_ x             →⟨ Acc-[]◯-η acc ⟩□
         Acc _[ _<_ ]◯_ (η x)  □)

  -- If ◯ (↑ a Bool) is a proposition, then the modality is not
  -- accessibility-modal.

  Is-proposition-◯→¬-Accessibility-modal :
    Is-proposition (◯ (↑ a Bool)) →
    ¬ Accessibility-modal
  Is-proposition-◯→¬-Accessibility-modal prop acc =
                                      $⟨ Acc-false ⟩
    Acc _<₁_ false                    →⟨ (λ hyp → A.Acc-on hyp) ⟩
    Acc _<₂_ (lift false)             →⟨ Acc-[]◯-η acc ⟩
    Acc _[ _<₂_ ]◯_ (η (lift false))  →⟨ A.<→¬-Acc cyclic ⟩□
    ⊥                                 □
    where
    _<₁_ : Bool → Bool → Type a
    false <₁ true = ↑ _ ⊤
    _     <₁ _    = ⊥

    _<₂_ : ↑ a Bool → ↑ a Bool → Type a
    _<₂_ = _<₁_ on lower

    Acc-false : Acc _<₁_ false
    Acc-false = A.acc λ where
      true  ()
      false ()

    cyclic : η (lift false) [ _<₂_ ]◯ η (lift false)
    cyclic =
      η ( lift false
        , lift true
        , prop _ _
        , prop _ _
        , lift tt
        )

  -- Accessibility-modal-for _<_ is propositional (assuming function
  -- extensionality).

  Accessibility-modal-for-propositional :
    Extensionality a a →
    Is-proposition (Accessibility-modal-for _<_)
  Accessibility-modal-for-propositional ext =
    ×-closure 1
      (implicit-Π-closure ext 1 λ _ →
       Π-closure ext 1 λ _ →
       A.Acc-propositional ext) $
      (implicit-Π-closure ext 1 λ _ →
       Π-closure ext 1 λ _ →
       A.Acc-propositional ext)

  -- Accessibility-modal is propositional (assuming function
  -- extensionality).

  Accessibility-modal-propositional :
    Extensionality (lsuc a) (lsuc a) →
    Is-proposition Accessibility-modal
  Accessibility-modal-propositional ext =
    implicit-Π-closure ext                                1 λ _ →
    implicit-Π-closure (lower-extensionality lzero _ ext) 1 λ _ →
    Accessibility-modal-for-propositional
      (lower-extensionality _ _ ext)

  -- Accessibility-modal-for _<_ is "erasure-stable".

  Accessibility-modal-for-erasure-stable :
    {@0 A : Type a} {@0 _<_ : A → A → Type a} →
    E.Stable (Accessibility-modal-for _<_)
  Accessibility-modal-for-erasure-stable E.[ acc₁ , acc₂ ] =
      (λ acc → A.Acc-map id (acc₁ acc))
    , (λ acc → A.Acc-map id (acc₂ acc))

  -- Accessibility-modal is "erasure-stable".

  Accessibility-modal-erasure-stable :
    E.Stable Accessibility-modal
  Accessibility-modal-erasure-stable E.[ acc ] =
    Accessibility-modal-for-erasure-stable E.[ acc ]

  -- Accessibility-modal modalities are empty-modal.

  Accessibility-modal→Empty-modal : Accessibility-modal → Empty-modal M
  Accessibility-modal→Empty-modal acc =
    Stable→left-inverse→Modal
      stable
      (λ x → ⊥-elim x)
    where
    stable =
      ◯ ⊥                                           →⟨ ◯-map ⊥-elim ⟩
      ◯ (Acc _[ (λ _ _ → ↑ a ⊤) ]◯_ (η (lift tt)))  →⟨ Stable-Acc-[]◯ acc ⟩
      Acc _[ (λ _ _ → ↑ a ⊤) ]◯_ (η (lift tt))      →⟨ ⊥-elim ∘ A.<→¬-Acc (◯→η-[]◯-η (η _)) ⟩□
      ⊥                                             □

  -- An unfolding lemma for ◯ (W A (P ∘ η)).
  --
  -- See also ◯Wη≃Σ◯Π◯Wη in Modality.Has-choice.

  ◯Wη→Σ◯Π◯Wη :
    {P : ◯ A → Type a} →
    ◯ (W A (P ∘ η)) → Σ (◯ A) (λ x → P x → ◯ (W A (P ∘ η)))
  ◯Wη→Σ◯Π◯Wη =
    ◯-elim′
      (λ _ → Stable-Σ Modal-◯ λ _ →
             Stable-Π λ _ →
             Modal→Stable Modal-◯)
      (λ where
         (sup x f) → η x , η ∘ f)

  -- A "computation rule" for ◯Wη→Σ◯Π◯Wη.

  ◯Wη→Σ◯Π◯Wη-η :
    Extensionality a a →
    ◯Wη→Σ◯Π◯Wη (η (sup x f)) ≡ (η x , η ∘ f)
  ◯Wη→Σ◯Π◯Wη-η {x = x} {f = f} ext =
    ◯-elim′-η′
      (Stable-Σ Modal-◯
         (λ _ → Stable-Π λ _ → Modal→Stable Modal-◯)
         (η (η x , η ∘ f))                                 ≡⟨ (cong (λ s → Stable-Σ Modal-◯ s (η (η x , η ∘ f))) $
                                                               apply-ext ext λ _ →
                                                               Stable-Π-Modal-Π ext) ⟩
       Stable-Σ Modal-◯
         (λ _ → Modal→Stable $ Modal-Π ext λ _ → Modal-◯)
         (η (η x , η ∘ f))                                 ≡⟨ Stable-Σ-Modal-Σ
                                                                (λ _ → Modal-Π ext λ _ → Modal-◯) ⟩
       Modal→Stable
         (Modal-Σ Modal-◯ λ _ →
          Modal-Π ext λ _ → Modal-◯)
         (η (η x , η ∘ f))                                 ≡⟨ Modal→Stable-η ⟩∎

       (η x , η ∘ f)                                       ∎)

  private

    -- A lemma used in the implementation of ◯Wη→W◯.

    ◯Wη→W◯-Acc :
      @0 Extensionality a a →
      (x : ◯ (W A (P ∘ η))) →
      @0 Acc _[ _<W_ ]◯_ x →
      W (◯ A) P
    ◯Wη→W◯-Acc {P = P} ext w (A.acc a) =
      sup x′ λ y → ◯Wη→W◯-Acc ext (f′ y) (a (f′ y) (f′<w y))
      where
      p′ = ◯Wη→Σ◯Π◯Wη {P = P} w

      x′ = p′ .proj₁
      f′ = p′ .proj₂

      @0 f′<w : ∀ y → f′ y [ _<W_ ]◯ w
      f′<w =
        ◯-elim′
          {P = λ w →
                 let (x′ , f′) = ◯Wη→Σ◯Π◯Wη {P = P} w in
                 ∀ y → f′ y [ _<W_ ]◯ w}
          (λ _ → Stable-Π λ _ → Modal→Stable Modal-◯)
          (λ @0 where
             w@(sup x f) y →
               let x′ , f′ = ◯Wη→Σ◯Π◯Wη (η w)

                   @0 lemma : (x′ , f′) ≡ (η x , η ∘ f)
                   lemma = ◯Wη→Σ◯Π◯Wη-η ext
               in
               η ( f (subst (P ∘ proj₁) lemma y)
                 , w
                 , (f′ y                               ≡⟨ elim₁
                                                            (λ {(x′ , f′)} eq →
                                                               (y : P x′) → f′ y ≡ η (f (subst (P ∘ proj₁) eq y)))
                                                            (λ _ → cong (η ∘ f) $ sym $ subst-refl _ _)
                                                            lemma y ⟩∎
                    η (f (subst (P ∘ proj₁) lemma y))  ∎)
                 , (η w  ∎)
                 , (_ , refl _)
                 ))
          w

    -- A "computation rule" for ◯Wη→W◯-Acc.

    ◯Wη→W◯-Acc-η :
      (@0 ext : Extensionality a a) →
      Extensionality a a →
      []-cong-axiomatisation a →
      (x : W A (P ∘ η))
      (@0 acc : Acc _[ _<W_ ]◯_ (η x)) →
      ◯Wη→W◯-Acc {P = P} ext (η x) acc ≡ W-map η id x
    ◯Wη→W◯-Acc-η {A = A} {P = P} ext ext′ ax (sup x f) (A.acc acc) =
      cong (uncurry sup) $
      Σ-≡,≡→≡
        (cong proj₁ lemma)
        (apply-ext ext′ λ y →
           let @0 acc₁ : ∀ y → Acc _[ _<W_ ]◯_ (p′ .proj₂ y)
               acc₁ = _
           in
           subst (λ y → P y → W (◯ A) P)
             (cong proj₁ lemma)
             (λ y → ◯Wη→W◯-Acc ext (p′ .proj₂ y) (acc₁ y))
             y
                                                            ≡⟨ elim₁
                                                                 (λ {(x′ , f′)} lemma →
                                                                    (y : P (η x))
                                                                    (@0 acc₁ : (y : P x′) → Acc _[ _<W_ ]◯_ (f′ y)) →
                                                                    subst (λ y → P y → W (◯ A) P)
                                                                      (cong proj₁ lemma)
                                                                      (λ y → ◯Wη→W◯-Acc ext (f′ y) (acc₁ y))
                                                                      y ≡
                                                                    ◯Wη→W◯-Acc ext (η (f y)) (acc₂ y))
                                                                 (λ y (@0 acc₁) →
             subst (λ y → P y → W (◯ A) P)
               (cong proj₁ (refl _))
               (λ y → ◯Wη→W◯-Acc ext (η (f y)) (acc₁ y))
               y                                                    ≡⟨ cong (_$ y) $ cong (flip (subst (λ y → P y → W (◯ A) P)) _) $
                                                                       cong-refl _ ⟩
             subst (λ y → P y → W (◯ A) P)
               (refl _)
               (λ y → ◯Wη→W◯-Acc ext (η (f y)) (acc₁ y))
               y                                                    ≡⟨ cong (_$ y) $ subst-refl _ _ ⟩

             ◯Wη→W◯-Acc ext (η (f y)) (acc₁ y)                      ≡⟨ cong (λ acc → ◯Wη→W◯-Acc ext (η (f y)) (E.erased acc)) $
                                                                       []-cong-axiomatisation.[]-cong ax E.[ A.Acc-propositional ext _ _ ] ⟩∎
             ◯Wη→W◯-Acc ext (η (f y)) (acc₂ y)                      ∎)
                                                                 lemma y acc₁ ⟩

           ◯Wη→W◯-Acc ext (η (f y)) (acc₂ y)                ≡⟨ ◯Wη→W◯-Acc-η ext ext′ ax (f y) (acc₂ y) ⟩∎

           W-map η id (f y)                                 ∎)
      where
      p′ = ◯Wη→Σ◯Π◯Wη {P = P} (η (sup x f))

      lemma : p′ ≡ (η x , η ∘ f)
      lemma = ◯Wη→Σ◯Π◯Wη-η ext′

      @0 acc₂ : ∀ y → Acc _[ _<W_ ]◯_ (η (f y))
      acc₂ y =
        acc (η (f y)) (η (_ , _ , refl _ , refl _ , _ , refl _))

  -- If the modality is accessibility-modal for a certain relation,
  -- then ◯ (W A (P ∘ η)) implies W (◯ A) P (assuming function
  -- extensionality).
  --
  -- See also W◯→◯Wη and ◯Wη≃W◯ in Modality.Has-choice.

  ◯Wη→W◯ :
    {P : ◯ A → Type a} →
    @0 Accessibility-modal-for (_<W_ {A = A} {P = P ∘ η}) →
    @0 Extensionality a a →
    ◯ (W A (P ∘ η)) → W (◯ A) P
  ◯Wη→W◯ {A = A} {P = P} acc ext =
    ◯ (W A (P ∘ η))                                      →⟨ ◯-map (λ x → x , A.Well-founded-W x) ⟩
    ◯ (∃ λ (x : W A (P ∘ η)) → Acc _<W_ x)               →⟨ ◯-map (Σ-map id (acc′ .proj₁)) ⟩
    ◯ (∃ λ (x : W A (P ∘ η)) → Acc _[ _<W_ ]◯_ (η x))    →⟨ ◯Ση≃Σ◯◯ _ ⟩
    (∃ λ (x : ◯ (W A (P ∘ η))) → ◯ (Acc _[ _<W_ ]◯_ x))  →⟨ Σ-map id (acc′ .proj₂) ⟩
    (∃ λ (x : ◯ (W A (P ∘ η))) → Acc _[ _<W_ ]◯_ x)      →⟨ (λ (x , a) → ◯Wη→W◯-Acc ext x a) ⟩□
    W (◯ A) P                                            □
    where
    acc′ = Accessibility-modal-for-erasure-stable E.[ acc ]

  -- A "computation rule" for ◯Wη→W◯.
  --
  -- Note that the final argument can be proved using the previous
  -- one, see Erased.Level-1.Extensionality→[]-cong-axiomatisation.

  ◯Wη→W◯-η :
    {x : W A (P ∘ η)}
    (@0 acc : Accessibility-modal-for _<W_)
    (@0 ext : Extensionality a a) →
    Extensionality a a →
    []-cong-axiomatisation a →
    ◯Wη→W◯ {P = P} acc ext (η x) ≡ W-map η id x
  ◯Wη→W◯-η {A = A} {P = P} {x = x} acc ext ext′ ax =
    (λ (x , a) → ◯Wη→W◯-Acc ext x (acc′ .proj₂ a))
      (◯Ση≃Σ◯◯ _
         (◯-map (Σ-map id (acc′ .proj₁))
            (◯-map (λ x → x , A.Well-founded-W x) (η x))))  ≡⟨ cong (λ (x , a) → ◯Wη→W◯-Acc ext x (acc′ .proj₂ a)) $
                                                               trans (cong (◯Ση≃Σ◯◯ _) $
                                                                      trans (cong (◯-map _) ◯-map-η)
                                                                      ◯-map-η)
                                                               ◯-rec-η ⟩
    (λ (x , a) → ◯Wη→W◯-Acc ext x (acc′ .proj₂ a))
      (η x , η (acc′ .proj₁ (A.Well-founded-W x)))          ≡⟨⟩

    ◯Wη→W◯-Acc ext (η x)
      (acc′ .proj₂ (η (acc′ .proj₁ (A.Well-founded-W x))))  ≡⟨ ◯Wη→W◯-Acc-η ext ext′ ax _ _ ⟩∎

    W-map η id x                                            ∎
    where
    acc′ = Accessibility-modal-for-erasure-stable E.[ acc ]

  -- If the modality is accessibility-modal for a certain relation and
  -- A is modal, then W A P is stable (assuming function
  -- extensionality).
  --
  -- See also Modal-W in Modality.Has-choice.

  Stable-W :
    @0 Accessibility-modal-for (_<W_ {A = A} {P = P}) →
    @0 Extensionality a a →
    Modal A →
    Stable (W A P)
  Stable-W {A = A} {P = P} acc ext m =
    ◯ (W A P)                         →⟨ ◯-map $ W-map id (subst P Modal→Stable-η) ⟩
    ◯ (W A (P ∘ Modal→Stable m ∘ η))  →⟨ ◯Wη→W◯ acc′ ext ⟩
    W (◯ A) (P ∘ Modal→Stable m)      →⟨ W-map (Modal→Stable m) id ⟩□
    W A P                             □
    where
    @0 acc′ :
      Accessibility-modal-for
        (_<W_ {A = A} {P = P ∘ Modal→Stable m ∘ η})
    acc′ =
      subst
        (λ f → Accessibility-modal-for (_<W_ {A = A} {P = P ∘ f}))
        (apply-ext ext λ _ → sym Modal→Stable-η)
        acc

  ----------------------------------------------------------------------
  -- W-modal modalities

  -- I did not take the lemma in this section from "Modalities in
  -- Homotopy Type Theory" or the corresponding Coq code.

  -- W-modal modalities are empty-modal.

  W-modal→Empty-modal : W-modal M → Empty-modal M
  W-modal→Empty-modal =
    W-modal M                      →⟨ (λ m → m Modal-⊤) ⟩
    Modal (W (↑ a ⊤) λ _ → ↑ a ⊤)  →⟨ Modal-respects-↠ record
                                        { logical-equivalence = record
                                          { to   = ⊥-elim ∘ inhabited⇒W-empty _
                                          ; from = λ ()
                                          }
                                        ; right-inverse-of = λ ()
                                        } ⟩□
    Empty-modal M                  □

  ----------------------------------------------------------------------
  -- Applicative functor application

  -- I did not take the results in this section from "Modalities in
  -- Homotopy Type Theory" or the corresponding Coq code (but perhaps
  -- something resembling at least some of these results can be found
  -- there).

  -- "Applicative functor application".

  ◯-map-◯ : ◯ (A → B) → ◯ A → ◯ B
  ◯-map-◯ {A = A} {B = B} = curry
    (◯ (A → B) × ◯ A  ↔⟨ inverse ◯× ⟩
     ◯ ((A → B) × A)  →⟨ ◯-map (uncurry _$_) ⟩□
     ◯ B              □)

  -- Three "computation rules" for ◯-map-◯.

  ◯-map-◯-η : ◯-map-◯ (η f) (η x) ≡ η (f x)
  ◯-map-◯-η {f = f} {x = x} =
    ◯-map (uncurry _$_) (_≃_.from ◯× (η f , η x))  ≡⟨ cong (◯-map _) ◯×⁻¹-η ⟩
    ◯-map (uncurry _$_) (η (f , x))                ≡⟨ ◯-map-η ⟩∎
    η (f x)                                        ∎

  ◯-map-◯-ηˡ : ◯-map-◯ (η f) x ≡ ◯-map f x
  ◯-map-◯-ηˡ {f = f} {x = x} =
    ◯-elim
      {P = λ x → ◯-map-◯ (η f) x ≡ ◯-map f x}
      (λ _ → Separated-◯ _ _)
      (λ x →
         ◯-map-◯ (η f) (η x)  ≡⟨ ◯-map-◯-η ⟩
         η (f x)              ≡⟨ sym ◯-map-η ⟩∎
         ◯-map f (η x)        ∎)
      x

  ◯-map-◯-ηʳ : ◯-map-◯ f (η x) ≡ ◯-map (_$ x) f
  ◯-map-◯-ηʳ {f = f} {x = x} =
    ◯-elim
      {P = λ f → ◯-map-◯ f (η x) ≡ ◯-map (_$ x) f}
      (λ _ → Separated-◯ _ _)
      (λ f →
         ◯-map-◯ (η f) (η x)  ≡⟨ ◯-map-◯-η ⟩
         η (f x)              ≡⟨ sym ◯-map-η ⟩∎
         ◯-map (_$ x) (η f)   ∎)
      f

  ----------------------------------------------------------------------
  -- Some commutation properties

  -- I did not take the definitions or results in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code.

  -- A generalisation of ◯-cong-⇔.

  ◯-cong-⇔-◯ : ◯ (A ⇔ B) → ◯ A ⇔ ◯ B
  ◯-cong-⇔-◯ {A = A} {B = B} =
    ◯ (A ⇔ B)                  ↔⟨ ◯-cong-↔ ⇔↔→×→ ⟩
    ◯ ((A → B) × (B → A))      ↔⟨ ◯× ⟩
    ◯ (A → B) × ◯ (B → A)      →⟨ Σ-map ◯-map-◯ ◯-map-◯ ⟩
    (◯ A → ◯ B) × (◯ B → ◯ A)  ↔⟨ inverse ⇔↔→×→ ⟩□
    ◯ A ⇔ ◯ B                  □

  -- A lemma that can be used to prove that ◯ (F A B) implies
  -- F (◯ A) (◯ B).

  ◯↝→◯↝◯ :
    {F : Type a → Type a → Type a}
    {P : {A B : Type a} → (A → B) → Type a} →
    (∀ {A B} → F A B ↔ (∃ λ (f : A → B) → P f)) →
    ({f : A → B} → ◯ (P f) → P (◯-map f)) →
    ({f g : ◯ A → ◯ B} → (∀ x → f x ≡ g x) → P f → P g) →
    ({f : ◯ A → ◯ B} → Stable (P f)) →
    ◯ (F A B) → F (◯ A) (◯ B)
  ◯↝→◯↝◯ {A = A} {B = B} {F = F} {P = P} F↔ ◯∘P→P∘◯-map P-map P-stable =
    ◯ (F A B)                                  ↔⟨ ◯-cong-↔ F↔ ⟩
    ◯ (∃ λ (f : A → B) → P f)                  ↔⟨ inverse ◯Σ◯≃◯Σ ⟩
    ◯ (∃ λ (f : A → B) → ◯ (P f))              →⟨ (◯-map $ ∃-cong λ _ → ◯∘P→P∘◯-map) ⟩
    ◯ (∃ λ (f : A → B) → P (◯-map f))          →⟨ (◯-map $ ∃-cong λ _ → P-map λ _ → sym ◯-map-◯-ηˡ) ⟩
    ◯ (∃ λ (f : A → B) → P (◯-map-◯ (η f)))    →⟨ ◯Ση≃Σ◯◯ _ ⟩
    (∃ λ (f : ◯ (A → B)) → ◯ (P (◯-map-◯ f)))  →⟨ Σ-map ◯-map-◯ id ⟩
    (∃ λ (f : ◯ A → ◯ B) → ◯ (P f))            →⟨ (∃-cong λ _ → P-stable) ⟩
    (∃ λ (f : ◯ A → ◯ B) → P f)                ↔⟨ inverse F↔ ⟩□
    F (◯ A) (◯ B)                              □

  private

    -- An example of how ◯↝→◯↝◯ can be used.

    ◯-cong-⇔-◯′ : ◯ (A ⇔ B) → ◯ A ⇔ ◯ B
    ◯-cong-⇔-◯′ =
      ◯↝→◯↝◯
        ⇔↔→×→
        ◯-map-◯
        (λ _ → id)
        (Stable-Π λ _ → Modal→Stable Modal-◯)

  -- ◯ (Split-surjective f) implies Split-surjective (◯-map f).

  ◯-Split-surjective→Split-surjective :
    ◯ (Split-surjective f) → Split-surjective (◯-map f)
  ◯-Split-surjective→Split-surjective {f = f} =
    ◯ (∀ y → ∃ λ x → f x ≡ y)              →⟨ ◯Π→Π◯ ⟩
    (∀ y → ◯ (∃ λ x → f x ≡ y))            →⟨ (∀-cong _ λ _ → _≃_.from ◯Σ◯≃◯Σ) ⟩
    (∀ y → ◯ (∃ λ x → ◯ (f x ≡ y)))        →⟨ (∀-cong _ λ _ → ◯-map $ ∃-cong λ _ → η-cong) ⟩
    (∀ y → ◯ (∃ λ x → η (f x) ≡ η y))      →⟨ _⇔_.from $ Π◯◯≃Π◯η _ ⟩
    (∀ y → ◯ (∃ λ x → η (f x) ≡ y))        →⟨ (∀-cong _ λ _ → ◯-map $ ∃-cong λ _ → subst (_≡ _) (sym ◯-map-η)) ⟩
    (∀ y → ◯ (∃ λ x → ◯-map f (η x) ≡ y))  →⟨ (∀-cong _ λ _ → ◯Ση≃Σ◯◯ _) ⟩
    (∀ y → ∃ λ x → ◯ (◯-map f x ≡ y))      →⟨ (∀-cong _ λ _ → ∃-cong λ _ → Modal→Stable (Separated-◯ _ _)) ⟩□
    (∀ y → ∃ λ x → ◯-map f x ≡ y)          □

  -- A generalisation of ◯-cong-↠.

  ◯-cong-↠-◯ : ◯ (A ↠ B) → ◯ A ↠ ◯ B
  ◯-cong-↠-◯ =
    ◯↝→◯↝◯
      ↠↔∃-Split-surjective
      ◯-Split-surjective→Split-surjective
      (Split-surjective-cong _)
      (Stable-Π λ _ → Modal→Stable $
       Modal-Σ Modal-◯ λ _ → Separated-◯ _ _)

  -- ◯ (Has-quasi-inverse f) implies Has-quasi-inverse (◯-map f).

  ◯-Has-quasi-inverse→Has-quasi-inverse :
    ◯ (Has-quasi-inverse f) → Has-quasi-inverse (◯-map f)
  ◯-Has-quasi-inverse→Has-quasi-inverse {f = f} =
    ◯ (∃ λ g → (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x))              ↔⟨ inverse ◯Σ◯≃◯Σ ⟩

    ◯ (∃ λ g → ◯ ((∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x)))          ↔⟨ (◯-cong-≃ $ ∃-cong λ _ → ◯×) ⟩

    ◯ (∃ λ g → ◯ (∀ x → f (g x) ≡ x) × ◯ (∀ x → g (f x) ≡ x))          →⟨ (◯-map $ ∃-cong λ _ → ◯Π→Π◯ ×-cong ◯Π→Π◯) ⟩

    ◯ (∃ λ g → (∀ x → ◯ (f (g x) ≡ x)) × (∀ x → ◯ (g (f x) ≡ x)))      →⟨ (◯-map $ ∃-cong λ _ →
                                                                           (∀-cong _ λ _ → η-cong) ×-cong (∀-cong _ λ _ → η-cong)) ⟩

    ◯ (∃ λ g → (∀ x → η (f (g x)) ≡ η x) × (∀ x → η (g (f x)) ≡ η x))  →⟨ (◯-map $ ∃-cong λ _ →
                                                                           (∀-cong _ λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                            trans (cong (◯-map f) ◯-map-◯-η) ◯-map-η)
                                                                             ×-cong
                                                                           (∀-cong _ λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                            ◯-map-◯-η)) ⟩
    ◯ (∃ λ g → (∀ x → ◯-map f (◯-map-◯ (η g) (η x)) ≡ η x) ×
               (∀ x → ◯-map-◯ (η g) (η (f x)) ≡ η x))                  →⟨ ◯Ση≃Σ◯◯ _ ⟩

    (∃ λ g → ◯ ((∀ x → ◯-map f (◯-map-◯ g (η x)) ≡ η x) ×
                (∀ x → ◯-map-◯ g (η (f x)) ≡ η x)))                    ↔⟨ (∃-cong λ _ → ◯×) ⟩

    (∃ λ g → ◯ (∀ x → ◯-map f (◯-map-◯ g (η x)) ≡ η x) ×
             ◯ (∀ x → ◯-map-◯ g (η (f x)) ≡ η x))                      →⟨ (∃-cong λ _ → ◯Π→Π◯ ×-cong ◯Π→Π◯) ⟩

    (∃ λ g → (∀ x → ◯ (◯-map f (◯-map-◯ g (η x)) ≡ η x)) ×
             (∀ x → ◯ (◯-map-◯ g (η (f x)) ≡ η x)))                    →⟨ (∃-cong λ g → ∃-cong λ _ → ∀-cong _ λ _ → ◯-map $
                                                                           ≡⇒↝ _ $ cong ((_≡ _) ∘ ◯-map-◯ g) $ sym ◯-map-η) ⟩
    (∃ λ g → (∀ x → ◯ (◯-map f (◯-map-◯ g (η x)) ≡ η x)) ×
             (∀ x → ◯ (◯-map-◯ g (◯-map f (η x)) ≡ η x)))              →⟨ (∃-cong λ _ →
                                                                           _⇔_.from (Π◯◯≃Π◯η _) ×-cong _⇔_.from (Π◯◯≃Π◯η _)) ⟩
    (∃ λ g → (∀ x → ◯ (◯-map f (◯-map-◯ g x) ≡ x)) ×
             (∀ x → ◯ (◯-map-◯ g (◯-map f x) ≡ x)))                    →⟨ (∃-cong λ _ →
                                                                           (∀-cong _ λ _ → Modal→Stable (Separated-◯ _ _))
                                                                             ×-cong
                                                                           (∀-cong _ λ _ → Modal→Stable (Separated-◯ _ _))) ⟩
    (∃ λ g → (∀ x → ◯-map f (◯-map-◯ g x) ≡ x) ×
             (∀ x → ◯-map-◯ g (◯-map f x) ≡ x))                        →⟨ Σ-map ◯-map-◯ id ⟩□

    (∃ λ g → (∀ x → ◯-map f (g x) ≡ x) × (∀ x → g (◯-map f x) ≡ x))    □

  -- ◯ (Is-equivalence f) implies Is-equivalence (◯-map f).

  ◯-Is-equivalence→Is-equivalence :
    ◯ (Is-equivalence f) → Is-equivalence (◯-map f)
  ◯-Is-equivalence→Is-equivalence {f = f} =
    ◯ (Is-equivalence f)         →⟨ ◯-map (proj₂ ∘ _↔_.to Bijection.↔-as-Σ ∘ from-equivalence ∘ Eq.⟨ _ ,_⟩) ⟩
    ◯ (Has-quasi-inverse f)      →⟨ ◯-Has-quasi-inverse→Has-quasi-inverse ⟩
    Has-quasi-inverse (◯-map f)  →⟨ _≃_.is-equivalence ∘ from-isomorphism ∘ _↔_.from Bijection.↔-as-Σ ∘ (_ ,_) ⟩□
    Is-equivalence (◯-map f)     □

  -- A generalisation of ◯-cong-≃.

  ◯-cong-≃-◯ : ◯ (A ≃ B) → ◯ A ≃ ◯ B
  ◯-cong-≃-◯ =
    ◯↝→◯↝◯
      Eq.≃-as-Σ
      ◯-Is-equivalence→Is-equivalence
      (Is-equivalence-cong _)
      (Modal→Stable-Is-equivalence Modal-◯ Separated-◯)

  -- A generalisation of ◯-cong-↔.

  ◯-cong-↔-◯ : ◯ (A ↔ B) → ◯ A ↔ ◯ B
  ◯-cong-↔-◯ {A = A} {B = B} =
    ◯ (A ↔ B)  →⟨ ◯-map from-isomorphism ⟩
    ◯ (A ≃ B)  →⟨ ◯-cong-≃-◯ ⟩
    ◯ A ≃ ◯ B  →⟨ from-equivalence ⟩□
    ◯ A ↔ ◯ B  □

  -- ◯ (Is-equivalenceᴱ f) implies Is-equivalenceᴱ (◯-map f).

  ◯-Is-equivalenceᴱ→Is-equivalenceᴱ :
    ◯ (Is-equivalenceᴱ f) → Is-equivalenceᴱ (◯-map f)
  ◯-Is-equivalenceᴱ→Is-equivalenceᴱ {f = f} eq =
    _≃ᴱ_.is-equivalence $
    EEq.↔→≃ᴱ
      _
      (◯-map-◯ (◯-map (_≃ᴱ_.from ∘ EEq.⟨ f ,_⟩) eq))
      (◯-elim (λ _ → Separated-◯ _ _) λ x →
       ◯-elim
         (λ _ → Separated-◯ _ _)
         (λ eq →
            let equiv = EEq.⟨ f , eq ⟩ in

            ◯-map f
              (◯-map-◯ (◯-map (_≃ᴱ_.from ∘ EEq.⟨ f ,_⟩) (η eq)) (η x))  ≡⟨ cong (◯-map f) $ cong (flip ◯-map-◯ _) ◯-map-η ⟩

            ◯-map f (◯-map-◯ (η (_≃ᴱ_.from equiv)) (η x))               ≡⟨ cong (◯-map f) ◯-map-◯-η ⟩

            ◯-map f (η (_≃ᴱ_.from equiv x))                             ≡⟨ ◯-map-η ⟩

            η (f (_≃ᴱ_.from equiv x))                                   ≡⟨ cong η $ _≃ᴱ_.right-inverse-of equiv _ ⟩∎

            η x                                                         ∎)
         eq)
      (◯-elim (λ _ → Separated-◯ _ _) λ x →
       ◯-elim
         (λ _ → Separated-◯ _ _)
         (λ eq →
            let equiv = EEq.⟨ f , eq ⟩ in

            ◯-map-◯ (◯-map (_≃ᴱ_.from ∘ EEq.⟨ f ,_⟩) (η eq))
              (◯-map f (η x))                                 ≡⟨ cong₂ ◯-map-◯ ◯-map-η ◯-map-η ⟩

            ◯-map-◯ (η (_≃ᴱ_.from equiv)) (η (f x))           ≡⟨ ◯-map-◯-η ⟩

            η (_≃ᴱ_.from equiv (f x))                         ≡⟨ cong η $ _≃ᴱ_.left-inverse-of equiv _ ⟩∎

            η x                                               ∎)
         eq)

------------------------------------------------------------------------
-- Lemmas relating two modalities to each other

-- If the modal operators and units of two modalities (for a given
-- universe level) are related in a certain way, then the modalities
-- have the same modal types.

◯≃◯→Modal⇔Modal :
  (M₁ M₂ : Modality a) →
  (∃ λ (eq : ∀ A → Modality.◯ M₁ A ≃ Modality.◯ M₂ A) →
     ∀ A → _≃_.to (eq A) ∘ Modality.η M₁ ≡ Modality.η M₂) →
  (∀ A → Modality.Modal M₁ A ⇔ Modality.Modal M₂ A)
◯≃◯→Modal⇔Modal {a = a} M₁ M₂ (eq , η≡η) A =
  M₁.Modal A                                     ↝⟨ M₁.Modal≃Is-equivalence-η _ ⟩
  Is-equivalence (M₁.η {A = A})                  ↝⟨ Is-equivalence≃Is-equivalence-∘ˡ (_≃_.is-equivalence (eq A)) _ ⟩
  Is-equivalence (_≃_.to (eq A) ∘ M₁.η {A = A})  ↝⟨ Is-equivalence-cong _ (ext⁻¹ (η≡η A)) ⟩
  Is-equivalence (M₂.η {A = A})                  ↝⟨ inverse $ M₂.Modal≃Is-equivalence-η _ ⟩□
  M₂.Modal A                                     □
  where
  module M₁ = Modality M₁
  module M₂ = Modality M₂

-- Given two modalities (for a given universe level) there is an
-- equivalence between "the modalities have the same modal types" and
-- "the modal operators and units are related (in a certain way)",
-- assuming function extensionality.

Modal⇔Modal≃◯≃◯ :
  Extensionality a a →
  (M₁ M₂ : Modality a) →

  (∀ A → Modality.Modal M₁ A ⇔ Modality.Modal M₂ A)
    ↝[ lsuc a ∣ a ]
  (∃ λ (eq : ∀ A → Modality.◯ M₁ A ≃ Modality.◯ M₂ A) →
     ∀ A → _≃_.to (eq A) ∘ Modality.η M₁ ≡ Modality.η M₂)
Modal⇔Modal≃◯≃◯ {a = a} ext M₁ M₂ =
  generalise-ext?-prop
    (record { to = to; from = ◯≃◯→Modal⇔Modal M₁ M₂ })
    (λ ext′ →
       Π-closure ext′ 1 λ _ →
       ⇔-closure ext 1
         (M₁.Modal-propositional ext)
         (M₂.Modal-propositional ext))
    (λ ext′ →                                                            $⟨ (Π-closure ext′ 1 λ _ → prop) ⟩
       Is-proposition
         (∀ A →
          ∃ λ ((f , _) : ∃ λ (f : M₁.◯ A → M₂.◯ A) → f ∘ M₁.η ≡ M₂.η) →
            Is-equivalence f)                                            →⟨ H-level-cong _ 1 (inverse $ equiv ext′) ⟩□

       Is-proposition
         (∃ λ (eq : ∀ A → M₁.◯ A ≃ M₂.◯ A) →
            ∀ A → _≃_.to (eq A) ∘ M₁.η ≡ M₂.η)                           □)
  where
  module M₁ = Modality M₁
  module M₂ = Modality M₂

  module _
    (Modal⇔Modal :
       ∀ A → Modality.Modal M₁ A ⇔ Modality.Modal M₂ A)
    where

    module _ {A : Type a} where abstract

      c₁₁ : Contractible (_∘ M₁.η ⁻¹ M₁.η {A = A})
      c₁₁ =                                            $⟨ M₁.extendable-along-η (λ _ → M₁.Modal-◯) ⟩
        Is-∞-extendable-along-[ M₁.η ] (λ _ → M₁.◯ A)  ↔⟨ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩
        Is-equivalence (_∘ M₁.η)                       →⟨ (λ eq →
                                                             Preimage.bijection⁻¹-contractible
                                                               (_≃_.bijection Eq.⟨ _ , eq ⟩) _) ⟩□
        Contractible (_∘ M₁.η ⁻¹ M₁.η)                 □

      c₁₂ : Contractible (_∘ M₁.η ⁻¹ M₂.η {A = A})
      c₁₂ =                                            $⟨ M₁.extendable-along-η (λ _ → _⇔_.from (Modal⇔Modal _) M₂.Modal-◯) ⟩
        Is-∞-extendable-along-[ M₁.η ] (λ _ → M₂.◯ A)  ↔⟨ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩
        Is-equivalence (_∘ M₁.η)                       →⟨ (λ eq →
                                                             Preimage.bijection⁻¹-contractible
                                                               (_≃_.bijection Eq.⟨ _ , eq ⟩) _) ⟩□
        Contractible (_∘ M₁.η ⁻¹ M₂.η)                 □

      c₂₁ : Contractible (_∘ M₂.η ⁻¹ M₁.η {A = A})
      c₂₁ =                                            $⟨ M₂.extendable-along-η (λ _ → _⇔_.to (Modal⇔Modal _) M₁.Modal-◯) ⟩
        Is-∞-extendable-along-[ M₂.η ] (λ _ → M₁.◯ A)  ↔⟨ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩
        Is-equivalence (_∘ M₂.η)                       →⟨ (λ eq →
                                                             Preimage.bijection⁻¹-contractible
                                                               (_≃_.bijection Eq.⟨ _ , eq ⟩) _) ⟩□
        Contractible (_∘ M₂.η ⁻¹ M₁.η)                 □

      c₂₂ : Contractible (_∘ M₂.η ⁻¹ M₂.η {A = A})
      c₂₂ =                                            $⟨ M₂.extendable-along-η (λ _ → M₂.Modal-◯) ⟩
        Is-∞-extendable-along-[ M₂.η ] (λ _ → M₂.◯ A)  ↔⟨ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩
        Is-equivalence (_∘ M₂.η)                       →⟨ (λ eq →
                                                             Preimage.bijection⁻¹-contractible
                                                               (_≃_.bijection Eq.⟨ _ , eq ⟩) _) ⟩□
        Contractible (_∘ M₂.η ⁻¹ M₂.η)                 □

    to =
        (λ _ →
           Eq.↔→≃
             (c₁₂ .proj₁ .proj₁)
             (c₂₁ .proj₁ .proj₁)
             (λ x →
                (c₁₂ .proj₁ .proj₁ ∘ c₂₁ .proj₁ .proj₁) x       ≡⟨ cong (λ p → proj₁ p x) $ sym $ c₂₂ .proj₂ $ _ , (

                  c₁₂ .proj₁ .proj₁ ∘ c₂₁ .proj₁ .proj₁ ∘ M₂.η       ≡⟨ cong (c₁₂ .proj₁ .proj₁ ∘_) $ c₂₁ .proj₁ .proj₂ ⟩
                  c₁₂ .proj₁ .proj₁ ∘ M₁.η                           ≡⟨ c₁₂ .proj₁ .proj₂ ⟩∎
                  M₂.η                                               ∎) ⟩

                c₂₂ .proj₁ .proj₁ x                             ≡⟨ cong (λ p → proj₁ p x) $ c₂₂ .proj₂ (_ , refl _) ⟩∎

                id x                                            ∎)
             (λ x →
                (c₂₁ .proj₁ .proj₁ ∘ c₁₂ .proj₁ .proj₁) x       ≡⟨ cong (λ p → proj₁ p x) $ sym $ c₁₁ .proj₂ $ _ , (

                  c₂₁ .proj₁ .proj₁ ∘ c₁₂ .proj₁ .proj₁ ∘ M₁.η       ≡⟨ cong (c₂₁ .proj₁ .proj₁ ∘_) $ c₁₂ .proj₁ .proj₂ ⟩
                  c₂₁ .proj₁ .proj₁ ∘ M₂.η                           ≡⟨ c₂₁ .proj₁ .proj₂ ⟩∎
                  M₁.η                                               ∎) ⟩

                c₁₁ .proj₁ .proj₁ x                             ≡⟨ cong (λ p → proj₁ p x) $ c₁₁ .proj₂ (_ , refl _) ⟩∎

                id x                                            ∎))
      , (λ _ → c₁₂ .proj₁ .proj₂)

  equiv = λ ext′ →

    (∃ λ (eq : ∀ A → M₁.◯ A ≃ M₂.◯ A) →
       ∀ A → _≃_.to (eq A) ∘ M₁.η ≡ M₂.η)                            ↝⟨ inverse ΠΣ-comm ⟩

    (∀ A → ∃ λ (eq : M₁.◯ A ≃ M₂.◯ A) → _≃_.to eq ∘ M₁.η ≡ M₂.η)     ↝⟨ (∀-cong ext′ λ _ → Σ-cong Eq.≃-as-Σ λ _ → F.id) ⟩

    (∀ A →
     ∃ λ ((f , _) : ∃ λ (f : M₁.◯ A → M₂.◯ A) → Is-equivalence f) →
       f ∘ M₁.η ≡ M₂.η)                                              ↝⟨ (∀-cong ext′ λ _ →
                                                                         Σ-assoc F.∘ (∃-cong λ _ → ×-comm) F.∘ inverse Σ-assoc) ⟩□
    (∀ A →
     ∃ λ ((f , _) : ∃ λ (f : M₁.◯ A → M₂.◯ A) → f ∘ M₁.η ≡ M₂.η) →
       Is-equivalence f)                                             □

  prop :
    Is-proposition
      (∃ λ ((f , _) : ∃ λ (f : M₁.◯ A → M₂.◯ A) → f ∘ M₁.η ≡ M₂.η) →
         Is-equivalence f)
  prop ((f₁ , eq₁) , equiv₁) ((f₂ , eq₂) , equiv₂) =
    _↔_.to (ignore-propositional-component
              (Is-equivalence-propositional ext)) $
    Σ-≡,≡→≡
      (⟨ext⟩ lemma)
      (subst (λ f → f ∘ M₁.η ≡ M₂.η) (⟨ext⟩ lemma) eq₁        ≡⟨ subst-∘ _ _ _ ⟩
       subst (_≡ M₂.η) (cong (_∘ M₁.η) $ ⟨ext⟩ lemma) eq₁     ≡⟨ cong (flip (subst _) _) $
                                                                 cong-pre-∘-ext ext ext ⟩
       subst (_≡ M₂.η) (⟨ext⟩ $ lemma ∘ M₁.η) eq₁             ≡⟨ subst-trans-sym ⟩
       trans (sym $ ⟨ext⟩ $ lemma ∘ M₁.η) eq₁                 ≡⟨ (cong (flip trans _ ∘ sym) $ cong ⟨ext⟩ $ ⟨ext⟩ λ _ →
                                                                  M₁.∘η≡∘η→≡-η) ⟩
       trans (sym $ ⟨ext⟩ $ ext⁻¹ $ trans eq₁ (sym eq₂)) eq₁  ≡⟨ cong (flip trans _ ∘ sym) $
                                                                 _≃_.right-inverse-of (Eq.extensionality-isomorphism ext) _ ⟩
       trans (sym $ trans eq₁ (sym eq₂)) eq₁                  ≡⟨ trans (cong (flip trans _) $
                                                                        sym-trans _ _) $
                                                                 trans (trans-[trans-sym]- _ _) $
                                                                 sym-sym _ ⟩∎
       eq₂                                                    ∎)
    where
    ⟨ext⟩ = apply-ext ext

    lemma : ∀ x → f₁ x ≡ f₂ x
    lemma =
      M₁.∘η≡∘η→≡
        (λ _ → M₁.Modal-respects-≃ Eq.⟨ _ , equiv₁ ⟩ M₁.Modal-◯)
        (ext⁻¹ (
           f₁ ∘ M₁.η  ≡⟨ eq₁ ⟩
           M₂.η       ≡⟨ sym eq₂ ⟩∎
           f₂ ∘ M₁.η  ∎))

-- Two modalities (for the same universe level) are equal exactly when
-- they have the same modal types (assuming function extensionality
-- and univalence).

Modal⇔Modal≃≡ :
  {M₁ M₂ : Modality a} →
  Extensionality (lsuc a) (lsuc a) →
  Univalence a →
  (∀ A → Modality.Modal M₁ A ⇔ Modality.Modal M₂ A) ≃
  (M₁ ≡ M₂)
Modal⇔Modal≃≡ {a = a} {M₁ = M₁} {M₂ = M₂} ext univ =
  (∀ A → Modality.Modal M₁ A ⇔ Modality.Modal M₂ A)                ↔⟨ (∀-cong ext λ _ →
                                                                       ⇔↔≡ ext″ univ
                                                                         (Modality.Modal-propositional M₁ ext″)
                                                                         (Modality.Modal-propositional M₂ ext″)) ⟩
  (∀ A → Modality.Modal M₁ A ≡ Modality.Modal M₂ A)                ↝⟨ Eq.extensionality-isomorphism ext ⟩
  Modality.Modal M₁ ≡ Modality.Modal M₂                            ↔⟨ (ignore-propositional-component λ M₁′ M₂′ →
                                                                       _↔_.to (ignore-propositional-component
                                                                                 (×-closure 1
                                                                                    (implicit-Π-closure ext 1 λ _ →
                                                                                     Π-closure ext′ 1 λ ext →
                                                                                     H-level-propositional ext 1) $
                                                                                  ×-closure 1
                                                                                    (implicit-Π-closure ext′ 1 λ _ →
                                                                                     Modality.Modal-propositional M₂ ext″) $
                                                                                  ×-closure 1
                                                                                    (implicit-Π-closure ext 1 λ _ →
                                                                                     implicit-Π-closure ext′ 1 λ _ →
                                                                                     Π-closure ext″ 1 λ _ →
                                                                                     Π-closure ext″ 1 λ _ →
                                                                                     Modality.Modal-propositional M₂ ext″) $
                                                                                  implicit-Π-closure ext 1 λ _ →
                                                                                  implicit-Π-closure ext′ 1 λ _ →
                                                                                  Π-closure ext″ 1 λ _ →
                                                                                  PS.Is-∞-extendable-along-propositional ext″)) $
                                                                       lemma
                                                                         (_≃_.from equiv (Modality.Modal M₂ , M₁′))
                                                                         (_≃_.from equiv (Modality.Modal M₂ , M₂′))
                                                                         (λ _ → F.id)) ⟩
  _≃_.to equiv M₁ ≡ _≃_.to equiv M₂                                ↝⟨ Eq.≃-≡ equiv ⟩□
  M₁ ≡ M₂                                                          □
  where
  ext′ : Extensionality (lsuc a) a
  ext′ = lower-extensionality lzero _ ext

  ext″ : Extensionality a a
  ext″ = lower-extensionality _ _ ext

  equiv :
    Modality a ≃
    (∃ λ (Modal : Type a → Type a) →
     ∃ λ ((◯ , η) :
          ∃ λ (◯ : Type a → Type a) → {A : Type a} → A → ◯ A) →
     ({A : Type a} → Extensionality a a → Is-proposition (Modal A)) ×
     ({A : Type a} → Modal (◯ A)) ×
     ({A B : Type a} → A ≃ B → Modal A → Modal B) ×
     ({A : Type a} {P : ◯ A → Type a} →
      (∀ x → Modal (P x)) →
      Is-∞-extendable-along-[ η ] P))
  equiv = Eq.↔→≃
    (λ M →
       let open Modality M in
         Modal
       , (◯ , η)
       , Modal-propositional
       , Modal-◯
       , Modal-respects-≃
       , extendable-along-η)
    _
    refl
    refl

  lemma :
    (M₁ M₂ : Modality a) →
    (∀ A → Modality.Modal M₁ A ⇔ Modality.Modal M₂ A) →
    _≡_ {A = ∃ λ (◯ : Type a → Type a) → {A : Type a} → A → ◯ A}
      (Modality.◯ M₁ , Modality.η M₁)
      (Modality.◯ M₂ , Modality.η M₂)
  lemma M₁ M₂ Modal⇔Modal =
    let ◯≃◯ , η≡η = Modal⇔Modal≃◯≃◯ ext″ M₁ M₂ _ Modal⇔Modal in
    Σ-≡,≡→≡
      (apply-ext ext (≃⇒≡ univ ∘ ◯≃◯))
      (implicit-extensionality ext′ λ A →

       subst (λ ◯ → ∀ {A} → A → ◯ A) (apply-ext ext (≃⇒≡ univ ∘ ◯≃◯))
         (Modality.η M₁)                                               ≡⟨ sym $
                                                                          push-subst-implicit-application _ _ ⟩
       subst (λ ◯ → A → ◯ A) (apply-ext ext (≃⇒≡ univ ∘ ◯≃◯))
         (Modality.η M₁)                                               ≡⟨ (apply-ext ext″ λ _ → sym $
                                                                           push-subst-application _ _) ⟩
       subst (λ ◯ → ◯ A) (apply-ext ext (≃⇒≡ univ ∘ ◯≃◯)) ∘
       Modality.η M₁                                                   ≡⟨ (apply-ext ext″ λ _ →
                                                                           subst-ext ext) ⟩

       subst id (≃⇒≡ univ (◯≃◯ A)) ∘ Modality.η M₁                     ≡⟨ (apply-ext ext″ λ _ →
                                                                           subst-id-in-terms-of-≡⇒↝ equivalence) ⟩

       ≡⇒→ (≃⇒≡ univ (◯≃◯ A)) ∘ Modality.η M₁                          ≡⟨ cong (λ eq → _≃_.to eq ∘ Modality.η M₁) $
                                                                          _≃_.right-inverse-of (≡≃≃ univ) _ ⟩

       _≃_.to (◯≃◯ A) ∘ Modality.η M₁                                  ≡⟨ η≡η A ⟩∎

       Modality.η M₂                                                   ∎)
