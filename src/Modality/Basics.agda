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
open import Equivalence eq-J as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased.Basics eq-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages.Basics eq-J
  using (Contractibleᴱ; _⁻¹ᴱ_)
import Equivalence.Half-adjoint eq-J as HA
open import Equivalence.Path-split eq-J as PS
  using (Is-∞-extendable-along-[_])
open import Erased.Box-cong-axiomatisation eq-J
  using ([]-cong-axiomatisation)
open import For-iterated-equality eq-J
open import Function-universe eq-J as F hiding (id; _∘_)
open import H-level eq-J as H-level
open import H-level.Closure eq-J
open import Injection eq-J using (_↣_; Injective)
open import Preimage eq-J as Preimage using (_⁻¹_)
open import Surjection eq-J using (_↠_; Split-surjective)

private
  variable
    a c d                          : Level
    A B C                          : Type a
    eq f g k m m₁ m₂ p s x y z _<_ : A
    P                              : A → Type p

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
      ◯     : Type a → Type a
      η     : A → ◯ A
      Modal : Type a → Type a

      Modal-propositional :
        Extensionality a a →
        Is-proposition (Modal A)

      Modal-◯ : Modal (◯ A)

      Modal-respects-≃ : A ≃ B → Modal A → Modal B

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

    .Modality-record.Modal-propositional ext →
      Eq.propositional ext _

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
-- Some definitions

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

-- A definition of what it means for a modality to be accessible (for
-- a certain universe level).
--
-- This definition is based on (one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory".

Accessible : (ℓ : Level) → Modality a → Type (lsuc (a ⊔ ℓ))
Accessible {a = a} ℓ M =
  ∃ λ (I : Type ℓ) →
  ∃ λ (P : I → Type ℓ) →
    (A : Type a) →
    Modal A ⇔
    ∀ i →
    Is-∞-extendable-along-[ (λ (_ : P i) → lift tt) ]
      (λ (_ : ↑ ℓ ⊤) → A)
  where
  open Modality-record M

-- A definition of what it means for a modality to be topological (for
-- a certain universe level).
--
-- This definition is based on (one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory".

Topological : (ℓ : Level) → Modality a → Type (lsuc (a ⊔ ℓ))
Topological {a = a} ℓ M =
  ∃ λ ((_ , P , _) : Accessible ℓ M) →
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
      (λ ext → Eq.propositional ext _)

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

  -- ◯ (↑ a ⊤) is equivalent to ⊤.

  ◯⊤≃ : ◯ (↑ a ⊤) ≃ ⊤
  ◯⊤≃ =
    ◯ (↑ a ⊤)  ↝⟨ inverse Eq.⟨ _ , Modal≃Is-equivalence-η _ Modal-⊤ ⟩ ⟩
    ↑ a ⊤      ↔⟨ Bijection.↑↔ ⟩□
    ⊤          □

  -- ◯ commutes with _×_.

  ◯×≃ : ◯ (A × B) ≃ (◯ A × ◯ B)
  ◯×≃ = Eq.↔→≃
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
    m′ = Modal-Σ Modal-◯ λ _ → Modal-◯

  -- Four "computation rules" for ◯×≃.

  ◯×≃-η : _≃_.to ◯×≃ (η (x , y)) ≡ (η x , η y)
  ◯×≃-η = ◯-rec-η

  ◯×≃⁻¹-ηʳ : {y : B} → _≃_.from ◯×≃ (x , η y) ≡ ◯-map (_, y) x
  ◯×≃⁻¹-ηʳ {x = x} {y = y} =
    ◯-rec Modal-◯ (λ y → ◯-map (_, y) x) (η y)  ≡⟨ ◯-rec-η ⟩∎
    ◯-map (_, y) x                              ∎

  ◯×≃⁻¹-η : {y : B} → _≃_.from ◯×≃ (η x , η y) ≡ η (x , y)
  ◯×≃⁻¹-η {x = x} {y = y} =
    _≃_.from ◯×≃ (η x , η y)  ≡⟨ ◯×≃⁻¹-ηʳ ⟩
    ◯-map (_, y) (η x)        ≡⟨ ◯-map-η ⟩∎
    η (x , y)                 ∎

  ◯×≃⁻¹-ηˡ : {y : ◯ B} → _≃_.from ◯×≃ (η x , y) ≡ ◯-map (x ,_) y
  ◯×≃⁻¹-ηˡ {x = x} {y = y} =
    ◯-elim
      {P = λ y → _≃_.from ◯×≃ (η x , y) ≡ ◯-map (x ,_) y}
      (λ _ → Separated-◯ _ _)
      (λ y →
         _≃_.from ◯×≃ (η x , η y)  ≡⟨ ◯×≃⁻¹-η ⟩
         η (x , y)                 ≡⟨ sym ◯-map-η ⟩∎
         ◯-map (x ,_) (η y)        ∎)
      y

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

  -- I did not take the remaining results in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code (but that does not mean that one cannot find something
  -- similar in those places).

  -- The right-to-left direction of Modality.Very-modal.Π◯≃◯Π.

  ◯Π→Π◯ :
    {A : Type a} {P : A → Type a} →
    ◯ ((x : A) → P x) → ((x : A) → ◯ (P x))
  ◯Π→Π◯ = flip (◯-map ∘ flip _$_)

  -- A "computation rule" for ◯Π→Π◯.

  ◯Π→Π◯-η :
    Extensionality a a →
    ◯Π→Π◯ (η f) ≡ η ∘ f
  ◯Π→Π◯-η ext = apply-ext ext λ _ → ◯-map-η

  -- The forward direction of ◯Ση≃Σ◯◯, which is defined below (and
  -- which is due to Felix Cherubini). This direction does not depend
  -- on function extensionality.

  ◯Ση→Σ◯◯ : ◯ (Σ A (P ∘ η)) → Σ (◯ A) (◯ ∘ P)
  ◯Ση→Σ◯◯ {A = A} {P = P} = ◯-rec m′ (Σ-map η η)
    where
    abstract
      m′ : Modal (Σ (◯ A) (◯ ∘ P))
      m′ = Modal-Σ Modal-◯ λ _ → Modal-◯

  -- ◯ commutes with Σ in a certain way (assuming function
  -- extensionality).
  --
  -- This lemma is due to Felix Cherubini.
  --
  -- See also Modality.Very-modal.◯Ση≃Σ◯◯.

  ◯Ση≃Σ◯◯ :
    Extensionality a a →
    ◯ (Σ A (P ∘ η)) ≃ Σ (◯ A) (◯ ∘ P)
  ◯Ση≃Σ◯◯ {A = A} {P = P} ext = Eq.↔→≃
    ◯Ση→Σ◯◯
    (Σ (◯ A) (◯ ∘ P)  →⟨ (λ (x , y) → ◯-map (x ,_) y) ⟩
     ◯ (Σ (◯ A) P)    →⟨ ◯-rec Modal-◯ (uncurry $ ◯-elim m″ $ curry η) ⟩□
     ◯ (Σ A (P ∘ η))  □)
    (uncurry $
     ◯-elim
       (λ _ → Modal-Π ext λ _ →
              Modal→Separated m′ _ _)
       (λ x →
          ◯-elim
            (λ _ → Modal→Separated m′ _ _)
            (λ y →
               ◯Ση→Σ◯◯
                 (◯-rec Modal-◯ (uncurry $ ◯-elim m″ $ curry η)
                    (◯-map (η x ,_) (η y)))                      ≡⟨ cong ◯Ση→Σ◯◯ $ cong (◯-rec _ _) ◯-map-η ⟩

               ◯Ση→Σ◯◯
                 (◯-rec Modal-◯ (uncurry $ ◯-elim m″ $ curry η)
                    (η (η x , y)))                               ≡⟨ cong ◯Ση→Σ◯◯ ◯-rec-η ⟩

               ◯Ση→Σ◯◯ (◯-elim m″ (curry η) (η x) y)             ≡⟨ cong ◯Ση→Σ◯◯ $ cong (_$ y) ◯-elim-η ⟩

               ◯Ση→Σ◯◯ (η (x , y))                               ≡⟨⟩

               ◯-rec m′ (Σ-map η η) (η (x , y))                  ≡⟨ ◯-rec-η ⟩∎

               (η x , η y)                                       ∎)))
    (◯-elim
       (λ _ → Separated-◯ _ _)
       (λ (x , y) →
          let f = λ (x , y) → ◯-map (x ,_) y in

          ◯-rec Modal-◯ (uncurry $ ◯-elim m″ $ curry η)
            (f (◯-rec m′ (Σ-map η η) (η (x , y))))                     ≡⟨ cong (◯-rec _ _) $ cong f ◯-rec-η ⟩

          ◯-rec Modal-◯ (uncurry $ ◯-elim m″ $ curry η)
            (◯-map (η x ,_) (η y))                                     ≡⟨ cong (◯-rec _ _) ◯-map-η ⟩

          ◯-rec Modal-◯ (uncurry $ ◯-elim m″ $ curry η) (η (η x , y))  ≡⟨ ◯-rec-η ⟩

          ◯-elim m″ (curry η) (η x) y                                  ≡⟨ cong (_$ y) ◯-elim-η ⟩∎

          η (x , y)                                                    ∎))
    where
    m′ = _
    m″ = λ _ → Modal-Π ext λ _ → Modal-◯

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
    ◯ (A × B)  ↔⟨ ◯×≃ ⟩
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

  -- ◯ (Erased A) implies Erased (◯ A).

  ◯-Erased→Erased-◯ :
    {@0 A : Type a} →
    @0 ◯ (Erased A) → Erased (◯ A)
  ◯-Erased→Erased-◯ x = E.[ ◯-map E.erased x ]

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

  ◯→η-[]◯-η : ◯ (x < y) → η x [ _<_ ]◯ η y
  ◯→η-[]◯-η = ◯-map (λ x<y → _ , _ , refl _ , refl _ , x<y)

  -- If A is modal and _<_ has type A → A → Type a, then
  -- η x [ _<_ ]◯ η y is equivalent to ◯ (x < y).

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
  -- See also Modality.Very-modal.◯Wη≃Σ◯Π◯Wη.

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
  -- See also Modality.Very-modal.W◯→◯Wη and
  -- Modality.Very-modal.◯Wη≃W◯.

  ◯Wη→W◯ :
    {P : ◯ A → Type a} →
    @0 Accessibility-modal-for (_<W_ {A = A} {P = P ∘ η}) →
    @0 Extensionality a a →
    ◯ (W A (P ∘ η)) → W (◯ A) P
  ◯Wη→W◯ {A = A} {P = P} acc ext =
    ◯ (W A (P ∘ η))                                      →⟨ ◯-map (λ x → x , A.Well-founded-W x) ⟩
    ◯ (∃ λ (x : W A (P ∘ η)) → Acc _<W_ x)               →⟨ ◯-map (Σ-map id (acc′ .proj₁)) ⟩
    ◯ (∃ λ (x : W A (P ∘ η)) → Acc _[ _<W_ ]◯_ (η x))    →⟨ ◯Ση→Σ◯◯ ⟩
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
      (◯Ση→Σ◯◯
         (◯-map (Σ-map id (acc′ .proj₁))
            (◯-map (λ x → x , A.Well-founded-W x) (η x))))  ≡⟨ cong (λ (x , a) → ◯Wη→W◯-Acc ext x (acc′ .proj₂ a)) $
                                                               trans (cong ◯Ση→Σ◯◯ $
                                                                      trans (cong (◯-map _) ◯-map-η)
                                                                      ◯-map-η)
                                                               ◯-rec-η ⟩
    (λ (x , a) → ◯Wη→W◯-Acc ext x (acc′ .proj₂ a))
      (η x , η (acc′ .proj₁ (A.Well-founded-W x)))           ≡⟨⟩

    ◯Wη→W◯-Acc ext (η x)
      (acc′ .proj₂ (η (acc′ .proj₁ (A.Well-founded-W x))))  ≡⟨ ◯Wη→W◯-Acc-η ext ext′ ax _ _ ⟩∎

    W-map η id x                                            ∎
    where
    acc′ = Accessibility-modal-for-erasure-stable E.[ acc ]

  -- If the modality is accessibility-modal for a certain relation and
  -- A is modal, then W A P is stable (assuming function
  -- extensionality).
  --
  -- See also Modality.Very-modal.Modal-W.

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
  -- More equivalences

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
  Separated-W {A = A} {P = P} ext′ s = λ x y →
    Stable→left-inverse→Modal
      (Stable-≡-W   x y)
      (Stable-≡-W-η x y)
    where
    ext = Eq.good-ext ext′

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
                                                                          trans (Eq.good-ext-cong ext′) $
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

  -- If ◯ (∀ x → Modal (P x)) holds, then ◯ ((x : A) → ◯ (P x)) is
  -- equivalent to ◯ ((x : A) → P x) (assuming function
  -- extensionality).
  --
  -- I did not take this lemma from "Modalities in Homotopy Type
  -- Theory" or the corresponding Coq code.

  ◯Π◯≃◯Π :
    {A : Type a} {P : A → Type a} →
    ◯ (∀ x → Modal (P x)) →
    ◯ ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ ((x : A) → P x)
  ◯Π◯≃◯Π {A = A} {P = P} m =
    flatten-↝
      (λ F → (x : A) → F (P x))
      (λ f g x → f (g x))
      (λ f → ◯-map (λ m x → Modal→Stable (m x) (f x)) m)
      (λ ext →
           (λ f →
              ◯-elim
                {P = λ m →
                       ◯-map (λ m x → Modal→Stable (m x) (η (f x))) m
                         ≡
                       η f}
                (λ _ → Separated-◯ _ _)
                (λ m →
                   ◯-map (λ m x → Modal→Stable (m x) (η (f x))) (η m)  ≡⟨ ◯-map-η ⟩
                   η (λ x → Modal→Stable (m x) (η (f x)))              ≡⟨ (cong η $ apply-ext ext λ _ →
                                                                           Modal→Stable-η) ⟩∎
                   η f                                                 ∎)
                _)
         , (λ f →
              ◯-map (λ g x → η (g x))
                (◯-map (λ m x → Modal→Stable (m x) (f x)) m)           ≡⟨ sym ◯-map-∘ ⟩

              ◯-map (λ m x → η (Modal→Stable (m x) (f x))) m           ≡⟨ ◯-elim
                                                                            {P = λ m →
                                                                                   ◯-map (λ m x → η (Modal→Stable (m x) (f x))) m ≡
                                                                                   η f}
                                                                            (λ _ → Separated-◯ _ _)
                                                                            (λ m →
                ◯-map (λ m x → η (Modal→Stable (m x) (f x))) (η m)             ≡⟨ ◯-map-η ⟩

                η (λ x → η (Modal→Stable (m x) (f x)))                         ≡⟨ (cong η $ apply-ext ext λ x →
                                                                                   _≃_.right-inverse-of (Modal→≃◯ (m x)) _) ⟩∎
                η f                                                            ∎)
                                                                            _ ⟩∎
              η f                                                      ∎))

  -- Two "computation rules" for ◯Π◯≃◯Π.

  ◯Π◯≃◯Π-η :
    ◯Π◯≃◯Π (η m) _ (η f) ≡ η (λ x → Modal→Stable (m x) (f x))
  ◯Π◯≃◯Π-η {m = m} {f = f} =
    ◯Π◯≃◯Π (η m) _ (η f)                                      ≡⟨⟩

    ◯-rec
      Modal-◯
      (λ f → ◯-map (λ m x → Modal→Stable (m x) (f x)) (η m))
      (η f)                                                   ≡⟨ ◯-rec-η ⟩

    ◯-map (λ m x → Modal→Stable (m x) (f x)) (η m)            ≡⟨ ◯-map-η ⟩∎

    η (λ x → Modal→Stable (m x) (f x))                        ∎

  ◯Π◯≃◯Π⁻¹-η : _⇔_.from (◯Π◯≃◯Π m _) (η f) ≡ η (η ∘ f)
  ◯Π◯≃◯Π⁻¹-η {m = m} {f = f} =
    _⇔_.from (◯Π◯≃◯Π m _) (η f)    ≡⟨⟩
    ◯-map (λ g x → η (g x)) (η f)  ≡⟨ ◯-map-η ⟩∎
    η (η ∘ f)                      ∎

  ----------------------------------------------------------------------
  -- Some results related to connectedness

  -- ◯ -Connected_ preserves equivalences (assuming function
  -- extensionality).

  Connected-cong :
    Extensionality? k a a →
    A ≃ B → ◯ -Connected A ↝[ k ] ◯ -Connected B
  Connected-cong {A = A} {B = B} ext A≃B =
    Contractible (◯ A) ↝⟨ H-level-cong ext 0 $ ◯-cong-≃ A≃B ⟩□
    Contractible (◯ B) □

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
      (λ ext → Eq.propositional ext _)
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

  ----------------------------------------------------------------------
  -- Left exact modalities

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
    Eq.propositional ext′ _
    where
    ext′ = lower-extensionality _ lzero ext

  -- If the modality is left exact, then there is an equivalence
  -- between ◯ (x ≡ y) and η x ≡ η y.

  ◯≡≃η≡η :
    Left-exact-η-cong →
    ◯ (x ≡ y) ≃ (η x ≡ η y)
  ◯≡≃η≡η lex = Eq.⟨ η-cong , lex ⟩

  -- If the modality is left exact, then η-cong has an inverse.

  η-cong⁻¹ :
    Left-exact-η-cong →
    η x ≡ η y → ◯ (x ≡ y)
  η-cong⁻¹ lex = _≃_.from $ ◯≡≃η≡η lex

  η-cong-η-cong⁻¹ :
    (lex : Left-exact-η-cong) →
    η-cong (η-cong⁻¹ lex p) ≡ p
  η-cong-η-cong⁻¹ lex = _≃_.right-inverse-of (◯≡≃η≡η lex) _

  η-cong⁻¹-η-cong :
    (lex : Left-exact-η-cong) →
    η-cong⁻¹ lex (η-cong p) ≡ p
  η-cong⁻¹-η-cong lex = _≃_.left-inverse-of (◯≡≃η≡η lex) _

  -- A "computation rule" for η-cong⁻¹.

  η-cong⁻¹-η :
    (lex : Left-exact-η-cong) →
    η-cong⁻¹ lex (refl (η x)) ≡ η (refl x)
  η-cong⁻¹-η {x = x} lex = _≃_.to-from (◯≡≃η≡η lex)
    (η-cong (η (refl x))  ≡⟨ η-cong-η ⟩
     cong η (refl x)      ≡⟨ cong-refl _ ⟩∎
     refl (η x)           ∎)

  -- Left-exact-η-cong implies Left-exact ◯.

  Left-exact-η-cong→Left-exact : Left-exact-η-cong → Left-exact ◯
  Left-exact-η-cong→Left-exact lex {A = A} {x = x} {y = y} =
    Contractible (◯ A)        →⟨ H-level.⇒≡ 0 ⟩
    Contractible (η x ≡ η y)  →⟨ H-level-cong _ 0 $ inverse $ ◯≡≃η≡η lex ⟩□
    Contractible (◯ (x ≡ y))  □

  -- If the modality is left exact, then A is separated if and only if
  -- η is an embedding for A.
  --
  -- I did not take this lemma from "Modalities in Homotopy Type
  -- Theory" or the corresponding Coq code.

  Separated≃Is-embedding-η :
    Left-exact-η-cong →
    Separated A ↝[ a ∣ a ] Is-embedding (η ⦂ (A → ◯ A))
  Separated≃Is-embedding-η {A = A} lex ext =
    (∀ x y → Modal (x ≡ y))                            ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Modal≃Is-equivalence-η ext) ⟩
    (∀ x y → Is-equivalence (η {A = x ≡ y}))           ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                           Is-equivalence≃Is-equivalence-∘ˡ lex ext) ⟩
    (∀ x y → Is-equivalence (η-cong ∘ η {A = x ≡ y}))  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Is-equivalence-cong ext λ _ → η-cong-η) ⟩□
    (∀ x y → Is-equivalence (cong {x = x} {y = y} η))  □

  -- If ◯ is left exact, then non-dependent functions between
  -- ◯-connected types are ◯-connected.

  Left-exact→Connected→Connected→Connected-→ :
    {f : A → B} →
    Left-exact ◯ → ◯ -Connected A → ◯ -Connected B → ◯ -Connected-→ f
  Left-exact→Connected→Connected→Connected-→ lex cA cB _ =
    Connected-Σ cA λ _ → lex cB

  -- If ◯ is left exact, then the remaining part of the
  -- two-out-of-three property holds for ◯-connectedness. (For the two
  -- other parts, see Connected-→→Connected-→≃Connected-→-∘.)

  Left-exact→Connected-→→Connected-→-∘≃Connected-→ :
    Left-exact ◯ →
    ◯ -Connected-→ g → ◯ -Connected-→ (g ∘ f) → ◯ -Connected-→ f
  Left-exact→Connected-→→Connected-→-∘≃Connected-→
    {g = g} {f = f} lex c-g c-g∘f =                    $⟨ (λ _ →
                                                             Left-exact→Connected→Connected→Connected-→
                                                               lex (c-g∘f _) (c-g _) _) ⟩
    (∀ y → ◯ -Connected (∘⁻¹→⁻¹ ⁻¹ (y , refl (g y))))  →⟨ (∀-cong _ λ y → Connected-cong _ Σ-map--id-⁻¹≃⁻¹) ⟩□
    (∀ y → ◯ -Connected (f ⁻¹ y))                      □
    where
    ∘⁻¹→⁻¹ : g ∘ f ⁻¹ g y → g ⁻¹ g y
    ∘⁻¹→⁻¹ = Σ-map f id

  -- If ◯ is left exact, then the function f is ◯-connected if and
  -- only if ◯-map f is an equivalence.

  Left-exact→Connected-→≃Is-equivalence-◯-map :
    Left-exact ◯ →
    ◯ -Connected-→ f ↝[ a ∣ a ] Is-equivalence (◯-map f)
  Left-exact→Connected-→≃Is-equivalence-◯-map {f = f} lex =
    generalise-ext?-prop
      (record { to = Connected→Is-equivalence-◯-map; from = from })
      (flip Connected-→-propositional ◯)
      (flip Eq.propositional _)
    where
    from : Is-equivalence (◯-map f) → ◯ -Connected-→ f
    from =
      Is-equivalence (◯-map f)  →⟨ _⇔_.from $ Connected-→-η-∘-≃Is-equivalence-◯-map _ ⟩
      ◯ -Connected-→ (η ∘ f)    →⟨ Left-exact→Connected-→→Connected-→-∘≃Connected-→ lex Connected-→-η ⟩□
      ◯ -Connected-→ f          □

  -- If ◯ is left exact and A is a proposition, then ◯ A is a
  -- proposition.

  Left-exact→Is-proposition→Is-proposition-◯ :
    Left-exact-η-cong → Is-proposition A → Is-proposition (◯ A)
  Left-exact→Is-proposition→Is-proposition-◯ {A = A} lex prop x y =
    x                                         ≡⟨ cong proj₁ $ sym $ _≃_.right-inverse-of ◯×≃ _ ⟩
    _≃_.to ◯×≃ (_≃_.from ◯×≃ (x , y)) .proj₁  ≡⟨ ◯-elim
                                                   {P = λ p → _≃_.to ◯×≃ p .proj₁ ≡ _≃_.to ◯×≃ p .proj₂}
                                                   (λ _ → Separated-◯ _ _)
                                                   (λ (x , y) →
      _≃_.to ◯×≃ (η (x , y)) .proj₁                   ≡⟨ cong proj₁ ◯×≃-η ⟩
      η x                                             ≡⟨ cong η $ prop _ _ ⟩
      η y                                             ≡⟨ cong proj₂ $ sym ◯×≃-η ⟩∎
      _≃_.to ◯×≃ (η (x , y)) .proj₂                   ∎)
                                                   (_≃_.from ◯×≃ (x , y)) ⟩
    _≃_.to ◯×≃ (_≃_.from ◯×≃ (x , y)) .proj₂  ≡⟨ cong proj₂ $ _≃_.right-inverse-of ◯×≃ _ ⟩∎
    y                                         ∎

  -- If ◯ is left exact and A has a given h-level, then ◯ A has the
  -- same h-level (assuming function extensionality).
  --
  -- TODO: Can this be proved without the use of function
  -- extensionality? The Coq code accompanying "Modalities in Homotopy
  -- Type Theory" contains the following comment in connection with
  -- the corresponding lemma:
  --
  --   "With a little more work, this can probably be proven without
  --   [Funext]."

  Left-exact→H-level′→H-level′-◯ :
    Extensionality a a →
    Left-exact-η-cong → ∀ n → H-level′ n A → H-level′ n (◯ A)
  Left-exact→H-level′→H-level′-◯ {A = A} _ _ zero =
    Contractible A      →⟨ Contractible→Connected ⟩□
    Contractible (◯ A)  □
  Left-exact→H-level′→H-level′-◯ {A = A} ext lex (suc n) =
    ((x y : A) → H-level′ n (x ≡ y))      →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → Left-exact→H-level′→H-level′-◯ ext lex n) ⟩
    ((x y : A) → H-level′ n (◯ (x ≡ y)))  →⟨ (λ h →
                                                ◯-elim (λ _ → Modal-Π ext λ _ →
                                                              Modal-H-level′ ext n $
                                                              Modal→Modalⁿ n $
                                                              Separated-◯ _ _) λ x →
                                                ◯-elim (λ _ → Modal-H-level′ ext n $
                                                              Modal→Modalⁿ n $
                                                              Separated-◯ _ _) λ y →
                                                H-level′-cong _ n (◯≡≃η≡η lex) (h x y)) ⟩□
    ((x y : ◯ A) → H-level′ n (x ≡ y))    □

  -- If ◯ is left exact and A has a given h-level, then ◯ A has the
  -- same h-level (assuming function extensionality).
  --
  -- See also Modality.Very-modal.H-level→H-level-◯.

  Left-exact-η-cong→H-level→H-level-◯ :
    Extensionality a a →
    Left-exact-η-cong → ∀ n → H-level n A → H-level n (◯ A)
  Left-exact-η-cong→H-level→H-level-◯ {A = A} ext lex n =
    H-level n A       ↝⟨ H-level↔H-level′ _ ⟩
    H-level′ n A      ↝⟨ Left-exact→H-level′→H-level′-◯ ext lex n ⟩
    H-level′ n (◯ A)  ↝⟨ _⇔_.from (H-level↔H-level′ _) ⟩□
    H-level n (◯ A)   □

  -- I did not take the remaining result in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code.

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
       ◯ (Modal A) × ◯ (η x ≡ η y)  →⟨ _≃_.from ◯×≃ ⟩
       ◯ (Modal A × η x ≡ η y)      →⟨ ◯-map lemma ⟩□
       ◯ (x ≡ y)                    □)
      (λ p →
         ◯-elim
           {P = λ m →
                  ◯-rec m′ (cong η)
                    (◯-map lemma (_≃_.from ◯×≃ (m , η p))) ≡
                  p}
           (λ _ → Modal→Separated m′ _ _)
           (λ m →
              ◯-rec m′ (cong η)
                (◯-map lemma (_≃_.from ◯×≃ (η m , η p)))   ≡⟨ cong (◯-rec m′ (cong η) ∘ ◯-map _) ◯×≃⁻¹-η ⟩

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
                       (_≃_.from ◯×≃
                          (m , η (◯-rec m′ (cong η) (η p)))) ≡
                     η p}
              (λ _ → Separated-◯ _ _)
              (λ m →
                 ◯-map lemma
                   (_≃_.from ◯×≃ (η m , η (◯-rec m′ (cong η) (η p))))  ≡⟨ cong (◯-map lemma) ◯×≃⁻¹-η ⟩

                 ◯-map lemma (η (m , ◯-rec m′ (cong η) (η p)))         ≡⟨ ◯-map-η ⟩

                 η (lemma (m , ◯-rec m′ (cong η) (η p)))               ≡⟨ cong (η ∘ lemma ∘ (m ,_)) ◯-rec-η ⟩

                 η (lemma (m , cong η p))                              ≡⟨ cong η $ _≃_.left-inverse-of (≡≃η≡η m) _ ⟩∎

                 η p                                                   ∎)
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
  -- Applicative functor application

  -- I did not take the results in this section from "Modalities in
  -- Homotopy Type Theory" or the corresponding Coq code (but perhaps
  -- something resembling at least some of these results can be found
  -- there).

  -- "Applicative functor application".

  ◯-map-◯ : ◯ (A → B) → ◯ A → ◯ B
  ◯-map-◯ {A = A} {B = B} = curry
    (◯ (A → B) × ◯ A  ↔⟨ inverse ◯×≃ ⟩
     ◯ ((A → B) × A)  →⟨ ◯-map (uncurry _$_) ⟩□
     ◯ B              □)

  -- Three "computation rules" for ◯-map-◯.

  ◯-map-◯-η : ◯-map-◯ (η f) (η x) ≡ η (f x)
  ◯-map-◯-η {f = f} {x = x} =
    ◯-map (uncurry _$_) (_≃_.from ◯×≃ (η f , η x))  ≡⟨ cong (◯-map _) ◯×≃⁻¹-η ⟩
    ◯-map (uncurry _$_) (η (f , x))                 ≡⟨ ◯-map-η ⟩∎
    η (f x)                                         ∎

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
    ◯ ((A → B) × (B → A))      ↔⟨ ◯×≃ ⟩
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
    ◯ (∃ λ (f : A → B) → P (◯-map-◯ (η f)))    →⟨ ◯Ση→Σ◯◯ ⟩
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
    (∀ y → ◯ (∃ λ x → ◯-map f (η x) ≡ y))  →⟨ (∀-cong _ λ _ → ◯Ση→Σ◯◯) ⟩
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

    ◯ (∃ λ g → ◯ ((∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x)))          ↔⟨ (◯-cong-≃ $ ∃-cong λ _ → ◯×≃) ⟩

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
               (∀ x → ◯-map-◯ (η g) (η (f x)) ≡ η x))                  →⟨ ◯Ση→Σ◯◯ ⟩

    (∃ λ g → ◯ ((∀ x → ◯-map f (◯-map-◯ g (η x)) ≡ η x) ×
                (∀ x → ◯-map-◯ g (η (f x)) ≡ η x)))                    ↔⟨ (∃-cong λ _ → ◯×≃) ⟩

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

  -- If the modality is left exact, then ◯ (Injective f) implies
  -- Injective (◯-map f).

  ◯-Injective→Injective :
    Left-exact-η-cong →
    ◯ (Injective f) → Injective (◯-map f)
  ◯-Injective→Injective {f = f} lex =
    ◯ (∀ {x y} → f x ≡ f y → x ≡ y)                      →⟨ ◯-map (λ g _ _ → g) ⟩
    ◯ (∀ x y → f x ≡ f y → x ≡ y)                        →⟨ ◯Π→Π◯ ⟩
    (∀ x → ◯ (∀ y → f x ≡ f y → x ≡ y))                  →⟨ (∀-cong _ λ _ → ◯Π→Π◯) ⟩
    (∀ x y → ◯ (f x ≡ f y → x ≡ y))                      →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → ◯-map-◯) ⟩
    (∀ x y → ◯ (f x ≡ f y) → ◯ (x ≡ y))                  →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                             →-cong-→ (_≃_.from $ ◯≡≃η≡η lex) η-cong) ⟩
    (∀ x y → η (f x) ≡ η (f y) → η x ≡ η y)              →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                             →-cong-→ (≡⇒↝ _ $ cong₂ _≡_ ◯-map-η ◯-map-η) id) ⟩
    (∀ x y → ◯-map f (η x) ≡ ◯-map f (η y) → η x ≡ η y)  →⟨ (∀-cong _ λ _ → _⇔_.from $ Π◯⇔Πη s′) ⟩
    (∀ x y → ◯-map f (η x) ≡ ◯-map f y → η x ≡ y)        →⟨ (_⇔_.from $ Π◯⇔Πη λ _ → Stable-Π s′) ⟩
    (∀ x y → ◯-map f x ≡ ◯-map f y → x ≡ y)              →⟨ (λ g → g _ _) ⟩□
    (∀ {x y} → ◯-map f x ≡ ◯-map f y → x ≡ y)            □
    where
    s′ : ∀ {x} y → Stable (◯-map f x ≡ ◯-map f y → x ≡ y)
    s′ _ = Stable-Π λ _ → Modal→Stable $ Separated-◯ _ _

  -- If the modality is left exact, then ◯ (A ↣ B) implies ◯ A ↣ ◯ B.

  ◯-cong-↣-◯ :
    Left-exact-η-cong →
    ◯ (A ↣ B) → ◯ A ↣ ◯ B
  ◯-cong-↣-◯ lex =
    ◯↝→◯↝◯
      ↣↔∃-Injective
      (◯-Injective→Injective lex)
      (Injective-cong _)
      (Stable-implicit-Π λ _ → Stable-implicit-Π λ _ → Stable-Π λ _ →
       Modal→Stable $ Separated-◯ _ _)

  -- A lemma used in the implementations of
  -- ◯-Is-embedding→Is-embedding and
  -- Modality.Very-modal.◯-Is-embedding≃Is-embedding.

  ◯-map-cong≡ :
    ∀ (lex : Left-exact-η-cong) (p : ◯ (x ≡ y)) →
    ◯-map (cong f) p ≡
    (η-cong⁻¹ lex ∘
     _≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
     cong (◯-map f) ∘
     η-cong) p
  ◯-map-cong≡ {f = f} lex =
    ◯-elim (λ _ → Separated-◯ _ _) $
    elim¹
      (λ p →
         ◯-map (cong f) (η p) ≡
         η-cong⁻¹ lex
           (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η))
              (cong (◯-map f) (η-cong (η p)))))
      (◯-map (cong f) (η (refl _))                                                ≡⟨ trans ◯-map-η $
                                                                                     cong η $ cong-refl _ ⟩

       η (refl _)                                                                 ≡⟨ sym $ η-cong⁻¹-η lex ⟩

       η-cong⁻¹ lex (refl _)                                                      ≡⟨ cong (η-cong⁻¹ lex) $
                                                                                     trans (sym $ trans-symˡ _) $
                                                                                     cong (flip trans _) $
                                                                                     sym $ trans-reflʳ _ ⟩

       η-cong⁻¹ lex (trans (trans (sym ◯-map-η) (refl _)) ◯-map-η)                ≡⟨ cong (η-cong⁻¹ lex) $
                                                                                     trans trans-subst $
                                                                                     cong (subst (_ ≡_) _) $
                                                                                     sym subst-trans-sym ⟩
       η-cong⁻¹ lex
         (subst (η _ ≡_) ◯-map-η (subst (_≡ ◯-map _ _) ◯-map-η (refl _)))         ≡⟨ cong (η-cong⁻¹ lex) $ sym $
                                                                                     ≡⇒↝-cong₂≡subst-subst equivalence {P = _≡_} ⟩
       η-cong⁻¹ lex
         (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) (refl _))                    ≡⟨ cong (η-cong⁻¹ lex) $ cong (_≃_.to (≡⇒↝ _ _)) $
                                                                                     trans (sym $ cong-refl _) $
                                                                                     cong (cong (◯-map f)) $
                                                                                     trans (sym $ cong-refl _) $
                                                                                     sym η-cong-η ⟩∎
       η-cong⁻¹ lex
         (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η))
            (cong (◯-map f) (η-cong (η (refl _)))))                               ∎)

  -- If the modality is left exact, then ◯ (Is-embedding f) implies
  -- Is-embedding (◯-map f).

  ◯-Is-embedding→Is-embedding :
    Left-exact-η-cong →
    ◯ (Is-embedding f) → Is-embedding (◯-map f)
  ◯-Is-embedding→Is-embedding {f = f} lex =
    ◯ (∀ x y → Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y)))             →⟨ ◯Π→Π◯ ⟩

    (∀ x → ◯ (∀ y → Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y))))       →⟨ (∀-cong _ λ _ → ◯Π→Π◯) ⟩

    (∀ x y → ◯ (Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y))))           →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                                              ◯-Is-equivalence→Is-equivalence) ⟩

    (∀ x y → Is-equivalence (◯-map (cong f ⦂ (x ≡ y → f x ≡ f y))))       →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → Is-equivalence-cong _ $
                                                                              ◯-map-cong≡ lex) ⟩
    (∀ x y →
       Is-equivalence
         (η-cong⁻¹ lex ∘
          _≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
          cong (◯-map f) ∘ η-cong ⦂ (◯ (x ≡ y) → ◯ (f x ≡ f y))))         →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → _⇔_.from $
                                                                              Is-equivalence≃Is-equivalence-∘ˡ
                                                                                (_≃_.is-equivalence $ inverse $ ◯≡≃η≡η lex) _) ⟩
    (∀ x y →
       Is-equivalence
         (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
          cong (◯-map f) ∘ η-cong ⦂ (◯ (x ≡ y) → η (f x) ≡ η (f y))))     →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → _⇔_.from $
                                                                              Is-equivalence≃Is-equivalence-∘ʳ lex _) ⟩
    (∀ x y →
       Is-equivalence
         (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
          cong (◯-map f) ⦂ (η x ≡ η y → η (f x) ≡ η (f y))))              →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → _⇔_.from $
                                                                              Is-equivalence≃Is-equivalence-∘ˡ
                                                                                (_≃_.is-equivalence $ ≡⇒↝ _ _) _) ⟩
    (∀ x y →
       Is-equivalence
         (cong (◯-map f) ⦂ (η x ≡ η y → ◯-map f (η x) ≡ ◯-map f (η y))))  →⟨ (_⇔_.from $
                                                                              Π◯⇔Πη λ _ → Stable-Π λ _ →
                                                                              Modal→Stable-Is-equivalence
                                                                                (Separated-◯ _ _) (Modal→Separated (Separated-◯ _ _))) ⟩
    (∀ x y →
       Is-equivalence
         (cong (◯-map f) ⦂ (x ≡ η y → ◯-map f x ≡ ◯-map f (η y))))        →⟨ (∀-cong _ λ _ → _⇔_.from $
                                                                              Π◯⇔Πη λ _ →
                                                                              Modal→Stable-Is-equivalence
                                                                                (Separated-◯ _ _) (Modal→Separated (Separated-◯ _ _))) ⟩□
    (∀ x y →
       Is-equivalence
         (cong (◯-map f) ⦂ (x ≡ y → ◯-map f x ≡ ◯-map f y)))              □

  -- If the modality is left exact, then ◯ (Embedding A B) implies
  -- Embedding (◯ A) (◯ B).

  ◯-cong-Embedding-◯ :
    Left-exact-η-cong →
    ◯ (Embedding A B) → Embedding (◯ A) (◯ B)
  ◯-cong-Embedding-◯ lex =
    ◯↝→◯↝◯
      Emb.Embedding-as-Σ
      (◯-Is-embedding→Is-embedding lex)
      (Is-embedding-cong _)
      (Stable-Π λ _ → Stable-Π λ _ →
       Modal→Stable-Is-equivalence
         (Separated-◯ _ _) (Modal→Separated (Separated-◯ _ _)))
