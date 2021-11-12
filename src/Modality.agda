------------------------------------------------------------------------
-- Idempotent monadic modalities
------------------------------------------------------------------------

-- Unless otherwise noted this code is based on "Modalities in
-- Homotopy Type Theory" by Rijke, Shulman and Spitters, and/or (some
-- version of) the corresponding Coq code. (Details may differ, and
-- perhaps there are some "obvious" results that do not have direct
-- counterparts in the work of Rijke, Shulman and Spitters, even
-- though there is no note about this.)

{-# OPTIONS --without-K --safe #-}

open import Equality

module Modality
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Erased.Basics as E using (Erased)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_; Has-quasi-inverse)
open import Embedding eq as Emb using (Embedding; Is-embedding)
open import Equality.Decidable-UIP eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased.Basics eq as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages.Basics eq
  using (Contractibleᴱ; _⁻¹ᴱ_)
open import Equivalence.Path-split eq as PS
  using (Is-∞-extendable-along-[_]; _-Null_)
open import For-iterated-equality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (_↣_; Injective)
open import Preimage eq as Preimage using (_⁻¹_)
open import Surjection eq using (_↠_; Split-surjective)

private
  variable
    a c d ℓ         : Level
    A B C           : Type a
    f g h k m p x y : A
    P Q             : A → Type p

------------------------------------------------------------------------
-- Some basic definitions

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
-- of) the Coq code of Rijke et al. Note that Is-modal-propositional
-- is only given access to function extensionality for a given
-- universe level.

record Σ-closed-reflective-subuniverse a : Type (lsuc a) where
  field
    ◯        : Type a → Type a
    η        : A → ◯ A
    Is-modal : Type a → Type a

    Is-modal-propositional :
      Extensionality a a →
      Is-proposition (Is-modal A)

    Is-modal-◯ : Is-modal (◯ A)

    Is-modal-respects-≃ : A ≃ B → Is-modal A → Is-modal B

    extendable-along-η :
      Is-modal B → Is-∞-extendable-along-[ η ] (λ (_ : ◯ A) → B)

    Σ-closed : Is-modal A → (∀ x → Is-modal (P x)) → Is-modal (Σ A P)

-- The following is a definition of "uniquely eliminating modality"
-- based on that in "Modalities in Homotopy Type Theory".

record Uniquely-eliminating-modality a : Type (lsuc a) where
  field
    ◯                    : Type a → Type a
    η                    : A → ◯ A
    uniquely-eliminating :
      Is-equivalence (λ (f : (x : ◯ A) → ◯ (P x)) → f ∘ η)

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
      ◯        : Type a → Type a
      η        : A → ◯ A
      Is-modal : Type a → Type a

      Is-modal-propositional :
        Extensionality a a →
        Is-proposition (Is-modal A)

      Is-modal-◯ : Is-modal (◯ A)

      Is-modal-respects-≃ : A ≃ B → Is-modal A → Is-modal B

      extendable-along-η :
        {P : ◯ A → Type a} →
        (∀ x → Is-modal (P x)) →
        Is-∞-extendable-along-[ η ] P

open Dummy public
  using (module Modality-record)
  renaming (Modality-record to Modality)

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
    Is-modal A ⇔
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
Empty-modal M = Is-modal ⊥
  where
  open Modality-record M

-- Empty-modal M is propositional (assuming function extensionality).

Empty-modal-propositional :
  {M : Modality a} →
  Extensionality a a →
  Is-proposition (Empty-modal M)
Empty-modal-propositional {M = M} ext =
  Is-modal-propositional ext
  where
  open Modality-record M

-- A modality is called "very modal" if ◯ (Is-modal A) always holds.
--
-- I did not take this definition from "Modalities in Homotopy Type
-- Theory" or the corresponding Coq code.
--
-- See also Very-modal-propositional below.

Very-modal : Modality a → Type (lsuc a)
Very-modal {a = a} M = {A : Type a} → ◯ (Is-modal A)
  where
  open Modality-record M

------------------------------------------------------------------------
-- Some results that hold for every modality

module Modality (M : Modality a) where

  open Dummy.Modality-record M public

  ----------------------------------------------------------------------
  -- Eliminators

  -- An eliminator for ◯.

  ◯-elim :
    {P : ◯ A → Type a} →
    (∀ x → Is-modal (P x)) →
    ((x : A) → P (η x)) →
    ((x : ◯ A) → P x)
  ◯-elim m f = extendable-along-η m 1 .proj₁ f .proj₁

  -- A "computation rule" for ◯-elim.

  ◯-elim-η : ◯-elim m f (η x) ≡ f x
  ◯-elim-η {m = m} {f = f} {x = x} =
    extendable-along-η m 1 .proj₁ f .proj₂ x

  -- A non-dependent eliminator for ◯.

  ◯-rec : Is-modal B → (A → B) → (◯ A → B)
  ◯-rec m = ◯-elim (λ _ → m)

  -- A "computation rule" for ◯-rec.

  ◯-rec-η : ◯-rec m f (η x) ≡ f x
  ◯-rec-η = ◯-elim-η

  -- If f and g have type (x : ◯ A) → P x, where P x is modal for all
  -- x, and f ∘ η and g ∘ η are pointwise equal, then f and g are
  -- pointwise equal.

  ∘η≡∘η→≡ :
    {f g : (x : ◯ A) → P x} →
    (∀ x → Is-modal (P x)) →
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

  Is-equivalence-η→Is-modal :
    Is-equivalence (η {A = A}) → Is-modal A
  Is-equivalence-η→Is-modal {A = A} =
    Is-equivalence (η {A = A})     →⟨ Eq.⟨ _ ,_⟩ ⟩
    A ≃ ◯ A                        →⟨ Is-modal-respects-≃ ∘ inverse ⟩
    (Is-modal (◯ A) → Is-modal A)  →⟨ _$ Is-modal-◯ ⟩□
    Is-modal A                     □

  -- A type is stable if ◯ A implies A.

  Stable : Type a → Type a
  Stable A = ◯ A → A

  -- If A is stable, and the stability proof is a left inverse of η,
  -- then A is modal.

  Stable→left-inverse→Is-modal :
    (s : Stable A) → (∀ x → s (η x) ≡ x) → Is-modal A
  Stable→left-inverse→Is-modal s eq =
    Is-equivalence-η→Is-modal $
    _≃_.is-equivalence $
    Eq.↔→≃
      _
      s
      (∘η≡∘η→≡ (λ _ → Is-modal-◯) (cong η ∘ eq))
      eq

  -- Stable propositions are modal.

  Stable→Is-proposition→Is-modal :
    Stable A → Is-proposition A → Is-modal A
  Stable→Is-proposition→Is-modal s prop =
    Stable→left-inverse→Is-modal s (λ _ → prop _ _)

  -- A type is separated if equality is modal for this type.
  --
  -- This definition is taken from "Localization in homotopy type
  -- theory" by Christensen, Opie, Rijke and Scoccola.

  Separated : Type a → Type a
  Separated = For-iterated-equality 1 Is-modal

  -- If a type is modal, then it is separated.

  Is-modal→Separated : Is-modal A → Separated A
  Is-modal→Separated m x y =
    Stable→left-inverse→Is-modal
      (◯ (x ≡ y)  →⟨ ∘η≡∘η→≡
                       {f = λ (_ : ◯ (x ≡ y)) → x}
                       {g = λ (_ : ◯ (x ≡ y)) → y}
                       (λ _ → m)
                       id ⟩□
       x ≡ y      □)
      (λ _ → ∘η≡∘η→≡-η)

  -- The type ◯ A is separated.

  Separated-◯ : Separated (◯ A)
  Separated-◯ = Is-modal→Separated Is-modal-◯

  -- If ◯ (x ≡ y) holds, then η x is equal to η y.

  η-cong : ◯ (x ≡ y) → η x ≡ η y
  η-cong = ◯-rec (Separated-◯ _ _) (cong η)

  -- A "computation rule" for η-cong.

  η-cong-η : η-cong (η p) ≡ cong η p
  η-cong-η = ◯-rec-η

  -- A is modal if and only if η is an equivalence for A.

  Is-modal≃Is-equivalence-η :
    Is-modal A ↝[ a ∣ a ] Is-equivalence (η {A = A})
  Is-modal≃Is-equivalence-η =
    generalise-ext?-prop
      (record
         { to = λ m →
             _≃_.is-equivalence $
             Eq.↔→≃
               _
               (◯-rec m id)
               (◯-elim
                  (λ _ → Separated-◯ _ _)
                  (λ _ → cong η ◯-elim-η))
               (λ _ → ◯-elim-η)
         ; from = Is-equivalence-η→Is-modal
         })
      Is-modal-propositional
      (λ ext → Eq.propositional ext _)

  -- If A is modal, then A is equivalent to ◯ A.

  Is-modal→≃◯ : Is-modal A → A ≃ ◯ A
  Is-modal→≃◯ m = Eq.⟨ _ , Is-modal≃Is-equivalence-η _ m ⟩

  -- If A is modal, then η is an embedding for A.

  Is-modal→Is-embedding-η :
    Is-modal A → Is-embedding (η ⦂ (A → ◯ A))
  Is-modal→Is-embedding-η m =
    Emb.Is-equivalence→Is-embedding
      (Is-modal≃Is-equivalence-η _ m)

  -- For modal types the function η has an inverse.

  η⁻¹ : Is-modal A → ◯ A → A
  η⁻¹ m = _≃_.from (Is-modal→≃◯ m)

  η-η⁻¹ : η (η⁻¹ m x) ≡ x
  η-η⁻¹ = _≃_.right-inverse-of (Is-modal→≃◯ _) _

  η⁻¹-η : η⁻¹ m (η x) ≡ x
  η⁻¹-η = _≃_.left-inverse-of (Is-modal→≃◯ _) _

  ----------------------------------------------------------------------
  -- Some closure properties related to Is-modal

  -- The unit type (lifted) is modal.

  Is-modal-⊤ : Is-modal (↑ a ⊤)
  Is-modal-⊤ = Stable→left-inverse→Is-modal _ refl

  -- Is-modal is closed under "Π A" (assuming function
  -- extensionality).

  Is-modal-Π :
    {A : Type a} {P : A → Type a} →
    Extensionality a a →
    (∀ x → Is-modal (P x)) → Is-modal ((x : A) → P x)
  Is-modal-Π ext m =
    Stable→left-inverse→Is-modal
      (λ f x → ◯-rec (m x) (_$ x) f)
      (λ f → apply-ext ext λ x →
         ◯-rec (m x) (_$ x) (η f)  ≡⟨ ◯-rec-η ⟩∎
         f x                       ∎)

  -- Is-modal is closed under Σ.

  Is-modal-Σ :
    Is-modal A → (∀ x → Is-modal (P x)) → Is-modal (Σ A P)
  Is-modal-Σ {A = A} {P = P} mA mP =
    Stable→left-inverse→Is-modal
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

  -- A generalisation of Is-modal-Σ.

  Is-modal-Σ≃Π-Is-modal :
    Is-modal A →
    Is-modal (Σ A P) ↝[ a ∣ a ] (∀ x → Is-modal (P x))
  Is-modal-Σ≃Π-Is-modal {A = A} {P = P} m =
    generalise-ext?-prop
      (record
         { from = Is-modal-Σ m
         ; to   = flip λ x →
             Is-modal (Σ A P)                          ↝⟨ flip Is-modal-Σ (λ _ → Is-modal→Separated m _ _) ⟩
             Is-modal (∃ λ ((y , _) : Σ A P) → y ≡ x)  ↝⟨ Is-modal-respects-≃ $ from-bijection $ inverse Σ-assoc ⟩
             Is-modal (∃ λ (y : A) → P y × y ≡ x)      ↝⟨ Is-modal-respects-≃ $ from-bijection $ inverse $ ∃-intro _ _ ⟩□
             Is-modal (P x)                            □
         })
      Is-modal-propositional
      (λ ext →
         Π-closure ext 1 λ _ →
         Is-modal-propositional ext)

  -- I did not take the remaining results in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code (but that does not mean that one cannot find something
  -- similar in those places).

  -- If A is "modal n levels up", then H-level′ n A is modal (assuming
  -- function extensionality).

  Is-modal-H-level′ :
    Extensionality a a →
    ∀ n →
    For-iterated-equality n Is-modal A →
    Is-modal (H-level′ n A)
  Is-modal-H-level′ {A = A} ext n =
    For-iterated-equality n Is-modal A                   ↝⟨ For-iterated-equality-cong₁ _ n lemma ⟩
    For-iterated-equality n (Is-modal ∘ Contractible) A  ↝⟨ For-iterated-equality-commutes-← _ Is-modal n (Is-modal-Π ext) ⟩□
    Is-modal (H-level′ n A)                              □
    where
    lemma : ∀ {A} → Is-modal A → Is-modal (Contractible A)
    lemma m =
      Is-modal-Σ m λ _ →
      Is-modal-Π ext λ _ →
      Is-modal→Separated m _ _

  -- If A is "modal n levels up", then H-level n A is modal (assuming
  -- function extensionality).

  Is-modal-H-level :
    Extensionality a a →
    ∀ n →
    For-iterated-equality n Is-modal A →
    Is-modal (H-level n A)
  Is-modal-H-level {A = A} ext n =
    For-iterated-equality n Is-modal A  ↝⟨ Is-modal-H-level′ ext n ⟩
    Is-modal (H-level′ n A)             ↝⟨ Is-modal-respects-≃ (inverse $ H-level↔H-level′ ext) ⟩□
    Is-modal (H-level n A)              □

  -- Some generalisations of Is-modal→Separated.

  Is-modalⁿ→Is-modal¹⁺ⁿ :
    ∀ n →
    For-iterated-equality n       Is-modal A →
    For-iterated-equality (1 + n) Is-modal A
  Is-modalⁿ→Is-modal¹⁺ⁿ {A = A} n =
    For-iterated-equality n Is-modal A        →⟨ For-iterated-equality-cong₁ _ n Is-modal→Separated ⟩
    For-iterated-equality n Separated A       →⟨ For-iterated-equality-For-iterated-equality n 1 _ ⟩□
    For-iterated-equality (1 + n) Is-modal A  □

  Is-modal→Is-modalⁿ :
    ∀ n →
    Is-modal A →
    For-iterated-equality n Is-modal A
  Is-modal→Is-modalⁿ zero = id
  Is-modal→Is-modalⁿ {A = A} (suc n) =
    Is-modal A                                →⟨ Is-modal→Is-modalⁿ n ⟩
    For-iterated-equality n Is-modal A        →⟨ Is-modalⁿ→Is-modal¹⁺ⁿ n ⟩□
    For-iterated-equality (suc n) Is-modal A  □

  ----------------------------------------------------------------------
  -- The function ◯-map

  -- A map function for ◯.

  ◯-map : (A → B) → ◯ A → ◯ B
  ◯-map f = ◯-rec Is-modal-◯ (η ∘ f)

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
      (λ _ → Is-modal-◯)
      (λ x →
         ◯-map f (η x)  ≡⟨ ◯-map-η ⟩
         η (f x)        ≡⟨ cong η (p x) ⟩
         η (g x)        ≡⟨ sym ◯-map-η ⟩∎
         ◯-map g (η x)  ∎)
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

  -- If A ↝[ c ∣ d ] B holds, then ◯ A ↝[ k ] ◯ B holds for all k for
  -- which Extensionality? k c d holds.

  ◯-cong-↝ :
    Extensionality? k c d →
    A ↝[ c ∣ d ] B →
    ◯ A ↝[ k ] ◯ B
  ◯-cong-↝ ext hyp = generalise-ext?′
    (◯-cong-⇔ (hyp _))
    (λ ext → ◯-cong-↔ (hyp ext))
    (λ ext → ◯-cong-≃ᴱ (hyp E.[ ext ]))
    ext

  ----------------------------------------------------------------------
  -- Some equivalences and related results

  -- ◯ (↑ a ⊤) is equivalent to ⊤.

  ◯⊤≃ : ◯ (↑ a ⊤) ≃ ⊤
  ◯⊤≃ =
    ◯ (↑ a ⊤)  ↝⟨ inverse Eq.⟨ _ , Is-modal≃Is-equivalence-η _ Is-modal-⊤ ⟩ ⟩
    ↑ a ⊤      ↔⟨ Bijection.↑↔ ⟩□
    ⊤          □

  -- ◯ commutes with _×_.

  ◯×≃ : ◯ (A × B) ≃ (◯ A × ◯ B)
  ◯×≃ = Eq.↔→≃
    (◯-rec m′ (Σ-map η η))
    (uncurry λ x → ◯-rec Is-modal-◯ λ y → ◯-map (_, y) x)
    (λ (x , y) →
       ◯-rec m′ (Σ-map η η) (◯-rec Is-modal-◯ (λ y → ◯-map (_, y) x) y)  ≡⟨ ◯-elim
                                                                              {P = λ y →
                                                                                     ◯-rec m′ (Σ-map η η)
                                                                                       (◯-rec Is-modal-◯ (λ y → ◯-map (_, y) x) y) ≡
                                                                                     (x , y)}
                                                                              (λ _ → Is-modal→Separated m′ _ _)
                                                                              (λ y →
         ◯-rec m′ (Σ-map η η)
           (◯-rec Is-modal-◯ (λ y → ◯-map (_, y) x) (η y))                       ≡⟨ cong (◯-rec _ _)
                                                                                    ◯-rec-η ⟩

         ◯-rec m′ (Σ-map η η) (◯-map (_, y) x)                                   ≡⟨ ◯-elim
                                                                                      (λ _ → Is-modal→Separated m′ _ _)
                                                                                      (λ x →
           ◯-rec m′ (Σ-map η η) (◯-map (_, y) (η x))                                     ≡⟨ cong (◯-rec _ _)
                                                                                            ◯-map-η ⟩

           ◯-rec m′ (Σ-map η η) (η (x , y))                                              ≡⟨ ◯-rec-η ⟩∎

           (η x , η y)                                                                   ∎)
                                                                                      x ⟩∎
         (x , η y)                                                               ∎)
                                                                              _ ⟩∎
       (x , y)                                                           ∎)
    (◯-elim
       (λ _ → Separated-◯ _ _)
       (λ (x , y) →
          uncurry (λ x → ◯-rec Is-modal-◯ λ y → ◯-map (_, y) x)
            (◯-rec m′ (Σ-map η η) (η (x , y)))                   ≡⟨ cong (uncurry λ x → ◯-rec Is-modal-◯ λ y → ◯-map (_, y) x)
                                                                    ◯-rec-η ⟩
          uncurry (λ x → ◯-rec Is-modal-◯ λ y → ◯-map (_, y) x)
            (η x , η y)                                          ≡⟨⟩

          ◯-rec Is-modal-◯ (λ y → ◯-map (_, y) (η x)) (η y)      ≡⟨ ◯-rec-η ⟩


          ◯-map (_, y) (η x)                                     ≡⟨ ◯-map-η ⟩∎

          η (x , y)                                              ∎))
    where
    m′ = Is-modal-Σ Is-modal-◯ λ _ → Is-modal-◯

  -- Four "computation rules" for ◯×≃.

  ◯×≃-η : _≃_.to ◯×≃ (η (x , y)) ≡ (η x , η y)
  ◯×≃-η = ◯-rec-η

  ◯×≃⁻¹-ηʳ : {y : B} → _≃_.from ◯×≃ (x , η y) ≡ ◯-map (_, y) x
  ◯×≃⁻¹-ηʳ {x = x} {y = y} =
    ◯-rec Is-modal-◯ (λ y → ◯-map (_, y) x) (η y)  ≡⟨ ◯-rec-η ⟩∎
    ◯-map (_, y) x                                 ∎

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
      (record { to = _∘ η; from = ◯-elim (λ _ → Is-modal-◯) })
      (λ ext →
           (λ f → apply-ext ext λ x →
              ◯-elim (λ _ → Is-modal-◯) f (η x)  ≡⟨ ◯-elim-η ⟩∎
              f x                                ∎)
         , (λ f → apply-ext ext (◯-elim (λ _ → Separated-◯ _ _) λ x →
              ◯-elim (λ _ → Is-modal-◯) (f ∘ η) (η x)  ≡⟨ ◯-elim-η ⟩∎
              f (η x)                                  ∎)))

  -- I did not take the remaining results in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code (but that does not mean that one cannot find something
  -- similar in those places).

  -- A function with the same type as the right-to-left direction of
  -- Very-modal.Π◯≃◯Π, which is defined below.

  ◯Π→Π◯ :
    {A : Type a} {P : A → Type a} →
    ◯ ((x : A) → P x) → ((x : A) → ◯ (P x))
  ◯Π→Π◯ = flip (◯-map ∘ flip _$_)

  -- The forward direction of ◯Ση≃Σ◯◯, which is defined below (and
  -- which is due to Felix Cherubini). This direction does not depend
  -- on function extensionality.

  ◯Ση→Σ◯◯ : ◯ (Σ A (P ∘ η)) → Σ (◯ A) (◯ ∘ P)
  ◯Ση→Σ◯◯ = ◯-rec m₁ (Σ-map η η)
    where
    m₁ = Is-modal-Σ Is-modal-◯ λ _ → Is-modal-◯

  -- ◯ commutes with Σ in a certain way (assuming function
  -- extensionality).
  --
  -- This lemma is due to Felix Cherubini.
  --
  -- See also Very-modal.◯Ση≃Σ◯◯ below.

  ◯Ση≃Σ◯◯ :
    Extensionality a a →
    ◯ (Σ A (P ∘ η)) ≃ Σ (◯ A) (◯ ∘ P)
  ◯Ση≃Σ◯◯ {A = A} {P = P} ext = Eq.↔→≃
    ◯Ση→Σ◯◯
    (Σ (◯ A) (◯ ∘ P)  →⟨ (λ (x , y) → ◯-map (x ,_) y) ⟩
     ◯ (Σ (◯ A) P)    →⟨ ◯-rec Is-modal-◯ (uncurry $ ◯-elim m₂ $ curry η) ⟩□
     ◯ (Σ A (P ∘ η))  □)
    (uncurry $
     ◯-elim
       (λ _ → Is-modal-Π ext λ _ →
              Is-modal→Separated m₁ _ _)
       (λ x →
          ◯-elim
            (λ _ → Is-modal→Separated m₁ _ _)
            (λ y →
               ◯Ση→Σ◯◯
                 (◯-rec Is-modal-◯ (uncurry $ ◯-elim m₂ $ curry η)
                    (◯-map (η x ,_) (η y)))                         ≡⟨ cong ◯Ση→Σ◯◯ $ cong (◯-rec _ _) ◯-map-η ⟩

               ◯Ση→Σ◯◯
                 (◯-rec Is-modal-◯ (uncurry $ ◯-elim m₂ $ curry η)
                    (η (η x , y)))                                  ≡⟨ cong ◯Ση→Σ◯◯ ◯-rec-η ⟩

               ◯Ση→Σ◯◯ (◯-elim m₂ (curry η) (η x) y)                ≡⟨ cong ◯Ση→Σ◯◯ $ cong (_$ y) ◯-elim-η ⟩

               ◯Ση→Σ◯◯ (η (x , y))                                  ≡⟨⟩

               ◯-rec m₁ (Σ-map η η) (η (x , y))                     ≡⟨ ◯-elim-η ⟩∎

               (η x , η y)                                          ∎)))
    (◯-elim
       (λ _ → Separated-◯ _ _)
       (λ (x , y) →
          let f = λ (x , y) → ◯-map (x ,_) y in

          ◯-rec Is-modal-◯ (uncurry $ ◯-elim m₂ $ curry η)
            (f (◯-rec m₁ (Σ-map η η) (η (x , y))))                        ≡⟨ cong (◯-rec _ _) $ cong f ◯-rec-η ⟩

          ◯-rec Is-modal-◯ (uncurry $ ◯-elim m₂ $ curry η)
            (◯-map (η x ,_) (η y))                                        ≡⟨ cong (◯-rec _ _) ◯-map-η ⟩

          ◯-rec Is-modal-◯ (uncurry $ ◯-elim m₂ $ curry η) (η (η x , y))  ≡⟨ ◯-rec-η ⟩

          ◯-elim m₂ (curry η) (η x) y                                     ≡⟨ cong (_$ y) ◯-elim-η ⟩∎

          η (x , y)                                                       ∎))
    where
    m₁ = Is-modal-Σ Is-modal-◯ λ _ → Is-modal-◯
    m₂ = λ _ → Is-modal-Π ext λ _ → Is-modal-◯

  -- If A is modal, then ◯ (Σ A P) is equivalent to Σ A (◯ ∘ P).

  Is-modal→◯Σ≃Σ◯ :
    Is-modal A →
    ◯ (Σ A P) ≃ Σ A (◯ ∘ P)
  Is-modal→◯Σ≃Σ◯ {A = A} {P = P} m = Eq.↔→≃
    (◯-rec m′ (Σ-map id η))
    (λ (x , y) → ◯-map (x ,_) y)
    (uncurry λ x →
       ◯-elim (λ _ → Is-modal→Separated m′ _ _) λ y →
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
    m′ = Is-modal-Σ m λ _ → Is-modal-◯

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

  Is-modal→Stable : Is-modal A → Stable-[ k ] A
  Is-modal→Stable {A = A} {k = k} =
    Is-modal A      →⟨ Is-modal→≃◯ ⟩
    (A ≃ ◯ A)       →⟨ inverse ⟩
    (◯ A ≃ A)       →⟨ from-equivalence ⟩□
    Stable-[ k ] A  □

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

  -- If A is modal, and P x is k-stable for all x, then Σ A P is
  -- k-stable.

  Stable-Σ :
    {A : Type a} {P : A → Type a} →
    Is-modal A →
    (∀ x → Stable-[ k ] (P x)) →
    Stable-[ k ] (Σ A P)
  Stable-Σ {A = A} {P = P} m s =
    ◯ (Σ A P)    ↔⟨ Is-modal→◯Σ≃Σ◯ m ⟩
    Σ A (◯ ∘ P)  ↝⟨ ∃-cong s ⟩□
    Σ A P        □

  -- If A and B are k-stable, then A × B is k-stable.

  Stable-× : Stable-[ k ] A → Stable-[ k ] B → Stable-[ k ] (A × B)
  Stable-× {A = A} {B = B} sA sB =
    ◯ (A × B)  ↔⟨ ◯×≃ ⟩
    ◯ A × ◯ B  ↝⟨ sA ×-cong sB ⟩□
    A × B      □

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

  -- If f has type A → B, where A and B are modal, then
  -- Is-equivalence f is stable.

  Is-modal→Stable-Is-equivalence :
    {f : A → B} →
    Is-modal A → Is-modal B →
    Stable (Is-equivalence f)
  Is-modal→Stable-Is-equivalence {f = f} mA mB =
                                          $⟨ s ⟩
    Stable (∀ y → Contractible (f ⁻¹ y))  →⟨ Stable-respects-⇔ $ inverse $
                                             Is-equivalence≃Is-equivalence-CP _ ⟩□
    Stable (Is-equivalence f)             □
    where
    s =
      Stable-Π λ y →
      let m : Is-modal (f ⁻¹ y)
          m = Is-modal-Σ mA (λ _ → Is-modal→Separated mB _ _) in
      Stable-Σ m λ _ →
      Stable-Π λ _ →
      Is-modal→Stable (Is-modal→Separated m _ _)

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
    Is-modal A →
    Stable (Contractibleᴱ A)
  Stable-Contractibleᴱ m =
    Stable-Σ m λ _ →
    Stable-Erased (
    Stable-Π λ _ →
    Is-modal→Stable (Is-modal→Separated m _ _))

  -- If f has type A → B, A is modal, and equality is stable for B,
  -- then f ⁻¹ᴱ y is stable.

  Stable-⁻¹ᴱ :
    {A B : Type a} {f : A → B} {y : B} →
    Is-modal A →
    For-iterated-equality 1 Stable B →
    Stable (f ⁻¹ᴱ y)
  Stable-⁻¹ᴱ m s =
    Stable-Σ m λ _ →
    Stable-Erased (s _ _)

  -- A variant of ◯-elim that uses Stable instead of Is-modal.

  ◯-elim′ :
    (∀ x → Stable (P x)) →
    ((x : A) → P (η x)) →
    ((x : ◯ A) → P x)
  ◯-elim′ {A = A} {P = P} s =
    ((x : A) → P (η x))      →⟨ η ∘_ ⟩
    ((x : A) → ◯ (P (η x)))  →⟨ _⇔_.from $ Π◯◯≃Π◯η _ ⟩
    ((x : ◯ A) → ◯ (P x))    →⟨ (λ f x → s x (f x)) ⟩□
    ((x : ◯ A) → P x)        □

  -- A variant of ◯-rec that uses Stable instead of Is-modal.

  ◯-rec′ : Stable B → (A → B) → (◯ A → B)
  ◯-rec′ s = ◯-elim′ (λ _ → s)

  -- If s : Stable B and a certain "computation rule" holds for ◯-rec′
  -- and s, then B is modal.

  ◯-rec′-η→Is-modal :
    (s : Stable B) →
    (∀ {A} {f : A → B} {x : A} → ◯-rec′ s f (η x) ≡ f x) →
    Is-modal B
  ◯-rec′-η→Is-modal s ◯-rec′-η =
    Stable→left-inverse→Is-modal
      s
      (λ x →
         s (η x)                                ≡⟨ cong s $ sym ◯-elim-η ⟩
         s (◯-elim (λ _ → Is-modal-◯) η (η x))  ≡⟨⟩
         ◯-rec′ s id (η x)                      ≡⟨ ◯-rec′-η ⟩∎
         x                                      ∎)

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

  ----------------------------------------------------------------------
  -- Map-like lemmas for Is-modal and Separated, and a related result

  -- If there is an embedding from B to A, and A is separated, then B
  -- is separated.
  --
  -- This follows from one part of Remark 2.16 (2) from "Localization
  -- in homotopy type theory" by Christensen, Opie, Rijke and
  -- Scoccola.
  --
  -- I based the proof on that of in_SepO_embedding, implemented by
  -- Mike Shulman in the file Separated.v in (one version of) the Coq
  -- HoTT library. The proof is very easy, but the Coq lemma is proved
  -- for an arbitrary subuniverse, not a reflective subuniverse, so I
  -- thought that it could perhaps be proved without using η-cong.
  -- However, the definition of subuniverse in the Coq code includes
  -- something like Is-modal-respects-≃.

  Embedding→Separated→Separated :
    Embedding B A → Separated A → Separated B
  Embedding→Separated→Separated B↣A s x y =
                                                        $⟨ s _ _ ⟩
    Is-modal (Embedding.to B↣A x ≡ Embedding.to B↣A y)  →⟨ Is-modal-respects-≃ (inverse $ Embedding.equivalence B↣A) ⟩□
    Is-modal (x ≡ y)                                    □

  -- I did not take the remaining results in this section from
  -- "Modalities in Homotopy Type Theory" or the corresponding Coq
  -- code.

  -- Propositions are separated.
  --
  -- This is Remark 2.16 (3) from "Localization in homotopy type
  -- theory" by Christensen, Opie, Rijke and Scoccola.

  Is-proposition→Separated : Is-proposition A → Separated A
  Is-proposition→Separated {A = A} prop =
    Embedding→Separated→Separated
      emb
      (Is-modal→Separated Is-modal-⊤)
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

  -- Is-modal respects split surjections.

  Is-modal-respects-↠ : A ↠ B → Is-modal A → Is-modal B
  Is-modal-respects-↠ {A = A} {B = B} A↠B m =
    Stable→left-inverse→Is-modal
      (◯ B  →⟨ ◯-map (_↠_.from A↠B) ⟩
       ◯ A  →⟨ η⁻¹ m ⟩
       A    →⟨ _↠_.to A↠B ⟩□
       B    □)
      (λ x →
         _↠_.to A↠B (η⁻¹ m (◯-map (_↠_.from A↠B) (η x)))  ≡⟨ cong (_↠_.to A↠B ∘ η⁻¹ _) ◯-map-η ⟩
         _↠_.to A↠B (η⁻¹ m (η (_↠_.from A↠B x)))          ≡⟨ cong (_↠_.to A↠B) η⁻¹-η ⟩
         _↠_.to A↠B (_↠_.from A↠B x)                      ≡⟨ _↠_.right-inverse-of A↠B x ⟩∎
         x                                                ∎)

  -- A generalisation of Is-modal-respects-↠.
  --
  -- The case for 1 is one part of Remark 2.16 (2) from "Localization
  -- in homotopy type theory" by Christensen, Opie, Rijke and
  -- Scoccola.

  Is-modal-respects-↠ⁿ :
    ∀ n →
    A ↠ B →
    For-iterated-equality n Is-modal A →
    For-iterated-equality n Is-modal B
  Is-modal-respects-↠ⁿ n =
    For-iterated-equality-cong-→ n Is-modal-respects-↠

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
  flatten-→ _ f = ◯-rec Is-modal-◯ f

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
              ◯-rec Is-modal-◯ f (◯-map (map η) (η x))  ≡⟨ cong (◯-rec Is-modal-◯ f) ◯-map-η ⟩
              ◯-rec Is-modal-◯ f (η (map η x))          ≡⟨ ◯-rec-η ⟩
              f (map η x)                               ≡⟨ f-map x ⟩∎
              η x                                       ∎)

      from-to :
        (∀ x → ◯-map (map η) (f x) ≡ η x) →
        ∀ x → from (to x) ≡ x
      from-to map-f =
        ◯-elim
          (λ _ → Separated-◯ _ _)
          (λ x →
             ◯-map (map η) (◯-rec Is-modal-◯ f (η x))  ≡⟨ cong (◯-map (map η)) ◯-rec-η ⟩
             ◯-map (map η) (f x)                       ≡⟨ map-f x ⟩∎
             η x                                       ∎)

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
    (◯-rec Is-modal-◯ id)
    (◯-elim
       (λ _ → Separated-◯ _ _)
       (λ x →
          η (◯-rec Is-modal-◯ id (η x))  ≡⟨ cong η ◯-rec-η ⟩∎
          η x                            ∎))
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

  -- If ◯ (∀ x → Is-modal (P x)) holds, then ◯ ((x : A) → ◯ (P x)) is
  -- equivalent to ◯ (((x : A) → P x)) (assuming function
  -- extensionality).
  --
  -- I did not take this lemma from "Modalities in Homotopy Type
  -- Theory" or the corresponding Coq code.

  ◯Π◯≃◯Π :
    {A : Type a} {P : A → Type a} →
    ◯ (∀ x → Is-modal (P x)) →
    ◯ ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ (((x : A) → P x))
  ◯Π◯≃◯Π {A = A} {P = P} m =
    flatten-↝
      (λ F → (x : A) → F (P x))
      (λ f g x → f (g x))
      (λ f → ◯-map (λ m x → Is-modal→Stable (m x) (f x)) m)
      (λ ext →
           (λ f →
              ◯-elim
                {P = λ m →
                       ◯-map (λ m x → Is-modal→Stable (m x) (η (f x))) m
                         ≡
                       η f}
                (λ _ → Separated-◯ _ _)
                (λ m →
                   ◯-map (λ m x → Is-modal→Stable (m x) (η (f x))) (η m)  ≡⟨ ◯-map-η ⟩
                   η (λ x → Is-modal→Stable (m x) (η (f x)))              ≡⟨ (cong η $ apply-ext ext λ x →
                                                                              _≃_.left-inverse-of (Is-modal→≃◯ (m x)) _) ⟩∎
                   η f                                                    ∎)
                _)
         , (λ f →
              ◯-map (λ g x → η (g x))
                (◯-map (λ m x → Is-modal→Stable (m x) (f x)) m)        ≡⟨ sym ◯-map-∘ ⟩

              ◯-map (λ m x → η (Is-modal→Stable (m x) (f x))) m        ≡⟨ ◯-elim
                                                                            {P = λ m →
                                                                                   ◯-map (λ m x → η (Is-modal→Stable (m x) (f x))) m ≡
                                                                                   η f}
                                                                            (λ _ → Separated-◯ _ _)
                                                                            (λ m →
                ◯-map (λ m x → η (Is-modal→Stable (m x) (f x))) (η m)          ≡⟨ ◯-map-η ⟩

                η (λ x → η (Is-modal→Stable (m x) (f x)))                      ≡⟨ (cong η $ apply-ext ext λ x →
                                                                                            _≃_.right-inverse-of (Is-modal→≃◯ (m x)) _) ⟩∎
                η f                                                            ∎)
                                                                            _ ⟩∎
              η f                                                      ∎))

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
      (◯-rec Is-modal-◯ λ y → ◯-map proj₁ (c y .proj₁))
      (◯-elim
         (λ _ → Separated-◯ _ _)
         (λ y →
            ◯-map f
              (◯-rec Is-modal-◯ (λ y → ◯-map proj₁ (c y .proj₁)) (η y))  ≡⟨ cong (◯-map f) ◯-rec-η ⟩

            ◯-map f (◯-map proj₁ (c y .proj₁))                           ≡⟨ sym ◯-map-∘ ⟩

            ◯-map (f ∘ proj₁) (c y .proj₁)                               ≡⟨⟩

            ◯-map (λ ((x , _) : f ⁻¹ y) → f x) (c y .proj₁)              ≡⟨ ◯-map-cong proj₂ ⟩

            ◯-map (λ _ → y) (c y .proj₁)                                 ≡⟨ ◯-map-const ⟩∎

            η y                                                          ∎))
      (◯-elim
         (λ _ → Separated-◯ _ _)
         (λ x →
            ◯-rec Is-modal-◯ (λ y → ◯-map proj₁ (c y .proj₁))
              (◯-map f (η x))                                            ≡⟨ cong (◯-rec _ _) ◯-map-η ⟩

            ◯-rec Is-modal-◯ (λ y → ◯-map proj₁ (c y .proj₁)) (η (f x))  ≡⟨ ◯-rec-η ⟩

            ◯-map proj₁ (c (f x) .proj₁)                                 ≡⟨ cong (◯-map _) $ c (f x) .proj₂ (η (x , refl _)) ⟩

            ◯-map proj₁ (η (x , refl (f x)))                             ≡⟨ ◯-map-η ⟩∎

            η x                                                          ∎))

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
        (λ _ → Is-modal→Separated Is-modal-◯ _ _)
        (lemma y)
    where
    ◯η⁻¹ : ∀ y → ◯ (η ⁻¹ y)
    ◯η⁻¹ = ◯-elim
      (λ _ → Is-modal-◯)
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

  -- If m : Is-modal B, then a function f to B is ◯-connected if and
  -- only if ◯-rec m f is an equivalence.

  Connected-→≃Is-equivalence-◯-rec :
    {f : A → B} →
    (m : Is-modal B) →
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

      Is-equivalence (η ∘ ◯-rec m f)  →⟨ _⇔_.from (Is-equivalence≃Is-equivalence-∘ˡ (Is-modal≃Is-equivalence-η _ m) _) ⟩□

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
  Connected-→-η-∘-≃Is-equivalence-◯-map =
    Connected-→≃Is-equivalence-◯-rec Is-modal-◯

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
    (∀ x y → Is-modal (x ≡ y))                         ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Is-modal≃Is-equivalence-η ext) ⟩
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
                                                ◯-elim (λ _ → Is-modal-Π ext λ _ →
                                                              Is-modal-H-level′ ext n $
                                                              Is-modal→Is-modalⁿ n $
                                                              Separated-◯ _ _) λ x →
                                                ◯-elim (λ _ → Is-modal-H-level′ ext n $
                                                              Is-modal→Is-modalⁿ n $
                                                              Separated-◯ _ _) λ y →
                                                H-level′-cong _ n (◯≡≃η≡η lex) (h x y)) ⟩□
    ((x y : ◯ A) → H-level′ n (x ≡ y))    □

  -- If ◯ is left exact and A has a given h-level, then ◯ A has the
  -- same h-level (assuming function extensionality).
  --
  -- See also Very-modal.H-level→H-level-◯.

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

  -- If ◯ (Is-modal A) holds, then the function η-cong {x = x} {y = y}
  -- is an equivalence for all x and y of type A.

  ◯-Is-modal→Is-equivalence-η-cong :
    ◯ (Is-modal A) →
    (x y : A) → Is-equivalence (η-cong ⦂ (◯ (x ≡ y) → η x ≡ η y))
  ◯-Is-modal→Is-equivalence-η-cong {A = A} = λ m x y →
    let m′ = Separated-◯ _ _ in
    _≃_.is-equivalence $
    Eq.↔→≃
      _
      (η x ≡ η y                      →⟨ η ⟩
       ◯ (η x ≡ η y)                  →⟨ m ,_ ⟩
       ◯ (Is-modal A) × ◯ (η x ≡ η y) →⟨ _≃_.from ◯×≃ ⟩
       ◯ (Is-modal A × η x ≡ η y)     →⟨ ◯-map lemma ⟩□
       ◯ (x ≡ y)                      □)
      (λ p →
         ◯-elim
           {P = λ m →
                  ◯-rec m′ (cong η)
                    (◯-map lemma (_≃_.from ◯×≃ (m , η p))) ≡
                  p}
           (λ _ → Is-modal→Separated m′ _ _)
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
    lemma : {x y : A} → Is-modal A × η x ≡ η y → x ≡ y
    lemma {x = x} {y = y} (m , p) =
      x            ≡⟨ sym η⁻¹-η ⟩
      η⁻¹ m (η x)  ≡⟨ cong (η⁻¹ m) p ⟩
      η⁻¹ m (η y)  ≡⟨ η⁻¹-η ⟩∎
      y            ∎

    ≡≃η≡η : {x y : A} → Is-modal A → (x ≡ y) ≃ (η x ≡ η y)
    ≡≃η≡η m =
      Embedding.equivalence $
      record
        { is-embedding = Is-modal→Is-embedding-η m
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
        (Stable-Π λ _ → Is-modal→Stable Is-modal-◯)

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
    (∀ y → ∃ λ x → ◯ (◯-map f x ≡ y))      →⟨ (∀-cong _ λ _ → ∃-cong λ _ → Is-modal→Stable (Separated-◯ _ _)) ⟩□
    (∀ y → ∃ λ x → ◯-map f x ≡ y)          □

  -- A generalisation of ◯-cong-↠.

  ◯-cong-↠-◯ : ◯ (A ↠ B) → ◯ A ↠ ◯ B
  ◯-cong-↠-◯ =
    ◯↝→◯↝◯
      ↠↔∃-Split-surjective
      ◯-Split-surjective→Split-surjective
      (Split-surjective-cong _)
      (Stable-Π λ _ → Is-modal→Stable $
       Is-modal-Σ Is-modal-◯ λ _ → Separated-◯ _ _)

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
                                                                           (∀-cong _ λ _ → Is-modal→Stable (Separated-◯ _ _))
                                                                             ×-cong
                                                                           (∀-cong _ λ _ → Is-modal→Stable (Separated-◯ _ _))) ⟩
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
      (Is-modal→Stable-Is-equivalence Is-modal-◯ Is-modal-◯)

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
    (∀ x y → ◯-map f (η x) ≡ ◯-map f (η y) → η x ≡ η y)  →⟨ (∀-cong _ λ _ → _⇔_.from $ Π◯⇔Πη s) ⟩
    (∀ x y → ◯-map f (η x) ≡ ◯-map f y → η x ≡ y)        →⟨ (_⇔_.from $ Π◯⇔Πη λ _ → Stable-Π s) ⟩
    (∀ x y → ◯-map f x ≡ ◯-map f y → x ≡ y)              →⟨ (λ g → g _ _) ⟩□
    (∀ {x y} → ◯-map f x ≡ ◯-map f y → x ≡ y)            □
    where
    s : ∀ {x} y → Stable (◯-map f x ≡ ◯-map f y → x ≡ y)
    s _ = Stable-Π λ _ → Is-modal→Stable $ Separated-◯ _ _

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
       Is-modal→Stable $ Separated-◯ _ _)

  -- A lemma used in the implementations of
  -- ◯-Is-embedding→Is-embedding and
  -- Very-modal.◯-Is-embedding≃Is-embedding.

  ◯-map-cong≡ :
    (lex : Left-exact-η-cong) (p : ◯ (x ≡ y)) →
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
                                                                              Is-modal→Stable-Is-equivalence
                                                                                (Separated-◯ _ _) (Separated-◯ _ _)) ⟩
    (∀ x y →
       Is-equivalence
         (cong (◯-map f) ⦂ (x ≡ η y → ◯-map f x ≡ ◯-map f (η y))))        →⟨ (∀-cong _ λ _ → _⇔_.from $
                                                                              Π◯⇔Πη λ _ →
                                                                              Is-modal→Stable-Is-equivalence
                                                                                (Separated-◯ _ _) (Separated-◯ _ _)) ⟩□
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
       Is-modal→Stable-Is-equivalence
         (Separated-◯ _ _) (Separated-◯ _ _))

------------------------------------------------------------------------
-- Some results that hold for every empty-modal modality

-- These results are not based on "Modalities in Homotopy Type Theory"
-- or the corresponding Coq code (unless otherwise noted).

module Empty-modal (M : Modality a) (Is-modal-⊥ : Empty-modal M) where

  open Modality M

  -- ◯ ⊥ is equivalent to ⊥₀.

  ◯⊥≃⊥ : ◯ ⊥ ≃ ⊥₀
  ◯⊥≃⊥ =
    ◯ ⊥  ↝⟨ inverse $ Is-modal→≃◯ Is-modal-⊥ ⟩
    ⊥    ↔⟨ ⊥↔⊥ ⟩□
    ⊥₀   □

  -- ◯ commutes with ¬_ (assuming extensionality).

  ◯¬≃¬ : ◯ (¬ A) ↝[ a ∣ lzero ] ¬ ◯ A
  ◯¬≃¬ {A = A} = generalise-ext?
    (record
       { to = λ f x →   $⟨ _≃_.from ◯×≃ (f , x) ⟩
           ◯ (¬ A × A)  →⟨ ◯-map (_↔_.to ⊥↔⊥ ∘ uncurry _$_) ⟩
           ◯ ⊥          ↔⟨ ◯⊥≃⊥ ⟩□
           ⊥₀           □
       ; from = λ hyp → η (hyp ∘ η)
       })
    (λ ext →
         (λ f → apply-ext ext λ x →
            ⊥-elim (f x))
       , ◯-elim
           (λ _ → Separated-◯ _ _)
           (λ f → cong η $ apply-ext ext λ x →
              ⊥-elim (f x)))

  -- ◯ can be dropped under ¬_ (assuming extensionality).

  ¬◯≃¬ : ¬ ◯ A ↝[ a ∣ lzero ] ¬ A
  ¬◯≃¬ {A = A} =
    generalise-ext?-prop
      (record
         { to   = _∘ η
         ; from = λ f → ⊥-elim ∘ ◯-rec Is-modal-⊥ (⊥-elim ∘ f)
         })
      ¬-propositional
      ¬-propositional

  -- Dec A implies Dec (◯ A).
  --
  -- This result appears in (at least one version of) the Coq code
  -- accompanying "Modalities in Homotopy Type Theory".

  Dec→Dec-◯ : Dec A → Dec (◯ A)
  Dec→Dec-◯ (yes x)    = yes (η x)
  Dec→Dec-◯ (no empty) =
    no (⊥-elim ∘ ◯-rec Is-modal-⊥ (⊥-elim ∘ empty))

  -- ◯ A implies ¬ ¬ A.

  ◯→¬¬ : ◯ A → ¬ ¬ A
  ◯→¬¬ x f = _≃_.to ◯⊥≃⊥ (◯-map (⊥-elim ∘ f) x)

  -- Types that are stable for double negation are stable.

  ¬¬-stable→Stable : (¬ ¬ A → A) → Stable A
  ¬¬-stable→Stable = _∘ ◯→¬¬

  -- Types for which it is known whether or not they are inhabited are
  -- stable.

  Dec→Stable : Dec A → Stable A
  Dec→Stable         (yes x)    = λ _ → x
  Dec→Stable {A = A} (no empty) =
    ◯ A    →⟨ ◯→¬¬ ⟩
    ¬ ¬ A  →⟨ _$ empty ⟩
    ⊥      →⟨ ⊥-elim ⟩□
    A      □

  -- If equality is decidable for A, then A is separated.

  Decidable-equality→Separated :
    Decidable-equality A → Separated A
  Decidable-equality→Separated dec x y =
    Stable→Is-proposition→Is-modal
      (Dec→Stable (dec x y))
      (decidable⇒set dec)

  -- The type ¬ A is k-stable (perhaps assuming function
  -- extensionality).

  Stable-¬ :
    Extensionality? k a lzero →
    Stable-[ k ] (¬ A)
  Stable-¬ {A = A} ext =
    ◯ (¬ A)  ↝⟨ ◯¬≃¬ ext ⟩
    ¬ (◯ A)  ↝⟨ ¬◯≃¬ ext ⟩□
    ¬ A      □

  -- ¬ A is modal (assuming function extensionality).

  Is-modal-¬ :
    Extensionality a lzero →
    Is-modal (¬ A)
  Is-modal-¬ {A = A} ext =
    Is-equivalence-η→Is-modal $
    _≃_.is-equivalence $
    Eq.with-other-function
      (inverse $ Stable-¬ ext)
      η
      (λ empty → cong η $ apply-ext ext (⊥-elim ∘ empty))

  -- If equality is k-stable for A and B, then equality is k-stable
  -- for A ⊎ B. (The lemma is more general.)

  Stable-≡-⊎ :
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    For-iterated-equality (1 + n) Stable-[ k ] B →
    For-iterated-equality (1 + n) Stable-[ k ] (A ⊎ B)
  Stable-≡-⊎ n sA sB =
    For-iterated-equality-⊎-suc
      n
      lemma
      (Is-modal→Stable Is-modal-⊥)
      (For-iterated-equality-↑ _ (1 + n) lemma sA)
      (For-iterated-equality-↑ _ (1 + n) lemma sB)
    where
    lemma : A ↔ B → Stable-[ k ] A → Stable-[ k ] B
    lemma = Stable-respects-≃ ∘ from-isomorphism

  -- If A and B are separated, then A ⊎ B is separated. (The lemma is
  -- more general.)

  Separated-⊎ :
    ∀ n →
    For-iterated-equality (1 + n) Is-modal A →
    For-iterated-equality (1 + n) Is-modal B →
    For-iterated-equality (1 + n) Is-modal (A ⊎ B)
  Separated-⊎ n sA sB =
    For-iterated-equality-⊎-suc
      n
      lemma
      Is-modal-⊥
      (For-iterated-equality-↑ _ (1 + n) lemma sA)
      (For-iterated-equality-↑ _ (1 + n) lemma sB)
    where
    lemma : A ↔ B → Is-modal A → Is-modal B
    lemma = Is-modal-respects-≃ ∘ from-isomorphism

  -- If equality is k-stable for A, then it is k-stable for List A.
  -- (The lemma is more general.)

  Stable-≡-List :
    ∀ n →
    For-iterated-equality (1 + n) Stable-[ k ] A →
    For-iterated-equality (1 + n) Stable-[ k ] (List A)
  Stable-≡-List n =
    For-iterated-equality-List-suc
      n
      (Stable-respects-≃ ∘ from-isomorphism)
      (Is-modal→Stable Is-modal-⊤)
      (Is-modal→Stable Is-modal-⊥)
      Stable-×

  -- If A is separated, then List A is separated. (The lemma is more
  -- general.)

  Separated-List :
    ∀ n →
    For-iterated-equality (1 + n) Is-modal A →
    For-iterated-equality (1 + n) Is-modal (List A)
  Separated-List n =
    For-iterated-equality-List-suc
      n
      (Is-modal-respects-≃ ∘ from-isomorphism)
      Is-modal-⊤
      Is-modal-⊥
      (λ mA mB → Is-modal-Σ mA λ _ → mB)

------------------------------------------------------------------------
-- Some results that hold for every very modal modality

module Very-modal (M : Modality a) (very-modal : Very-modal M) where

  open Modality M
    hiding (◯Ση≃Σ◯◯; Stable-Π; Stable-implicit-Π;
            Is-modal→Stable-Is-equivalence)

  -- I did not take the results in this module from "Modalities in
  -- Homotopy Type Theory" or the corresponding Coq code.

  ----------------------------------------------------------------------
  -- Should "Very-modal" be stated differently?

  -- ◯ (∀ x → Is-modal (P x)) is inhabited.
  --
  -- One might wonder if something like ◯ ({A : Type a} → Is-modal A)
  -- would be more general than Very-modal M. However, the former
  -- statement is not type-correct. The statement
  --
  --   {A : Type a} {P : A → Type a} → ◯ (∀ x → Is-modal (P x))
  --
  -- is type-correct, but follows from Very-modal M.

  ◯-Π-Is-modal :
    {A : Type a} {P : A → Type a} → ◯ (∀ x → Is-modal (P x))
  ◯-Π-Is-modal {A = A} {P = P} =
                                           $⟨ (λ {_} → very-modal) ⟩
    Very-modal M                           →⟨ (λ m → m , m) ⟩
    ◯ (Is-modal A) × ◯ (Is-modal (Σ A P))  →⟨ _≃_.from ◯×≃ ⟩
    ◯ (Is-modal A × Is-modal (Σ A P))      →⟨ ◯-map (λ (mA , mΣAP) → Is-modal-Σ≃Π-Is-modal mA _ mΣAP) ⟩□
    ◯ (∀ x → Is-modal (P x))               □

  ----------------------------------------------------------------------
  -- The modality is left exact and, assuming function extensionality,
  -- topological

  -- Very modal modalities are left exact.
  --
  -- See also left-exact below.

  left-exact-η-cong : Left-exact-η-cong
  left-exact-η-cong =
    ◯-Is-modal→Is-equivalence-η-cong very-modal _ _

  -- Is-modal A is equivalent to Is-modal -Null A (assuming function
  -- extensionality).

  Is-modal≃Is-modal-Null :
    Extensionality a a →
    Is-modal A ↝[ lsuc a ∣ a ] Is-modal -Null A
  Is-modal≃Is-modal-Null {A = A} ext =
    generalise-ext?-prop
      (record { to = to; from = from })
      (λ _ → Is-modal-propositional ext)
      (λ ext′ →
         Π-closure ext′ 1 λ _ →
         Eq.propositional ext _)
    where
    to : Is-modal A → Is-modal -Null A
    to m _ =
      _≃_.is-equivalence $
      Eq.↔→≃
        const
        (λ f → η⁻¹ m (◯-map f very-modal))
        (λ f → apply-ext ext λ m′ →
           ◯-elim
             {P = λ m″ → η⁻¹ m (◯-map f m″) ≡ f m′}
             (λ _ → Is-modal→Separated m _ _)
             (λ m″ →
                η⁻¹ m (◯-map f (η m″))  ≡⟨ cong (η⁻¹ m) ◯-map-η ⟩
                η⁻¹ m (η (f m″))        ≡⟨ η⁻¹-η ⟩
                f m″                    ≡⟨ cong f $ Is-modal-propositional ext _ _ ⟩∎
                f m′                    ∎)
             very-modal)
        (λ x →
           ◯-elim
             {P = λ m′ → η⁻¹ m (◯-map (const x) m′) ≡ x}
             (λ _ → Is-modal→Separated m _ _)
             (λ m′ →
                η⁻¹ m (◯-map (const x) (η m′))  ≡⟨ cong (η⁻¹ m) ◯-map-η ⟩
                η⁻¹ m (η x)                     ≡⟨ η⁻¹-η ⟩∎
                x                               ∎)
             very-modal)

    from : Is-modal -Null A → Is-modal A
    from null =
      Is-equivalence-η→Is-modal $
      _≃_.is-equivalence $
      Eq.↔→≃
        η
        (◯ A               →⟨ flip η⁻¹ ⟩
         (Is-modal A → A)  ↔⟨ inverse A≃ ⟩□
         A                 □)
        (◯-elim
           (λ _ → Separated-◯ _ _)
           (λ x → cong η (lemma x)))
        lemma
      where
      A≃ : A ≃ (Is-modal A → A)
      A≃ = Eq.⟨ const , null A ⟩

      lemma : ∀ x → _≃_.from A≃ (λ m → η⁻¹ m (η x)) ≡ x
      lemma x =
        _≃_.from A≃ (λ m → η⁻¹ m (η x))  ≡⟨ (cong (_≃_.from A≃) $
                                             apply-ext ext λ _ →
                                             η⁻¹-η) ⟩
        _≃_.from A≃ (const x)            ≡⟨⟩
        _≃_.from A≃ (_≃_.to A≃ x)        ≡⟨ _≃_.left-inverse-of A≃ _ ⟩∎
        x                                ∎

  -- The modality is topological for certain universe levels (assuming
  -- function extensionality).
  --
  -- TODO: Are there any topological modalities which are not very
  -- modal?

  topological :
    Extensionality (lsuc a ⊔ ℓ) (lsuc a ⊔ ℓ) →
    Topological (lsuc a ⊔ ℓ) M
  topological {ℓ = ℓ} ext =
      ( ↑ ℓ (Type a)
      , ↑ _ ∘ Is-modal ∘ lower
      , (λ A →
           Is-modal A                                     ↝⟨ Is-modal≃Is-modal-Null ext′ _ ⟩
           Is-modal -Null A                               ↝⟨ (inverse $
                                                              Π-cong _ Bijection.↑↔ λ B →
                                                              Is-equivalence≃Is-equivalence-∘ˡ
                                                                (_≃_.is-equivalence $
                                                                 Eq.↔→≃ (_∘ lift) (_∘ lower) refl refl)
                                                                _) ⟩
           (↑ _ ∘ Is-modal ∘ lower) -Null A               ↔⟨ inverse $ PS.Π-Is-∞-extendable-along≃Null ext ⟩□
           (∀ _ → Is-∞-extendable-along-[ _ ] (λ _ → A))  □)
      )
    , (λ _ → ↑-closure 1 $ Is-modal-propositional ext′)
    where
    ext′ = lower-extensionality _ _ ext

  ----------------------------------------------------------------------
  -- Some equivalences

  -- ◯ (Is-modal A) is equivalent to the unit type (assuming function
  -- extensionality).

  ◯-Is-modal≃⊤ : ◯ (Is-modal A) ↝[ a ∣ a ] ⊤
  ◯-Is-modal≃⊤ {A = A} =
    generalise-ext?
      (record { from = λ _ → very-modal })
      (λ ext →
           refl
         , (λ m →
              very-modal  ≡⟨ Left-exact-η-cong→H-level→H-level-◯
                               ext left-exact-η-cong 1
                               (Is-modal-propositional ext)
                               _ _ ⟩∎
              m           ∎))

  -- ◯ B is equivalent to ◯ (Is-modal A × B) (assuming function
  -- extensionality).

  ◯≃◯-Is-modal-× : ◯ B ↝[ a ∣ a ] ◯ (Is-modal A × B)
  ◯≃◯-Is-modal-× {B = B} {A = A} ext =
    ◯ B                   ↝⟨ inverse-ext? (drop-⊤-left-× ∘ const ∘ ◯-Is-modal≃⊤) ext ⟩
    ◯ (Is-modal A) × ◯ B  ↔⟨ inverse ◯×≃ ⟩□
    ◯ (Is-modal A × B)    □

  -- A variant of ◯≃◯-Is-modal-×.

  ◯≃◯Σ-Is-modal :
    (P : A → Type a) →
    ◯ (P x) ↝[ a ∣ a ] ◯ (∃ λ (m : Is-modal A) → P (◯-rec m id (η x)))
  ◯≃◯Σ-Is-modal {A = A} {x = x} P ext =
    ◯ (P x)                                          ↝⟨ ◯≃◯-Is-modal-× ext ⟩
    ◯ (Is-modal A × P x)                             ↔⟨ (◯-cong-≃ $ ∃-cong λ _ → ≡⇒↝ _ $ cong P $ sym ◯-rec-η) ⟩□
    ◯ (∃ λ (m : Is-modal A) → P (◯-rec m id (η x)))  □

  -- A kind of choice principle holds.

  Π◯≃◯Π :
    {A : Type a} {P : A → Type a} →
    ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ ((x : A) → P x)
  Π◯≃◯Π {A = A} {P = P} ext =
    ((x : A) → ◯ (P x))    ↝⟨ lemma ext ⟩
    ◯ ((x : A) → ◯ (P x))  ↝⟨ ◯Π◯≃◯Π ◯-Π-Is-modal ext ⟩□
    ◯ ((x : A) → P x)      □
    where
    from =
      ◯ ((x : A) → ◯ (P x))    →⟨ ◯Π→Π◯ ⟩
      ((x : A) → ◯ (◯ (P x)))  →⟨ _≃_.from ◯≃◯◯ ∘_ ⟩□
      ((x : A) → ◯ (P x))      □

    lemma =
      generalise-ext?
        (record { to = η; from = from })
        (λ ext →
           let from-η : ∀ f → from (η f) ≡ f
               from-η = λ f → apply-ext ext λ x →
                 from (η f) x                              ≡⟨⟩
                 ◯-rec Is-modal-◯ id (◯-map (_$ x) (η f))  ≡⟨ cong (◯-rec _ _) ◯-map-η ⟩
                 ◯-rec Is-modal-◯ id (η (f x))             ≡⟨ ◯-rec-η ⟩∎
                 f x                                       ∎
           in
             (◯-elim
                (λ _ → Separated-◯ _ _)
                (λ f →
                   η (from (η f))  ≡⟨ cong η $ from-η f ⟩∎
                   η f             ∎))
           , from-η)

  -- A variant of Modality-lemma.◯Ση≃Σ◯◯ proved using the assumption
  -- that the modality is very modal, instead of function
  -- extensionality.

  ◯Ση≃Σ◯◯ : ◯ (Σ A (P ∘ η)) ≃ Σ (◯ A) (◯ ∘ P)
  ◯Ση≃Σ◯◯ {A = A} {P = P} = Eq.↔→≃
    ◯Ση→Σ◯◯
    (Σ (◯ A) (◯ ∘ P)             →⟨ (λ (x , y) → ◯-map (x ,_) y) ⟩
     ◯ (Σ (◯ A) P)               →⟨ ◯≃◯-Is-modal-× _ ⟩
     ◯ (Is-modal A × Σ (◯ A) P)  →⟨ ◯-map (proj₂ ∘ ∃-cong λ m → _≃_.from $ Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id) ⟩□
     ◯ (Σ A (P ∘ η))             □)
    (λ (x , y) →
       ◯-elim
         {P = λ m →
                ◯-rec m₁ (Σ-map η η)
                  (◯-map (proj₂ ∘
                          ∃-cong λ m → _≃_.from $
                          Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                     (_≃_.from ◯×≃ (m , ◯-map (x ,_) y))) ≡
                (x , y)}
         (λ _ → Is-modal→Separated m₁ _ _)
         (λ m →
            ◯-elim
              {P = λ y →
                     ◯-rec m₁ (Σ-map η η)
                       (◯-map (proj₂ ∘
                               ∃-cong λ m → _≃_.from $
                               Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                          (_≃_.from ◯×≃ (η m , ◯-map (x ,_) y))) ≡
                     (x , y)}
              (λ _ → Is-modal→Separated m₁ _ _)
              (λ y →
                 ◯-rec m₁ (Σ-map η η)
                   (◯-map (proj₂ ∘
                           ∃-cong λ m → _≃_.from $
                           Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                      (_≃_.from ◯×≃ (η m , ◯-map (x ,_) (η y))))        ≡⟨ cong (◯-rec _ _) $ cong (◯-map _) $ cong (_≃_.from ◯×≃) $ cong (η m ,_)
                                                                           ◯-map-η ⟩
                 ◯-rec m₁ (Σ-map η η)
                   (◯-map (proj₂ ∘
                           ∃-cong λ m → _≃_.from $
                           Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                      (_≃_.from ◯×≃ (η m , η (x , y))))                 ≡⟨ cong (◯-rec _ _) $ cong (◯-map _)
                                                                           ◯×≃⁻¹-η ⟩
                 ◯-rec m₁ (Σ-map η η)
                   (◯-map (proj₂ ∘
                           ∃-cong λ m → _≃_.from $
                           Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                      (η (m , x , y)))                                  ≡⟨ cong (◯-rec _ _)
                                                                           ◯-map-η ⟩
                 ◯-rec m₁ (Σ-map η η)
                   (η (_≃_.from
                         (Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                         (x , y)))                                      ≡⟨ ◯-rec-η ⟩

                 Σ-map η η
                   (_≃_.from (Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                      (x , y))                                          ≡⟨⟩

                 ( η (_≃_.from (Is-modal→≃◯ m) x)
                 , η (subst P
                        (sym (_≃_.right-inverse-of (Is-modal→≃◯ m) x))
                        y)
                 )                                                      ≡⟨ elim₁
                                                                             (λ {x′} eq → (x′ , η (subst P (sym eq) y)) ≡ (x , η y))
                                                                             (
                   (x , η (subst P (sym $ refl x) y))                         ≡⟨ cong (x ,_) $ cong η $
                                                                                 trans (cong (flip (subst P) _) $ sym-refl) $
                                                                                 subst-refl _ _ ⟩∎
                   (x , η y)                                                  ∎)
                                                                             _ ⟩∎
                 (x , η y)                                              ∎)
              y)
         very-modal)
    (◯-elim
       (λ _ → Separated-◯ _ _)
       (λ (x , y) →
          let f = (λ (x , y) → ◯-map (x ,_) y) in
          ◯-elim
            {P = λ m →
                   ◯-map (proj₂ ∘
                          ∃-cong λ m → _≃_.from $
                          Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                     (_≃_.from ◯×≃
                        (m , f (◯-rec m₁ (Σ-map η η) (η (x , y))))) ≡
                   η (x , y)}
            (λ _ → Separated-◯ _ _)
            (λ m →
               ◯-map (proj₂ ∘
                      ∃-cong λ m → _≃_.from $
                      Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                 (_≃_.from ◯×≃
                    (η m , f (◯-rec m₁ (Σ-map η η) (η (x , y)))))        ≡⟨ cong (◯-map _) $ cong (_≃_.from ◯×≃) $ cong (η m ,_) $ cong f
                                                                            ◯-rec-η ⟩
               ◯-map (proj₂ ∘
                      ∃-cong λ m → _≃_.from $
                      Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                 (_≃_.from ◯×≃ (η m , ◯-map (η x ,_) (η y)))             ≡⟨ cong (◯-map _) $ cong (_≃_.from ◯×≃) $ cong (η m ,_)
                                                                            ◯-map-η ⟩
               ◯-map (proj₂ ∘
                      ∃-cong λ m → _≃_.from $
                      Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                 (_≃_.from ◯×≃ (η m , η (η x , y)))                      ≡⟨ cong (◯-map _)
                                                                            ◯×≃⁻¹-η ⟩
               ◯-map (proj₂ ∘
                      ∃-cong λ m → _≃_.from $
                      Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                 (η (m , η x , y))                                       ≡⟨ ◯-map-η ⟩

               η (_≃_.from (Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                    (η x , y))                                           ≡⟨⟩

               η ( _≃_.from (Is-modal→≃◯ m) (η x)
                 , subst P
                     (sym (_≃_.right-inverse-of (Is-modal→≃◯ m) (η x)))
                     y
                 )                                                       ≡⟨ cong η $ cong (_ ,_) $ cong (flip (subst P) _) $ cong sym $ sym $
                                                                            _≃_.left-right-lemma (Is-modal→≃◯ m) _ ⟩
               η ( _≃_.from (Is-modal→≃◯ m) (η x)
                 , subst P
                     (sym $ cong η $
                      _≃_.left-inverse-of (Is-modal→≃◯ m) x)
                     y
                 )                                                       ≡⟨ cong η $
                                                                            elim₁
                                                                              (λ {x′} eq → (x′ , subst P (sym $ cong η eq) y) ≡ (x , y))
                                                                              (
                 (x , subst P (sym $ cong η $ refl x) y)                       ≡⟨ cong (x ,_) $
                                                                                  trans (cong (flip (subst P) _) $
                                                                                         trans (cong sym $ cong-refl _) $
                                                                                         sym-refl) $
                                                                                  subst-refl _ _ ⟩∎
                 (x , y)                                                       ∎)
                                                                              _ ⟩∎
               η (x , y)                                                 ∎)
            very-modal))
    where
    m₁ = Is-modal-Σ Is-modal-◯ λ _ → Is-modal-◯

  -- ◯ commutes with Σ in a certain way.

  ◯Σ≃Σ◯◯ :
    {P : A → Type a} →
    ◯ (Σ A P) ↝[ a ∣ a ] Σ (◯ A) (λ x → ◯ (∃ λ m → P (◯-rec m id x)))
  ◯Σ≃Σ◯◯ {A = A} {P = P} ext =
    ◯ (Σ A P)                                     ↝⟨ ◯≃◯-Is-modal-× ext ⟩
    ◯ (Is-modal A × Σ A P)                        ↔⟨ ◯-cong-↔ ∃-comm ⟩
    ◯ (Σ A (λ x → Is-modal A × P x))              ↔⟨ ◯-cong-≃ $ (∃-cong λ _ → ∃-cong λ _ → ≡⇒↝ _ $ cong P $ sym ◯-rec-η) ⟩
    ◯ (Σ A (λ x → ∃ λ m → P (◯-rec m id (η x))))  ↔⟨ ◯Ση≃Σ◯◯ ⟩□
    Σ (◯ A) (λ x → ◯ (∃ λ m → P (◯-rec m id x)))  □

  ----------------------------------------------------------------------
  -- Stability

  -- Stability (k-stability) is closed under Π-types (perhaps assuming
  -- function extensionality).

  Stable-Π :
    {A : Type a} {P : A → Type a} →
    Extensionality? k a a →
    (∀ x → Stable-[ k ] (P x)) →
    Stable-[ k ] ((x : A) → P x)
  Stable-Π {A = A} {P = P} ext hyp =
    ◯ ((x : A) → P x)    ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
    ((x : A) → ◯ (P x))  ↝⟨ ∀-cong ext hyp ⟩□
    ((x : A) → P x)      □

  -- Stability (k-stability) is closed under implicit Π-types (perhaps
  -- assuming function extensionality).

  Stable-implicit-Π :
    {A : Type a} {P : A → Type a} →
    Extensionality? k a a →
    (∀ x → Stable-[ k ] (P x)) →
    Stable-[ k ] ({x : A} → P x)
  Stable-implicit-Π {A = A} {P = P} ext hyp =
    ◯ ({x : A} → P x)  ↔⟨ ◯-cong-↔ Bijection.implicit-Π↔Π ⟩
    ◯ ((x : A) → P x)  ↝⟨ Stable-Π ext hyp ⟩
    ((x : A) → P x)    ↔⟨ inverse Bijection.implicit-Π↔Π ⟩□
    ({x : A} → P x)    □

  -- If f has type A → B, where A and B are modal, then
  -- Is-equivalence f is k-stable (perhaps assuming function
  -- extensionality).

  Is-modal→Stable-Is-equivalence :
    {f : A → B} →
    Extensionality? k a a →
    Is-modal A → Is-modal B →
    Stable-[ k ] (Is-equivalence f)
  Is-modal→Stable-Is-equivalence {k = k} {f = f} ext mA mB =
                                                $⟨ s ⟩
    Stable-[ k ] (∀ y → Contractible (f ⁻¹ y))  →⟨ Stable-respects-↝ ext $ inverse-ext?
                                                   Is-equivalence≃Is-equivalence-CP ⟩□
    Stable-[ k ] (Is-equivalence f)             □
    where
    s =
      Stable-Π ext λ y →
      let m : Is-modal (f ⁻¹ y)
          m = Is-modal-Σ mA (λ _ → Is-modal→Separated mB _ _) in
      Stable-Σ m λ _ →
      Stable-Π ext λ _ →
      Is-modal→Stable (Is-modal→Separated m _ _)

  -- If A is modal, then H-level′ n A is k-stable (perhaps assuming
  -- function extensionality).

  Stable-H-level′ :
    Extensionality? k a a →
    ∀ n →
    Is-modal A →
    Stable-[ k ] (H-level′ n A)
  Stable-H-level′ {k = k} {A = A} ext zero =
    Is-modal A                     →⟨ (λ m →
                                         Stable-Σ m λ _ →
                                         Stable-Π ext λ _ →
                                         Is-modal→Stable $ Is-modal→Separated m _ _) ⟩□
    Stable-[ k ] (Contractible A)  □
  Stable-H-level′ {k = k} {A = A} ext (suc n) =
    Is-modal A                                     →⟨ (λ m →
                                                         Stable-Π ext λ _ →
                                                         Stable-Π ext λ _ →
                                                         Stable-H-level′ ext n $
                                                         Is-modal→Separated m _ _) ⟩□
    Stable-[ k ] ((x y : A) → H-level′ n (x ≡ y))  □

  -- If A is modal, then H-level n A is k-stable (perhaps assuming
  -- function extensionality).

  Stable-H-level :
    Extensionality? k a a →
    ∀ n →
    Is-modal A →
    Stable-[ k ] (H-level n A)
  Stable-H-level {A = A} ext n m =
    ◯ (H-level n A)   ↝⟨ ◯-cong-↝ ext H-level↔H-level′ ⟩
    ◯ (H-level′ n A)  ↝⟨ Stable-H-level′ ext n m ⟩
    H-level′ n A      ↝⟨ inverse-ext? H-level↔H-level′ ext ⟩□
    H-level n A       □

  ----------------------------------------------------------------------
  -- Preservation lemmas

  -- One can prove that ◯ A ↝[ k ] ◯ B holds by proving A ↝[ d ∣ e ] B
  -- under the assumption that any type C is modal (perhaps assuming
  -- function extensionality).

  ◯-cong-↝-Is-modal→ :
    ∀ d e →
    Extensionality? k (a ⊔ d) (a ⊔ e) →
    (Is-modal C → A ↝[ a ⊔ d ∣ a ⊔ e ] B) →
    ◯ A ↝[ k ] ◯ B
  ◯-cong-↝-Is-modal→ {C = C} {A = A} {B = B} d e ext hyp =
    generalise-ext?′
      (◯ A                 ↝⟨ ◯≃◯-Is-modal-× _ ⟩
       ◯ (Is-modal C × A)  ↝⟨ ◯-cong-⇔ (∃-cong λ m → hyp m _) ⟩
       ◯ (Is-modal C × B)  ↝⟨ inverse-ext? ◯≃◯-Is-modal-× _ ⟩□
       ◯ B                 □)
      (λ ext →
         ◯ A                 ↝⟨ ◯≃◯-Is-modal-× (lower-extensionality d e ext) ⟩
         ◯ (Is-modal C × A)  ↝⟨ ◯-cong-↔ (∃-cong λ m → hyp m ext) ⟩
         ◯ (Is-modal C × B)  ↝⟨ inverse-ext? ◯≃◯-Is-modal-× (lower-extensionality d e ext) ⟩□
         ◯ B                 □)
      (λ ext →
         ◯ A                 ↝⟨ ◯≃◯-Is-modal-× (lower-extensionality? equivalenceᴱ d e E.[ ext ]) ⟩
         ◯ (Is-modal C × A)  ↝⟨ ◯-cong-≃ᴱ (∃-cong λ m → hyp m E.[ ext ]) ⟩
         ◯ (Is-modal C × B)  ↝⟨ inverse-ext? ◯≃◯-Is-modal-× (lower-extensionality? equivalenceᴱ d e E.[ ext ]) ⟩□
         ◯ B                 □)
      ext

  -- A variant of ◯-cong-↝-Is-modal→.

  Is-modal→↝→↝ :
    ∀ d e →
    Extensionality? k (a ⊔ d) (a ⊔ e) →
    A ↝[ k ] ◯ A →
    ◯ B ↝[ k ] B →
    (Is-modal C → A ↝[ a ⊔ d ∣ a ⊔ e ] B) →
    A ↝[ k ] B
  Is-modal→↝→↝ {A = A} {B = B} d e ext A↝◯A ◯B↝B A↝B =
    A    ↝⟨ A↝◯A ⟩
    ◯ A  ↝⟨ ◯-cong-↝-Is-modal→ d e ext A↝B ⟩
    ◯ B  ↝⟨ ◯B↝B ⟩□
    B    □

  ----------------------------------------------------------------------
  -- H-levels

  -- H-level′ n commutes with ◯ (in a certain sense).

  H-level′-◯≃◯-H-level′ :
    ∀ n → H-level′ n (◯ A) ↝[ a ∣ a ] ◯ (H-level′ n A)
  H-level′-◯≃◯-H-level′ {A = A} zero ext =
    Contractible (◯ A)                   ↔⟨⟩
    (∃ λ (x : ◯ A) → ∀ y → x ≡ y)        ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → from-equivalence $
                                             Is-modal→≃◯ (Separated-◯ _ _)) ⟩
    (∃ λ (x : ◯ A) → ∀ y → ◯ (x ≡ y))    ↝⟨ (∃-cong λ _ → Π◯≃◯Π ext) ⟩
    (∃ λ (x : ◯ A) → ◯ (∀ y → x ≡ y))    ↝⟨ (∃-cong λ _ → ◯-cong-↝-Is-modal→ lzero lzero ext λ m →
                                             inverse-ext? λ ext → Π-cong ext (Is-modal→≃◯ m) λ _ → F.id) ⟩
    (∃ λ (x : ◯ A) → ◯ (∀ y → x ≡ η y))  ↔⟨ inverse ◯Ση≃Σ◯◯ ⟩
    ◯ (∃ λ (x : A) → ∀ y → η x ≡ η y)    ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → ∀-cong ext λ _ → from-equivalence $
                                             inverse $ ◯≡≃η≡η left-exact-η-cong) ⟩
    ◯ (∃ λ (x : A) → ∀ y → ◯ (x ≡ y))    ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → Π◯≃◯Π ext) ⟩
    ◯ (∃ λ (x : A) → ◯ (∀ y → x ≡ y))    ↔⟨ ◯Σ◯≃◯Σ ⟩
    ◯ (∃ λ (x : A) → ∀ y → x ≡ y)        ↔⟨⟩
    ◯ (Contractible A)                   □
  H-level′-◯≃◯-H-level′ {A = A} (suc n) ext =
    H-level′ (suc n) (◯ A)                              ↔⟨⟩
    ((x y : ◯ A) → H-level′ n (x ≡ y))                  ↝⟨ Is-modal→↝→↝ lzero lzero ext
                                                             (
      ((x y : ◯ A) → H-level′ n (x ≡ y))                      ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                  inverse-ext?
                                                                    (λ ext →
                                                                       Stable-H-level′ ext n $
                                                                       Separated-◯ _ _)
                                                                    ext) ⟩
      ((x y : ◯ A) → ◯ (H-level′ n (x ≡ y)))                  ↝⟨ (∀-cong ext λ _ → Π◯≃◯Π ext) ⟩
      ((x : ◯ A) → ◯ ((y : ◯ A) → H-level′ n (x ≡ y)))        ↝⟨ Π◯≃◯Π ext ⟩□
      ◯ ((x y : ◯ A) → H-level′ n (x ≡ y))                    □)
                                                             (
      ◯ ((x y : A) → ◯ (H-level′ n (x ≡ y)))                  ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
      ((x : A) → ◯ ((y : A) → ◯ (H-level′ n (x ≡ y))))        ↝⟨ (∀-cong ext λ _ → inverse-ext? Π◯≃◯Π ext) ⟩
      ((x y : A) → ◯ (◯ (H-level′ n (x ≡ y))))                ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → from-equivalence $ inverse ◯≃◯◯) ⟩□
      ((x y : A) → ◯ (H-level′ n (x ≡ y)))                    □)
                                                             (λ (m : Is-modal A) ext →
      ((x y : ◯ A) → H-level′ n (x ≡ y))                        ↝⟨ (Π-cong-contra ext (Is-modal→≃◯ m) λ _ →
                                                                    Π-cong-contra ext (Is-modal→≃◯ m) λ _ →
                                                                    F.id) ⟩
      ((x y : A) → H-level′ n (η x ≡ η y))                      ↝⟨ ((∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                    H-level′-cong ext n $ inverse $
                                                                    ◯≡≃η≡η left-exact-η-cong)) ⟩
      ((x y : A) → H-level′ n (◯ (x ≡ y)))                      ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                    H-level′-◯≃◯-H-level′ n ext) ⟩□
      ((x y : A) → ◯ (H-level′ n (x ≡ y)))                      □) ⟩

    ((x y : A) → ◯ (H-level′ n (x ≡ y)))                ↝⟨ (∀-cong ext λ _ → Π◯≃◯Π ext) ⟩
    ((x : A) → ◯ ((y : A) → H-level′ n (x ≡ y)))        ↝⟨ Π◯≃◯Π ext ⟩
    ◯ ((x y : A) → H-level′ n (x ≡ y))                  ↔⟨⟩
    ◯ (H-level′ (suc n) A)                              □

  -- H-level n commutes with ◯ (in a certain sense).

  H-level-◯≃◯-H-level :
    ∀ n → H-level n (◯ A) ↝[ a ∣ a ] ◯ (H-level n A)
  H-level-◯≃◯-H-level {A = A} n ext =
    H-level n (◯ A)   ↝⟨ H-level↔H-level′ ext ⟩
    H-level′ n (◯ A)  ↝⟨ H-level′-◯≃◯-H-level′ n ext ⟩
    ◯ (H-level′ n A)  ↝⟨ ◯-cong-↝ ext $ inverse-ext? H-level↔H-level′ ⟩□
    ◯ (H-level n A)   □

  -- A variant of Left-exact-η-cong→H-level→H-level-◯ proved using the
  -- assumption that the modality is very modal, instead of function
  -- extensionality and left exactness.

  H-level→H-level-◯ :
    ∀ n → H-level n A → H-level n (◯ A)
  H-level→H-level-◯ {A = A} n =
    H-level n A      →⟨ η ⟩
    ◯ (H-level n A)  →⟨ _⇔_.from (H-level-◯≃◯-H-level n _) ⟩□
    H-level n (◯ A)  □

  ----------------------------------------------------------------------
  -- The modality is left exact

  -- Very modal modalities are left exact.
  --
  -- See also left-exact-η-cong above.

  left-exact : Left-exact ◯
  left-exact {A = A} {x = x} {y = y} =
    Contractible (◯ A)        →⟨ H-level′-◯≃◯-H-level′ 0 _ ⟩
    ◯ (Contractible A)        →⟨ ◯-map $ H-level.⇒≡ 0 ⟩
    ◯ (Contractible (x ≡ y))  →⟨ inverse-ext? (H-level′-◯≃◯-H-level′ 0) _ ⟩□
    Contractible (◯ (x ≡ y))  □

  ----------------------------------------------------------------------
  -- More equivalences

  private

    -- A lemma used to implement ◯→⇔◯→◯.

    ◯→⇔◯→◯-lemma : (◯ A → ◯ B) → (A → Is-modal B) → A → B
    ◯→⇔◯→◯-lemma f m x = Is-modal→Stable (m x) (f (η x))

    -- ◯ commutes with the non-dependent function space (up to _⇔_).

    ◯→⇔◯→◯ : ◯ (A → B) ⇔ (◯ A → ◯ B)
    ◯→⇔◯→◯ {A = A} {B = B} = record
      { to   = ◯-map-◯
      ; from = λ f → ◯-map (◯→⇔◯→◯-lemma f) ◯-Π-Is-modal
      }

    abstract

      -- A lemma related to ◯→⇔◯→◯.

      ◯→⇔◯→◯-◯→⇔◯→◯ :
        (f : ◯ A → ◯ B) →
        _⇔_.to ◯→⇔◯→◯ (_⇔_.from ◯→⇔◯→◯ f) x ≡ f x
      ◯→⇔◯→◯-◯→⇔◯→◯ {x = x} f =
        ◯-elim
          {P = λ m → ◯-map-◯ (◯-map (◯→⇔◯→◯-lemma f) m) x ≡ f x}
          (λ _ → Separated-◯ _ _)
          (λ m →
             ◯-elim
               (λ _ → Separated-◯ _ _)
               (λ x →
                  ◯-map-◯ (◯-map (◯→⇔◯→◯-lemma f) (η m)) (η x)  ≡⟨ cong (flip ◯-map-◯ _) ◯-map-η ⟩

                  ◯-map-◯ (η (◯→⇔◯→◯-lemma f m)) (η x)          ≡⟨ ◯-map-◯-η ⟩

                  η (◯→⇔◯→◯-lemma f m x)                        ≡⟨⟩

                  η (Is-modal→Stable (m x) (f (η x)))           ≡⟨ _≃_.right-inverse-of (Is-modal→≃◯ (m x)) _ ⟩∎

                  f (η x)                                       ∎)
               x)
          ◯-Π-Is-modal

  -- ◯ commutes with the non-dependent function space (assuming
  -- function extensionality).

  ◯→≃◯→◯ : ◯ (A → B) ↝[ a ∣ a ] (◯ A → ◯ B)
  ◯→≃◯→◯ {A = A} {B = B} =
    generalise-ext?
      ◯→⇔◯→◯
      (λ ext →
           (λ f → apply-ext ext λ _ → ◯→⇔◯→◯-◯→⇔◯→◯ f)
         , (◯-elim (λ _ → Separated-◯ _ _) λ f →
              ◯-elim
                {P = λ m → ◯-map (◯→⇔◯→◯-lemma (◯-map-◯ (η f))) m ≡ η f}
                (λ _ → Separated-◯ _ _)
                (λ m →
                   ◯-map (◯→⇔◯→◯-lemma (◯-map-◯ (η f))) (η m)             ≡⟨ ◯-map-η ⟩
                   η (◯→⇔◯→◯-lemma (◯-map-◯ (η f)) m)                     ≡⟨⟩
                   η (λ x → Is-modal→Stable (m x) (◯-map-◯ (η f) (η x)))  ≡⟨ (cong η $ apply-ext ext λ x → cong (Is-modal→Stable (m x))
                                                                              ◯-map-◯-η) ⟩
                   η (λ x → Is-modal→Stable (m x) (η (f x)))              ≡⟨ (cong η $ apply-ext ext λ x →
                                                                              _≃_.left-inverse-of (Is-modal→≃◯ (m x)) _) ⟩∎
                   η f                                                    ∎)
                ◯-Π-Is-modal))

  -- ◯ commutes with _⇔_ (assuming function extensionality).

  ◯⇔≃◯⇔◯ : ◯ (A ⇔ B) ↝[ a ∣ a ] (◯ A ⇔ ◯ B)
  ◯⇔≃◯⇔◯ {A = A} {B = B} ext =
    ◯ (A ⇔ B)                  ↔⟨ ◯-cong-↔ ⇔↔→×→ ⟩
    ◯ ((A → B) × (B → A))      ↔⟨ ◯×≃ ⟩
    ◯ (A → B) × ◯ (B → A)      ↝⟨ ◯→≃◯→◯ ext ×-cong ◯→≃◯→◯ ext ⟩
    (◯ A → ◯ B) × (◯ B → ◯ A)  ↔⟨ inverse ⇔↔→×→ ⟩□
    ◯ A ⇔ ◯ B                  □

  -- A lemma that is easy to prove, but relies on function
  -- extensionality.

  _ :
    Extensionality a a →
    Σ (◯ (A → B)) (P ∘ ◯-map-◯) ↝[ k ] Σ (◯ A → ◯ B) P
  _ = λ ext → Σ-cong (◯→≃◯→◯ {k = equivalence} ext) λ _ → F.id

  -- A variant of the lemma above that only relies on conditional
  -- function extensionality.

  Σ-cong-◯→≃◯→◯ :
    (P-resp : {f g : ◯ A → ◯ B} → (∀ x → f x ≡ g x) → P f → P g) →
    (∀ {f x} → Extensionality a a → P-resp (refl ∘ f) x ≡ x) →
    Σ (◯ (A → B)) (P ∘ ◯-map-◯) ↝[ a ∣ a ] Σ (◯ A → ◯ B) P
  Σ-cong-◯→≃◯→◯ {P = P} P-resp P-resp-refl = generalise-ext?
    (record { to = to; from = from })
    (λ ext →
       let ext′ = Eq.good-ext ext in
         (λ (f , p) → Σ-≡,≡→≡
            (apply-ext ext′ $ eq′ f)
            (lemma ext f p))
       , (λ (f , p) → Σ-≡,≡→≡
            (_≃_.left-inverse-of (◯→≃◯→◯ ext′) f)
            (subst (P ∘ ◯-map-◯)
               (_≃_.left-inverse-of (◯→≃◯→◯ ext′) f)
               (P-resp (sym ∘ eq′ (◯-map-◯ f)) p)                    ≡⟨ subst-∘ _ _ _ ⟩

             subst P
               (cong ◯-map-◯ $ _≃_.left-inverse-of (◯→≃◯→◯ ext′) f)
               (P-resp (sym ∘ eq′ (◯-map-◯ f)) p)                    ≡⟨ cong (flip (subst P) _) $
                                                                        _≃_.left-right-lemma (◯→≃◯→◯ ext′) _ ⟩
             subst P
               (_≃_.right-inverse-of (◯→≃◯→◯ ext′) (◯-map-◯ f))
               (P-resp (sym ∘ eq′ (◯-map-◯ f)) p)                    ≡⟨ lemma ext _ _ ⟩∎

             p                                                       ∎)))
    where
    eq′ = λ f x → ◯→⇔◯→◯-◯→⇔◯→◯ {x = x} f

    to   = Σ-map (_⇔_.to   ◯→⇔◯→◯) id
    from = Σ-map (_⇔_.from ◯→⇔◯→◯) λ {f} →
      P f                                    →⟨ (P-resp λ _ → sym $ ◯→⇔◯→◯-◯→⇔◯→◯ f) ⟩□
      P (_⇔_.to ◯→⇔◯→◯ (_⇔_.from ◯→⇔◯→◯ f))  □

    lemma = λ ext f p →
      let eq = apply-ext (Eq.good-ext ext) (eq′ f) in

      subst P eq (P-resp (sym ∘ eq′ f) p)                   ≡⟨ cong (λ eq′ → subst P eq (P-resp (sym ∘ eq′) p)) $ sym $
                                                               _≃_.left-inverse-of (Eq.extensionality-isomorphism ext) _ ⟩

      subst P eq (P-resp (sym ∘ ext⁻¹ eq) p)                ≡⟨ elim₁
                                                                 (λ eq → subst P eq (P-resp (sym ∘ ext⁻¹ eq) p) ≡ p)
                                                                 (
        subst P (refl _) (P-resp (sym ∘ ext⁻¹ (refl _)) p)        ≡⟨ subst-refl _ _ ⟩

        P-resp (sym ∘ ext⁻¹ (refl f)) p                           ≡⟨ (cong (λ q → P-resp (sym ∘ q) p) $ apply-ext ext λ _ →
                                                                      ext⁻¹-refl _) ⟩

        P-resp (sym ∘ refl ∘ f) p                                 ≡⟨ (cong (λ q → P-resp q p) $ apply-ext ext λ _ →
                                                                      sym-refl) ⟩

        P-resp (refl ∘ f) p                                       ≡⟨ P-resp-refl ext ⟩∎

        p                                                         ∎)
                                                                 _ ⟩∎
      p                                                     ∎

  -- A variant of Stable-Σ.

  Stable-Σ[◯→◯] :
    Extensionality? k a a →
    (P-resp : {f g : ◯ A → ◯ B} → (∀ x → f x ≡ g x) → P f → P g) →
    (∀ {f x} → Extensionality a a → P-resp (refl ∘ f) x ≡ x) →
    (∀ f → Stable-[ k ] (P f)) →
    Stable-[ k ] (Σ (◯ A → ◯ B) P)
  Stable-Σ[◯→◯] {A = A} {B = B} {P = P} ext P-resp P-resp-refl s =
    ◯ (Σ (◯ A → ◯ B) P)              ↝⟨ ◯-cong-↝ ext $ inverse-ext? (Σ-cong-◯→≃◯→◯ P-resp P-resp-refl) ⟩
    ◯ (Σ (◯ (A → B)) (P ∘ ◯-map-◯))  ↝⟨ Stable-Σ Is-modal-◯ (s ∘ ◯-map-◯) ⟩
    Σ (◯ (A → B)) (P ∘ ◯-map-◯)      ↝⟨ Σ-cong-◯→≃◯→◯ P-resp P-resp-refl ext ⟩□
    Σ (◯ A → ◯ B) P                  □

  -- A lemma that can be used to prove that ◯ (F A B) is equivalent to
  -- F (◯ A) (◯ B).

  ◯↝↝◯↝◯ :
    {F : Type a → Type a → Type a}
    {P : {A B : Type a} → (A → B) → Type a} →
    (∀ {A B} → F A B ↔ (∃ λ (f : A → B) → P f)) →
    ({f : A → B} → ◯ (P f) ↝[ a ∣ a ] P (◯-map f)) →
    (P-cong :
       ∀ {k} {f g : ◯ A → ◯ B} →
       Extensionality? k a a → (∀ x → f x ≡ g x) → P f ↝[ k ] P g) →
    (∀ {f x} →
     Extensionality a a →
     P-cong {k = implication} _ (refl ∘ f) x ≡ x) →
    ({f : ◯ A → ◯ B} → Stable-[ k ] (P f)) →
    Extensionality? k a a →
    ◯ (F A B) ↝[ k ] F (◯ A) (◯ B)
  ◯↝↝◯↝◯ {A = A} {B = B} {F = F} {P = P}
    F↔ ◯∘P↝P∘◯-map P-cong P-cong-refl P-stable ext =
    ◯ (F A B)                                  ↔⟨ ◯-cong-↔ F↔ ⟩
    ◯ (∃ λ (f : A → B) → P f)                  ↔⟨ inverse ◯Σ◯≃◯Σ ⟩
    ◯ (∃ λ (f : A → B) → ◯ (P f))              ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → ◯∘P↝P∘◯-map ext) ⟩
    ◯ (∃ λ (f : A → B) → P (◯-map f))          ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → P-cong ext λ _ → sym ◯-map-◯-ηˡ) ⟩
    ◯ (∃ λ (f : A → B) → P (◯-map-◯ (η f)))    ↔⟨ ◯Ση≃Σ◯◯ ⟩
    (∃ λ (f : ◯ (A → B)) → ◯ (P (◯-map-◯ f)))  ↝⟨ (∃-cong λ _ → P-stable) ⟩
    (∃ λ (f : ◯ (A → B)) → P (◯-map-◯ f))      ↝⟨ Σ-cong-◯→≃◯→◯ (P-cong _) P-cong-refl ext ⟩
    (∃ λ (f : ◯ A → ◯ B) → P f)                ↔⟨ inverse F↔ ⟩□
    F (◯ A) (◯ B)                              □

  private

    -- An example of how ◯↝↝◯↝◯ can be used.

    ◯⇔≃◯⇔◯′ : ◯ (A ⇔ B) ↝[ a ∣ a ] (◯ A ⇔ ◯ B)
    ◯⇔≃◯⇔◯′ ext =
      ◯↝↝◯↝◯
        ⇔↔→×→
        ◯→≃◯→◯
        (λ _ _ → F.id)
        (λ _ → refl _)
        (Stable-Π ext λ _ → Is-modal→Stable Is-modal-◯)
        ext

  -- ◯ (Split-surjective f) is equivalent to
  -- Split-surjective (◯-map f) (assuming function extensionality).

  ◯-Split-surjective≃Split-surjective :
    ◯ (Split-surjective f) ↝[ a ∣ a ] Split-surjective (◯-map f)
  ◯-Split-surjective≃Split-surjective {f = f} {k = k} ext =
    ◯ (∀ y → ∃ λ x → f x ≡ y)              ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
    (∀ y → ◯ (∃ λ x → f x ≡ y))            ↝⟨ (∀-cong′ λ _ → inverse ◯Σ◯≃◯Σ) ⟩
    (∀ y → ◯ (∃ λ x → ◯ (f x ≡ y)))        ↝⟨ (∀-cong′ λ _ → ◯-cong-≃ $ ∃-cong λ _ → ◯≡≃η≡η left-exact-η-cong) ⟩
    (∀ y → ◯ (∃ λ x → η (f x) ≡ η y))      ↝⟨ inverse-ext? Π◯◯≃Π◯η ext ⟩
    (∀ y → ◯ (∃ λ x → η (f x) ≡ y))        ↝⟨ (∀-cong′ λ _ → ◯-cong-≃ $ ∃-cong λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym ◯-map-η) ⟩
    (∀ y → ◯ (∃ λ x → ◯-map f (η x) ≡ y))  ↝⟨ (∀-cong′ λ _ → ◯Ση≃Σ◯◯) ⟩
    (∀ y → ∃ λ x → ◯ (◯-map f x ≡ y))      ↝⟨ (∀-cong′ λ _ → ∃-cong λ _ → Is-modal→Stable (Separated-◯ _ _)) ⟩□
    (∀ y → ∃ λ x → ◯-map f x ≡ y)          □
    where
    ∀-cong′ :
      {A : Type a} {P Q : A → Type a} →
      (∀ x → P x ≃ Q x) → ((x : A) → P x) ↝[ k ] ((x : A) → Q x)
    ∀-cong′ = ∀-cong ext ∘ (from-equivalence ∘_)

  -- ◯ commutes with _↠_ (assuming function extensionality).

  ◯↠≃◯↠◯ : ◯ (A ↠ B) ↝[ a ∣ a ] (◯ A ↠ ◯ B)
  ◯↠≃◯↠◯ ext =
    ◯↝↝◯↝◯
      ↠↔∃-Split-surjective
      ◯-Split-surjective≃Split-surjective
      Split-surjective-cong
      Split-surjective-cong-refl
      (Stable-Π ext λ _ → Is-modal→Stable $
       Is-modal-Σ Is-modal-◯ λ _ → Separated-◯ _ _)
      ext

  -- ◯ (Is-equivalence f) is equivalent to Is-equivalence (◯-map f)
  -- (assuming function extensionality).

  ◯-Is-equivalence≃Is-equivalence :
    ◯ (Is-equivalence f) ↝[ a ∣ a ] Is-equivalence (◯-map f)
  ◯-Is-equivalence≃Is-equivalence {f = f} ext =
    ◯ (Is-equivalence f)                           ↝⟨ ◯-cong-↝ ext Is-equivalence≃Is-equivalence-CP ⟩
    ◯ (∀ y → Contractible (f ⁻¹ y))                ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
    (∀ y → ◯ (Contractible (f ⁻¹ y)))              ↝⟨ Is-modal→↝→↝ lzero lzero ext
                                                        (
      (∀ x → ◯ (Contractible (f ⁻¹ x)))                  ↝⟨ inverse-ext?
                                                              (λ ext →
                                                                 Stable-Π ext λ _ →
                                                                 Is-modal→Stable Is-modal-◯)
                                                              ext ⟩
      ◯ (∀ x → ◯ (Contractible (f ⁻¹ x)))                □)
                                                        (
      ◯ (∀ x → Contractible (◯ (η ∘ f ⁻¹ x)))            ↝⟨ (Stable-Π ext λ _ →
                                                             Stable-H-level′ ext 0 Is-modal-◯) ⟩□
      (∀ x → Contractible (◯ (η ∘ f ⁻¹ x)))              □)
                                                        (λ m ext →
                                                           Π-cong-contra ext (inverse $ Is-modal→≃◯ m) λ x →
      ◯ (Contractible (f ⁻¹ Is-modal→Stable m x))            ↝⟨ inverse-ext? (H-level′-◯≃◯-H-level′ 0) ext ⟩
      Contractible (◯ (f ⁻¹ Is-modal→Stable m x))            ↝⟨ H-level-cong ext 0 $ ◯-cong-≃ $ inverse $
                                                                to-∘-⁻¹-≃-⁻¹-from (Is-modal→≃◯ m) ⟩□
      Contractible (◯ (η ∘ f ⁻¹ x))                          □) ⟩

    (∀ y → Contractible (◯ (η ∘ f ⁻¹ y)))          ↔⟨⟩
    ◯ -Connected-→ (η ∘ f)                         ↝⟨ Connected-→-η-∘-≃Is-equivalence-◯-map ext ⟩□
    Is-equivalence (◯-map f)                       □

  -- A function f is ◯-connected if and only if ◯ (Is-equivalence f)
  -- holds.

  Connected-→≃◯-Is-equivalence :
    ◯ -Connected-→ f ↝[ a ∣ a ] ◯ (Is-equivalence f)
  Connected-→≃◯-Is-equivalence {f = f} ext =
    ◯ -Connected-→ f          ↝⟨ Left-exact→Connected-→≃Is-equivalence-◯-map left-exact ext ⟩
    Is-equivalence (◯-map f)  ↝⟨ inverse-ext? ◯-Is-equivalence≃Is-equivalence ext ⟩□
    ◯ (Is-equivalence f)      □

  -- ◯ commutes with _≃_ (assuming function extensionality).

  ◯≃≃◯≃◯ : ◯ (A ≃ B) ↝[ a ∣ a ] (◯ A ≃ ◯ B)
  ◯≃≃◯≃◯ ext =
    ◯↝↝◯↝◯
      Eq.≃-as-Σ
      ◯-Is-equivalence≃Is-equivalence
      Is-equivalence-cong
      (λ ext → Eq.propositional ext _ _ _)
      (Is-modal→Stable-Is-equivalence ext Is-modal-◯ Is-modal-◯)
      ext

  private

    -- Some definitions used in the implementations of
    -- ◯-Has-quasi-inverse≃Has-quasi-inverse and ◯↔≃◯↔◯.

    Has-quasi-inverse-proofs :
      (◯ A → ◯ B) → (◯ B → ◯ A) → Type a
    Has-quasi-inverse-proofs f f⁻¹ =
      (∀ x → f (f⁻¹ x) ≡ x) × (∀ x → f⁻¹ (f x) ≡ x)

    Has-quasi-inverse-proofs-resp :
      (∀ x → g x ≡ h x) →
      Has-quasi-inverse-proofs f g →
      Has-quasi-inverse-proofs f h
    Has-quasi-inverse-proofs-resp {f = f} g≡h =
      Σ-map (trans (cong f $ sym $ g≡h _) ∘_)
            (trans (sym $ g≡h _) ∘_)

    Has-quasi-inverse-proofs-resp-refl :
      Extensionality a a →
      Has-quasi-inverse-proofs-resp (refl ∘ f) p ≡ p
    Has-quasi-inverse-proofs-resp-refl {p = p , q} ext =
      ( trans (cong _ $ sym $ refl _) ∘ p
      , trans (sym $ refl _) ∘ q
      )                                    ≡⟨ cong₂ _,_
                                                (apply-ext ext λ _ →
                                                 trans (cong (flip trans _) $
                                                        trans (cong (cong _) sym-refl) $
                                                        cong-refl _) $
                                                 trans-reflˡ _)
                                                (apply-ext ext λ _ →
                                                 trans (cong (flip trans _)
                                                        sym-refl) $
                                                 trans-reflˡ _) ⟩∎
      (p , q)                              ∎

  -- ◯ (Has-quasi-inverse f) is equivalent to
  -- Has-quasi-inverse (◯-map f) (assuming function extensionality).

  ◯-Has-quasi-inverse≃Has-quasi-inverse :
    ◯ (Has-quasi-inverse f) ↝[ a ∣ a ] Has-quasi-inverse (◯-map f)
  ◯-Has-quasi-inverse≃Has-quasi-inverse {f = f} ext =
    ◯ (∃ λ g → (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x))              ↔⟨ inverse ◯Σ◯≃◯Σ ⟩

    ◯ (∃ λ g → ◯ ((∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x)))          ↔⟨ (◯-cong-≃ $ ∃-cong λ _ → ◯×≃) ⟩

    ◯ (∃ λ g → ◯ (∀ x → f (g x) ≡ x) × ◯ (∀ x → g (f x) ≡ x))          ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ →
                                                                           inverse-ext? (λ ext → Π◯≃◯Π ext ×-cong Π◯≃◯Π ext) ext) ⟩

    ◯ (∃ λ g → (∀ x → ◯ (f (g x) ≡ x)) × (∀ x → ◯ (g (f x) ≡ x)))      ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ →
                                                                           (∀-cong ext λ _ → from-equivalence $ ◯≡≃η≡η left-exact-η-cong)
                                                                             ×-cong
                                                                           (∀-cong ext λ _ → from-equivalence $ ◯≡≃η≡η left-exact-η-cong)) ⟩

    ◯ (∃ λ g → (∀ x → η (f (g x)) ≡ η x) × (∀ x → η (g (f x)) ≡ η x))  ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ →
                                                                           (∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                            trans (cong (◯-map f) ◯-map-◯-η) ◯-map-η)
                                                                             ×-cong
                                                                           (∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                            ◯-map-◯-η)) ⟩
    ◯ (∃ λ g → (∀ x → ◯-map f (◯-map-◯ (η g) (η x)) ≡ η x) ×
               (∀ x → ◯-map-◯ (η g) (η (f x)) ≡ η x))                  ↔⟨ ◯Ση≃Σ◯◯ ⟩

    (∃ λ g → ◯ ((∀ x → ◯-map f (◯-map-◯ g (η x)) ≡ η x) ×
                (∀ x → ◯-map-◯ g (η (f x)) ≡ η x)))                    ↔⟨ (∃-cong λ _ → ◯×≃) ⟩

    (∃ λ g → ◯ (∀ x → ◯-map f (◯-map-◯ g (η x)) ≡ η x) ×
             ◯ (∀ x → ◯-map-◯ g (η (f x)) ≡ η x))                      ↝⟨ inverse-ext?
                                                                            (λ ext → ∃-cong λ _ → Π◯≃◯Π ext ×-cong Π◯≃◯Π ext)
                                                                            ext ⟩
    (∃ λ g → (∀ x → ◯ (◯-map f (◯-map-◯ g (η x)) ≡ η x)) ×
             (∀ x → ◯ (◯-map-◯ g (η (f x)) ≡ η x)))                    ↝⟨ (∃-cong λ g → ∃-cong λ _ → ∀-cong ext λ _ → ◯-cong-↝ ext λ _ →
                                                                           ≡⇒↝ _ $ cong ((_≡ _) ∘ ◯-map-◯ g) $ sym ◯-map-η) ⟩
    (∃ λ g → (∀ x → ◯ (◯-map f (◯-map-◯ g (η x)) ≡ η x)) ×
             (∀ x → ◯ (◯-map-◯ g (◯-map f (η x)) ≡ η x)))              ↝⟨ (∃-cong λ _ →
                                                                           inverse-ext? (λ ext → Π◯◯≃Π◯η ext ×-cong Π◯◯≃Π◯η ext) ext) ⟩
    (∃ λ g → (∀ x → ◯ (◯-map f (◯-map-◯ g x) ≡ x)) ×
             (∀ x → ◯ (◯-map-◯ g (◯-map f x) ≡ x)))                    ↝⟨ (∃-cong λ _ →
                                                                           (∀-cong ext λ _ → Is-modal→Stable (Separated-◯ _ _))
                                                                             ×-cong
                                                                           (∀-cong ext λ _ → Is-modal→Stable (Separated-◯ _ _))) ⟩
    (∃ λ g → (∀ x → ◯-map f (◯-map-◯ g x) ≡ x) ×
             (∀ x → ◯-map-◯ g (◯-map f x) ≡ x))                        ↝⟨ Σ-cong-◯→≃◯→◯
                                                                            Has-quasi-inverse-proofs-resp
                                                                            Has-quasi-inverse-proofs-resp-refl
                                                                            ext ⟩□
    (∃ λ g → (∀ x → ◯-map f (g x) ≡ x) × (∀ x → g (◯-map f x) ≡ x))    □

  -- ◯ commutes with _↔_ (assuming function extensionality).

  ◯↔≃◯↔◯ : ◯ (A ↔ B) ↝[ a ∣ a ] (◯ A ↔ ◯ B)
  ◯↔≃◯↔◯ ext =
    ◯↝↝◯↝◯
      Bijection.↔-as-Σ
      ◯-Has-quasi-inverse≃Has-quasi-inverse
      Has-quasi-inverse-cong
      Has-quasi-inverse-cong-refl
      (Stable-Σ[◯→◯] ext
         Has-quasi-inverse-proofs-resp
         Has-quasi-inverse-proofs-resp-refl λ _ →
       Stable-×
         (Stable-Π ext λ _ →
          Is-modal→Stable (Is-modal→Separated Is-modal-◯ _ _))
         (Stable-Π ext λ _ →
          Is-modal→Stable (Is-modal→Separated Is-modal-◯ _ _)))
      ext

  -- ◯ (Injective f) is equivalent to Injective (◯-map f) (assuming
  -- function extensionality).

  ◯-Injective≃Injective :
    ◯ (Injective f) ↝[ a ∣ a ] Injective (◯-map f)
  ◯-Injective≃Injective {f = f} ext =
    ◯ (∀ {x y} → f x ≡ f y → x ≡ y)                      ↔⟨ ◯-cong-≃ $ inverse lemma ⟩
    ◯ (∀ x y → f x ≡ f y → x ≡ y)                        ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
    (∀ x → ◯ (∀ y → f x ≡ f y → x ≡ y))                  ↝⟨ (∀-cong ext λ _ → inverse-ext? Π◯≃◯Π ext) ⟩
    (∀ x y → ◯ (f x ≡ f y → x ≡ y))                      ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ◯→≃◯→◯ ext) ⟩
    (∀ x y → ◯ (f x ≡ f y) → ◯ (x ≡ y))                  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → →-cong₁ ext $
                                                             ◯≡≃η≡η left-exact-η-cong) ⟩
    (∀ x y → η (f x) ≡ η (f y) → ◯ (x ≡ y))              ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                             from-equivalence $ ◯≡≃η≡η left-exact-η-cong) ⟩
    (∀ x y → η (f x) ≡ η (f y) → η x ≡ η y)              ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → →-cong₁ ext $
                                                             ≡⇒↝ equivalence $ sym $ cong₂ _≡_ ◯-map-η ◯-map-η) ⟩
    (∀ x y → ◯-map f (η x) ≡ ◯-map f (η y) → η x ≡ η y)  ↝⟨ (∀-cong ext λ _ → inverse-ext? (Π◯↝Πη s) ext) ⟩
    (∀ x y → ◯-map f (η x) ≡ ◯-map f y → η x ≡ y)        ↝⟨ inverse-ext? (Π◯↝Πη λ ext _ → Stable-Π ext (s ext)) ext ⟩
    (∀ x y → ◯-map f x ≡ ◯-map f y → x ≡ y)              ↔⟨ lemma ⟩□
    (∀ {x y} → ◯-map f x ≡ ◯-map f y → x ≡ y)            □
    where
    lemma :
      {P : A → B → Type p} →
      (∀ x y → P x y) ≃ (∀ {x y} → P x y)
    lemma = Eq.↔→≃ (λ f → f _ _) (λ f _ _ → f) refl refl

    s :
      Extensionality? k a a →
      ∀ y → Stable-[ k ] (◯-map f x ≡ ◯-map f y → x ≡ y)
    s ext _ = Stable-Π ext λ _ → Is-modal→Stable $ Separated-◯ _ _

  -- ◯ commutes with _↣_ (assuming function extensionality).

  ◯↣≃◯↣◯ : ◯ (A ↣ B) ↝[ a ∣ a ] (◯ A ↣ ◯ B)
  ◯↣≃◯↣◯ ext =
    ◯↝↝◯↝◯
      ↣↔∃-Injective
      ◯-Injective≃Injective
      Injective-cong
      Injective-cong-refl
      (Stable-implicit-Π ext λ _ →
       Stable-implicit-Π ext λ _ →
       Stable-Π          ext λ _ →
       Is-modal→Stable $ Separated-◯ _ _)
      ext

  -- ◯ (Is-embedding f) is equivalent to Is-embedding (◯-map f)
  -- (assuming function extensionality).

  ◯-Is-embedding≃Is-embedding :
    ◯ (Is-embedding f) ↝[ a ∣ a ] Is-embedding (◯-map f)
  ◯-Is-embedding≃Is-embedding {f = f} ext =
    ◯ (∀ x y → Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y)))             ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩

    (∀ x → ◯ (∀ y → Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y))))       ↝⟨ (∀-cong ext λ _ → inverse-ext? Π◯≃◯Π ext) ⟩

    (∀ x y → ◯ (Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y))))           ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              ◯-Is-equivalence≃Is-equivalence ext) ⟩

    (∀ x y → Is-equivalence (◯-map (cong f ⦂ (x ≡ y → f x ≡ f y))))       ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Is-equivalence-cong ext $
                                                                              ◯-map-cong≡ left-exact-η-cong) ⟩
    (∀ x y →
       Is-equivalence
         (η-cong⁻¹ left-exact-η-cong ∘
          _≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
          cong (◯-map f) ∘ η-cong ⦂ (◯ (x ≡ y) → ◯ (f x ≡ f y))))         ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              inverse-ext?
                                                                                (Is-equivalence≃Is-equivalence-∘ˡ
                                                                                   (_≃_.is-equivalence $ inverse $ ◯≡≃η≡η left-exact-η-cong))
                                                                                ext) ⟩
    (∀ x y →
       Is-equivalence
         (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
          cong (◯-map f) ∘ η-cong ⦂ (◯ (x ≡ y) → η (f x) ≡ η (f y))))     ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              inverse-ext?
                                                                                (Is-equivalence≃Is-equivalence-∘ʳ left-exact-η-cong)
                                                                                ext) ⟩
    (∀ x y →
       Is-equivalence
         (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
          cong (◯-map f) ⦂ (η x ≡ η y → η (f x) ≡ η (f y))))              ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              inverse-ext?
                                                                                (Is-equivalence≃Is-equivalence-∘ˡ
                                                                                   (_≃_.is-equivalence $ ≡⇒↝ _ _))
                                                                                ext) ⟩
    (∀ x y →
       Is-equivalence
         (cong (◯-map f) ⦂ (η x ≡ η y → ◯-map f (η x) ≡ ◯-map f (η y))))  ↝⟨ inverse-ext?
                                                                               (Π◯↝Πη λ ext _ →
                                                                                Stable-Π ext λ _ →
                                                                                Is-modal→Stable-Is-equivalence ext
                                                                                  (Separated-◯ _ _) (Separated-◯ _ _))
                                                                               ext ⟩
    (∀ x y →
       Is-equivalence
         (cong (◯-map f) ⦂ (x ≡ η y → ◯-map f x ≡ ◯-map f (η y))))        ↝⟨ (∀-cong ext λ _ →
                                                                              inverse-ext?
                                                                                (Π◯↝Πη λ ext _ →
                                                                                 Is-modal→Stable-Is-equivalence ext
                                                                                   (Separated-◯ _ _) (Separated-◯ _ _))
                                                                                ext) ⟩□
    (∀ x y →
       Is-equivalence
         (cong (◯-map f) ⦂ (x ≡ y → ◯-map f x ≡ ◯-map f y)))              □

  -- ◯ commutes with Embedding (assuming function extensionality).

  ◯-Embedding≃Embedding-◯-◯ :
    ◯ (Embedding A B) ↝[ a ∣ a ] Embedding (◯ A) (◯ B)
  ◯-Embedding≃Embedding-◯-◯ ext =
    ◯↝↝◯↝◯
      Emb.Embedding-as-Σ
      ◯-Is-embedding≃Is-embedding
      Is-embedding-cong
      (λ ext → Emb.Is-embedding-propositional ext _ _)
      (Stable-Π ext λ _ → Stable-Π ext λ _ →
       Is-modal→Stable-Is-equivalence ext
         (Separated-◯ _ _) (Separated-◯ _ _))
      ext

------------------------------------------------------------------------
-- Another lemma

-- Very-modal M is propositional (assuming function extensionality).

Very-modal-propositional :
  {M : Modality a} →
  Extensionality (lsuc a) a →
  Is-proposition (Very-modal M)
Very-modal-propositional {M = M} ext =
  [inhabited⇒+]⇒+ {A = Very-modal M} 0 λ very-modal →
  let open Very-modal M very-modal in
  implicit-Π-closure ext 1 λ _ →
  H-level→H-level-◯ 1 $
  Is-modal-propositional ext′
  where
  open Modality M

  ext′ = lower-extensionality _ lzero ext
