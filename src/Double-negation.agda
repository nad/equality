------------------------------------------------------------------------
-- The double-negation monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Double-negation
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude

import Accessibility eq as A
open import Bijection eq as B using (_↔_)
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Equivalence.Path-split eq as PS
  using (Is-∞-extendable-along-[_])
open import Erased.Level-1 eq as E using (Erased)
open import Excluded-middle eq
open import Extensionality eq
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import Modality.Basics eq
open import Monad eq

-- The double-negation monad, defined using a wrapper type to make
-- instance resolution easier.

infix 3 ¬¬_

record ¬¬_ {a} (A : Type a) : Type a where
  constructor wrap
  field
    run : ¬ ¬ A

open ¬¬_ public

-- ¬¬ A is a proposition (assuming extensionality).

¬¬-propositional :
  ∀ {a} {A : Type a} →
  Extensionality a lzero →
  Is-proposition (¬¬ A)
¬¬-propositional ext _ _ =
  cong wrap $ ¬-propositional ext _ _

-- An extra universe-polymorphic variant of map.

map′ :
  ∀ {a b} {@0 A : Type a} {@0 B : Type b} →
  (A → B) → ¬¬ A → ¬¬ B
run (map′ f ¬¬a) = λ ¬b → run ¬¬a (λ a → ¬b (f a))

-- A variant of bind with extra universe-polymorphism (and some erased
-- arguments).

infixl 5 _>>=′_

_>>=′_ :
  ∀ {a b} {@0 A : Type a} {@0 B : Type b} →
  ¬¬ A → (A → ¬¬ B) → ¬¬ B
run (x >>=′ f) = join (map′ (run ∘ f) x)
  where
  join : ∀ {a} {@0 A : Type a} → ¬¬ ¬ A → ¬ A
  join ¬¬¬a = λ a → run ¬¬¬a (λ ¬a → ¬a a)

-- Instances.

instance

  double-negation-monad : ∀ {ℓ} → Raw-monad (λ (A : Type ℓ) → ¬¬ A)
  Raw-monad.return double-negation-monad x .run = _$ x
  Raw-monad._>>=_  double-negation-monad        = _>>=′_

monad : ∀ {ℓ} →
        Extensionality ℓ lzero →
        Monad (λ (A : Type ℓ) → ¬¬ A)
Monad.raw-monad      (monad _)         = double-negation-monad
Monad.left-identity  (monad ext) _ _   = ¬¬-propositional ext _ _
Monad.right-identity (monad ext) _     = ¬¬-propositional ext _ _
Monad.associativity  (monad ext) _ _ _ = ¬¬-propositional ext _ _

-- The following variant of excluded middle is provable.

excluded-middle : ∀ {a} {@0 A : Type a} → ¬¬ Dec A
run excluded-middle ¬[a⊎¬a] = ¬[a⊎¬a] (no λ a → ¬[a⊎¬a] (yes a))

-- The following variant of Peirce's law is provable.

call/cc : ∀ {a w} {@0 A : Type a} {Whatever : Type w} →
          ((A → Whatever) → ¬¬ A) → ¬¬ A
run (call/cc hyp) ¬a = run (hyp (λ a → ⊥-elim (¬a a))) ¬a

-- If one can prove that the empty type is inhabited in the
-- double-negation monad, then the empty type is inhabited.

¬¬¬⊥ : ∀ {ℓ} → ¬ (¬¬ (⊥ {ℓ = ℓ}))
¬¬¬⊥ ¬¬⊥ = run ¬¬⊥ ⊥-elim

-- If the double-negation of a negation can be proved, then the
-- negation itself can be proved.

¬¬¬→¬ : ∀ {a} {A : Type a} → ¬¬ ¬ A → ¬ A
¬¬¬→¬ ¬¬¬a = λ a → ¬¬¬⊥ (¬¬¬a >>= λ ¬a → ⊥-elim (¬a a))

------------------------------------------------------------------------
-- Excluded middle and double-negation elimination

-- Double-negation elimination (roughly as stated in the HoTT book).

Double-negation-elimination : (ℓ : Level) → Type (lsuc ℓ)
Double-negation-elimination p =
  {P : Type p} → Is-proposition P → ¬¬ P → P

-- Double-negation elimination is propositional (assuming
-- extensionality).

Double-negation-elimination-propositional :
  ∀ {ℓ} →
  Extensionality (lsuc ℓ) ℓ →
  Is-proposition (Double-negation-elimination ℓ)
Double-negation-elimination-propositional ext =
  implicit-Π-closure ext 1 λ _ →
  Π-closure (lower-extensionality _ lzero ext) 1 λ P-prop →
  Π-closure (lower-extensionality _ lzero ext) 1 λ _ →
  P-prop

-- In the presence of double-negation elimination ¬¬ A is equivalent
-- to A for propositions A (assuming extensionality).

¬¬≃ :
  ∀ {a} {A : Type a} →
  Is-proposition A →
  Double-negation-elimination a →
  (¬¬ A) ↝[ a ∣ lzero ] A
¬¬≃ prop dne =
  generalise-ext?-prop
    (record { to = dne prop; from = return })
    ¬¬-propositional
    (λ _ → prop)

-- Excluded middle implies double-negation elimination.

Excluded-middle→Double-negation-elimination :
  ∀ {ℓ} → Excluded-middle ℓ → Double-negation-elimination ℓ
Excluded-middle→Double-negation-elimination em P-prop ¬¬p =
  [ id , ⊥-elim ∘ run ¬¬p ] (em P-prop)

-- Excluded middle is pointwise equivalent to double-negation
-- elimination (assuming extensionality).

Excluded-middle≃Double-negation-elimination :
  ∀ {ℓ} →
  Extensionality (lsuc ℓ) (lsuc ℓ) →
  Excluded-middle ℓ ≃ Double-negation-elimination ℓ
Excluded-middle≃Double-negation-elimination ext =
  _↔_.to (Eq.⇔↔≃
            ext
            (Excluded-middle-propositional
               (lower-extensionality lzero _ ext))
            (Double-negation-elimination-propositional
               (lower-extensionality lzero _ ext)))
    (record
       { to   = Excluded-middle→Double-negation-elimination
       ; from = λ dne P-prop →
                  dne (Dec-closure-propositional
                         (lower-extensionality _ _ ext) P-prop)
                      excluded-middle
       })

------------------------------------------------------------------------
-- The double-negation modality

-- The double-negation monad is a modality (assuming extensionality).
--
-- This fact is taken from "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters, but the proof might be different.

¬¬-modality : ∀ {ℓ} → Extensionality ℓ ℓ → Modality ℓ
¬¬-modality {ℓ = ℓ} ext = λ where
    .◯ → ¬¬_

    .η → return

    .Modal → ¬¬-modal

    .Modal-propositional ext →
      Σ-closure 1 (H-level-propositional ext 1) λ prop →
      Π-closure ext 1 λ _ →
      prop

    .Modal-◯ → ¬¬-propositional ext₀ , _>>= id

    .Modal-respects-≃ {A = A} {B = B} A≃B →
      Σ-map
        (H-level-cong _ 1 A≃B)
        ((¬¬ A → A)  →⟨ (_≃_.to A≃B ∘_) ∘ (_∘ map (_≃_.from A≃B)) ⟩□
         (¬¬ B → B)  □)

    .extendable-along-η {A = A} {P = P} →
      (∀ x → ¬¬-modal (P x))              →⟨ lemma ⟩
      Is-equivalence (_∘ return)          ↔⟨ inverse $ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩□
      Is-∞-extendable-along-[ return ] P  □
  where
  open Modality

  ext₀ = lower-extensionality lzero _ ext

  -- A type A is modal if it is a proposition for which ¬¬ A
  -- implies A.

  ¬¬-modal : Type ℓ → Type ℓ
  ¬¬-modal A = Is-proposition A × (¬¬ A → A)

  lemma :
    {A : Type ℓ} {P : ¬¬ A → Type ℓ} →
    (∀ x → ¬¬-modal (P x)) →
    Is-equivalence (λ (g : ∀ x → P x) → g ∘ return)
  lemma {A = A} {P = P} hyp =
    _≃_.is-equivalence $
    Eq.⇔→≃
      (Π-closure ext 1 λ x →
       hyp x .proj₁)
      (Π-closure ext 1 λ x →
       hyp (return x) .proj₁)
      _
      (((x : A) → P (return x))                  →⟨ (λ f x → map (λ x → x , f x) x) ⟩
       ((x : ¬¬ A) → ¬¬ (∃ λ x → P (return x)))  →⟨ (λ f x → hyp x .proj₂ $ map (subst P (¬¬-propositional ext₀ _ _) ∘ proj₂) (f x)) ⟩□
       ((x : ¬¬ A) → P x)                        □)

-- The double-negation modality is empty-modal.

¬¬-empty-modal :
  ∀ {ℓ} (ext : Extensionality ℓ ℓ) →
  Empty-modal (¬¬-modality ext)
¬¬-empty-modal _ =
  ⊥-propositional , ⊥-elim ∘ ¬¬¬⊥

-- The double-negation modality is not left exact (assuming
-- extensionality).

¬¬-not-left-exact :
  ∀ {a} →
  Extensionality a a →
  ¬ Left-exact (¬¬_ {a = a})
¬¬-not-left-exact {a = a} ext =
  Empty-modal→Is-proposition-◯→¬-Left-exact
    (¬¬-empty-modal ext)
    (¬¬-propositional (lower-extensionality lzero _ ext))
  where
  open Modality (¬¬-modality ext)

-- The double-negation modality is not very modal.

¬¬-not-very-modal :
  ∀ {ℓ} (ext : Extensionality ℓ ℓ) →
  ¬ Very-modal (¬¬-modality ext)
¬¬-not-very-modal {ℓ = ℓ} ext =
  ({A : Type ℓ} → ¬¬ (Is-proposition A × (¬¬ A → A)))        →⟨ (λ hyp → hyp) ⟩
  ¬¬ (Is-proposition (↑ ℓ Bool) × (¬¬ ↑ ℓ Bool → ↑ ℓ Bool))  →⟨ map′ proj₁ ⟩
  ¬¬ Is-proposition (↑ ℓ Bool)                               →⟨ map′ (H-level-cong _ 1 B.↑↔) ⟩
  ¬¬ Is-proposition Bool                                     →⟨ map′ ¬-Bool-propositional ⟩
  ¬¬ ⊥                                                       →⟨ ¬¬¬⊥ ⟩□
  ⊥                                                          □

-- If double-negation elimination holds, then the double-negation
-- modality is W-modal.

¬¬-W-modal :
  ∀ {ℓ} (ext : Extensionality ℓ ℓ) →
  Double-negation-elimination ℓ →
  W-modal (¬¬-modality ext)
¬¬-W-modal ext dne {A = A} {P = P} (p , _) =
  prop , dne prop
  where
  open Modality (¬¬-modality ext)

  prop : Is-proposition (W A P)
  prop = W-closure ext 0 p

-- The double-negation modality is not accessibility-modal.

¬¬-not-accessibility-modal :
  ∀ {ℓ} (ext : Extensionality ℓ ℓ) →
  ¬ Modality.Accessibility-modal (¬¬-modality ext)
¬¬-not-accessibility-modal {ℓ = ℓ} ext =
  Is-proposition-◯→¬-Accessibility-modal
    (¬¬-propositional (lower-extensionality lzero _ ext))
  where
  open Modality (¬¬-modality ext)

-- If double-negation elimination holds, then the double-negation
-- modality is accessibility-modal for propositional relations on
-- propositions.

¬¬-accessibility-modal-for-propositions :
  ∀ {ℓ} {A : Type ℓ} {_<_ : A → A → Type ℓ}
  (ext : Extensionality ℓ ℓ) →
  Double-negation-elimination ℓ →
  Is-proposition A →
  (∀ {x y} → Is-proposition (x < y)) →
  Modality.Accessibility-modal-for (¬¬-modality ext) _<_
¬¬-accessibility-modal-for-propositions {_<_ = _<_} ext dne prop prop′ =
    (λ acc → Modal→Acc→Acc-[]◯-η (prop , dne prop) (dne prop′) acc)
  , dne (A.Acc-propositional ext)
  where
  open Modality (¬¬-modality ext)

-- The double-negation modality commutes with Σ.

¬¬-commutes-with-Σ :
  ∀ {ℓ}
  (ext : Extensionality ℓ ℓ) →
  Modality.Commutes-with-Σ (¬¬-modality ext)
¬¬-commutes-with-Σ ext = Modality.commutes-with-Σ (¬¬-modality ext) ext

-- The double-negation modality commutes with Erased.

commutes-with-Erased :
  ∀ {ℓ} →
  (ext : Extensionality ℓ ℓ) →
  Modality.Commutes-with-Erased (¬¬-modality ext)
commutes-with-Erased {ℓ = ℓ} ext =
  _≃_.is-equivalence $
  Eq.↔→≃
    _
    from
    (λ _ → E.[]-cong₁.H-level-Erased
             (E.Extensionality→[]-cong-axiomatisation ext)
             1
             (¬¬-propositional ext₀)
             _ _)
    (λ _ → ¬¬-propositional ext₀ _ _)
  where
  open Modality (¬¬-modality ext)

  ext₀ : Extensionality ℓ lzero
  ext₀ = lower-extensionality lzero _ ext

  from : {@0 A : Type ℓ} → Erased (¬¬ A) → ¬¬ Erased A
  from {A = A} =
    Erased (¬¬ A)   →⟨ E.map run ⟩
    Erased (¬ ¬ A)  →⟨ E.Erased-¬↔¬ _ ⟩
    ¬ Erased (¬ A)  →⟨ →-cong-→ (_⇔_.from (E.Erased-¬↔¬ _)) id ⟩
    ¬ ¬ Erased A    →⟨ wrap ⟩□
    ¬¬ Erased A     □
