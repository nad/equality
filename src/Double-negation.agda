------------------------------------------------------------------------
-- The double-negation monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Double-negation
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as B using (_↔_)
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Equivalence.Path-split eq as PS
  using (Is-∞-extendable-along-[_])
open import Excluded-middle eq
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

-- Instances.

instance

  double-negation-monad : ∀ {ℓ} → Raw-monad (λ (A : Type ℓ) → ¬¬ A)
  run (Raw-monad.return double-negation-monad x)   = _$ x
  run (Raw-monad._>>=_  double-negation-monad x f) =
    join (map′ (run ∘ f) x)
    where
    join : ∀ {a} {A : Type a} → ¬¬ ¬ A → ¬ A
    join ¬¬¬a = λ a → run ¬¬¬a (λ ¬a → ¬a a)

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
