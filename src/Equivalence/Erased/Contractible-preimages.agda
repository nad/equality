------------------------------------------------------------------------
-- Equivalences with erased "proofs", defined in terms of partly
-- erased contractible fibres
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Equivalence.Erased.Contractible-preimages
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
import Equivalence.Contractible-preimages eq as CP
open import Erased.Level-1 eq as Erased
  hiding (module []-cong; module []-cong₁;
          module []-cong₂; module []-cong₂-⊔)
open import Extensionality eq
open import Function-universe eq hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Preimage eq as Preimage using (_⁻¹_)
open import Surjection eq using (_↠_; Split-surjective)

private
  variable
    a b ℓ ℓ₁ ℓ₂      : Level
    A B              : Type a
    c ext k k′ p x y : A
    P                : A → Type p
    f                : (x : A) → P x

open import Equivalence.Erased.Contractible-preimages.Basics eq public

------------------------------------------------------------------------
-- Some conversion lemmas

-- Another conversion between _⁻¹_ and _⁻¹ᴱ_.

@0 ⁻¹≃⁻¹ᴱ : f ⁻¹ y ≃ f ⁻¹ᴱ y
⁻¹≃⁻¹ᴱ {f} {y} =
  (∃ λ x → f x ≡ y)           ↝⟨ (∃-cong λ _ → Eq.inverse $ Eq.↔⇒≃ $ erased Erased↔) ⟩□
  (∃ λ x → Erased (f x ≡ y))  □

_ : _≃_.to ⁻¹≃⁻¹ᴱ p ≡ ⁻¹→⁻¹ᴱ p
_ = refl _

@0 _ : _≃_.from ⁻¹≃⁻¹ᴱ p ≡ ⁻¹ᴱ→⁻¹ p
_ = refl _

-- Another conversion between Contractible and Contractibleᴱ.

@0 Contractible≃Contractibleᴱ :
  Contractible A ≃ Contractibleᴱ A
Contractible≃Contractibleᴱ =
  (∃ λ x → ∀ y → x ≡ y)           ↝⟨ (∃-cong λ _ → Eq.inverse $ Eq.↔⇒≃ $ erased Erased↔) ⟩□
  (∃ λ x → Erased (∀ y → x ≡ y))  □

_ :
  _≃_.to Contractible≃Contractibleᴱ c ≡ Contractible→Contractibleᴱ c
_ = refl _

@0 _ :
  _≃_.from Contractible≃Contractibleᴱ c ≡ Contractibleᴱ→Contractible c
_ = refl _

private

  -- In an erased context CP.Is-equivalence and Is-equivalenceᴱ are
  -- pointwise equivalent (assuming extensionality).
  --
  -- This lemma is not exported. See Is-equivalence≃Is-equivalenceᴱ
  -- below, which computes in a different way.

  @0 Is-equivalence≃Is-equivalenceᴱ′ :
    {A : Type a} {B : Type b} {f : A → B} →
    CP.Is-equivalence f ↝[ a ⊔ b ∣ a ⊔ b ] Is-equivalenceᴱ f
  Is-equivalence≃Is-equivalenceᴱ′ {a} {f} {k} ext =
    (∀ y → Contractible (f ⁻¹ y))    ↝⟨ (∀-cong ext′ λ _ → H-level-cong ext 0 ⁻¹≃⁻¹ᴱ) ⟩
    (∀ y → Contractible (f ⁻¹ᴱ y))   ↝⟨ (∀-cong ext′ λ _ → from-isomorphism Contractible≃Contractibleᴱ) ⟩□
    (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))  □
    where
    ext′ = lower-extensionality? k a lzero ext

------------------------------------------------------------------------
-- Some type formers are propositional in erased contexts

-- In an erased context Contractibleᴱ is propositional (assuming
-- extensionality).

@0 Contractibleᴱ-propositional :
  {A : Type a} →
  Extensionality a a →
  Is-proposition (Contractibleᴱ A)
Contractibleᴱ-propositional ext =
  H-level.respects-surjection
    (_≃_.surjection Contractible≃Contractibleᴱ)
    1
    (Contractible-propositional ext)

-- In an erased context Is-equivalenceᴱ f is a proposition (assuming
-- extensionality).
--
-- See also Is-equivalenceᴱ-propositional-for-Erased below.

@0 Is-equivalenceᴱ-propositional :
  {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  (f : A → B) → Is-proposition (Is-equivalenceᴱ f)
Is-equivalenceᴱ-propositional ext f =
  H-level.respects-surjection
    (_≃_.surjection $ Is-equivalence≃Is-equivalenceᴱ′ ext)
    1
    (Is-equivalence-CP-propositional ext)

------------------------------------------------------------------------
-- More conversion lemmas

-- In an erased context CP.Is-equivalence and Is-equivalenceᴱ are
-- pointwise equivalent (assuming extensionality).

@0 Is-equivalence≃Is-equivalenceᴱ :
  {A : Type a} {B : Type b} {f : A → B} →
  CP.Is-equivalence f ↝[ a ⊔ b ∣ a ⊔ b ] Is-equivalenceᴱ f
Is-equivalence≃Is-equivalenceᴱ {k = equivalence} ext =
  Eq.with-other-function
    (Eq.with-other-inverse
       (Is-equivalence≃Is-equivalenceᴱ′ ext)
       Is-equivalenceᴱ→Is-equivalence
       (λ _ → Is-equivalence-CP-propositional ext _ _))
    Is-equivalence→Is-equivalenceᴱ
    (λ _ → Is-equivalenceᴱ-propositional ext _ _ _)
Is-equivalence≃Is-equivalenceᴱ = Is-equivalence≃Is-equivalenceᴱ′

_ :
  _≃_.to (Is-equivalence≃Is-equivalenceᴱ ext) p ≡
  Is-equivalence→Is-equivalenceᴱ p
_ = refl _

@0 _ :
  _≃_.from (Is-equivalence≃Is-equivalenceᴱ ext) p ≡
  Is-equivalenceᴱ→Is-equivalence p
_ = refl _

-- In an erased context CP._≃_ and _≃ᴱ_ are pointwise equivalent
-- (assuming extensionality).

@0 ≃≃≃ᴱ :
  {A : Type a} {B : Type b} →
  (A CP.≃ B) ↝[ a ⊔ b ∣ a ⊔ b ] (A ≃ᴱ B)
≃≃≃ᴱ {A} {B} ext =
  A CP.≃ B                       ↔⟨⟩
  (∃ λ f → CP.Is-equivalence f)  ↝⟨ (∃-cong λ _ → Is-equivalence≃Is-equivalenceᴱ ext) ⟩
  (∃ λ f → Is-equivalenceᴱ f)    ↔⟨⟩
  A ≃ᴱ B                         □

_ : _≃_.to (≃≃≃ᴱ ext) p ≡ ≃→≃ᴱ p
_ = refl _

@0 _ : _≃_.from (≃≃≃ᴱ ext) p ≡ ≃ᴱ→≃ p
_ = refl _

------------------------------------------------------------------------
-- Results that follow if the []-cong axioms hold for one universe
-- level

module []-cong₁ (ax : []-cong-axiomatisation ℓ) where

  open Erased-cong ax ax
  open Erased.[]-cong₁ ax

  ----------------------------------------------------------------------
  -- Some results related to _⁻¹ᴱ_

  -- An isomorphism relating _⁻¹ᴱ_ to _⁻¹_.
  --
  -- If the --erased-matches flag is activated, then this lemma can be
  -- proved without the use of []-cong, see
  -- Erased.Erased-matches.Erased-⁻¹ᴱ↔Erased-⁻¹.

  Erased-⁻¹ᴱ↔Erased-⁻¹ :
    {@0 A : Type a} {@0 B : Type ℓ} {@0 f : A → B} {@0 y : B} →
    Erased (f ⁻¹ᴱ y) ↔ Erased (f ⁻¹ y)
  Erased-⁻¹ᴱ↔Erased-⁻¹ {f} {y} =
    Erased (∃ λ x → Erased (f x ≡ y))             ↝⟨ Erased-Σ↔Σ ⟩
    (∃ λ x → Erased (Erased (f (erased x) ≡ y)))  ↝⟨ (∃-cong λ _ → Erased-Erased↔Erased) ⟩
    (∃ λ x → Erased (f (erased x) ≡ y))           ↝⟨ inverse Erased-Σ↔Σ ⟩□
    Erased (∃ λ x → f x ≡ y)                      □

  -- The function _⁻¹ᴱ y respects erased extensional equality.

  ⁻¹ᴱ-respects-extensional-equality :
    {@0 B : Type ℓ} {@0 f g : A → B} {@0 y : B} →
    @0 (∀ x → f x ≡ g x) → f ⁻¹ᴱ y ≃ g ⁻¹ᴱ y
  ⁻¹ᴱ-respects-extensional-equality {f} {g} {y} f≡g =
    (∃ λ x → Erased (f x ≡ y))  ↝⟨ (∃-cong λ _ → Erased-cong-≃ (≡⇒↝ _ (cong (_≡ _) $ f≡g _))) ⟩□
    (∃ λ x → Erased (g x ≡ y))  □

  -- An isomorphism relating _⁻¹ᴱ_ to _⁻¹_.

  ⁻¹ᴱ[]↔⁻¹[] :
    {@0 B : Type ℓ} {f : A → Erased B} {@0 y : B} →
    f ⁻¹ᴱ [ y ] ↔ f ⁻¹ [ y ]
  ⁻¹ᴱ[]↔⁻¹[] {f} {y} =
    (∃ λ x → Erased (f x ≡ [ y ]))               ↔⟨ (∃-cong λ _ → Erased-cong-≃ (≡⇒↝ _ $ cong (_≡ _) $ sym Erased-η)) ⟩
    (∃ λ x → Erased ([ erased (f x) ] ≡ [ y ]))  ↔⟨ (∃-cong λ _ → Erased-cong-≃ (Eq.≃-≡ $ Eq.↔⇒≃ $ inverse $ erased Erased↔)) ⟩
    (∃ λ x → Erased (erased (f x) ≡ y))          ↔⟨ (∃-cong λ _ → Erased-≡≃≡) ⟩
    (∃ λ x → f x ≡ [ y ])                        □

  -- Erased "commutes" with _⁻¹ᴱ_.

  Erased-⁻¹ᴱ :
    {@0 A : Type a} {@0 B : Type ℓ} {@0 f : A → B} {@0 y : B} →
    Erased (f ⁻¹ᴱ y) ↔ map f ⁻¹ᴱ [ y ]
  Erased-⁻¹ᴱ {f} {y} =
    Erased (f ⁻¹ᴱ y)  ↝⟨ Erased-⁻¹ᴱ↔Erased-⁻¹ ⟩
    Erased (f ⁻¹ y)   ↝⟨ Erased-⁻¹ ⟩
    map f ⁻¹ [ y ]    ↝⟨ inverse ⁻¹ᴱ[]↔⁻¹[] ⟩□
    map f ⁻¹ᴱ [ y ]   □

  ----------------------------------------------------------------------
  -- Some results related to Contractibleᴱ

  -- An isomorphism relating Contractibleᴱ to Contractible.
  --
  -- If the --erased-matches flag is activated, then this lemma can be
  -- proved without the use of []-cong, see
  -- Erased.Erased-matches.Erased-Contractibleᴱ↔Erased-Contractible.

  Erased-Contractibleᴱ↔Erased-Contractible :
    {@0 A : Type ℓ} →
    Erased (Contractibleᴱ A) ↔ Erased (Contractible A)
  Erased-Contractibleᴱ↔Erased-Contractible =
    Erased (∃ λ x → Erased (∀ y → x ≡ y))           ↝⟨ Erased-Σ↔Σ ⟩
    (∃ λ x → Erased (Erased (∀ y → erased x ≡ y)))  ↝⟨ (∃-cong λ _ → Erased-Erased↔Erased) ⟩
    (∃ λ x → Erased (∀ y → erased x ≡ y))           ↝⟨ inverse Erased-Σ↔Σ ⟩□
    Erased (∃ λ x → ∀ y → x ≡ y)                    □

  -- Erased commutes with Contractibleᴱ.
  --
  -- See also
  -- Erased.Level-2.Erased-Contractibleᴱ≃Contractibleᴱ-Erased.

  Erased-Contractibleᴱ↔Contractibleᴱ-Erased :
    {@0 A : Type ℓ} →
    Erased (Contractibleᴱ A) ↝[ ℓ ∣ ℓ ]ᴱ Contractibleᴱ (Erased A)
  Erased-Contractibleᴱ↔Contractibleᴱ-Erased {A} ext =
    Erased (∃ λ x → Erased ((y : A) → x ≡ y))           ↔⟨ Erased-cong-↔ (∃-cong λ _ → erased Erased↔) ⟩
    Erased (∃ λ x → (y : A) → x ≡ y)                    ↔⟨ Erased-Σ↔Σ ⟩
    (∃ λ x → Erased ((y : A) → erased x ≡ y))           ↝⟨ (∃-cong λ _ →
                                                            Erased-cong?
                                                              (λ ext → ∀-cong ext λ _ →
                                                                         from-isomorphism (inverse $ erased Erased↔))
                                                              ext) ⟩
    (∃ λ x → Erased ((y : A) → Erased (erased x ≡ y)))  ↝⟨ (∃-cong λ _ →
                                                            Erased-cong?
                                                              (λ ext → Π-cong ext (inverse $ erased Erased↔) λ _ →
                                                                         from-isomorphism Erased-≡≃≡)
                                                              ext) ⟩□
    (∃ λ x → Erased ((y : Erased A) → x ≡ y))           □

  -- An isomorphism relating Contractibleᴱ to Contractible.

  Contractibleᴱ-Erased↔Contractible-Erased :
    {@0 A : Type ℓ} →
    Contractibleᴱ (Erased A) ↝[ ℓ ∣ ℓ ] Contractible (Erased A)
  Contractibleᴱ-Erased↔Contractible-Erased {A} ext =
    Contractibleᴱ (Erased A)  ↝⟨ inverse-erased-ext? Erased-Contractibleᴱ↔Contractibleᴱ-Erased ext ⟩
    Erased (Contractibleᴱ A)  ↔⟨ Erased-Contractibleᴱ↔Erased-Contractible ⟩
    Erased (Contractible A)   ↝⟨ Erased-H-level↔H-level 0 ext ⟩□
    Contractible (Erased A)   □

------------------------------------------------------------------------
-- Results that follow if the []-cong axioms hold for two universe
-- levels

module []-cong₂
  (ax₁ : []-cong-axiomatisation ℓ₁)
  (ax₂ : []-cong-axiomatisation ℓ₂)
  where

  open Erased-cong ax₁ ax₂

  ----------------------------------------------------------------------
  -- A result related to Contractibleᴱ

  -- Contractibleᴱ preserves isomorphisms (assuming extensionality).

  Contractibleᴱ-cong :
    {A : Type ℓ₁} {B : Type ℓ₂} →
    @0 Extensionality? k′ (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    A ↔[ k ] B → Contractibleᴱ A ↝[ k′ ] Contractibleᴱ B
  Contractibleᴱ-cong {A} {B} ext A↔B =
    (∃ λ (x : A) → Erased ((y : A) → x ≡ y))  ↝⟨ (Σ-cong A≃B′ λ _ →
                                                  Erased-cong?
                                                    (λ ext → Π-cong ext A≃B′ λ _ →
                                                             from-isomorphism $ inverse $ Eq.≃-≡ A≃B′)
                                                    ext) ⟩□
    (∃ λ (x : B) → Erased ((y : B) → x ≡ y))  □
    where
    A≃B′ = from-isomorphism A↔B

------------------------------------------------------------------------
-- Results that follow if the []-cong axioms hold for two universe
-- levels and their maximum

module []-cong₂-⊔
  (ax₁ : []-cong-axiomatisation ℓ₁)
  (ax₂ : []-cong-axiomatisation ℓ₂)
  (ax  : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
  where

  ----------------------------------------------------------------------
  -- A preservation lemma

  -- Is-equivalenceᴱ f is equivalent to Is-equivalenceᴱ g if f and g
  -- are pointwise equal (assuming extensionality).

  Is-equivalenceᴱ-cong :
    {A : Type ℓ₁} {B : Type ℓ₂} {@0 f g : A → B} →
    Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    @0 (∀ x → f x ≡ g x) →
    Is-equivalenceᴱ f ↝[ k ] Is-equivalenceᴱ g
  Is-equivalenceᴱ-cong {k} ext f≡g =
    ∀-cong (lower-extensionality? k ℓ₁ lzero ext) λ _ →
    []-cong₂.Contractibleᴱ-cong ax ax ext $ ∃-cong λ _ →
    Erased-cong.Erased-cong-≃ ax₂ ax₂ (≡⇒↝ _ $ cong (_≡ _) $ f≡g _)

  ----------------------------------------------------------------------
  -- Some equivalences

  -- A variant of ∘⁻¹≃.

  ∘⁻¹ᴱ≃ :
    ∀ {B : Type ℓ₁} {C : Type ℓ₂} {z} →
    (f : B → C) (g : A → B) →
    f ∘ g ⁻¹ᴱ z ≃ ∃ λ (([ y , _ ]) : Erased (f ⁻¹ z)) → g ⁻¹ᴱ y
  ∘⁻¹ᴱ≃ {z} f g =
    f ∘ g ⁻¹ᴱ z                                                       ↔⟨⟩
    (∃ λ a → Erased (f (g a) ≡ z))                                    ↔⟨ (∃-cong λ _ → Erased-cong.Erased-cong-≃ ax₂ ax (other-∃-intro _ _)) ⟩
    (∃ λ a → Erased (∃ λ y → f y ≡ z × g a ≡ y))                      ↔⟨ (∃-cong λ _ → Erased-cong.Erased-cong-↔ ax ax Σ-assoc) ⟩
    (∃ λ a → Erased (∃ λ ((y , _) : f ⁻¹ z) → g a ≡ y))               ↔⟨ (∃-cong λ _ → Erased-Σ↔Σ) ⟩
    (∃ λ a → ∃ λ (([ y , _ ]) : Erased (f ⁻¹ z)) → Erased (g a ≡ y))  ↔⟨ ∃-comm ⟩□
    (∃ λ (([ y , _ ]) : Erased (f ⁻¹ z)) → g ⁻¹ᴱ y)                   □

  -- A variant of to-∘-⁻¹-≃-⁻¹-from.

  to-∘-⁻¹ᴱ-≃-⁻¹ᴱ-from :
    {B : Type ℓ₁} {C : Type ℓ₂} {f : A → B} {z : C} →
    (B≃C : B ≃ C) →
    _≃_.to B≃C ∘ f ⁻¹ᴱ z ≃ f ⁻¹ᴱ _≃_.from B≃C z
  to-∘-⁻¹ᴱ-≃-⁻¹ᴱ-from {f} {z} B≃C =
    _≃_.to B≃C ∘ f ⁻¹ᴱ z                                      ↝⟨ ∘⁻¹ᴱ≃ _ _ ⟩
    (∃ λ (([ y , _ ]) : Erased (_≃_.to B≃C ⁻¹ z)) → f ⁻¹ᴱ y)  ↔⟨ drop-⊤-left-Σ $
                                                                 _⇔_.to contractible⇔↔⊤ $
                                                                 Erased.[]-cong₁.H-level-Erased ax 0 (Preimage.bijection⁻¹-contractible (_≃_.bijection B≃C) _) ⟩□
    f ⁻¹ᴱ _≃_.from B≃C z                                      □

------------------------------------------------------------------------
-- Results that follow if the []-cong axioms hold for all universe
-- levels

module []-cong (ax : ∀ {ℓ} → []-cong-axiomatisation ℓ) where

  private
    open module BC₁ {ℓ} =
      []-cong₁ (ax {ℓ = ℓ})
      public
    open module BC₂ {ℓ₁ ℓ₂} =
      []-cong₂ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂})
      public
    open module BC₂-⊔ {ℓ₁ ℓ₂} =
      []-cong₂-⊔ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) ax
      public
