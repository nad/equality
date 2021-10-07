------------------------------------------------------------------------
-- Equivalences with erased "proofs", defined in terms of partly
-- erased contractible fibres
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Equivalence.Erased.Contractible-preimages
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Prelude

open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
import Equivalence.Contractible-preimages eq as CP
open import Erased.Level-1 eq as Erased
  hiding (module []-cong; module []-cong₁; module []-cong₂)
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

------------------------------------------------------------------------
-- Some basic types

-- "Preimages" with erased proofs.

infix 5 _⁻¹ᴱ_

_⁻¹ᴱ_ : {A : Type a} {@0 B : Type b} → @0 (A → B) → @0 B → Type (a ⊔ b)
f ⁻¹ᴱ y = ∃ λ x → Erased (f x ≡ y)

-- Contractibility with an erased proof.

Contractibleᴱ : Type ℓ → Type ℓ
Contractibleᴱ A = ∃ λ (x : A) → Erased (∀ y → x ≡ y)

-- The property of being an equivalence (with erased proofs).

Is-equivalenceᴱ : {A : Type a} {B : Type b} → @0 (A → B) → Type (a ⊔ b)
Is-equivalenceᴱ f = ∀ y → Contractibleᴱ (f ⁻¹ᴱ y)

-- Equivalences with erased proofs.

_≃ᴱ_ : Type a → Type b → Type (a ⊔ b)
A ≃ᴱ B = ∃ λ (f : A → B) → Is-equivalenceᴱ f

------------------------------------------------------------------------
-- Some conversion lemmas

-- Conversions between _⁻¹_ and _⁻¹ᴱ_.

⁻¹→⁻¹ᴱ :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} {@0 y : B} →
  f ⁻¹ y → f ⁻¹ᴱ y
⁻¹→⁻¹ᴱ = Σ-map id [_]→

@0 ⁻¹ᴱ→⁻¹ : f ⁻¹ᴱ x → f ⁻¹ x
⁻¹ᴱ→⁻¹ = Σ-map id erased

@0 ⁻¹≃⁻¹ᴱ : f ⁻¹ y ≃ f ⁻¹ᴱ y
⁻¹≃⁻¹ᴱ {f = f} {y = y} =
  (∃ λ x → f x ≡ y)           ↝⟨ (∃-cong λ _ → Eq.inverse $ Eq.↔⇒≃ $ erased Erased↔) ⟩□
  (∃ λ x → Erased (f x ≡ y))  □

_ : _≃_.to ⁻¹≃⁻¹ᴱ p ≡ ⁻¹→⁻¹ᴱ p
_ = refl _

@0 _ : _≃_.from ⁻¹≃⁻¹ᴱ p ≡ ⁻¹ᴱ→⁻¹ p
_ = refl _

-- Conversions between Contractible and Contractibleᴱ.

Contractible→Contractibleᴱ :
  {@0 A : Type a} →
  Contractible A → Contractibleᴱ A
Contractible→Contractibleᴱ = Σ-map id [_]→

@0 Contractibleᴱ→Contractible : Contractibleᴱ A → Contractible A
Contractibleᴱ→Contractible = Σ-map id erased

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

-- Conversions between CP.Is-equivalence and Is-equivalenceᴱ.

Is-equivalence→Is-equivalenceᴱ :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
  CP.Is-equivalence f → Is-equivalenceᴱ f
Is-equivalence→Is-equivalenceᴱ eq y =
    ⁻¹→⁻¹ᴱ (proj₁₀ (eq y))
  , [ cong ⁻¹→⁻¹ᴱ ∘ proj₂ (eq y) ∘ ⁻¹ᴱ→⁻¹ ]

@0 Is-equivalenceᴱ→Is-equivalence :
  Is-equivalenceᴱ f → CP.Is-equivalence f
Is-equivalenceᴱ→Is-equivalence eq y =
    ⁻¹ᴱ→⁻¹ (proj₁ (eq y))
  , cong ⁻¹ᴱ→⁻¹ ∘ erased (proj₂ (eq y)) ∘ ⁻¹→⁻¹ᴱ

private

  -- In an erased context CP.Is-equivalence and Is-equivalenceᴱ are
  -- pointwise equivalent (assuming extensionality).
  --
  -- This lemma is not exported. See Is-equivalence≃Is-equivalenceᴱ
  -- below, which computes in a different way.

  @0 Is-equivalence≃Is-equivalenceᴱ′ :
    {A : Type a} {B : Type b} {f : A → B} →
    CP.Is-equivalence f ↝[ a ⊔ b ∣ a ⊔ b ] Is-equivalenceᴱ f
  Is-equivalence≃Is-equivalenceᴱ′ {a = a} {f = f} {k = k} ext =
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
    (CP.propositional ext f)

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
       (λ _ → CP.propositional ext _ _ _))
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

-- Conversions between CP._≃_ and _≃ᴱ_.

≃→≃ᴱ :
  {@0 A : Type a} {@0 B : Type b} →
  A CP.≃ B → A ≃ᴱ B
≃→≃ᴱ = Σ-map id Is-equivalence→Is-equivalenceᴱ

@0 ≃ᴱ→≃ : A ≃ᴱ B → A CP.≃ B
≃ᴱ→≃ = Σ-map id Is-equivalenceᴱ→Is-equivalence

-- In an erased context CP._≃_ and _≃ᴱ_ are pointwise equivalent
-- (assuming extensionality).

@0 ≃≃≃ᴱ :
  {A : Type a} {B : Type b} →
  (A CP.≃ B) ↝[ a ⊔ b ∣ a ⊔ b ] (A ≃ᴱ B)
≃≃≃ᴱ {A = A} {B = B} ext =
  A CP.≃ B                       ↔⟨⟩
  (∃ λ f → CP.Is-equivalence f)  ↝⟨ (∃-cong λ _ → Is-equivalence≃Is-equivalenceᴱ ext) ⟩
  (∃ λ f → Is-equivalenceᴱ f)    ↔⟨⟩
  A ≃ᴱ B                         □

_ : _≃_.to (≃≃≃ᴱ ext) p ≡ ≃→≃ᴱ p
_ = refl _

@0 _ : _≃_.from (≃≃≃ᴱ ext) p ≡ ≃ᴱ→≃ p
_ = refl _

-- An isomorphism relating _⁻¹ᴱ_ to _⁻¹_.

Erased-⁻¹ᴱ↔Erased-⁻¹ :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} {@0 y : B} →
  Erased (f ⁻¹ᴱ y) ↔ Erased (f ⁻¹ y)
Erased-⁻¹ᴱ↔Erased-⁻¹ {f = f} {y = y} =
  Erased (∃ λ x → Erased (f x ≡ y))             ↝⟨ Erased-Σ↔Σ ⟩
  (∃ λ x → Erased (Erased (f (erased x) ≡ y)))  ↝⟨ (∃-cong λ _ → Erased-Erased↔Erased) ⟩
  (∃ λ x → Erased (f (erased x) ≡ y))           ↝⟨ inverse Erased-Σ↔Σ ⟩□
  Erased (∃ λ x → f x ≡ y)                      □

-- An isomorphism relating Contractibleᴱ to Contractible.

Erased-Contractibleᴱ↔Erased-Contractible :
  {@0 A : Type a} →
  Erased (Contractibleᴱ A) ↔ Erased (Contractible A)
Erased-Contractibleᴱ↔Erased-Contractible =
  Erased (∃ λ x → Erased (∀ y → x ≡ y))           ↝⟨ Erased-Σ↔Σ ⟩
  (∃ λ x → Erased (Erased (∀ y → erased x ≡ y)))  ↝⟨ (∃-cong λ _ → Erased-Erased↔Erased) ⟩
  (∃ λ x → Erased (∀ y → erased x ≡ y))           ↝⟨ inverse Erased-Σ↔Σ ⟩□
  Erased (∃ λ x → ∀ y → x ≡ y)                    □

------------------------------------------------------------------------
-- Some results related to Contractibleᴱ

-- Contractibleᴱ respects split surjections with erased proofs.

Contractibleᴱ-respects-surjection :
  {@0 A : Type a} {@0 B : Type b}
  (f : A → B) → @0 Split-surjective f →
  Contractibleᴱ A → Contractibleᴱ B
Contractibleᴱ-respects-surjection {A = A} {B = B} f s h@(x , _) =
    f x
  , [ proj₂ (H-level.respects-surjection surj 0
               (Contractibleᴱ→Contractible h))
    ]
  where
  @0 surj : A ↠ B
  surj = record
    { logical-equivalence = record
      { to   = f
      ; from = proj₁ ∘ s
      }
    ; right-inverse-of = proj₂ ∘ s
    }

-- "Preimages" (with erased proofs) of an erased function with a
-- quasi-inverse with erased proofs are contractible.

Contractibleᴱ-⁻¹ᴱ :
  {@0 A : Type a} {@0 B : Type b}
  (@0 f : A → B)
  (g : B → A)
  (@0 f∘g : ∀ x → f (g x) ≡ x)
  (@0 g∘f : ∀ x → g (f x) ≡ x) →
  ∀ y → Contractibleᴱ (f ⁻¹ᴱ y)
Contractibleᴱ-⁻¹ᴱ {A = A} {B = B} f g f∘g g∘f y =
    (g y , [ proj₂ (proj₁ c′) ])
  , [ cong ⁻¹→⁻¹ᴱ ∘ proj₂ c′ ∘ ⁻¹ᴱ→⁻¹ ]
  where
  @0 A↔B : A ↔ B
  A↔B = record
    { surjection = record
      { logical-equivalence = record
        { to   = f
        ; from = g
        }
      ; right-inverse-of = f∘g
      }
    ; left-inverse-of = g∘f
    }

  @0 c′ : Contractible (f ⁻¹ y)
  c′ = Preimage.bijection⁻¹-contractible A↔B y

-- If an inhabited type comes with an erased proof of
-- propositionality, then it is contractible (with erased proofs).

inhabited→Is-proposition→Contractibleᴱ :
  {@0 A : Type a} →
  A → @0 Is-proposition A → Contractibleᴱ A
inhabited→Is-proposition→Contractibleᴱ x prop = (x , [ prop x ])

-- Some closure properties.

Contractibleᴱ-Σ :
  {@0 A : Type a} {@0 P : A → Type p} →
  Contractibleᴱ A → (∀ x → Contractibleᴱ (P x)) → Contractibleᴱ (Σ A P)
Contractibleᴱ-Σ cA@(a , _) cP =
    (a , proj₁₀ (cP a))
  , [ proj₂ $ Σ-closure 0 (Contractibleᴱ→Contractible cA)
                          (Contractibleᴱ→Contractible ∘ cP)
    ]

Contractibleᴱ-× :
  {@0 A : Type a} {@0 B : Type b} →
  Contractibleᴱ A → Contractibleᴱ B → Contractibleᴱ (A × B)
Contractibleᴱ-× cA cB = Contractibleᴱ-Σ cA (λ _ → cB)

Contractibleᴱ-Π :
  {@0 A : Type a} {@0 P : A → Type p} →
  @0 Extensionality a p →
  (∀ x → Contractibleᴱ (P x)) → Contractibleᴱ ((x : A) → P x)
Contractibleᴱ-Π ext c =
    proj₁₀ ∘ c
  , [ proj₂ $ Π-closure ext 0 (Contractibleᴱ→Contractible ∘ c)
    ]

Contractibleᴱ-↑ :
  {@0 A : Type a} →
  Contractibleᴱ A → Contractibleᴱ (↑ ℓ A)
Contractibleᴱ-↑ c@(a , _) =
    lift a
  , [ proj₂ $ ↑-closure 0 (Contractibleᴱ→Contractible c)
    ]

------------------------------------------------------------------------
-- Results that follow if the []-cong axioms hold for one universe
-- level

module []-cong₁ (ax : []-cong-axiomatisation ℓ) where

  open Erased-cong ax ax
  open Erased.[]-cong₁ ax

  ----------------------------------------------------------------------
  -- Some results related to _⁻¹ᴱ_

  -- The function _⁻¹ᴱ y respects erased extensional equality.

  ⁻¹ᴱ-respects-extensional-equality :
    {@0 B : Type ℓ} {@0 f g : A → B} {@0 y : B} →
    @0 (∀ x → f x ≡ g x) → f ⁻¹ᴱ y ≃ g ⁻¹ᴱ y
  ⁻¹ᴱ-respects-extensional-equality {f = f} {g = g} {y = y} f≡g =
    (∃ λ x → Erased (f x ≡ y))  ↝⟨ (∃-cong λ _ → Erased-cong-≃ (≡⇒↝ _ (cong (_≡ _) $ f≡g _))) ⟩□
    (∃ λ x → Erased (g x ≡ y))  □

  -- An isomorphism relating _⁻¹ᴱ_ to _⁻¹_.

  ⁻¹ᴱ[]↔⁻¹[] :
    {@0 B : Type ℓ} {f : A → Erased B} {@0 y : B} →
    f ⁻¹ᴱ [ y ] ↔ f ⁻¹ [ y ]
  ⁻¹ᴱ[]↔⁻¹[] {f = f} {y = y} =
    (∃ λ x → Erased (f x ≡ [ y ]))       ↔⟨ (∃-cong λ _ → Erased-cong-≃ (Eq.≃-≡ $ Eq.↔⇒≃ $ inverse $ erased Erased↔)) ⟩
    (∃ λ x → Erased (erased (f x) ≡ y))  ↝⟨ (∃-cong λ _ → Erased-≡↔[]≡[]) ⟩□
    (∃ λ x → f x ≡ [ y ])                □

  -- Erased "commutes" with _⁻¹ᴱ_.

  Erased-⁻¹ᴱ :
    {@0 A : Type a} {@0 B : Type ℓ} {@0 f : A → B} {@0 y : B} →
    Erased (f ⁻¹ᴱ y) ↔ map f ⁻¹ᴱ [ y ]
  Erased-⁻¹ᴱ {f = f} {y = y} =
    Erased (f ⁻¹ᴱ y)  ↝⟨ Erased-⁻¹ᴱ↔Erased-⁻¹ ⟩
    Erased (f ⁻¹ y)   ↝⟨ Erased-⁻¹ ⟩
    map f ⁻¹ [ y ]    ↝⟨ inverse ⁻¹ᴱ[]↔⁻¹[] ⟩□
    map f ⁻¹ᴱ [ y ]   □

  ----------------------------------------------------------------------
  -- Some results related to Contractibleᴱ

  -- Erased commutes with Contractibleᴱ.

  Erased-Contractibleᴱ↔Contractibleᴱ-Erased :
    {@0 A : Type ℓ} →
    Erased (Contractibleᴱ A) ↝[ ℓ ∣ ℓ ]ᴱ Contractibleᴱ (Erased A)
  Erased-Contractibleᴱ↔Contractibleᴱ-Erased {A = A} ext =
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
                                                                         from-isomorphism Erased-≡↔[]≡[])
                                                              ext) ⟩□
    (∃ λ x → Erased ((y : Erased A) → x ≡ y))           □

  -- An isomorphism relating Contractibleᴱ to Contractible.

  Contractibleᴱ-Erased↔Contractible-Erased :
    {@0 A : Type ℓ} →
    Contractibleᴱ (Erased A) ↝[ ℓ ∣ ℓ ] Contractible (Erased A)
  Contractibleᴱ-Erased↔Contractible-Erased {A = A} ext =
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
  Contractibleᴱ-cong {A = A} {B = B} ext A↔B =
    (∃ λ (x : A) → Erased ((y : A) → x ≡ y))  ↝⟨ (Σ-cong A≃B′ λ _ →
                                                  Erased-cong?
                                                    (λ ext → Π-cong ext A≃B′ λ _ →
                                                             from-isomorphism $ inverse $ Eq.≃-≡ A≃B′)
                                                    ext) ⟩□
    (∃ λ (x : B) → Erased ((y : B) → x ≡ y))  □
    where
    A≃B′ = from-isomorphism A↔B

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
