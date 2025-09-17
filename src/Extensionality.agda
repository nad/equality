------------------------------------------------------------------------
-- Function extensionality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Extensionality
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equivalence.Half-adjoint eq
import H-level eq as H-level
open import Surjection eq using (_↠_)

private
  variable
    a b c p pℓ q : Level
    A            : Type a
    P            : A → Type p
    x            : A

------------------------------------------------------------------------
-- Function extensionality

-- This section is based on the HoTT book.

-- The "inverse of extensionality".

ext⁻¹ :
  {f g : (x : A) → P x} →
  f ≡ g → (∀ x → f x ≡ g x)
ext⁻¹ f≡g = λ x → cong (λ h → h x) f≡g

opaque

  -- A "computation rule" for ext⁻¹.

  ext⁻¹-refl : (f : (x : A) → P x) → ext⁻¹ (refl f) x ≡ refl (f x)
  ext⁻¹-refl _ = cong-refl _

-- Extensionality for functions of a certain type.

Extensionality′ : (A : Type a) → (A → Type p) → Type (a ⊔ p)
Extensionality′ A P =
  {f g : (x : A) → P x} →
  Is-equivalence (ext⁻¹ {f = f} {g = g})

-- If Extensionality′ A P holds, then any two pointwise equal
-- functions of type (x : A) → P x are equal.

apply-ext′ :
  {f g : (x : A) → P x} →
  Extensionality′ A P →
  (∀ x → f x ≡ g x) → f ≡ g
apply-ext′ ext = inverse ext

-- Extensionality for functions at certain levels.
--
-- The definition is wrapped in a record type in order to avoid
-- certain problems related to Agda's handling of implicit
-- arguments.

record Extensionality (a p : Level) : Type (lsuc (a ⊔ p)) where
  no-eta-equality
  pattern
  field
    extensionality :
      {A : Type a} {P : A → Type p} →
      Extensionality′ A P

  apply-ext :
    {A : Type a} {P : A → Type p} {f g : (x : A) → P x} →
    (∀ x → f x ≡ g x) → f ≡ g
  apply-ext = inverse extensionality

open Extensionality public using (apply-ext)

------------------------------------------------------------------------
-- A different (logically equivalent) statement of function
-- extensionality

-- This section is based on Voevodsky's work on univalent foundations.

-- Extensionality for functions of a certain type.

Function-extensionality′ : (A : Type a) → (A → Type p) → Type (a ⊔ p)
Function-extensionality′ A P =
  {f g : (x : A) → P x} →
  (∀ x → f x ≡ g x) → f ≡ g

-- Extensionality for functions at certain levels.

Function-extensionality : (a p : Level) → Type (lsuc (a ⊔ p))
Function-extensionality a p =
  {A : Type a} {P : A → Type p} →
  Function-extensionality′ A P

-- Closure of contractibility under Π A is logically equivalent to
-- having extensional equality for functions from A.

[Π-Contractible→Contractible-Π]⇔Function-extensionality′ :
  ∀ {a p} {A : Type a} →
  ({P : A → Type p} →
   (∀ x → Contractible (P x)) → Contractible ((x : A) → P x)) ⇔
  ({P : A → Type p} → Function-extensionality′ A P)
[Π-Contractible→Contractible-Π]⇔Function-extensionality′ {p} {A} =
  record
    { to   = to
    ; from = λ ext cP →
          (λ x → cP x .proj₁)
        , (λ f → ext λ x → cP x .proj₂ (f x))
    }
  where
  to :
    ({P : A → Type p} →
     (∀ x → Contractible (P x)) → Contractible ((x : A) → P x)) →
    ({P : A → Type p} → Function-extensionality′ A P)
  to closure {P} {f} {g} f≡g =
    f                                     ≡⟨ (sym (cong (λ c → λ x → c x .proj₁) $
                                              contractible .proj₂ λ x → f x , f≡g x)) ⟩
    (λ x → proj₁ (proj₁ contractible x))  ≡⟨ (cong (λ c → λ x → c x .proj₁) $
                                              contractible .proj₂ λ x → g x , refl (g x)) ⟩∎
    g                                     ∎
    where
    contractible : Contractible ((x : A) → Singleton (g x))
    contractible = closure (singleton-contractible ∘ g)

opaque

  -- The function ext⁻¹ is an equivalence (assuming extensionality).

  ext⁻¹-is-equivalence :
    ({P : A → Type p} → Function-extensionality′ A P) →
    {P : A → Type p} {f g : (x : A) → P x} →
    Is-equivalence (ext⁻¹ {f = f} {g = g})
  ext⁻¹-is-equivalence {A} ext {P} {f} {g} =
    drop-Σ-map-id ext⁻¹ lemma₂ f
    where
    surj :
      (∀ x → Singleton (g x)) ↠
      (∃ λ (f : (x : A) → P x) → ∀ x → f x ≡ g x)
    surj = record
      { logical-equivalence = record
        { to   = λ f → proj₁ ∘ f , proj₂ ∘ f
        ; from = λ p x → proj₁ p x , proj₂ p x
        }
      ; right-inverse-of = refl
      }

    lemma₁ : Contractible (∃ λ (f : (x : A) → P x) → ∀ x → f x ≡ g x)
    lemma₁ =
      H-level.respects-surjection surj 0 $
      _⇔_.from [Π-Contractible→Contractible-Π]⇔Function-extensionality′
        ext (singleton-contractible ∘ g)

    lemma₂ :
      Is-equivalence
        {A = ∃ λ f → f ≡ g}
        {B = ∃ λ f → ∀ x → f x ≡ g x}
        (Σ-map id ext⁻¹)
    lemma₂ =
      function-between-contractible-types-is-equivalence
        _ (singleton-contractible g) lemma₁

-- Extensionality a p is logically equivalent to
-- Function-extensionality a p.

Extensionality⇔Function-extensionality :
  Extensionality a p ⇔ Function-extensionality a p
Extensionality⇔Function-extensionality = record
  { to   = apply-ext
  ; from = λ ext → record { extensionality = ext⁻¹-is-equivalence ext }
  }

------------------------------------------------------------------------
-- Lemmas related to function extensionality

opaque

  -- Extensionality at given levels works at lower levels as well.

  lower-extensionality :
    ∀ â p̂ → Extensionality (a ⊔ â) (p ⊔ p̂) → Extensionality a p
  lower-extensionality {a} {p} â p̂ =
    Extensionality (a ⊔ â) (p ⊔ p̂)           →⟨ _⇔_.to Extensionality⇔Function-extensionality ⟩
    Function-extensionality (a ⊔ â) (p ⊔ p̂)  →⟨ lemma ⟩
    Function-extensionality a p              →⟨ _⇔_.from Extensionality⇔Function-extensionality ⟩□
    Extensionality a p                       □
    where
    lemma :
      Function-extensionality (a ⊔ â) (p ⊔ p̂) →
      Function-extensionality a p
    lemma ext {A} {P} f≡g =
      cong (λ h → lower ∘ h ∘ lift) $
      ext {A = ↑ â A} {P = ↑ p̂ ∘ P ∘ lower} (cong lift ∘ f≡g ∘ lower)

-- Pointwise equal functions with implicit function types are equal
-- (assuming extensionality).

implicit-extensionality :
  Extensionality a p →
  {A : Type a} {P : A → Type p} {f g : {x : A} → P x} →
  (∀ x → f {x} ≡ g {x}) → (λ {@ω x} → f {x}) ≡ g
implicit-extensionality ext f≡g =
  cong (λ f {x} → f x) $ apply-ext ext f≡g

opaque

  -- Some simplification/rearrangement lemmas related to apply-ext.

  ext-ext⁻¹ :
    {A : Type a} {P : A → Type p} {f g : (x : A) → P x} {f≡g : f ≡ g}
    (ext : Extensionality a p) →
    apply-ext ext (ext⁻¹ f≡g) ≡ f≡g
  ext-ext⁻¹ ext =
    left-inverse-of (ext .Extensionality.extensionality) _

  ext⁻¹-ext :
    {A : Type a} {P : A → Type p}
    {f g : (x : A) → P x} {f≡g : ∀ x → f x ≡ g x}
    (ext : Extensionality a p) →
    ext⁻¹ (apply-ext ext f≡g) ≡ f≡g
  ext⁻¹-ext ext =
    right-inverse-of (ext .Extensionality.extensionality) _

  ext-refl :
    {A : Type a} {P : A → Type p} {f : (x : A) → P x}
    (ext : Extensionality a p) →
    apply-ext ext (λ x → refl (f x)) ≡ refl f
  ext-refl {f} ext =
    apply-ext ext (λ x → refl (f x))  ≡⟨ (cong (apply-ext ext) $ sym $ apply-ext ext λ _ → ext⁻¹-refl f) ⟩
    apply-ext ext (ext⁻¹ (refl f))    ≡⟨ left-inverse-of (Extensionality.extensionality ext) _ ⟩∎
    refl f                            ∎

  ext-const :
    {A : Type a} {B : Type b} {x y : B} {x≡y : x ≡ y}
    (ext : Extensionality a b) →
    apply-ext ext (const {B = A} x≡y) ≡
    cong const x≡y
  ext-const {x≡y} ext =
    apply-ext ext (const x≡y)                        ≡⟨ cong (apply-ext ext ∘ const) $ cong-id _ ⟩
    apply-ext ext (const (cong id x≡y))              ≡⟨⟩
    apply-ext ext (λ z → cong ((_$ z) ∘ const) x≡y)  ≡⟨ (cong (apply-ext ext) $ apply-ext ext λ _ → sym $ cong-∘ _ _ _) ⟩
    apply-ext ext (ext⁻¹ (cong const x≡y))           ≡⟨ left-inverse-of (Extensionality.extensionality ext) _ ⟩∎
    cong const x≡y                                   ∎

  cong-ext :
    ∀ {A : Type a} {P : A → Type p} {f g : (x : A) → P x} {x}
      {f≡g : ∀ x → f x ≡ g x}
    (ext : Extensionality a p) →
    cong (_$ x) (apply-ext ext f≡g) ≡ f≡g x
  cong-ext {x} {f≡g} ext =
    cong (_$ x) (apply-ext ext f≡g)  ≡⟨⟩
    ext⁻¹ (apply-ext ext f≡g) x      ≡⟨ cong (_$ x) $ ext⁻¹-ext ext ⟩∎
    f≡g x                            ∎

  ext-cong :
    {A : Type a} {B : Type b} {P : B → Type p}
    {f : A → (x : B) → P x} {x y : A} {x≡y : x ≡ y}
    (ext : Extensionality b p) →
    apply-ext ext (λ z → cong (flip f z) x≡y) ≡ cong f x≡y
  ext-cong {f} {x≡y} ext =
    apply-ext ext (λ z → cong (flip f z) x≡y)       ≡⟨ (cong (apply-ext ext) $ apply-ext ext λ _ → sym $ cong-∘ _ _ _) ⟩
    apply-ext ext (λ z → cong (_$ z) (cong f x≡y))  ≡⟨⟩
    apply-ext ext (ext⁻¹ (cong f x≡y))              ≡⟨ left-inverse-of (Extensionality.extensionality ext) _ ⟩∎
    cong f x≡y                                      ∎

  subst-ext :
    ∀ {A : Type a} {P : A → Type pℓ} {x} {Q : P x → Type q}
      {f g : (x : A) → P x} {f≡g : ∀ x → f x ≡ g x} {p}
    (ext : Extensionality a pℓ) →
    subst (λ f → Q (f x)) (apply-ext ext f≡g) p ≡
    subst Q (f≡g x) p
  subst-ext {x} {Q} {f≡g} {p} ext =
    subst (λ f → Q (f x)) (apply-ext ext f≡g) p  ≡⟨ subst-∘ Q (_$ x) _ ⟩
    subst Q (cong (_$ x) (apply-ext ext f≡g)) p  ≡⟨ cong (λ eq → subst Q eq p) (cong-ext ext) ⟩∎
    subst Q (f≡g x) p                            ∎

  elim-ext :
    {A : Type a} {P : A → Type p} {x : A}
    {Q : P x → P x → Type q} {q : (y : P x) → Q y y}
    {f g : (x : A) → P x} {f≡g : ∀ x → f x ≡ g x} →
    (ext : Extensionality a p) →
    elim (λ {f g} _ → Q (f x) (g x)) (q ∘ (_$ x)) (apply-ext ext f≡g) ≡
    elim (λ {x y} _ → Q x y) q (f≡g x)
  elim-ext {x} {Q} {q} {f≡g} ext =
    elim (λ {f g} _ → Q (f x) (g x)) (q ∘ (_$ x)) (apply-ext ext f≡g)  ≡⟨ sym $ elim-cong _ _ _ ⟩
    elim (λ {x y} _ → Q x y) q (cong (_$ x) (apply-ext ext f≡g))       ≡⟨ cong (elim (λ {x y} _ → Q x y) q) (cong-ext ext) ⟩∎
    elim (λ {x y} _ → Q x y) q (f≡g x)                                 ∎

  -- I based the statements of the following three lemmas on code in
  -- the Lean Homotopy Type Theory Library with Jakob von Raumer and
  -- Floris van Doorn listed as authors. The file was claimed to have
  -- been ported from the Coq HoTT library. (The third lemma has later
  -- been generalised.)

  ext-sym :
    {A : Type a} {P : A → Type p}
    {f g : (x : A) → P x} {f≡g : ∀ x → f x ≡ g x} →
    (ext : Extensionality a p) →
    apply-ext ext (sym ∘ f≡g) ≡ sym (apply-ext ext f≡g)
  ext-sym {f≡g} ext =
    apply-ext ext (sym ∘ f≡g)                                    ≡⟨ cong (apply-ext ext ∘ (sym ∘_)) $ sym $
                                                                    right-inverse-of (Extensionality.extensionality ext) _ ⟩
    apply-ext ext (sym ∘ ext⁻¹ (apply-ext ext f≡g))              ≡⟨⟩
    apply-ext ext (λ x → sym $ cong (_$ x) (apply-ext ext f≡g))  ≡⟨ (cong (apply-ext ext) $ apply-ext ext λ _ → sym $ cong-sym _ _) ⟩
    apply-ext ext (λ x → cong (_$ x) (sym $ apply-ext ext f≡g))  ≡⟨⟩
    apply-ext ext (ext⁻¹ (sym $ apply-ext ext f≡g))              ≡⟨ left-inverse-of (Extensionality.extensionality ext) _ ⟩∎
    sym (apply-ext ext f≡g)                                      ∎

  ext-trans :
    {A : Type a} {P : A → Type p} {f g h : (x : A) → P x}
    {f≡g : ∀ x → f x ≡ g x} {g≡h : ∀ x → g x ≡ h x}
    (ext : Extensionality a p) →
    apply-ext ext (λ x → trans (f≡g x) (g≡h x)) ≡
    trans (apply-ext ext f≡g) (apply-ext ext g≡h)
  ext-trans {f≡g} {g≡h} ext =
    (apply-ext ext λ x → trans (f≡g x) (g≡h x))                          ≡⟨ sym $ cong₂ (λ f g → apply-ext ext (λ x → trans (f x) (g x)))
                                                                              (right-inverse-of (Extensionality.extensionality ext) _)
                                                                              (right-inverse-of (Extensionality.extensionality ext) _) ⟩
    (apply-ext ext λ x →
     trans (ext⁻¹ (apply-ext ext f≡g) x) (ext⁻¹ (apply-ext ext g≡h) x))  ≡⟨⟩

    (apply-ext ext λ x →
     trans (cong (_$ x) (apply-ext ext f≡g))
           (cong (_$ x) (apply-ext ext g≡h)))                            ≡⟨ (cong (apply-ext ext) $ apply-ext ext λ _ → sym $
                                                                             cong-trans _ _ _) ⟩
    (apply-ext ext λ x →
     cong (_$ x) (trans (apply-ext ext f≡g) (apply-ext ext g≡h)))        ≡⟨⟩

    apply-ext ext
      (ext⁻¹ (trans (apply-ext ext f≡g) (apply-ext ext g≡h)))            ≡⟨ left-inverse-of (Extensionality.extensionality ext) _ ⟩∎

    trans (apply-ext ext f≡g) (apply-ext ext g≡h)                        ∎

  cong-post-∘-ext :
    {A : Type a} {P : A → Type p} {Q : A → Type q}
    {f g : (x : A) → P x} {h : ∀ {x} → P x → Q x}
    {f≡g : ∀ x → f x ≡ g x}
    (ext₁ : Extensionality a p) (ext₂ : Extensionality a q) →
    cong (h ∘_) (apply-ext ext₁ f≡g) ≡
    apply-ext ext₂ (cong h ∘ f≡g)
  cong-post-∘-ext {f} {g} {h} {f≡g} ext₁ ext₂ =
    cong (h ∘_) (apply-ext ext₁ f≡g)                                  ≡⟨ sym $ left-inverse-of (Extensionality.extensionality ext₂) _ ⟩

    apply-ext ext₂ (ext⁻¹ (cong (h ∘_) (apply-ext ext₁ f≡g)))         ≡⟨⟩

    apply-ext ext₂
      (λ x → cong (_$ x) (cong (h ∘_) (apply-ext ext₁ f≡g)))          ≡⟨ (cong (apply-ext ext₂) $ apply-ext ext₂ λ _ → cong-∘ _ _ _) ⟩

    apply-ext ext₂ (λ x → cong (λ f → h (f x)) (apply-ext ext₁ f≡g))  ≡⟨ (cong (apply-ext ext₂) $ apply-ext ext₂ λ _ → sym $ cong-∘ _ _ _) ⟩

    apply-ext ext₂ (λ x → cong h (cong (_$ x) (apply-ext ext₁ f≡g)))  ≡⟨⟩

    apply-ext ext₂ (cong h ∘ ext⁻¹ (apply-ext ext₁ f≡g))              ≡⟨ cong (apply-ext ext₂ ∘ (cong h ∘_)) $
                                                                         right-inverse-of (Extensionality.extensionality ext₁) _ ⟩∎
    apply-ext ext₂ (cong h ∘ f≡g)                                     ∎

  cong-pre-∘-ext :
    {A : Type a} {B : Type b} {P : B → Type p}
    {f g : (x : B) → P x} {h : A → B} {f≡g : ∀ x → f x ≡ g x}
    (ext₁ : Extensionality a p)
    (ext₂ : Extensionality b p) →
    cong (_∘ h) (apply-ext ext₂ f≡g) ≡ apply-ext ext₁ (f≡g ∘ h)
  cong-pre-∘-ext {f} {g} {h} {f≡g} ext₁ ext₂ =
    cong (_∘ h) (apply-ext ext₂ f≡g)                           ≡⟨ sym $ left-inverse-of (Extensionality.extensionality ext₁) _ ⟩

    apply-ext ext₁ (ext⁻¹ (cong (_∘ h) (apply-ext ext₂ f≡g)))  ≡⟨⟩

    apply-ext ext₁
      (λ x → cong (_$ x) (cong (_∘ h) (apply-ext ext₂ f≡g)))   ≡⟨ (cong (apply-ext ext₁) $ apply-ext ext₁ λ _ → cong-∘ _ _ _) ⟩

    apply-ext ext₁ (λ x → cong (_$ h x) (apply-ext ext₂ f≡g))  ≡⟨ (cong (apply-ext ext₁) $ apply-ext ext₁ λ _ → cong-ext ext₂) ⟩

    apply-ext ext₁ (λ x → f≡g (h x))                           ≡⟨⟩

    apply-ext ext₁ (f≡g ∘ h)                                   ∎

  cong-∘-ext :
    {A : Type a} {B : Type b} {C : Type c}
    {f g : B → C} {f≡g : ∀ x → f x ≡ g x} →
    (ext₁ : Extensionality b c)
    (ext₂ : Extensionality (a ⊔ b) (a ⊔ c))
    (ext₃ : Extensionality a c) →
    cong (λ f → f ∘_ ⦂ ((A → B) → (A → C))) (apply-ext ext₁ f≡g) ≡
    apply-ext ext₂ λ h → apply-ext ext₃ λ x → f≡g (h x)
  cong-∘-ext {f≡g} ext₁ ext₂ ext₃ =
    cong (λ f → f ∘_) (apply-ext ext₁ f≡g)                   ≡⟨ sym $ left-inverse-of (Extensionality.extensionality ext₂) _ ⟩

    (apply-ext ext₂ λ h →
     cong (_$ h) (cong (λ f → f ∘_) (apply-ext ext₁ f≡g)))   ≡⟨ (cong (apply-ext ext₂) $ apply-ext ext₂ λ _ → cong-∘ _ _ _) ⟩

    (apply-ext ext₂ λ h → cong (_∘ h) (apply-ext ext₁ f≡g))  ≡⟨ (cong (apply-ext ext₂) $ apply-ext ext₂ λ _ → cong-pre-∘-ext ext₃ ext₁) ⟩∎

    (apply-ext ext₂ λ h → apply-ext ext₃ λ x → f≡g (h x))    ∎
