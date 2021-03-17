------------------------------------------------------------------------
-- Truncation, defined as a HIT
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- The beginning of this module follows the HoTT book rather closely.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the truncation uses path equality,
-- but the supplied notion of equality is used for many other things.

import Equality.Path as P

module H-level.Truncation
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as TP using (∥_∥)
open import Monad equality-with-J
open import Nat equality-with-J as Nat using (_≤_; min)
import Pointed-type equality-with-J as PT
open import Sphere eq
open import Suspension eq as Susp using (north)
open import Univalence-axiom equality-with-J

private
  variable
    a b ℓ p : Level
    A B C   : Type a
    P       : A → Type p
    e x y   : A
    f g r   : A → B
    m n     : ℕ
    k       : Isomorphism-kind

-- A truncation operator for positive h-levels.

data ∥_∥[1+_] (A : Type a) (n : ℕ) : Type a where
  ∣_∣    : A → ∥ A ∥[1+ n ]
  hub    : (r : 𝕊 n → ∥ A ∥[1+ n ]) → ∥ A ∥[1+ n ]
  spokeᴾ : (r : 𝕊 n → ∥ A ∥[1+ n ]) (x : 𝕊 n) → r x P.≡ hub r

-- Spoke equalities.

spoke : (r : 𝕊 n → ∥ A ∥[1+ n ]) (x : 𝕊 n) → r x ≡ hub r
spoke r x = _↔_.from ≡↔≡ (spokeᴾ r x)

-- The truncation operator produces types of the right h-level.

truncation-has-correct-h-level : ∀ n → H-level (1 + n) ∥ A ∥[1+ n ]
truncation-has-correct-h-level {A = A} n =
  _↔_.from +↔∀contractible𝕊→ᴮ c
  where
  c : ∀ x → Contractible ((𝕊 n , north) PT.→ᴮ (∥ A ∥[1+ n ] , x))
  c x =
      (const x , (const x (north {A = 𝕊 n})  ≡⟨⟩
                  x                          ∎))
    , λ { (f , fn≡x) → Σ-≡,≡→≡
            (⟨ext⟩ λ y →
               const x y  ≡⟨⟩
               x          ≡⟨ sym fn≡x ⟩
               f north    ≡⟨ spoke f north ⟩
               hub f      ≡⟨ sym $ spoke f y ⟩∎
               f y        ∎)
            (subst (λ f → f north ≡ x)
                   (⟨ext⟩ (λ y → trans (sym fn≡x)
                                   (trans (spoke f north)
                                      (sym (spoke f y)))))
                   (refl x)                                             ≡⟨ subst-ext _ _ ⟩

             subst (_≡ x)
                   (trans (sym fn≡x)
                      (trans (spoke f north) (sym (spoke f north))))
                   (refl x)                                             ≡⟨ cong (λ p → subst (_≡ x) (trans (sym fn≡x) p) (refl x)) $ trans-symʳ _ ⟩

             subst (_≡ x) (trans (sym fn≡x) (refl (f north))) (refl x)  ≡⟨ cong (λ p → subst (_≡ x) p (refl x)) $ trans-reflʳ _ ⟩

             subst (_≡ x) (sym fn≡x) (refl x)                           ≡⟨ subst-trans _ ⟩

             trans fn≡x (refl x)                                        ≡⟨ trans-reflʳ _ ⟩∎

             fn≡x                                                       ∎)
        }

-- A dependent eliminator, expressed using paths.

record Elimᴾ {A : Type a} (P : ∥ A ∥[1+ n ] → Type p) :
             Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ    : ∀ x → P ∣ x ∣
    hubʳ   : (r : 𝕊 n → ∥ A ∥[1+ n ]) →
             (∀ x → P (r x)) →
             P (hub r)
    spokeʳ : (r : 𝕊 n → ∥ A ∥[1+ n ])
             (p : ∀ x → P (r x))
             (x : 𝕊 n) →
             P.[ (λ i → P (spokeᴾ r x i)) ] p x ≡ hubʳ r p

open Elimᴾ public

elimᴾ : Elimᴾ P → ∀ x → P x
elimᴾ {P = P} e = helper
  where
  module E = Elimᴾ e

  helper : ∀ x → P x
  helper ∣ x ∣          = E.∣∣ʳ x
  helper (hub r)        = E.hubʳ r (λ x → helper (r x))
  helper (spokeᴾ r x i) = E.spokeʳ r (λ x → helper (r x)) x i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (n : ℕ) (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ    : A → B
    hubʳ   : (𝕊 n → ∥ A ∥[1+ n ]) → (𝕊 n → B) → B
    spokeʳ : (r : 𝕊 n → ∥ A ∥[1+ n ]) (p : 𝕊 n → B) (x : 𝕊 n) →
             p x P.≡ hubʳ r p

open Recᴾ public

recᴾ : Recᴾ n A B → ∥ A ∥[1+ n ] → B
recᴾ r = elimᴾ eᴾ
  where
  module R = Recᴾ r

  eᴾ : Elimᴾ _
  eᴾ .∣∣ʳ    = r .∣∣ʳ
  eᴾ .hubʳ   = r .hubʳ
  eᴾ .spokeʳ = r .spokeʳ

-- A dependent eliminator.

record Elim′ {A : Type a} (P : ∥ A ∥[1+ n ] → Type p) :
             Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ    : ∀ x → P ∣ x ∣
    hubʳ   : (r : 𝕊 n → ∥ A ∥[1+ n ]) →
             (∀ x → P (r x)) →
             P (hub r)
    spokeʳ : (r : 𝕊 n → ∥ A ∥[1+ n ])
             (p : ∀ x → P (r x))
             (x : 𝕊 n) →
             subst P (spoke r x) (p x) ≡ hubʳ r p

open Elim′ public

elim′ : Elim′ P → ∀ x → P x
elim′ e′ = elimᴾ eᴾ
  where
  module E′ = Elim′ e′

  eᴾ : Elimᴾ _
  eᴾ .∣∣ʳ          = E′.∣∣ʳ
  eᴾ .hubʳ         = E′.hubʳ
  eᴾ .spokeʳ r p x = subst≡→[]≡ (E′.spokeʳ r p x)

elim′-spoke :
  dcong (elim′ e) (spoke r x) ≡
  Elim′.spokeʳ e r (λ x → elim′ e (r x)) x
elim′-spoke = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

record Rec′ (n : ℕ) (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ    : A → B
    hubʳ   : (𝕊 n → ∥ A ∥[1+ n ]) → (𝕊 n → B) → B
    spokeʳ : (r : 𝕊 n → ∥ A ∥[1+ n ]) (p : 𝕊 n → B) (x : 𝕊 n) →
             p x ≡ hubʳ r p

open Rec′ public

rec′ : Rec′ n A B → ∥ A ∥[1+ n ] → B
rec′ r′ = recᴾ rᴾ
  where
  module R′ = Rec′ r′

  rᴾ : Recᴾ _ _ _
  rᴾ .∣∣ʳ          = R′.∣∣ʳ
  rᴾ .hubʳ         = R′.hubʳ
  rᴾ .spokeʳ r p x = _↔_.to ≡↔≡ (R′.spokeʳ r p x)

rec′-spoke :
  cong (rec′ e) (spoke r x) ≡ Rec′.spokeʳ e r (λ x → rec′ e (r x)) x
rec′-spoke = cong-≡↔≡ (refl _)

-- A dependent eliminator that can be used when the motive is a family
-- of types, all of a certain h-level.

record Elim {A : Type a} (P : ∥ A ∥[1+ n ] → Type p) :
            Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ      : ∀ x → P ∣ x ∣
    h-levelʳ : ∀ x → H-level (1 + n) (P x)

open Elim public

elim : Elim {n = n} {A = A} P → ∀ x → P x
elim {n = n} {A = A} {P = P} e = elim′ e′
  where
  module _ (r : 𝕊 n → ∥ A ∥[1+ n ]) (p : ∀ x → P (r x)) where

    h′ : 𝕊 n → P (hub r)
    h′ x = subst P (spoke r x) (p x)

    h = h′ north

    lemma =                                                       $⟨ e .h-levelʳ ⟩
      (∀ x → H-level (1 + n) (P x))                               ↝⟨ _$ _ ⟩
      H-level (1 + n) (P (hub r))                                 ↔⟨ +↔∀contractible𝕊→ᴮ ⟩
      (∀ h → Contractible ((𝕊 n , north) PT.→ᴮ (P (hub r) , h)))  ↝⟨ _$ _ ⟩
      Contractible ((𝕊 n , north) PT.→ᴮ (P (hub r) , h))          ↝⟨ mono₁ _ ⟩□
      Is-proposition ((𝕊 n , north) PT.→ᴮ (P (hub r) , h))        □

    s = λ x →
      subst P (spoke r x) (p x)  ≡⟨⟩
      h′ x                       ≡⟨ cong (λ f → proj₁ f x) $ lemma (h′ , refl _) (const h , refl _) ⟩
      const h x                  ≡⟨⟩
      h                          ∎

  e′ : Elim′ _
  e′ .∣∣ʳ    = e .∣∣ʳ
  e′ .hubʳ   = h
  e′ .spokeʳ = s

-- A non-dependent eliminator that can be used when the motive is a
-- type of a certain h-level.

record Rec (n : ℕ) (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ      : A → B
    h-levelʳ : H-level (1 + n) B

open Rec public

rec : Rec n A B → ∥ A ∥[1+ n ] → B
rec r = elim λ where
  .∣∣ʳ        → r .∣∣ʳ
  .h-levelʳ _ → r .h-levelʳ

-- Dependent functions into P that agree on the image of ∣_∣ agree
-- everywhere, if P is a family of types that all have a certain
-- h-level.

uniqueness′ :
  {f g : (x : ∥ A ∥[1+ n ]) → P x} →
  (∀ x → H-level (2 + n) (P x)) →
  ((x : A) → f ∣ x ∣ ≡ g ∣ x ∣) →
  ((x : ∥ A ∥[1+ n ]) → f x ≡ g x)
uniqueness′ {n = n} P-h f≡g = elim λ where
  .∣∣ʳ        → f≡g
  .h-levelʳ _ → +⇒≡ {n = suc n} (P-h _)

-- A special case of the previous property.

uniqueness :
  {f g : ∥ A ∥[1+ n ] → B} →
  H-level (1 + n) B →
  ((x : A) → f ∣ x ∣ ≡ g ∣ x ∣) →
  ((x : ∥ A ∥[1+ n ]) → f x ≡ g x)
uniqueness h = uniqueness′ (λ _ → mono₁ _ h)

-- The truncation operator's universal property.

universal-property :
  H-level (1 + n) B →
  (∥ A ∥[1+ n ] → B) ↔ (A → B)
universal-property h = record
  { surjection = record
    { logical-equivalence = record
      { to   = _∘ ∣_∣
      ; from = λ f → rec λ where
          .∣∣ʳ      → f
          .h-levelʳ → h
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = λ f → ⟨ext⟩ $ uniqueness h (λ x → f ∣ x ∣  ∎)
  }

-- The truncation operator ∥_∥[1+ n ] is a functor.

∥∥-map : (A → B) → ∥ A ∥[1+ n ] → ∥ B ∥[1+ n ]
∥∥-map {A = A} {B = B} {n = n} =
  (A → B)                        ↝⟨ ∣_∣ ∘_ ⟩
  (A → ∥ B ∥[1+ n ])             ↔⟨ inverse $ universal-property (truncation-has-correct-h-level _) ⟩□
  (∥ A ∥[1+ n ] → ∥ B ∥[1+ n ])  □

∥∥-map-id :
  (x : ∥ A ∥[1+ n ]) →
  ∥∥-map id x ≡ x
∥∥-map-id = uniqueness
  (truncation-has-correct-h-level _)
  (λ x → ∣ x ∣  ∎)

∥∥-map-∘ :
  (x : ∥ A ∥[1+ n ]) →
  ∥∥-map (f ∘ g) x ≡ ∥∥-map f (∥∥-map g x)
∥∥-map-∘ {f = f} {g = g} = uniqueness
  (truncation-has-correct-h-level _)
  (λ x → ∣ f (g x) ∣  ∎)

-- A zip function.

∥∥-zip : (A → B → C) → ∥ A ∥[1+ n ] → ∥ B ∥[1+ n ] → ∥ C ∥[1+ n ]
∥∥-zip f = rec λ where
  .∣∣ʳ x    → ∥∥-map (f x)
  .h-levelʳ → Π-closure ext _ λ _ →
              truncation-has-correct-h-level _

-- A has h-level 1 + n if and only if it is isomorphic to
-- ∥ A ∥[1+ n ].

+⇔∥∥↔ : H-level (1 + n) A ⇔ (∥ A ∥[1+ n ] ↔ A)
+⇔∥∥↔ {n = n} {A = A} = record
  { to = λ h → record
    { surjection = record
      { logical-equivalence = record
        { from = ∣_∣
        ; to   = rec λ where
            .∣∣ʳ      → id
            .h-levelʳ → h
        }
      ; right-inverse-of = refl
      }
    ; left-inverse-of = elim λ where
        .∣∣ʳ x      → ∣ x ∣  ∎
        .h-levelʳ _ → ⇒≡ _ $ truncation-has-correct-h-level _
    }
  ; from =
      ∥ A ∥[1+ n ] ↔ A                                    ↝⟨ H-level-cong ext _ ⟩
      (H-level (1 + n) ∥ A ∥[1+ n ] ↔ H-level (1 + n) A)  ↝⟨ (λ hyp → _↔_.to hyp (truncation-has-correct-h-level _)) ⟩□
      H-level (1 + n) A                                   □
  }

-- The (1 + n)-truncation of x ≡ y, where x and y have type A, is
-- equivalent to the equality of ∣ x ∣ and ∣ y ∣ (as elements of the
-- (2 + n)-truncation of A), assuming univalence.
--
-- Along with the fact that this lemma computes in a certain way (see
-- below) this is more or less Theorem 7.3.12 from the HoTT book.

∥≡∥≃∣∣≡∣∣ :
  {A : Type a} {x y : A} →
  Univalence a →
  ∥ x ≡ y ∥[1+ n ] ≃ _≡_ {A = ∥ A ∥[1+ suc n ]} ∣ x ∣ ∣ y ∣
∥≡∥≃∣∣≡∣∣ {n = n} {A = A} univ = Eq.↔→≃
  (decode ∣ _ ∣ ∣ _ ∣)
  (encode ∣ _ ∣ ∣ _ ∣)
  (decode-encode _)
  (encode-decode _ _)
  where
  Eq : (_ _ : ∥ A ∥[1+ suc n ]) → ∃ λ (B : Type _) → H-level (suc n) B
  Eq = rec λ where
    .h-levelʳ →
      Π-closure ext (2 + n) λ _ →
      ∃-H-level-H-level-1+ ext univ (1 + n)
    .∣∣ʳ x → rec λ where
      .h-levelʳ → ∃-H-level-H-level-1+ ext univ (1 + n)
      .∣∣ʳ y →
        ∥ x ≡ y ∥[1+ n ] , truncation-has-correct-h-level n

  Eq-refl : (x : ∥ A ∥[1+ suc n ]) → proj₁ (Eq x x)
  Eq-refl = elim λ where
    .∣∣ʳ x      → ∣ refl x ∣
    .h-levelʳ x → mono₁ (1 + n) $ proj₂ (Eq x x)

  decode : ∀ x y → proj₁ (Eq x y) → x ≡ y
  decode = elim λ where
    .h-levelʳ _ →
      Π-closure ext (2 + n) λ _ →
      Π-closure ext (2 + n) λ _ →
      mono₁ (2 + n) $ truncation-has-correct-h-level (1 + n)
    .∣∣ʳ x → elim λ where
      .h-levelʳ _ →
        Π-closure ext (2 + n) λ _ →
        mono₁ (2 + n) $ truncation-has-correct-h-level (1 + n)
      .∣∣ʳ y → rec λ where
        .h-levelʳ → truncation-has-correct-h-level (1 + n)
        .∣∣ʳ      → cong ∣_∣

  encode : ∀ x y → x ≡ y → proj₁ (Eq x y)
  encode x y x≡y = subst (λ y → proj₁ (Eq x y)) x≡y (Eq-refl x)

  decode-encode : ∀ x (x≡y : x ≡ y) → decode x y (encode x y x≡y) ≡ x≡y
  decode-encode = elim λ where
    .h-levelʳ _ →
      Π-closure ext (2 + n) λ _ →
      mono₁ (3 + n) $ mono₁ (2 + n) $
      truncation-has-correct-h-level (1 + n)
    .∣∣ʳ x → elim¹
      (λ x≡y → decode _ _ (encode _ _ x≡y) ≡ x≡y)
      (decode (∣ x ∣) (∣ x ∣) (encode ∣ x ∣ ∣ x ∣ (refl ∣ x ∣))      ≡⟨⟩

       decode (∣ x ∣) (∣ x ∣)
         (subst (λ y → proj₁ (Eq ∣ x ∣ y)) (refl ∣ x ∣) ∣ refl x ∣)  ≡⟨ cong (decode _ _) $ subst-refl _ _ ⟩

       decode (∣ x ∣) (∣ x ∣) (∣ refl x ∣)                           ≡⟨⟩

       cong ∣_∣ (refl x)                                             ≡⟨ cong-refl _ ⟩∎

       refl ∣ x ∣                                                    ∎)

  encode-decode :
    ∀ x y (eq : proj₁ (Eq x y)) → encode x y (decode x y eq) ≡ eq
  encode-decode = elim λ where
    .h-levelʳ x →
       Π-closure ext (2 + n) λ y →
       Π-closure ext (2 + n) λ _ →
       mono₁ (2 + n) $ mono₁ (1 + n) $
       proj₂ (Eq x y)
    .∣∣ʳ x → elim λ where
      .h-levelʳ y →
        Π-closure ext (2 + n) λ _ →
        mono₁ (2 + n) $ mono₁ (1 + n) $
        proj₂ (Eq ∣ x ∣ y)
      .∣∣ʳ y → elim λ where
        .h-levelʳ _ →
          mono₁ (1 + n) $ truncation-has-correct-h-level n
        .∣∣ʳ eq →
          encode ∣ x ∣ ∣ y ∣ (decode (∣ x ∣) (∣ y ∣) (∣ eq ∣))         ≡⟨⟩
          subst (λ y → proj₁ (Eq ∣ x ∣ y)) (cong ∣_∣ eq) (∣ refl x ∣)  ≡⟨ sym $ subst-∘ _ _ _ ⟩
          subst (λ y → proj₁ (Eq ∣ x ∣ ∣ y ∣)) eq (∣ refl x ∣)         ≡⟨⟩
          subst (λ y → ∥ x ≡ y ∥[1+ n ]) eq (∣ refl x ∣)               ≡⟨ elim¹
                                                                            (λ eq → subst (λ y → ∥ x ≡ y ∥[1+ n ]) eq (∣ refl x ∣) ≡
                                                                                    ∣ subst (x ≡_) eq (refl x) ∣)
                                                                            (trans (subst-refl _ _) $
                                                                             cong ∣_∣ $ sym $ subst-refl _ _)
                                                                            _ ⟩
          ∣ subst (x ≡_) eq (refl x) ∣                                 ≡⟨ cong ∣_∣ $ sym trans-subst ⟩
          ∣ trans (refl x) eq ∣                                        ≡⟨ cong ∣_∣ $ trans-reflˡ _ ⟩∎
          ∣ eq ∣                                                       ∎

_ :
  {A : Type a} {x y : A} {univ : Univalence a}
  {x≡y : x ≡ y} →
  _≃_.to (∥≡∥≃∣∣≡∣∣ {n = n} univ) ∣ x≡y ∣ ≡ cong ∣_∣ x≡y
_ = refl _

-- Nested truncations where the inner truncation's h-level is at least
-- as large as the outer truncation's h-level can be flattened.

flatten-≥ : m ≤ n → ∥ ∥ A ∥[1+ n ] ∥[1+ m ] ↔ ∥ A ∥[1+ m ]
flatten-≥ m≤n = record
  { surjection = record
    { logical-equivalence = record
      { from = ∥∥-map ∣_∣
      ; to   = rec λ where
          .h-levelʳ → truncation-has-correct-h-level _
          .∣∣ʳ      → rec λ where
            .∣∣ʳ      → ∣_∣
            .h-levelʳ → mono (Nat.suc≤suc m≤n)
                             (truncation-has-correct-h-level _)
      }
    ; right-inverse-of = uniqueness
        (truncation-has-correct-h-level _)
        (λ x → ∣ x ∣  ∎)
    }
  ; left-inverse-of = uniqueness
      (truncation-has-correct-h-level _)
      (uniqueness
         (mono (Nat.suc≤suc m≤n)
               (truncation-has-correct-h-level _))
         (λ x → ∣ ∣ x ∣ ∣  ∎))
  }

-- The remainder of this module is not based on the HoTT book.

-- Nested truncations where the inner truncation's h-level is at most
-- as large as the outer truncation's h-level can be flattened.

flatten-≤ : m ≤ n → ∥ ∥ A ∥[1+ m ] ∥[1+ n ] ↔ ∥ A ∥[1+ m ]
flatten-≤ m≤n = record
  { surjection = record
    { logical-equivalence = record
      { from = ∣_∣
      ; to   = rec λ where
          .∣∣ʳ      → id
          .h-levelʳ → mono (Nat.suc≤suc m≤n)
                           (truncation-has-correct-h-level _)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = uniqueness
      (truncation-has-correct-h-level _)
      (λ x → ∣ x ∣  ∎)
  }

-- Nested truncations can be flattened.

flatten : ∥ ∥ A ∥[1+ m ] ∥[1+ n ] ↔ ∥ A ∥[1+ min m n ]
flatten {A = A} {m = m} {n = n} = case Nat.total m n of λ where
  (inj₁ m≤n) → ∥ ∥ A ∥[1+ m ] ∥[1+ n ]  ↝⟨ flatten-≤ m≤n ⟩
               ∥ A ∥[1+ m ]             ↝⟨ ≡⇒↝ _ $ cong ∥ A ∥[1+_] $ sym $ _⇔_.to Nat.≤⇔min≡ m≤n ⟩□
               ∥ A ∥[1+ min m n ]       □
  (inj₂ m≥n) → ∥ ∥ A ∥[1+ m ] ∥[1+ n ]  ↝⟨ flatten-≥ m≥n ⟩
               ∥ A ∥[1+ n ]             ↝⟨ ≡⇒↝ _ $ cong ∥ A ∥[1+_] $ sym $ _⇔_.to Nat.≤⇔min≡ m≥n ⟩
               ∥ A ∥[1+ min n m ]       ↝⟨ ≡⇒↝ _ $ cong ∥ A ∥[1+_] $ Nat.min-comm _ _ ⟩□
               ∥ A ∥[1+ min m n ]       □

-- The propositional truncation operator ∥_∥ is pointwise isomorphic
-- to ∥_∥[1+ 0 ].

∥∥↔∥∥ : ∥ A ∥ ↔ ∥ A ∥[1+ 0 ]
∥∥↔∥∥ = record
  { surjection = record
    { logical-equivalence = record
      { to   = TP.rec (truncation-has-correct-h-level 0) ∣_∣
      ; from = rec λ where
          .∣∣ʳ      → TP.∣_∣
          .h-levelʳ → TP.truncation-is-proposition
      }
    ; right-inverse-of = λ _ → truncation-has-correct-h-level 0 _ _
    }
  ; left-inverse-of = λ _ → TP.truncation-is-proposition _ _
  }

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∥ A ∥[1+ n ] → (A → ∥ B ∥[1+ n ]) → ∥ B ∥[1+ n ]
_>>=′_ {A = A} {n = n} {B = B} = curry (
  ∥ A ∥[1+ n ] × (A → ∥ B ∥[1+ n ])  ↝⟨ uncurry (flip ∥∥-map) ⟩
  ∥ ∥ B ∥[1+ n ] ∥[1+ n ]            ↔⟨ flatten-≤ Nat.≤-refl ⟩□
  ∥ B ∥[1+ n ]                       □)

-- ∥_∥[1+ n ] is a monad.

instance

  monad : Monad {c = ℓ} (∥_∥[1+ n ])
  Raw-monad.return (Monad.raw-monad monad) = ∣_∣

  Raw-monad._>>=_ (Monad.raw-monad monad) = _>>=′_

  Monad.left-identity monad = λ _ _ → refl _

  Monad.right-identity monad =
    uniqueness (truncation-has-correct-h-level _) (λ _ → refl _)

  Monad.associativity monad = flip λ f → flip λ g → uniqueness
    (truncation-has-correct-h-level _)
    (λ x → f x >>=′ g  ∎)

-- The truncation operator preserves logical equivalences.

∥∥-cong-⇔ : A ⇔ B → ∥ A ∥[1+ n ] ⇔ ∥ B ∥[1+ n ]
∥∥-cong-⇔ A⇔B = record
  { to   = ∥∥-map (_⇔_.to   A⇔B)
  ; from = ∥∥-map (_⇔_.from A⇔B)
  }

-- The truncation operator preserves bijections.

∥∥-cong : A ↔[ k ] B → ∥ A ∥[1+ n ] ↔[ k ] ∥ B ∥[1+ n ]
∥∥-cong {n = n} A↝B = from-bijection (record
  { surjection = record
    { logical-equivalence = record
      { to   = ∥∥-map (_↔_.to   A↔B)
      ; from = ∥∥-map (_↔_.from A↔B)
      }
    ; right-inverse-of = lemma A↔B
    }
  ; left-inverse-of = lemma (inverse A↔B)
  })
  where
  A↔B = from-isomorphism A↝B

  lemma :
    (A↔B : A ↔ B) (x : ∥ B ∥[1+ n ]) →
    ∥∥-map (_↔_.to A↔B) (∥∥-map (_↔_.from A↔B) x) ≡ x
  lemma A↔B x =
    ∥∥-map (_↔_.to A↔B) (∥∥-map (_↔_.from A↔B) x)  ≡⟨ sym $ ∥∥-map-∘ x ⟩
    ∥∥-map (_↔_.to A↔B ∘ _↔_.from A↔B) x           ≡⟨ cong (λ f → ∥∥-map f x) $ ⟨ext⟩ $ _↔_.right-inverse-of A↔B ⟩
    ∥∥-map id x                                    ≡⟨ ∥∥-map-id x ⟩∎
    x                                              ∎

-- ∥ A ∥[1+_] is downwards closed.

downwards-closed : m ≤ n → ∥ A ∥[1+ n ] → ∥ A ∥[1+ m ]
downwards-closed {m = m} {n = n} {A = A} m≤n =
  ∥ A ∥[1+ n ]             ↝⟨ ∥∥-map ∣_∣ ⟩
  ∥ ∥ A ∥[1+ m ] ∥[1+ n ]  ↔⟨ flatten-≤ m≤n ⟩□
  ∥ A ∥[1+ m ]             □
