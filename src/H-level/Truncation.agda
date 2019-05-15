------------------------------------------------------------------------
-- Truncation, defined as a HIT
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- The beginning of this module follows the HoTT book rather closely.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the truncation uses path equality,
-- but the supplied notion of equality is used for many other things.

open import Equality

module H-level.Truncation
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq hiding (elim)

import Equality.Path as P
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open import Equality.Path.Isomorphisms eq
import Equivalence eq as Eq
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Truncation.Propositional eq as TP using (∥_∥)
open import Monad eq
open import Nat eq as Nat using (_≤_; min)
open import Pointed-type eq
open import Sphere eq
open import Suspension eq as Susp using (north)

private
  variable
    a ℓ p : Level
    A B   : Set a
    P     : A → Set p
    x     : A
    f g r : A → B
    m n   : ℕ
    k     : Isomorphism-kind

-- A truncation operator for positive h-levels.

data ∥_∥[1+_] (A : Set a) (n : ℕ) : Set a where
  ∣_∣    : A → ∥ A ∥[1+ n ]
  hub    : (r : 𝕊 n → ∥ A ∥[1+ n ]) → ∥ A ∥[1+ n ]
  spoke′ : (r : 𝕊 n → ∥ A ∥[1+ n ]) (x : 𝕊 n) → r x P.≡ hub r

-- Spoke equalities.

spoke : (r : 𝕊 n → ∥ A ∥[1+ n ]) (x : 𝕊 n) → r x ≡ hub r
spoke r x = _↔_.from ≡↔≡ (spoke′ r x)

-- The truncation operator produces types of the right h-level.

truncation-has-correct-h-level : ∀ n → H-level (1 + n) ∥ A ∥[1+ n ]
truncation-has-correct-h-level {A = A} n =
  _↔_.from +↔∀contractible𝕊→ᴮ c
  where
  c : ∀ x → Contractible ((𝕊 n , north) →ᴮ (∥ A ∥[1+ n ] , x))
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

-- A dependent eliminator.

module Elim′
  (P : ∥ A ∥[1+ n ] → Set p)
  (f : ∀ x → P ∣ x ∣)
  (h : (r : 𝕊 n → ∥ A ∥[1+ n ]) →
       (∀ x → P (r x)) →
       P (hub r))
  (s : (r : 𝕊 n → ∥ A ∥[1+ n ])
       (p : ∀ x → P (r x))
       (x : 𝕊 n) →
       subst P (spoke r x) (p x) ≡ h r p)
  where

  elim′ : ∀ x → P x
  elim′ ∣ x ∣          = f x
  elim′ (hub r)        = h r (λ x → elim′ (r x))
  elim′ (spoke′ r x i) = subst≡→[]≡ (s r (λ x → elim′ (r x)) x) i

  elim′-spoke : dcong elim′ (spoke r x) ≡ s r (λ x → elim′ (r x)) x
  elim′-spoke = dcong-subst≡→[]≡ (refl _)

open Elim′ public

-- A non-dependent eliminator.

module Rec′
  (f : A → B)
  (h : (r : 𝕊 n → ∥ A ∥[1+ n ]) → (𝕊 n → B) → B)
  (s : (r : 𝕊 n → ∥ A ∥[1+ n ]) (p : 𝕊 n → B) (x : 𝕊 n) → p x ≡ h r p)
  where

  private
    module E = Elim′ (const B) f h
      (λ r p x →
        subst (λ _ → B) (spoke r x) (p x)  ≡⟨ subst-const _ ⟩
        p x                                ≡⟨ s r p x ⟩∎
        h r p                              ∎)

  rec′ : ∥ A ∥[1+ n ] → B
  rec′ = E.elim′

  rec′-spoke : cong rec′ (spoke r x) ≡ s r (λ x → rec′ (r x)) x
  rec′-spoke = dcong≡→cong≡ E.elim′-spoke

open Rec′ public

-- A dependent eliminator that can be used when the motive is a family
-- of types, all of a certain h-level.

elim :
  (P : ∥ A ∥[1+ n ] → Set p) →
  (∀ x → H-level (1 + n) (P x)) →
  (∀ x → P ∣ x ∣) →
  ∀ x → P x
elim {A = A} {n = n} P P-h f = elim′ P f h s
  where

  module _ (r : 𝕊 n → ∥ A ∥[1+ n ]) (p : ∀ x → P (r x)) where

    h′ : 𝕊 n → P (hub r)
    h′ x = subst P (spoke r x) (p x)

    h = h′ north

    lemma =                                                    $⟨ P-h ⟩
      (∀ x → H-level (1 + n) (P x))                            ↝⟨ _$ _ ⟩
      H-level (1 + n) (P (hub r))                              ↔⟨ +↔∀contractible𝕊→ᴮ ⟩
      (∀ h → Contractible ((𝕊 n , north) →ᴮ (P (hub r) , h)))  ↝⟨ _$ _ ⟩
      Contractible ((𝕊 n , north) →ᴮ (P (hub r) , h))          ↝⟨ mono₁ _ ⟩□
      Is-proposition ((𝕊 n , north) →ᴮ (P (hub r) , h))        □

    s = λ x →
      subst P (spoke r x) (p x)  ≡⟨⟩
      h′ x                       ≡⟨ cong (λ f → proj₁ f x) $ lemma (h′ , refl _) (const h , refl _) ⟩
      const h x                  ≡⟨⟩
      h                          ∎

-- A non-dependent eliminator that can be used when the motive is a
-- type of a certain h-level.

rec : H-level (1 + n) B → (A → B) → ∥ A ∥[1+ n ] → B
rec B-h = elim _ (const B-h)

-- Dependent functions into P that agree on the image of ∣_∣ agree
-- everywhere, if P is a family of types that all have a certain
-- h-level.

uniqueness′ :
  {f g : (x : ∥ A ∥[1+ n ]) → P x} →
  (∀ x → H-level (2 + n) (P x)) →
  ((x : A) → f ∣ x ∣ ≡ g ∣ x ∣) →
  ((x : ∥ A ∥[1+ n ]) → f x ≡ g x)
uniqueness′ {n = n} P-h = elim _ (λ _ → +⇒≡ {n = suc n} (P-h _))

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
      ; from = rec h
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

-- A has h-level 1 + n if and only if it is isomorphic to
-- ∥ A ∥[1+ n ].

+⇔∥∥↔ : H-level (1 + n) A ⇔ (∥ A ∥[1+ n ] ↔ A)
+⇔∥∥↔ {n = n} {A = A} = record
  { to = λ h → record
    { surjection = record
      { logical-equivalence = record
        { to   = rec h id
        ; from = ∣_∣
        }
      ; right-inverse-of = refl
      }
    ; left-inverse-of = elim _
        (λ _ → ⇒≡ _ $ truncation-has-correct-h-level _)
        (λ x → ∣ x ∣  ∎)
    }
  ; from =
      ∥ A ∥[1+ n ] ↔ A                                    ↝⟨ H-level-cong ext _ ⟩
      (H-level (1 + n) ∥ A ∥[1+ n ] ↔ H-level (1 + n) A)  ↝⟨ (λ hyp → _↔_.to hyp (truncation-has-correct-h-level _)) ⟩□
      H-level (1 + n) A                                   □
  }

-- Nested truncations where the inner truncation's h-level is at least
-- as large as the outer truncation's h-level can be flattened.

flatten-≥ : m ≤ n → ∥ ∥ A ∥[1+ n ] ∥[1+ m ] ↔ ∥ A ∥[1+ m ]
flatten-≥ m≤n = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec (truncation-has-correct-h-level _)
                   (rec (mono (Nat.suc≤suc m≤n)
                              (truncation-has-correct-h-level _))
                        ∣_∣)
      ; from = ∥∥-map ∣_∣
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
      { to   = rec (mono (Nat.suc≤suc m≤n)
                         (truncation-has-correct-h-level _))
                   id
      ; from = ∣_∣
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
      ; from = rec TP.truncation-is-proposition TP.∣_∣
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
