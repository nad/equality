------------------------------------------------------------------------
-- Pushouts, defined using a HIT
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- This module follows the HoTT book rather closely.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining pushouts uses path equality, but
-- the supplied notion of equality is used for many other things.

import Equality.Path as P

module Pushout
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Pointed-type equality-with-J
import Suspension eq as S

private
  variable
    a b l m p r : Level
    A           : Set a
    S           : A

-- Spans.

record Span l r m : Set (lsuc (l ⊔ r ⊔ m)) where
  field
    {Left}   : Set l
    {Right}  : Set r
    {Middle} : Set m
    left     : Middle → Left
    right    : Middle → Right

-- Pushouts.

data Pushout (S : Span l r m) : Set (l ⊔ r ⊔ m) where
  inl   : Span.Left  S → Pushout S
  inr   : Span.Right S → Pushout S
  glueᴾ : (x : Span.Middle S) →
          inl (Span.left S x) P.≡ inr (Span.right S x)

-- Glue.

glue : (x : Span.Middle S) →
       _≡_ {A = Pushout S} (inl (Span.left S x)) (inr (Span.right S x))
glue x = _↔_.from ≡↔≡ (glueᴾ x)

-- A dependent eliminator, expressed using paths.

elimᴾ :
  {S : Span l m r} (open Span S)
  (P : Pushout S → Set p)
  (h₁ : (x : Left) → P (inl x))
  (h₂ : (x : Right) → P (inr x)) →
  (∀ x → P.[ (λ i → P (glueᴾ x i)) ] h₁ (left x) ≡ h₂ (right x)) →
  (x : Pushout S) → P x
elimᴾ P h₁ h₂ g = λ where
  (inl x)     → h₁ x
  (inr x)     → h₂ x
  (glueᴾ x i) → g x i

-- A non-dependent eliminator.

recᴾ :
  {S : Span l m r} (open Span S)
  (h₁ : Left → A)
  (h₂ : Right → A) →
  (∀ x → h₁ (left x) P.≡ h₂ (right x)) →
  Pushout S → A
recᴾ = elimᴾ _

-- A dependent eliminator.

elim :
  {S : Span l m r} (open Span S)
  (P : Pushout S → Set p)
  (h₁ : (x : Left) → P (inl x))
  (h₂ : (x : Right) → P (inr x)) →
  (∀ x → subst P (glue x) (h₁ (left x)) ≡ h₂ (right x)) →
  (x : Pushout S) → P x
elim P h₁ h₂ g = elimᴾ P h₁ h₂ (subst≡→[]≡ ∘ g)

elim-glue :
  {S : Span l m r} (open Span S) {P : Pushout S → Set p}
  {h₁ : (x : Left) → P (inl x)}
  {h₂ : (x : Right) → P (inr x)}
  {g : ∀ x → subst P (glue x) (h₁ (left x)) ≡ h₂ (right x)}
  {x : Middle} →
  dcong (elim P h₁ h₂ g) (glue x) ≡ g x
elim-glue = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

rec :
  {S : Span l m r} (open Span S)
  (h₁ : Left → A)
  (h₂ : Right → A) →
  (∀ x → h₁ (left x) ≡ h₂ (right x)) →
  Pushout S → A
rec h₁ h₂ g = recᴾ h₁ h₂ (_↔_.to ≡↔≡ ∘ g)

rec-glue :
  {S : Span l m r} (open Span S)
  {h₁ : Left → A} {h₂ : Right → A}
  {g : ∀ x → h₁ (left x) ≡ h₂ (right x)}
  {x : Middle} →
  cong (rec h₁ h₂ g) (glue x) ≡ g x
rec-glue = cong-≡↔≡ (refl _)

-- Cocones.

Cocone : Span l m r → Set a → Set (a ⊔ l ⊔ m ⊔ r)
Cocone S A =
  ∃ λ (left  : Left  → A) →
  ∃ λ (right : Right → A) →
    (x : Middle) → left (Span.left S x) ≡ right (Span.right S x)
  where
  open Span S using (Left; Right; Middle)

-- Some projection functions for cocones.

module Cocone (c : Cocone S A) where
  open Span S using (Left; Right; Middle)

  left : Left → A
  left = proj₁ c

  right : Right → A
  right = proj₁ (proj₂ c)

  left-left≡right-right :
    (x : Middle) → left (Span.left S x) ≡ right (Span.right S x)
  left-left≡right-right = proj₂ (proj₂ c)

-- A universal property for pushouts.

Pushout→↔Cocone : (Pushout S → A) ↔ Cocone S A
Pushout→↔Cocone {S = S} {A = A} = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to-from
    }
  ; left-inverse-of = from-to
  }
  where
  open Span S

  to : (Pushout S → A) → Cocone S A
  to f = f ∘ inl , f ∘ inr , cong f ∘ glue

  from : Cocone S A → (Pushout S → A)
  from c = rec
    (Cocone.left c)
    (Cocone.right c)
    (Cocone.left-left≡right-right c)

  to-from : ∀ c → to (from c) ≡ c
  to-from c = cong (λ x → _ , _ , x) $ ⟨ext⟩ λ x →
    cong (from c) (glue x)            ≡⟨ rec-glue ⟩∎
    Cocone.left-left≡right-right c x  ∎

  from-to : ∀ f → from (to f) ≡ f
  from-to f = ⟨ext⟩ $ elim
    _
    (λ _ → refl _)
    (λ _ → refl _)
    (λ x →
       subst (λ y → from (to f) y ≡ f y) (glue x) (refl _)                    ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (from (to f)) (glue x)))
         (trans (refl _) (cong f (glue x)))                                   ≡⟨ cong (trans _) $ trans-reflˡ _ ⟩

       trans (sym (cong (from (to f)) (glue x))) (cong f (glue x))            ≡⟨ cong (λ eq → trans (sym eq) (cong f (glue x))) rec-glue ⟩

       trans (sym (Cocone.left-left≡right-right (to f) x)) (cong f (glue x))  ≡⟨⟩

       trans (sym (cong f (glue x))) (cong f (glue x))                        ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                                 ∎)

-- Joins.

Join : Set a → Set b → Set (a ⊔ b)
Join A B = Pushout (record
  { Middle = A × B
  ; left   = proj₁
  ; right  = proj₂
  })

-- Cones.

Cone : {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Cone f = Pushout (record
  { Left  = ⊤
  ; right = f
  })

-- Wedges.

Wedge : Pointed-type a → Pointed-type b → Set (a ⊔ b)
Wedge (A , a) (B , b) =
  Pushout (record
    { Middle = ⊤
    ; left   = const a
    ; right  = const b
    })

-- Smash products.

Smash-product : Pointed-type a → Pointed-type b → Set (a ⊔ b)
Smash-product PA@(A , a) PB@(B , b) = Cone f
  where
  f : Wedge PA PB → A × B
  f = rec (_, b) (a ,_) (λ _ → refl _)

-- Suspensions.

Susp : Set a → Set a
Susp A = Pushout (record
  { Left   = ⊤
  ; Middle = A
  ; Right  = ⊤
  })

-- These suspensions are equivalent to the ones defined in Suspension.

Susp≃Susp : Susp A ≃ S.Susp A
Susp≃Susp = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  })
  where
  to : Susp A → S.Susp A
  to = recᴾ (λ _ → S.north) (λ _ → S.south) S.meridianᴾ

  from : S.Susp A → Susp A
  from = S.recᴾ (inl _) (inr _) glueᴾ

  to∘from : ∀ x → to (from x) ≡ x
  to∘from =
    _↔_.from ≡↔≡ ∘
    S.elimᴾ _ P.refl P.refl (λ a i _ → S.meridianᴾ a i)

  from∘to : ∀ x → from (to x) ≡ x
  from∘to =
    _↔_.from ≡↔≡ ∘
    elimᴾ _ (λ _ → P.refl) (λ _ → P.refl) (λ a i _ → glueᴾ a i)
