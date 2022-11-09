------------------------------------------------------------------------
-- Some definitions related to the binary sum type former
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Sum {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

private
  variable
    a               : Level
    A B C D         : Type a
    x y             : A
    f f₁ f₂ g g₁ g₂ : A → B

-- Functor laws.

⊎-map-id : ⊎-map id id x ≡ x
⊎-map-id {x = inj₁ _} = refl _
⊎-map-id {x = inj₂ _} = refl _

⊎-map-∘ :
  ∀ x → ⊎-map (f₁ ∘ g₁) (f₂ ∘ g₂) x ≡ ⊎-map f₁ f₂ (⊎-map g₁ g₂ x)
⊎-map-∘ = [ (λ _ → refl _) , (λ _ → refl _) ]

-- If A can be decided, then ¬ A can be decided.

dec-¬ : Dec A → Dec (¬ A)
dec-¬ (yes p) = no (_$ p)
dec-¬ (no  p) = yes p

-- A simplification lemma related to if_then_else_ and ⊎-map.

if-⊎-map-then-else :
  ∀ b →
  if ⊎-map f g b then x else y ≡ if b then x else y
if-⊎-map-then-else (yes _) = refl _
if-⊎-map-then-else (no  _) = refl _

-- Non-dependent function application commutes with if_then_else_.

if-then-else-commutes :
  (f : C → D) (b : A ⊎ B) →
  f (if b then x else y) ≡ if b then f x else f y
if-then-else-commutes _ (yes _) = refl _
if-then-else-commutes _ (no  _) = refl _
