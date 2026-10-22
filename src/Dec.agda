------------------------------------------------------------------------
-- Some definitions related to Dec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Dec where

open import Logical-equivalence hiding (_∘_)
open import Prelude

private
  variable
    a   : Level
    A B : Type a

mutual

  -- A map function for Dec.

  Dec-map : A ⇔ B → Dec A → Dec B
  Dec-map A⇔B = Dec-map₀ to from
    where
    open _⇔_ A⇔B

  -- A generalisation of Dec-map.

  Dec-map₀ : (A → B) → @0 (B → A) → Dec A → Dec B
  Dec-map₀ to from = ⊎-map to (λ f x → ⊥-elim₀ (f (from x)))

-- Dec preserves logical equivalences.

Dec-preserves : A ⇔ B → Dec A ⇔ Dec B
Dec-preserves A⇔B = record
  { to   = Dec-map A⇔B
  ; from = Dec-map (inverse A⇔B)
  }

-- If A and B are decided, then A × B is.

Dec-× : Dec A → Dec B → Dec (A × B)
Dec-× (yes p) (yes q) = yes (p , q)
Dec-× (no p)  _       = no (p ∘ proj₁)
Dec-× _       (no p)  = no (p ∘ proj₂)

-- If A and B are decided, then A ⊎ B is.

Dec-⊎ : Dec A → Dec B → Dec (A ⊎ B)
Dec-⊎ (yes p) _       = yes (inj₁ p)
Dec-⊎ _       (yes p) = yes (inj₂ p)
Dec-⊎ (no p)  (no q)  = no [ p , q ]

-- If A is decided, then ¬ ¬ A implies A.

decided-stable : Dec A → @0 ¬ ¬ A → A
decided-stable (yes x) _ = x
decided-stable (no f)  g = ⊥-elim₀ (g f)

opaque

  -- If d : Dec A and d is yes something, then A is inhabited.

  Dec→T→ : (d : Dec A) → T d → A
  Dec→T→ (yes p) _ = p
