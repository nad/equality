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
Dec-× =
  [ (λ a → [ (λ b → yes (a , b))
           , (λ ¬b → no (¬b ∘ proj₂))
           ])
  , (λ ¬a _ → no (¬a ∘ proj₁))
  ]

-- If A and B are decided, then A ⊎ B is.

Dec-⊎ : Dec A → Dec B → Dec (A ⊎ B)
Dec-⊎ =
  [ (λ a _ → yes (inj₁ a))
  , (λ ¬a →
       [ (λ b → yes (inj₂ b))
       , (λ ¬b → no [ ¬a , ¬b ])
       ])
  ]
