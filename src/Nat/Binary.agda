------------------------------------------------------------------------
-- A binary representation of natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
import Erased.Basics

module Nat.Binary
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)

  -- An instantiation of the []-cong axioms.
  (ax : ∀ {a} → Erased.Basics.[]-cong-axiomatisation eq a)
  where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_; Dec-map)
open import Prelude hiding (suc; _^_) renaming (_+_ to _⊕_; _*_ to _⊛_)

open import Bijection eq using (_↔_)
open import Equality.Decision-procedures eq
open import Erased eq ax
open import Function-universe eq hiding (id; _∘_)
open import List eq
open import Nat.Solver eq
import Nat.Wrapper eq ax as Wrapper
open import Surjection eq using (_↠_)

private

  module N where
    open import Nat eq public
    open Prelude public using (zero; suc; _^_)

  variable
    A     : Set
    inv n : A
    b     : Bool
    bs    : List Bool

------------------------------------------------------------------------
-- The underlying representation

private

  module Bin′ where

    abstract

      -- The underlying representation of binary natural numbers. The
      -- least significant digit comes first; true stands for one and
      -- false for zero. Leading zeros (at the end of the lists) are
      -- not allowed.
      --
      -- The type is abstract to ensure that a change to a different
      -- representation does not break code that uses this module.

      mutual

        infixr 5 _∷_

        data Bin′ : Set where
          []  : Bin′
          _∷_ : (b : Bool) (n : Bin′)
                { @0 invariant : Invariant b n } → Bin′

        private

          Invariant : Bool → Bin′ → Set
          Invariant true  _       = ⊤
          Invariant false (_ ∷ _) = ⊤
          Invariant false []      = ⊥

          -- A variant of _∷_ with three explicit arguments.

          pattern _∷_⟨_⟩ b n inv = _∷_ b n {invariant = inv}

      private

        -- The underlying list.

        to-List : Bin′ → List Bool
        to-List []       = []
        to-List (b ∷ bs) = b ∷ to-List bs

        -- The invariant implies that the last element in the
        -- underlying list, if any, is not false, so there are no
        -- leading zeros in the number.

        invariant-correct : ∀ n bs → ¬ to-List n ≡ bs ++ false ∷ []
        invariant-correct [] bs =
          [] ≡ bs ++ false ∷ []  ↝⟨ []≢++∷ bs ⟩□
          ⊥                      □
        invariant-correct (true ∷ n) [] =
          true ∷ to-List n ≡ false ∷ []  ↝⟨ List.cancel-∷-head ⟩
          true ≡ false                   ↝⟨ Bool.true≢false ⟩□
          ⊥                              □
        invariant-correct (false ∷ n@(_ ∷ _)) [] =
          false ∷ to-List n ≡ false ∷ []  ↝⟨ List.cancel-∷-tail ⟩
          to-List n ≡ []                  ↝⟨ List.[]≢∷ ∘ sym ⟩□
          ⊥                               □
        invariant-correct (b ∷ n) (b′ ∷ bs) =
          b ∷ to-List n ≡ b′ ∷ bs ++ false ∷ []  ↝⟨ List.cancel-∷-tail ⟩
          to-List n ≡ bs ++ false ∷ []           ↝⟨ invariant-correct n bs ⟩□
          ⊥                                      □

        -- The invariant is propositional.

        Invariant-propositional :
          {b : Bool} {n : Bin′} → Is-proposition (Invariant b n)
        Invariant-propositional {b = true}              _ _ = refl _
        Invariant-propositional {b = false} {n = _ ∷ _} _ _ = refl _

        -- Converts from Bool to ℕ.

        from-Bool : Bool → ℕ
        from-Bool = if_then 1 else 0

        -- Converts from List Bool to ℕ.

        List-to-ℕ : List Bool → ℕ
        List-to-ℕ = foldr (λ b n → from-Bool b ⊕ 2 ⊛ n) 0

      -- Converts from Bin′ to ℕ.

      to-ℕ′ : Bin′ → ℕ
      to-ℕ′ = List-to-ℕ ∘ to-List

      private

        -- A smart constructor.

        infixr 5 _∷ˢ_

        _∷ˢ_ : Bool → Bin′ → Bin′
        true  ∷ˢ n         = true ∷ n
        false ∷ˢ []        = []
        false ∷ˢ n@(_ ∷ _) = false ∷ n

        -- A lemma relating to-ℕ′ and _∷ˢ_.

        to-ℕ′-∷ˢ : ∀ b n → to-ℕ′ (b ∷ˢ n) ≡ from-Bool b ⊕ 2 ⊛ to-ℕ′ n
        to-ℕ′-∷ˢ true  _       = refl _
        to-ℕ′-∷ˢ false []      = refl _
        to-ℕ′-∷ˢ false (_ ∷ _) = refl _

      -- Zero.

      zero′ : Bin′
      zero′ = []

      -- A lemma relating zero′ and N.zero.

      to-ℕ′-zero′ : to-ℕ′ zero′ ≡ N.zero
      to-ℕ′-zero′ = refl _

      -- The number's successor.

      suc′ : Bin′ → Bin′
      suc′ []          = true ∷ˢ []
      suc′ (false ∷ n) = true ∷ˢ n
      suc′ (true  ∷ n) = false ∷ˢ suc′ n

      private

        -- The successor of the smart cons constructor applied to
        -- false and n is the smart cons constructor applied to true
        -- and n.

        suc′-false-∷ˢ : ∀ n → suc′ (false ∷ˢ n) ≡ true ∷ˢ n
        suc′-false-∷ˢ []      = refl _
        suc′-false-∷ˢ (_ ∷ _) = refl _

      -- A lemma relating suc′ and N.suc.

      to-ℕ′-suc′ : ∀ bs → to-ℕ′ (suc′ bs) ≡ N.suc (to-ℕ′ bs)
      to-ℕ′-suc′ []             = refl _
      to-ℕ′-suc′ n@(false ∷ n′) =
        to-ℕ′ (suc′ n)      ≡⟨⟩
        to-ℕ′ (true ∷ˢ n′)  ≡⟨ to-ℕ′-∷ˢ true n′ ⟩
        1 ⊕ 2 ⊛ to-ℕ′ n′    ≡⟨⟩
        N.suc (to-ℕ′ n)     ∎
      to-ℕ′-suc′ n@(true ∷ n′) =
        to-ℕ′ (suc′ n)            ≡⟨⟩
        to-ℕ′ (false ∷ˢ suc′ n′)  ≡⟨ to-ℕ′-∷ˢ false (suc′ n′) ⟩
        2 ⊛ to-ℕ′ (suc′ n′)       ≡⟨ cong (2 ⊛_) (to-ℕ′-suc′ n′) ⟩
        2 ⊛ N.suc (to-ℕ′ n′)      ≡⟨ solve 1 (λ n → con 2 :* (con 1 :+ n) := con 2 :+ con 2 :* n) (refl _) _ ⟩
        2 ⊕ 2 ⊛ to-ℕ′ n′          ≡⟨⟩
        N.suc (to-ℕ′ n)           ∎

      private

        -- Converts from ℕ to Bin′.

        from-ℕ′ : ℕ → Bin′
        from-ℕ′ zero      = []
        from-ℕ′ (N.suc n) = suc′ (from-ℕ′ n)

        -- The function from-ℕ′ commutes with "multiplication by two".

        from-ℕ′-2-⊛ : ∀ n → from-ℕ′ (2 ⊛ n) ≡ false ∷ˢ from-ℕ′ n
        from-ℕ′-2-⊛ zero      = refl _
        from-ℕ′-2-⊛ (N.suc n) =
          from-ℕ′ (2 ⊛ N.suc n)               ≡⟨⟩
          suc′ (from-ℕ′ (n ⊕ N.suc (n ⊕ 0)))  ≡⟨ cong (suc′ ∘ from-ℕ′) $ sym $ N.suc+≡+suc n ⟩
          suc′ (from-ℕ′ (N.suc (2 ⊛ n)))      ≡⟨⟩
          suc′ (suc′ (from-ℕ′ (2 ⊛ n)))       ≡⟨ cong (suc′ ∘ suc′) (from-ℕ′-2-⊛ n) ⟩
          suc′ (suc′ (false ∷ˢ from-ℕ′ n))    ≡⟨ cong suc′ (suc′-false-∷ˢ (from-ℕ′ n)) ⟩
          suc′ (true ∷ˢ from-ℕ′ n)            ≡⟨⟩
          false ∷ˢ suc′ (from-ℕ′ n)           ≡⟨⟩
          false ∷ˢ from-ℕ′ (N.suc n)          ∎

    -- There is a bijection from Bin′ to ℕ.

    Bin′↔ℕ : Bin′ ↔ ℕ
    Bin′↔ℕ = record
      { surjection = record
        { logical-equivalence = record
          { to   = to-ℕ′
          ; from = from-ℕ′
          }
        ; right-inverse-of = to-ℕ′∘from-ℕ′
        }
      ; left-inverse-of = from-ℕ′∘to-ℕ′
      }
      where

      abstract

        to-ℕ′∘from-ℕ′ : ∀ n → to-ℕ′ (from-ℕ′ n) ≡ n
        to-ℕ′∘from-ℕ′ zero      = refl _
        to-ℕ′∘from-ℕ′ (N.suc n) =
          to-ℕ′ (from-ℕ′ (N.suc n))  ≡⟨⟩
          to-ℕ′ (suc′ (from-ℕ′ n))   ≡⟨ to-ℕ′-suc′ (from-ℕ′ n) ⟩
          N.suc (to-ℕ′ (from-ℕ′ n))  ≡⟨ cong N.suc (to-ℕ′∘from-ℕ′ n) ⟩∎
          N.suc n                    ∎

        from-ℕ′∘to-ℕ′ : ∀ n → from-ℕ′ (to-ℕ′ n) ≡ n
        from-ℕ′∘to-ℕ′ [] = refl _

        from-ℕ′∘to-ℕ′ n@(true ∷ n′) =
          from-ℕ′ (to-ℕ′ n)                   ≡⟨⟩
          from-ℕ′ (1 ⊕ 2 ⊛ to-ℕ′ n′)          ≡⟨⟩
          suc′ (from-ℕ′ (2 ⊛ to-ℕ′ n′))       ≡⟨ cong suc′ (from-ℕ′-2-⊛ (to-ℕ′ n′)) ⟩
          suc′ (false ∷ˢ from-ℕ′ (to-ℕ′ n′))  ≡⟨ cong (suc′ ∘ (false ∷ˢ_)) (from-ℕ′∘to-ℕ′ n′) ⟩
          suc′ (false ∷ˢ n′)                  ≡⟨ suc′-false-∷ˢ n′ ⟩
          true ∷ˢ n′                          ≡⟨⟩
          n                                   ∎

        from-ℕ′∘to-ℕ′ n@(false ∷ n′@(_ ∷ _)) =
          from-ℕ′ (to-ℕ′ n)            ≡⟨⟩
          from-ℕ′ (2 ⊛ to-ℕ′ n′)       ≡⟨ from-ℕ′-2-⊛ (to-ℕ′ n′) ⟩
          false ∷ˢ from-ℕ′ (to-ℕ′ n′)  ≡⟨ cong (false ∷ˢ_) (from-ℕ′∘to-ℕ′ n′) ⟩
          false ∷ˢ n′                  ≡⟨⟩
          n                            ∎

    abstract

      private

        -- Helper functions used to implement addition.

        add-with-carryᴮ : Bool → Bool → Bool → Bool × Bool
        add-with-carryᴮ false false false = false , false
        add-with-carryᴮ false false true  = true  , false
        add-with-carryᴮ false true  false = true  , false
        add-with-carryᴮ false true  true  = false , true
        add-with-carryᴮ true  false false = true  , false
        add-with-carryᴮ true  false true  = false , true
        add-with-carryᴮ true  true  false = false , true
        add-with-carryᴮ true  true  true  = true  , true

        add-with-carry₁ : Bool → Bin′ → Bin′
        add-with-carry₁ false = id
        add-with-carry₁ true  = suc′

        add-with-carry₂ : Bool → Bin′ → Bin′ → Bin′
        add-with-carry₂ b []        n  = add-with-carry₁ b n
        add-with-carry₂ b m@(_ ∷ _) [] = add-with-carry₁ b m

        add-with-carry₂ b (c ∷ m) (d ∷ n) =
          case add-with-carryᴮ b c d of λ where
            (e , f) → e ∷ˢ add-with-carry₂ f m n

        to-ℕ′-add-with-carry₁ :
          ∀ b cs →
          to-ℕ′ (add-with-carry₁ b cs) ≡
          from-Bool b ⊕ to-ℕ′ cs
        to-ℕ′-add-with-carry₁ false n = refl _
        to-ℕ′-add-with-carry₁ true  n = to-ℕ′-suc′ n

        to-ℕ′-add-with-carry₂ :
          ∀ b m n →
          to-ℕ′ (add-with-carry₂ b m n) ≡
          from-Bool b ⊕ (to-ℕ′ m ⊕ to-ℕ′ n)
        to-ℕ′-add-with-carry₂ b [] n = to-ℕ′-add-with-carry₁ b n

        to-ℕ′-add-with-carry₂ b m@(_ ∷ _) [] =
          to-ℕ′ (add-with-carry₁ b m)         ≡⟨ to-ℕ′-add-with-carry₁ b m ⟩
          from-Bool b ⊕ to-ℕ′ m               ≡⟨ solve 2 (λ b c → b :+ c := b :+ (c :+ con 0)) (refl _) (from-Bool b) _ ⟩
          from-Bool b ⊕ (to-ℕ′ m ⊕ 0)         ≡⟨⟩
          from-Bool b ⊕ (to-ℕ′ m ⊕ to-ℕ′ [])  ∎

        to-ℕ′-add-with-carry₂ false m@(false ∷ m′) n@(false ∷ n′) =
          to-ℕ′ (false ∷ˢ add-with-carry₂ false m′ n′)  ≡⟨ to-ℕ′-∷ˢ false (add-with-carry₂ false m′ n′) ⟩
          2 ⊛ to-ℕ′ (add-with-carry₂ false m′ n′)       ≡⟨ cong (2 ⊛_) (to-ℕ′-add-with-carry₂ false m′ n′) ⟩
          2 ⊛ (to-ℕ′ m′ ⊕ to-ℕ′ n′)                     ≡⟨ solve 2 (λ c d → con 2 :* (c :+ d) :=
                                                                            con 2 :* c :+ con 2 :* d)
                                                                 (refl _) (to-ℕ′ m′) _ ⟩
          2 ⊛ to-ℕ′ m′ ⊕ 2 ⊛ to-ℕ′ n′                   ≡⟨⟩
          to-ℕ′ m ⊕ to-ℕ′ n       ∎

        to-ℕ′-add-with-carry₂ false m@(false ∷ m′) n@(true  ∷ n′) =
          to-ℕ′ (true ∷ˢ add-with-carry₂ false m′ n′)  ≡⟨ to-ℕ′-∷ˢ true (add-with-carry₂ false m′ n′) ⟩
          1 ⊕ 2 ⊛ to-ℕ′ (add-with-carry₂ false m′ n′)  ≡⟨ cong ((1 ⊕_) ∘ (2 ⊛_)) (to-ℕ′-add-with-carry₂ false m′ n′) ⟩
          1 ⊕ 2 ⊛ (to-ℕ′ m′ ⊕ to-ℕ′ n′)                ≡⟨ solve 2 (λ c d → con 1 :+ con 2 :* (c :+ d) :=
                                                                           con 2 :* c :+ (con 1 :+ con 2 :* d))
                                                                (refl _) (to-ℕ′ m′) _ ⟩
          2 ⊛ to-ℕ′ m′ ⊕ (1 ⊕ 2 ⊛ to-ℕ′ n′)            ≡⟨⟩
          to-ℕ′ m ⊕ to-ℕ′ n       ∎

        to-ℕ′-add-with-carry₂ false m@(true  ∷ m′) n@(false ∷ n′) =
          to-ℕ′ (true ∷ˢ add-with-carry₂ false m′ n′)  ≡⟨ to-ℕ′-∷ˢ true (add-with-carry₂ false m′ n′) ⟩
          1 ⊕ 2 ⊛ to-ℕ′ (add-with-carry₂ false m′ n′)  ≡⟨ cong ((1 ⊕_) ∘ (2 ⊛_)) (to-ℕ′-add-with-carry₂ false m′ n′) ⟩
          1 ⊕ 2 ⊛ (to-ℕ′ m′ ⊕ to-ℕ′ n′)                ≡⟨ solve 2 (λ c d → con 1 :+ con 2 :* (c :+ d) :=
                                                                           con 1 :+ con 2 :* c :+ con 2 :* d)
                                                                (refl _) (to-ℕ′ m′) _ ⟩
          1 ⊕ 2 ⊛ to-ℕ′ m′ ⊕ 2 ⊛ to-ℕ′ n′              ≡⟨⟩
          to-ℕ′ m ⊕ to-ℕ′ n                            ∎

        to-ℕ′-add-with-carry₂ false m@(true ∷ m′) n@(true ∷ n′) =
          to-ℕ′ (false ∷ˢ add-with-carry₂ true m′ n′)  ≡⟨ to-ℕ′-∷ˢ false (add-with-carry₂ true m′ n′) ⟩
          2 ⊛ to-ℕ′ (add-with-carry₂ true m′ n′)       ≡⟨ cong (2 ⊛_) (to-ℕ′-add-with-carry₂ true m′ n′) ⟩
          2 ⊛ (1 ⊕ to-ℕ′ m′ ⊕ to-ℕ′ n′)                ≡⟨ solve 2 (λ c d → con 2 :* (con 1 :+ c :+ d) :=
                                                                           con 1 :+ con 2 :* c :+ (con 1 :+ con 2 :* d))
                                                                (refl _) (to-ℕ′ m′) _ ⟩
          1 ⊕ 2 ⊛ to-ℕ′ m′ ⊕ (1 ⊕ 2 ⊛ to-ℕ′ n′)        ≡⟨⟩
          to-ℕ′ m ⊕ to-ℕ′ n                            ∎

        to-ℕ′-add-with-carry₂ true m@(false ∷ m′) n@(false ∷ n′) =
          to-ℕ′ (true ∷ˢ add-with-carry₂ false m′ n′)  ≡⟨ to-ℕ′-∷ˢ true (add-with-carry₂ false m′ n′) ⟩
          1 ⊕ 2 ⊛ to-ℕ′ (add-with-carry₂ false m′ n′)  ≡⟨ cong ((1 ⊕_) ∘ (2 ⊛_)) (to-ℕ′-add-with-carry₂ false m′ n′) ⟩
          1 ⊕ 2 ⊛ (to-ℕ′ m′ ⊕ to-ℕ′ n′)                ≡⟨ solve 2 (λ c d → con 1 :+ con 2 :* (c :+ d) :=
                                                                           con 1 :+ con 2 :* c :+ con 2 :* d)
                                                                (refl _) (to-ℕ′ m′) _ ⟩
          1 ⊕ 2 ⊛ to-ℕ′ m′ ⊕ 2 ⊛ to-ℕ′ n′              ≡⟨⟩
          1 ⊕ to-ℕ′ m ⊕ to-ℕ′ n                        ∎

        to-ℕ′-add-with-carry₂ true m@(false ∷ m′) n@(true  ∷ n′) =
          to-ℕ′ (false ∷ˢ add-with-carry₂ true m′ n′)  ≡⟨ to-ℕ′-∷ˢ false (add-with-carry₂ true m′ n′) ⟩
          2 ⊛ to-ℕ′ (add-with-carry₂ true m′ n′)       ≡⟨ cong (2 ⊛_) (to-ℕ′-add-with-carry₂ true m′ n′) ⟩
          2 ⊛ (1 ⊕ to-ℕ′ m′ ⊕ to-ℕ′ n′)                ≡⟨ solve 2 (λ c d → con 2 :* (con 1 :+ c :+ d) :=
                                                                           con 1 :+ con 2 :* c :+ (con 1 :+ con 2 :* d))
                                                                (refl _) (to-ℕ′ m′) _ ⟩
          1 ⊕ 2 ⊛ to-ℕ′ m′ ⊕ (1 ⊕ 2 ⊛ to-ℕ′ n′)        ≡⟨⟩
          1 ⊕ to-ℕ′ m ⊕ to-ℕ′ n                        ∎

        to-ℕ′-add-with-carry₂ true m@(true  ∷ m′) n@(false ∷ n′) =
          to-ℕ′ (false ∷ˢ add-with-carry₂ true m′ n′)  ≡⟨ to-ℕ′-∷ˢ false (add-with-carry₂ true m′ n′) ⟩
          2 ⊛ to-ℕ′ (add-with-carry₂ true m′ n′)       ≡⟨ cong (2 ⊛_) (to-ℕ′-add-with-carry₂ true m′ n′) ⟩
          2 ⊛ (1 ⊕ to-ℕ′ m′ ⊕ to-ℕ′ n′)                ≡⟨ solve 2 (λ c d → con 2 :* (con 1 :+ c :+ d) :=
                                                                           con 2 :+ con 2 :* c :+ con 2 :* d)
                                                                (refl _) (to-ℕ′ m′) _ ⟩
          2 ⊕ 2 ⊛ to-ℕ′ m′ ⊕ 2 ⊛ to-ℕ′ n′              ≡⟨⟩
          1 ⊕ to-ℕ′ m ⊕ to-ℕ′ n                        ∎

        to-ℕ′-add-with-carry₂ true m@(true ∷ m′) n@(true ∷ n′) =
          to-ℕ′ (true ∷ˢ add-with-carry₂ true m′ n′)  ≡⟨ to-ℕ′-∷ˢ true (add-with-carry₂ true m′ n′) ⟩
          1 ⊕ 2 ⊛ to-ℕ′ (add-with-carry₂ true m′ n′)  ≡⟨ cong ((1 ⊕_) ∘ (2 ⊛_)) (to-ℕ′-add-with-carry₂ true m′ n′) ⟩
          1 ⊕ 2 ⊛ (1 ⊕ to-ℕ′ m′ ⊕ to-ℕ′ n′)           ≡⟨ solve 2 (λ c d → con 1 :+ con 2 :* (con 1 :+ c :+ d) :=
                                                                          con 2 :+ con 2 :* c :+ (con 1 :+ con 2 :* d))
                                                               (refl _) (to-ℕ′ m′) _ ⟩
          2 ⊕ 2 ⊛ to-ℕ′ m′ ⊕ (1 ⊕ 2 ⊛ to-ℕ′ n′)       ≡⟨⟩
          1 ⊕ to-ℕ′ m ⊕ to-ℕ′ n                       ∎

      -- Addition.

      add-with-carry : Bin′ → Bin′ → Bin′
      add-with-carry = add-with-carry₂ false

      to-ℕ′-add-with-carry :
        ∀ m n →
        to-ℕ′ (add-with-carry m n) ≡
        to-ℕ′ m ⊕ to-ℕ′ n
      to-ℕ′-add-with-carry = to-ℕ′-add-with-carry₂ false

      -- Division by two, rounded downwards.

      ⌊_/2⌋ : Bin′ → Bin′
      ⌊ []    /2⌋ = []
      ⌊ _ ∷ n /2⌋ = n

      to-ℕ′-⌊/2⌋ : ∀ n → to-ℕ′ ⌊ n /2⌋ ≡ N.⌊ to-ℕ′ n /2⌋
      to-ℕ′-⌊/2⌋ []          = refl _
      to-ℕ′-⌊/2⌋ (false ∷ n) =
        to-ℕ′ n              ≡⟨ sym $ N.⌊2*/2⌋≡ _ ⟩∎
        N.⌊ 2 ⊛ to-ℕ′ n /2⌋  ∎

      to-ℕ′-⌊/2⌋ (true ∷ n) =
        to-ℕ′ n                  ≡⟨ sym $ N.⌊1+2*/2⌋≡ _ ⟩∎
        N.⌊ 1 ⊕ 2 ⊛ to-ℕ′ n /2⌋  ∎

      -- Division by two, rounded upwards.

      ⌈_/2⌉ : Bin′ → Bin′
      ⌈ []        /2⌉ = []
      ⌈ false ∷ n /2⌉ = n
      ⌈ true  ∷ n /2⌉ = suc′ n

      to-ℕ′-⌈/2⌉ : ∀ n → to-ℕ′ ⌈ n /2⌉ ≡ N.⌈ to-ℕ′ n /2⌉
      to-ℕ′-⌈/2⌉ []          = refl _
      to-ℕ′-⌈/2⌉ (false ∷ n) =
        to-ℕ′ n              ≡⟨ sym $ N.⌈2*/2⌉≡ _ ⟩∎
        N.⌈ 2 ⊛ to-ℕ′ n /2⌉  ∎

      to-ℕ′-⌈/2⌉ (true ∷ n) =
        to-ℕ′ (suc′ n)           ≡⟨ to-ℕ′-suc′ n ⟩
        1 ⊕ to-ℕ′ n              ≡⟨ sym $ N.⌈1+2*/2⌉≡ _ ⟩∎
        N.⌈ 1 ⊕ 2 ⊛ to-ℕ′ n /2⌉  ∎

      -- Multiplication.

      infixl 7 _*_

      _*_ : Bin′ → Bin′ → Bin′
      []      * n = zero′
      (b ∷ m) * n =
        (if b then add-with-carry n else id)
          (false ∷ˢ m * n)

      to-ℕ′-* : ∀ m n → to-ℕ′ (m * n) ≡ to-ℕ′ m ⊛ to-ℕ′ n
      to-ℕ′-* []                  n = refl _
      to-ℕ′-* (false ∷ m ⟨ inv ⟩) n =
        to-ℕ′ (false ∷ˢ m * n)               ≡⟨ to-ℕ′-∷ˢ false (m * n) ⟩
        2 ⊛ to-ℕ′ (m * n)                    ≡⟨ cong (2 ⊛_) (to-ℕ′-* m _) ⟩
        2 ⊛ (to-ℕ′ m ⊛ to-ℕ′ n)              ≡⟨ N.*-assoc 2 {n = to-ℕ′ m} ⟩
        (2 ⊛ to-ℕ′ m) ⊛ to-ℕ′ n              ≡⟨⟩
        to-ℕ′ (false ∷ m ⟨ inv ⟩) ⊛ to-ℕ′ n  ∎
      to-ℕ′-* (true ∷ m) n =
        to-ℕ′ (add-with-carry n (false ∷ˢ m * n))  ≡⟨ to-ℕ′-add-with-carry n _ ⟩
        to-ℕ′ n ⊕ to-ℕ′ (false ∷ˢ m * n)           ≡⟨ cong (to-ℕ′ n ⊕_) (to-ℕ′-∷ˢ false (m * n)) ⟩
        to-ℕ′ n ⊕ 2 ⊛ to-ℕ′ (m * n)                ≡⟨ cong (λ x → to-ℕ′ n ⊕ 2 ⊛ x) (to-ℕ′-* m _) ⟩
        to-ℕ′ n ⊕ 2 ⊛ (to-ℕ′ m ⊛ to-ℕ′ n)          ≡⟨ solve 2 (λ m n → n :+ con 2 :* (m :* n) :=
                                                                       (con 1 :+ con 2 :* m) :* n)
                                                            (refl _) (to-ℕ′ m) _ ⟩
        (1 ⊕ 2 ⊛ to-ℕ′ m) ⊛ to-ℕ′ n                ≡⟨⟩
        to-ℕ′ (true ∷ m) ⊛ to-ℕ′ n                 ∎

      -- Exponentiation.

      infixr 8 _^_

      _^_ : Bin′ → Bin′ → Bin′
      m ^ []      = suc′ zero′
      m ^ (b ∷ n) =
        (if b then (m *_) else id)
          ((m * m) ^ n)

      to-ℕ′-^ : ∀ m n → to-ℕ′ (m ^ n) ≡ to-ℕ′ m N.^ to-ℕ′ n
      to-ℕ′-^ m []                  = refl _
      to-ℕ′-^ m (false ∷ n ⟨ inv ⟩) =
        to-ℕ′ (m ^ (false ∷ n ⟨ inv ⟩))        ≡⟨⟩
        to-ℕ′ ((m * m) ^ n)                    ≡⟨ to-ℕ′-^ (m * m) n ⟩
        to-ℕ′ (m * m) N.^ to-ℕ′ n              ≡⟨ cong (N._^ to-ℕ′ n) (to-ℕ′-* m m) ⟩
        (to-ℕ′ m ⊛ to-ℕ′ m) N.^ to-ℕ′ n        ≡⟨ cong (λ x → (to-ℕ′ m ⊛ x) N.^ to-ℕ′ n) (sym (N.*-right-identity (to-ℕ′ m))) ⟩
        (to-ℕ′ m N.^ 2) N.^ to-ℕ′ n            ≡⟨ N.^^≡^* 2 {k = to-ℕ′ n} ⟩
        to-ℕ′ m N.^ (2 ⊛ to-ℕ′ n)              ≡⟨⟩
        to-ℕ′ m N.^ to-ℕ′ (false ∷ n ⟨ inv ⟩)  ∎
      to-ℕ′-^ m (true ∷ n) =
        to-ℕ′ (m ^ (true ∷ n))                     ≡⟨⟩
        to-ℕ′ (m * (m * m) ^ n)                    ≡⟨ to-ℕ′-* m ((m * m) ^ n) ⟩
        to-ℕ′ m ⊛ to-ℕ′ ((m * m) ^ n)              ≡⟨ cong (to-ℕ′ m ⊛_) (to-ℕ′-^ (m * m) n) ⟩
        to-ℕ′ m ⊛ to-ℕ′ (m * m) N.^ to-ℕ′ n        ≡⟨ cong (λ x → to-ℕ′ m ⊛ x N.^ to-ℕ′ n) (to-ℕ′-* m m) ⟩
        to-ℕ′ m ⊛ (to-ℕ′ m ⊛ to-ℕ′ m) N.^ to-ℕ′ n  ≡⟨ cong (λ x → to-ℕ′ m ⊛ (to-ℕ′ m ⊛ x) N.^ to-ℕ′ n) (sym (N.*-right-identity (to-ℕ′ m))) ⟩
        to-ℕ′ m ⊛ (to-ℕ′ m N.^ 2) N.^ to-ℕ′ n      ≡⟨ cong₂ _⊛_ (sym (N.^-right-identity {n = to-ℕ′ m})) (N.^^≡^* 2 {k = to-ℕ′ n}) ⟩
        to-ℕ′ m N.^ 1 ⊛ to-ℕ′ m N.^ (2 ⊛ to-ℕ′ n)  ≡⟨ sym $ N.^+≡^*^ {m = to-ℕ′ m} 1 {k = 2 ⊛ to-ℕ′ n} ⟩
        to-ℕ′ m N.^ (1 ⊕ 2 ⊛ to-ℕ′ n)              ≡⟨⟩
        to-ℕ′ m N.^ to-ℕ′ (true ∷ n)               ∎

      -- "Left shift".

      infixl 8 _*2^_

      _*2^_ : Bin′ → ℕ → Bin′
      m *2^ zero    = m
      m *2^ N.suc n = (false ∷ˢ m) *2^ n

      to-ℕ′-*2^ :
        ∀ m n →
        to-ℕ′ (m *2^ n) ≡
        to-ℕ′ m ⊛ 2 N.^ n
      to-ℕ′-*2^ m zero =
        to-ℕ′ m      ≡⟨ sym $ N.*-right-identity _ ⟩∎
        to-ℕ′ m ⊛ 1  ∎
      to-ℕ′-*2^ m (N.suc n) =
        to-ℕ′ ((false ∷ˢ m) *2^ n)    ≡⟨ to-ℕ′-*2^ (false ∷ˢ m) n ⟩
        to-ℕ′ (false ∷ˢ m) ⊛ 2 N.^ n  ≡⟨ cong (_⊛ _) $ to-ℕ′-∷ˢ false m ⟩
        2 ⊛ to-ℕ′ m ⊛ 2 N.^ n         ≡⟨ cong (_⊛ (2 N.^ n)) $ N.*-comm 2 {n = to-ℕ′ m} ⟩
        to-ℕ′ m ⊛ 2 ⊛ 2 N.^ n         ≡⟨ sym $ N.*-assoc (to-ℕ′ m) ⟩∎
        to-ℕ′ m ⊛ 2 N.^ N.suc n       ∎

      private

        -- The empty list is not equal to any non-empty list.

        []≢∷ : ([] ⦂ Bin′) ≢ b ∷ n ⟨ inv ⟩
        []≢∷ {b = b} {n = n} =
          [] ≡ b ∷ n          ↝⟨ cong to-List ⟩
          [] ≡ b ∷ to-List n  ↝⟨ List.[]≢∷ ⟩□
          ⊥                   □

        -- Equality is decidable for Bin′.
        --
        -- This definition uses Dec-Erased instead of Dec ∘ Erased
        -- because I thought this made the code a little less
        -- complicated.

        equal? : (m n : Bin′) → Dec-Erased (m ≡ n)
        equal? [] [] = yes [ refl _ ]

        equal? [] (b ∷ n) = no [ []≢∷ ]

        equal? (b ∷ n) [] = no [ []≢∷ ∘ sym ]

        equal? (b₁ ∷ n₁) (b₂ ∷ n₂) =
          helper₁ _ _ (b₁ Bool.≟ b₂)
          where
          helper₂ :
            ∀ n₁ n₂
            (@0 inv₁ : Invariant b₁ n₁) (@0 inv₂ : Invariant b₂ n₂) →
            b₁ ≡ b₂ →
            Dec-Erased (n₁ ≡ n₂) →
            Dec-Erased ((b₁ ∷ n₁ ⟨ inv₁ ⟩) ≡ (b₂ ∷ n₂ ⟨ inv₂ ⟩))
          helper₂ n₁ n₂ _ _ _ (no [ n₁≢n₂ ]) = no [
            (b₁ ∷ n₁ ⟨ _ ⟩) ≡ (b₂ ∷ n₂ ⟨ _ ⟩)  ↝⟨ cong to-List ⟩
            b₁ ∷ to-List n₁ ≡ b₂ ∷ to-List n₂  ↝⟨ List.cancel-∷-tail ⟩
            to-List n₁ ≡ to-List n₂            ↝⟨ cong List-to-ℕ ⟩
            to-ℕ′ n₁ ≡ to-ℕ′ n₂                ↝⟨ _↔_.injective Bin′↔ℕ ⟩
            n₁ ≡ n₂                            ↝⟨ n₁≢n₂ ⟩□
            ⊥                                  □ ]

          helper₂ n₁ n₂ inv₁ inv₂ b₁≡b₂ (yes [ n₁≡n₂ ]) = yes [  $⟨ b₁≡b₂ , n₁≡n₂ ⟩
            b₁ ≡ b₂ × n₁ ≡ n₂                                    ↝⟨ Σ-map id (cong to-List) ⟩
            b₁ ≡ b₂ × to-List n₁ ≡ to-List n₂                    ↔⟨ inverse ∷≡∷↔≡×≡ ⟩
            b₁ ∷ to-List n₁ ≡ b₂ ∷ to-List n₂                    ↝⟨ cong List-to-ℕ ⟩
            to-ℕ′ (b₁ ∷ n₁ ⟨ inv₁ ⟩) ≡ to-ℕ′ (b₂ ∷ n₂ ⟨ inv₂ ⟩)  ↝⟨ _↔_.injective Bin′↔ℕ ⟩□
            b₁ ∷ n₁ ≡ b₂ ∷ n₂                                    □ ]

          helper₁ :
            ∀ n₁ n₂
              {@0 inv₁ : Invariant b₁ n₁} {@0 inv₂ : Invariant b₂ n₂} →
            Dec (b₁ ≡ b₂) →
            Dec-Erased ((b₁ ∷ n₁ ⟨ inv₁ ⟩) ≡ (b₂ ∷ n₂ ⟨ inv₂ ⟩))
          helper₁ n₁ n₂ (yes b₁≡b₂) =
            helper₂ _ _ _ _ b₁≡b₂ (equal? n₁ n₂)

          helper₁ n₁ n₂ (no b₁≢b₂) = no [
            b₁ ∷ n₁ ≡ b₂ ∷ n₂                  ↝⟨ cong to-List ⟩
            b₁ ∷ to-List n₁ ≡ b₂ ∷ to-List n₂  ↝⟨ List.cancel-∷-head ⟩
            b₁ ≡ b₂                            ↝⟨ b₁≢b₂ ⟩□
            ⊥                                  □ ]

      -- An equality test.

      infix 4 _≟_

      _≟_ : (m n : Bin′) → Dec (Erased (to-ℕ′ m ≡ to-ℕ′ n))
      m ≟ n =                             $⟨ equal? m n ⟩
        Dec-Erased (m ≡ n)                ↝⟨ Dec-Erased-map lemma ⟩
        Dec-Erased (to-ℕ′ m ≡ to-ℕ′ n)    ↝⟨ Dec-Erased↔Dec-Erased _ ⟩□
        Dec (Erased (to-ℕ′ m ≡ to-ℕ′ n))  □
        where
        lemma : m ≡ n ⇔ to-ℕ′ m ≡ to-ℕ′ n
        lemma = record { to = cong to-ℕ′; from = _↔_.injective Bin′↔ℕ }

      private

        -- A lemma used to prove that from-bits and to-bits are
        -- correct.

        to-ℕ′-foldr-∷ˢ-[] :
          ∀ bs →
          to-ℕ′ (foldr _∷ˢ_ [] bs) ≡
          foldr (λ b n → from-Bool b ⊕ 2 ⊛ n) 0 bs
        to-ℕ′-foldr-∷ˢ-[] []       = refl _
        to-ℕ′-foldr-∷ˢ-[] (b ∷ bs) =
          to-ℕ′ (foldr _∷ˢ_ [] (b ∷ bs))                              ≡⟨⟩
          to-ℕ′ (b ∷ˢ foldr _∷ˢ_ [] bs)                               ≡⟨ to-ℕ′-∷ˢ b _ ⟩
          from-Bool b ⊕ 2 ⊛ to-ℕ′ (foldr _∷ˢ_ [] bs)                  ≡⟨ cong (λ n → from-Bool b ⊕ 2 ⊛ n) (to-ℕ′-foldr-∷ˢ-[] bs) ⟩
          from-Bool b ⊕ 2 ⊛ foldr (λ b n → from-Bool b ⊕ 2 ⊛ n) 0 bs  ≡⟨⟩
          foldr (λ b n → from-Bool b ⊕ 2 ⊛ n) 0 (b ∷ bs)              ∎

      -- Converts from lists of bits. (The most significant bit comes
      -- first.)

      from-bits : List Bool → Bin′
      from-bits = foldr _∷ˢ_ [] ∘ reverse

      to-ℕ′-from-bits :
        ∀ bs →
        to-ℕ′ (from-bits bs) ≡
        foldl (λ n b → (if b then 1 else 0) ⊕ 2 ⊛ n) 0 bs
      to-ℕ′-from-bits bs =
        to-ℕ′ (from-bits bs)                                ≡⟨⟩
        to-ℕ′ (foldr _∷ˢ_ [] (reverse bs))                  ≡⟨ to-ℕ′-foldr-∷ˢ-[] (reverse bs) ⟩
        foldr (λ b n → from-Bool b ⊕ 2 ⊛ n) 0 (reverse bs)  ≡⟨ foldr-reverse bs ⟩∎
        foldl (λ n b → from-Bool b ⊕ 2 ⊛ n) 0 bs            ∎

      -- Converts to lists of bits. (The most significant bit comes
      -- first.)

      to-bits : Bin′ → List Bool
      to-bits = reverse ∘ to-List

      to-ℕ′-from-bits-to-bits :
        ∀ n → to-ℕ′ (from-bits (to-bits n)) ≡ to-ℕ′ n
      to-ℕ′-from-bits-to-bits n =
        to-ℕ′ (foldr _∷ˢ_ [] (reverse (reverse (to-List n))))  ≡⟨ cong (to-ℕ′ ∘ foldr _∷ˢ_ []) (reverse-reverse (to-List n)) ⟩
        to-ℕ′ (foldr _∷ˢ_ [] (to-List n))                      ≡⟨ to-ℕ′-foldr-∷ˢ-[] (to-List n) ⟩
        foldr (λ b n → from-Bool b ⊕ 2 ⊛ n) 0 (to-List n)      ≡⟨⟩
        to-ℕ′ n                                                ∎

------------------------------------------------------------------------
-- Binary natural numbers

private

  module Bin-wrapper = Wrapper Bin′.Bin′ Bin′.Bin′↔ℕ
  open Bin-wrapper using (Operations)

-- Some definitions from Nat.Wrapper are reexported.

open Bin-wrapper public
  using (⌊_⌋; ≡-for-indices↔≡; ⌈_⌉; ≡⌊⌋;
         nullary-[]; nullary; nullary-correct;
         unary-[]; unary; unary-correct;
         binary-[]; binary; binary-correct;
         n-ary-[]; n-ary; n-ary-correct)
  renaming
    ( Nat-[_] to Bin-[_]
    ; Nat-[]-propositional to Bin-[]-propositional
    ; Nat to Bin
    ; Nat-[]↔Σℕ to Bin-[]↔Σℕ
    ; Nat↔ℕ to Bin↔ℕ
    )

private

  -- An implementation of some operations for Bin′.

  Operations-for-Bin′ : Operations
  Operations-for-Bin′ = λ where
    .Operations.zero                   → Bin′.zero′
    .Operations.to-ℕ-zero              → Bin′.to-ℕ′-zero′
    .Operations.suc                    → Bin′.suc′
    .Operations.to-ℕ-suc               → Bin′.to-ℕ′-suc′
    .Operations._+_                    → Bin′.add-with-carry
    .Operations.to-ℕ-+                 → Bin′.to-ℕ′-add-with-carry
    .Operations._*_                    → Bin′._*_
    .Operations.to-ℕ-*                 → Bin′.to-ℕ′-*
    .Operations._^_                    → Bin′._^_
    .Operations.to-ℕ-^                 → Bin′.to-ℕ′-^
    .Operations.⌊_/2⌋                  → Bin′.⌊_/2⌋
    .Operations.to-ℕ-⌊/2⌋              → Bin′.to-ℕ′-⌊/2⌋
    .Operations.⌈_/2⌉                  → Bin′.⌈_/2⌉
    .Operations.to-ℕ-⌈/2⌉              → Bin′.to-ℕ′-⌈/2⌉
    .Operations._*2^_                  → Bin′._*2^_
    .Operations.to-ℕ-*2^               → Bin′.to-ℕ′-*2^
    .Operations._≟_                    → Bin′._≟_
    .Operations.from-bits              → Bin′.from-bits
    .Operations.to-ℕ-from-bits         → Bin′.to-ℕ′-from-bits
    .Operations.to-bits                → Bin′.to-bits
    .Operations.to-ℕ-from-bits-to-bits → Bin′.to-ℕ′-from-bits-to-bits

-- Operations for Bin-[_].

module Operations-for-Bin-[] =
  Bin-wrapper.Operations-for-Nat-[] Operations-for-Bin′

-- Operations for Bin.

module Operations-for-Bin =
  Bin-wrapper.Operations-for-Nat Operations-for-Bin′

------------------------------------------------------------------------
-- Some examples

private

  module Bin-[]-examples where

    open Operations-for-Bin-[]

    -- Converts unary natural numbers to binary natural numbers.

    from-ℕ : ∀ n → Bin-[ n ]
    from-ℕ = proj₂ ∘ _↔_.from Bin↔ℕ

    -- Bin n is a proposition, so it is easy to prove that two values
    -- of this type are equal.

    example₁ : from-ℕ 4 + ⌊ from-ℕ 12 /2⌋ ≡ from-ℕ 10
    example₁ = Bin-[]-propositional _ _

    -- However, stating that two values of type Bin m and Bin n are
    -- equal, for equal natural numbers m and n, can be awkward.

    @0 example₂ :
      {@0 m n : ℕ}
      (b : Bin-[ m ]) (c : Bin-[ n ]) →
      subst (λ n → Bin-[ n ]) (N.+-comm m) (b + c) ≡ c + b
    example₂ _ _ = Bin-[]-propositional _ _

  module Bin-examples where

    open Operations-for-Bin

    -- If Bin is used instead of Bin-[_], then it can be easier to
    -- state that two values are equal.

    example₁ : ⌈ 4 ⌉ + ⌊ ⌈ 12 ⌉ /2⌋ ≡ ⌈ 10 ⌉
    example₁ = _↔_.to ≡-for-indices↔≡ [ refl _ ]

    example₂ : ∀ m n → m + n ≡ n + m
    example₂ m n = _↔_.to ≡-for-indices↔≡
      [ ⌊ m ⌋ ⊕ ⌊ n ⌋  ≡⟨ N.+-comm ⌊ m ⌋ ⟩∎
        ⌊ n ⌋ ⊕ ⌊ m ⌋  ∎
      ]

    -- One can construct a proof showing that ⌈ 5 ⌉ is either equal or
    -- not equal to ⌈ 2 ⌉ + ⌈ 3 ⌉, but the proof does not compute to
    -- "inj₁ something" at compile-time.

    example₃ : Dec (⌈ 5 ⌉ ≡ ⌈ 2 ⌉ + ⌈ 3 ⌉)
    example₃ =
      Dec-map (_↔_.logical-equivalence ≡-for-indices↔≡)
        (⌈ 5 ⌉ ≟ ⌈ 2 ⌉ + ⌈ 3 ⌉)
