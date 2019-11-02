------------------------------------------------------------------------
-- A binary representation of natural numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality

module Nat.Binary
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_; Dec-map)
open import Prelude hiding (suc) renaming (_+_ to _⊕_; _*_ to _⊛_)

open import Bijection eq using (_↔_)
open import Equality.Decision-procedures eq
open import Erased.Cubical eq
open import Function-universe eq hiding (_∘_)
open import List eq
import Nat eq as Nat
open import Nat.Solver eq
import Nat.Wrapper eq as Wrapper
open import Surjection eq using (_↠_)

private

  module N where
    open import Nat eq public
    open Prelude public using (zero; suc)

------------------------------------------------------------------------
-- The underlying representation

private

  module Bin′ where

    abstract

      -- The underlying representation of binary natural numbers. The
      -- least significant digit comes first; true stands for one and
      -- false for zero. Leading zeros (at the end of the lists) and
      -- empty lists are allowed, so the representation of a given
      -- natural number is never unique.
      --
      -- The type is abstract to ensure that a change to a different
      -- representation (for instance a variant without leading zeros)
      -- does not break code that uses this module.

      Bin′ : Set
      Bin′ = List Bool

      private

        -- Converts from Bool to ℕ.

        from-Bool : Bool → ℕ
        from-Bool = if_then 1 else 0

      -- Converts from Bin′ to ℕ.

      to-ℕ′ : Bin′ → ℕ
      to-ℕ′ = foldr (λ b n → from-Bool b ⊕ 2 ⊛ n) 0

      -- One representation of zero.

      zero′ : Bin′
      zero′ = []

      -- A lemma relating zero′ and N.zero.

      to-ℕ′-zero′ : to-ℕ′ zero′ ≡ N.zero
      to-ℕ′-zero′ = refl _

      -- One of the number's successors.

      suc′ : Bin′ → Bin′
      suc′ []           = true ∷ []
      suc′ (false ∷ bs) = true ∷ bs
      suc′ (true  ∷ bs) = false ∷ suc′ bs

      -- A lemma relating suc′ and N.suc.

      to-ℕ′-suc′ : ∀ bs → to-ℕ′ (suc′ bs) ≡ N.suc (to-ℕ′ bs)
      to-ℕ′-suc′ []           = refl _
      to-ℕ′-suc′ (false ∷ bs) =
        to-ℕ′ (suc′ (false ∷ bs))   ≡⟨⟩
        to-ℕ′ (true ∷ bs)           ≡⟨⟩
        1 ⊕ 2 ⊛ to-ℕ′ bs            ≡⟨⟩
        N.suc (to-ℕ′ (false ∷ bs))  ∎
      to-ℕ′-suc′ (true ∷ bs) =
        to-ℕ′ (suc′ (true ∷ bs))   ≡⟨⟩
        to-ℕ′ (false ∷ suc′ bs)    ≡⟨⟩
        2 ⊛ to-ℕ′ (suc′ bs)        ≡⟨ cong (2 ⊛_) (to-ℕ′-suc′ bs) ⟩
        2 ⊛ N.suc (to-ℕ′ bs)       ≡⟨ solve 1 (λ n → con 2 :* (con 1 :+ n) := con 2 :+ con 2 :* n) (refl _) _ ⟩
        2 ⊕ 2 ⊛ to-ℕ′ bs           ≡⟨⟩
        N.suc (to-ℕ′ (true ∷ bs))  ∎

    -- There is a split surjection from Bin′ to ℕ.

    Bin′↠ℕ : Bin′ ↠ ℕ
    Bin′↠ℕ = record
      { logical-equivalence = record
        { to   = to-ℕ′
        ; from = from-ℕ′
        }
      ; right-inverse-of = to-ℕ′∘from-ℕ′
      }
      where

      abstract

        from-ℕ′ : ℕ → Bin′
        from-ℕ′ zero      = false ∷ []
        from-ℕ′ (N.suc n) = suc′ (from-ℕ′ n)

        to-ℕ′∘from-ℕ′ : ∀ n → to-ℕ′ (from-ℕ′ n) ≡ n
        to-ℕ′∘from-ℕ′ zero      = refl _
        to-ℕ′∘from-ℕ′ (N.suc n) =
          to-ℕ′ (from-ℕ′ (N.suc n))  ≡⟨⟩
          to-ℕ′ (suc′ (from-ℕ′ n))   ≡⟨ to-ℕ′-suc′ (from-ℕ′ n) ⟩
          N.suc (to-ℕ′ (from-ℕ′ n))  ≡⟨ cong N.suc (to-ℕ′∘from-ℕ′ n) ⟩∎
          N.suc n                    ∎

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
        add-with-carry₁ b     []           = b ∷ []
        add-with-carry₁ false cs@(_ ∷ _)   = cs
        add-with-carry₁ true  (false ∷ cs) = true ∷ cs
        add-with-carry₁ true  (true  ∷ cs) =
          false ∷ add-with-carry₁ true cs

        add-with-carry₂ : Bool → Bin′ → Bin′ → Bin′
        add-with-carry₂ b []         ds       = add-with-carry₁ b ds
        add-with-carry₂ b cs@(_ ∷ _) []       = add-with-carry₁ b cs
        add-with-carry₂ b (c ∷ cs)   (d ∷ ds) =
          case add-with-carryᴮ b c d of λ where
            (e , f) → e ∷ add-with-carry₂ f cs ds

        to-ℕ′-add-with-carry₁ :
          ∀ b cs →
          to-ℕ′ (add-with-carry₁ b cs) ≡
          from-Bool b ⊕ to-ℕ′ cs
        to-ℕ′-add-with-carry₁ b     []           = refl _
        to-ℕ′-add-with-carry₁ false (_ ∷ _)      = refl _
        to-ℕ′-add-with-carry₁ true  (false ∷ _)  = refl _
        to-ℕ′-add-with-carry₁ true  (true  ∷ cs) =
          to-ℕ′ (add-with-carry₁ true (true ∷ cs))  ≡⟨⟩
          2 ⊛ to-ℕ′ (add-with-carry₁ true cs)       ≡⟨ cong (2 ⊛_) (to-ℕ′-add-with-carry₁ true cs) ⟩
          2 ⊛ (1 ⊕ to-ℕ′ cs)                        ≡⟨ solve 1 (λ n → con 2 :* (con 1 :+ n) := con 2 :+ con 2 :* n) (refl _) _ ⟩
          2 ⊕ 2 ⊛ to-ℕ′ cs                          ≡⟨⟩
          from-Bool true ⊕ to-ℕ′ (true ∷ cs)        ∎

        to-ℕ′-add-with-carry₂ :
          ∀ b cs ds →
          to-ℕ′ (add-with-carry₂ b cs ds) ≡
          from-Bool b ⊕ (to-ℕ′ cs ⊕ to-ℕ′ ds)
        to-ℕ′-add-with-carry₂ b []         ds = to-ℕ′-add-with-carry₁ b ds
        to-ℕ′-add-with-carry₂ b cs@(_ ∷ _) [] =
          to-ℕ′ (add-with-carry₁ b cs)         ≡⟨ to-ℕ′-add-with-carry₁ b cs ⟩
          from-Bool b ⊕ to-ℕ′ cs               ≡⟨ solve 2 (λ b c → b :+ c := b :+ (c :+ con 0)) (refl _) (from-Bool b) _ ⟩
          from-Bool b ⊕ (to-ℕ′ cs ⊕ 0)         ≡⟨⟩
          from-Bool b ⊕ (to-ℕ′ cs ⊕ to-ℕ′ [])  ∎

        to-ℕ′-add-with-carry₂ false (false ∷ cs) (false ∷ ds) =
          to-ℕ′ (false ∷ add-with-carry₂ false cs ds)  ≡⟨⟩
          2 ⊛ to-ℕ′ (add-with-carry₂ false cs ds)      ≡⟨ cong (2 ⊛_) (to-ℕ′-add-with-carry₂ false cs ds) ⟩
          2 ⊛ (to-ℕ′ cs ⊕ to-ℕ′ ds)                    ≡⟨ solve 2 (λ c d → con 2 :* (c :+ d) :=
                                                                           con 2 :* c :+ con 2 :* d)
                                                                (refl _) (to-ℕ′ cs) _ ⟩
          2 ⊛ to-ℕ′ cs ⊕ 2 ⊛ to-ℕ′ ds                  ≡⟨⟩
          to-ℕ′ (false ∷ cs) ⊕ to-ℕ′ (false ∷ ds)      ∎

        to-ℕ′-add-with-carry₂ false (false ∷ cs) (true ∷ ds) =
          to-ℕ′ (true ∷ add-with-carry₂ false cs ds)   ≡⟨⟩
          1 ⊕ 2 ⊛ to-ℕ′ (add-with-carry₂ false cs ds)  ≡⟨ cong ((1 ⊕_) ∘ (2 ⊛_)) (to-ℕ′-add-with-carry₂ false cs ds) ⟩
          1 ⊕ 2 ⊛ (to-ℕ′ cs ⊕ to-ℕ′ ds)                ≡⟨ solve 2 (λ c d → con 1 :+ con 2 :* (c :+ d) :=
                                                                           con 2 :* c :+ (con 1 :+ con 2 :* d))
                                                                (refl _) (to-ℕ′ cs) _ ⟩
          2 ⊛ to-ℕ′ cs ⊕ (1 ⊕ 2 ⊛ to-ℕ′ ds)            ≡⟨⟩
          to-ℕ′ (false ∷ cs) ⊕ to-ℕ′ (true ∷ ds)       ∎

        to-ℕ′-add-with-carry₂ false (true ∷ cs) (false ∷ ds) =
          to-ℕ′ (true ∷ add-with-carry₂ false cs ds)   ≡⟨⟩
          1 ⊕ 2 ⊛ to-ℕ′ (add-with-carry₂ false cs ds)  ≡⟨ cong ((1 ⊕_) ∘ (2 ⊛_)) (to-ℕ′-add-with-carry₂ false cs ds) ⟩
          1 ⊕ 2 ⊛ (to-ℕ′ cs ⊕ to-ℕ′ ds)                ≡⟨ solve 2 (λ c d → con 1 :+ con 2 :* (c :+ d) :=
                                                                           con 1 :+ con 2 :* c :+ con 2 :* d)
                                                                (refl _) (to-ℕ′ cs) _ ⟩
          1 ⊕ 2 ⊛ to-ℕ′ cs ⊕ 2 ⊛ to-ℕ′ ds              ≡⟨⟩
          to-ℕ′ (true ∷ cs) ⊕ to-ℕ′ (false ∷ ds)       ∎

        to-ℕ′-add-with-carry₂ false (true ∷ cs) (true ∷ ds) =
          to-ℕ′ (false ∷ add-with-carry₂ true cs ds)  ≡⟨⟩
          2 ⊛ to-ℕ′ (add-with-carry₂ true cs ds)      ≡⟨ cong (2 ⊛_) (to-ℕ′-add-with-carry₂ true cs ds) ⟩
          2 ⊛ (1 ⊕ to-ℕ′ cs ⊕ to-ℕ′ ds)               ≡⟨ solve 2 (λ c d → con 2 :* (con 1 :+ c :+ d) :=
                                                                          con 1 :+ con 2 :* c :+ (con 1 :+ con 2 :* d))
                                                               (refl _) (to-ℕ′ cs) _ ⟩
          1 ⊕ 2 ⊛ to-ℕ′ cs ⊕ (1 ⊕ 2 ⊛ to-ℕ′ ds)       ≡⟨⟩
          to-ℕ′ (true ∷ cs) ⊕ to-ℕ′ (true ∷ ds)       ∎

        to-ℕ′-add-with-carry₂ true (false ∷ cs) (false ∷ ds) =
          to-ℕ′ (true ∷ add-with-carry₂ false cs ds)   ≡⟨⟩
          1 ⊕ 2 ⊛ to-ℕ′ (add-with-carry₂ false cs ds)  ≡⟨ cong ((1 ⊕_) ∘ (2 ⊛_)) (to-ℕ′-add-with-carry₂ false cs ds) ⟩
          1 ⊕ 2 ⊛ (to-ℕ′ cs ⊕ to-ℕ′ ds)                ≡⟨ solve 2 (λ c d → con 1 :+ con 2 :* (c :+ d) :=
                                                                           con 1 :+ con 2 :* c :+ con 2 :* d)
                                                                (refl _) (to-ℕ′ cs) _ ⟩
          1 ⊕ 2 ⊛ to-ℕ′ cs ⊕ 2 ⊛ to-ℕ′ ds              ≡⟨⟩
          1 ⊕ to-ℕ′ (false ∷ cs) ⊕ to-ℕ′ (false ∷ ds)  ∎

        to-ℕ′-add-with-carry₂ true (false ∷ cs) (true ∷ ds) =
          to-ℕ′ (false ∷ add-with-carry₂ true cs ds)  ≡⟨⟩
          2 ⊛ to-ℕ′ (add-with-carry₂ true cs ds)      ≡⟨ cong (2 ⊛_) (to-ℕ′-add-with-carry₂ true cs ds) ⟩
          2 ⊛ (1 ⊕ to-ℕ′ cs ⊕ to-ℕ′ ds)               ≡⟨ solve 2 (λ c d → con 2 :* (con 1 :+ c :+ d) :=
                                                                          con 1 :+ con 2 :* c :+ (con 1 :+ con 2 :* d))
                                                               (refl _) (to-ℕ′ cs) _ ⟩
          1 ⊕ 2 ⊛ to-ℕ′ cs ⊕ (1 ⊕ 2 ⊛ to-ℕ′ ds)       ≡⟨⟩
          1 ⊕ to-ℕ′ (false ∷ cs) ⊕ to-ℕ′ (true ∷ ds)  ∎

        to-ℕ′-add-with-carry₂ true (true ∷ cs) (false ∷ ds) =
          to-ℕ′ (false ∷ add-with-carry₂ true cs ds)  ≡⟨⟩
          2 ⊛ to-ℕ′ (add-with-carry₂ true cs ds)      ≡⟨ cong (2 ⊛_) (to-ℕ′-add-with-carry₂ true cs ds) ⟩
          2 ⊛ (1 ⊕ to-ℕ′ cs ⊕ to-ℕ′ ds)               ≡⟨ solve 2 (λ c d → con 2 :* (con 1 :+ c :+ d) :=
                                                                          con 2 :+ con 2 :* c :+ con 2 :* d)
                                                               (refl _) (to-ℕ′ cs) _ ⟩
          2 ⊕ 2 ⊛ to-ℕ′ cs ⊕ 2 ⊛ to-ℕ′ ds             ≡⟨⟩
          1 ⊕ to-ℕ′ (true ∷ cs) ⊕ to-ℕ′ (false ∷ ds)  ∎

        to-ℕ′-add-with-carry₂ true (true ∷ cs) (true ∷ ds) =
          to-ℕ′ (true ∷ add-with-carry₂ true cs ds)   ≡⟨⟩
          1 ⊕ 2 ⊛ to-ℕ′ (add-with-carry₂ true cs ds)  ≡⟨ cong ((1 ⊕_) ∘ (2 ⊛_)) (to-ℕ′-add-with-carry₂ true cs ds) ⟩
          1 ⊕ 2 ⊛ (1 ⊕ to-ℕ′ cs ⊕ to-ℕ′ ds)           ≡⟨ solve 2 (λ c d → con 1 :+ con 2 :* (con 1 :+ c :+ d) :=
                                                                          con 2 :+ con 2 :* c :+ (con 1 :+ con 2 :* d))
                                                               (refl _) (to-ℕ′ cs) _ ⟩
          2 ⊕ 2 ⊛ to-ℕ′ cs ⊕ (1 ⊕ 2 ⊛ to-ℕ′ ds)       ≡⟨⟩
          1 ⊕ to-ℕ′ (true ∷ cs) ⊕ to-ℕ′ (true ∷ ds)   ∎

      -- Addition.
      --
      -- Note that this function can return a number with leading
      -- zeros even if the input does not contain leading zeros. It
      -- might make sense to change the implementation.

      add-with-carry : Bin′ → Bin′ → Bin′
      add-with-carry = add-with-carry₂ false

      to-ℕ′-add-with-carry :
        ∀ bs cs →
        to-ℕ′ (add-with-carry bs cs) ≡
        to-ℕ′ bs ⊕ to-ℕ′ cs
      to-ℕ′-add-with-carry = to-ℕ′-add-with-carry₂ false

      -- Division by two, rounded downwards.

      ⌊_/2⌋ : Bin′ → Bin′
      ⌊ []     /2⌋ = []
      ⌊ _ ∷ bs /2⌋ = bs

      to-ℕ′-⌊/2⌋ : ∀ bs → to-ℕ′ ⌊ bs /2⌋ ≡ N.⌊ to-ℕ′ bs /2⌋
      to-ℕ′-⌊/2⌋ []           = refl _
      to-ℕ′-⌊/2⌋ (false ∷ bs) =
        to-ℕ′ bs              ≡⟨ sym $ N.⌊2*/2⌋≡ _ ⟩∎
        N.⌊ 2 ⊛ to-ℕ′ bs /2⌋  ∎

      to-ℕ′-⌊/2⌋ (true ∷ bs) =
        to-ℕ′ bs                  ≡⟨ sym $ N.⌊1+2*/2⌋≡ _ ⟩∎
        N.⌊ 1 ⊕ 2 ⊛ to-ℕ′ bs /2⌋  ∎

      -- Division by two, rounded upwards.

      ⌈_/2⌉ : Bin′ → Bin′
      ⌈ []         /2⌉ = []
      ⌈ false ∷ bs /2⌉ = bs
      ⌈ true  ∷ bs /2⌉ = suc′ bs

      to-ℕ′-⌈/2⌉ : ∀ bs → to-ℕ′ ⌈ bs /2⌉ ≡ N.⌈ to-ℕ′ bs /2⌉
      to-ℕ′-⌈/2⌉ []           = refl _
      to-ℕ′-⌈/2⌉ (false ∷ bs) =
        to-ℕ′ bs              ≡⟨ sym $ N.⌈2*/2⌉≡ _ ⟩∎
        N.⌈ 2 ⊛ to-ℕ′ bs /2⌉  ∎

      to-ℕ′-⌈/2⌉ (true ∷ bs) =
        to-ℕ′ (suc′ bs)           ≡⟨ to-ℕ′-suc′ bs ⟩
        1 ⊕ to-ℕ′ bs              ≡⟨ sym $ N.⌈1+2*/2⌉≡ _ ⟩∎
        N.⌈ 1 ⊕ 2 ⊛ to-ℕ′ bs /2⌉  ∎

      private

        -- A helper function used in strip-leading-zeros.

        maybe-cons : Bool → Bin′ → Bin′
        maybe-cons false [] = []
        maybe-cons b     bs = b ∷ bs

        -- Removes leading zeros.

        strip-leading-zeros : Bin′ → Bin′
        strip-leading-zeros = foldr maybe-cons []

        -- Removing leading zeros does not affect the "semantics" of a
        -- number.

        to-ℕ′-strip-leading-zeros :
          ∀ bs → to-ℕ′ (strip-leading-zeros bs) ≡ to-ℕ′ bs
        to-ℕ′-strip-leading-zeros []           = refl _
        to-ℕ′-strip-leading-zeros (true ∷ bs)  =
          to-ℕ′ (true ∷ strip-leading-zeros bs)   ≡⟨⟩
          1 ⊕ 2 ⊛ to-ℕ′ (strip-leading-zeros bs)  ≡⟨ cong (λ n → 1 ⊕ 2 ⊛ n) $ to-ℕ′-strip-leading-zeros bs ⟩
          1 ⊕ 2 ⊛ to-ℕ′ bs                        ≡⟨⟩
          to-ℕ′ (true ∷ bs)                       ∎
        to-ℕ′-strip-leading-zeros (false ∷ bs)
          with strip-leading-zeros bs
             | to-ℕ′-strip-leading-zeros bs
        ... | [] | eq =
          to-ℕ′ []            ≡⟨⟩
          0                   ≡⟨ cong (2 ⊛_) eq ⟩
          2 ⊛ to-ℕ′ bs        ≡⟨⟩
          to-ℕ′ (false ∷ bs)  ∎
        ... | bs′@(_ ∷ _) | eq =
          to-ℕ′ (false ∷ bs′)  ≡⟨⟩
          2 ⊛ to-ℕ′ bs′        ≡⟨ cong (2 ⊛_) eq ⟩
          2 ⊛ to-ℕ′ bs         ≡⟨⟩
          to-ℕ′ (false ∷ bs)   ∎

        -- If the "semantics" of a stripped list is zero, then the
        -- stripped list is equal to zero′.

        zero′-unique :
            ∀ bs →
            to-ℕ′ (strip-leading-zeros bs) ≡ 0 →
            strip-leading-zeros bs ≡ zero′
        zero′-unique []           eq = refl _
        zero′-unique (true  ∷ bs) eq = ⊥-elim $ Nat.0≢+ $ sym eq
        zero′-unique (false ∷ bs) eq =
          maybe-cons false (strip-leading-zeros bs)         ≡⟨ cong (maybe-cons false) $ zero′-unique bs (

              to-ℕ′ (strip-leading-zeros bs)                     ≡⟨ Nat.*-cancellativeˡ 1 (

                  2 ⊛ to-ℕ′ (strip-leading-zeros bs)               ≡⟨ cong (2 ⊛_) $ to-ℕ′-strip-leading-zeros bs ⟩
                  2 ⊛ to-ℕ′ bs                                     ≡⟨⟩
                  to-ℕ′ (false ∷ bs)                               ≡⟨ sym $ to-ℕ′-strip-leading-zeros (false ∷ bs) ⟩
                  to-ℕ′ (strip-leading-zeros (false ∷ bs))         ≡⟨ eq ⟩
                  0                                                ≡⟨⟩
                  2 ⊛ 0                                            ∎) ⟩∎

              0                                                  ∎) ⟩

          maybe-cons false []                               ≡⟨⟩
          []                                                ∎

        -- Doubles the number.
        --
        -- This operation is not exported, it is only used in the type
        -- signatures of some lemmas. Note that this function can
        -- return a number with leading zeros even if the input does
        -- not contain leading zeros.

        double′ : Bin′ → Bin′
        double′ = false ∷_

        -- Doubles the number and adds one.
        --
        -- This operation is not exported, it is only used in the type
        -- signatures of some lemmas.

        suc-double′ : Bin′ → Bin′
        suc-double′ = true ∷_

        -- It is impossible that lists starting with true and false
        -- have the same semantics.

        distinct-heads→distinct-semantics :
          ∀ bs₁ bs₂ → to-ℕ′ (suc-double′ bs₁) ≢ to-ℕ′ (double′ bs₂)
        distinct-heads→distinct-semantics bs₁ bs₂ eq =
          Nat.even≢odd (to-ℕ′ bs₂) (to-ℕ′ bs₁) (sym eq)

        -- A variant of the previous lemma.

        distinct-heads→distinct-semantics′ :
          ∀ bs₁ bs₂ →
          to-ℕ′ (suc-double′ bs₁) ≢
          to-ℕ′ (strip-leading-zeros (double′ bs₂))
        distinct-heads→distinct-semantics′ bs₁ bs₂ eq
          with strip-leading-zeros bs₂
        ... | []           = Nat.0≢+ $ sym eq
        ... | bs₂′@(_ ∷ _) =
          distinct-heads→distinct-semantics bs₁ bs₂′ eq

      -- The function to-ℕ′ is, in a certain sense, injective on the
      -- image of strip-leading-zeros.

      to-ℕ′-injective :
        ∀ bs₁ bs₂ →
        to-ℕ′ (strip-leading-zeros bs₁) ≡
        to-ℕ′ (strip-leading-zeros bs₂) →
        strip-leading-zeros bs₁ ≡ strip-leading-zeros bs₂
      to-ℕ′-injective [] [] eq = refl _

      to-ℕ′-injective [] (true ∷ bs₂) eq = ⊥-elim $ Nat.0≢+ eq

      to-ℕ′-injective [] (false ∷ bs₂) eq =
        strip-leading-zeros []             ≡⟨⟩
        []                                 ≡⟨ sym $ zero′-unique (false ∷ bs₂) (sym eq) ⟩∎
        strip-leading-zeros (false ∷ bs₂)  ∎

      to-ℕ′-injective (true ∷ bs₁) [] eq = ⊥-elim $ Nat.0≢+ $ sym eq

      to-ℕ′-injective (false ∷ bs₁) [] eq =
        strip-leading-zeros (false ∷ bs₁)  ≡⟨ zero′-unique (false ∷ bs₁) eq ⟩
        []                                 ≡⟨⟩
        strip-leading-zeros []             ∎

      to-ℕ′-injective (true ∷ bs₁) (true ∷ bs₂) eq =
        cong (true ∷_) $ to-ℕ′-injective bs₁ bs₂ (
          to-ℕ′ (strip-leading-zeros bs₁)  ≡⟨ Nat.*-cancellativeˡ 1 $ Nat.cancel-suc eq ⟩∎
          to-ℕ′ (strip-leading-zeros bs₂)  ∎)

      to-ℕ′-injective (true ∷ bs₁) (false ∷ bs₂) eq =
        ⊥-elim $
          distinct-heads→distinct-semantics′
            (strip-leading-zeros bs₁) bs₂ eq
      to-ℕ′-injective (false ∷ bs₁) (true ∷ bs₂) eq =
        ⊥-elim $
          distinct-heads→distinct-semantics′
            (strip-leading-zeros bs₂) bs₁ (sym eq)

      to-ℕ′-injective (false ∷ bs₁) (false ∷ bs₂) eq =
        cong-false-∷ bs₁ bs₂ $ to-ℕ′-injective bs₁ bs₂ (
          to-ℕ′ (strip-leading-zeros bs₁)                ≡⟨ Nat.*-cancellativeˡ 1 (

              2 ⊛ to-ℕ′ (strip-leading-zeros bs₁)             ≡⟨ cong (2 ⊛_) $ to-ℕ′-strip-leading-zeros bs₁ ⟩
              to-ℕ′ (false ∷ bs₁)                             ≡⟨ sym $ to-ℕ′-strip-leading-zeros (false ∷ bs₁) ⟩
              to-ℕ′ (strip-leading-zeros (false ∷ bs₁))       ≡⟨ eq ⟩
              to-ℕ′ (strip-leading-zeros (false ∷ bs₂))       ≡⟨ to-ℕ′-strip-leading-zeros (false ∷ bs₂) ⟩
              to-ℕ′ (false ∷ bs₂)                             ≡⟨ cong (2 ⊛_) $ sym $ to-ℕ′-strip-leading-zeros bs₂ ⟩∎
              2 ⊛ to-ℕ′ (strip-leading-zeros bs₂)             ∎) ⟩∎

          to-ℕ′ (strip-leading-zeros bs₂)                ∎)
        where
        cong-false-∷ :
          ∀ bs₁ bs₂ →
          strip-leading-zeros bs₁ ≡ strip-leading-zeros bs₂ →
          strip-leading-zeros (false ∷ bs₁) ≡
          strip-leading-zeros (false ∷ bs₂)
        cong-false-∷ bs₁ bs₂ eq
          with strip-leading-zeros bs₁
             | strip-leading-zeros bs₂
        ... | []    | []    = refl _
        ... | []    | _ ∷ _ = ⊥-elim $ List.[]≢∷ eq
        ... | _ ∷ _ | []    = ⊥-elim $ List.[]≢∷ $ sym eq
        ... | _ ∷ _ | _ ∷ _ = cong (false ∷_) eq


      -- An equality test.

      private

        equal? :
          (bs₁ bs₂ : Bin′) →
          Dec ((_≡_ on strip-leading-zeros) bs₁ bs₂)
        equal? = List.Dec._≟_ Bool._≟_ on strip-leading-zeros

      _==_ : Bin′ → Bin′ → Bool
      bs₁ == bs₂ = ⊎-map _ _ (equal? bs₁ bs₂)

      to-ℕ′-== : ∀ bs₁ bs₂ → T (bs₁ == bs₂) ⇔ (to-ℕ′ bs₁ ≡ to-ℕ′ bs₂)
      to-ℕ′-== bs₁ bs₂ with equal? bs₁ bs₂
      ... | yes p = record
        { to = λ _ →
            to-ℕ′ bs₁                        ≡⟨ sym $ to-ℕ′-strip-leading-zeros bs₁ ⟩
            to-ℕ′ (strip-leading-zeros bs₁)  ≡⟨ cong to-ℕ′ p ⟩
            to-ℕ′ (strip-leading-zeros bs₂)  ≡⟨ to-ℕ′-strip-leading-zeros bs₂ ⟩∎
            to-ℕ′ bs₂                        ∎
        }
      ... | no p = record
        { to   = λ ()
        ; from =
            to-ℕ′ bs₁ ≡ to-ℕ′ bs₂              ↝⟨ (λ eq → trans (to-ℕ′-strip-leading-zeros bs₁)
                                                            (trans eq (sym $ to-ℕ′-strip-leading-zeros bs₂))) ⟩
            to-ℕ′ (strip-leading-zeros bs₁) ≡
            to-ℕ′ (strip-leading-zeros bs₂)    ↝⟨ to-ℕ′-injective bs₁ bs₂ ⟩

            strip-leading-zeros bs₁ ≡
            strip-leading-zeros bs₂            ↝⟨ p ⟩□

            ⊥                                  □
        }

------------------------------------------------------------------------
-- Binary natural numbers

private

  module Bin-wrapper = Wrapper Bin′.Bin′ Bin′.Bin′↠ℕ
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
  Operations.zero      Operations-for-Bin′ = Bin′.zero′
  Operations.to-ℕ-zero Operations-for-Bin′ = Bin′.to-ℕ′-zero′
  Operations.suc       Operations-for-Bin′ = Bin′.suc′
  Operations.to-ℕ-suc  Operations-for-Bin′ = Bin′.to-ℕ′-suc′
  Operations._+_       Operations-for-Bin′ = Bin′.add-with-carry
  Operations.to-ℕ-+    Operations-for-Bin′ = Bin′.to-ℕ′-add-with-carry
  Operations.⌊_/2⌋     Operations-for-Bin′ = Bin′.⌊_/2⌋
  Operations.to-ℕ-⌊/2⌋ Operations-for-Bin′ = Bin′.to-ℕ′-⌊/2⌋
  Operations.⌈_/2⌉     Operations-for-Bin′ = Bin′.⌈_/2⌉
  Operations.to-ℕ-⌈/2⌉ Operations-for-Bin′ = Bin′.to-ℕ′-⌈/2⌉
  Operations._==_      Operations-for-Bin′ = Bin′._==_
  Operations.to-ℕ-==   Operations-for-Bin′ = Bin′.to-ℕ′-==

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
      subst Bin-[_] (N.+-comm m) (b + c) ≡ c + b
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
