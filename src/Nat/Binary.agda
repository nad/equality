------------------------------------------------------------------------
-- A binary representation of natural numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality

module Nat.Binary
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (suc) renaming (_+_ to _⊕_; _*_ to _⊛_)

open import Bijection eq using (_↔_)
open import Equality.Decision-procedures eq
open import Equality.Path.Isomorphisms eq
import Equivalence eq as Eq
open import Erased eq
open import Erased.Singleton eq
open import Erased.Stability eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
open import List eq
open import Monad eq hiding (_⊛_)
open import Nat.Solver eq
open import Quotient eq
open import Surjection eq using (_↠_)

private

  module N where
    open import Nat eq public
    open Prelude public using (suc; _+_)

  variable
    A      : Set
    bs p   : A
    @0 m n : ℕ

------------------------------------------------------------------------
-- The underlying representation

private

  -- The underlying representation of binary natural numbers. The
  -- least significant digit comes first; true stands for one and
  -- false for zero. Leading zeroes (at the end of the lists) and
  -- empty lists are allowed, so the representation of a given natural
  -- number is never unique.

  Bin′ : Set
  Bin′ = List Bool

  -- Converts from Bool to ℕ.

  from-Bool : Bool → ℕ
  from-Bool = if_then 1 else 0

  -- Converts from Bin′ to ℕ.

  to-ℕ′ : Bin′ → ℕ
  to-ℕ′ = foldr (λ b n → from-Bool b ⊕ 2 ⊛ n) 0

  -- One of the number's successors.

  suc′ : Bin′ → Bin′
  suc′ []           = true ∷ []
  suc′ (false ∷ bs) = true ∷ bs
  suc′ (true  ∷ bs) = false ∷ suc′ bs

  -- A lemma relating suc′ and N.suc.

  to-ℕ′∘suc′ : ∀ bs → to-ℕ′ (suc′ bs) ≡ N.suc (to-ℕ′ bs)
  to-ℕ′∘suc′ []           = refl _
  to-ℕ′∘suc′ (false ∷ bs) =
    to-ℕ′ (suc′ (false ∷ bs))   ≡⟨⟩
    to-ℕ′ (true ∷ bs)           ≡⟨⟩
    1 ⊕ 2 ⊛ to-ℕ′ bs            ≡⟨⟩
    N.suc (to-ℕ′ (false ∷ bs))  ∎
  to-ℕ′∘suc′ (true ∷ bs) =
    to-ℕ′ (suc′ (true ∷ bs))   ≡⟨⟩
    to-ℕ′ (false ∷ suc′ bs)    ≡⟨⟩
    2 ⊛ to-ℕ′ (suc′ bs)        ≡⟨ cong (2 ⊛_) (to-ℕ′∘suc′ bs) ⟩
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
    from-ℕ′ : ℕ → Bin′
    from-ℕ′ zero      = false ∷ []
    from-ℕ′ (N.suc n) = suc′ (from-ℕ′ n)

    to-ℕ′∘from-ℕ′ : ∀ n → to-ℕ′ (from-ℕ′ n) ≡ n
    to-ℕ′∘from-ℕ′ zero      = refl _
    to-ℕ′∘from-ℕ′ (N.suc n) =
      to-ℕ′ (from-ℕ′ (N.suc n))  ≡⟨⟩
      to-ℕ′ (suc′ (from-ℕ′ n))   ≡⟨ to-ℕ′∘suc′ (from-ℕ′ n) ⟩
      N.suc (to-ℕ′ (from-ℕ′ n))  ≡⟨ cong N.suc (to-ℕ′∘from-ℕ′ n) ⟩∎
      N.suc n                    ∎

------------------------------------------------------------------------
-- Binary natural numbers

abstract

  -- Binary natural numbers indexed by corresponding natural numbers,
  -- and truncated so that any two binary natural numbers that stand
  -- for the same natural number are seen as equal.
  --
  -- The type is abstract to ensure that a change to a different
  -- representation (for instance a variant of Bin′ without leading
  -- zeroes) does not break code that uses this module.

  Bin : @0 ℕ → Set
  Bin n = ∥ (∃ λ (b : Bin′) → Erased (to-ℕ′ b ≡ n)) ∥

  -- Bin n is a proposition.

  Bin-propositional : Is-proposition (Bin n)
  Bin-propositional = truncation-is-proposition

-- A non-indexed variant of Bin.

Nat : Set
Nat = ∃ λ (n : Erased ℕ) → Bin (erased n)

-- Returns the (erased) index.

@0 ⌊_⌋ : Nat → ℕ
⌊_⌋ = erased ∘ proj₁

-- There is a bijection between equality of two values of type Nat and
-- erased equality of the corresponding unary natural number indices.

≡-for-indices↔≡ :
  {m n : Nat} →
  Erased (⌊ m ⌋ ≡ ⌊ n ⌋) ↔ m ≡ n
≡-for-indices↔≡ {m = m} {n = n} =
  Erased (⌊ m ⌋ ≡ ⌊ n ⌋)  ↝⟨ Erased-≡↔[]≡[] ⟩
  proj₁ m ≡ proj₁ n       ↝⟨ ignore-propositional-component Bin-propositional ⟩□
  m ≡ n                   □

------------------------------------------------------------------------
-- Conversion functions

abstract

  -- Bin n is isomorphic to the type of natural numbers equal (with
  -- erased equality proofs) to n.

  Bin↔Σℕ : Bin n ↔ ∃ λ m → Erased (m ≡ n)
  Bin↔Σℕ = ↠→↔Erased-singleton
    Bin′↠ℕ
    (Decidable-equality→Very-stable-≡ N._≟_)

-- Nat is isomorphic to the type of unary natural numbers.

Nat↔ℕ : Nat ↔ ℕ
Nat↔ℕ =
  Nat                                                   ↔⟨⟩
  (∃ λ (n : Erased ℕ) → Bin (erased n))                 ↝⟨ (∃-cong λ _ → Bin↔Σℕ) ⟩
  (∃ λ (n : Erased ℕ) → ∃ λ m → Erased (m ≡ erased n))  ↝⟨ Σ-Erased-Erased-singleton↔ ⟩□
  ℕ                                                     □

-- Converts from ℕ to Nat.

⌈_⌉ : ℕ → Nat
⌈_⌉ = _↔_.from Nat↔ℕ

abstract

  -- The index matches the result of _↔_.to Nat↔ℕ.

  @0 ≡⌊⌋ : ∀ {n} → _↔_.to Nat↔ℕ n ≡ ⌊ n ⌋
  ≡⌊⌋ {n = n} =
    to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡
      Bin′↠ℕ (Decidable-equality→Very-stable-≡ N._≟_) n

------------------------------------------------------------------------
-- Arithmetic with Bin

module Bin where

  abstract

    private

      -- A helper function that can be used to define unary operators.

      unary :
        {@0 f : ℕ → ℕ}
        (g : Bin′ → Bin′) →
        @0 (∀ b → to-ℕ′ (g b) ≡ f (to-ℕ′ b)) →
        Bin n → Bin (f n)
      unary {n = n} {f = f} g hyp = Trunc.rec
        truncation-is-proposition
        (uncurry λ b p →
           ∣ g b
           , [ to-ℕ′ (g b)  ≡⟨ hyp _ ⟩
               f (to-ℕ′ b)  ≡⟨ cong f (erased p) ⟩∎
               f n          ∎
             ]
           ∣)

      -- A helper function that can be used to define binary
      -- operators.

      binary :
        {@0 f : ℕ → ℕ → ℕ}
        (g : Bin′ → Bin′ → Bin′) →
        @0 (∀ b c → to-ℕ′ (g b c) ≡ f (to-ℕ′ b) (to-ℕ′ c)) →
        Bin m → Bin n → Bin (f m n)
      binary {m = m} {n = n} {f = f} g hyp = Trunc.rec
        (Π-closure ext 1 λ _ →
         truncation-is-proposition)
        (uncurry λ b p → Trunc.rec
           truncation-is-proposition
           (uncurry λ c q →
              ∣ g b c
              , [ to-ℕ′ (g b c)          ≡⟨ hyp _ _ ⟩
                  f (to-ℕ′ b) (to-ℕ′ c)  ≡⟨ cong₂ f (erased p) (erased q) ⟩∎
                  f m n                  ∎
                ]
              ∣))

    -- The number's successor.

    suc : Bin n → Bin (N.suc n)
    suc = unary suc′ to-ℕ′∘suc′

    -- Addition.

    infixl 6 _+_

    _+_ : Bin m → Bin n → Bin (m N.+ n)
    _+_ = binary (add-with-carry₂ false) (to-ℕ′-add-with-carry₂ false)
      where
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

    -- Division by two, rounded downwards.

    ⌊_/2⌋ : Bin n → Bin N.⌊ n /2⌋
    ⌊_/2⌋ = unary div-by-2 to-ℕ′∘div-by-2
      where
      div-by-2 : Bin′ → Bin′
      div-by-2 []       = []
      div-by-2 (_ ∷ bs) = bs

      to-ℕ′∘div-by-2 : ∀ bs → to-ℕ′ (div-by-2 bs) ≡ N.⌊ to-ℕ′ bs /2⌋
      to-ℕ′∘div-by-2 []           = refl _
      to-ℕ′∘div-by-2 (false ∷ bs) =
        to-ℕ′ bs              ≡⟨ sym $ N.⌊2*/2⌋≡ _ ⟩∎
        N.⌊ 2 ⊛ to-ℕ′ bs /2⌋  ∎

      to-ℕ′∘div-by-2 (true ∷ bs) =
        to-ℕ′ bs                  ≡⟨ sym $ N.⌊1+2*/2⌋≡ _ ⟩∎
        N.⌊ 1 ⊕ 2 ⊛ to-ℕ′ bs /2⌋  ∎

    -- Division by two, rounded upwards.

    ⌈_/2⌉ : Bin n → Bin N.⌈ n /2⌉
    ⌈_/2⌉ = unary div-by-2 to-ℕ′∘div-by-2
      where
      div-by-2 : Bin′ → Bin′
      div-by-2 []           = []
      div-by-2 (false ∷ bs) = bs
      div-by-2 (true  ∷ bs) = suc′ bs

      to-ℕ′∘div-by-2 : ∀ bs → to-ℕ′ (div-by-2 bs) ≡ N.⌈ to-ℕ′ bs /2⌉
      to-ℕ′∘div-by-2 []           = refl _
      to-ℕ′∘div-by-2 (false ∷ bs) =
        to-ℕ′ bs              ≡⟨ sym $ N.⌈2*/2⌉≡ _ ⟩∎
        N.⌈ 2 ⊛ to-ℕ′ bs /2⌉  ∎

      to-ℕ′∘div-by-2 (true ∷ bs) =
        to-ℕ′ (suc′ bs)           ≡⟨ to-ℕ′∘suc′ bs ⟩
        1 ⊕ to-ℕ′ bs              ≡⟨ sym $ N.⌈1+2*/2⌉≡ _ ⟩∎
        N.⌈ 1 ⊕ 2 ⊛ to-ℕ′ bs /2⌉  ∎

------------------------------------------------------------------------
-- Arithmetic with Nat

module Nat where

  -- The number's successor.

  suc : Nat → Nat
  suc = Σ-map _ Bin.suc

  -- Addition.

  infixl 6 _+_

  _+_ : Nat → Nat → Nat
  _+_ = Σ-zip _ Bin._+_

  -- Division by two, rounded downwards.

  ⌊_/2⌋ : Nat → Nat
  ⌊_/2⌋ = Σ-map _ Bin.⌊_/2⌋

  -- Division by two, rounded upwards.

  ⌈_/2⌉ : Nat → Nat
  ⌈_/2⌉ = Σ-map _ Bin.⌈_/2⌉

------------------------------------------------------------------------
-- Some examples

private

  module Bin-examples where

    open Bin

    -- Converts unary natural numbers to binary natural numbers.

    from-ℕ : ∀ n → Bin n
    from-ℕ = proj₂ ∘ _↔_.from Nat↔ℕ

    -- Bin n is a proposition, so it is easy to prove that two values
    -- of this type are equal.

    example₁ : from-ℕ 4 + ⌊ from-ℕ 12 /2⌋ ≡ from-ℕ 10
    example₁ = Bin-propositional _ _

    -- However, stating that two values of type Bin m and Bin n are
    -- equal, for equal natural numbers m and n, can be awkward.

    @0 example₂ :
      (b : Bin m) (c : Bin n) →
      subst Bin (N.+-comm m) (b + c) ≡ c + b
    example₂ _ _ = Bin-propositional _ _

  module Nat-examples where

    open Nat

    -- If Nat is used instead of Bin, then it can be easier to state
    -- that two values are equal.

    example₁ : ⌈ 4 ⌉ + ⌊ ⌈ 12 ⌉ /2⌋ ≡ ⌈ 10 ⌉
    example₁ = _↔_.to ≡-for-indices↔≡ [ refl _ ]

    example₂ : ∀ m n → m + n ≡ n + m
    example₂ m n = _↔_.to ≡-for-indices↔≡
      [ ⌊ m ⌋ ⊕ ⌊ n ⌋  ≡⟨ N.+-comm ⌊ m ⌋ ⟩∎
        ⌊ n ⌋ ⊕ ⌊ m ⌋  ∎
      ]
