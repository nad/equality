------------------------------------------------------------------------
-- A wrapper that turns a representation of natural numbers, possibly
-- with several representations for some numbers, into a
-- representation with unique representatives, that additionally
-- computes roughly like the unary natural numbers (at least for some
-- operations)
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality
open import Prelude hiding (zero; suc; _+_)
import Surjection

module Nat.Wrapper
  {reflexive}
  (eq : ∀ {a p} → Equality-with-J a p reflexive)
  (open Surjection eq using (_↠_))

  -- The underlying representation of natural numbers.
  (Nat′ : Set)
  -- A split surjection from this representation to the unary natural
  -- numbers.
  (Nat′↠ℕ : Nat′ ↠ ℕ)
  where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_; Dec-map)

open import Bijection eq using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Erased.Cubical eq
open import Erased.Cubical.Singleton eq
open import Function-universe eq hiding (_∘_)
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
open import List.All.Recursive eq
open import Vec eq as Vec

private

  module N where
    open import Nat eq public
    open Prelude public using (zero; suc; _+_)

  variable
    A               : Set
    f f′ m n n′ hyp : A

------------------------------------------------------------------------
-- The wrapper

private

  -- Converts from the underlying representation to unary natural
  -- numbers.

  to-ℕ : Nat′ → ℕ
  to-ℕ = _↠_.to Nat′↠ℕ

-- Natural numbers built on top of Nat′, indexed by corresponding
-- unary natural numbers, and truncated so that any two numbers that
-- stand for the same unary natural number are seen as equal.

Nat-[_] : @0 ℕ → Set
Nat-[ m ] = ∥ (∃ λ (n : Nat′) → Erased (to-ℕ n ≡ m)) ∥

-- Nat-[ n ] is a proposition.

Nat-[]-propositional : {@0 n : ℕ} → Is-proposition Nat-[ n ]
Nat-[]-propositional = truncation-is-proposition

-- A non-indexed variant of Nat-[_].

Nat : Set
Nat = ∃ λ (n : Erased ℕ) → Nat-[ erased n ]

-- Returns the (erased) index.

@0 ⌊_⌋ : Nat → ℕ
⌊ [ n ] , _ ⌋ = n

-- There is a bijection between equality of two values of type Nat and
-- erased equality of the corresponding unary natural number indices.

≡-for-indices↔≡ :
  {m n : Nat} →
  Erased (⌊ m ⌋ ≡ ⌊ n ⌋) ↔ m ≡ n
≡-for-indices↔≡ {m = m} {n = n} =
  Erased (⌊ m ⌋ ≡ ⌊ n ⌋)  ↝⟨ Erased-≡↔[]≡[] ⟩
  proj₁ m ≡ proj₁ n       ↝⟨ ignore-propositional-component Nat-[]-propositional ⟩□
  m ≡ n                   □

------------------------------------------------------------------------
-- Conversion functions

private

  -- Equality is very stable for the natural numbers.

  ℕ-very-stable : Very-stable-≡ ℕ
  ℕ-very-stable = Decidable-equality→Very-stable-≡ N._≟_

-- Nat-[ n ] is isomorphic to the type of natural numbers equal
-- (with erased equality proofs) to n.

Nat-[]↔Σℕ : {@0 n : ℕ} → Nat-[ n ] ↔ ∃ λ m → Erased (m ≡ n)
Nat-[]↔Σℕ = ↠→↔Erased-singleton Nat′↠ℕ ℕ-very-stable

-- Nat is isomorphic to the type of unary natural numbers.

Nat↔ℕ : Nat ↔ ℕ
Nat↔ℕ = Σ-Erased-∥-Σ-Erased-≡-∥↔ Nat′↠ℕ ℕ-very-stable

-- Converts from ℕ to Nat.

⌈_⌉ : ℕ → Nat
⌈_⌉ = _↔_.from Nat↔ℕ

-- The index matches the result of _↔_.to Nat↔ℕ.

@0 ≡⌊⌋ : ∀ n → _↔_.to Nat↔ℕ n ≡ ⌊ n ⌋
≡⌊⌋ n = to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡ Nat′↠ℕ ℕ-very-stable n

------------------------------------------------------------------------
-- Some operations for Nat-[_]

-- A helper function that can be used to define constants.

nullary-[] :
  {@0 n : ℕ}
  (n′ : Nat′) →
  @0 to-ℕ n′ ≡ n →
  Nat-[ n ]
nullary-[] n′ hyp = ∣ n′ , [ hyp ] ∣

-- A helper function that can be used to define unary operators.

unary-[] :
  {@0 n : ℕ} {@0 f : ℕ → ℕ}
  (f′ : Nat′ → Nat′) →
  @0 (∀ n → to-ℕ (f′ n) ≡ f (to-ℕ n)) →
  Nat-[ n ] → Nat-[ f n ]
unary-[] {n = n} {f = f} f′ hyp = Trunc.rec
  truncation-is-proposition
  (uncurry λ n′ p →
     ∣ f′ n′
     , [ to-ℕ (f′ n′)  ≡⟨ hyp _ ⟩
         f (to-ℕ n′)   ≡⟨ cong f (erased p) ⟩∎
         f n           ∎
       ]
     ∣)

-- A helper function that can be used to define n-ary operators.

n-ary-[] :
  (n : ℕ)
  {@0 ms : Vec (Erased ℕ) n}
  (@0 f : Vec ℕ n → ℕ)
  (f′ : Vec Nat′ n → Nat′) →
  @0 (∀ ms → to-ℕ (f′ ms) ≡ f (Vec.map to-ℕ ms)) →
  All (Nat-[_] ∘ erased) (Vec.to-list ms) →
  Nat-[ f (Vec.map erased ms) ]
n-ary-[] N.zero _ f′ hyp _ =
  nullary-[] (f′ _) (hyp _)
n-ary-[] (N.suc n) {ms = ms} f f′ hyp (m′ , ms′) =
  Trunc.rec
    truncation-is-proposition
    (uncurry λ m′ p →
       n-ary-[]
         n
         (f ∘ (erased (Vec.head ms) ,_))
         (λ ms′ → f′ (m′ , ms′))
         (λ ms′ →
            to-ℕ (f′ (m′ , ms′))                         ≡⟨ hyp (m′ , ms′) ⟩
            f (to-ℕ m′              , Vec.map to-ℕ ms′)  ≡⟨ cong (λ x → f (x , _)) (erased p) ⟩∎
            f (erased (Vec.head ms) , Vec.map to-ℕ ms′)  ∎)
         ms′)
    m′

-- The function n-ary-[] should be normalised by the compiler.

{-# STATIC n-ary-[] #-}

-- A helper function that can be used to define binary
-- operators.

binary-[] :
  {@0 m n : ℕ} {@0 f : ℕ → ℕ → ℕ}
  (f′ : Nat′ → Nat′ → Nat′) →
  @0 (∀ m n → to-ℕ (f′ m n) ≡ f (to-ℕ m) (to-ℕ n)) →
  Nat-[ m ] → Nat-[ n ] → Nat-[ f m n ]
binary-[] f′ hyp m n =
  n-ary-[]
    2
    _
    (λ (m , n , _) → f′ m n)
    (λ (m , n , _) → hyp m n)
    (m , n , _)

-- The code below is parametrised by implementations of (and
-- correctness properties for) certain operations for Nat′.

record Operations : Set where
  infix 4 _==_

  field
    zero      : Nat′
    to-ℕ-zero : to-ℕ zero ≡ N.zero

    suc       : Nat′ → Nat′
    to-ℕ-suc  : ∀ n → to-ℕ (suc n) ≡ N.suc (to-ℕ n)

    _+_       : Nat′ → Nat′ → Nat′
    to-ℕ-+    : ∀ m n → to-ℕ (m + n) ≡ to-ℕ m N.+ to-ℕ n

    ⌊_/2⌋     : Nat′ → Nat′
    to-ℕ-⌊/2⌋ : ∀ n → to-ℕ ⌊ n /2⌋ ≡ N.⌊ to-ℕ n /2⌋

    ⌈_/2⌉     : Nat′ → Nat′
    to-ℕ-⌈/2⌉ : ∀ n → to-ℕ ⌈ n /2⌉ ≡ N.⌈ to-ℕ n /2⌉

    _==_      : Nat′ → Nat′ → Bool
    to-ℕ-==   : ∀ m n → T (m == n) ⇔ (to-ℕ m ≡ to-ℕ n)

  -- A variant of decidable equality.

  infix 4 _≟_

  _≟_ : ∀ m n → Dec (Erased (to-ℕ m ≡ to-ℕ n))
  m ≟ n with m == n | [ to-ℕ-== m n ]
  ... | true  | [ hyp ] = yes [ _⇔_.to hyp _ ]
  ... | false | [ hyp ] = no (
    Erased (to-ℕ m ≡ to-ℕ n)  ↝⟨ Erased-cong (_⇔_.from hyp) ⟩
    Erased ⊥                  ↔⟨ Erased-⊥↔⊥ ⟩□
    ⊥                         □)

-- If certain operations are defined for Nat′, then they can be
-- defined for Nat-[_] as well.

module Operations-for-Nat-[] (o : Operations) where

  private

    module O = Operations o

  -- Zero.

  zero : Nat-[ N.zero ]
  zero = nullary-[] O.zero O.to-ℕ-zero

  -- The number's successor.

  suc : {@0 n : ℕ} → Nat-[ n ] → Nat-[ N.suc n ]
  suc = unary-[] O.suc O.to-ℕ-suc

  -- Addition.

  infixl 6 _+_

  _+_ : {@0 m n : ℕ} → Nat-[ m ] → Nat-[ n ] → Nat-[ m N.+ n ]
  _+_ = binary-[] O._+_ O.to-ℕ-+

  -- Division by two, rounded downwards.

  ⌊_/2⌋ : {@0 n : ℕ} → Nat-[ n ] → Nat-[ N.⌊ n /2⌋ ]
  ⌊_/2⌋ = unary-[] O.⌊_/2⌋ O.to-ℕ-⌊/2⌋

  -- Division by two, rounded upwards.

  ⌈_/2⌉ : {@0 n : ℕ} → Nat-[ n ] → Nat-[ N.⌈ n /2⌉ ]
  ⌈_/2⌉ = unary-[] O.⌈_/2⌉ O.to-ℕ-⌈/2⌉

  -- Equality is decidable (in a certain sense).

  infix 4 _≟_

  _≟_ :
    {@0 m n : ℕ} →
    Nat-[ m ] → Nat-[ n ] →
    Dec (Erased (m ≡ n))
  _≟_ {m = m} {n = n} m′ n′ = Trunc.rec
    erased-decidable-equality-propositional
    (uncurry λ m′ ([ m≡m′ ]) → Trunc.rec
       erased-decidable-equality-propositional
       (uncurry λ n′ ([ n≡n′ ]) →
          Dec-map
            (Erased-cong (
               to-ℕ m′ ≡ to-ℕ n′  ↝⟨ ≡⇒↝ _ (cong₂ _≡_ m≡m′ n≡n′) ⟩□
               m ≡ n              □))
            (m′ O.≟ n′))
       n′)
    m′
    where
    erased-decidable-equality-propositional :
      {@0 m n : ℕ} →
      Is-proposition (Dec (Erased (m ≡ n)))
    erased-decidable-equality-propositional {m = m} {n = n} =
      Dec-closure-propositional
        ext
        (H-level-Erased 1 ℕ-set)

------------------------------------------------------------------------
-- Operations for Nat

-- A helper function that can be used to define constants.

nullary :
  (@0 n : ℕ) (n′ : Nat′) →
  @0 to-ℕ n′ ≡ n →
  Nat
nullary n n′ hyp = [ n ] , nullary-[] n′ hyp

-- The function nullary is correct.
--
-- Note that the first of the correctness results holds by definition.

private

  @0 nullary-correct′ : ⌊ nullary n n′ hyp ⌋ ≡ n
  nullary-correct′ = refl _

nullary-correct :
  (@0 hyp : to-ℕ n′ ≡ n) →
  _↔_.to Nat↔ℕ (nullary n n′ hyp) ≡ n
nullary-correct {n′ = n′} {n = n} hyp =
  Very-stable→Stable 1 ℕ-very-stable _ _
     [ _↔_.to Nat↔ℕ (nullary n n′ hyp)  ≡⟨ ≡⌊⌋ (nullary n n′ hyp) ⟩
       ⌊ nullary n n′ hyp ⌋             ≡⟨⟩
       n                                ∎
     ]

-- A helper function that can be used to define unary operators.

unary :
  (@0 f : ℕ → ℕ) (f′ : Nat′ → Nat′) →
  @0 (∀ n → to-ℕ (f′ n) ≡ f (to-ℕ n)) →
  Nat → Nat
unary f f′ hyp ([ n ] , n′) = ([ f n ] , unary-[] f′ hyp n′)

-- The function unary is correct.
--
-- Note that the first of the correctness results holds by definition.

private

  @0 unary-correct′ : ⌊ unary f f′ hyp n ⌋ ≡ f ⌊ n ⌋
  unary-correct′ = refl _

unary-correct :
  {@0 hyp : ∀ n → to-ℕ (f′ n) ≡ f (to-ℕ n)} →
  ∀ n → _↔_.to Nat↔ℕ (unary f f′ hyp n) ≡ f (_↔_.to Nat↔ℕ n)
unary-correct {f′ = f′} {f = f} {hyp = hyp} n =
  Very-stable→Stable 1 ℕ-very-stable _ _
    [ _↔_.to Nat↔ℕ (unary f f′ hyp n)  ≡⟨ ≡⌊⌋ (unary f f′ hyp n) ⟩
      ⌊ unary f f′ hyp n ⌋             ≡⟨⟩
      f ⌊ n ⌋                          ≡⟨ sym $ cong f $ ≡⌊⌋ n ⟩∎
      f (_↔_.to Nat↔ℕ n)               ∎
    ]

-- A helper function that can be used to define n-ary operators.

n-ary :
  (n : ℕ)
  (@0 f : Vec ℕ n → ℕ)
  (f′ : Vec Nat′ n → Nat′) →
  @0 (∀ ms → to-ℕ (f′ ms) ≡ f (Vec.map to-ℕ ms)) →
  Vec Nat n → Nat
n-ary n f f′ hyp ms =
    [ f (Vec.map erased (proj₁ (_↔_.to Vec-Σ ms))) ]
  , n-ary-[] n f f′ hyp (proj₂ (_↔_.to Vec-Σ ms))

-- The function n-ary should be normalised by the compiler.

{-# STATIC n-ary #-}

-- The function n-ary is correct.

n-ary-correct :
  ∀ (n : ℕ) {f f′}
  (@0 hyp : ∀ ms → to-ℕ (f′ ms) ≡ f (Vec.map to-ℕ ms)) →
  ∀ ms →
  _↔_.to Nat↔ℕ (n-ary n f f′ hyp ms) ≡ f (Vec.map (_↔_.to Nat↔ℕ) ms)
n-ary-correct n {f = f} {f′ = f′} hyp ms =
  Very-stable→Stable 1 ℕ-very-stable _ _
    [ _↔_.to Nat↔ℕ (n-ary n f f′ hyp ms)            ≡⟨ ≡⌊⌋ (n-ary n f f′ hyp ms) ⟩
      ⌊ n-ary n f f′ hyp ms ⌋                       ≡⟨⟩
      f (Vec.map erased (proj₁ (_↔_.to Vec-Σ ms)))  ≡⟨ cong (f ∘ Vec.map _) proj₁-Vec-Σ ⟩
      f (Vec.map erased (Vec.map proj₁ ms))         ≡⟨ cong f $ sym Vec.map-∘ ⟩
      f (Vec.map ⌊_⌋ ms)                            ≡⟨ cong f $ sym $ Vec.map-cong ≡⌊⌋ ⟩∎
      f (Vec.map (_↔_.to Nat↔ℕ) ms)                 ∎
    ]

-- A helper function that can be used to define binary operators

binary :
  (@0 f : ℕ → ℕ → ℕ) (f′ : Nat′ → Nat′ → Nat′) →
  @0 (∀ m n → to-ℕ (f′ m n) ≡ f (to-ℕ m) (to-ℕ n)) →
  Nat → Nat → Nat
binary f g hyp m n =
  n-ary
    2
    (λ (m , n , _) → f m n)
    (λ (m , n , _) → g m n)
    (λ (m , n , _) → hyp m n)
    (m , n , _)

-- The function binary is correct.
--
-- Note that the first of the correctness results holds by definition.

private

  @0 binary-correct′ : ⌊ binary f f′ hyp m n ⌋ ≡ f ⌊ m ⌋ ⌊ n ⌋
  binary-correct′ = refl _

binary-correct :
  {@0 hyp : ∀ m n → to-ℕ (f′ m n) ≡ f (to-ℕ m) (to-ℕ n)} →
  ∀ m n →
  _↔_.to Nat↔ℕ (binary f f′ hyp m n) ≡
  f (_↔_.to Nat↔ℕ m) (_↔_.to Nat↔ℕ n)
binary-correct {hyp = hyp} m n =
  n-ary-correct
    2
    (λ (m , n , _) → hyp m n)
    (m , n , _)

-- If certain operations are defined for Nat′, then they can be
-- defined for Nat-[_] as well.

module Operations-for-Nat (o : Operations) where

  private

    module O    = Operations o
    module O-[] = Operations-for-Nat-[] o

  -- Zero.

  zero : Nat
  zero = nullary N.zero O.zero O.to-ℕ-zero

  to-ℕ-zero : _↔_.to Nat↔ℕ zero ≡ N.zero
  to-ℕ-zero = nullary-correct O.to-ℕ-zero

  -- The number's successor.

  suc : Nat → Nat
  suc = unary N.suc O.suc O.to-ℕ-suc

  to-ℕ-suc : ∀ n → _↔_.to Nat↔ℕ (suc n) ≡ N.suc (_↔_.to Nat↔ℕ n)
  to-ℕ-suc = unary-correct

  -- Addition.

  infixl 6 _+_

  _+_ : Nat → Nat → Nat
  _+_ = binary N._+_ O._+_ O.to-ℕ-+

  to-ℕ-+ :
    ∀ m n → _↔_.to Nat↔ℕ (m + n) ≡ _↔_.to Nat↔ℕ m N.+ _↔_.to Nat↔ℕ n
  to-ℕ-+ = binary-correct

  -- Division by two, rounded downwards.

  ⌊_/2⌋ : Nat → Nat
  ⌊_/2⌋ = unary N.⌊_/2⌋ O.⌊_/2⌋ O.to-ℕ-⌊/2⌋

  to-ℕ-⌊/2⌋ : ∀ n → _↔_.to Nat↔ℕ ⌊ n /2⌋ ≡ N.⌊ _↔_.to Nat↔ℕ n /2⌋
  to-ℕ-⌊/2⌋ = unary-correct

  -- Division by two, rounded upwards.

  ⌈_/2⌉ : Nat → Nat
  ⌈_/2⌉ = unary N.⌈_/2⌉ O.⌈_/2⌉ O.to-ℕ-⌈/2⌉

  to-ℕ-⌈/2⌉ : ∀ n → _↔_.to Nat↔ℕ ⌈ n /2⌉ ≡ N.⌈ _↔_.to Nat↔ℕ n /2⌉
  to-ℕ-⌈/2⌉ = unary-correct

  -- Equality is decidable (in a certain sense).

  infix 4 _≟_

  _≟_ : (m n : Nat) → Dec (Erased (⌊ m ⌋ ≡ ⌊ n ⌋))
  (_ , m′) ≟ (_ , n′) = m′ O-[].≟ n′

------------------------------------------------------------------------
-- Some examples

private

  module Nat-[]-examples (o : Operations) where

    open Operations-for-Nat-[] o

    -- Converts unary natural numbers to binary natural numbers.

    from-ℕ : ∀ n → Nat-[ n ]
    from-ℕ = proj₂ ∘ _↔_.from Nat↔ℕ

    -- Nat n is a proposition, so it is easy to prove that two values
    -- of this type are equal.

    example₁ : from-ℕ 4 + ⌊ from-ℕ 12 /2⌋ ≡ from-ℕ 10
    example₁ = Nat-[]-propositional _ _

    -- However, stating that two values of type Nat m and Nat n are
    -- equal, for equal natural numbers m and n, can be awkward.

    @0 example₂ :
      {@0 m n : ℕ} →
      (b : Nat-[ m ]) (c : Nat-[ n ]) →
      subst Nat-[_] (N.+-comm m) (b + c) ≡ c + b
    example₂ _ _ = Nat-[]-propositional _ _

  module Nat-examples (o : Operations) where

    open Operations-for-Nat o

    -- If Nat is used instead of Nat-[_], then it can be easier to
    -- state that two values are equal.

    example₁ : ⌈ 4 ⌉ + ⌊ ⌈ 12 ⌉ /2⌋ ≡ ⌈ 10 ⌉
    example₁ = _↔_.to ≡-for-indices↔≡ [ refl _ ]

    example₂ : ∀ m n → m + n ≡ n + m
    example₂ m n = _↔_.to ≡-for-indices↔≡
      [ ⌊ m ⌋ N.+ ⌊ n ⌋  ≡⟨ N.+-comm ⌊ m ⌋ ⟩∎
        ⌊ n ⌋ N.+ ⌊ m ⌋  ∎
      ]

    -- One can construct a proof showing that ⌈ 5 ⌉ is either equal or
    -- not equal to ⌈ 2 ⌉ + ⌈ 3 ⌉, but the proof does not compute to
    -- "inj₁ something" at compile-time.

    example₃ : Dec (⌈ 5 ⌉ ≡ ⌈ 2 ⌉ + ⌈ 3 ⌉)
    example₃ =
      Dec-map (_↔_.logical-equivalence ≡-for-indices↔≡)
        (⌈ 5 ⌉ ≟ ⌈ 2 ⌉ + ⌈ 3 ⌉)
