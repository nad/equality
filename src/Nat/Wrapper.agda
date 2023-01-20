------------------------------------------------------------------------
-- A wrapper that turns a representation of natural numbers (with a
-- unique representative for every number) into a representation that
-- computes roughly like the unary natural numbers (at least for some
-- operations)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

import Bijection
open import Equality
import Erased.Without-box-cong
open import Prelude hiding (zero; suc; _+_; _*_; _^_)

module Nat.Wrapper
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)

  -- The underlying representation of natural numbers.
  (Nat′ : Type)
  -- A bijection between this representation and the unary natural
  -- numbers.
  (open Bijection eq using (_↔_))
  (Nat′↔ℕ : Nat′ ↔ ℕ)
  where

open Derived-definitions-and-properties eq

open import Dec
import Erased.Level-1 eq as E₁
import Erased.Stability eq as ES
open import Logical-equivalence using (_⇔_)

open import Erased.Without-box-cong eq
open import Function-universe eq as F hiding (_∘_)
open import H-level eq
open import H-level.Closure eq
open import List eq
open import List.All.Recursive eq
open import Vec eq as Vec

private

  module N where
    open import Nat eq public
    open Prelude public using (zero; suc; _+_; _*_; _^_)

  variable
    A               : Type
    f f′ m n n′ hyp : A

------------------------------------------------------------------------
-- The wrapper

private

  -- Converts from the underlying representation to unary natural
  -- numbers.

  to-ℕ : Nat′ → ℕ
  to-ℕ = _↔_.to Nat′↔ℕ

-- Natural numbers built on top of Nat′, indexed by corresponding
-- unary natural numbers.

Nat-[_] : @0 ℕ → Type
Nat-[ m ] = ∃ λ (n : Nat′) → Erased (to-ℕ n ≡ m)

-- A non-indexed variant of Nat-[_].

Nat : Type
Nat = ∃ λ (n : Erased ℕ) → Nat-[ erased n ]

-- Returns the (erased) index.

@0 ⌊_⌋ : Nat → ℕ
⌊ [ n ] , _ ⌋ = n

------------------------------------------------------------------------
-- Some conversion functions

-- Nat-[ n ] is isomorphic to the type of natural numbers equal
-- (with erased equality proofs) to n.

Nat-[]↔Σℕ : {@0 n : ℕ} → Nat-[ n ] ↔ ∃ λ m → Erased (m ≡ n)
Nat-[]↔Σℕ {n} =
  (∃ λ (m : Nat′) → Erased (to-ℕ m ≡ n))  ↝⟨ (Σ-cong Nat′↔ℕ λ _ → F.id) ⟩□
  (∃ λ m → Erased (m ≡ n))                □

-- Nat is logically equivalent to the type of unary natural numbers.

Nat⇔ℕ : Nat ⇔ ℕ
Nat⇔ℕ =
  Nat                                                   ↔⟨⟩
  (∃ λ (n : Erased ℕ) → Nat-[ erased n ])               ↔⟨ (∃-cong λ _ → Nat-[]↔Σℕ) ⟩
  (∃ λ (n : Erased ℕ) → ∃ λ m → Erased (m ≡ erased n))  ↝⟨ Σ-Erased-Erased-singleton⇔ ⟩□
  ℕ                                                     □

-- Converts from Nat to ℕ.

Nat→ℕ : Nat → ℕ
Nat→ℕ (_ , n′ , _) = to-ℕ n′

-- Nat→ℕ is definitionally equal to the forward direction of Nat⇔ℕ.

_ : Nat→ℕ ≡ _⇔_.to Nat⇔ℕ
_ = refl _

-- Converts from ℕ to Nat.

⌈_⌉ : ℕ → Nat
⌈_⌉ = _⇔_.from Nat⇔ℕ

-- The index matches the result of Nat→ℕ.

@0 ≡⌊⌋ : ∀ n → Nat→ℕ n ≡ ⌊ n ⌋
≡⌊⌋ ([ m ] , n , eq) =
  Nat→ℕ ([ m ] , n , eq)  ≡⟨⟩
  to-ℕ n                  ≡⟨ erased eq ⟩∎
  m                       ∎

------------------------------------------------------------------------
-- Some operations for Nat-[_]

-- A helper function that can be used to define constants.

nullary-[] :
  {@0 n : ℕ}
  (n′ : Nat′) →
  @0 to-ℕ n′ ≡ n →
  Nat-[ n ]
nullary-[] n′ hyp = n′ , [ hyp ]

-- A helper function that can be used to define unary operators.

unary-[] :
  {@0 n : ℕ} {@0 f : ℕ → ℕ}
  (f′ : Nat′ → Nat′) →
  @0 (∀ n → to-ℕ (f′ n) ≡ f (to-ℕ n)) →
  Nat-[ n ] → Nat-[ f n ]
unary-[] {n} {f} f′ hyp (n′ , p) =
    f′ n′
  , [ to-ℕ (f′ n′)  ≡⟨ hyp _ ⟩
      f (to-ℕ n′)   ≡⟨ cong f (erased p) ⟩∎
      f n           ∎
    ]

-- A helper function that can be used to define n-ary operators.

n-ary-[] :
  (n : ℕ)
  {@0 ms : Vec (Erased ℕ) n}
  (@0 f : Vec ℕ n → ℕ)
  (f′ : Vec Nat′ n → Nat′) →
  @0 (∀ ms → to-ℕ (f′ ms) ≡ f (Vec.map to-ℕ ms)) →
  All (λ m → Nat-[ erased m ]) (Vec.to-list ms) →
  Nat-[ f (Vec.map erased ms) ]
n-ary-[] N.zero _ f′ hyp _ =
  nullary-[] (f′ _) (hyp _)
n-ary-[] (N.suc n) {ms} f f′ hyp ((m′ , p) , ms′) =
  n-ary-[]
    n
    (f ∘ (erased (Vec.head ms) ,_))
    (λ ms′ → f′ (m′ , ms′))
    (λ ms′ →
       to-ℕ (f′ (m′ , ms′))                         ≡⟨ hyp (m′ , ms′) ⟩
       f (to-ℕ m′              , Vec.map to-ℕ ms′)  ≡⟨ cong (λ x → f (x , _)) (erased p) ⟩∎
       f (erased (Vec.head ms) , Vec.map to-ℕ ms′)  ∎)
    ms′

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

record Operations : Type where
  infixl 8 _*2^_
  infixr 8 _^_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≟_

  field
    zero      : Nat′
    to-ℕ-zero : to-ℕ zero ≡ N.zero

    suc       : Nat′ → Nat′
    to-ℕ-suc  : ∀ n → to-ℕ (suc n) ≡ N.suc (to-ℕ n)

    _+_       : Nat′ → Nat′ → Nat′
    to-ℕ-+    : ∀ m n → to-ℕ (m + n) ≡ to-ℕ m N.+ to-ℕ n

    _*_       : Nat′ → Nat′ → Nat′
    to-ℕ-*    : ∀ m n → to-ℕ (m * n) ≡ to-ℕ m N.* to-ℕ n

    _^_       : Nat′ → Nat′ → Nat′
    to-ℕ-^    : ∀ m n → to-ℕ (m ^ n) ≡ to-ℕ m N.^ to-ℕ n

    ⌊_/2⌋     : Nat′ → Nat′
    to-ℕ-⌊/2⌋ : ∀ n → to-ℕ ⌊ n /2⌋ ≡ N.⌊ to-ℕ n /2⌋

    ⌈_/2⌉     : Nat′ → Nat′
    to-ℕ-⌈/2⌉ : ∀ n → to-ℕ ⌈ n /2⌉ ≡ N.⌈ to-ℕ n /2⌉

    _*2^_     : Nat′ → ℕ → Nat′
    to-ℕ-*2^  : ∀ m n → to-ℕ (m *2^ n) ≡ to-ℕ m N.* 2 N.^ n

    _≟_       : ∀ m n → Dec (Erased (to-ℕ m ≡ to-ℕ n))

    from-bits      : List Bool → Nat′
    to-ℕ-from-bits :
      ∀ bs →
      to-ℕ (from-bits bs) ≡
      foldl (λ n b → (if b then 1 else 0) N.+ 2 N.* n) 0 bs

    to-bits                : Nat′ → List Bool
    to-ℕ-from-bits-to-bits :
      ∀ n → to-ℕ (from-bits (to-bits n)) ≡ to-ℕ n

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

  -- Multiplication.

  infixl 7 _*_

  _*_ : {@0 m n : ℕ} → Nat-[ m ] → Nat-[ n ] → Nat-[ m N.* n ]
  _*_ = binary-[] O._*_ O.to-ℕ-*

  -- Exponentiation.

  infixr 8 _^_

  _^_ : {@0 m n : ℕ} → Nat-[ m ] → Nat-[ n ] → Nat-[ m N.^ n ]
  _^_ = binary-[] O._^_ O.to-ℕ-^

  -- Division by two, rounded downwards.

  ⌊_/2⌋ : {@0 n : ℕ} → Nat-[ n ] → Nat-[ N.⌊ n /2⌋ ]
  ⌊_/2⌋ = unary-[] O.⌊_/2⌋ O.to-ℕ-⌊/2⌋

  -- Division by two, rounded upwards.

  ⌈_/2⌉ : {@0 n : ℕ} → Nat-[ n ] → Nat-[ N.⌈ n /2⌉ ]
  ⌈_/2⌉ = unary-[] O.⌈_/2⌉ O.to-ℕ-⌈/2⌉

  -- Left shift.

  infixl 8 _*2^_

  _*2^_ : {@0 m : ℕ} → Nat-[ m ] → ∀ n → Nat-[ m N.* 2 N.^ n ]
  m *2^ n = unary-[] (O._*2^ n) (flip O.to-ℕ-*2^ n) m

  -- Equality is decidable (in a certain sense).

  infix 4 _≟_

  _≟_ :
    {@0 m n : ℕ} →
    Nat-[ m ] → Nat-[ n ] →
    Dec (Erased (m ≡ n))
  _≟_ {m} {n} (m′ , [ m≡m′ ]) (n′ , [ n≡n′ ]) =
    Dec-map
      (Erased-cong-⇔ (
         to-ℕ m′ ≡ to-ℕ n′  ↝⟨ ≡⇒↝ _ (cong₂ _≡_ m≡m′ n≡n′) ⟩□
         m ≡ n              □))
      (m′ O.≟ n′)

  -- Conversion from bits. (The most significant bit comes first.)

  from-bits :
    (bs : List Bool) →
    Nat-[ foldl (λ n b → (if b then 1 else 0) N.+ 2 N.* n) 0 bs ]
  from-bits bs = nullary-[] (O.from-bits bs) (O.to-ℕ-from-bits bs)

  -- Conversion to bits. (The most significant bit comes first.)

  to-bits :
    {@0 n : ℕ} →
    Nat-[ n ] →
    ∃ λ (bs : List Bool) →
      Erased (foldl (λ n b → (if b then 1 else 0) N.+ 2 N.* n) 0 bs ≡ n)
  to-bits {n} (n′ , [ n′≡n ]) =
      O.to-bits n′
    , [ foldl (λ n b → (if b then 1 else 0) N.+ 2 N.* n) 0
          (O.to-bits n′)                                    ≡⟨ sym $ O.to-ℕ-from-bits _ ⟩

        to-ℕ (O.from-bits (O.to-bits n′))                   ≡⟨ O.to-ℕ-from-bits-to-bits _ ⟩

        to-ℕ n′                                             ≡⟨ n′≡n ⟩∎

        n                                                   ∎
      ]

------------------------------------------------------------------------
-- Operations for Nat

private

  -- Equality is stable for the natural numbers.

  Stable-≡-ℕ : Stable-≡ ℕ
  Stable-≡-ℕ m n = Dec→Stable (m N.≟ n)

-- A helper function that can be used to define constants.

nullary :
  (@0 n : ℕ) (n′ : Nat′) →
  @0 to-ℕ n′ ≡ n →
  Nat
nullary n n′ hyp = [ n ] , nullary-[] n′ hyp

-- A first correctness result for nullary.
--
-- Note that this result holds by definition.

private

  @0 nullary-correct′ : ⌊ nullary n n′ hyp ⌋ ≡ n
  nullary-correct′ = refl _

-- A second correctness result for nullary.

nullary-correct :
  (@0 hyp : to-ℕ n′ ≡ n) →
  Nat→ℕ (nullary n n′ hyp) ≡ n
nullary-correct {n′} {n} hyp =
  Stable-≡-ℕ _ _
     [ Nat→ℕ (nullary n n′ hyp)  ≡⟨ ≡⌊⌋ (nullary n n′ hyp) ⟩
       ⌊ nullary n n′ hyp ⌋      ≡⟨⟩
       n                         ∎
     ]

-- A helper function that can be used to define unary operators.

unary :
  (@0 f : ℕ → ℕ) (f′ : Nat′ → Nat′) →
  @0 (∀ n → to-ℕ (f′ n) ≡ f (to-ℕ n)) →
  Nat → Nat
unary f f′ hyp ([ n ] , n′) = ([ f n ] , unary-[] f′ hyp n′)

-- A first correctness result for unary.
--
-- Note that this result holds by definition.

private

  @0 unary-correct′ : ⌊ unary f f′ hyp n ⌋ ≡ f ⌊ n ⌋
  unary-correct′ = refl _

-- A second correctness result for unary.

unary-correct :
  (f : ℕ → ℕ) (@0 hyp : ∀ n → to-ℕ (f′ n) ≡ f (to-ℕ n)) →
  ∀ n → Nat→ℕ (unary f f′ hyp n) ≡ f (Nat→ℕ n)
unary-correct {f′} f hyp n =
  Stable-≡-ℕ _ _
    [ Nat→ℕ (unary f f′ hyp n)  ≡⟨ ≡⌊⌋ (unary f f′ hyp n) ⟩
      ⌊ unary f f′ hyp n ⌋      ≡⟨⟩
      f ⌊ n ⌋                   ≡⟨ sym $ cong f $ ≡⌊⌋ n ⟩∎
      f (Nat→ℕ n)               ∎
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
  ∀ (n : ℕ) f {f′}
  (@0 hyp : ∀ ms → to-ℕ (f′ ms) ≡ f (Vec.map to-ℕ ms)) →
  ∀ ms →
  Nat→ℕ (n-ary n f f′ hyp ms) ≡ f (Vec.map (Nat→ℕ) ms)
n-ary-correct n f {f′} hyp ms =
  Stable-≡-ℕ _ _
    [ Nat→ℕ (n-ary n f f′ hyp ms)                   ≡⟨ ≡⌊⌋ (n-ary n f f′ hyp ms) ⟩
      ⌊ n-ary n f f′ hyp ms ⌋                       ≡⟨⟩
      f (Vec.map erased (proj₁ (_↔_.to Vec-Σ ms)))  ≡⟨ cong (f ∘ Vec.map _) proj₁-Vec-Σ ⟩
      f (Vec.map erased (Vec.map proj₁ ms))         ≡⟨ cong f $ sym Vec.map-∘ ⟩
      f (Vec.map ⌊_⌋ ms)                            ≡⟨ cong f $ sym $ Vec.map-cong ≡⌊⌋ ⟩∎
      f (Vec.map (Nat→ℕ) ms)                        ∎
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

-- A first correctness result for binary.
--
-- Note that this result holds by definition.

private

  @0 binary-correct′ : ⌊ binary f f′ hyp m n ⌋ ≡ f ⌊ m ⌋ ⌊ n ⌋
  binary-correct′ = refl _

-- A second correctness result for binary.

binary-correct :
  (f : ℕ → ℕ → ℕ)
  (@0 hyp : ∀ m n → to-ℕ (f′ m n) ≡ f (to-ℕ m) (to-ℕ n)) →
  ∀ m n →
  Nat→ℕ (binary f f′ hyp m n) ≡ f (Nat→ℕ m) (Nat→ℕ n)
binary-correct f hyp m n =
  n-ary-correct
    2
    (λ (m , n , _) → f m n)
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

  to-ℕ-zero : Nat→ℕ zero ≡ N.zero
  to-ℕ-zero = nullary-correct O.to-ℕ-zero

  -- The number's successor.

  suc : Nat → Nat
  suc = unary N.suc O.suc O.to-ℕ-suc

  to-ℕ-suc : ∀ n → Nat→ℕ (suc n) ≡ N.suc (Nat→ℕ n)
  to-ℕ-suc = unary-correct N.suc O.to-ℕ-suc

  -- Addition.

  infixl 6 _+_

  _+_ : Nat → Nat → Nat
  _+_ = binary N._+_ O._+_ O.to-ℕ-+

  to-ℕ-+ : ∀ m n → Nat→ℕ (m + n) ≡ Nat→ℕ m N.+ Nat→ℕ n
  to-ℕ-+ = binary-correct N._+_ O.to-ℕ-+

  -- Multiplication.

  infixl 7 _*_

  _*_ : Nat → Nat → Nat
  _*_ = binary N._*_ O._*_ O.to-ℕ-*

  to-ℕ-* : ∀ m n → Nat→ℕ (m * n) ≡ Nat→ℕ m N.* Nat→ℕ n
  to-ℕ-* = binary-correct N._*_ O.to-ℕ-*

  -- Multiplication.

  infixr 8 _^_

  _^_ : Nat → Nat → Nat
  _^_ = binary N._^_ O._^_ O.to-ℕ-^

  to-ℕ-^ : ∀ m n → Nat→ℕ (m ^ n) ≡ Nat→ℕ m N.^ Nat→ℕ n
  to-ℕ-^ = binary-correct N._^_ O.to-ℕ-^

  -- Division by two, rounded downwards.

  ⌊_/2⌋ : Nat → Nat
  ⌊_/2⌋ = unary N.⌊_/2⌋ O.⌊_/2⌋ O.to-ℕ-⌊/2⌋

  to-ℕ-⌊/2⌋ : ∀ n → Nat→ℕ ⌊ n /2⌋ ≡ N.⌊ Nat→ℕ n /2⌋
  to-ℕ-⌊/2⌋ = unary-correct N.⌊_/2⌋ O.to-ℕ-⌊/2⌋

  -- Division by two, rounded upwards.

  ⌈_/2⌉ : Nat → Nat
  ⌈_/2⌉ = unary N.⌈_/2⌉ O.⌈_/2⌉ O.to-ℕ-⌈/2⌉

  to-ℕ-⌈/2⌉ : ∀ n → Nat→ℕ ⌈ n /2⌉ ≡ N.⌈ Nat→ℕ n /2⌉
  to-ℕ-⌈/2⌉ = unary-correct N.⌈_/2⌉ O.to-ℕ-⌈/2⌉

  -- Left shift.

  infixl 8 _*2^_

  _*2^_ : Nat → ℕ → Nat
  m *2^ n =
    unary (λ m → m N.* 2 N.^ n) (O._*2^ n) (flip O.to-ℕ-*2^ n) m

  to-ℕ-*2^ : ∀ m n → Nat→ℕ (m *2^ n) ≡ Nat→ℕ m N.* 2 N.^ n
  to-ℕ-*2^ m n =
    unary-correct (λ m → m N.* 2 N.^ n) (flip O.to-ℕ-*2^ n) m

  -- Equality is decidable (in a certain sense).

  infix 4 _≟_

  _≟_ : (m n : Nat) → Dec (Erased (⌊ m ⌋ ≡ ⌊ n ⌋))
  (_ , m′) ≟ (_ , n′) = m′ O-[].≟ n′

  -- Conversion from bits. (The most significant bit comes first.)

  from-bits : List Bool → Nat
  from-bits bs =
    nullary
      (foldl (λ n b → (if b then 1 else 0) N.+ 2 N.* n) 0 bs)
      (O.from-bits bs)
      (O.to-ℕ-from-bits bs)

  to-ℕ-from-bits :
    ∀ bs →
    Nat→ℕ (from-bits bs) ≡
    foldl (λ n b → (if b then 1 else 0) N.+ 2 N.* n) 0 bs
  to-ℕ-from-bits bs = nullary-correct (O.to-ℕ-from-bits bs)

  -- Conversion to bits. (The most significant bit comes first.)

  to-bits : Nat → List Bool
  to-bits (_ , n′) = proj₁ (O-[].to-bits n′)

------------------------------------------------------------------------
-- Results that make use of an instantiation of the []-cong axioms

module []-cong (ax : []-cong-axiomatisation lzero) where

  open E₁.[]-cong₁ ax
  open E₁.Erased-cong ax ax
  open ES.[]-cong₁ ax
  open ES.[]-cong₂ ax ax

  ----------------------------------------------------------------------
  -- Some lemmas

  private

    -- Equality is very stable for the natural numbers.

    Very-stable-≡-ℕ : Very-stable-≡ ℕ
    Very-stable-≡-ℕ = Decidable-equality→Very-stable-≡ N._≟_

  -- Nat-[ n ] is a proposition.

  Nat-[]-propositional : {@0 n : ℕ} → Is-proposition Nat-[ n ]
  Nat-[]-propositional {n} =                                          $⟨ Very-stable-≡-ℕ ⟩
    Very-stable-≡ ℕ                                                   ↝⟨ Very-stable-congⁿ _ 1 (inverse Nat′↔ℕ) ⟩
    Very-stable-≡ Nat′                                                ↝⟨ Very-stable→Very-stableᴱ 1 ⟩
    Very-stableᴱ-≡ Nat′                                               ↝⟨ erased-singleton-with-erased-center-propositional ⟩
    Is-proposition (∃ λ (m : Nat′) → Erased (m ≡ _↔_.from Nat′↔ℕ n))  ↝⟨ (H-level-cong _ 1 $ ∃-cong λ _ → Erased-cong-↔ (inverse $
                                                                          from≡↔≡to (from-isomorphism $ inverse Nat′↔ℕ))) ⟩□
    Is-proposition (∃ λ (m : Nat′) → Erased (to-ℕ m ≡ n))             □

  -- There is a bijection between equality of two values of type Nat
  -- and erased equality of the corresponding unary natural number
  -- indices.

  ≡-for-indices↔≡ :
    {m n : Nat} →
    Erased (⌊ m ⌋ ≡ ⌊ n ⌋) ↔ m ≡ n
  ≡-for-indices↔≡ {m} {n} =
    Erased (⌊ m ⌋ ≡ ⌊ n ⌋)  ↝⟨ Erased-≡↔[]≡[] ⟩
    proj₁ m ≡ proj₁ n       ↝⟨ ignore-propositional-component Nat-[]-propositional ⟩□
    m ≡ n                   □

  ----------------------------------------------------------------------
  -- Another conversion function

  -- Nat is isomorphic to the type of unary natural numbers.

  Nat↔ℕ : Nat ↔ ℕ
  Nat↔ℕ =
    Nat                                                   ↔⟨⟩
    (∃ λ (n : Erased ℕ) → Nat-[ erased n ])               ↝⟨ (∃-cong λ _ → Nat-[]↔Σℕ) ⟩
    (∃ λ (n : Erased ℕ) → ∃ λ m → Erased (m ≡ erased n))  ↝⟨ Σ-Erased-Erased-singleton↔ ⟩□
    ℕ                                                     □

  -- The logical equivalence underlying Nat↔ℕ is definitionally equal
  -- to Nat⇔ℕ.

  _ : _↔_.logical-equivalence Nat↔ℕ ≡ Nat⇔ℕ
  _ = refl _

  ----------------------------------------------------------------------
  -- A correctness result related to the module Operations-for-Nat

  module Operations-for-Nat-correct (o : Operations) where

    private

      module O-[] = Operations-for-Nat-[] o

    open Operations-for-Nat o

    to-ℕ-from-bits-to-bits :
      ∀ n → Nat→ℕ (from-bits (to-bits n)) ≡ Nat→ℕ n
    to-ℕ-from-bits-to-bits n@(_ , n′) =
      cong Nat→ℕ $
        _↔_.to (≡-for-indices↔≡ {m = from-bits (to-bits n)} {n = n})
          [ ⌊ from-bits (to-bits n) ⌋  ≡⟨ erased (proj₂ (O-[].to-bits n′)) ⟩∎
            ⌊ n ⌋                      ∎
          ]

  ----------------------------------------------------------------------
  -- Some examples

  private

    module Nat-[]-examples (o : Operations) where

      open Operations-for-Nat-[] o

      -- Converts unary natural numbers to binary natural numbers.

      from-ℕ : ∀ n → Nat-[ n ]
      from-ℕ = proj₂ ∘ _↔_.from Nat↔ℕ

      -- Nat n is a proposition, so it is easy to prove that two
      -- values of this type are equal.

      example₁ : from-ℕ 4 + ⌊ from-ℕ 12 /2⌋ ≡ from-ℕ 10
      example₁ = Nat-[]-propositional _ _

      -- However, stating that two values of type Nat m and Nat n are
      -- equal, for equal natural numbers m and n, can be awkward.

      @0 example₂ :
        {@0 m n : ℕ} →
        (b : Nat-[ m ]) (c : Nat-[ n ]) →
        subst (λ n → Nat-[ n ]) (N.+-comm m) (b + c) ≡ c + b
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

      -- One can construct a proof showing that ⌈ 5 ⌉ is either equal
      -- or not equal to ⌈ 2 ⌉ + ⌈ 3 ⌉, but the proof does not compute
      -- to "inj₁ something" at compile-time.

      example₃ : Dec (⌈ 5 ⌉ ≡ ⌈ 2 ⌉ + ⌈ 3 ⌉)
      example₃ =
        Dec-map (_↔_.logical-equivalence ≡-for-indices↔≡)
          (⌈ 5 ⌉ ≟ ⌈ 2 ⌉ + ⌈ 3 ⌉)
