------------------------------------------------------------------------
-- Strict total orders with erased proofs
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Total-order.Erased
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Equality.Instances-related
import Equality.Propositional as EP
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open import Bool eq
open import Erased.Level-1 eq as E
open import Function-universe eq
import Nat eq as N

private variable
  a r   : Level
  A     : Type _
  x y z : A

------------------------------------------------------------------------
-- Strict total orders

-- Some pattern synonyms that can be used with the result of the field
-- compare introduced below.

pattern ltᵀ p = inj₁ [ p ]
pattern eqᵀ p = inj₂ (inj₁ [ p ])
pattern gtᵀ p = inj₂ (inj₂ [ p ])

-- Strict total orders on A.

record Total-order (A : Type a) (r : Level) : Type (a ⊔ lsuc r) where
  infix 4 _<_
  field
    -- The ordering relation.
    @0 _<_ : A → A → Type r

    -- A comparison function.
    compare : ∀ x y → Erased (x < y) ⊎ Erased (x ≡ y) ⊎ Erased (y < x)

    -- The relation is irreflexive.
    @0 <-irreflexive : ¬ x < x

    -- The relation is transitive.
    @0 <-trans : x < y → y < z → x < z

  infix 4 _>_

  -- The converse relation.

  @0 _>_ : A → A → Type r
  x > y = y < x

  opaque

    -- The relation is asymmetric.

    @0 <-asymmetric : x < y → ¬ y < x
    <-asymmetric x<y y<x = <-irreflexive (<-trans x<y y<x)

  opaque

    -- A derived partial order.

    infix 4 _≤_

    @0 _≤_ : A → A → Type (a ⊔ r)
    x ≤ y = x < y ⊎ x ≡ y

    -- The partial order is reflexive.

    ≤-refl : x ≤ x
    ≤-refl = inj₂ (refl _)

    -- The partial order is antisymmetric.

    @0 ≤-antisym : x ≤ y → y ≤ x → x ≡ y
    ≤-antisym (inj₂ x≡y) _          = x≡y
    ≤-antisym _          (inj₂ y≡x) = sym y≡x
    ≤-antisym (inj₁ x<y) (inj₁ y<x) = ⊥-elim (<-asymmetric x<y y<x)

    -- One form of transitivity.

    @0 <-≤-trans : x < y → y ≤ z → x < z
    <-≤-trans x<y (inj₁ y<z) = <-trans x<y y<z
    <-≤-trans x<y (inj₂ y≡z) = subst (_ <_) y≡z x<y

    -- Another form of transitivity.

    @0 ≤-<-trans : x ≤ y → y < z → x < z
    ≤-<-trans (inj₁ x<y) y<z = <-trans x<y y<z
    ≤-<-trans (inj₂ x≡y) y<z = subst (_< _) (sym x≡y) y<z

    -- The partial order is transitive.

    @0 ≤-trans : x ≤ y → y ≤ z → x ≤ z
    ≤-trans (inj₁ x<y) y≤z = inj₁ (<-≤-trans x<y y≤z)
    ≤-trans (inj₂ x≡y) y≤z = subst (_≤ _) (sym x≡y) y≤z

open Total-order

------------------------------------------------------------------------
-- Extending a total order with new bottom and top elements

-- This section is based on McBride's "How to Keep Your Neighbours in
-- Order".

-- Extends a type with two new elements.

data Extended (A : Type a) : Type a where
  min max : Extended A
  [_]     : (x : A) → Extended A

-- Extends a relation.

data Extended-order
       {A : Type a} (R : (_ _ : A) → Type r) :
       (_ _ : Extended A) → Type (a ⊔ r) where
  min-max : Extended-order R min max
  min-[]  : Extended-order R min [ y ]
  []-max  : Extended-order R [ x ] max
  []-[]   : R x y → Extended-order R [ x ] [ y ]

-- A total order can be extended with new bottom and top elements.

extended :
  {A : Type a} →
  Total-order A r →
  Total-order (Extended A) (a ⊔ r)
extended 𝓞 ._<_ =
  Extended-order (𝓞 ._<_)
extended 𝓞 .compare min   min   = inj₂ (inj₁ [ refl min ])
extended 𝓞 .compare min   [ _ ] = inj₁ [ min-[] ]
extended 𝓞 .compare min   max   = inj₁ [ min-max ]
extended 𝓞 .compare max   min   = inj₂ (inj₂ [ min-max ])
extended 𝓞 .compare max   [ _ ] = inj₂ (inj₂ [ []-max ])
extended 𝓞 .compare max   max   = inj₂ (inj₁ [ refl max ])
extended 𝓞 .compare [ _ ] min   = inj₂ (inj₂ [ min-[] ])
extended 𝓞 .compare [ _ ] max   = inj₁ [ []-max ]
extended 𝓞 .compare [ x ] [ y ] =
    ⊎-map (E.map []-[]) (⊎-map (E.map (cong [_])) (E.map []-[]))
      (𝓞 .compare x y)
extended 𝓞 .Total-order.<-irreflexive ([]-[] x<x) =
  𝓞 .<-irreflexive x<x
extended 𝓞 .<-trans min-max     ()
extended 𝓞 .<-trans min-[]      []-max      = min-max
extended 𝓞 .<-trans min-[]      ([]-[] _)   = min-[]
extended 𝓞 .<-trans []-max      ()
extended 𝓞 .<-trans ([]-[] _)   []-max      = []-max
extended 𝓞 .<-trans ([]-[] x<y) ([]-[] y<z) =
  []-[] (𝓞 .<-trans x<y y<z)

------------------------------------------------------------------------
-- An example: natural numbers

private opaque

  -- A function that converts from EP._≡_ to _≡_.

  ≡→≡ : x EP.≡ y → x ≡ y
  ≡→≡ =
    _↔_.from
      (all-equality-types-isomorphic eq EP.equality-with-J .proj₁)

opaque

  -- A hopefully reasonably efficient equality test for natural
  -- numbers.

  compare-ℕ :
    ∀ m n → Erased (m N.< n) ⊎ Erased (m ≡ n) ⊎ Erased (n N.< m)
  compare-ℕ m n with m N.<= n in leq
  … | false =
    inj₂ $ inj₂
      [ N.≰→> $ _⇔_.to (¬-cong _ (from-bijection T[<=]↔≤)) $
        _⇔_.from ¬T⇔≡false (≡→≡ leq)
      ]
  … | true with m N.== n in eq
  … | true =
    inj₂ (inj₁ [ _↔_.to T[==]↔≡ (_↔_.from T↔≡true (≡→≡ eq)) ])
  … | false =
    inj₁
      [ N.≤≢→< (_↔_.to T[<=]↔≤ (_↔_.from T↔≡true (≡→≡ leq)))
          (_⇔_.to (¬-cong _ (from-bijection T[==]↔≡)) $
           _⇔_.from ¬T⇔≡false (≡→≡ eq))
      ]

opaque

  -- A strict total order for natural numbers.

  ℕ-order : Total-order ℕ lzero
  ℕ-order .Total-order._<_           = N._<_
  ℕ-order .Total-order.compare       = compare-ℕ
  ℕ-order .Total-order.<-irreflexive = N.<-irreflexive
  ℕ-order .Total-order.<-trans       = N.<-trans
