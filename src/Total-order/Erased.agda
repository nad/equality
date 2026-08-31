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
open import Prelude as P

open import Bag-equivalence eq
open import Bijection eq using (_↔_)
open import Bool eq
open import Equality.Decidable-UIP eq
open import Erased.Level-1 eq as E
open import Function-universe eq as F hiding (id)
import H-level.Closure eq as H
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
  no-eta-equality
  infix 4 _<_
  field
    -- The ordering relation.
    @0 _<_ : A → A → Type r

    -- A comparison function.
    compare : ∀ x y → Erased (x < y) ⊎ Erased (x ≡ y) ⊎ Erased (y < x)

    -- The relation _<_ is propositional.
    @0 <-propositional : Is-proposition (x < y)

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

    -- The strict order is contained in the partial one.

    <→≤ : x < y → x ≤ y
    <→≤ = inj₁

    -- The partial order is reflexive.

    ≤-reflexive : x ≡ y → x ≤ y
    ≤-reflexive = inj₂

    -- The partial order is reflexive.

    ≤-refl : x ≤ x
    ≤-refl = ≤-reflexive (refl _)

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

  opaque

    -- If x < y, then x ≢ y.

    @0 <→≢ : x < y → x ≢ y
    <→≢ x<y x≡y =
      <-irreflexive (<-≤-trans x<y (≤-reflexive (sym x≡y)))

  opaque

    -- Erased equality is decidable for A.

    infix 4 _≟_

    _≟_ : Decidable-erased-equality A
    x ≟ y with compare x y
    … | eqᵀ x≡y = yes [ x≡y ]
    … | ltᵀ x<y = no [ (λ x≡y → <→≢ x<y x≡y) ]
    … | gtᵀ x>y = no [ (λ x≡y → <→≢ x>y (sym x≡y)) ]

  opaque

    -- The relation _<_ is decidable (with erased proofs).

    infix 4 _<?_

    _<?_ : (x y : A) → Dec-Erased (x < y)
    x <? y with compare x y
    … | inj₁ x<y = yes x<y
    … | inj₂ not =
      no [ P.[ (λ ([ x≡y ]) x<y → <→≢ x<y x≡y)
             , (λ ([ x>y ]) x<y → <-asymmetric x<y x>y)
             ]
             not
         ]

  opaque

    -- The relation _≤_ is decidable (with erased proofs).

    infix 4 _≤?_

    _≤?_ : (x y : A) → Dec-Erased (x ≤ y)
    x ≤? y with compare x y
    … | ltᵀ x<y = yes [ <→≤ x<y ]
    … | eqᵀ x≡y = yes [ ≤-reflexive x≡y ]
    … | gtᵀ x>y = no [ (λ x≤y → <-irreflexive (<-≤-trans x>y x≤y)) ]

  opaque

    -- The type A is a set.

    @0 is-set : Is-set A
    is-set =
      decidable⇒set
        (Decidable-erased-equality≃Decidable-equality _ _≟_)

  opaque
    unfolding _≤_

    -- The relation _≤_ is propositional.

    @0 ≤-propositional : Is-proposition (x ≤ y)
    ≤-propositional =
      H.⊎-closure-propositional <→≢ <-propositional is-set

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

module _ where

  open Total-order

  -- A total order can be extended with new bottom and top elements.

  extended :
    {A : Type a} →
    Total-order A r →
    Total-order (Extended A) (a ⊔ r)
  extended 𝓞 ._<_ =
    Extended-order (𝓞 ._<_)
  extended 𝓞 .<-propositional min-max   min-max   = refl _
  extended 𝓞 .<-propositional min-[]    min-[]    = refl _
  extended 𝓞 .<-propositional []-max    []-max    = refl _
  extended 𝓞 .<-propositional ([]-[] p) ([]-[] q) =
    cong []-[] (𝓞 .<-propositional p q)
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
-- Sorted lists

module @0 Sorted-list {A : Type a} (O : Total-order A r) where

  open Total-order (extended O)

  private variable
    lb lb₁ lb₂ ub ub₁ ub₂ : Extended A
    xs xs₁ xs₂            : List A

  -- Sorted lb ub xs means that xs is sorted (strictly), with lb as a
  -- strict lower bound and ub as a strict upper bound.
  --
  -- This predicate is based on McBride's "How to Keep Your Neighbours
  -- in Order".

  Sorted : Extended A → Extended A → List A → Type (a ⊔ r)
  Sorted lb ub []       = lb < ub
  Sorted lb ub (x ∷ xs) = lb < [ x ] × Sorted [ x ] ub xs

  opaque

    -- Sorted is propositional.

    Sorted-propositional : ∀ xs → Is-proposition (Sorted lb ub xs)
    Sorted-propositional []       = <-propositional
    Sorted-propositional (_ ∷ xs) =
      H.×-closure 1 <-propositional (Sorted-propositional xs)

  opaque

    -- The lower bound is strictly below the upper bound.

    Sorted→lower-bound-<-upper-bound :
      ∀ xs → Sorted lb ub xs → lb < ub
    Sorted→lower-bound-<-upper-bound []       lb<ub     = lb<ub
    Sorted→lower-bound-<-upper-bound (_ ∷ xs) (lb< , s) =
      <-trans lb< (Sorted→lower-bound-<-upper-bound xs s)

  opaque

    -- Elements of a sorted list are between the bounds (strictly).

    Sorted→∈→<< :
      Sorted lb ub xs → x ∈ xs → lb < [ x ] × [ x ] < ub
    Sorted→∈→<< {lb} {ub} {xs = _ ∷ ys} (lb<y , s) (inj₁ x≡y) =
      subst (λ x → lb < [ x ] × [ x ] < ub) (sym x≡y)
        (lb<y , Sorted→lower-bound-<-upper-bound ys s)
    Sorted→∈→<< {xs = _ ∷ _} (lb<y , s) (inj₂ x∈ys) =
      Σ-map (<-trans lb<y) id (Sorted→∈→<< s x∈ys)

  opaque

    -- Sorted, set equivalent lists are equal.

    Sorted→≈→≡ :
      Sorted lb₁ ub₁ xs₁ → Sorted lb₂ ub₂ xs₂ → xs₁ ∼[ set ] xs₂ →
      xs₁ ≡ xs₂
    Sorted→≈→≡ {xs₁ = []} {xs₂ = []} _ _ _ =
      refl _
    Sorted→≈→≡ {xs₁ = []} {xs₂ = x ∷ xs} _ _ []≈x∷xs =
                   $⟨ inj₁ (refl _) ⟩
      x ∈ x ∷ xs   →⟨ _⇔_.from ([]≈x∷xs _) ⟩
      x ∈ []       ↔⟨⟩
      ⊥            →⟨ ⊥-elim ⟩□
      [] ≡ x ∷ xs  □
    Sorted→≈→≡ {xs₁ = x ∷ xs} {xs₂ = []} _ _ x∷xs≈[] =
                   $⟨ inj₁ (refl _) ⟩
      x ∈ x ∷ xs   →⟨ _⇔_.to (x∷xs≈[] _) ⟩
      x ∈ []       ↔⟨⟩
      ⊥            →⟨ ⊥-elim ⟩□
      x ∷ xs ≡ []  □
    Sorted→≈→≡
      {xs₁ = x₁ ∷ xs₁} {xs₂ = x₂ ∷ xs₂}
      (<x₁ , x₁<xs₁) (<x₂ , x₂<xs₂) x₁∷xs₁≈x₂∷xs₂ =
      let x₁∈ : x₁ ∈ x₂ ∷ xs₂
          x₁∈ = _⇔_.to (x₁∷xs₁≈x₂∷xs₂ _) (inj₁ (refl _))

          x₂∈ : x₂ ∈ x₁ ∷ xs₁
          x₂∈ = _⇔_.from (x₁∷xs₁≈x₂∷xs₂ _) (inj₁ (refl _))

          x₁≡x₂ : x₁ ≡ x₂
          x₁≡x₂ = case x₁∈ of λ where
            (inj₁ x₁≡x₂)  → x₁≡x₂
            (inj₂ x₁∈xs₂) →
              case x₂∈ of λ where
                (inj₁ x₂≡x₁)  → sym x₂≡x₁
                (inj₂ x₂∈xs₁) →
                  let x₂<x₁ , _ = Sorted→∈→<< x₂<xs₂ x₁∈xs₂
                      x₁<x₂ , _ = Sorted→∈→<< x₁<xs₁ x₂∈xs₁
                  in
                  ⊥-elim (<-asymmetric x₁<x₂ x₂<x₁)

          xs₁≈xs₂ : xs₁ ∼[ set ] xs₂
          xs₁≈xs₂ y =
            y ∈ xs₁                ↝⟨ (inverse $ ⇔⊎→×¬⇔ F.id λ y≡x₁ y∈xs₁ →
                                       <→≢ (Sorted→∈→<< x₁<xs₁ y∈xs₁ .proj₁) (cong [_] (sym y≡x₁))) ⟩
            y ∈ x₁ ∷ xs₁ × y ≢ x₁  ↝⟨ x₁∷xs₁≈x₂∷xs₂ _ ×-cong →-cong _ (≡⇒↝ _ (cong (_ ≡_) x₁≡x₂)) F.id ⟩
            y ∈ x₂ ∷ xs₂ × y ≢ x₂  ↝⟨ (⇔⊎→×¬⇔ F.id λ y≡x₂ y∈xs₂ →
                                       <→≢ (Sorted→∈→<< x₂<xs₂ y∈xs₂ .proj₁) (cong [_] (sym y≡x₂))) ⟩□
            y ∈ xs₂                □
      in
      cong₂ _∷_ x₁≡x₂ (Sorted→≈→≡ x₁<xs₁ x₂<xs₂ xs₁≈xs₂)

  -- A variant of Sorted that allows the lower bound to be equal to the
  -- first element (or the upper bound, if the list is empty).

  Sorted-≤₁ : Extended A → Extended A → List A → Type (a ⊔ r)
  Sorted-≤₁ lb ub []       = lb ≤ ub
  Sorted-≤₁ lb ub (x ∷ xs) = lb ≤ [ x ] × Sorted [ x ] ub xs

  opaque

    -- Sorted-≤₁ is propositional.

    Sorted-≤₁-propositional :
      ∀ xs → Is-proposition (Sorted-≤₁ lb ub xs)
    Sorted-≤₁-propositional []       = ≤-propositional
    Sorted-≤₁-propositional (_ ∷ xs) =
      H.×-closure 1 ≤-propositional (Sorted-propositional xs)

  opaque

    -- One can convert from Sorted-≤₁ to Sorted.

    Sorted-≤₁→Sorted :
      ∀ xs → lb₁ < lb₂ → Sorted-≤₁ lb₂ ub xs → Sorted lb₁ ub xs
    Sorted-≤₁→Sorted [] lb₁<lb₂ lb₂≤ub =
      <-≤-trans lb₁<lb₂ lb₂≤ub
    Sorted-≤₁→Sorted (_ ∷ _) lb₁<lb₂ (lb₂≤ , s) =
      <-≤-trans lb₁<lb₂ lb₂≤ , s

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
  ℕ-order .Total-order._<_             = N._<_
  ℕ-order .Total-order.<-propositional = H.≤-propositional
  ℕ-order .Total-order.compare         = compare-ℕ
  ℕ-order .Total-order.<-irreflexive   = N.<-irreflexive
  ℕ-order .Total-order.<-trans         = N.<-trans
