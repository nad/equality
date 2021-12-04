------------------------------------------------------------------------
-- The accessibility predicate and well-founded induction
------------------------------------------------------------------------

-- Partly based on "Constructing Recursion Operators in Intuitionistic
-- Type Theory" by Lawrence C Paulson.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Accessibility {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Erased.Basics as Erased
open import Prelude

open import Function-universe eq hiding (id; _∘_)
open import H-level.Closure eq
import Nat eq as Nat
open import Preimage eq using (_⁻¹_)

private
  variable
    a b ℓ p q r r₁ r₂ : Level
    A                 : Type a
    P                 : A → Type p
    x z               : A

------------------------------------------------------------------------
-- Accessibility and well-founded relations

-- The accessibility predicate.
--
-- The element x is accessible with respect to _<_ if every element
-- that is below x is accessible.

data Acc {A : Type a} (_<_ : A → A → Type r) (x : A) :
         Type (a ⊔ r) where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

-- A relation is well-founded if every element is accessible.

Well-founded : {A : Type a} → (A → A → Type r) → Type (a ⊔ r)
Well-founded _<_ = ∀ x → Acc _<_ x

-- The accessibility predicate is propositional (assuming
-- extensionality).

Acc-propositional :
  {A : Type a} {_<_ : A → A → Type r} {x : A} →
  Extensionality (a ⊔ r) (a ⊔ r) →
  Is-proposition (Acc _<_ x)
Acc-propositional {a = a} {r = r} ext (acc f) (acc g) =
  cong acc $
  apply-ext (lower-extensionality r lzero ext) λ y →
  apply-ext (lower-extensionality a lzero ext) λ y<x →
  Acc-propositional ext (f y y<x) (g y y<x)

-- Well-founded is pointwise propositional (assuming extensionality).

Well-founded-propositional :
  {A : Type a} {_<_ : A → A → Type r} →
  Extensionality (a ⊔ r) (a ⊔ r) →
  Is-proposition (Well-founded _<_)
Well-founded-propositional {r = r} ext =
  Π-closure (lower-extensionality r lzero ext) 1 λ _ →
  Acc-propositional ext

------------------------------------------------------------------------
-- Well-founded induction

-- Well-founded induction for accessible values.
--
-- Note that the accessibility argument is erased.

well-founded-induction-Acc :
  {@0 A : Type a} {@0 _<_ : A → A → Type r}
  (@0 P : A → Type p) →
  (∀ x → (∀ y → @0 y < x → P y) → P x) →
  ∀ x → @0 Acc _<_ x → P x
well-founded-induction-Acc P f x (acc g) =
  f x (λ y y<x → well-founded-induction-Acc P f y (g y y<x))

-- Well-founded induction for well-founded relations.

well-founded-induction :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} →
  @0 Well-founded _<_ →
  (@0 P : A → Type p) →
  (∀ x → (∀ y → @0 y < x → P y) → P x) →
  ∀ x → P x
well-founded-induction wf P f x =
  well-founded-induction-Acc P f x (wf x)

------------------------------------------------------------------------
-- Specific examples of well-founded relations

-- The always undefined relation is well-founded.

Well-founded-⊥ : Well-founded (λ (_ _ : A) → ⊥ {ℓ = ℓ})
Well-founded-⊥ _ = acc λ _ ()

-- The relation Nat._<_ is well-founded.

Well-founded-ℕ : Well-founded Nat._<_
Well-founded-ℕ m = acc (helper m)
  where
  helper : ∀ m n → n Nat.< m → Acc Nat._<_ n
  helper zero    n (Nat.≤-refl′ eq)   = ⊥-elim (Nat.0≢+ (sym eq))
  helper zero    n (Nat.≤-step′ _ eq) = ⊥-elim (Nat.0≢+ (sym eq))
  helper (suc m) n (Nat.≤-refl′ eq)   =
    subst (Acc Nat._<_) (sym (Nat.cancel-suc eq)) (Well-founded-ℕ m)
  helper (suc m) n (Nat.≤-step′ p eq) =
    helper m n (subst (n Nat.<_) (Nat.cancel-suc eq) p)

-- The value x is below sup y f if x is equal to f z for some z.

_<W_ :
  {A : Type a} {P : A → Type p} →
  W A P → W A P → Type (a ⊔ p)
x <W sup _ f = f ⁻¹ x

-- The relation _<W_ is well-founded.

Well-founded-W : Well-founded {A = W A P} _<W_
Well-founded-W (sup _ f) = acc λ where
  (sup x g) (y , eq) → subst (Acc _) eq (Well-founded-W (f y))

------------------------------------------------------------------------
-- Transitive closure

-- The transitive closure of a relation.

infix  4 _[_]⋆_
infixr 5 _∷_

data _[_]⋆_
       {A : Type a}
       (x : A)
       (_<_ : A → A → Type r)
       (y : A) :
       Type (a ⊔ r) where
  [_] : x < y → x [ _<_ ]⋆ y
  _∷_ : x < z → z [ _<_ ]⋆ y → x [ _<_ ]⋆ y

-- A relation contains a cycle if its transitive closure contains a
-- loop.

Cycle : {A : Type a} → (A → A → Type r) → Type (a ⊔ r)
Cycle _<_ = ∃ λ x → x [ _<_ ]⋆ x

------------------------------------------------------------------------
-- Lemmas that can be used to prove that relations are well-founded,
-- or that values are accessible

-- If _<₂_ is contained in _<₁_, then Acc _<₁_ x implies Acc _<₂_ x.

Acc-map :
  {@0 A : Type a} {@0 x : A}
  {@0 _<₁_ : A → A → Type r₁}
  {@0 _<₂_ : A → A → Type r₂} →
  @0 (∀ {x y} → x <₂ y → x <₁ y) →
  @0 Acc _<₁_ x → Acc _<₂_ x
Acc-map f (acc g) = acc λ y y<₂x → Acc-map f (g y (f y<₂x))

-- If _<₂_ is contained in _<₁_, then Well-founded _<₁_ implies
-- Well-founded _<₂_.

Well-founded-map :
  {@0 A : Type a}
  {@0 _<₁_ : A → A → Type r₁}
  {@0 _<₂_ : A → A → Type r₂} →
  @0 (∀ {x y} → x <₂ y → x <₁ y) →
  @0 Well-founded _<₁_ → Well-founded _<₂_
Well-founded-map f wf x = Acc-map f (wf x)

-- Acc _<_ x is erasure-stable.

Acc-erasure-stable :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} {@0 x : A} →
  Erased.Stable (Acc _<_ x)
Acc-erasure-stable [ a ] = Acc-map id a

-- Well-founded _<_ is erasure-stable.

Well-founded-erasure-stable :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} →
  Erased.Stable (Well-founded _<_)
Well-founded-erasure-stable [ wf ] = Well-founded-map id wf

-- If f x is accessible with respect to _<_, then x is accessible with
-- respect to _<_ on f.

Acc-on :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B}
  {@0 _<_ : B → B → Type r} {@0 x : A} →
  @0 Acc _<_ (f x) → Acc (_<_ on f) x
Acc-on {f = f} (acc g) = acc λ y fy<fx → Acc-on (g (f y) fy<fx)

-- If _<_ is well-founded, then _<_ on f is well-founded.

Well-founded-on :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B}
  {@0 _<_ : B → B → Type r} →
  @0 Well-founded _<_ → Well-founded (_<_ on f)
Well-founded-on {f = f} wf x = Acc-on (wf (f x))

-- If x is accessible with respect to _<_, then x is also accessible
-- with respect to the transitive closure of _<_.

Acc-⋆ :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} {@0 x : A} →
  @0 Acc _<_ x → Acc _[ _<_ ]⋆_ x
Acc-⋆ {_<_ = _<_} {x = x} (acc f) = acc helper
  where
  helper : ∀ y → y [ _<_ ]⋆ x → Acc _[ _<_ ]⋆_ y
  helper y [ y<x ]      = Acc-⋆ (f y y<x)
  helper y (y<z ∷ z<⋆x) = case helper _ z<⋆x of λ where
    (acc f) → f y [ y<z ]

-- If a relation is well-founded, then its transitive closure is also
-- well-founded.

Well-founded-⋆ :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} →
  @0 Well-founded _<_ →
  Well-founded _[ _<_ ]⋆_
Well-founded-⋆ wf x = Acc-⋆ (wf x)

-- Acc _<_ x is equivalent to Acc (λ x y → ↑ ℓ (x < y)) x (assuming
-- extensionality).

Acc-↑ :
  ∀ {A : Type a} {_<_ : A → A → Type r} {x} →
  Acc _<_ x ↝[ a ⊔ ℓ ⊔ r ∣ a ⊔ ℓ ⊔ r ]
  Acc (λ x y → ↑ ℓ (x < y)) x
Acc-↑ {a = a} {r = r} {ℓ = ℓ} {_<_ = _<_} =
  generalise-ext?
    (record { to = to; from = from })
    (λ ext → to-from ext , from-to ext)
  where
  to : ∀ {@0 x} → Acc _<_ x → Acc (λ x y → ↑ ℓ (x < y)) x
  to (acc f) = acc λ y y<x → to (f y (lower y<x))

  from : ∀ {@0 x} → Acc (λ x y → ↑ ℓ (x < y)) x → Acc _<_ x
  from (acc f) = acc λ y y<x → from (f y (lift y<x))

  module _ (ext : Extensionality (a ⊔ ℓ ⊔ r) (a ⊔ ℓ ⊔ r)) where
    to-from : (p : Acc (λ x y → ↑ ℓ (x < y)) x) → to (from p) ≡ p
    to-from (acc f) =
      cong acc $
      apply-ext (lower-extensionality (ℓ ⊔ r) lzero ext) λ y   →
      apply-ext (lower-extensionality a       lzero ext) λ y<x →
      to-from (f y y<x)

    from-to : (p : Acc _<_ x) → from (to p) ≡ p
    from-to (acc f) =
      cong acc $
      apply-ext (lower-extensionality (ℓ ⊔ r) ℓ ext) λ y   →
      apply-ext (lower-extensionality (a ⊔ ℓ) ℓ ext) λ y<x →
      from-to (f y y<x)

-- Well-founded _<_ is equivalent to
-- Well-founded (λ x y → ↑ ℓ (x < y)) (assuming extensionality).

Well-founded-↑ :
  ∀ {A : Type a} {_<_ : A → A → Type r} →
  Well-founded _<_ ↝[ a ⊔ ℓ ⊔ r ∣ a ⊔ ℓ ⊔ r ]
  Well-founded (λ x y → ↑ ℓ (x < y))
Well-founded-↑ {r = r} {ℓ = ℓ} {_<_ = _<_} {k = k} ext =
  (∀ x → Acc _<_ x)                    ↝⟨ (∀-cong (lower-extensionality? k (ℓ ⊔ r) lzero ext) λ _ → Acc-↑ ext) ⟩□
  (∀ x → Acc (λ x y → ↑ ℓ (x < y)) x)  □

------------------------------------------------------------------------
-- Some negative results

-- If x < x, then x is not accessible with respect to _<_.

<→¬-Acc :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} {x : A} →
  x < x → ¬ Acc _<_ x
<→¬-Acc x<x (acc f) = <→¬-Acc x<x (f _ x<x)

-- If x < x, then _<_ is not well-founded.

<→¬-Well-founded :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} {x : A} →
  x < x → ¬ Well-founded _<_
<→¬-Well-founded x<x wf = <→¬-Acc x<x (wf _)

-- If a relation contains a cycle, then it is not well-founded.

Cycle→¬-Well-founded :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} →
  Cycle _<_ → ¬ Well-founded _<_
Cycle→¬-Well-founded {_<_ = _<_} (x , x<⋆x) =
                             $⟨ x<⋆x ⟩
  x [ _<_ ]⋆ x               →⟨ <→¬-Well-founded ⟩
  ¬ Well-founded _[ _<_ ]⋆_  →⟨ _∘ (λ wf → Well-founded-⋆ wf) ⟩□
  ¬ Well-founded _<_         □
