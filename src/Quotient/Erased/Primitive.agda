------------------------------------------------------------------------
-- Agda's primitive set quotients with erased higher constructors,
-- along with function and propositional extensionality
------------------------------------------------------------------------

{-# OPTIONS
      --cubical-compatible --safe --erased-propext
      --erased-quotients #-}

open import Equality

module Quotient.Erased.Primitive
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Equality.Instances-related
import Equality.Propositional as EP
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open import Extensionality eq
open import Quotient.Erased.Axiomatised eq
open import Univalence-axiom eq

import Agda.Builtin.Erased.Funext as F
import Agda.Builtin.Erased.Propext as P
import Agda.Builtin.Erased.Quotient

private
  module Q = Agda.Builtin.Erased.Quotient

private variable
  a p  : Level
  A    : Type _
  @0 R : A → A → Type _
  x y  : A

------------------------------------------------------------------------
-- Some conversion functions

private

  opaque

    -- A pointwise bijection between _≡_ and EP._≡_.

    iso : x ≡ y ↔ x EP.≡ y
    iso = all-equality-types-isomorphic eq EP.equality-with-J .proj₁

    -- A "computation" rule for iso.

    iso-refl : _↔_.to iso (refl x) ≡ EP.refl
    iso-refl =
      _↔_.from iso $
      all-equality-types-isomorphic eq EP.equality-with-J .proj₂ .proj₁

  opaque

    -- Q.Is-set is contained in Is-set.

    Is-set→Is-set : Q.Is-set A → Is-set A
    Is-set→Is-set set p q =
      trans (sym (_↔_.left-inverse-of iso _)) $
      flip trans (_↔_.left-inverse-of iso _) $
      cong (_↔_.from iso) $ _↔_.from iso $
      set (_↔_.to iso p) (_↔_.to iso q)

  opaque

    -- Is-set is contained in Q.Is-set.

    Is-set←Is-set : Is-set A → Q.Is-set A
    Is-set←Is-set set p q =
      EP.trans (EP.sym (_↔_.to iso (_↔_.right-inverse-of iso _))) $
      flip EP.trans (_↔_.to iso (_↔_.right-inverse-of iso _)) $
      EP.cong (_↔_.to iso) $ _↔_.to iso $
      set (_↔_.from iso p) (_↔_.from iso q)

------------------------------------------------------------------------
-- Function and propositional extensionality

opaque

  -- Function extensionality.

  @0 ext : Extensionality a p
  ext =
    _⇔_.from Extensionality⇔Function-extensionality
      (λ f≡g → _↔_.from iso (F.funext (λ x → _↔_.to iso (f≡g x))))

opaque

  -- Propositional extensionality.

  @0 propext : Propositional-extensionality a
  propext A-prop B-prop A⇔B =
    _↔_.from iso $
    P.propext
      (λ x y → _↔_.to iso (A-prop x y))
      (λ x y → _↔_.to iso (B-prop x y))
      (_⇔_.to A⇔B) (_⇔_.from A⇔B)

------------------------------------------------------------------------
-- Set quotients

-- The builtin quotient type is re-exported.

open Agda.Builtin.Erased.Quotient public
  using ([_]) renaming (_/_ to _/ᴱ_)

opaque

  -- The point constructor respects the quotient relation.

  @0 []-respects-relation :
       R x y → _≡_ {A = A /ᴱ R} [ x ] [ y ]
  []-respects-relation = _↔_.from iso ∘ Q.resp

opaque

  -- The quotient type is set-truncated.

  @0 /ᴱ-is-set : Is-set (A /ᴱ R)
  /ᴱ-is-set = Is-set→Is-set Q.set

opaque
  unfolding []-respects-relation

  -- An eliminator.

  eliminator :
    (P : A /ᴱ R → Type p)
    (f : ∀ x → P [ x ]) →
    @0 (∀ {x y} (r : R x y) →
        subst P ([]-respects-relation r) (f x) ≡ f y) →
    @0 (∀ x → Is-set (P x)) →
    (x : A /ᴱ R) → P x
  eliminator {A} {R} P f resp set =
    Q.qrec P f resp′ set′
    where
    opaque

      @0 resp′ : (r : R x y) → Q.subst P (Q.resp r) (f x) EP.≡ f y
      resp′ {x} {y} r =
        _↔_.to iso
          (Q.subst P (Q.resp r) (f x)                              ≡⟨ cong (flip (Q.subst _) _) (sym (_↔_.right-inverse-of iso _)) ⟩
           Q.subst P (_↔_.to iso (_↔_.from iso (Q.resp r))) (f x)  ≡⟨ elim¹ (λ eq → Q.subst P (_↔_.to iso eq) (f x) ≡ subst P eq (f x))
                                                                        (
             Q.subst P (_↔_.to iso (refl _)) (f x)                       ≡⟨ cong (flip (Q.subst _) _) iso-refl ⟩
             Q.subst P EP.refl (f x)                                     ≡⟨⟩
             f x                                                         ≡⟨ sym (subst-refl _ _) ⟩∎
             subst P (refl _) (f x)                                      ∎)
                                                                        _ ⟩
           subst P (_↔_.from iso (Q.resp r)) (f x)                 ≡⟨⟩
           subst P ([]-respects-relation r) (f x)                  ≡⟨ resp r ⟩
           f y                                                     ∎)

      @0 set′ : (x : A Q./ R) → Q.Is-set (P x)
      set′ = Is-set←Is-set ∘ set

opaque
  unfolding eliminator

  -- A computation rule for eliminator.

  eliminator-[] :
    {P : A /ᴱ R → Type p} {f : ∀ x → P [ x ]}
    {@0 p :
       ∀ {x y} (r : R x y) →
       subst P ([]-respects-relation r) (f x) ≡ f y}
    {@0 s : ∀ x → Is-set (P x)} →
    eliminator P f p s [ x ] ≡ f x
  eliminator-[] = refl _

------------------------------------------------------------------------
-- An instantiation of Quotientᴱ

-- _/ᴱ_ is a quotient operator.

quotient : Quotientᴱ
quotient .Quotientᴱ._/ᴱ_                 = _/ᴱ_
quotient .Quotientᴱ.[_]                  = [_]
quotient .Quotientᴱ.[]-respects-relation = []-respects-relation
quotient .Quotientᴱ./ᴱ-is-set            = /ᴱ-is-set
quotient .Quotientᴱ.eliminator           = eliminator _
quotient .Quotientᴱ.eliminator-[]        = eliminator-[]

open Quotientᴱ quotient public
  hiding
    (_/ᴱ_; [_]; []-respects-relation; /ᴱ-is-set; eliminator;
     eliminator-[]; module Truncation; effective; effective′;
     effective₀; ≃[]≡[]; decidable-erased-equality)

open Quotientᴱ.Truncation-/ᴱ quotient public
  hiding (module Propositional-extensionality)

private
  open module Propext {r} =
    Quotientᴱ.Truncation-/ᴱ.Propositional-extensionality
      quotient {r = r} ext propext
    public
