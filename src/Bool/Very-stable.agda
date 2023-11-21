------------------------------------------------------------------------
-- Very stable booleans
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the very stable booleans uses path
-- equality, but the supplied notion of equality is used for other
-- things.

import Equality.Path as P

module Bool.Very-stable
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

import Equality.Path.Univalence as PU
open import Prelude as Bool hiding (true; false)

open import Bijection equality-with-J using (_↔_)
import Bijection P.equality-with-J as PB
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equality.Path.Isomorphisms.Univalence eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Erased.Cubical eq as Erased
import Erased.Cubical P.equality-with-paths as PE
open import Function-universe equality-with-J hiding (_∘_)
open import Injection equality-with-J using (Injective)

private
  variable
    a p          : Level
    A            : Type a
    P            : A → Type p
    b f r r-[] t : A

------------------------------------------------------------------------
-- Very stable booleans

-- Very stable booleans.
--
-- This type uses a construction due to Thierry Coquand and Fabian
-- Ruch. I think this construction is a variant of a construction due
-- to Rijke, Shulman and Spitters (see "Modalities in Homotopy Type
-- Theory").

data B̃ool : Type where
  true false : B̃ool
  stable     : Erased B̃ool → B̃ool
  stable-[]ᴾ : (b : B̃ool) → stable [ b ] P.≡ b

-- The constructor stable is a left inverse of [_].

stable-[] : (b : B̃ool) → stable [ b ] ≡ b
stable-[] = _↔_.from ≡↔≡ ∘ stable-[]ᴾ

-- B̃ool is very stable.

Very-stable-B̃ool : Very-stable B̃ool
Very-stable-B̃ool = Stable→Left-inverse→Very-stable stable stable-[]

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

elimᴾ :
  (P : B̃ool → Type p) →
  P true →
  P false →
  (r : ∀ b → Erased (P (erased b)) → P (stable b)) →
  (∀ b (p : P b) →
   P.[ (λ i → P (stable-[]ᴾ b i)) ] r [ b ] [ p ] ≡ p) →
  ∀ b → P b
elimᴾ P t f r r-[] = λ where
  true             → t
  false            → f
  (stable b)       → r b [ elimᴾ P t f r r-[] (erased b) ]
  (stable-[]ᴾ b i) → r-[] b (elimᴾ P t f r r-[] b) i

-- A non-dependent eliminator, expressed using paths.

recᴾ :
  A → A →
  (r : Erased B̃ool → Erased A → A) →
  (∀ b p → r [ b ] [ p ] P.≡ p) →
  B̃ool → A
recᴾ = elimᴾ _

-- A dependent eliminator, expressed using equality.

elim :
  (P : B̃ool → Type p) →
  P true →
  P false →
  (r : ∀ b → Erased (P (erased b)) → P (stable b)) →
  (∀ b (p : P b) → subst P (stable-[] b) (r [ b ] [ p ]) ≡ p) →
  ∀ b → P b
elim P t f r r-[] = elimᴾ P t f r (λ b p → subst≡→[]≡ (r-[] b p))

-- A "computation" rule.

elim-stable-[] :
  dcong (elim P t f r r-[]) (stable-[] b) ≡
  r-[] b (elim P t f r r-[] b)
elim-stable-[] = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator, expressed using equality.

rec :
  A → A →
  (r : Erased B̃ool → Erased A → A) →
  (∀ b p → r [ b ] [ p ] ≡ p) →
  B̃ool → A
rec t f r r-[] = recᴾ t f r (λ b p → _↔_.to ≡↔≡ (r-[] b p))

-- A "computation" rule.

rec-stable-[] :
  cong (rec t f r r-[]) (stable-[] b) ≡
  r-[] b (rec t f r r-[] b)
rec-stable-[] = cong-≡↔≡ (refl _)

-- A dependent eliminator that can be used when eliminating into very
-- stable type families.

elim-Very-stable :
  (P : B̃ool → Type p) →
  P true →
  P false →
  (∀ b → Very-stable (P b)) →
  ∀ b → P b
elim-Very-stable P t f s =
  elim P t f
    (λ { b@([ _ ]) →
         Erased (P (erased b))  ↝⟨ Erased.map (subst P (

             erased b                ≡⟨ sym $ stable-[] (erased b) ⟩∎
             stable b                ∎)) ⟩

         Erased (P (stable b))  ↝⟨ Very-stable→Stable 0 (s (stable b)) ⟩□

         P (stable b)           □ })
    (λ b p →
       Very-stable→Stable 1 (Very-stable→Very-stable-≡ 0 (s b)) _ _
         [ subst P (stable-[] b)
             (_≃_.from Eq.⟨ _ , s (stable [ b ]) ⟩
                [ subst P (sym $ stable-[] b) p ])                ≡⟨ cong (subst P (stable-[] b)) $ sym $
                                                                     _≃_.left-inverse-unique Eq.⟨ _ , s (stable [ b ]) ⟩ erased refl _ ⟩
           subst P (stable-[] b)
             (erased [ subst P (sym $ stable-[] b) p ])           ≡⟨⟩

           subst P (stable-[] b) (subst P (sym $ stable-[] b) p)  ≡⟨ subst-subst-sym _ _ _ ⟩∎

           p                                                      ∎
         ])

-- A non-dependent eliminator that can be used when eliminating into
-- very stable type families.

rec-Very-stable : A → A → Very-stable A → B̃ool → A
rec-Very-stable t f s = elim-Very-stable _ t f (λ _ → s)

------------------------------------------------------------------------
-- Some properties

private
 module Dummy where

  -- A function mapping very stable booleans to types: true is mapped
  -- to the unit type and false to the empty type.

  private

    T̃′ : B̃ool → Σ Type Very-stable
    T̃′ = rec-Very-stable
      (⊤ , Very-stable-⊤)
      (⊥ , Very-stable-⊥)
      (Very-stable-∃-Very-stable ext univ)

  T̃ : B̃ool → Type
  T̃ = proj₁ ∘ T̃′

  -- Some computation rules that hold by definition.

  _ : T̃ true ≡ ⊤
  _ = refl _

  _ : T̃ false ≡ ⊥
  _ = refl _

  -- The output of T̃ is very stable.

  Very-stable-T̃ : ∀ b → Very-stable (T̃ b)
  Very-stable-T̃ = proj₂ ∘ T̃′

  -- The values true and false are not equal.

  true≢false : true ≢ false
  true≢false =
    true ≡ false      ↝⟨ cong T̃ ⟩
    T̃ true ≡ T̃ false  ↔⟨⟩
    ⊤ ≡ ⊥             ↝⟨ (λ eq → ≡⇒↝ _ eq _) ⟩□
    ⊥                 □

module Alternative-T̃ where

  -- A direct implementation of T̃.

  private

    T̃′ : B̃ool → Σ Type PE.Very-stable

  T̃ : B̃ool → Type
  T̃ b = proj₁ (T̃′ b)

  Very-stable-T̃ : ∀ b → PE.Very-stable (T̃ b)
  Very-stable-T̃ b = proj₂ (T̃′ b)

  T̃′ true             = ⊤ , PE.Very-stable-⊤
  T̃′ false            = ⊥ , PE.Very-stable-⊥
  T̃′ (stable [ b ])   = PE.Erased (T̃ b) , PE.Very-stable-Erased
  T̃′ (stable-[]ᴾ b i) = lemma₁ i , lemma₂ i
    where
    lemma₁ : PE.Erased (T̃ b) P.≡ T̃ b
    lemma₁ = PU.≃⇒≡ (PE.Very-stable→Stable 0 (Very-stable-T̃ b))

    lemma₂ :
      P.[ (λ i → PE.Very-stable (lemma₁ i)) ]
        PE.Very-stable-Erased ≡ Very-stable-T̃ b
    lemma₂ =
      P.heterogeneous-irrelevance₀
        (PE.Very-stable-propositional P.ext)

  -- Some computation rules that hold by definition.

  _ : T̃ true ≡ ⊤
  _ = refl _

  _ : T̃ false ≡ ⊥
  _ = refl _

  _ : T̃ (stable [ b ]) ≡ PE.Erased (T̃ b)
  _ = refl _

open Dummy public

-- A function from booleans to very stable booleans.

from-Bool : Bool → B̃ool
from-Bool = if_then true else false

-- The function from-Bool is injective.
--
-- This lemma was suggested by Mike Shulman.

from-Bool-injective : Injective from-Bool
from-Bool-injective {x = Bool.true}  {y = Bool.true}  = λ _ → refl _
from-Bool-injective {x = Bool.true}  {y = Bool.false} = ⊥-elim ∘ true≢false
from-Bool-injective {x = Bool.false} {y = Bool.true}  = ⊥-elim ∘ true≢false ∘ sym
from-Bool-injective {x = Bool.false} {y = Bool.false} = λ _ → refl _

-- B̃ool is equivalent to Erased Bool.
--
-- This lemma was suggested by Mike Shulman.

B̃ool≃Erased-Bool : B̃ool ≃ Erased Bool
B̃ool≃Erased-Bool = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = λ b →
        Very-stable→Stable 0
          (Very-stable→Very-stable-≡ 0 Very-stable-Erased _ _)
          [ to (from b)                           ≡⟨⟩
            to (stable [ from-Bool (erased b) ])  ≡⟨ cong to (stable-[] _) ⟩
            to (from-Bool (erased b))             ≡⟨ lemma (erased b) ⟩
            [ erased b ]                          ≡⟨ Erased-η ⟩
            b                                     ∎
          ]
    }
  ; left-inverse-of = elim-Very-stable
      _
      (stable-[] true)
      (stable-[] false)
      (λ _ → Very-stable→Very-stable-≡ 0 Very-stable-B̃ool _ _)
  })
  where
  to = rec-Very-stable [ Bool.true ] [ Bool.false ] Very-stable-Erased

  from = stable ∘ Erased.map from-Bool

  lemma : ∀ b → to (from-Bool b) ≡ [ b ]
  lemma Bool.true  = refl _
  lemma Bool.false = refl _

------------------------------------------------------------------------
-- An example

private

  -- At the time of writing it is unclear if there is a reasonable way
  -- to compile very stable booleans. The constructors true and false
  -- are distinct, and it is reasonable to think that a compiler will
  -- compile them in different ways. Now consider the following two
  -- very stable booleans:

  b₁ : B̃ool
  b₁ = stable [ true ]

  b₂ : B̃ool
  b₂ = stable [ false ]

  -- The first one is equal to true, and the second one is equal to
  -- false:

  _ : b₁ ≡ true
  _ = stable-[] true

  _ : b₂ ≡ false
  _ = stable-[] false

  -- However, unlike the constructors true and false, b₁ and b₂ should
  -- be compiled in the same way, because the argument to [_] is
  -- erased.

  -- One question, raised by Andrea Vezzosi, is whether it is possible
  -- to write a program that gives /observably/ different results
  -- (after erasure) for true and false. If this is the case, then the
  -- erasure mechanism is not well-behaved.
