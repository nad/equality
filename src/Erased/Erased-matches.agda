------------------------------------------------------------------------
-- Results related to Erased that are implemented using
-- --erased-matches
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --erased-matches #-}

open import Equality

module Erased.Erased-matches
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Accessibility eq as A using (Acc; Well-founded)
open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_)
open import Equivalence.Erased.Contractible-preimages eq
  using (_⁻¹ᴱ_; Contractibleᴱ)
open import Erased.Level-1 eq as EL₁
  hiding (module []-cong₁; module []-cong₂-⊔; module []-cong;
          module Extensionality)
open import Erased.Stability eq as ES
  hiding (module []-cong₁; module []-cong;
          module Extensionality)
open import Extensionality eq hiding (module Extensionality)
open import For-iterated-equality eq
open import Function-universe eq hiding (_∘_)
open import H-level eq
open import H-level.Closure eq
open import Modality.Basics eq
open import Preimage eq using (_⁻¹_)
open import Surjection eq using (_↠_)
open import Univalence-axiom eq

private variable
  a b ℓ ℓ₁ ℓ₂ p r : Level
  A               : Type a
  x               : A

------------------------------------------------------------------------
-- Some lemmas that can be proved without --erased-matches if an
-- instantiation of the []-cong axioms is available

-- Erased (Erased A) is isomorphic to Erased A.
--
-- See also Erased.Level-1.[]-cong₁.Erased-Erased↔Erased.

Erased-Erased↔Erased :
  {@0 A : Type a} →
  Erased (Erased A) ↔ Erased A
Erased-Erased↔Erased = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ x → [ erased (erased x) ]
      ; from = [_]→
      }
    ; right-inverse-of = λ { [ _ ] → refl _ }
    }
  ; left-inverse-of = λ { [ [ _ ] ] → refl _ }
  }

-- An isomorphism relating _⁻¹ᴱ_ to _⁻¹_.
--
-- See also
-- Equivalence.Erased.Contractible-preimages.[]-cong₁.Erased-⁻¹ᴱ↔Erased-⁻¹.

Erased-⁻¹ᴱ↔Erased-⁻¹ :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} {@0 y : B} →
  Erased (f ⁻¹ᴱ y) ↔ Erased (f ⁻¹ y)
Erased-⁻¹ᴱ↔Erased-⁻¹ {f} {y} =
  Erased (∃ λ x → Erased (f x ≡ y))             ↝⟨ Erased-Σ↔Σ ⟩
  (∃ λ x → Erased (Erased (f (erased x) ≡ y)))  ↝⟨ (∃-cong λ _ → Erased-Erased↔Erased) ⟩
  (∃ λ x → Erased (f (erased x) ≡ y))           ↝⟨ inverse Erased-Σ↔Σ ⟩□
  Erased (∃ λ x → f x ≡ y)                      □

-- An isomorphism relating Contractibleᴱ to Contractible.
--
-- See also
-- Equivalence.Erased.Contractible-preimages.[]-cong₁.Erased-Contractibleᴱ↔Erased-Contractible.

Erased-Contractibleᴱ↔Erased-Contractible :
  {@0 A : Type a} →
  Erased (Contractibleᴱ A) ↔ Erased (Contractible A)
Erased-Contractibleᴱ↔Erased-Contractible =
  Erased (∃ λ x → Erased (∀ y → x ≡ y))           ↝⟨ Erased-Σ↔Σ ⟩
  (∃ λ x → Erased (Erased (∀ y → erased x ≡ y)))  ↝⟨ (∃-cong λ _ → Erased-Erased↔Erased) ⟩
  (∃ λ x → Erased (∀ y → erased x ≡ y))           ↝⟨ inverse Erased-Σ↔Σ ⟩□
  Erased (∃ λ x → ∀ y → x ≡ y)                    □

-- Erased A is very stable.
--
-- See also Erased.Stability.[]-cong₁.Very-stable-Erased.

Very-stable-Erased :
  {@0 A : Type a} → Very-stable (Erased A)
Very-stable-Erased =
  _≃_.is-equivalence (Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { from = λ ([ x ]) → [ erased x ]
        }
      ; right-inverse-of = λ { [ [ x ] ] → refl [ [ x ] ] }
      }
    ; left-inverse-of = λ { [ x ] → refl [ x ] }
    }))

-- ∃ λ (A : Set a) → Very-stable A is stable.
--
-- This result is based on Theorem 3.11 in "Modalities in Homotopy
-- Type Theory" by Rijke, Shulman and Spitters.
--
-- See also Erased.Stability.[]-cong₁.Stable-∃-Very-stable.

Stable-∃-Very-stable : Stable (∃ λ (A : Type a) → Very-stable A)
Stable-∃-Very-stable [ A ] = Erased (proj₁ A) , Very-stable-Erased

-- ∃ λ (A : Set a) → Very-stable A is stable with erased proofs.
--
-- This result is based on Theorem 3.11 in "Modalities in Homotopy
-- Type Theory" by Rijke, Shulman and Spitters.
--
-- See also Erased.Stability.[]-cong₁.Stable-∃-Very-stableᴱ.

Stable-∃-Very-stableᴱ : Stable (∃ λ (A : Type a) → Very-stableᴱ A)
Stable-∃-Very-stableᴱ [ A ] =
  Erased (proj₁ A) , Very-stable→Very-stableᴱ 0 Very-stable-Erased

-- ∃ λ (A : Set a) → Very-stableᴱ A is very stable (with erased
-- proofs), assuming extensionality and univalence.
--
-- This result is based on Theorem 3.11 in "Modalities in Homotopy
-- Type Theory" by Rijke, Shulman and Spitters.
--
-- See also Erased.Stability.[]-cong₁.Very-stableᴱ-∃-Very-stableᴱ.

Very-stableᴱ-∃-Very-stableᴱ :
  @0 Extensionality a a →
  @0 Univalence a →
  Very-stableᴱ (∃ λ (A : Type a) → Very-stableᴱ A)
Very-stableᴱ-∃-Very-stableᴱ ext univ =
  Stable→Left-inverse→Very-stableᴱ Stable-∃-Very-stableᴱ inv
  where
  @0 inv : ∀ p → Stable-∃-Very-stableᴱ [ p ] ≡ p
  inv (A , s) = Σ-≡,≡→≡
    (Erased A  ≡⟨ ≃⇒≡ univ (Very-stable→Stable 0 (Very-stableᴱ→Very-stable 0 s)) ⟩∎
     A         ∎)
    (Very-stableᴱ-propositional ext _ _)

------------------------------------------------------------------------
-- Some types are logically equivalent to []-cong-axiomatisation ℓ if
-- --erased-matches is used

-- The type []-cong-axiomatisation ℓ is equivalent to
-- 2-extendable-along-[]→-axiomatisation ℓ (assuming extensionality).

[]-cong-axiomatisation≃2-extendable-along-[]→-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ]
  2-extendable-along-[]→-axiomatisation ℓ
[]-cong-axiomatisation≃2-extendable-along-[]→-axiomatisation {ℓ} =
  generalise-ext?-prop
    {B = 2-extendable-along-[]→-axiomatisation ℓ}
    (record
       { to   = λ ax s → ES.[]-cong₁.extendable ax (λ _ → s) 2
       ; from =
           2-extendable-along-[]→-axiomatisation ℓ         ↝⟨ _$ Very-stable-Erased ⟩
           2-extendable-along-[]→-Erased-axiomatisation ℓ  ↝⟨ _⇔_.from ([]-cong-axiomatisation≃2-extendable-along-[]→-Erased-axiomatisation _) ⟩□
           []-cong-axiomatisation ℓ                        □
       })
    ([]-cong-axiomatisation-propositional ∘
     lower-extensionality lzero _)
    2-extendable-along-[]→-axiomatisation-propositional

-- The type []-cong-axiomatisation ℓ is equivalent to
-- ∞-extendable-along-[]→-axiomatisation ℓ (assuming extensionality).

[]-cong-axiomatisation≃∞-extendable-along-[]→-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ]
  ∞-extendable-along-[]→-axiomatisation ℓ
[]-cong-axiomatisation≃∞-extendable-along-[]→-axiomatisation {ℓ} =
  generalise-ext?-prop
    {B = ∞-extendable-along-[]→-axiomatisation ℓ}
    (record
       { to   = λ ax s → ES.[]-cong₁.extendable ax (λ _ → s)
       ; from =
           ∞-extendable-along-[]→-axiomatisation ℓ  ↝⟨ (λ ext s → ext s 2) ⟩
           2-extendable-along-[]→-axiomatisation ℓ  ↝⟨ _⇔_.from ([]-cong-axiomatisation≃2-extendable-along-[]→-axiomatisation _) ⟩□
           []-cong-axiomatisation ℓ                 □
       })
    ([]-cong-axiomatisation-propositional ∘
     lower-extensionality lzero _)
    ∞-extendable-along-[]→-axiomatisation-propositional

------------------------------------------------------------------------
-- Some lemmas related to W

-- Erased commutes with W up to logical equivalence.

Erased-W⇔W :
  {@0 A : Type a} {@0 P : A → Type p} →
  Erased (W A P) ⇔ W (Erased A) (λ x → Erased (P (erased x)))
Erased-W⇔W {A} {P} = record { to = to; from = from }
  where
  to : Erased (W A P) → W (Erased A) (λ x → Erased (P (erased x)))
  to [ sup x f ] = sup [ x ] (λ ([ y ]) → to [ f y ])

  from : W (Erased A) (λ x → Erased (P (erased x))) → Erased (W A P)
  from (sup [ x ] f) = [ sup x (λ y → erased (from (f [ y ]))) ]

-- If A is very stable with erased proofs, then W A P is very stable
-- with erased proofs (assuming extensionality).

Very-stableᴱ-W :
  {@0 A : Type a} {@0 P : A → Type p} →
  @0 Extensionality p (a ⊔ p) →
  Very-stableᴱ A →
  Very-stableᴱ (W A P)
Very-stableᴱ-W {A} {P} ext s =
  _≃ᴱ_.is-equivalence $
  EEq.↔→≃ᴱ [_]→ from []∘from from∘[]
  where
  A≃ᴱE-A : A ≃ᴱ Erased A
  A≃ᴱE-A = EEq.⟨ _ , s ⟩₀

  from : Erased (W A P) → W A P
  from [ sup x f ] = sup
    (_≃ᴱ_.from A≃ᴱE-A [ x ])
    (λ y → from [ f (subst P (_≃ᴱ_.left-inverse-of A≃ᴱE-A x) y) ])

  @0 from∘[] : ∀ x → from [ x ] ≡ x
  from∘[] (sup x f) = curry (_↠_.to (W-≡,≡↠≡ ext))
    (_≃ᴱ_.left-inverse-of A≃ᴱE-A x)
    (λ y → from∘[] (f (subst P (_≃ᴱ_.left-inverse-of A≃ᴱE-A x) y)))

  @0 []∘from : ∀ x → [ from x ] ≡ x
  []∘from [ x ] = cong [_]→ (from∘[] x)

------------------------------------------------------------------------
-- Some lemmas related to Acc and Well-founded

-- The operator _[_]Erased_ lifts a relation from A to Erased A.

_[_]Erased_ :
  {@0 A : Type a} → Erased A → @0 (A → A → Type r) → Erased A → Type r
x [ _<_ ]Erased y = Erased (erased x < erased y)

-- Erased "commutes" with Acc (up to logical equivalence).
--
-- See also Erased-Acc below.

Erased-Acc-⇔ :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} {@0 x : A} →
  Erased (Acc _<_ x) ⇔ Acc _[ _<_ ]Erased_ [ x ]
Erased-Acc-⇔ {_<_} = record
  { to   = λ acc → to (erased acc)
  ; from = [_]→ ∘ from
  }
  where
  to : ∀ {@0 x} → @0 Acc _<_ x → Acc _[ _<_ ]Erased_ [ x ]
  to (A.acc f) = A.acc λ { [ y ] [ y<x ] → to (f y y<x) }

  from : ∀ {@0 x} → Acc _[ _<_ ]Erased_ [ x ] → Acc _<_ x
  from (A.acc f) = A.acc λ y y<x → from (f [ y ] [ y<x ])

-- Erased "commutes" with Well-founded (up to logical equivalence).
--
-- See also Erased-Well-founded below.

Erased-Well-founded-⇔ :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} →
  Erased (Well-founded _<_) ⇔ Well-founded _[ _<_ ]Erased_
Erased-Well-founded-⇔ {_<_} =
  Erased (Well-founded _<_)            ↔⟨⟩
  Erased (∀ x → Acc _<_ x)             ↝⟨ Erased-Π↔Π-Erased _ ⟩
  (∀ x → Erased (Acc _<_ (erased x)))  ↝⟨ (∀-cong _ λ { [ _ ] → Erased-Acc-⇔ }) ⟩
  (∀ x → Acc _[ _<_ ]Erased_ x)        ↔⟨⟩
  Well-founded _[ _<_ ]Erased_         □

-- Acc _<_ x is stable.

Stable-Acc :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} {@0 x : A} →
  Stable (Acc _<_ x)
Stable-Acc [ A.acc f ] = A.acc (λ y y<x → Stable-Acc [ f y y<x ])

-- Well-founded _<_ is stable.

Stable-Well-founded :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} →
  Stable (Well-founded _<_)
Stable-Well-founded =
  Stable-Π λ _ → Stable-Acc

------------------------------------------------------------------------
-- Some results that follow if the []-cong axioms hold for the maximum
-- of two universe levels (as well as for the two universe levels)

module []-cong₂-⊔
  (ax₁ : []-cong-axiomatisation ℓ₁)
  (ax₂ : []-cong-axiomatisation ℓ₂)
  (ax  : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
  where

  open EL₁.[]-cong₁ ax
  open ES.[]-cong₁ ax

  ----------------------------------------------------------------------
  -- Some lemmas related to W

  -- Erased commutes with W (assuming extensionality).

  Erased-W↔W :
    {@0 A : Type ℓ₁} {@0 P : A → Type ℓ₂} →
    Erased (W A P) ↝[ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ]
    W (Erased A) (λ x → Erased (P (erased x)))
  Erased-W↔W {A} {P} =
    generalise-ext?
      Erased-W⇔W
      (λ ext → to∘from ext , from∘to ext)
    where
    open _⇔_ Erased-W⇔W

    to∘from :
      Extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) →
      (x : W (Erased A) (λ x → Erased (P (erased x)))) →
      to (from x) ≡ x
    to∘from ext (sup [ x ] f) =
      cong (sup [ x ]) $
      apply-ext ext λ { y@([ _ ]) →
        to [ erased (from (f y)) ]  ≡⟨ cong to Erased-η ⟩
        to (from (f y))             ≡⟨ to∘from ext (f y) ⟩∎
        f y                         ∎ }

    from∘to :
      Extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) →
      (x : Erased (W A P)) → from (to x) ≡ x
    from∘to ext [ sup x f ] =
      []-cong
        [ (cong (sup x) $
           apply-ext ext λ y →
           cong erased (from∘to ext [ f y ]))
        ]

  -- If A is very stable, then W A P is very stable (assuming
  -- extensionality).

  Very-stable-W :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    Extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) →
    Very-stable A →
    Very-stable (W A P)
  Very-stable-W {A} {P} ext s =
    _≃_.is-equivalence $
    Eq.↔⇒≃ (record
      { surjection = record
        { logical-equivalence = record
          { to   = [_]→
          ; from = from
          }
        ; right-inverse-of = []∘from
        }
      ; left-inverse-of = from∘[]
      })
    where
    module E = _≃_ Eq.⟨ _ , s ⟩

    from : Erased (W A P) → W A P
    from [ sup x f ] = sup
      (E.from [ x ])
      (λ y → from [ f (subst P (E.left-inverse-of x) y) ])

    from∘[] : ∀ x → from [ x ] ≡ x
    from∘[] (sup x f) = curry (_↠_.to (W-≡,≡↠≡ ext))
      (E.left-inverse-of x)
      (λ y → from∘[] (f (subst P (E.left-inverse-of x) y)))

    []∘from : ∀ x → [ from x ] ≡ x
    []∘from [ x ] = []-cong [ from∘[] x ]

  -- A generalisation of Very-stable-W.

  Very-stable-Wⁿ :
    {A : Type ℓ₁} {P : A → Type ℓ₂} →
    Extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) →
    ∀ n →
    For-iterated-equality n Very-stable A →
    For-iterated-equality n Very-stable (W A P)
  Very-stable-Wⁿ {A} {P} ext n =
    For-iterated-equality-W
      ext
      n
      ([]-cong₂.Very-stable-cong ax ax _ ∘ from-isomorphism)
      (Very-stable-Π ext)
      Very-stable-Σ
      (Very-stable-W ext)

  ----------------------------------------------------------------------
  -- Some lemmas related to Acc and Well-founded

  -- Erased "commutes" with Acc.

  Erased-Acc :
    {@0 A : Type ℓ₁} {@0 _<_ : A → A → Type ℓ₂} {@0 x : A} →
    Erased (Acc _<_ x) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ]
    Acc _[ _<_ ]Erased_ [ x ]
  Erased-Acc = generalise-ext?-prop
    Erased-Acc-⇔
    (λ ext → H-level-Erased 1 (A.Acc-propositional ext))
    A.Acc-propositional

  -- Erased "commutes" with Well-founded.

  Erased-Well-founded :
    {@0 A : Type ℓ₁} {@0 _<_ : A → A → Type ℓ₂} →
    Erased (Well-founded _<_) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ]
    Well-founded _[ _<_ ]Erased_
  Erased-Well-founded = generalise-ext?-prop
    Erased-Well-founded-⇔
    (λ ext → H-level-Erased 1 (A.Well-founded-propositional ext))
    A.Well-founded-propositional

  -- Acc _<_ x is very stable (assuming extensionality).

  Very-stable-Acc :
    {A : Type ℓ₁} {_<_ : A → A → Type ℓ₂} {x : A} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Very-stable (Acc _<_ x)
  Very-stable-Acc {_<_} ext =
    Stable→Left-inverse→Very-stable Stable-Acc lemma
    where
    lemma : (a : Acc _<_ x) → Stable-Acc [ a ] ≡ a
    lemma (A.acc f) =
      cong A.acc $
      apply-ext (lower-extensionality ℓ₂ lzero ext) λ y →
      apply-ext (lower-extensionality ℓ₁ lzero ext) λ y<x →
      lemma (f y y<x)

  -- Well-founded _<_ is very stable (assuming extensionality).

  Very-stable-Well-founded :
    {A : Type ℓ₁} {_<_ : A → A → Type ℓ₂} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Very-stable (Well-founded _<_)
  Very-stable-Well-founded {_<_} ext =
    Very-stable-Π (lower-extensionality ℓ₂ lzero ext) λ _ →
    Very-stable-Acc ext

------------------------------------------------------------------------
-- Some results that follow if the []-cong axioms hold for a single
-- universe level

module []-cong₁ (ax : []-cong-axiomatisation ℓ) where

  open ES.[]-cong₁ ax

  ----------------------------------------------------------------------
  -- Some lemmas related to W

  -- A generalisation of Very-stableᴱ-W.

  Very-stableᴱ-Wⁿ :
    {A : Type ℓ} {P : A → Type p} →
    Extensionality p (ℓ ⊔ p) →
    ∀ n →
    For-iterated-equality n Very-stableᴱ A →
    For-iterated-equality n Very-stableᴱ (W A P)
  Very-stableᴱ-Wⁿ {A} {P} ext n =
    For-iterated-equality-W
      ext
      n
      (≃ᴱ→Very-stableᴱ→Very-stableᴱ ∘ from-isomorphism)
      (Very-stableᴱ-Π ext)
      Very-stableᴱ-Σ
      (Very-stableᴱ-W ext)

  -- The modality is W-modal (assuming extensionality).

  Erased-W-modal :
    Extensionality ℓ ℓ →
    W-modal Erased-modality
  Erased-W-modal ext = []-cong₂-⊔.Very-stable-W ax ax ax ext

  ----------------------------------------------------------------------
  -- A lemma related to Acc

  -- The modality is accessibility-modal.

  Erased-accessibility-modal :
    Modality.Accessibility-modal Erased-modality
  Erased-accessibility-modal {_<_} =
      (λ {x} →
         Acc _<_ x                  →⟨ _⇔_.to Erased-Acc-⇔ ∘ [_]→ ⟩
         Acc _[ _<_ ]Erased_ [ x ]  →⟨ (λ acc →
                                          A.Acc-map
                                            (map λ (y , z , ≡[y] , ≡[z] , y<z) →
                                                   subst (uncurry _<_)
                                                     (sym $ cong₂ _,_ (cong erased ≡[y]) (cong erased ≡[z]))
                                                     y<z)
                                            acc) ⟩□
         Acc _[ _<_ ]◯_ [ x ]       □)
    , Stable-Acc
    where
    open Modality Erased-modality using (_[_]◯_)

------------------------------------------------------------------------
-- Some results that follow if the []-cong axioms hold for all
-- universe levels

module []-cong (ax : ∀ {ℓ} → []-cong-axiomatisation ℓ) where

  private
    open module BC₂ {ℓ₁ ℓ₂} =
      []-cong₂-⊔ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) ax
      public
    open module BC₁ {ℓ} = []-cong₁ (ax {ℓ = ℓ})
      public

------------------------------------------------------------------------
-- Some lemmas that were proved assuming (perhaps conditional)
-- function extensionality and also that one or more instances of the
-- []-cong axioms can be implemented, reproved without the latter
-- assumptions

module Extensionality where

  ----------------------------------------------------------------------
  -- Some lemmas related to W

  -- Erased commutes with W (assuming extensionality).
  --
  -- See also Erased-W↔W above: That property is defined assuming that
  -- the []-cong axioms can be instantiated, but is stated using
  -- _↝[ p ∣ a ⊔ p ]_ instead of _↝[ a ⊔ p ∣ a ⊔ p ]_.

  Erased-W↔W :
    {@0 A : Type a} {@0 P : A → Type p} →
    Erased (W A P) ↝[ a ⊔ p ∣ a ⊔ p ]
    W (Erased A) (λ x → Erased (P (erased x)))
  Erased-W↔W {a} {p} =
    generalise-ext?
      Erased-W⇔W
      (λ ext →
         let bij = []-cong₂-⊔.Erased-W↔W
                     (Extensionality→[]-cong-axiomatisation $
                      lower-extensionality p p ext)
                     (Extensionality→[]-cong-axiomatisation $
                      lower-extensionality a a ext)
                     (Extensionality→[]-cong-axiomatisation ext)
                     (lower-extensionality a lzero ext)
         in _↔_.right-inverse-of bij , _↔_.left-inverse-of bij)

  -- The modality is W-modal (assuming extensionality).

  Erased-W-modal :
    (ext : Extensionality ℓ ℓ) →
    W-modal (ES.Extensionality.Erased-modality {ℓ = ℓ} ext)
  Erased-W-modal ext =
    []-cong₁.Erased-W-modal
      (Extensionality→[]-cong-axiomatisation ext)
      ext
