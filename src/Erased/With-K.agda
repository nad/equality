------------------------------------------------------------------------
-- Some theory of Erased, developed using the K rule and propositional
-- equality
------------------------------------------------------------------------

-- This module instantiates and reexports code from Erased.

{-# OPTIONS --with-K --safe #-}

module Erased.With-K where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Embedding equality-with-J as Emb using (Is-embedding)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
import Erased.Basics equality-with-J as EB
open import H-level equality-with-J
open import Injection equality-with-J using (Injective)

private
  variable
    a p : Level
    A   : Type a

------------------------------------------------------------------------
-- Code related to the module Erased

-- Given an erased proof of equality of x and y one can show that
-- [ x ] is equal to [ y ].

[]-cong : {@0 A : Type a} {@0 x y : A} →
          EB.Erased (x ≡ y) → EB.[ x ] ≡ EB.[ y ]
[]-cong EB.[ refl ] = refl

-- []-cong is an equivalence.

[]-cong-equivalence :
  {@0 A : Type a} {@0 x y : A} →
  Is-equivalence ([]-cong {x = x} {y = y})
[]-cong-equivalence {x = x} {y = y} = _≃_.is-equivalence (Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = []-cong
      ; from = λ eq → EB.[ cong EB.erased eq ]
      }
    ; right-inverse-of = λ { refl → refl }
    }
  ; left-inverse-of = λ { EB.[ refl ] → refl }
  }))

-- []-cong maps [ refl ] to refl (by definition).

[]-cong-[refl] :
  {@0 A : Type a} {@0 x : A} →
  []-cong EB.[ refl {x = x} ] ≡ refl {x = EB.[ x ]}
[]-cong-[refl] = refl

-- The []-cong axioms can be instantiated.

instance-of-[]-cong-axiomatisation : EB.[]-cong-axiomatisation a
instance-of-[]-cong-axiomatisation = λ where
  .EB.[]-cong-axiomatisation.[]-cong             → []-cong
  .EB.[]-cong-axiomatisation.[]-cong-equivalence → []-cong-equivalence
  .EB.[]-cong-axiomatisation.[]-cong-[refl]      → []-cong-[refl]

-- Some reexported definitions.

open import Erased equality-with-J instance-of-[]-cong-axiomatisation
  public
  hiding ([]-cong; []-cong-equivalence; []-cong-[refl]; Π-Erased↔Π0[])

------------------------------------------------------------------------
-- Other code

-- [_]→ is injective.

Injective-[] : {@0 A : Type a} → Injective ([_]→ {A = A})
Injective-[] refl = refl

-- [_]→ is an embedding.

Is-embedding-[] : {@0 A : Type a} → Is-embedding ([_]→ {A = A})
Is-embedding-[] _ _ refl = (refl , refl) , λ { (refl , refl) → refl }

-- If Erased A is a proposition, then A is a proposition.

Is-proposition-Erased→Is-proposition :
  {@0 A : Type a} →
  Is-proposition (Erased A) → Is-proposition A
Is-proposition-Erased→Is-proposition prop x y =
  Injective-[] (prop [ x ] [ y ])

-- A variant of the previous result.

H-level′-1-Erased→H-level′-1 :
  {@0 A : Type a} →
  H-level′ 1 (Erased A) → H-level′ 1 A
H-level′-1-Erased→H-level′-1 prop x y
  with proj₁ (prop [ x ] [ y ])
... | refl = refl , λ { refl → refl }

-- Equality is always very stable.

Very-stable-≡-trivial : Very-stable-≡ A
Very-stable-≡-trivial =
  _⇔_.from (Very-stable-≡↔Is-embedding-[] _)
           Is-embedding-[]

-- The following four results are inspired by a result in
-- Mishra-Linger's PhD thesis (see Section 5.4.1).

-- There is a bijection between (x : Erased A) → P x and
-- (@0 x : A) → P [ x ].
--
-- This is a strengthening of the result of the same name from Erased.

Π-Erased↔Π0[] :
  {@0 A : Type a} {@0 P : Erased A → Type p} →
  ((x : Erased A) → P x) ↔ ((@0 x : A) → P [ x ])
Π-Erased↔Π0[] = record
  { surjection = record
    { logical-equivalence = Π-Erased⇔Π0
    ; right-inverse-of = λ _ → refl
    }
  ; left-inverse-of = λ _ → refl
  }

-- There is an equivalence between (x : Erased A) → P x and
-- (@0 x : A) → P [ x ].
--
-- This is not proved by converting Π-Erased↔Π0[] to an equivalence,
-- because the type arguments of the conversion function in
-- Equivalence are not erased, and A and P can only be used in erased
-- contexts.

Π-Erased≃Π0[] :
  {@0 A : Type a} {@0 P : Erased A → Type p} →
  ((x : Erased A) → P x) ≃ ((@0 x : A) → P [ x ])
Π-Erased≃Π0[] = record
  { to             = λ f x → f [ x ]
  ; is-equivalence = λ f →
      ( (λ ([ x ]) → f x)
      , refl
      )
      , λ { (_ , refl) → refl }
  }

-- There is a bijection between (x : Erased A) → P (erased x) and
-- (@0 x : A) → P x.

Π-Erased↔Π0 :
  {@0 A : Type a} {@0 P : A → Type p} →
  ((x : Erased A) → P (erased x)) ↔ ((@0 x : A) → P x)
Π-Erased↔Π0 = Π-Erased↔Π0[]

-- There is an equivalence between (x : Erased A) → P (erased x) and
-- (@0 x : A) → P x.

Π-Erased≃Π0 :
  {@0 A : Type a} {@0 P : A → Type p} →
  ((x : Erased A) → P (erased x)) ≃ ((@0 x : A) → P x)
Π-Erased≃Π0 = Π-Erased≃Π0[]

private

  -- As an aside it is possible to prove the four previous results
  -- without relying on eta-equality for Erased. However, the code
  -- makes use of extensionality, and it also makes use of
  -- eta-equality for Π. (The use of η-equality for Π could perhaps be
  -- avoided, but Agda does not, at the time of writing, provide a
  -- simple way to turn off this kind of η-equality.)

  data Erased-no-η (@0 A : Type a) : Type a where
    [_] : @0 A → Erased-no-η A

  @0 erased-no-η : Erased-no-η A → A
  erased-no-η [ x ] = x

  -- Some lemmas.

  Π-Erased-no-η→Π0[] :
    {@0 A : Type a} {@0 P : Erased-no-η A → Type p} →
    ((x : Erased-no-η A) → P x) → (@0 x : A) → P [ x ]
  Π-Erased-no-η→Π0[] f x = f [ x ]

  Π0[]→Π-Erased-no-η :
    {@0 A : Type a} (@0 P : Erased-no-η A → Type p) →
    ((@0 x : A) → P [ x ]) → (x : Erased-no-η A) → P x
  Π0[]→Π-Erased-no-η _ f [ x ] = f x

  Π0[]→Π-Erased-no-η-Π-Erased-no-η→Π0[] :
    {@0 A : Type a} {@0 P : Erased-no-η A → Type p}
    (f : (x : Erased-no-η A) → P x) (x : Erased-no-η A) →
    Π0[]→Π-Erased-no-η P (Π-Erased-no-η→Π0[] f) x ≡ f x
  Π0[]→Π-Erased-no-η-Π-Erased-no-η→Π0[] f [ x ] = refl

  -- There is a bijection between (x : Erased-no-η A) → P x and
  -- (@0 x : A) → P [ x ] (assuming extensionality).

  Π-Erased-no-η↔Π0[] :
    {@0 A : Type a} {@0 P : Erased-no-η A → Type p} →
    Extensionality′ (Erased-no-η A) P →
    ((x : Erased-no-η A) → P x) ↔ ((@0 x : A) → P [ x ])
  Π-Erased-no-η↔Π0[] {P = P} ext = record
    { surjection = record
      { logical-equivalence = record
        { to   = Π-Erased-no-η→Π0[]
        ; from = Π0[]→Π-Erased-no-η _
        }
      ; right-inverse-of    = λ _ → refl
      }
    ; left-inverse-of = λ f →
        ext (Π0[]→Π-Erased-no-η-Π-Erased-no-η→Π0[] f)
    }

  -- There is an equivalence between (x : Erased-no-η A) → P x and
  -- (@0 x : A) → P [ x ] (assuming extensionality).
  --
  -- This is not proved by converting Π-Erased-no-η↔Π0[] to an
  -- equivalence, because the type arguments of the conversion
  -- function in Equivalence are not erased, and A and P can only be
  -- used in erased contexts.

  Π-Erased-no-η≃Π0[] :
    {@0 A : Type a} {@0 P : Erased-no-η A → Type p} →
    Extensionality′ (Erased-no-η A) P →
    ((x : Erased-no-η A) → P x) ≃ ((@0 x : A) → P [ x ])
  Π-Erased-no-η≃Π0[] {A = A} {P = P} ext = record
    { to             = λ f x → f [ x ]
    ; is-equivalence = λ f →
        ( Π0[]→Π-Erased-no-η _ f
        , refl
        )
        , λ { (g , refl) → lemma g }
    }
    where
    Σ-≡,≡→≡′ :
      {@0 A : Type a} {@0 P : A → Type p} {p₁ p₂ : Σ A P} →
      (p : proj₁ p₁ ≡ proj₁ p₂) →
      subst P p (proj₂ p₁) ≡ proj₂ p₂ →
      p₁ ≡ p₂
    Σ-≡,≡→≡′ refl refl = refl

    subst-lemma :
      ({g} g′ : (x : Erased-no-η A) → P x)
      (eq₁ : Π0[]→Π-Erased-no-η P (λ (@0 x) → g′ [ x ]) ≡ g)
      (eq₂ : (λ (@0 x) → g′ [ x ]) ≡ (λ (@0 x) → g [ x ])) →
      subst (λ f → (λ (@0 x) → f [ x ]) ≡ (λ (@0 x) → g [ x ]))
            eq₁ eq₂ ≡
      refl
    subst-lemma _ refl refl = refl

    lemma :
      (g : (x : Erased-no-η A) → P x) →
      (Π0[]→Π-Erased-no-η P (λ (@0 x) → g [ x ]) , refl) ≡ (g , refl)
    lemma g = Σ-≡,≡→≡′ eq (subst-lemma g eq refl)
      where
      eq = ext (Π0[]→Π-Erased-no-η-Π-Erased-no-η→Π0[] g)

  -- There is a bijection between
  -- (x : Erased-no-η A) → P (erased-no-η x) and (@0 x : A) → P x
  -- (assuming extensionality).

  Π-Erased-no-η↔Π0 :
    {@0 A : Type a} {@0 P : A → Type p} →
    Extensionality′ (Erased-no-η A) (P ∘ erased-no-η) →
    ((x : Erased-no-η A) → P (erased-no-η x)) ↔ ((@0 x : A) → P x)
  Π-Erased-no-η↔Π0 = Π-Erased-no-η↔Π0[]

  -- There is an equivalence between
  -- (x : Erased-no-η A) → P (erased-no-η x) and (@0 x : A) → P x
  -- (assuming extensionality).

  Π-Erased-no-η≃Π0 :
    {@0 A : Type a} {@0 P : A → Type p} →
    Extensionality′ (Erased-no-η A) (P ∘ erased-no-η) →
    ((x : Erased-no-η A) → P (erased-no-η x)) ≃ ((@0 x : A) → P x)
  Π-Erased-no-η≃Π0 = Π-Erased-no-η≃Π0[]
