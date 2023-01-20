------------------------------------------------------------------------
-- Bi-invertibility with erased proofs
------------------------------------------------------------------------

-- The development is based on the presentation of bi-invertibility
-- (for types and functions) and related things in the HoTT book, but
-- adapted to a setting with erasure.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
open import Prelude as P hiding (id; _∘_; [_,_])

-- The code is parametrised by something like a "raw" category.

module Bi-invertibility.Erased
  {e⁺}
  (eq : ∀ {a p} → Equality-with-J a p e⁺)
  {o h}
  (Obj : Type o)
  (Hom : Obj → Obj → Type h)
  (id : {A : Obj} → Hom A A)
  (_∘′_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C)
  where

open import Bi-invertibility eq Obj Hom id _∘′_ as Bi
  using (Has-left-inverse; Has-right-inverse; Is-bi-invertible;
         Has-quasi-inverse; _≊_; _≅_)
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_)
open import Equivalence.Erased.Contractible-preimages eq as ECP
  using (Contractibleᴱ)
open import Erased.Without-box-cong eq
open import Function-universe eq as F hiding (id; _∘_)
open import Logical-equivalence using (_⇔_)
open import H-level eq
open import H-level.Closure eq
open import Preimage eq
open import Surjection eq using (_↠_)

private
  variable
    A B : Obj
    f   : Hom A B

  infixr 9 _∘_

  _∘_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
  _∘_ = _∘′_

-- Has-left-inverseᴱ f means that f has a left inverse. The proof is
-- erased.

Has-left-inverseᴱ : @0 Hom A B → Type h
Has-left-inverseᴱ f = ∃ λ f⁻¹ → Erased (f⁻¹ ∘ f ≡ id)

-- Has-right-inverseᴱ f means that f has a right inverse. The proof is
-- erased.

Has-right-inverseᴱ : @0 Hom A B → Type h
Has-right-inverseᴱ f = ∃ λ f⁻¹ → Erased (f ∘ f⁻¹ ≡ id)

-- Is-bi-invertibleᴱ f means that f has a left inverse and a (possibly
-- distinct) right inverse. The proofs are erased.

Is-bi-invertibleᴱ : @0 Hom A B → Type h
Is-bi-invertibleᴱ f =
  Has-left-inverseᴱ f × Has-right-inverseᴱ f

-- Has-quasi-inverseᴱ f means that f has a left inverse that is also a
-- right inverse. The proofs are erased.

Has-quasi-inverseᴱ : @0 Hom A B → Type h
Has-quasi-inverseᴱ f =
  ∃ λ f⁻¹ → Erased (f ∘ f⁻¹ ≡ id × f⁻¹ ∘ f ≡ id)

-- Some notions of isomorphism or equivalence.

infix 4 _≊ᴱ_ _≅ᴱ_

_≊ᴱ_ : Obj → Obj → Type h
A ≊ᴱ B = ∃ λ (f : Hom A B) → Is-bi-invertibleᴱ f

_≅ᴱ_ : Obj → Obj → Type h
A ≅ᴱ B = ∃ λ (f : Hom A B) → Has-quasi-inverseᴱ f

-- Morphisms with quasi-inverses are bi-invertible.

Has-quasi-inverseᴱ→Is-bi-invertibleᴱ :
  (@0 f : Hom A B) → Has-quasi-inverseᴱ f → Is-bi-invertibleᴱ f
Has-quasi-inverseᴱ→Is-bi-invertibleᴱ _ (f⁻¹ , [ f∘f⁻¹≡id , f⁻¹∘f≡id ]) =
    (f⁻¹ , [ f⁻¹∘f≡id ])
  , (f⁻¹ , [ f∘f⁻¹≡id ])

≅ᴱ→≊ᴱ : A ≅ᴱ B → A ≊ᴱ B
≅ᴱ→≊ᴱ = ∃-cong λ f → Has-quasi-inverseᴱ→Is-bi-invertibleᴱ f

-- Some conversion functions.

Has-left-inverse→Has-left-inverseᴱ :
  Has-left-inverse f → Has-left-inverseᴱ f
Has-left-inverse→Has-left-inverseᴱ = Σ-map P.id [_]→

@0 Has-left-inverse≃Has-left-inverseᴱ :
  Has-left-inverse f ≃ Has-left-inverseᴱ f
Has-left-inverse≃Has-left-inverseᴱ {f} =
  (∃ λ f⁻¹ →         f⁻¹ ∘ f ≡ id )  ↔⟨ (∃-cong λ _ → inverse $ erased Erased↔) ⟩□
  (∃ λ f⁻¹ → Erased (f⁻¹ ∘ f ≡ id))  □

Has-right-inverse→Has-right-inverseᴱ :
  Has-right-inverse f → Has-right-inverseᴱ f
Has-right-inverse→Has-right-inverseᴱ = Σ-map P.id [_]→

@0 Has-right-inverse≃Has-right-inverseᴱ :
  Has-right-inverse f ≃ Has-right-inverseᴱ f
Has-right-inverse≃Has-right-inverseᴱ {f} =
  (∃ λ f⁻¹ →         f ∘ f⁻¹ ≡ id )  ↔⟨ (∃-cong λ _ → inverse $ erased Erased↔) ⟩□
  (∃ λ f⁻¹ → Erased (f ∘ f⁻¹ ≡ id))  □

Is-bi-invertible→Is-bi-invertibleᴱ :
  Is-bi-invertible f → Is-bi-invertibleᴱ f
Is-bi-invertible→Is-bi-invertibleᴱ =
  Σ-map Has-left-inverse→Has-left-inverseᴱ
        Has-right-inverse→Has-right-inverseᴱ

@0 Is-bi-invertible≃Is-bi-invertibleᴱ :
  Is-bi-invertible f ≃ Is-bi-invertibleᴱ f
Is-bi-invertible≃Is-bi-invertibleᴱ {f} =
  Has-left-inverse  f × Has-right-inverse  f  ↝⟨ Has-left-inverse≃Has-left-inverseᴱ ×-cong
                                                 Has-right-inverse≃Has-right-inverseᴱ ⟩□
  Has-left-inverseᴱ f × Has-right-inverseᴱ f  □

Has-quasi-inverse→Has-quasi-inverseᴱ :
  Has-quasi-inverse f → Has-quasi-inverseᴱ f
Has-quasi-inverse→Has-quasi-inverseᴱ = Σ-map P.id [_]→

@0 Has-quasi-inverse≃Has-quasi-inverseᴱ :
  Has-quasi-inverse f ≃ Has-quasi-inverseᴱ f
Has-quasi-inverse≃Has-quasi-inverseᴱ {f} =
  (∃ λ f⁻¹ →         f ∘ f⁻¹ ≡ id × f⁻¹ ∘ f ≡ id )  ↔⟨ (∃-cong λ _ → inverse $ erased Erased↔) ⟩□
  (∃ λ f⁻¹ → Erased (f ∘ f⁻¹ ≡ id × f⁻¹ ∘ f ≡ id))  □

≊→≊ᴱ : A ≊ B → A ≊ᴱ B
≊→≊ᴱ = Σ-map P.id Is-bi-invertible→Is-bi-invertibleᴱ

@0 ≊≃≊ᴱ : (A ≊ B) ≃ (A ≊ᴱ B)
≊≃≊ᴱ {A} {B} =
  (∃ λ (f : Hom A B) → Is-bi-invertible  f)  ↝⟨ (∃-cong λ _ → Is-bi-invertible≃Is-bi-invertibleᴱ) ⟩□
  (∃ λ (f : Hom A B) → Is-bi-invertibleᴱ f)  □

≅→≅ᴱ : A ≅ B → A ≅ᴱ B
≅→≅ᴱ = Σ-map P.id Has-quasi-inverse→Has-quasi-inverseᴱ

@0 ≅≃≅ᴱ : (A ≅ B) ≃ (A ≅ᴱ B)
≅≃≅ᴱ {A} {B} =
  (∃ λ (f : Hom A B) → Has-quasi-inverse  f)  ↝⟨ (∃-cong λ _ → Has-quasi-inverse≃Has-quasi-inverseᴱ) ⟩□
  (∃ λ (f : Hom A B) → Has-quasi-inverseᴱ f)  □

-- The remaining code relies on some further assumptions, similar to
-- those of a precategory. However, note that Hom A B is not required
-- to be a set (some properties require Hom A A to be a set for some
-- A).

module More
  (@0 left-identity  : {A B : Obj} (f : Hom A B) → id ∘ f ≡ f)
  (@0 right-identity : {A B : Obj} (f : Hom A B) → f ∘ id ≡ f)
  (@0 associativity  : {A B C D : Obj}
                       (f : Hom C D) (g : Hom B C) (h : Hom A B) →
                       f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h)
  where

  private
    module @0 BiM =
      Bi.More left-identity right-identity associativity

  -- Bi-invertible morphisms have quasi-inverses.

  Is-bi-invertibleᴱ→Has-quasi-inverseᴱ :
    Is-bi-invertibleᴱ f → Has-quasi-inverseᴱ f
  Is-bi-invertibleᴱ→Has-quasi-inverseᴱ
    {f} ((f⁻¹₁ , [ f⁻¹₁∘f≡id ]) , (f⁻¹₂ , [ f∘f⁻¹₂≡id ])) =
      (f⁻¹₁ ∘ f ∘ f⁻¹₂)
    , [ (f ∘ f⁻¹₁ ∘ f ∘ f⁻¹₂    ≡⟨ cong (f ∘_) $ associativity _ _ _ ⟩
         f ∘ (f⁻¹₁ ∘ f) ∘ f⁻¹₂  ≡⟨ cong (λ f′ → f ∘ f′ ∘ f⁻¹₂) f⁻¹₁∘f≡id ⟩
         f ∘ id ∘ f⁻¹₂          ≡⟨ cong (f ∘_) $ left-identity _ ⟩
         f ∘ f⁻¹₂               ≡⟨ f∘f⁻¹₂≡id ⟩∎
         id                     ∎)
      , ((f⁻¹₁ ∘ f ∘ f⁻¹₂) ∘ f  ≡⟨ cong (λ f′ → (f⁻¹₁ ∘ f′) ∘ f) f∘f⁻¹₂≡id ⟩
         (f⁻¹₁ ∘ id) ∘ f        ≡⟨ cong (_∘ f) $ right-identity _ ⟩
         f⁻¹₁ ∘ f               ≡⟨ f⁻¹₁∘f≡id ⟩∎
         id                     ∎)
      ]

  -- Has-left-inverseᴱ f is contractible (with an erased proof) if f
  -- has a quasi-inverse (with erased proofs).

  Contractibleᴱ-Has-left-inverseᴱ :
    {@0 f : Hom A B} →
    Has-quasi-inverseᴱ f → Contractibleᴱ (Has-left-inverseᴱ f)
  Contractibleᴱ-Has-left-inverseᴱ {f} (f⁻¹ , [ f∘f⁻¹≡id , f⁻¹∘f≡id ]) =
    ECP.Contractibleᴱ-⁻¹ᴱ
      (_∘ f)
      (_∘ f⁻¹)
      (λ g →
         (g ∘ f⁻¹) ∘ f  ≡⟨ sym $ associativity _ _ _ ⟩
         g ∘ f⁻¹ ∘ f    ≡⟨ cong (g ∘_) f⁻¹∘f≡id ⟩
         g ∘ id         ≡⟨ right-identity _ ⟩∎
         g              ∎)
      (λ g →
         (g ∘ f) ∘ f⁻¹  ≡⟨ sym $ associativity _ _ _ ⟩
         g ∘ f ∘ f⁻¹    ≡⟨ cong (g ∘_) f∘f⁻¹≡id ⟩
         g ∘ id         ≡⟨ right-identity _ ⟩∎
         g              ∎)
      id

  -- Has-right-inverseᴱ f is contractible (with an erased proof) if f
  -- has a quasi-inverse (with erased proofs).

  Contractibleᴱ-Has-right-inverseᴱ :
    {@0 f : Hom A B} →
    Has-quasi-inverseᴱ f → Contractibleᴱ (Has-right-inverseᴱ f)
  Contractibleᴱ-Has-right-inverseᴱ {f} (f⁻¹ , [ f∘f⁻¹≡id , f⁻¹∘f≡id ]) =
    ECP.Contractibleᴱ-⁻¹ᴱ
      (f ∘_)
      (f⁻¹ ∘_)
      (λ g →
         f ∘ f⁻¹ ∘ g    ≡⟨ associativity _ _ _ ⟩
         (f ∘ f⁻¹) ∘ g  ≡⟨ cong (_∘ g) f∘f⁻¹≡id ⟩
         id ∘ g         ≡⟨ left-identity _ ⟩∎
         g              ∎)
      (λ g →
         f⁻¹ ∘ f ∘ g    ≡⟨ associativity _ _ _ ⟩
         (f⁻¹ ∘ f) ∘ g  ≡⟨ cong (_∘ g) f⁻¹∘f≡id ⟩
         id ∘ g         ≡⟨ left-identity _ ⟩∎
         g              ∎)
      id

  -- Is-bi-invertibleᴱ f is a proposition (in erased contexts).

  @0 Is-bi-invertibleᴱ-propositional :
    (f : Hom A B) → Is-proposition (Is-bi-invertibleᴱ f)
  Is-bi-invertibleᴱ-propositional f =     $⟨ BiM.Is-bi-invertible-propositional f ⟩
    Is-proposition (Is-bi-invertible  f)  ↝⟨ H-level-cong _ 1 Is-bi-invertible≃Is-bi-invertibleᴱ ⦂ (_ → _) ⟩
    Is-proposition (Is-bi-invertibleᴱ f)  □

  -- If Hom A A is a set, where A is the domain of f, then
  -- Has-quasi-inverseᴱ f is a proposition (in erased contexts).

  @0 Has-quasi-inverseᴱ-propositional-domain :
    {f : Hom A B} →
    Is-set (Hom A A) →
    Is-proposition (Has-quasi-inverseᴱ f)
  Has-quasi-inverseᴱ-propositional-domain {f} s =
                                           $⟨ BiM.Has-quasi-inverse-propositional-domain s ⟩
    Is-proposition (Has-quasi-inverse  f)  ↝⟨ H-level-cong _ 1 Has-quasi-inverse≃Has-quasi-inverseᴱ ⦂ (_ → _) ⟩□
    Is-proposition (Has-quasi-inverseᴱ f)  □

  -- If Hom B B is a set, where B is the codomain of f, then
  -- Has-quasi-inverseᴱ f is a proposition (in erased contexts).

  @0 Has-quasi-inverseᴱ-propositional-codomain :
    {f : Hom A B} →
    Is-set (Hom B B) →
    Is-proposition (Has-quasi-inverseᴱ f)
  Has-quasi-inverseᴱ-propositional-codomain {f} s =
                                           $⟨ BiM.Has-quasi-inverse-propositional-codomain s ⟩
    Is-proposition (Has-quasi-inverse  f)  ↝⟨ H-level-cong _ 1 Has-quasi-inverse≃Has-quasi-inverseᴱ ⦂ (_ → _) ⟩□
    Is-proposition (Has-quasi-inverseᴱ f)  □

  -- There is a logical equivalence between Has-quasi-inverseᴱ f and
  -- Is-bi-invertibleᴱ f.

  Has-quasi-inverseᴱ⇔Is-bi-invertibleᴱ :
    Has-quasi-inverseᴱ f ⇔ Is-bi-invertibleᴱ f
  Has-quasi-inverseᴱ⇔Is-bi-invertibleᴱ = record
    { to   = Has-quasi-inverseᴱ→Is-bi-invertibleᴱ _
    ; from = Is-bi-invertibleᴱ→Has-quasi-inverseᴱ
    }

  -- There is a logical equivalence between A ≅ᴱ B and A ≊ᴱ B.

  ≅ᴱ⇔≊ᴱ : (A ≅ᴱ B) ⇔ (A ≊ᴱ B)
  ≅ᴱ⇔≊ᴱ = ∃-cong λ _ → Has-quasi-inverseᴱ⇔Is-bi-invertibleᴱ

  -- Is-bi-invertibleᴱ and Has-quasi-inverseᴱ are equivalent (with
  -- erased proofs) for morphisms with domain A for which Hom A A is a
  -- set.

  Is-bi-invertibleᴱ≃ᴱHas-quasi-inverseᴱ-domain :
    {f : Hom A B} →
    @0 Is-set (Hom A A) →
    Is-bi-invertibleᴱ f ≃ᴱ Has-quasi-inverseᴱ f
  Is-bi-invertibleᴱ≃ᴱHas-quasi-inverseᴱ-domain s = EEq.⇔→≃ᴱ
    (Is-bi-invertibleᴱ-propositional _)
    (Has-quasi-inverseᴱ-propositional-domain s)
    (_⇔_.from Has-quasi-inverseᴱ⇔Is-bi-invertibleᴱ)
    (_⇔_.to   Has-quasi-inverseᴱ⇔Is-bi-invertibleᴱ)

  -- Is-bi-invertibleᴱ and Has-quasi-inverseᴱ are equivalent (with
  -- erased proofs) for morphisms with codomain B for which Hom B B is
  -- a set.

  Is-bi-invertibleᴱ≃ᴱHas-quasi-inverseᴱ-codomain :
    {f : Hom A B} →
    @0 Is-set (Hom B B) →
    Is-bi-invertibleᴱ f ≃ᴱ Has-quasi-inverseᴱ f
  Is-bi-invertibleᴱ≃ᴱHas-quasi-inverseᴱ-codomain s = EEq.⇔→≃ᴱ
    (Is-bi-invertibleᴱ-propositional _)
    (Has-quasi-inverseᴱ-propositional-codomain s)
    (_⇔_.from Has-quasi-inverseᴱ⇔Is-bi-invertibleᴱ)
    (_⇔_.to   Has-quasi-inverseᴱ⇔Is-bi-invertibleᴱ)

  -- A ≊ᴱ B and A ≅ᴱ B are equivalent (with erased proofs) if Hom A A
  -- is a set.

  ≊ᴱ≃ᴱ≅ᴱ-domain :
    @0 Is-set (Hom A A) →
    (A ≊ᴱ B) ≃ᴱ (A ≅ᴱ B)
  ≊ᴱ≃ᴱ≅ᴱ-domain s =
    ∃-cong λ _ → Is-bi-invertibleᴱ≃ᴱHas-quasi-inverseᴱ-domain s

  -- A ≊ᴱ B and A ≅ᴱ B are equivalent (with erased proofs) if Hom B B
  -- is a set.

  ≊ᴱ≃ᴱ≅ᴱ-codomain :
    @0 Is-set (Hom B B) →
    (A ≊ᴱ B) ≃ᴱ (A ≅ᴱ B)
  ≊ᴱ≃ᴱ≅ᴱ-codomain s =
    ∃-cong λ _ → Is-bi-invertibleᴱ≃ᴱHas-quasi-inverseᴱ-codomain s

  -- An equality characterisation lemma for _≊ᴱ_.

  @0 equality-characterisation-≊ᴱ :
    (f g : A ≊ᴱ B) → (f ≡ g) ≃ (proj₁ f ≡ proj₁ g)
  equality-characterisation-≊ᴱ f g =
    f ≡ g                              ↝⟨ inverse $ Eq.≃-≡ (inverse ≊≃≊ᴱ) ⟩
    _≃_.from ≊≃≊ᴱ f ≡ _≃_.from ≊≃≊ᴱ g  ↝⟨ BiM.equality-characterisation-≊ _ _ ⟩□
    proj₁ f ≡ proj₁ g                  □

  -- Two equality characterisation lemmas for _≅ᴱ_.

  @0 equality-characterisation-≅ᴱ-domain :
    Is-set (Hom A A) →
    (f g : A ≅ᴱ B) → (f ≡ g) ≃ (proj₁ f ≡ proj₁ g)
  equality-characterisation-≅ᴱ-domain s f g =
    f ≡ g                              ↝⟨ inverse $ Eq.≃-≡ (inverse ≅≃≅ᴱ) ⟩
    _≃_.from ≅≃≅ᴱ f ≡ _≃_.from ≅≃≅ᴱ g  ↝⟨ BiM.equality-characterisation-≅-domain s _ _ ⟩□
    proj₁ f ≡ proj₁ g                  □

  @0 equality-characterisation-≅ᴱ-codomain :
    Is-set (Hom B B) →
    (f g : A ≅ᴱ B) → (f ≡ g) ≃ (proj₁ f ≡ proj₁ g)
  equality-characterisation-≅ᴱ-codomain s f g =
    f ≡ g                              ↝⟨ inverse $ Eq.≃-≡ (inverse ≅≃≅ᴱ) ⟩
    _≃_.from ≅≃≅ᴱ f ≡ _≃_.from ≅≃≅ᴱ g  ↝⟨ BiM.equality-characterisation-≅-codomain s _ _ ⟩□
    proj₁ f ≡ proj₁ g                  □

  -- If f : Hom A B has a quasi-inverse, then Has-quasi-inverseᴱ f is
  -- equivalent to id ≡ id (in erased contexts), where id stands for
  -- either the identity at A or at B.

  @0 Has-quasi-inverseᴱ≃id≡id-domain :
    {f : Hom A B} →
    Has-quasi-inverseᴱ f →
    Has-quasi-inverseᴱ f ≃ (id ≡ id {A = A})
  Has-quasi-inverseᴱ≃id≡id-domain {f} q-inv =
    Has-quasi-inverseᴱ f  ↝⟨ inverse Has-quasi-inverse≃Has-quasi-inverseᴱ ⟩
    Has-quasi-inverse f   ↝⟨ BiM.Has-quasi-inverse≃id≡id-domain (_≃_.from Has-quasi-inverse≃Has-quasi-inverseᴱ q-inv) ⟩□
    id ≡ id               □

  @0 Has-quasi-inverseᴱ≃id≡id-codomain :
    {f : Hom A B} →
    Has-quasi-inverseᴱ f →
    Has-quasi-inverseᴱ f ≃ (id ≡ id {A = B})
  Has-quasi-inverseᴱ≃id≡id-codomain {f} q-inv =
    Has-quasi-inverseᴱ f  ↝⟨ inverse Has-quasi-inverse≃Has-quasi-inverseᴱ ⟩
    Has-quasi-inverse f   ↝⟨ BiM.Has-quasi-inverse≃id≡id-codomain (_≃_.from Has-quasi-inverse≃Has-quasi-inverseᴱ q-inv) ⟩□
    id ≡ id               □
