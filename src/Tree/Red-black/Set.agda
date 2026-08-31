------------------------------------------------------------------------
-- Finite sets, implemented using red-black trees
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
import Extensionality
open import Prelude
import Quotient.Erased.Axiomatised
import Total-order.Erased
import Univalence-axiom

module Tree.Red-black.Set
  {e⁺}
  (eq : ∀ {a p} → Equality-with-J a p e⁺)
  (open Extensionality eq)
  (open Quotient.Erased.Axiomatised eq)
  (open Total-order.Erased eq)
  (open Univalence-axiom eq hiding (extensionality))
  -- The code is parametrised by an implementation of quotients.
  (quot : Quotientᴱ)
  {a o}
  -- It is assumed that function and propositional extensionality hold.
  (@0 ext      : Extensionality (lsuc a ⊔ o) (lsuc a ⊔ o))
  (@0 prop-ext : Propositional-extensionality a)
  -- The carrier type.
  {A : Type a}
  -- The carrier type is assumed to be totally ordered.
  (O : Total-order A o)
  where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)

import Bag-equivalence eq as L
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_)
import Equivalence.Erased eq as EEq
open import Erased.Level-1 eq as Erased
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level hiding (Set)
open import H-level.Closure eq
open import H-level.Truncation.Propositional.Erased.Axiomatised eq
open import List eq
open import Maybe eq
open import Monad eq
import Nat eq as N
open import Surjection eq using (_↠_)
import Tree.Red-black eq O as T

private
  module @0 BC {a} =
    Erased.[]-cong₁ (erased-instance-of-[]-cong-axiomatisation {a = a})
  open module Q  = Quotientᴱ quot renaming ([_] to [_]Q)
  open module Tr = Truncationᴱ Q.truncation
  open module O  = Total-order O using (_<_; _≤_)

open Sorted-list O

private variable
  x y : A

------------------------------------------------------------------------
-- Sets

opaque

  -- Finite sets.
  --
  -- The implementation uses red-black trees quotiented by set
  -- equivalence.

  Set : Type (a ⊔ o)
  Set = T.Tree /ᴱ T._≈_

private variable
  xs xs′ xs₁ xs₂ : Set

opaque
  unfolding Set

  -- Set is a set.

  @0 Set-set : Is-set Set
  Set-set = Q./ᴱ-is-set

private opaque
  unfolding Set

  -- The type of ≈≃[]≡[]-type.

  @0 ≈≃[]≡[]-type : Type (a ⊔ o)
  ≈≃[]≡[]-type =
    ∀ {t₁ t₂} →
    (t₁ T.≈ t₂) ≃ (_≡_ {A = Set} [ t₁ ]Q [ t₂ ]Q)

  -- A lemma used below.

  @0 ≈≃[]≡[] : ≈≃[]≡[]-type
  ≈≃[]≡[] =
    ≃[]≡[]
      (effective₀ (lower-extensionality o o ext) prop-ext
         T.≈-equivalence
         (λ _ _ → T.≈-propositional (lower-extensionality _ _ ext)))
      (T.≈-propositional (lower-extensionality _ _ ext))

------------------------------------------------------------------------
-- Set membership

private opaque
  unfolding Set T._≈_

  -- Set membership.

  Membership :
    A → Set → ∃ λ (B : Type a) → Erased (Is-proposition B)
  Membership x = Q.rec λ where
    .is-setʳ →
      Is-set-∃-Erased-Is-proposition (lower-extensionality o o ext)
        prop-ext
    .[]ʳ t →
      (x T.∈ t) , [ T.∈-propositional ]
    .[]-respects-relationʳ {x = xs} {y = ys} →
      (∀ {z} → z T.∈ xs ⇔ z T.∈ ys)           →⟨ (λ xs≈ys → xs≈ys) ⟩

      x T.∈ xs ⇔ x T.∈ ys                     →⟨ prop-ext T.∈-propositional T.∈-propositional ⟩

      (x T.∈ xs) ≡ (x T.∈ ys)                 ↔⟨ ignore-propositional-component
                                                   (BC.H-level-Erased 1
                                                      (H-level-propositional
                                                         (lower-extensionality _ _ ext) 1)) ⟩□
      ((x T.∈ xs) , [ T.∈-propositional ]) ≡
      ((x T.∈ ys) , [ T.∈-propositional ])    □

opaque
  unfolding Membership

  infix 4 _∈_

  -- Set membership.

  _∈_ : A → Set → Type a
  x ∈ xs = Membership x xs .proj₁

opaque
  unfolding _∈_

  -- Set membership is propositional.

  @0 ∈-propositional : Is-proposition (x ∈ xs)
  ∈-propositional = Membership _ _ .proj₂ .erased

private opaque
  unfolding _∈_

  -- The type of ∈[].

  ∈[]-type : Type (lsuc a ⊔ o)
  ∈[]-type = ∀ {x t} → (x ∈ [ t ]Q) ≡ (x T.∈ t)

  -- A computation rule for _∈_.

  ∈[] : ∈[]-type
  ∈[] = cong proj₁ Q.rec-[]

opaque
  unfolding Set ∈[]

  -- Extensionality for sets.

  @0 extensionality : (∀ {x} → x ∈ xs₁ ⇔ x ∈ xs₂) → xs₁ ≡ xs₂
  extensionality =
    Q.elim-prop₂ (λ xs₁ xs₂ → (∀ {x} → x ∈ xs₁ ⇔ x ∈ xs₂) → xs₁ ≡ xs₂)
      (λ _ _ →
         Π-closure (lower-extensionality _ (lsuc a) ext) 1 λ _ →
         Set-set)
      (λ t₁ t₂ t₁≈t₂ →
         Q.[]-respects-relation λ {x} →
           x T.∈ t₁     ↝⟨ ≡⇒↝ _ (sym ∈[]) ⟩
           x ∈ [ t₁ ]Q  ↝⟨ t₁≈t₂ ⟩
           x ∈ [ t₂ ]Q  ↝⟨ ≡⇒↝ _ ∈[] ⟩□
           x T.∈ t₂     □)
      _ _

------------------------------------------------------------------------
-- Non-empty

opaque

  -- The property of being non-empty.

  Non-empty : Set → Type a
  Non-empty xs = ∥ (∃ λ x → x ∈ xs) ∥ᴱ

opaque
  unfolding Non-empty

  -- Non-empty is propositional.

  @0 Non-empty-propositional : Is-proposition (Non-empty xs)
  Non-empty-propositional = truncation-is-proposition

private opaque
  unfolding Non-empty ∈[]

  -- The type of non-empty-lemma.

  @0 Non-empty-lemma : Type (a ⊔ o)
  Non-empty-lemma = ∀ {t} → Non-empty [ t ]Q → t ≢ T.empty

  -- A lemma used below.

  @0 non-empty-lemma : Non-empty-lemma
  non-empty-lemma {t} = Tr.rec λ @0 where
    .truncation-is-propositionʳ →
      ¬-propositional (lower-extensionality (lsuc a) _ ext)
    .∣∣ʳ (x , x∈t) →
      t ≡ T.empty       →⟨ flip (subst ((x ∈_) ∘ [_]Q)) x∈t ⟩
      x ∈ [ T.empty ]Q  →⟨ ≡⇒↝ _ ∈[] ⟩
      x T.∈ T.empty     →⟨ T.∉empty ⟩□
      ⊥                 □

opaque
  unfolding Non-empty

  -- There is an equivalence between "the set is not non-empty" and
  -- "every value is not in the set".

  @0 ¬-Non-empty-≃-∉ : (¬ Non-empty xs) ≃ (∀ {x} → ¬ x ∈ xs)
  ¬-Non-empty-≃-∉ =
    _↠_.from
      (Eq.≃↠⇔
         (¬-propositional (lower-extensionality _ _ ext))
         (implicit-Π-closure (lower-extensionality _ _ ext) 1 λ _ →
          ¬-propositional (lower-extensionality _ _ ext)))
      (record
         { to   = λ hyp ∈xs → hyp ∣ _ , ∈xs ∣
         ; from = λ hyp →
             Tr.rec λ where
               .truncation-is-propositionʳ → ⊥-propositional
               .∣∣ʳ (_ , ∈xs)              → hyp ∈xs
         })

------------------------------------------------------------------------
-- A membership test

opaque
  unfolding ∈[]

  -- Does the element exist in the set?

  member? : (x : A) (xs : Set) → Dec-Erased (x ∈ xs)
  member? x = Q.elim-prop λ where
    .is-propositionʳ _ →
      BC.Is-proposition-Dec-Erased (lower-extensionality _ _ ext)
        ∈-propositional
    .[]ʳ t →
      Dec-Erased-map
        (x T.∈ t     ↝⟨ ≡⇒↝ _ (sym ∈[]) ⟩
         x ∈ [ t ]Q  □)
        (T.member? x t)

------------------------------------------------------------------------
-- The empty set

opaque
  unfolding Set

  -- The empty set.

  ∅ : Set
  ∅ = [ T.empty ]Q

opaque
  unfolding ∅ ∈[]

  -- The empty set is empty.

  @0 ∉∅ : ¬ x ∈ ∅
  ∉∅ {x} =
    x ∈ [ T.empty ]Q  →⟨ ≡⇒↝ _ ∈[] ⟩
    x T.∈ T.empty     →⟨ T.∉empty ⟩□
    ⊥                 □

------------------------------------------------------------------------
-- Insertion

opaque
  unfolding Set

  -- Inserts an element into the set.

  insert : A → Set → Set
  insert x =
    T.insert x Q./ᴱ-map λ _ _ → T.insert-respects-set-equivalence

opaque
  unfolding _/ᴱ-map_ insert ∈[]

  -- There is an equivalence between "y is in insert x xs" and "merely
  -- y is x or in xs".

  @0 ∈insert≃ : (y ∈ insert x xs) ≃ (y ≡ x ∥⊎∥ᴱ y ∈ xs)
  ∈insert≃ {y} {x} {xs} =
    Q.elim-prop {P = λ xs → (y ∈ insert x xs) ≃ (y ≡ x ∥⊎∥ᴱ y ∈ xs)}
      (λ where
         .is-propositionʳ _ →
           Eq.left-closure (lower-extensionality _ _ ext) 0
             ∈-propositional
         .[]ʳ t →
           y ∈ insert x [ t ]Q      ↝⟨ ≡⇒↝ _ (cong (_∈_ _) Q.rec-[]) ⟩
           y ∈ [ T.insert x t ]Q    ↝⟨ ≡⇒↝ _ ∈[] ⟩
           y T.∈ T.insert x t       ↝⟨ inverse (∥∥ᴱ≃ T.∈-propositional) ⟩
           ∥ y T.∈ T.insert x t ∥ᴱ  ↝⟨ EEq.≃ᴱ→≃ (∥∥ᴱ-cong-⇔ T.∈-insert) ⟩
           y ≡ x ∥⊎∥ᴱ y T.∈ t       ↝⟨ ≡⇒↝ _ (cong (∥_∥ᴱ ∘ _⊎_ _) (sym ∈[])) ⟩□
           y ≡ x ∥⊎∥ᴱ y ∈ [ t ]Q    □)
      xs

------------------------------------------------------------------------
-- Deletion

opaque
  unfolding Set

  -- Removes the given element, if it exists in the set.

  delete : A → Set → Set
  delete x =
    T.delete x Q./ᴱ-map λ _ _ → T.delete-respects-set-equivalence

opaque
  unfolding _/ᴱ-map_ delete ∈[]

  -- There is an equivalence between "y is in delete x xs" and "y is
  -- distinct from x and in xs".

  @0 ∈delete≃ : (y ∈ delete x xs) ≃ (y ≢ x × y ∈ xs)
  ∈delete≃ {y} {x} {xs} =
    Q.elim-prop {P = λ xs → (y ∈ delete x xs) ≃ (y ≢ x × y ∈ xs)}
      (λ where
         .is-propositionʳ _ →
           Eq.left-closure (lower-extensionality _ _ ext) 0
             ∈-propositional
         .[]ʳ t →
           y ∈ delete x [ t ]Q    ↝⟨ ≡⇒↝ _ (cong (_∈_ _) Q.rec-[]) ⟩
           y ∈ [ T.delete x t ]Q  ↝⟨ ≡⇒↝ _ ∈[] ⟩
           y T.∈ T.delete x t     ↝⟨ _↠_.from
                                       (Eq.≃↠⇔ T.∈-propositional
                                          (×-closure 1
                                             (¬-propositional (lower-extensionality _ _ ext))
                                             T.∈-propositional))
                                       T.∈-delete ⟩
           y ≢ x × y T.∈ t        ↝⟨ ≡⇒↝ _ (cong (_×_ _) (sym ∈[])) ⟩□
           y ≢ x × y ∈ [ t ]Q     □)
      xs

opaque

  -- If x is not in xs, then delete x xs is equal to xs.

  @0 ∉→delete≡ : ¬ x ∈ xs → delete x xs ≡ xs
  ∉→delete≡ {x} {xs} x∉xs =
    extensionality λ {y} →
      y ∈ delete x xs  ↔⟨ ∈delete≃ ⟩
      y ≢ x × y ∈ xs   ↝⟨ record
                            { to   = proj₂
                            ; from = λ y∈xs → x∉xs ∘ flip (subst (_∈ _)) y∈xs , y∈xs
                            } ⟩□
      y ∈ xs           □

------------------------------------------------------------------------
-- Deleting the minimum element

opaque
  unfolding T.Delete-min-≈ Non-empty-lemma

  -- Returns and removes the minimum element. The set must be non-empty.

  delete-min : (xs : Set) → @0 Non-empty xs → A × Set
  delete-min = Q.elim λ where
    .is-setʳ _ →
      Πᴱ-closure (lower-extensionality _ (lsuc a) ext) 2 λ _ →
      ×-closure 2 O.is-set Set-set
    .[]ʳ t ∈t →
      Σ-map id [_]Q (T.delete-min t (non-empty-lemma ∈t))
    .[]-respects-relationʳ {x = t₁} {y = t₂} t₁≈t₂ →
      apply-extᴱ (lower-extensionality _ (lsuc a) ext) λ _ →
      let x₁≡x₂ , t₁′≈t₂′ =
            T.delete-min-respects-set-equivalence t₁≈t₂
      in
      subst (λ xs → @0 Non-empty xs → A × Set)
        ([]-respects-relation (λ {_} → t₁≈t₂))
        (λ _ → Σ-map id [_]Q (T.delete-min t₁ _))
        _                                                           ≡⟨ BC.subst-0→ ⟩

      subst (λ _ → A × Set) ([]-respects-relation (λ {_} → t₁≈t₂))
        (Σ-map id [_]Q (T.delete-min t₁ _))                         ≡⟨ subst-const _ ⟩

      Σ-map id [_]Q (T.delete-min t₁ _)                             ≡⟨ cong₂ _,_ x₁≡x₂ ([]-respects-relation (λ {_} → t₁′≈t₂′)) ⟩∎

      Σ-map id [_]Q (T.delete-min t₂ _)                             ∎

private opaque

  -- If x is strictly below all elements in xs, then y ≡ x ⊎ y ∈ xs is
  -- a proposition.

  @0 ≡⊎∈-propositional :
    (∀ {y} → y ∈ xs → x < y) →
    Is-proposition (y ≡ x ⊎ y ∈ xs)
  ≡⊎∈-propositional ∈→< =
    ⊎-closure-propositional (λ ≡x ∈xs′ → O.<→≢ (∈→< ∈xs′) (sym ≡x))
      O.is-set ∈-propositional

  -- Certain types are propositions.

  @0 ∈→<×∈⇔≡⊎∈-propositional :
    Is-proposition
      ((∀ {y} → y ∈ xs′ → x < y) ×
       (∀ {y} → y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′))
  ∈→<×∈⇔≡⊎∈-propositional =
    Σ-closure 1
      (implicit-Π-closure (lower-extensionality _ (lsuc a) ext)
         1 λ _ →
       Π-closure (lower-extensionality _ (lsuc a) ext) 1 λ _ →
       O.<-propositional) λ ∈→< →
      (implicit-Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       ⇔-closure (lower-extensionality _ _ ext) 1
         ∈-propositional (≡⊎∈-propositional ∈→<))

opaque
  unfolding T.Delete-min-≈ delete-min ∈[] ≈≃[]≡[]

  -- A uniqueness lemma for delete-min.

  @0 delete-min-unique :
    {∈xs : Non-empty xs} →
    (delete-min xs ∈xs ≡ (x , xs′)) ≃
    ((∀ {y} → y ∈ xs′ → x < y) × (∀ {y} → y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′))
  delete-min-unique {x} =
    let set : Is-set (A × Set)
        set = ×-closure 2 O.is-set Set-set
    in
    _↠_.from (Eq.≃↠⇔ set ∈→<×∈⇔≡⊎∈-propositional) $
    Q.elim-prop₂
      (λ xs xs′ →
         (∈xs : Non-empty xs) →
         delete-min xs ∈xs ≡ (x , xs′) ⇔
         (∀ {y} → y ∈ xs′ → x < y) ×
         (∀ {y} → y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′))
      (λ xs₁ xs₂ →
         Π-closure (lower-extensionality _ (lsuc a) ext) 1 λ _ →
         ⇔-closure (lower-extensionality (lsuc a) (lsuc a) ext) 1 set
           ∈→<×∈⇔≡⊎∈-propositional)
      (λ t₁ t₂ ∈t₁ →
         delete-min [ t₁ ]Q ∈t₁ ≡ (x , [ t₂ ]Q)             ↝⟨ ≡⇒↝ _ (cong (_≡ _) (cong {x = delete-min _} (λ f → f _) Q.elim-[])) ⟩

         Σ-map id [_]Q (T.delete-min t₁ _) ≡ (x , [ t₂ ]Q)  ↔⟨ inverse ≡×≡↔≡ ⟩

         (let x′ , t₁′ = T.delete-min t₁ _ in
          x′ ≡ x × [ t₁′ ]Q ≡ [ t₂ ]Q)                      ↔⟨ (inverse $ ∃-cong λ _ → ≈≃[]≡[]) ⟩

         T.Delete-min-≈ (T.delete-min t₁ _) (x , t₂)        ↝⟨ T.delete-min-unique ⟩

         (∀ {y} → y T.∈ t₂ → x < y) ×
         (∀ {y} → y T.∈ t₁ ⇔ y ≡ x ⊎ y T.∈ t₂)              ↝⟨ implicit-∀-cong _ (→-cong₁ _ (≡⇒↝ equivalence (sym ∈[])))
                                                                 ×-cong
                                                               implicit-∀-cong _
                                                                 (⇔-cong _ (≡⇒↝ _ (sym ∈[])) (F.id ⊎-cong ≡⇒↝ _ (sym ∈[]))) ⟩□
         (∀ {y} → y ∈ [ t₂ ]Q → x < y) ×
         (∀ {y} → y ∈ [ t₁ ]Q ⇔ y ≡ x ⊎ y ∈ [ t₂ ]Q)        □)
      _ _ _

opaque

  -- An ordering lemma for delete-min.

  @0 <-delete-min :
    {∈xs : Non-empty xs} →
    let x , xs′ = delete-min xs ∈xs in
    y ∈ xs′ → x < y
  <-delete-min =
    _≃_.to delete-min-unique (refl _) .proj₁

opaque

  -- A membership lemma for delete-min.

  @0 ∈-delete-min :
    {∈xs : Non-empty xs} →
    let x , xs′ = delete-min xs ∈xs in
    (y ∈ xs) ≃ (y ≡ x ⊎ y ∈ xs′)
  ∈-delete-min =
    _↠_.from (Eq.≃↠⇔ ∈-propositional (≡⊎∈-propositional <-delete-min))
      (_≃_.to delete-min-unique (refl _) .proj₂)

------------------------------------------------------------------------
-- A variant of delete-min for possibly non-empty sets

opaque
  unfolding Set T.Delete-min₀-≈

  -- Returns and removes the minimum element, if any. If the set is
  -- empty, then nothing is returned.

  delete-min₀ : Set → Maybe (A × Set)
  delete-min₀ = Q.rec λ where
      .is-setʳ →
        ⊎-closure 0 (H-level.mono (N.zero≤ 2) ⊤-contractible) $
        ×-closure 2 O.is-set Set-set
      .[]ʳ t →
        Σ-map id [_]Q ⟨$⟩ T.delete-min₀ t
      .[]-respects-relationʳ {x = t₁} {y = t₂} →
        t₁ T.≈ t₂                                              →⟨ T.delete-min₀-respects-set-equivalence ⟩

        T.Delete-min₀-≈ (T.delete-min₀ t₁) (T.delete-min₀ t₂)  →⟨ lemma (T.delete-min₀ _) _ ⟩□

        Σ-map id [_]Q ⟨$⟩ T.delete-min₀ t₁ ≡
        Σ-map id [_]Q ⟨$⟩ T.delete-min₀ t₂                     □
    where
    @0 lemma :
      (r₁ r₂ : Maybe (A × T.Tree)) →
      T.Delete-min₀-≈ r₁ r₂ →
      _≡_ {A = Maybe (A × Set)}
        (Σ-map id [_]Q ⟨$⟩ r₁) (Σ-map id [_]Q ⟨$⟩ r₂)
    lemma nothing  nothing  _               = refl _
    lemma (just _) (just _) (x₁≡x₂ , t₁≈t₂) =
      cong just $ cong₂ _,_ x₁≡x₂ (Q.[]-respects-relation t₁≈t₂)

opaque
  unfolding T._≈_ delete-min₀ ∈[] ≈≃[]≡[]

  -- There is an equivalence between "delete-min₀ xs is
  -- just (x , xs′)" and the conjunction of
  --
  -- * x is strictly smaller than all elements in xs′ and
  --
  -- * every value is in xs if and only it is either equal to x or in
  --   xs′.

  @0 delete-min₀-just-≃ :
    (delete-min₀ xs ≡ just (x , xs′)) ≃
    ((∀ {y} → y ∈ xs′ → x < y) × (∀ {y} → y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′))
  delete-min₀-just-≃ {x} =
    let set : Is-set (Maybe (A × Set))
        set =
          ⊎-closure 0 (H-level.mono (N.zero≤ 2) ⊤-contractible)
            (×-closure 2 O.is-set Set-set)

        prop :
          Is-proposition
            ((∀ {y} → y ∈ xs′ → x < y) ×
             (∀ {y} → y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′))
        prop =
          Σ-closure 1
            (implicit-Π-closure (lower-extensionality _ (lsuc a) ext)
               1 λ _ →
             Π-closure (lower-extensionality _ (lsuc a) ext) 1 λ _ →
             O.<-propositional) λ ∈→< →
            (implicit-Π-closure (lower-extensionality _ _ ext) 1 λ _ →
             ⇔-closure (lower-extensionality _ _ ext) 1
               ∈-propositional (≡⊎∈-propositional ∈→<))
    in
    _↠_.from (Eq.≃↠⇔ set prop) $
    Q.elim-prop₂
      (λ xs xs′ →
         delete-min₀ xs ≡ just (x , xs′) ⇔
         (∀ {y} → y ∈ xs′ → x < y) ×
         (∀ {y} → y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′))
      (λ xs₁ xs₂ →
         ⇔-closure (lower-extensionality (lsuc a) (lsuc a) ext) 1 set
           prop)
      (λ t₁ t₂ →
         delete-min₀ [ t₁ ]Q ≡ just (x , [ t₂ ]Q)                    ↝⟨ ≡⇒↝ _ (cong (_≡ _) Q.rec-[]) ⟩

         Σ-map id [_]Q ⟨$⟩ T.delete-min₀ t₁ ≡ just (x , [ t₂ ]Q)     ↝⟨ record { to   = lemma _
                                                                               ; from = λ (t₂′ , eq , t₂≈t₂′) →
           Σ-map id [_]Q ⟨$⟩ T.delete-min₀ t₁                                      ≡⟨ cong (_ ⟨$⟩_) eq ⟩
           just (x , [ t₂′ ]Q)                                                     ≡⟨ cong (just ∘ (x ,_))
                                                                                        (sym (Q.[]-respects-relation (λ {_} → t₂≈t₂′))) ⟩∎
           just (x , [ t₂ ]Q)                                                      ∎
                                                                               } ⟩

         (∃ λ t₂′ → T.delete-min₀ t₁ ≡ just (x , t₂′) × t₂ T.≈ t₂′)  ↝⟨ T.delete-min₀-just-⇔ ⟩

         (∀ {y} → y T.∈ t₂ → x < y) ×
         (∀ {y} → y T.∈ t₁ ⇔ y ≡ x ⊎ y T.∈ t₂)                       ↝⟨ implicit-∀-cong _ (→-cong₁ _ (≡⇒↝ equivalence (sym ∈[])))
                                                                          ×-cong
                                                                        implicit-∀-cong _
                                                                          (⇔-cong _ (≡⇒↝ _ (sym ∈[])) (F.id ⊎-cong ≡⇒↝ _ (sym ∈[]))) ⟩□
         (∀ {y} → y ∈ [ t₂ ]Q → x < y) ×
         (∀ {y} → y ∈ [ t₁ ]Q ⇔ y ≡ x ⊎ y ∈ [ t₂ ]Q)                 □)
      _ _
    where
    lemma :
      ∀ {t} (r : Maybe (A × T.Tree)) →
      _≡_ {A = Maybe (A × Set)}
        (Σ-map id [_]Q ⟨$⟩ r) (just (x , [ t ]Q)) →
      ∃ λ t′ → r ≡ just (x , t′) × t T.≈ t′
    lemma nothing =
      ⊥-elim ∘ ⊎.inj₁≢inj₂
    lemma {t} (just (x′ , t′)) =
      just (x′ , [ t′ ]Q) ≡ just (x , [ t ]Q)               →⟨ ⊎.cancel-inj₂ ⟩
      (x′ , [ t′ ]Q) ≡ (x , [ t ]Q)                         ↔⟨ inverse ≡×≡↔≡ ⟩
      x′ ≡ x × [ t′ ]Q ≡ [ t ]Q                             →⟨ Σ-map id (_≃_.from ≈≃[]≡[]) ⟩
      x′ ≡ x × t′ T.≈ t                                     →⟨ (λ (x′≡x , t′≈t) → _ , cong (just ∘ (_, t′)) x′≡x , F.inverse t′≈t) ⟩
      (∃ λ t″ → just (x′ , t′) ≡ just (x , t″) × t T.≈ t″)  □

opaque

  -- If every element in xs is either equal to x or in xs′, and x is
  -- strictly smaller than all elements in xs′, then delete-min₀ xs is
  -- equal to just (x , xs′).

  @0 delete-min₀-just :
    (∀ {y} → y ∈ xs′ → x < y) →
    (∀ {y} → y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′) →
    delete-min₀ xs ≡ just (x , xs′)
  delete-min₀-just = curry (_≃_.from delete-min₀-just-≃)

opaque

  -- An ordering lemma for delete-min₀.

  @0 <-delete-min₀ :
    delete-min₀ xs ≡ just (x , xs′) →
    y ∈ xs′ → x < y
  <-delete-min₀ eq = _≃_.to delete-min₀-just-≃ eq .proj₁

opaque

  -- A membership lemma for delete-min₀.

  @0 ∈-delete-min₀ :
    delete-min₀ xs ≡ just (x , xs′) →
    (y ∈ xs) ≃ (y ≡ x ⊎ y ∈ xs′)
  ∈-delete-min₀ eq =
    _↠_.from
      (Eq.≃↠⇔ ∈-propositional (≡⊎∈-propositional (<-delete-min₀ eq))) $
    _≃_.to delete-min₀-just-≃ eq .proj₂

opaque

  -- A variant of ∈-delete-min₀.

  @0 ∈-delete-min₀-≢ :
    delete-min₀ xs ≡ just (x , xs′) →
    (y ∈ xs′) ≃ (y ≢ x × y ∈ xs)
  ∈-delete-min₀-≢ {xs} {x} {xs′} {y} eq =
    y ∈ xs′         ↝⟨ inverse $
                       ≃⊎→×¬≃ (from-equivalence (∈-delete-min₀ eq))
                         (flip ((_∘ sym) ∘ O.<→≢ ∘ <-delete-min₀ eq))
                         (lower-extensionality _ _ ext) ⟩
    y ∈ xs × y ≢ x  ↔⟨ ×-comm ⟩□
    y ≢ x × y ∈ xs  □

opaque
  unfolding Non-empty delete-min₀ ∈[]

  -- There is an equivalence between "delete-min₀ xs is
  -- just something" and Non-empty xs.

  @0 Is-just-delete-min₀ : Is-just (delete-min₀ xs) ≃ Non-empty xs
  Is-just-delete-min₀ =
    Q.elim-prop
      {P = λ xs → Is-just (delete-min₀ xs) ≃ Non-empty xs}
      (λ where
         .is-propositionʳ _ →
           Eq.right-closure (lower-extensionality _ _ ext) 0
             truncation-is-proposition
         .[]ʳ t →
           Is-just (delete-min₀ [ t ]Q)                 ↝⟨ ≡⇒↝ _ (cong Is-just Q.rec-[]) ⟩
           Is-just (Σ-map id [_]Q ⟨$⟩ T.delete-min₀ t)  ↝⟨ lemma (T.delete-min₀ _) ⟩
           Is-just (T.delete-min₀ t)                    ↔⟨ inverse (∥∥ᴱ≃ (T-propositional (is-just (T.delete-min₀ _)))) ⟩
           ∥ Is-just (T.delete-min₀ t) ∥ᴱ               ↝⟨ EEq.≃ᴱ→≃ (∥∥ᴱ-cong-⇔ T.Is-just-delete-min₀) ⟩
           ∥ (∃ λ x → x T.∈ t) ∥ᴱ                       ↝⟨ ∥∥ᴱ-cong (∃-cong λ _ → ≡⇒↝ _ (sym ∈[])) ⟩□
           ∥ (∃ λ x → x ∈ [ t ]Q) ∥ᴱ                    □)
      _
    where
    lemma :
      (r : Maybe (A × T.Tree)) →
      Is-just (Σ-map id ([_]Q {R = T._≈_}) ⟨$⟩ r) ≃ Is-just r
    lemma nothing  = F.id
    lemma (just _) = F.id

opaque

  -- The function delete-min₀ returns nothing if and only if the set
  -- is empty.

  @0 Is-nothing-delete-min₀ :
    Is-nothing (delete-min₀ xs) ≃ (∀ {x} → ¬ x ∈ xs)
  Is-nothing-delete-min₀ {xs} =
    Is-nothing (delete-min₀ xs)  ↝⟨ lemma (delete-min₀ xs) ⟩
    ¬ Is-just (delete-min₀ xs)   ↝⟨ ¬-cong (lower-extensionality _ _ ext)
                                      Is-just-delete-min₀ ⟩
    ¬ Non-empty xs               ↝⟨ ¬-Non-empty-≃-∉ ⟩□
    (∀ {x} → ¬ x ∈ xs)           □
    where
    lemma :
      ∀ {a} {A : Type a} (x : Maybe A) → Is-nothing x ≃ (¬ Is-just x)
    lemma nothing  = inverse (¬⊥↔⊤ (lower-extensionality _ _ ext))
    lemma (just x) = inverse (from-bijection Π-left-identity)

------------------------------------------------------------------------
-- Finding the minimum element

opaque
  unfolding Non-empty-lemma

  -- Finds the minimum element. The set must be non-empty.

  find-min : (xs : Set) → @0 Non-empty xs → A
  find-min = Q.elim λ where
    .[]ʳ t ∈t →
      T.find-min t (non-empty-lemma ∈t)
    .[]-respects-relationʳ {x = t₁} {y = t₂} t₁≈t₂ →
      apply-extᴱ (lower-extensionality _ _ ext) λ _ →

      subst (λ xs → @0 Non-empty xs → A)
        ([]-respects-relation (λ {_} → t₁≈t₂))
        (λ _ → T.find-min t₁ _)
        _                                                     ≡⟨ BC.subst-0→ ⟩

      subst (λ _ → A) ([]-respects-relation (λ {_} → t₁≈t₂))
        (T.find-min t₁ _)                                     ≡⟨ subst-const _ ⟩

      T.find-min t₁ _                                         ≡⟨ T.find-min-respects-set-equivalence t₁≈t₂ ⟩∎

      T.find-min t₂ _                                         ∎
    .is-setʳ _ →
      Πᴱ-closure (lower-extensionality _ _ ext) 2 λ _ →
      O.is-set

opaque
  unfolding find-min

  -- The value returned by find-min is in the set.

  @0 find-min-∈ :
    {∈xs : Non-empty xs} →
    find-min xs ∈xs ∈ xs
  find-min-∈ =
    Q.elim-prop {P = λ xs → (∈xs : Non-empty xs) → find-min xs ∈xs ∈ xs}
      (λ where
         .is-propositionʳ _ →
           Π-closure (lower-extensionality _ _ ext) 1 λ _ →
           ∈-propositional
         .[]ʳ t ∈t →                                $⟨ T.find-min-∈ ⟩
           T.find-min t (non-empty-lemma ∈t) T.∈ t  →⟨ ≡⇒↝ _ $
                                                       cong {y = find-min _} (flip T._∈_ _ ∘ (λ f → f _)) $
                                                       sym Q.elim-[] ⟩
           find-min [ t ]Q ∈t T.∈ t                 →⟨ ≡⇒↝ _ (sym ∈[]) ⟩□
           find-min [ t ]Q ∈t ∈ [ t ]Q              □)
      _ _

opaque
  unfolding find-min

  -- The value returned by find-min is a lower bound for the elements
  -- in the set.

  @0 find-min-≤ :
    {∈xs : Non-empty xs} →
    x ∈ xs → find-min xs ∈xs ≤ x
  find-min-≤ {x} =
    Q.elim-prop
      {P = λ xs → (∈xs : Non-empty xs) → x ∈ xs → find-min xs ∈xs ≤ x}
      (λ where
         .is-propositionʳ _ →
           Π-closure (lower-extensionality _ (lsuc a) ext) 1 λ _ →
           Π-closure (lower-extensionality _ (lsuc a) ext) 1 λ _ →
           O.≤-propositional
         .[]ʳ t ∈t →
           x ∈ [ t ]Q                             →⟨ ≡⇒↝ _ ∈[] ⟩
           x T.∈ t                                →⟨ T.find-min-≤ ⟩
           T.find-min t (non-empty-lemma ∈t) ≤ x  →⟨ ≡⇒↝ _ $
                                                     cong {y = find-min _} (flip _≤_ _ ∘ (λ f → f _)) $
                                                     sym Q.elim-[] ⟩□
           find-min [ t ]Q ∈t ≤ x                 □)
      _ _

opaque
  unfolding Non-empty

  -- A set is inhabited if and only if it is non-empty.

  @0 ∈⇔Non-empty : (∃ λ x → x ∈ xs) ⇔ Non-empty xs
  ∈⇔Non-empty = record
    { to   = ∣_∣
    ; from = λ ∈xs → find-min _ ∈xs , find-min-∈
    }

------------------------------------------------------------------------
-- Conversion to lists

opaque
  unfolding Set

  -- Converts the set to a sorted list.

  to-List : Set → List A
  to-List = Q.rec λ where
    .[]ʳ                   → T.to-List
    .[]-respects-relationʳ → _⇔_.to T.≈⇔to-List≡to-List
    .is-setʳ               → H-level-List 0 O.is-set

opaque
  unfolding to-List ∈[]

  -- The list to-List xs is bag equivalent to the set xs.
  --
  -- Note that this implies that the set is finite.

  @0 ∈to-List≃ : (x L.∈ to-List xs) ≃ (x ∈ xs)
  ∈to-List≃ {x} =
    Q.elim-prop {P = λ xs → (x L.∈ to-List xs) ≃ (x ∈ xs)}
      (λ where
         .is-propositionʳ _ →
           Eq.right-closure (lower-extensionality _ _ ext) 0
             ∈-propositional
         .[]ʳ t →
           x L.∈ to-List [ t ]Q  ↝⟨ ≡⇒↝ _ (cong (L._∈_ _) Q.rec-[]) ⟩
           x L.∈ T.to-List t     ↝⟨ T.∈-to-List ⟩
           x T.∈ t               ↝⟨ ≡⇒↝ _ (sym ∈[]) ⟩□
           x ∈ [ t ]Q            □)
      _

opaque
  unfolding to-List

  -- The list returned by to-List is strictly ascending.

  @0 Sorted-to-List : Sorted min max (to-List xs)
  Sorted-to-List =
    Q.elim-prop {P = λ xs → Sorted min max (to-List xs)}
      (λ where
         .is-propositionʳ _ →
           Sorted-propositional (to-List _)
         .[]ʳ t →
                                            $⟨ T.Sorted-to-List ⟩
           Sorted min max (T.to-List t)     →⟨ subst (Sorted _ _) (sym Q.rec-[]) ⟩
           Sorted min max (to-List [ t ]Q)  □)
      _

------------------------------------------------------------------------
-- An equality test

opaque
  unfolding ≈≃[]≡[]

  infix 4 _≟_

  -- An equality test.

  _≟_ : Decidable-erased-equality Set
  _≟_ =
    Q.elim-prop₂ _
      (λ _ _ →
         BC.Is-proposition-Dec-Erased
           (lower-extensionality (lsuc a) _ ext) Set-set)
      (λ t₁ t₂ →
         Dec-Erased-map (from-equivalence ≈≃[]≡[]) (t₁ T.≟ t₂))

------------------------------------------------------------------------
-- Sizes

opaque
  unfolding Set

  -- The size of a finite set.
  --
  -- The function is erased because it is (at least) linear in the
  -- size of the set, so it is not recommended to be used at run-time.

  @0 size : Set → ℕ
  size = Q.rec λ where
    .[]ʳ                   → T.size
    .[]-respects-relationʳ → T.size-respects-set-equivalence
    .is-setʳ               → ℕ-set

opaque
  unfolding size to-List

  -- The function size can be expressed using length and to-List.

  @0 size≡length∘to-List : size xs ≡ length (to-List xs)
  size≡length∘to-List =
    Q.elim-prop {P = λ xs → size xs ≡ length (to-List xs)}
      (λ where
         .is-propositionʳ _ →
           ℕ-set
         .[]ʳ t →
           size [ t ]Q              ≡⟨ Q.rec-[] ⟩
           T.size t                 ≡⟨ T.size≡length∘to-List ⟩
           length (T.to-List t)     ≡⟨ cong length (sym Q.rec-[]) ⟩∎
           length (to-List [ t ]Q)  ∎)
      _
