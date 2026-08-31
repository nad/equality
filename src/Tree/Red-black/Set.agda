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
open import Equivalence.Erased eq using (_≃ᴱ_)
open import Erased.Level-1 eq as Erased
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level hiding (Set)
open import H-level.Closure eq
open import H-level.Truncation.Propositional.Erased.Axiomatised eq
open import List eq
open import Maybe eq
open import Monad eq
import Nat eq as N
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

  -- The value y is in insert x xs if and only if merely y is x or y
  -- is in xs.

  @0 ∈insert⇔ : y ∈ insert x xs ⇔ y ≡ x ∥⊎∥ᴱ y ∈ xs
  ∈insert⇔ {y} {x} {xs} =
    Q.elim-prop {P = λ xs → y ∈ insert x xs ⇔ y ≡ x ∥⊎∥ᴱ y ∈ xs}
      (λ where
         .is-propositionʳ _ →
           ⇔-closure (lower-extensionality _ _ ext) 1 ∈-propositional
             truncation-is-proposition
         .[]ʳ t →
           y ∈ insert x [ t ]Q      ↝⟨ ≡⇒↝ _ (cong (_∈_ _) Q.rec-[]) ⟩
           y ∈ [ T.insert x t ]Q    ↝⟨ ≡⇒↝ _ ∈[] ⟩
           y T.∈ T.insert x t       ↔⟨ inverse (∥∥ᴱ≃ T.∈-propositional) ⟩
           ∥ y T.∈ T.insert x t ∥ᴱ  ↝⟨ ∥∥ᴱ-cong T.∈-insert ⟩
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

  -- The value y is in delete x xs if and only if y is distinct from x
  -- and y is in xs.

  @0 ∈delete⇔ : y ∈ delete x xs ⇔ y ≢ x × y ∈ xs
  ∈delete⇔ {y} {x} {xs} =
    Q.elim-prop {P = λ xs → y ∈ delete x xs ⇔ y ≢ x × y ∈ xs}
      (λ where
         .is-propositionʳ _ →
           ⇔-closure (lower-extensionality _ _ ext) 1 ∈-propositional
             (×-closure 1
                (¬-propositional (lower-extensionality _ _ ext))
                ∈-propositional)
         .[]ʳ t →
           y ∈ delete x [ t ]Q      ↝⟨ ≡⇒↝ _ (cong (_∈_ _) Q.rec-[]) ⟩
           y ∈ [ T.delete x t ]Q    ↝⟨ ≡⇒↝ _ ∈[] ⟩
           y T.∈ T.delete x t       ↝⟨ T.∈-delete ⟩
           y ≢ x × y T.∈ t          ↝⟨ ≡⇒↝ _ (cong (_×_ _) (sym ∈[])) ⟩□
           y ≢ x × y ∈ [ t ]Q       □)
      xs

opaque

  -- If x is not in xs, then delete x xs is equal to xs.

  @0 ∉→delete≡ : ¬ x ∈ xs → delete x xs ≡ xs
  ∉→delete≡ {x} {xs} x∉xs =
    extensionality λ {y} →
      y ∈ delete x xs  ↝⟨ ∈delete⇔ ⟩
      y ≢ x × y ∈ xs   ↝⟨ record
                            { to   = proj₂
                            ; from = λ y∈xs → x∉xs ∘ flip (subst (_∈ _)) y∈xs , y∈xs
                            } ⟩□
      y ∈ xs           □

------------------------------------------------------------------------
-- Deleting the minimum element

opaque
  unfolding Set T.Delete-min-≈

  -- Removes the minimum element, if any. If the set is empty, then
  -- nothing is returned.

  delete-min : Set → Maybe (A × Set)
  delete-min = Q.rec λ where
      .is-setʳ →
        ⊎-closure 0 (H-level.mono (N.zero≤ 2) ⊤-contractible) $
        ×-closure 2 O.is-set Set-set
      .[]ʳ t →
        Σ-map id [_]Q ⟨$⟩ T.delete-min t
      .[]-respects-relationʳ {x = t₁} {y = t₂} →
        t₁ T.≈ t₂                                           →⟨ T.delete-min-respects-set-equivalence ⟩

        T.Delete-min-≈ (T.delete-min t₁) (T.delete-min t₂)  →⟨ lemma (T.delete-min _) _ ⟩□

        Σ-map id [_]Q ⟨$⟩ T.delete-min t₁ ≡
        Σ-map id [_]Q ⟨$⟩ T.delete-min t₂                   □
    where
    @0 lemma :
      (r₁ r₂ : Maybe (A × T.Tree)) →
      T.Delete-min-≈ r₁ r₂ →
      _≡_ {A = Maybe (A × Set)}
        (Σ-map id [_]Q ⟨$⟩ r₁) (Σ-map id [_]Q ⟨$⟩ r₂)
    lemma nothing  nothing  _               = refl _
    lemma (just _) (just _) (x₁≡x₂ , t₁≈t₂) =
      cong just $ cong₂ _,_ x₁≡x₂ (Q.[]-respects-relation t₁≈t₂)

opaque
  unfolding T._≈_ delete-min ∈[]

  -- The value of delete-min xs is just (x , xs′) if and only if
  --
  -- * x is strictly smaller than all elements in xs′ and
  --
  -- * every value is in xs if and only it is either equal to x or in
  --   xs′.

  @0 delete-min-just-⇔ :
    delete-min xs ≡ just (x , xs′) ⇔
    (∀ {y} → y ∈ xs′ → x < y) × (∀ {y} → y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′)
  delete-min-just-⇔ {x} =
    Q.elim-prop₂
      (λ xs xs′ →
         delete-min xs ≡ just (x , xs′) ⇔
         (∀ {y} → y ∈ xs′ → x < y) ×
         (∀ {y} → y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′))
      (λ _ _ →
         ⇔-closure (lower-extensionality (lsuc a) (lsuc a) ext) 1
           (⊎-closure 0 (H-level.mono (N.zero≤ 2) ⊤-contractible)
              (×-closure 2 O.is-set Set-set))
           (Σ-closure 1
              (implicit-Π-closure (lower-extensionality _ (lsuc a) ext)
                 1 λ _ →
               Π-closure (lower-extensionality _ (lsuc a) ext) 1 λ _ →
               O.<-propositional) λ ∈→< →
              (implicit-Π-closure (lower-extensionality _ _ ext) 1 λ _ →
               ⇔-closure (lower-extensionality _ _ ext) 1
                 ∈-propositional
                 (⊎-closure-propositional
                    (λ ≡x ∈xs′ → O.<→≢ (∈→< ∈xs′) (sym ≡x))
                    O.is-set ∈-propositional))))
      (λ t₁ t₂ →
         delete-min [ t₁ ]Q ≡ just (x , [ t₂ ]Q)                    ↝⟨ ≡⇒↝ _ (cong (_≡ _) Q.rec-[]) ⟩

         Σ-map id [_]Q ⟨$⟩ T.delete-min t₁ ≡ just (x , [ t₂ ]Q)     ↝⟨ record { to   = lemma _
                                                                              ; from = λ (t₂′ , eq , t₂≈t₂′) →
           Σ-map id [_]Q ⟨$⟩ T.delete-min t₁                                      ≡⟨ cong (_ ⟨$⟩_) eq ⟩
           just (x , [ t₂′ ]Q)                                                    ≡⟨ cong (just ∘ (x ,_))
                                                                                       (sym (Q.[]-respects-relation (λ {_} → t₂≈t₂′))) ⟩∎
           just (x , [ t₂ ]Q)                                                     ∎
                                                                              } ⟩

         (∃ λ t₂′ → T.delete-min t₁ ≡ just (x , t₂′) × t₂ T.≈ t₂′)  ↝⟨ T.delete-min-just-⇔ ⟩

         (∀ {y} → y T.∈ t₂ → x < y) ×
         (∀ {y} → y T.∈ t₁ ⇔ y ≡ x ⊎ y T.∈ t₂)                      ↝⟨ implicit-∀-cong _ (→-cong₁ _ (≡⇒↝ equivalence (sym ∈[])))
                                                                         ×-cong
                                                                       implicit-∀-cong _
                                                                         (⇔-cong _ (≡⇒↝ _ (sym ∈[])) (F.id ⊎-cong ≡⇒↝ _ (sym ∈[]))) ⟩□
         (∀ {y} → y ∈ [ t₂ ]Q → x < y) ×
         (∀ {y} → y ∈ [ t₁ ]Q ⇔ y ≡ x ⊎ y ∈ [ t₂ ]Q)                □)
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
      x′ ≡ x × [ t′ ]Q ≡ [ t ]Q                             →⟨ Σ-map id $
                                                               Q.effective₀ (lower-extensionality o o ext) prop-ext T.≈-equivalence
                                                                 (λ _ _ → T.≈-propositional (lower-extensionality _ _ ext)) ⟩
      x′ ≡ x × t′ T.≈ t                                     →⟨ (λ (x′≡x , t′≈t) → _ , cong (just ∘ (_, t′)) x′≡x , F.inverse t′≈t) ⟩
      (∃ λ t″ → just (x′ , t′) ≡ just (x , t″) × t T.≈ t″)  □

opaque

  -- If every element in xs is either equal to x or in xs′, and x is
  -- strictly smaller than all elements in xs′, then delete-min xs is
  -- equal to just (x , xs′).

  @0 delete-min-just :
    (∀ {y} → y ∈ xs′ → x < y) →
    (∀ {y} → y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′) →
    delete-min xs ≡ just (x , xs′)
  delete-min-just = curry (_⇔_.from delete-min-just-⇔)

opaque

  -- An ordering lemma for delete-min.

  @0 <-delete-min :
    delete-min xs ≡ just (x , xs′) →
    y ∈ xs′ → x < y
  <-delete-min eq = _⇔_.to delete-min-just-⇔ eq .proj₁

opaque

  -- A membership lemma for delete-min.

  @0 ∈-delete-min :
    delete-min xs ≡ just (x , xs′) →
    y ∈ xs ⇔ y ≡ x ⊎ y ∈ xs′
  ∈-delete-min eq = _⇔_.to delete-min-just-⇔ eq .proj₂

opaque

  -- A variant of ∈-delete-min.

  @0 ∈-delete-min-≢ :
    delete-min xs ≡ just (x , xs′) →
    y ∈ xs′ ⇔ y ≢ x × y ∈ xs
  ∈-delete-min-≢ {xs} {x} {xs′} {y} eq =
    y ∈ xs′         ↝⟨ inverse (⇔⊎→×¬⇔ (∈-delete-min eq) (flip ((_∘ sym) ∘ O.<→≢ ∘ <-delete-min eq))) ⟩
    y ∈ xs × y ≢ x  ↔⟨ ×-comm ⟩□
    y ≢ x × y ∈ xs  □

opaque
  unfolding delete-min ∈[]

  -- The function delete-min returns nothing if and only if the set is
  -- empty.

  @0 Is-nothing-delete-min :
    Is-nothing (delete-min xs) ⇔ (∀ {x} → ¬ x ∈ xs)
  Is-nothing-delete-min =
    Q.elim-prop
      {P = λ xs → Is-nothing (delete-min xs) ⇔ (∀ {x} → ¬ x ∈ xs)}
      (λ where
         .is-propositionʳ _ →
           ⇔-closure (lower-extensionality _ _ ext) 1
             (T-propositional (is-nothing (delete-min _)))
             (implicit-Π-closure (lower-extensionality _ _ ext) 1 λ _ →
              ¬-propositional (lower-extensionality _ _ ext))
         .[]ʳ t →
           Is-nothing (delete-min [ t ]Q)                 ↝⟨ ≡⇒↝ _ (cong Is-nothing Q.rec-[]) ⟩
           Is-nothing (Σ-map id [_]Q ⟨$⟩ T.delete-min t)  ↝⟨ lemma (T.delete-min _) ⟩
           Is-nothing (T.delete-min t)                    ↝⟨ T.Is-nothing-delete-min ⟩
           (∀ {x} → ¬ x T.∈ t)                            ↝⟨ implicit-∀-cong _ $
                                                             ¬-cong _ (≡⇒↝ _ (sym ∈[])) ⟩
           (∀ {x} → ¬ x ∈ [ t ]Q)                         □)
      _
    where
    lemma :
      (r : Maybe (A × T.Tree)) →
      Is-nothing (Σ-map id ([_]Q {R = T._≈_}) ⟨$⟩ r) ⇔ Is-nothing r
    lemma nothing  = F.id
    lemma (just _) = F.id

opaque
  unfolding delete-min ∈[]

  -- The value of delete-min xs is just something if and only if xs is
  -- (merely) non-empty.

  @0 Is-just-delete-min :
    Is-just (delete-min xs) ⇔ ∥ (∃ λ x → x ∈ xs) ∥ᴱ
  Is-just-delete-min =
    Q.elim-prop
      {P = λ xs → Is-just (delete-min xs) ⇔ ∥ (∃ λ x → x ∈ xs) ∥ᴱ}
      (λ where
         .is-propositionʳ _ →
           ⇔-closure (lower-extensionality _ _ ext) 1
             (T-propositional (is-just (delete-min _)))
             truncation-is-proposition
         .[]ʳ t →
           Is-just (delete-min [ t ]Q)                 ↝⟨ ≡⇒↝ _ (cong Is-just Q.rec-[]) ⟩
           Is-just (Σ-map id [_]Q ⟨$⟩ T.delete-min t)  ↝⟨ lemma (T.delete-min _) ⟩
           Is-just (T.delete-min t)                    ↔⟨ inverse (∥∥ᴱ≃ (T-propositional (is-just (T.delete-min _)))) ⟩
           ∥ Is-just (T.delete-min t) ∥ᴱ               ↝⟨ ∥∥ᴱ-cong T.Is-just-delete-min ⟩
           ∥ (∃ λ x → x T.∈ t) ∥ᴱ                      ↝⟨ ∥∥ᴱ-cong (∃-cong λ _ → ≡⇒↝ _ (sym ∈[])) ⟩□
           ∥ (∃ λ x → x ∈ [ t ]Q) ∥ᴱ                   □)
      _
    where
    lemma :
      (r : Maybe (A × T.Tree)) →
      Is-just (Σ-map id ([_]Q {R = T._≈_}) ⟨$⟩ r) ⇔ Is-just r
    lemma nothing  = F.id
    lemma (just _) = F.id

------------------------------------------------------------------------
-- Finding the minimum element

opaque

  -- A merely non-empty set contains a least element.

  find-min :
    {xs : Set} →
    @0 ∥ (∃ λ x → x ∈ xs) ∥ᴱ →
    ∃ λ (x : A) → Erased (x ∈ xs × (∀ {y} → y ∈ xs → x ≤ y))
  find-min {xs} non-empty =
    lemma (delete-min xs) (refl _) non-empty
    where
    lemma :
      (r : Maybe (A × Set)) →
      @0 delete-min xs ≡ r →
      @0 ∥ (∃ λ x → x ∈ xs) ∥ᴱ →
      ∃ λ x → Erased (x ∈ xs × (∀ {y} → y ∈ xs → x ≤ y))
    lemma nothing eq ∈xs =
      ⊥-elim₀
        (Tr.rec
           (λ @0 where
              .truncation-is-propositionʳ →
                ⊥-propositional
              .∣∣ʳ (_ , ∈xs) →
                _⇔_.to Is-nothing-delete-min
                  (subst Is-nothing (sym eq) _) ∈xs)
           ∈xs)
    lemma (just (x , _)) eq _ =
      x ,
      [ ( _⇔_.from (∈-delete-min eq) (inj₁ (refl _))
        , λ y∈xs →
            case _⇔_.to (∈-delete-min eq) y∈xs of λ @0 where
              (inj₁ y≡x)   → O.≤-reflexive (sym y≡x)
              (inj₂ y∈xs′) → O.<→≤ (<-delete-min eq y∈xs′)
        )
      ]

opaque

  -- A set is non-empty if and only if it is merely non-empty.

  @0 ∈⇔∥∈∥ᴱ : (∃ λ x → x ∈ xs) ⇔ ∥ (∃ λ x → x ∈ xs) ∥ᴱ
  ∈⇔∥∈∥ᴱ {xs} = record
    { to   = ∣_∣
    ; from =
        ∥ (∃ λ x → x ∈ xs) ∥ᴱ                                 →⟨ (λ hyp → find-min hyp) ⟩
        (∃ λ x → Erased (x ∈ xs × (∀ {y} → y ∈ xs → x ≤ y)))  ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
        (∃ λ x → x ∈ xs × (∀ {y} → y ∈ xs → x ≤ y))           →⟨ Σ-map id proj₁ ⟩
        (∃ λ x → x ∈ xs)                                      □
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
