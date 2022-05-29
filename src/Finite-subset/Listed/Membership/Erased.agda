------------------------------------------------------------------------
-- A membership relation for listed finite subsets (defined using
-- erased univalence)
------------------------------------------------------------------------

-- Based on Frumin, Geuvers, Gondelman and van der Weide's "Finite
-- Sets in Homotopy Type Theory".

{-# OPTIONS --erased-cubical --safe #-}

import Equality.Path as P

module Finite-subset.Listed.Membership.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Dec
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (swap)

open import Bag-equivalence equality-with-J as BE using (_∼[_]_; set)
open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equality.Path.Isomorphisms.Univalence eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Erased.Cubical eq as EC
  using (Erased; [_]; Dec-Erased; Very-stable)
open import Finite-subset.Listed eq
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; ∣_∣; _∥⊎∥_)
open import Injection equality-with-J using (Injective)
open import Maybe equality-with-J using (maybe)
open import Nat equality-with-J as Nat using (_<_)
open import Quotient eq as Q using (_/_)
import Univalence-axiom equality-with-J as Univ

private
  variable
    a                                 : Level
    A B                               : Type a
    H ms p q x x₁ x₂ y y₁ y₂ ys z _≟_ : A
    P                                 : A → Type p
    f                                 : (x : A) → P x
    m n                               : ℕ

------------------------------------------------------------------------
-- Membership

private

  -- Membership is used to define _∈_ and ∈-propositional below.
  --
  -- Note that Membership is erased. This ensures that the definition
  -- can use univalence, even though this module uses
  -- --erased-cubical.

  @0 Membership : {A : Type a} → A → Finite-subset-of A → Proposition a
  Membership x = rec r
    where
    r : Rec _ _
    r .[]ʳ = ⊥ , ⊥-propositional

    r .∷ʳ y z (x∈z , _) =
      (x ≡ y ∥⊎∥ x∈z) , Trunc.truncation-is-proposition

    r .dropʳ y z (P , P-prop) =
      _↔_.to (ignore-propositional-component
                (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ
        (x ≡ y ∥⊎∥ x ≡ y ∥⊎∥ P    ↔⟨ Trunc.∥⊎∥-assoc ⟩
         (x ≡ y ∥⊎∥ x ≡ y) ∥⊎∥ P  ↔⟨ Trunc.idempotent Trunc.∥⊎∥-cong F.id ⟩
         ∥ x ≡ y ∥ ∥⊎∥ P          ↔⟨ inverse Trunc.truncate-left-∥⊎∥ ⟩□
         x ≡ y ∥⊎∥ P              □)

    r .swapʳ y z u (P , P-prop) =
      _↔_.to (ignore-propositional-component
                (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ
        (x ≡ y ∥⊎∥ x ≡ z ∥⊎∥ P    ↔⟨ Trunc.∥⊎∥-assoc ⟩
         (x ≡ y ∥⊎∥ x ≡ z) ∥⊎∥ P  ↔⟨ (Trunc.∥⊎∥-comm Trunc.∥⊎∥-cong F.id) ⟩
         (x ≡ z ∥⊎∥ x ≡ y) ∥⊎∥ P  ↔⟨ inverse Trunc.∥⊎∥-assoc ⟩□
         x ≡ z ∥⊎∥ x ≡ y ∥⊎∥ P    □)

    r .is-setʳ =
      Univ.∃-H-level-H-level-1+ ext univ 1

-- Membership.
--
-- The type is wrapped to make it easier for Agda to infer the subset
-- argument.

private module Dummy where

  infix 4 _∈_

  record _∈_
    {A : Type a} (x : A) (y : Finite-subset-of A) : Type a where
    constructor box
    field
      unbox : Erased (proj₁ (Membership x y))

open Dummy public using (_∈_) hiding (module _∈_)

-- The negation of membership.

infix 4 _∉_

_∉_ : {A : Type a} → A → Finite-subset-of A → Type a
x ∉ y = ¬ x ∈ y

private

  -- An unfolding lemma.

  ∈≃ : (x ∈ y) ≃ Erased (proj₁ (Membership x y))
  ∈≃ = Eq.↔→≃ Dummy._∈_.unbox Dummy.box refl refl

-- Membership is propositional.

∈-propositional : Is-proposition (x ∈ y)
∈-propositional {x = x} {y = y} =                   $⟨ [ proj₂ (Membership x y) ] ⟩
  Erased (Is-proposition (proj₁ (Membership x y)))  →⟨ EC.Erased-H-level↔H-level 1 _ ⟩
  Is-proposition (Erased (proj₁ (Membership x y)))  →⟨ H-level-cong _ 1 (inverse ∈≃) ⟩□
  Is-proposition (x ∈ y)                            □

-- Membership is very stable.

Very-stable-∈ : Very-stable (x ∈ y)
Very-stable-∈ {x = x} {y = y} =                  $⟨ EC.Very-stable-Erased ⟩
  Very-stable (Erased (proj₁ (Membership x y)))  →⟨ EC.Very-stable-cong _ (inverse ∈≃) ⟩□
  Very-stable (x ∈ y)                            □

-- A lemma characterising [].

∈[]≃ : (x ∈ []) ≃ ⊥₀
∈[]≃ {x = x} =
  x ∈ []    ↝⟨ ∈≃ ⟩
  Erased ⊥  ↔⟨ EC.Erased-⊥↔⊥ ⟩
  ⊥         ↔⟨ ⊥↔⊥ ⟩□
  ⊥₀        □

-- The type Erased ((x ∈ y) ≃ A) is equivalent to (x ∈ y) ≃ Erased A.
-- Thus certain erased lemmas below (like ∈∷≃ and ∈singleton≃) can be
-- turned into non-erased lemmas with related types.

∈≃≃∈≃Erased : Erased ((x ∈ y) ≃ A) ≃ ((x ∈ y) ≃ Erased A)
∈≃≃∈≃Erased {x = x} {y = y} {A = A} =
  Erased ((x ∈ y) ≃ A)       ↝⟨ EC.Erased-↝↝↝ ext ⟩
  Erased (x ∈ y) ≃ Erased A  ↝⟨ ≃-cong ext (EC.Very-stable→Stable 0 Very-stable-∈) F.id ⟩□
  (x ∈ y) ≃ Erased A         □

-- A lemma characterising _∷_ (in erased contexts).

@0 ∈∷≃ : (x ∈ y ∷ z) ≃ (x ≡ y ∥⊎∥ x ∈ z)
∈∷≃ {x = x} {y = y} {z = z} =
  x ∈ y ∷ z                                  ↝⟨ ∈≃ ⟩
  Erased (x ≡ y ∥⊎∥ proj₁ (Membership x z))  ↔⟨ EC.erased EC.Erased↔ ⟩
  x ≡ y ∥⊎∥ proj₁ (Membership x z)           ↔⟨ F.id Trunc.∥⊎∥-cong inverse (EC.erased EC.Erased↔) ⟩
  x ≡ y ∥⊎∥ Erased (proj₁ (Membership x z))  ↝⟨ F.id Trunc.∥⊎∥-cong inverse ∈≃ ⟩□
  x ≡ y ∥⊎∥ x ∈ z                            □

-- A variant of ∈∷≃.

∈≢∷≃ : x ≢ y → (x ∈ y ∷ z) ≃ (x ∈ z)
∈≢∷≃ {x = x} {y = y} {z = z} x≢y =
  EC.Very-stable→Stable 0
    (EC.Very-stable-↝ ext Very-stable-∈ Very-stable-∈)
    [ x ∈ y ∷ z        ↝⟨ ∈∷≃ ⟩
      x ≡ y ∥⊎∥ x ∈ z  ↔⟨ Trunc.drop-⊥-left-∥⊎∥ ∈-propositional x≢y ⟩
      x ∈ z            □
    ]

-- A lemma characterising singleton (in erased contexts).

@0 ∈singleton≃ : (x ∈ singleton y) ≃ ∥ x ≡ y ∥
∈singleton≃ {x = x} {y = y} =
  x ∈ singleton y   ↝⟨ ∈∷≃ ⟩
  x ≡ y ∥⊎∥ x ∈ []  ↔⟨ Trunc.∥∥-cong $ drop-⊥-right ∈[]≃ ⟩□
  ∥ x ≡ y ∥         □

-- Some "introduction rules" for _∈_.

∈→∈∷ : x ∈ z → x ∈ y ∷ z
∈→∈∷ {x = x} {z = z} {y = y} =
  EC.Very-stable→Stable 0
    (EC.Very-stable-Π ext λ _ → Very-stable-∈)
    [ x ∈ z            →⟨ ∣_∣ ∘ inj₂ ⟩
      x ≡ y ∥⊎∥ x ∈ z  ↔⟨ inverse ∈∷≃ ⟩□
      x ∈ y ∷ z        □
    ]

∥≡∥→∈∷ : ∥ x ≡ y ∥ → x ∈ y ∷ z
∥≡∥→∈∷ {x = x} {y = y} {z = z} =
  EC.Very-stable→Stable 0
    (EC.Very-stable-Π ext λ _ → Very-stable-∈)
    [ ∥ x ≡ y ∥        →⟨ Trunc.∥∥-map inj₁ ⟩
      x ≡ y ∥⊎∥ x ∈ z  ↔⟨ inverse ∈∷≃ ⟩□
      x ∈ y ∷ z        □
    ]

≡→∈∷ : x ≡ y → x ∈ y ∷ z
≡→∈∷ = ∥≡∥→∈∷ ∘ ∣_∣

∥≡∥→∈singleton : ∥ x ≡ y ∥ → x ∈ singleton y
∥≡∥→∈singleton = ∥≡∥→∈∷

≡→∈singleton : x ≡ y → x ∈ singleton y
≡→∈singleton = ≡→∈∷

-- Membership of a union of two subsets can be expressed in terms of
-- membership of the subsets (in erased contexts).

@0 ∈∪≃ : (x ∈ y ∪ z) ≃ (x ∈ y ∥⊎∥ x ∈ z)
∈∪≃ {x = x} {y = y} {z = z} = elim-prop e y
  where
  e : Elim-prop (λ y → (x ∈ y ∪ z) ≃ (x ∈ y ∥⊎∥ x ∈ z))
  e .[]ʳ =
    x ∈ z             ↔⟨ inverse $ Trunc.∥∥↔ ∈-propositional ⟩
    ∥ x ∈ z ∥         ↔⟨ Trunc.∥∥-cong (inverse $ drop-⊥-left ∈[]≃) ⟩□
    x ∈ [] ∥⊎∥ x ∈ z  □

  e .∷ʳ {y = u} y hyp =
    x ∈ y ∷ u ∪ z                ↝⟨ ∈∷≃ ⟩
    x ≡ y ∥⊎∥ x ∈ u ∪ z          ↝⟨ F.id Trunc.∥⊎∥-cong hyp ⟩
    x ≡ y ∥⊎∥ x ∈ u ∥⊎∥ x ∈ z    ↔⟨ Trunc.∥⊎∥-assoc ⟩
    (x ≡ y ∥⊎∥ x ∈ u) ∥⊎∥ x ∈ z  ↝⟨ Trunc.∥∥-cong (inverse ∈∷≃ ⊎-cong F.id) ⟩□
    x ∈ y ∷ u ∥⊎∥ x ∈ z          □

  e .is-propositionʳ _ =
    Eq.left-closure ext 0 ∈-propositional

-- More "introduction rules".

∈→∈∪ˡ : x ∈ y → x ∈ y ∪ z
∈→∈∪ˡ {x = x} {y = y} {z = z} =
  EC.Very-stable→Stable 0
    (EC.Very-stable-Π ext λ _ → Very-stable-∈)
    [ x ∈ y            →⟨ ∣_∣ ∘ inj₁ ⟩
      x ∈ y ∥⊎∥ x ∈ z  ↔⟨ inverse ∈∪≃ ⟩□
      x ∈ y ∪ z        □
    ]

∈→∈∪ʳ : ∀ y → x ∈ z → x ∈ y ∪ z
∈→∈∪ʳ {x = x} {z = z} y =
  x ∈ z      →⟨ ∈→∈∪ˡ ⟩
  x ∈ z ∪ y  →⟨ ≡⇒↝ _ (cong (_ ∈_) (comm z)) ⟩□
  x ∈ y ∪ z  □

-- A lemma characterising join (in erased contexts).

@0 ∈join≃ : (x ∈ join z) ≃ ∥ (∃ λ y → x ∈ y × y ∈ z) ∥
∈join≃ {x = x} = elim-prop e _
  where
  e : Elim-prop (λ z → (x ∈ join z) ≃ ∥ (∃ λ y → x ∈ y × y ∈ z) ∥)
  e .[]ʳ =
    x ∈ join []                   ↔⟨⟩
    x ∈ []                        ↝⟨ ∈[]≃ ⟩
    ⊥                             ↔⟨ inverse $ Trunc.∥∥↔ ⊥-propositional ⟩
    ∥ ⊥ ∥                         ↔⟨ Trunc.∥∥-cong (inverse (×-right-zero {ℓ₁ = lzero} F.∘
                                                             ∃-cong (λ _ → ×-right-zero))) ⟩
    ∥ (∃ λ y → x ∈ y × ⊥) ∥       ↝⟨ Trunc.∥∥-cong (∃-cong λ _ → ∃-cong λ _ → inverse ∈[]≃) ⟩□
    ∥ (∃ λ y → x ∈ y × y ∈ []) ∥  □
  e .∷ʳ {y = z} u hyp =
    x ∈ join (u ∷ z)                                     ↔⟨⟩
    x ∈ u ∪ join z                                       ↝⟨ ∈∪≃ ⟩
    x ∈ u ∥⊎∥ x ∈ join z                                 ↝⟨ F.id Trunc.∥⊎∥-cong hyp ⟩
    x ∈ u ∥⊎∥ ∥ (∃ λ y → x ∈ y × y ∈ z) ∥                ↔⟨ inverse Trunc.truncate-right-∥⊎∥ ⟩
    x ∈ u ∥⊎∥ (∃ λ y → x ∈ y × y ∈ z)                    ↔⟨ ∃-intro _ _ Trunc.∥⊎∥-cong F.id ⟩
    (∃ λ y → x ∈ y × y ≡ u) ∥⊎∥ (∃ λ y → x ∈ y × y ∈ z)  ↔⟨ Trunc.∥∥-cong $ inverse $
                                                            ∃-⊎-distrib-left F.∘
                                                            (∃-cong λ _ → ∃-⊎-distrib-left) ⟩
    ∥ (∃ λ y → x ∈ y × (y ≡ u ⊎ y ∈ z)) ∥                ↔⟨ inverse $
                                                            Trunc.flatten′
                                                              (λ F → ∃ λ y → x ∈ y × F (y ≡ u ⊎ y ∈ z))
                                                              (λ f → Σ-map id (Σ-map id f))
                                                              (λ (y , p , q) → Trunc.∥∥-map (λ q → y , p , q) q) ⟩
    ∥ (∃ λ y → x ∈ y × (y ≡ u ∥⊎∥ y ∈ z)) ∥              ↝⟨ (Trunc.∥∥-cong $ ∃-cong λ _ → ∃-cong λ _ → inverse ∈∷≃) ⟩□
    ∥ (∃ λ y → x ∈ y × y ∈ u ∷ z) ∥                      □
  e .is-propositionʳ _ =
    Eq.left-closure ext 0 ∈-propositional

-- If truncated equality is decidable (with erased proofs), then
-- membership is decidable.

member? :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (x : A) (y : Finite-subset-of A) → Dec (x ∈ y)
member? equal? x = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ          = no λ ()
  e .∷ʳ {y = z} y = case equal? x y of λ where
    (yes ∥x≡y∥) _ →
      yes (EC.Very-stable→Stable 0 Very-stable-∈
             [ ∥≡∥→∈∷ (EC.erased ∥x≡y∥) ])
    (no ¬∥x≡y∥) →
      P.[ (λ x∈z → yes (∈→∈∷ x∈z))
        , (λ x∉z → no (EC.Stable-¬
             [ x ∈ y ∷ z        ↔⟨ ∈∷≃ ⟩
               x ≡ y ∥⊎∥ x ∈ z  →⟨ Trunc.∥∥-map P.[ EC.erased ¬∥x≡y∥ ∘ ∣_∣ , x∉z ] ⟩
               ∥ ⊥ ∥            ↔⟨ Trunc.not-inhabited⇒∥∥↔⊥ id ⟩□
               ⊥                □
             ]))
        ]
  e .is-propositionʳ y =
    Dec-closure-propositional ext ∈-propositional

-- If x is a member of y, then x ∷ y is equal to y (in erased
-- contexts).

@0 ∈→∷≡ : x ∈ y → x ∷ y ≡ y
∈→∷≡ {x = x} = elim-prop e _
  where
  e : Elim-prop (λ y → x ∈ y → x ∷ y ≡ y)
  e .∷ʳ {y = y} z hyp =
    x ∈ z ∷ y            ↔⟨ ∈∷≃ ⟩
    x ≡ z ∥⊎∥ x ∈ y      →⟨ id Trunc.∥⊎∥-cong hyp ⟩
    x ≡ z ∥⊎∥ x ∷ y ≡ y  →⟨ Trunc.rec is-set
                              P.[ (λ x≡z →
      x ∷ z ∷ y                    ≡⟨ cong (λ x → x ∷ _) x≡z ⟩
      z ∷ z ∷ y                    ≡⟨ drop ⟩∎
      z ∷ y                        ∎)
                                , (λ x∷y≡y →
      x ∷ z ∷ y                    ≡⟨ swap ⟩
      z ∷ x ∷ y                    ≡⟨ cong (_ ∷_) x∷y≡y ⟩∎
      z ∷ y                        ∎)
                                ] ⟩□
    x ∷ z ∷ y ≡ z ∷ y    □

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    is-set

------------------------------------------------------------------------
-- Subsets of subsets

-- Subsets.

infix 4 _⊆_

_⊆_ : {A : Type a} → Finite-subset-of A → Finite-subset-of A → Type a
x ⊆ y = ∀ z → z ∈ x → z ∈ y

-- _⊆_ is pointwise propositional.

⊆-propositional : Is-proposition (x ⊆ y)
⊆-propositional =
  Π-closure ext 1 λ _ →
  Π-closure ext 1 λ _ →
  ∈-propositional

-- _⊆_ is pointwise very stable.

Very-stable-⊆ : Very-stable (x ⊆ y)
Very-stable-⊆ =
  EC.Very-stable-Π ext λ _ →
  EC.Very-stable-Π ext λ _ →
  Very-stable-∈

-- The subset property can be expressed using _∪_ and _≡_ (in erased
-- contexts).

@0 ⊆≃∪≡ : ∀ x → (x ⊆ y) ≃ (x ∪ y ≡ y)
⊆≃∪≡ {y = y} x =
  Eq.⇔→≃
    (Π-closure ext 1 λ _ →
     Π-closure ext 1 λ _ →
     ∈-propositional)
    is-set
    (elim-prop e x)
    (λ p z →
       z ∈ x      →⟨ ∈→∈∪ˡ ⟩
       z ∈ x ∪ y  →⟨ ≡⇒↝ _ (cong (z ∈_) p) ⟩□
       z ∈ y      □)
  where
  e : Elim-prop (λ x → x ⊆ y → x ∪ y ≡ y)
  e .[]ʳ _ =
    [] ∪ y  ≡⟨⟩
    y       ∎

  e .∷ʳ {y = z} x hyp x∷z⊆y =
    x ∷ z ∪ y  ≡⟨ cong (x ∷_) (hyp (λ _ → x∷z⊆y _ ∘ ∈→∈∷)) ⟩
    x ∷ y      ≡⟨ ∈→∷≡ (x∷z⊆y x (≡→∈∷ (refl _))) ⟩∎
    y          ∎

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    is-set

-- A form of extensionality that holds in erased contexts.

@0 extensionality : (x ≡ y) ≃ (∀ z → z ∈ x ⇔ z ∈ y)
extensionality {x = x} {y = y} =
  Eq.⇔→≃
    is-set
    (Π-closure ext 1 λ _ →
     ⇔-closure ext 1
       ∈-propositional
       ∈-propositional)
    (λ x≡y z → ≡⇒↝ _ (cong (z ∈_) x≡y))
    ((∀ z → z ∈ x ⇔ z ∈ y)  →⟨ (λ p → _⇔_.to ∘ p , _⇔_.from ∘ p) ⟩
     x ⊆ y × y ⊆ x          ↔⟨ ⊆≃∪≡ x ×-cong ⊆≃∪≡ y ⟩
     x ∪ y ≡ y × y ∪ x ≡ x  →⟨ (λ (p , q) → trans (sym q) (trans (comm y) p)) ⟩□
     x ≡ y                  □)

-- Another way to characterise equality (in erased contexts).

@0 ≡≃⊆×⊇ : (x ≡ y) ≃ (x ⊆ y × y ⊆ x)
≡≃⊆×⊇ {x = x} {y = y} =
  x ≡ y                  ↝⟨ extensionality ⟩
  (∀ z → z ∈ x ⇔ z ∈ y)  ↝⟨ Eq.⇔→≃
                              (Π-closure ext 1 λ _ →
                               ⇔-closure ext 1
                                 ∈-propositional
                                 ∈-propositional)
                              (×-closure 1 ⊆-propositional ⊆-propositional)
                              (λ hyp → _⇔_.to ∘ hyp , _⇔_.from ∘ hyp)
                              (λ (x⊆y , y⊆x) z → record { to = x⊆y z ; from = y⊆x z }) ⟩□
  x ⊆ y × y ⊆ x          □

-- _⊆_ is a partial order (in erased contexts).

⊆-refl : x ⊆ x
⊆-refl _ = id

⊆-trans : x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans x⊆y y⊆z _ = y⊆z _ ∘ x⊆y _

@0 ⊆-antisymmetric : x ⊆ y → y ⊆ x → x ≡ y
⊆-antisymmetric = curry (_≃_.from ≡≃⊆×⊇)

-- If truncated equality is decidable (with erased proofs), then _⊆_
-- is decidable.

subset? :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (x y : Finite-subset-of A) → Dec (x ⊆ y)
subset? equal? x y = elim-prop r x
  where
  r : Elim-prop (λ x → Dec (x ⊆ y))
  r .[]ʳ = yes λ z →
    z ∈ []  ↔⟨ ∈[]≃ ⟩
    ⊥       →⟨ ⊥-elim ⟩□
    z ∈ y   □

  r .∷ʳ {y = x} z =
    Dec (x ⊆ y)                          →⟨ member? equal? z y ,_ ⟩
    Dec (z ∈ y) × Dec (x ⊆ y)            →⟨ uncurry
                                              P.[ (λ z∈y → Dec-map (
        x ⊆ y                                        ↝⟨ record
                                                          { to = λ x⊆y u →
                                                                   P.[ (λ u≡z → subst (_∈ y) (sym u≡z) z∈y)
                                                                     , x⊆y u
                                                                     ]
                                                          ; from = λ hyp u → hyp u ∘ inj₂
                                                          } ⟩
        (∀ u → u ≡ z ⊎ u ∈ x → u ∈ y)                ↔⟨ (∀-cong ext λ _ → inverse $
                                                         Trunc.universal-property ∈-propositional) ⟩
        (∀ u → u ≡ z ∥⊎∥ u ∈ x → u ∈ y)              ↝⟨ (∀-cong _ λ _ →
                                                         EC.Very-stable→Stable 0
                                                           (EC.Very-stable-↝ ext
                                                              (EC.Very-stable-Π ext λ _ → Very-stable-∈)
                                                              (EC.Very-stable-Π ext λ _ → Very-stable-∈))
                                                           [ →-cong₁ _ (inverse ∈∷≃) ]) ⟩
        (∀ u → u ∈ z ∷ x → u ∈ y)                    ↔⟨⟩
        z ∷ x ⊆ y                                    □))
                                                , (λ z∉y _ → no (
        z ∷ x ⊆ y                                    →⟨ (λ z∷x⊆y → z∷x⊆y z (≡→∈∷ (refl _))) ⟩
        z ∈ y                                        →⟨ z∉y ⟩□
        ⊥                                            □))
                                                ] ⟩□
    Dec (z ∷ x ⊆ y)                      □

  r .is-propositionʳ _ =
    Dec-closure-propositional ext ⊆-propositional

-- If truncated equality is decidable (with erased proofs), then _≡_
-- is also decidable (with erased proofs).

equal?ᴱ :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (x y : Finite-subset-of A) → Dec-Erased (x ≡ y)
equal?ᴱ eq? x y =             $⟨ subset? eq? x y , subset? eq? y x ⟩
  Dec (x ⊆ y) × Dec (y ⊆ x)   →⟨ uncurry Dec-× ⟩
  Dec (x ⊆ y × y ⊆ x)         →⟨ EC.Dec→Dec-Erased ⟩
  Dec-Erased (x ⊆ y × y ⊆ x)  →⟨ EC.Dec-Erased-map (from-equivalence $ inverse ≡≃⊆×⊇) ⟩□
  Dec-Erased (x ≡ y)          □

-- If truncated equality is decidable, then _≡_ is decidable (in
-- erased contexts).

@0 equal? :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x y : Finite-subset-of A) → Dec (x ≡ y)
equal? {A = A} =
  ((x y : A) → Dec ∥ x ≡ y ∥)                        →⟨ (λ hyp x y → EC.Dec→Dec-Erased (hyp x y)) ⟩
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥)                 →⟨ equal?ᴱ ⟩
  ((x y : Finite-subset-of A) → Dec-Erased (x ≡ y))  →⟨ (λ hyp x y → _≃_.to EC.Dec-Erased≃Dec (hyp x y)) ⟩□
  ((x y : Finite-subset-of A) → Dec (x ≡ y))         □

------------------------------------------------------------------------
-- Some properties related to map-Maybe and filter

-- A lemma characterising map-Maybe (in erased contexts).

@0 ∈map-Maybe≃ :
  (x ∈ map-Maybe f y) ≃ ∥ (∃ λ z → z ∈ y × f z ≡ just x) ∥
∈map-Maybe≃ {x = x} {f = f} = elim-prop e _
  where
  e : Elim-prop (λ y → (x ∈ map-Maybe f y) ≃
                       ∥ (∃ λ z → z ∈ y × f z ≡ just x) ∥)
  e .[]ʳ =
    x ∈ map-Maybe f []                   ↝⟨ ∈[]≃ ⟩
    ⊥                                    ↔⟨ inverse $ Trunc.∥∥↔ ⊥-propositional ⟩
    ∥ ⊥ ∥                                ↔⟨ Trunc.∥∥-cong (inverse (×-right-zero {ℓ₁ = lzero} F.∘
                                                                    ∃-cong (λ _ → ×-left-zero))) ⟩
    ∥ (∃ λ z → ⊥ × f z ≡ just x) ∥       ↝⟨ Trunc.∥∥-cong (∃-cong λ _ → inverse ∈[]≃ ×-cong F.id) ⟩□
    ∥ (∃ λ z → z ∈ [] × f z ≡ just x) ∥  □

  e .∷ʳ {y = y} z hyp =
    (x ∈ map-Maybe f (z ∷ y))                                          ↝⟨ lemma _ _ ⟩
    f z ≡ just x ∥⊎∥ (x ∈ map-Maybe f y)                               ↝⟨ from-isomorphism (inverse Trunc.truncate-right-∥⊎∥) F.∘
                                                                          (F.id Trunc.∥⊎∥-cong hyp) ⟩
    f z ≡ just x ∥⊎∥ (∃ λ u → u ∈ y × f u ≡ just x)                    ↔⟨ inverse $
                                                                          drop-⊤-left-Σ (_⇔_.to contractible⇔↔⊤ $ singleton-contractible _) F.∘
                                                                          Σ-assoc Trunc.∥⊎∥-cong F.id ⟩
    (∃ λ u → u ≡ z × f u ≡ just x) ∥⊎∥ (∃ λ u → u ∈ y × f u ≡ just x)  ↔⟨ Trunc.∥∥-cong $ inverse ∃-⊎-distrib-left ⟩
    ∥ (∃ λ u → u ≡ z × f u ≡ just x ⊎ u ∈ y × f u ≡ just x) ∥          ↔⟨ Trunc.∥∥-cong (∃-cong λ _ → inverse ∃-⊎-distrib-right) ⟩
    ∥ (∃ λ u → (u ≡ z ⊎ u ∈ y) × f u ≡ just x) ∥                       ↔⟨ inverse $
                                                                          Trunc.flatten′
                                                                            (λ F → (∃ λ u → F (u ≡ z ⊎ u ∈ y) × f u ≡ just x))
                                                                            (λ f → Σ-map id (Σ-map f id))
                                                                            (λ (u , p , q) → Trunc.∥∥-map (λ p → u , p , q) p) ⟩
    ∥ (∃ λ u → (u ≡ z ∥⊎∥ u ∈ y) × f u ≡ just x) ∥                     ↝⟨ Trunc.∥∥-cong (∃-cong λ _ → ×-cong₁ λ _ → inverse ∈∷≃) ⟩□
    ∥ (∃ λ u → u ∈ z ∷ y × f u ≡ just x) ∥                             □
    where
    lemma :
      ∀ m y →
      (x ∈ maybe {B = const _} _∷_ id m y) ≃ (m ≡ just x ∥⊎∥ x ∈ y)
    lemma nothing y =
      x ∈ y                         ↔⟨ inverse $ Trunc.drop-⊥-left-∥⊎∥ ∈-propositional ⊎.inj₁≢inj₂ ⟩□
      (nothing ≡ just x ∥⊎∥ x ∈ y)  □
    lemma (just z) y =
      x ∈ z ∷ y                  ↝⟨ ∈∷≃ ⟩
      x ≡ z ∥⊎∥ x ∈ y            ↔⟨ (Bijection.≡↔inj₂≡inj₂ F.∘ ≡-comm) Trunc.∥⊎∥-cong F.id ⟩□
      just z ≡ just x ∥⊎∥ x ∈ y  □

  e .is-propositionʳ y =
    Eq.left-closure ext 0 ∈-propositional

-- A lemma characterising map (in erased contexts).

@0 ∈map≃ : (x ∈ map f y) ≃ ∥ (∃ λ z → z ∈ y × f z ≡ x) ∥
∈map≃ {x = x} {f = f} {y = y} =
  x ∈ map f y                                ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) $ map≡map-Maybe-just y ⟩
  x ∈ map-Maybe (just ∘ f) y                 ↝⟨ ∈map-Maybe≃ ⟩
  ∥ (∃ λ z → z ∈ y × just (f z) ≡ just x) ∥  ↔⟨ Trunc.∥∥-cong (∃-cong λ _ → ∃-cong λ _ → inverse Bijection.≡↔inj₂≡inj₂) ⟩□
  ∥ (∃ λ z → z ∈ y × f z ≡ x) ∥              □

-- Some consequences of the characterisation of map.

∈→∈map :
  {f : A → B} →
  x ∈ y → f x ∈ map f y
∈→∈map {x = x} {y = y} {f = f} =
  EC.Very-stable→Stable 0
    (EC.Very-stable-Π ext λ _ → Very-stable-∈)
    [ x ∈ y                            →⟨ (λ x∈y → ∣ x , x∈y , refl _ ∣) ⟩
      ∥ (∃ λ z → z ∈ y × f z ≡ f x) ∥  ↔⟨ inverse ∈map≃ ⟩□
      f x ∈ map f y                    □
    ]

Injective→∈map≃ :
  {f : A → B} →
  Injective f →
  (f x ∈ map f y) ≃ (x ∈ y)
Injective→∈map≃ {x = x} {y = y} {f = f} inj =
  EC.Very-stable→Stable 0
    (EC.Very-stable-↝ ext Very-stable-∈ Very-stable-∈)
    [ f x ∈ map f y                    ↝⟨ ∈map≃ ⟩
      ∥ (∃ λ z → z ∈ y × f z ≡ f x) ∥  ↝⟨ (Trunc.∥∥-cong-⇔ $ ∃-cong λ _ → ∃-cong λ _ →
                                           record { to = inj; from = cong f }) ⟩
      ∥ (∃ λ z → z ∈ y × z ≡ x) ∥      ↔⟨ Trunc.∥∥-cong $ inverse $ ∃-intro _ _ ⟩
      ∥ x ∈ y ∥                        ↔⟨ Trunc.∥∥↔ ∈-propositional ⟩□
      x ∈ y                            □
    ]

-- A lemma characterising filter.

∈filter≃ :
  ∀ p → (x ∈ filter p y) ≃ (T (p x) × x ∈ y)
∈filter≃ {x = x} {y = y} p =
  EC.Very-stable→Stable 0
    (EC.Very-stable-↝ ext
       Very-stable-∈
       (EC.Very-stable-× (EC.Very-stable-T (p x)) Very-stable-∈))
    [ x ∈ map-Maybe (λ x → if p x then just x else nothing) y         ↝⟨ ∈map-Maybe≃ ⟩
      ∥ (∃ λ z → z ∈ y × if p z then just z else nothing ≡ just x) ∥  ↝⟨ (Trunc.∥∥-cong $ ∃-cong λ _ → ∃-cong λ _ → lemma _ (refl _)) ⟩
      ∥ (∃ λ z → z ∈ y × T (p z) × z ≡ x) ∥                           ↔⟨ (Trunc.∥∥-cong $ ∃-cong λ _ →
                                                                          (×-cong₁ λ z≡x → ≡⇒↝ _ $ cong (λ z → z ∈ y × T (p z)) z≡x) F.∘
                                                                          Σ-assoc) ⟩
      ∥ (∃ λ z → (x ∈ y × T (p x)) × z ≡ x) ∥                         ↔⟨ inverse Σ-assoc F.∘
                                                                         (×-cong₁ λ _ →
                                                                          ×-comm F.∘
                                                                          Trunc.∥∥↔ (×-closure 1 ∈-propositional (T-propositional (p x)))) F.∘
                                                                         inverse Trunc.∥∥×∥∥↔∥×∥ F.∘
                                                                         Trunc.∥∥-cong ∃-comm ⟩
      T (p x) × x ∈ y × ∥ (∃ λ z → z ≡ x) ∥                           ↔⟨ (∃-cong λ _ → drop-⊤-right λ _ →
                                                                          _⇔_.to contractible⇔↔⊤ (singleton-contractible _) F.∘
                                                                          Trunc.∥∥↔ (H-level.mono₁ 0 $ singleton-contractible _)) ⟩□
      T (p x) × x ∈ y                                                 □
    ]
  where
  lemma :
    ∀ b → p z ≡ b →
    (if b then just z else nothing ≡ just x) ≃
    (T b × z ≡ x)
  lemma {z = z} true eq =
    just z ≡ just x  ↔⟨ inverse Bijection.≡↔inj₂≡inj₂ ⟩
    z ≡ x            ↔⟨ inverse ×-left-identity ⟩□
    ⊤ × z ≡ x        □
  lemma {z = z} false eq =
    nothing ≡ just x  ↔⟨ Bijection.≡↔⊎ ⟩
    ⊥                 ↔⟨ inverse ×-left-zero ⟩□
    ⊥ × z ≡ x         □

-- The result of filtering is a subset of the original subset.

filter⊆ : ∀ p → filter p x ⊆ x
filter⊆ {x = x} p z =
  z ∈ filter p x   ↔⟨ ∈filter≃ p ⟩
  T (p z) × z ∈ x  →⟨ proj₂ ⟩□
  z ∈ x            □

------------------------------------------------------------------------
-- The functions minus and delete

-- If erased truncated equality is decidable, then one subset can be
-- removed from another.

minus :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  Finite-subset-of A → Finite-subset-of A → Finite-subset-of A
minus _≟_ x y =
  filter (λ z → if member? _≟_ z y then false else true) x

-- A lemma characterising minus.

∈minus≃ : (x ∈ minus _≟_ y z) ≃ (x ∈ y × x ∉ z)
∈minus≃ {x = x} {_≟_ = _≟_} {y = y} {z = z} =
  x ∈ minus _≟_ y z                                    ↝⟨ ∈filter≃ (λ _ → if member? _ _ z then _ else _) ⟩
  T (if member? _≟_ x z then false else true) × x ∈ y  ↔⟨ lemma (member? _≟_ x z) ×-cong F.id ⟩
  x ∉ z × x ∈ y                                        ↔⟨ ×-comm ⟩□
  x ∈ y × x ∉ z                                        □
  where
  lemma :
    (d : Dec A) →
    T (if d then false else true) ↔ ¬ A
  lemma {A = A} d@(yes a) =
    T (if d then false else true)  ↔⟨⟩
    ⊥                              ↝⟨ Bijection.⊥↔uninhabited (_$ a) ⟩□
    ¬ A                            □
  lemma {A = A} d@(no ¬a) =
    T (if d then false else true) ↔⟨⟩
    ⊤                             ↝⟨ inverse $
                                     _⇔_.to contractible⇔↔⊤ $
                                     propositional⇒inhabited⇒contractible
                                       (¬-propositional ext)
                                       ¬a ⟩□
    ¬ A                           □

-- The result of minus is a subset of the original subset.

minus⊆ : ∀ y → minus _≟_ x y ⊆ x
minus⊆ y =
  filter⊆ (λ _ → if member? _ _ y then _ else _)

-- Minus commutes with itself (in a certain sense).

minus-comm :
  ∀ x y z →
  minus _≟_ (minus _≟_ x y) z ≡ minus _≟_ (minus _≟_ x z) y
minus-comm x y z =
  filter-comm
    (λ _ → if member? _ _ z then _ else _)
    (λ _ → if member? _ _ y then _ else _)
    x

-- Minus commutes with union (in a certain sense).

minus-∪ :
  ∀ x z →
  minus _≟_ (x ∪ y) z ≡ minus _≟_ x z ∪ minus _≟_ y z
minus-∪ x z = filter-∪ (λ _ → if member? _ _ z then _ else _) x

-- A lemma relating minus, _⊆_ and _∪_.

minus⊆≃ : ∀ y → (minus _≟_ x y ⊆ z) ≃ (x ⊆ y ∪ z)
minus⊆≃ {_≟_ = _≟_} {x = x} {z = z} y =
  EC.Very-stable→Stable 0
    (EC.Very-stable-↝ ext Very-stable-⊆ Very-stable-⊆)
    [ Eq.⇔→≃
        ⊆-propositional
        ⊆-propositional
        (λ x-y⊆z u →
           u ∈ x                        →⟨ (λ u∈x →
                                              case member? _≟_ u y of
                                                P.[ Trunc.∣inj₁∣ , Trunc.∣inj₂∣ ∘ (u∈x ,_) ]) ⟩
           u ∈ y ∥⊎∥ (u ∈ x × u ∉ y)    ↔⟨ F.id Trunc.∥⊎∥-cong inverse ∈minus≃ ⟩
           u ∈ y ∥⊎∥ u ∈ minus _≟_ x y  →⟨ id Trunc.∥⊎∥-cong x-y⊆z u ⟩
           u ∈ y ∥⊎∥ u ∈ z              ↔⟨ inverse ∈∪≃ ⟩□
           u ∈ y ∪ z                    □)
        (λ x⊆y∪z u →
           u ∈ minus _≟_ x y          ↔⟨ ∈minus≃ ⟩
           u ∈ x × u ∉ y              →⟨ Σ-map (x⊆y∪z _) id ⟩
           u ∈ y ∪ z × u ∉ y          ↔⟨ ∈∪≃ ×-cong F.id ⟩
           (u ∈ y ∥⊎∥ u ∈ z) × u ∉ y  ↔⟨ (×-cong₁ λ u∉y → Trunc.drop-⊥-left-∥⊎∥ ∈-propositional u∉y) ⟩
           u ∈ z × u ∉ y              →⟨ proj₁ ⟩□
           u ∈ z                      □)
    ]

-- If erased truncated equality is decidable, then elements can be
-- removed from a subset.

delete :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  A → Finite-subset-of A → Finite-subset-of A
delete _≟_ x y = minus _≟_ y (singleton x)

-- A lemma characterising delete.

∈delete≃ : ∀ _≟_ → (x ∈ delete _≟_ y z) ≃ (x ≢ y × x ∈ z)
∈delete≃ {x = x} {y = y} {z = z} _≟_ =
  EC.Very-stable→Stable 0
    (EC.Very-stable-↝ ext
       Very-stable-∈
       (EC.Very-stable-× (EC.Very-stable-¬ ext) Very-stable-∈))
    [ x ∈ delete _≟_ y z       ↝⟨ ∈minus≃ {_≟_ = _≟_} ⟩
      x ∈ z × x ∉ singleton y  ↝⟨ F.id ×-cong →-cong₁ ext ∈singleton≃ ⟩
      x ∈ z × ¬ ∥ x ≡ y ∥      ↔⟨ F.id ×-cong Trunc.¬∥∥↔¬ ⟩
      x ∈ z × x ≢ y            ↔⟨ ×-comm ⟩□
      x ≢ y × x ∈ z            □
    ]

-- A deleted element is no longer a member of the set.

∉delete : ∀ _≟_ y → x ∉ delete _≟_ x y
∉delete {x = x} _≟_ y =
  x ∈ delete _≟_ x y  ↔⟨ ∈delete≃ _≟_ ⟩
  x ≢ x × x ∈ y       →⟨ (_$ refl _) ∘ proj₁ ⟩□
  ⊥                   □

-- Deletion commutes with itself (in a certain sense).

delete-comm :
  ∀ _≟_ z →
  delete _≟_ x (delete _≟_ y z) ≡ delete _≟_ y (delete _≟_ x z)
delete-comm _≟_ z =
  minus-comm {_≟_ = _≟_} z (singleton _) (singleton _)

-- Deletion commutes with union.

delete-∪ :
  ∀ _≟_ y →
  delete _≟_ x (y ∪ z) ≡ delete _≟_ x y ∪ delete _≟_ x z
delete-∪ _≟_ y = minus-∪ {_≟_ = _≟_} y (singleton _)

-- A lemma relating delete, _⊆_ and _∷_.

delete⊆≃ :
  (_≟_ : (x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (delete _≟_ x y ⊆ z) ≃ (y ⊆ x ∷ z)
delete⊆≃ _≟_ = minus⊆≃ {_≟_ = _≟_} (singleton _)

------------------------------------------------------------------------
-- Some preservation lemmas for _⊆_

-- Various operations preserve _⊆_.

∷-cong-⊆ : y ⊆ z → x ∷ y ⊆ x ∷ z
∷-cong-⊆ {y = y} {z = z} {x = x} y⊆z =
  EC.Very-stable→Stable 0 Very-stable-⊆
    [ (λ u →
         u ∈ x ∷ y        ↔⟨ ∈∷≃ ⟩
         u ≡ x ∥⊎∥ u ∈ y  →⟨ id Trunc.∥⊎∥-cong y⊆z _ ⟩
         u ≡ x ∥⊎∥ u ∈ z  ↔⟨ inverse ∈∷≃ ⟩□
         u ∈ x ∷ z        □)
    ]

∪-cong-⊆ : x₁ ⊆ x₂ → y₁ ⊆ y₂ → x₁ ∪ y₁ ⊆ x₂ ∪ y₂
∪-cong-⊆ {x₁ = x₁} {x₂ = x₂} {y₁ = y₁} {y₂ = y₂} x₁⊆x₂ y₁⊆y₂ =
  EC.Very-stable→Stable 0 Very-stable-⊆
    [ (λ z →
         z ∈ x₁ ∪ y₁        ↔⟨ ∈∪≃ ⟩
         z ∈ x₁ ∥⊎∥ z ∈ y₁  →⟨ x₁⊆x₂ _ Trunc.∥⊎∥-cong y₁⊆y₂ _ ⟩
         z ∈ x₂ ∥⊎∥ z ∈ y₂  ↔⟨ inverse ∈∪≃ ⟩□
         z ∈ x₂ ∪ y₂        □)
    ]

filter-cong-⊆ :
  (∀ z → T (p z) → T (q z)) →
  x ⊆ y → filter p x ⊆ filter q y
filter-cong-⊆ {p = p} {q = q} {x = x} {y = y} p⇒q x⊆y z =
  z ∈ filter p x   ↔⟨ ∈filter≃ p ⟩
  T (p z) × z ∈ x  →⟨ Σ-map (p⇒q _) (x⊆y _) ⟩
  T (q z) × z ∈ y  ↔⟨ inverse $ ∈filter≃ q ⟩□
  z ∈ filter q y   □

minus-cong-⊆ : x₁ ⊆ x₂ → y₂ ⊆ y₁ → minus _≟_ x₁ y₁ ⊆ minus _≟_ x₂ y₂
minus-cong-⊆ {x₁ = x₁} {x₂ = x₂} {y₂ = y₂} {y₁ = y₁} {_≟_ = _≟_}
             x₁⊆x₂ y₂⊆y₁ z =
  z ∈ minus _≟_ x₁ y₁  ↔⟨ ∈minus≃ ⟩
  z ∈ x₁ × z ∉ y₁      →⟨ Σ-map (x₁⊆x₂ _) (_∘ y₂⊆y₁ _) ⟩
  z ∈ x₂ × z ∉ y₂      ↔⟨ inverse ∈minus≃ ⟩□
  z ∈ minus _≟_ x₂ y₂  □

delete-cong-⊆ : ∀ _≟_ → y ⊆ z → delete _≟_ x y ⊆ delete _≟_ x z
delete-cong-⊆ _≟_ y⊆z =
  minus-cong-⊆ {_≟_ = _≟_} y⊆z (⊆-refl {x = singleton _})

------------------------------------------------------------------------
-- Size

private

  -- This definition is used to define ∣_∣≡ and ∣∣≡-propositional
  -- below.
  --
  -- This definition is not taken from "Finite Sets in Homotopy Type
  -- Theory", but it is based on the size function in that paper.

  @0 Size : {A : Type a} → Finite-subset-of A → ℕ → Proposition a
  Size {a = a} {A = A} = rec r
    where

    mutual

      -- The size of x ∷ y is equal to the size of y if x is a member
      -- of y, and otherwise it is equal to the successor of the size
      -- of y.

      Cons′ :
        A → Finite-subset-of A →
        (ℕ → Proposition a) → (ℕ → Type a)
      Cons′ x y ∣y∣≡ n =
        x ∈ y × Erased (proj₁ (∣y∣≡ n))
          ⊎
        Cons″ x y ∣y∣≡ n

      Cons″ :
        A → Finite-subset-of A →
        (ℕ → Proposition a) → (ℕ → Type a)
      Cons″ x y ∣y∣≡ zero    = ⊥
      Cons″ x y ∣y∣≡ (suc n) = x ∉ y × Erased (proj₁ (∣y∣≡ n))

    Cons′-propositional :
      ∀ Hyp n → Is-proposition (Cons′ x y Hyp n)
    Cons′-propositional Hyp zero =
      ⊎-closure-propositional
        (λ _ ())
        (×-closure 1
           ∈-propositional
           (EC.H-level-Erased 1 (proj₂ (Hyp 0))))
        ⊥-propositional
    Cons′-propositional Hyp (suc n) =
      ⊎-closure-propositional
        (λ (x∈y , _) (x∉y , _) → x∉y x∈y)
        (×-closure 1
           ∈-propositional
           (EC.H-level-Erased 1 (proj₂ (Hyp (suc n)))))
        (×-closure 1
           (¬-propositional ext)
           (EC.H-level-Erased 1 (proj₂ (Hyp n))))

    Cons :
      A → Finite-subset-of A →
      (ℕ → Proposition a) → (ℕ → Proposition a)
    Cons x y Hyp n =
        Cons′ x y Hyp n
      , Cons′-propositional _ _

    drop-lemma :
      Cons′ x (x ∷ y) (Cons x y H) n ≃ Cons′ x y H n
    drop-lemma {x = x} {y = y} {H = H} {n = n} =
      Cons′ x (x ∷ y) (Cons x y H) n            ↔⟨⟩
      x ∈ x ∷ y × Erased (Cons′ x y H n) ⊎ C n  ↔⟨ F.id ×-cong EC.erased EC.Erased↔ ⊎-cong F.id ⟩
      x ∈ x ∷ y × Cons′ x y H n ⊎ C n           ↔⟨ drop-⊥-right (C↔⊥ n) ⟩
      x ∈ x ∷ y × Cons′ x y H n                 ↔⟨ drop-⊤-left-× (λ _ → x∈x∷y↔⊤) ⟩
      Cons′ x y H n                             □
      where
      C = Cons″ x (x ∷ y) (Cons x y H)

      x∈x∷y↔⊤ : x ∈ x ∷ y ↔ ⊤
      x∈x∷y↔⊤ =
        x ∈ x ∷ y        ↔⟨ ∈∷≃ ⟩
        x ≡ x ∥⊎∥ x ∈ y  ↝⟨ Trunc.inhabited⇒∥∥↔⊤ ∣ inj₁ (refl _) ∣ ⟩□
        ⊤                □

      C↔⊥ : ∀ n → C n ↔ ⊥
      C↔⊥ zero    = ⊥↔⊥
      C↔⊥ (suc n) =
        x ∉ x ∷ y × Erased (Cons′ x y H n)  ↝⟨ F.id ×-cong EC.erased EC.Erased↔ ⟩
        x ∉ x ∷ y × Cons′ x y H n           ↝⟨ →-cong ext x∈x∷y↔⊤ F.id ×-cong F.id ⟩
        ¬ ⊤ × Cons′ x y H n                 ↝⟨ inverse (Bijection.⊥↔uninhabited (_$ _)) ×-cong F.id ⟩
        ⊥₀ × Cons′ x y H n                  ↝⟨ ×-left-zero ⟩□
        ⊥                                   □

    swap-lemma′ :
      ∀ n →
      x ∈ y ∷ z × Erased (Cons′ y z H n) ⊎
      Cons″ x (y ∷ z) (Cons y z H) n →
      y ∈ x ∷ z × Erased (Cons′ x z H n) ⊎
      Cons″ y (x ∷ z) (Cons x z H) n
    swap-lemma′ {x = x} {y = y} {z = z} {H = H} = λ @0 where
      n (inj₁ (x∈y∷z , [ inj₁ (y∈z , p) ])) →
        inj₁ ( ∈→∈∷ y∈z
             , [ inj₁
                   ( (                 $⟨ x∈y∷z ⟩
                      x ∈ y ∷ z        ↔⟨ ∈∷≃ ⟩
                      x ≡ y ∥⊎∥ x ∈ z  →⟨ Trunc.∥∥-map P.[ (flip (subst (_∈ z)) y∈z ∘ sym) , id ] ⟩
                      ∥ x ∈ z ∥        ↔⟨ Trunc.∥∥↔ ∈-propositional ⟩□
                      x ∈ z            □)
                   , p
                   )
               ]
             )

      (suc n) (inj₁ (x∈y∷z , [ inj₂ (y∉z , p) ])) →
        Trunc.rec (Cons′-propositional (Cons x z H) _)
          P.[ (λ x≡y →
                inj₁ ( ≡→∈∷ (sym x≡y)
                     , [ inj₂ ( (x ∈ z  →⟨ subst (_∈ z) x≡y ⟩
                                 y ∈ z  →⟨ y∉z ⟩□
                                 ⊥      □)
                              , p
                              )
                       ]
                     ))
            , (λ x∈z →
                 inj₂ ( (y ∈ x ∷ z        ↔⟨ ∈∷≃ ⟩
                         y ≡ x ∥⊎∥ y ∈ z  →⟨ Trunc.∥∥-map P.[ flip (subst (_∈ z)) x∈z ∘ sym , id ] ⟩
                         ∥ y ∈ z ∥        →⟨ Trunc.∥∥-map y∉z ⟩
                         ∥ ⊥ ∥            ↔⟨ Trunc.∥∥↔ ⊥-propositional ⟩□
                         ⊥                □)
                      , [ inj₁ (x∈z , p) ]
                      ))
            ]
          (_≃_.to ∈∷≃ x∈y∷z)

      (suc n) (inj₂ (x∉y∷z , [ inj₁ (y∈z , p) ])) →
        inj₁ ( ∈→∈∷ y∈z
             , [ inj₂ ( (x ∈ z      →⟨ ∈→∈∷ ⟩
                         x ∈ y ∷ z  →⟨ x∉y∷z ⟩□
                         ⊥          □)
                      , p
                      )
               ]
             )

      (suc (suc n)) (inj₂ (x∉y∷z , [ inj₂ (y∉z , p) ])) →
        inj₂ ( (y ∈ x ∷ z            ↔⟨ ∈∷≃ ⟩
                y ≡ x ∥⊎∥ y ∈ z      →⟨ ≡→∈∷ ∘ sym Trunc.∥⊎∥-cong id ⟩
                x ∈ y ∷ z ∥⊎∥ y ∈ z  →⟨ Trunc.∥∥-map P.[ x∉y∷z , y∉z ] ⟩
                ∥ ⊥ ∥                ↔⟨ Trunc.∥∥↔ ⊥-propositional ⟩□
                ⊥                    □)
             , [ inj₂ ( (x ∈ z      →⟨ ∈→∈∷ ⟩
                         x ∈ y ∷ z  →⟨ x∉y∷z ⟩□
                         ⊥          □)
                      , p
                      )
               ]
             )

    swap-lemma :
      Cons′ x (y ∷ z) (Cons y z H) n ≃
      Cons′ y (x ∷ z) (Cons x z H) n
    swap-lemma {x = x} {y = y} {z = z} {H = H} {n = n} =
      Eq.⇔→≃
        (Cons′-propositional _ _)
        (Cons′-propositional _ _)
        (swap-lemma′ _)
        (swap-lemma′ _)

    r : Rec A (ℕ → Proposition a)
    r .[]ʳ n = ↑ _ (n ≡ 0) , ↑-closure 1 ℕ-set

    r .∷ʳ = Cons

    r .dropʳ x y Hyp = ⟨ext⟩ λ _ →
      _↔_.to (ignore-propositional-component
             (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ drop-lemma

    r .swapʳ x y z Hyp = ⟨ext⟩ λ _ →
      _↔_.to (ignore-propositional-component
             (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ swap-lemma

    r .is-setʳ =
      Π-closure ext 2 λ _ →
      Univ.∃-H-level-H-level-1+ ext univ 1

-- Size.

infix 4 ∣_∣≡_

∣_∣≡_ : {A : Type a} → Finite-subset-of A → ℕ → Type a
∣ x ∣≡ n = Erased (proj₁ (Size x n))

-- The size predicate is propositional.

∣∣≡-propositional :
  (x : Finite-subset-of A) → Is-proposition (∣ x ∣≡ n)
∣∣≡-propositional {n = n} x =                 $⟨ [ proj₂ (Size x n) ] ⟩
  Erased (Is-proposition (proj₁ (Size x n)))  →⟨ EC.Erased-H-level↔H-level 1 _ ⟩
  Is-proposition (Erased (proj₁ (Size x n)))  ↔⟨⟩
  Is-proposition (∣ x ∣≡ n)                   □

-- The size predicate is very stable.

Very-stable-∣∣≡ : (x : Finite-subset-of A) → Very-stable (∣ x ∣≡ n)
Very-stable-∣∣≡ _ = EC.Very-stable-Erased

-- Unit tests documenting the computational behaviour of ∣_∣≡_.

_ : (∣ [] {A = A} ∣≡ n) ≡ Erased (↑ _ (n ≡ 0))
_ = refl _

_ : ∀ {A : Type a} {x : A} {y} →
    (∣ x ∷ y ∣≡ zero) ≡ Erased (x ∈ y × (∣ y ∣≡ zero) ⊎ ⊥)
_ = refl _

_ : (∣ x ∷ y ∣≡ suc n) ≡
    Erased (x ∈ y × ∣ y ∣≡ suc n ⊎ x ∉ y × ∣ y ∣≡ n)
_ = refl _

-- The size predicate is functional.

∣∣≡-functional :
  (x : Finite-subset-of A) → ∣ x ∣≡ m → ∣ x ∣≡ n → m ≡ n
∣∣≡-functional x ∣x∣≡m ∣x∣≡n =
  EC.Very-stable→Stable 1
    (EC.Decidable-equality→Very-stable-≡ Nat._≟_)
    _ _
    [ elim-prop e x _ _ ∣x∣≡m ∣x∣≡n ]
  where
  @0 e : Elim-prop (λ x → ∀ m n → ∣ x ∣≡ m → ∣ x ∣≡ n → m ≡ n)
  e .[]ʳ m n [ lift m≡0 ] [ lift n≡0 ] =
    m  ≡⟨ m≡0 ⟩
    0  ≡⟨ sym n≡0 ⟩∎
    n  ∎

  e .∷ʳ {y = y} x hyp = λ @0 where
    m n [ inj₁ (x∈y , ∣y∣≡m) ] [ inj₁ (x∈y′ , ∣y∣≡n) ] →
      hyp m n ∣y∣≡m ∣y∣≡n

    (suc m) (suc n) [ inj₂ (x∉y , ∣y∣≡m) ] [ inj₂ (x∉y′ , ∣y∣≡n) ] →
      cong suc (hyp m n ∣y∣≡m ∣y∣≡n)

    _ (suc _) [ inj₁ (x∈y , _) ] [ inj₂ (x∉y , _) ] → ⊥-elim (x∉y x∈y)
    (suc _) _ [ inj₂ (x∉y , _) ] [ inj₁ (x∈y , _) ] → ⊥-elim (x∉y x∈y)

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    ℕ-set

-- If truncated equality is decidable (with erased proofs), then one
-- can compute the size of a finite subset.

size :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (x : Finite-subset-of A) → ∃ λ n → ∣ x ∣≡ n
size equal? = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ = 0 , [ lift (refl _) ]

  e .∷ʳ {y = y} x (n , ∣y∣≡n) =
    case member? equal? x y of λ x∈?y →
        if x∈?y then n else suc n
      , lemma ∣y∣≡n x∈?y
    where
    lemma :
      ∣ y ∣≡ n →
      (x∈?y : Dec (x ∈ y)) →
      ∣ x ∷ y ∣≡ if x∈?y then n else suc n
    lemma ∣y∣≡n (yes x∈y) = [ inj₁ (x∈y , ∣y∣≡n) ]
    lemma ∣y∣≡n (no  x∉y) = [ inj₂ (x∉y , ∣y∣≡n) ]

  e .is-propositionʳ x (m , ∣x∣≡m) (n , ∣x∣≡n) =
    Σ-≡,≡→≡ (m  ≡⟨ ∣∣≡-functional x ∣x∣≡m ∣x∣≡n ⟩∎
             n  ∎)
            (∣∣≡-propositional x _ _)

------------------------------------------------------------------------
-- Finite types

-- A type is finite if there is some finite subset of the type for
-- which every element of the type is a member of the subset.

Is-finite : Type a → Type a
Is-finite A = Erased (∃ λ (s : Finite-subset-of A) → ∀ x → x ∈ s)

-- The Is-finite predicate is propositional.

Is-finite-propositional : Is-proposition (Is-finite A)
Is-finite-propositional [ x , p ] [ y , q ] =
                                $⟨ [ (λ z → record { to = λ _ → q z; from = λ _ → p z }) ] ⟩
  Erased (∀ z → z ∈ x ⇔ z ∈ y)  ↝⟨ EC.Erased-cong (inverse extensionality) ⟩
  Erased (x ≡ y)                ↔⟨ EC.Erased-cong (ignore-propositional-component (Π-closure ext 1 (λ _ → ∈-propositional))) ⟩
  Erased ((x , p) ≡ (y , q))    ↝⟨ EC.Erased-≡≃[]≡[] ⟩□
  [ (x , p) ] ≡ [ (y , q) ]     □

-- The Is-finite predicate is pointwise very stable.

Very-stable-Is-finite : Very-stable (Is-finite A)
Very-stable-Is-finite = EC.Very-stable-Erased

------------------------------------------------------------------------
-- Some definitions related to the definitions in Bag-equivalence

-- A lemma characterising from-List (in erased contexts).

@0 ∥∈∥≃∈-from-List : ∥ x BE.∈ ys ∥ ≃ (x ∈ from-List ys)
∥∈∥≃∈-from-List {x = x} {ys = ys} =
  Eq.⇔→≃
    Trunc.truncation-is-proposition
    ∈-propositional
    (to _)
    (from _)
  where
  to : ∀ ys → ∥ x BE.∈ ys ∥ → x ∈ from-List ys
  to []       = Trunc.rec ∈-propositional (λ ())
  to (y ∷ ys) = Trunc.rec ∈-propositional
                  P.[ ≡→∈∷ , ∈→∈∷ ∘ to ys ∘ ∣_∣ ]

  from : ∀ ys → x ∈ from-List ys → ∥ x BE.∈ ys ∥
  from [] ()
  from (y ∷ ys) =
    Trunc.rec
      Trunc.truncation-is-proposition
      P.[ ∣_∣ ∘ inj₁ , Trunc.∥∥-map inj₂ ∘ from ys ] ∘
    _≃_.to ∈∷≃

-- Finite subsets can be expressed as lists quotiented by set
-- equivalence (in erased contexts).

@0 ≃List/∼ : Finite-subset-of A ≃ List A / _∼[ set ]_
≃List/∼ = from-bijection (record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  })
  where
  cons : A → List A / _∼[ set ]_ → List A / _∼[ set ]_
  cons x = (x ∷_) Q./-map λ _ _ → refl _ BE.∷-cong_

  to : Finite-subset-of A → List A / _∼[ set ]_
  to = rec r
    where
    r : Rec _ _
    r .[]ʳ       = Q.[ [] ]
    r .∷ʳ x _ y  = cons x y
    r .is-setʳ   = Q./-is-set
    r .dropʳ x _ = Q.elim-prop λ where
      .Q.[]ʳ xs → Q.[]-respects-relation λ z →
        z BE.∈ x ∷ x ∷ xs      ↝⟨ record { to = P.[ inj₁ , id ]; from = inj₂ } ⟩□
        z BE.∈ x ∷ xs          □
      .Q.is-propositionʳ _ → Q./-is-set

    r .swapʳ x y _ = Q.elim-prop λ where
      .Q.[]ʳ xs → Q.[]-respects-relation λ z →
        z BE.∈ x ∷ y ∷ xs  ↔⟨ BE.swap-first-two z ⟩□
        z BE.∈ y ∷ x ∷ xs  □
      .Q.is-propositionʳ _ → Q./-is-set

  from : List A / _∼[ set ]_ → Finite-subset-of A
  from {A = A} = Q.rec λ @0 where
    .Q.[]ʳ → from-List

    .Q.[]-respects-relationʳ {x = xs} {y = ys} xs∼ys →
      _≃_.from extensionality λ z →
        z ∈ from-List xs  ↔⟨ inverse ∥∈∥≃∈-from-List ⟩
        ∥ z BE.∈ xs ∥     ↔⟨ Trunc.∥∥-cong-⇔ {k = bijection} (xs∼ys z) ⟩
        ∥ z BE.∈ ys ∥     ↔⟨ ∥∈∥≃∈-from-List ⟩□
        z ∈ from-List ys  □

    .Q.is-setʳ → is-set

  to∘from : ∀ x → to (from x) ≡ x
  to∘from = Q.elim-prop λ @0 where
      .Q.[]ʳ               → lemma
      .Q.is-propositionʳ _ → Q./-is-set
    where
    lemma : ∀ xs → to (from-List xs) ≡ Q.[ xs ]
    lemma []       = refl _
    lemma (x ∷ xs) =
      to (from-List (x ∷ xs))                              ≡⟨⟩
      ((x ∷_) Q./-map _) (to (from-List xs))               ≡⟨ cong ((x ∷_) Q./-map _) (lemma xs) ⟩
      ((x ∷_) Q./-map λ _ _ → refl _ BE.∷-cong_) Q.[ xs ]  ≡⟨⟩
      Q.[ x ∷ xs ]                                         ∎

  from∘to : ∀ x → from (to x) ≡ x
  from∘to = elim-prop e
    where
    e : Elim-prop _
    e .[]ʳ = refl _

    e .∷ʳ {y = y} x hyp =
      from (to (x ∷ y))     ≡⟨⟩
      from (cons x (to y))  ≡⟨ Q.elim-prop
                                 {P = λ y → from (cons x y) ≡ x ∷ from y}
                                 (λ @0 where
                                    .Q.[]ʳ _             → refl _
                                    .Q.is-propositionʳ _ → is-set)
                                 (to y) ⟩
      x ∷ from (to y)       ≡⟨ cong (x ∷_) hyp ⟩∎
      x ∷ y                 ∎

    e .is-propositionʳ _ = is-set

-- A truncated variant of the proof-relevant membership relation from
-- Bag-equivalence can be expressed in terms of _∈_ (in erased
-- contexts).

@0 ∥∈∥≃∈ : ∥ x BE.∈ ys ∥ ≃ (x ∈ _≃_.from ≃List/∼ Q.[ ys ])
∥∈∥≃∈ = ∥∈∥≃∈-from-List

------------------------------------------------------------------------
-- Fresh numbers

-- One can always find a natural number that is distinct from those in
-- a given finite set of natural numbers.

fresh :
  (ns : Finite-subset-of ℕ) →
  ∃ λ (n : ℕ) → n ∉ ns
fresh ns =
  Σ-map id
    (λ {m} →
       Erased (∀ n → n ∈ ns → n < m)  →⟨ EC.map (_$ m) ⟩
       Erased (m ∈ ns → m < m)        →⟨ EC.map (∀-cong _ λ _ → Nat.+≮ 0) ⟩
       Erased (m ∉ ns)                →⟨ EC.Stable-¬ ⟩□
       m ∉ ns                         □)
    (elim e ns)
  where
  OK : @0 Finite-subset-of ℕ → @0 ℕ → Type
  OK ms m = Erased (∀ n → n ∈ ms → n < m)

  prop : Is-proposition (OK ms m)
  prop =
    EC.H-level-Erased 1 (
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    ≤-propositional)

  ∷-max-suc :
    ∀ {ms n m} →
    OK ms n →
    OK (m ∷ ms) (Nat.max (suc m) n)
  ∷-max-suc {ms = ms} {n = n} {m = m} [ ub ] =
    [ (λ o →
         o ∈ m ∷ ms                   ↔⟨ ∈∷≃ ⟩
         o ≡ m ∥⊎∥ o ∈ ms             →⟨ Nat.≤-refl′ ∘ cong suc ∘ id Trunc.∥⊎∥-cong ub o ⟩
         o Nat.< suc m ∥⊎∥ o Nat.< n  →⟨ Trunc.rec ≤-propositional
                                           P.[ flip Nat.≤-trans (Nat.ˡ≤max _ n)
                                             , flip Nat.≤-trans (Nat.ʳ≤max (suc m) _)
                                             ] ⟩□
         o Nat.< Nat.max (suc m) n    □)
    ]

  e : Elim (λ ms → ∃ λ m → OK ms m)
  e .[]ʳ =
    0 , [ (λ _ ()) ]

  e .∷ʳ m (n , ub) =
    Nat.max (suc m) n , ∷-max-suc ub

  e .dropʳ {y = ns} m (n , ub) =
    _↔_.to (ignore-propositional-component prop)
      (proj₁ (subst (λ ms → ∃ λ m → OK ms m)
                    (drop {x = m} {y = ns})
                    ( Nat.max (suc m) (Nat.max (suc m) n)
                    , ∷-max-suc (∷-max-suc ub)
                    ))                                     ≡⟨ cong proj₁ $
                                                              push-subst-pair-× {y≡z = drop {x = m} {y = ns}} _
                                                                (λ (ms , m) → OK ms m)
                                                                {p = _ , ∷-max-suc (∷-max-suc ub)} ⟩

       Nat.max (suc m) (Nat.max (suc m) n)                 ≡⟨ Nat.max-assoc (suc m) {n = suc m} {o = n} ⟩

       Nat.max (Nat.max (suc m) (suc m)) n                 ≡⟨ cong (λ m → Nat.max m n) $ Nat.max-idempotent (suc m) ⟩∎

       Nat.max (suc m) n                                   ∎)

  e .swapʳ {z = ns} m n (o , ub) =
    _↔_.to (ignore-propositional-component prop)
      (proj₁ (subst (λ xs → ∃ λ m → OK xs m)
                    (swap {x = m} {y = n} {z = ns})
                    ( Nat.max (suc m) (Nat.max (suc n) o)
                    , ∷-max-suc (∷-max-suc ub)
                    ))                                     ≡⟨ cong proj₁ $
                                                              push-subst-pair-× {y≡z = swap {x = m} {y = n} {z = ns}} _
                                                                (λ (ms , m) → OK ms m)
                                                                {p = _ , ∷-max-suc (∷-max-suc ub)} ⟩

       Nat.max (suc m) (Nat.max (suc n) o)                 ≡⟨ Nat.max-assoc (suc m) {n = suc n} {o = o} ⟩

       Nat.max (Nat.max (suc m) (suc n)) o                 ≡⟨ cong (λ m → Nat.max m o) $ Nat.max-comm (suc m) (suc n) ⟩

       Nat.max (Nat.max (suc n) (suc m)) o                 ≡⟨ sym $ Nat.max-assoc (suc n) {n = suc m} {o = o} ⟩∎

       Nat.max (suc n) (Nat.max (suc m) o)                 ∎)

  e .is-setʳ _ =
    Σ-closure 2 ℕ-set λ _ →
    H-level.mono₁ 1 prop
