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
  using (Erased; [_]; [_]→; Dec-Erased; Dec→Dec-Erased; Very-stable)
open import Finite-subset.Listed eq
import Finite-subset.Listed.Membership eq as M
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
    a                                    : Level
    A B                                  : Type a
    H ms ns p q x x₁ x₂ y y₁ y₂ ys z _≟_ : A
    P                                    : A → Type p
    f g                                  : (x : A) → P x
    m n                                  : ℕ

------------------------------------------------------------------------
-- Membership

-- Membership.

infix 4 _∈_

_∈_ : {A : Type a} (x : A) (y : Finite-subset-of A) → Type a
x ∈ y = Erased (x M.∈ y)

-- In erased contexts x ∈ y is equivalent to x M.∈ y.

@0 ∈≃∈ : (x ∈ y) ≃ (x M.∈ y)
∈≃∈ {x} {y} =
  x ∈ y    ↔⟨ EC.erased EC.Erased↔ ⟩□
  x M.∈ y  □

-- The negation of membership.

infix 4 _∉_

_∉_ : {A : Type a} → A → Finite-subset-of A → Type a
x ∉ y = ¬ x ∈ y

-- Membership is propositional.

∈-propositional : Is-proposition (x ∈ y)
∈-propositional {x} {y} =            $⟨ [ M.∈-propositional ] ⟩
  Erased (Is-proposition (x M.∈ y))  →⟨ EC.Erased-H-level↔H-level 1 _ ⟩□
  Is-proposition (Erased (x M.∈ y))  □

-- Membership is very stable.

Very-stable-∈ : Very-stable (x ∈ y)
Very-stable-∈ = EC.Very-stable-Erased

-- A lemma characterising [].

∈[]≃ : (x ∈ []) ≃ ⊥₀
∈[]≃ {x} =
  x ∈ []    ↝⟨ EC.Erased-cong M.∈[]≃ ⟩
  Erased ⊥  ↔⟨ EC.Erased-⊥↔⊥ ⟩□
  ⊥         □

-- The type Erased ((x ∈ y) ≃ A) is equivalent to (x ∈ y) ≃ Erased A.
-- Thus certain erased lemmas below (like ∈∷≃ and ∈singleton≃) can be
-- turned into non-erased lemmas with related types.

∈≃≃∈≃Erased : Erased ((x ∈ y) ≃ A) ≃ ((x ∈ y) ≃ Erased A)
∈≃≃∈≃Erased {x} {y} {A} =
  Erased ((x ∈ y) ≃ A)       ↝⟨ EC.Erased-↝↝↝ ext ⟩
  Erased (x ∈ y) ≃ Erased A  ↝⟨ ≃-cong ext (EC.Very-stable→Stable 0 Very-stable-∈) F.id ⟩□
  (x ∈ y) ≃ Erased A         □

-- A lemma characterising _∷_ (in erased contexts).

@0 ∈∷≃ : (x ∈ y ∷ z) ≃ (x ≡ y ∥⊎∥ x ∈ z)
∈∷≃ {x} {y} {z} =
  x ∈ y ∷ z                   ↝⟨ EC.Erased-cong M.∈∷≃ ⟩
  Erased (x ≡ y ∥⊎∥ x M.∈ z)  ↔⟨ EC.erased EC.Erased↔ ⟩
  x ≡ y ∥⊎∥ x M.∈ z           ↝⟨ F.id Trunc.∥⊎∥-cong inverse ∈≃∈ ⟩□
  x ≡ y ∥⊎∥ x ∈ z             □

-- A variant of ∈∷≃.

∈≢∷≃ : x ≢ y → (x ∈ y ∷ z) ≃ (x ∈ z)
∈≢∷≃ x≢y = EC.Erased-cong (M.∈≢∷≃ x≢y)

-- A lemma characterising singleton (in erased contexts).

@0 ∈singleton≃ : (x ∈ singleton y) ≃ ∥ x ≡ y ∥
∈singleton≃ {x} {y} =
  x ∈ singleton y   ↝⟨ EC.Erased-cong M.∈singleton≃ ⟩
  Erased ∥ x ≡ y ∥  ↔⟨ EC.erased EC.Erased↔ ⟩
  ∥ x ≡ y ∥         □

-- Some "introduction rules" for _∈_.

∈→∈∷ : x ∈ z → x ∈ y ∷ z
∈→∈∷ {x} {z} {y} =
  EC.Very-stable→Stable 0
    (EC.Very-stable-Π ext λ _ → Very-stable-∈)
    [ x ∈ z      →⟨ EC.map M.∈→∈∷ ⟩□
      x ∈ y ∷ z  □
    ]

∥≡∥→∈∷ : ∥ x ≡ y ∥ → x ∈ y ∷ z
∥≡∥→∈∷ {x} {y} {z} =
  EC.Very-stable→Stable 0
    (EC.Very-stable-Π ext λ _ → Very-stable-∈)
    [ ∥ x ≡ y ∥  →⟨ [_]→ ∘ M.∥≡∥→∈∷ ⟩□
      x ∈ y ∷ z  □
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
∈∪≃ {x} {y} {z} =
  x ∈ y ∪ z                     ↝⟨ EC.Erased-cong M.∈∪≃ ⟩
  Erased (x M.∈ y ∥⊎∥ x M.∈ z)  ↔⟨ EC.erased EC.Erased↔ ⟩
  x M.∈ y ∥⊎∥ x M.∈ z           ↝⟨ inverse $ ∈≃∈ Trunc.∥⊎∥-cong ∈≃∈ ⟩□
  x ∈ y ∥⊎∥ x ∈ z               □

-- More "introduction rules".

∈→∈∪ˡ : x ∈ y → x ∈ y ∪ z
∈→∈∪ˡ {x} {y} {z} =
  EC.Very-stable→Stable 0
    (EC.Very-stable-Π ext λ _ → Very-stable-∈)
    [ x ∈ y      →⟨ EC.map M.∈→∈∪ˡ ⟩□
      x ∈ y ∪ z  □
    ]

∈→∈∪ʳ : ∀ y → x ∈ z → x ∈ y ∪ z
∈→∈∪ʳ {x} {z} y =
  EC.Very-stable→Stable 0
    (EC.Very-stable-Π ext λ _ → Very-stable-∈)
    [ x ∈ z      →⟨ EC.map (M.∈→∈∪ʳ y) ⟩□
      x ∈ y ∪ z  □
    ]

-- A lemma characterising join (in erased contexts).

@0 ∈join≃ : (x ∈ join z) ≃ ∥ (∃ λ y → x ∈ y × y ∈ z) ∥
∈join≃ {x} {z} =
  x ∈ join z                              ↝⟨ EC.Erased-cong M.∈join≃ ⟩
  Erased ∥ (∃ λ y → x M.∈ y × y M.∈ z) ∥  ↔⟨ EC.erased EC.Erased↔ ⟩
  ∥ (∃ λ y → x M.∈ y × y M.∈ z) ∥         ↝⟨ (inverse $ Trunc.∥∥-cong $ ∃-cong λ _ → ∈≃∈ ×-cong ∈≃∈) ⟩□
  ∥ (∃ λ y → x ∈ y × y ∈ z) ∥             □

-- If truncated equality is decidable (with erased proofs), then
-- membership is decidable.

member? :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (x : A) (y : Finite-subset-of A) → Dec (x ∈ y)
member? equal? x = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ          = no λ { [ () ] }
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

-- The functions member? and M.member? are related to each other (in
-- erased contexts).

@0 member?≡member?ᴱ :
  ∀ {equal? : (x y : A) → Dec-Erased ∥ x ≡ y ∥} y →
  Dec→Dec-Erased
    (Dec-map (_≃_.logical-equivalence ∈≃∈) (member? equal? x y)) ≡
  M.member?ᴱ equal? x y
member?≡member?ᴱ _ =
  EC.Is-proposition-Dec-Erased ext M.∈-propositional _ _

-- If x is a member of y, then x ∷ y is equal to y (in erased
-- contexts).

@0 ∈→∷≡ : x ∈ y → x ∷ y ≡ y
∈→∷≡ = M.∈→∷≡ ∘ EC.erased

------------------------------------------------------------------------
-- Subsets of subsets

-- Subsets.

infix 4 _⊆_

_⊆_ : {A : Type a} → Finite-subset-of A → Finite-subset-of A → Type a
x ⊆ y = ∀ z → z ∈ x → z ∈ y

-- In erased contexts x ⊆ y is equivalent to x M.⊆ y.

@0 ⊆≃⊆ : (x ⊆ y) ≃ (x M.⊆ y)
⊆≃⊆ {x} {y} =
  (∀ z → z ∈ x → z ∈ y)      ↝⟨ (∀-cong ext λ _ → →-cong ext ∈≃∈ ∈≃∈) ⟩□
  (∀ z → z M.∈ x → z M.∈ y)  □

-- _⊆_ is pointwise very stable.

Very-stable-⊆ : Very-stable (x ⊆ y)
Very-stable-⊆ =
  EC.Very-stable-Π ext λ _ →
  EC.Very-stable-Π ext λ _ →
  Very-stable-∈

-- _⊆_ is pointwise propositional.

⊆-propositional : Is-proposition (x ⊆ y)
⊆-propositional {x} {y} =            $⟨ [ M.⊆-propositional ] ⟩
  Erased (Is-proposition (x M.⊆ y))  →⟨ EC.map (H-level-cong _ 1 (inverse ⊆≃⊆)) ⟩
  Erased (Is-proposition (x ⊆ y))    →⟨ EC.Erased-H-level↔H-level 1 _ ⟩
  Is-proposition (Erased (x ⊆ y))    →⟨ H-level-cong _ 1 (EC.Very-stable→Stable {k = equivalence} 0 Very-stable-⊆) ⟩□
  Is-proposition (x ⊆ y)             □

-- The subset property can be expressed using _∪_ and _≡_ (in erased
-- contexts).

@0 ⊆≃∪≡ : ∀ x → (x ⊆ y) ≃ (x ∪ y ≡ y)
⊆≃∪≡ {y} x =
  x ⊆ y      ↝⟨ ⊆≃⊆ ⟩
  x M.⊆ y    ↝⟨ M.⊆≃∪≡ x ⟩□
  x ∪ y ≡ y  □

-- A form of extensionality that holds in erased contexts.

@0 extensionality : (x ≡ y) ≃ (∀ z → z ∈ x ⇔ z ∈ y)
extensionality {x} {y} =
  x ≡ y                      ↝⟨ M.extensionality ⟩
  (∀ z → z M.∈ x ⇔ z M.∈ y)  ↝⟨ inverse (∀-cong ext λ _ → ⇔-cong ext ∈≃∈ ∈≃∈) ⟩□
  (∀ z → z ∈ x ⇔ z ∈ y)      □

-- Another way to characterise equality (in erased contexts).

@0 ≡≃⊆×⊇ : (x ≡ y) ≃ (x ⊆ y × y ⊆ x)
≡≃⊆×⊇ {x} {y} =
  x ≡ y              ↝⟨ M.≡≃⊆×⊇ ⟩
  x M.⊆ y × y M.⊆ x  ↝⟨ inverse $ ⊆≃⊆ ×-cong ⊆≃⊆ ⟩□
  x ⊆ y × y ⊆ x      □

-- The empty set is not equal to a set constructed using _∷_.

[]≢∷ : Finite-subset-of.[] ≢ x ∷ y
[]≢∷ = EC.Very-stable→Stable 0 (EC.Very-stable-¬ ext) [ M.[]≢∷ ]

-- _⊆_ is a partial order (in erased contexts).

⊆-refl : x ⊆ x
⊆-refl {x} =        $⟨ [ M.⊆-refl ] ⟩
  Erased (x M.⊆ x)  →⟨ EC.map (_≃_.from ⊆≃⊆) ⟩
  Erased (x ⊆ x)    →⟨ EC.Very-stable→Stable 0 Very-stable-⊆ ⟩□
  x ⊆ x             □

⊆-trans : x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans {x} {y} {z} = curry
  (x ⊆ y × y ⊆ z               →⟨ [_]→ ⟩
   Erased (x ⊆ y × y ⊆ z)      ↔⟨ EC.Erased-cong (⊆≃⊆ ×-cong ⊆≃⊆) ⟩
   Erased (x M.⊆ y × y M.⊆ z)  →⟨ EC.map (uncurry M.⊆-trans) ⟩
   Erased (x M.⊆ z)            ↔⟨ EC.Erased-cong (inverse ⊆≃⊆) ⟩
   Erased (x ⊆ z)              →⟨ EC.Very-stable→Stable 0 Very-stable-⊆ ⟩□
   x ⊆ z                       □)

@0 ⊆-antisymmetric : x ⊆ y → y ⊆ x → x ≡ y
⊆-antisymmetric {x} {y} = curry
  (x ⊆ y × y ⊆ x      ↔⟨ ⊆≃⊆ ×-cong ⊆≃⊆ ⟩
   x M.⊆ y × y M.⊆ x  →⟨ uncurry M.⊆-antisymmetric ⟩□
   x ≡ y              □)

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
equal? = M.equal?

------------------------------------------------------------------------
-- Some properties related to map-Maybe and filter

-- A lemma characterising map-Maybe (in erased contexts).

@0 ∈map-Maybe≃ :
  (x ∈ map-Maybe f y) ≃ ∥ (∃ λ z → z ∈ y × f z ≡ just x) ∥
∈map-Maybe≃ {x} {f} {y} =
  x ∈ map-Maybe f y                     ↝⟨ ∈≃∈ ⟩
  x M.∈ map-Maybe f y                   ↝⟨ M.∈map-Maybe≃ ⟩
  ∥ (∃ λ z → z M.∈ y × f z ≡ just x) ∥  ↝⟨ Trunc.∥∥-cong (∃-cong λ _ → ×-cong₁ λ _ → inverse ∈≃∈) ⟩□
  ∥ (∃ λ z → z ∈ y × f z ≡ just x) ∥    □

-- A lemma characterising map (in erased contexts).

@0 ∈map≃ : (x ∈ map f y) ≃ ∥ (∃ λ z → z ∈ y × f z ≡ x) ∥
∈map≃ {x} {f} {y} =
  x ∈ map f y                      ↝⟨ ∈≃∈ ⟩
  x M.∈ map f y                    ↝⟨ M.∈map≃ ⟩
  ∥ (∃ λ z → z M.∈ y × f z ≡ x) ∥  ↝⟨ Trunc.∥∥-cong (∃-cong λ _ → ×-cong₁ λ _ → inverse ∈≃∈) ⟩□
  ∥ (∃ λ z → z ∈ y × f z ≡ x) ∥    □

-- If x ∈ y, then f x ∈ map f y.

∈→∈map :
  {f : A → B} →
  x ∈ y → f x ∈ map f y
∈→∈map {x} {y} {f} =
  EC.Very-stable→Stable 0
    (EC.Very-stable-Π ext λ _ → Very-stable-∈)
    [ x ∈ y            ↔⟨ ∈≃∈ ⟩
      x M.∈ y          →⟨ M.∈→∈map ⟩
      f x M.∈ map f y  ↔⟨ inverse ∈≃∈ ⟩□
      f x ∈ map f y    □
    ]

-- If f is injective, then f x ∈ map f y is equivalent to x ∈ y.

Injective→∈map≃ :
  {f : A → B} →
  Injective f →
  (f x ∈ map f y) ≃ (x ∈ y)
Injective→∈map≃ {x} {y} {f} inj =
  EC.Very-stable→Stable 0
    (EC.Very-stable-↝ ext Very-stable-∈ Very-stable-∈)
    [ f x ∈ map f y    ↝⟨ ∈≃∈ ⟩
      f x M.∈ map f y  ↝⟨ M.Injective→∈map≃ inj ⟩
      x M.∈ y          ↝⟨ inverse ∈≃∈ ⟩□
      x ∈ y            □
    ]

-- A lemma characterising filter.

∈filter≃ :
  ∀ p → (x ∈ filter p y) ≃ (T (p x) × x ∈ y)
∈filter≃ {x} {y} p =
  EC.Very-stable→Stable 0
    (EC.Very-stable-↝ ext
       Very-stable-∈
       (EC.Very-stable-× (EC.Very-stable-T (p x)) Very-stable-∈))
    [ x ∈ filter p y     ↝⟨ ∈≃∈ ⟩
      x M.∈ filter p y   ↝⟨ M.∈filter≃ p ⟩
      T (p x) × x M.∈ y  ↝⟨ (∃-cong λ _ → inverse ∈≃∈) ⟩□
      T (p x) × x ∈ y    □
    ]

-- The result of filtering is a subset of the original subset.

filter⊆ : ∀ p → filter p x ⊆ x
filter⊆ {x} p =
  EC.Very-stable→Stable 0
    Very-stable-⊆
    [                   $⟨ M.filter⊆ p ⟩
      filter p x M.⊆ x  ↝⟨ inverse ⊆≃⊆ ⟩□
      filter p x ⊆ x    □
    ]

------------------------------------------------------------------------
-- The functions minus and delete

-- If erased truncated equality is decidable, then one subset can be
-- removed from another.

minus :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  Finite-subset-of A → Finite-subset-of A → Finite-subset-of A
minus _≟_ x y =
  filter (λ z → if member? _≟_ z y then false else true) x

-- In erased contexts minus is pointwise equal to M.minus.

@0 minus≡minus : ∀ x y → minus _≟_ x y ≡ M.minus _≟_ x y
minus≡minus {_≟_} x y =
  cong
    {x = λ z → if member? _≟_ z y then false else true}
    {y = λ z → if M.member?ᴱ _≟_ z y then false else true}
    (λ m → filter m x) $
  ⟨ext⟩ λ z →
    if member? _≟_ z y then false else true         ≡⟨ lemma (member? _≟_ z y) ⟩
    if conv (member? _≟_ z y) then false else true  ≡⟨ cong (if_then false else true) $ member?≡member?ᴱ y ⟩∎
    if M.member?ᴱ _≟_ z y then false else true      ∎
  where
  conv : Dec (z ∈ y) → Dec-Erased (z M.∈ y)
  conv = Dec→Dec-Erased ∘ Dec-map (_≃_.logical-equivalence ∈≃∈)

  lemma :
    (x : Dec (z ∈ y)) →
    if x then false else true ≡
    if conv x then false else true
  lemma (yes _) = refl _
  lemma (no _)  = refl _

-- A lemma characterising minus.

∈minus≃ : (x ∈ minus _≟_ y z) ≃ (x ∈ y × x ∉ z)
∈minus≃ {x} {_≟_} {y} {z} =
  EC.Very-stable→Stable 0
    (EC.Very-stable-↝ ext
       Very-stable-∈
       (EC.Very-stable-× Very-stable-∈ (EC.Very-stable-¬ ext)))
    [ x ∈ minus _≟_ y z      ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) $ minus≡minus y z ⟩
      x ∈ M.minus _≟_ y z    ↝⟨ ∈≃∈ ⟩
      x M.∈ M.minus _≟_ y z  ↝⟨ M.∈minus≃ ⟩
      x M.∈ y × x M.∉ z      ↝⟨ inverse $ ∈≃∈ ×-cong ¬-cong ext ∈≃∈ ⟩□
      x ∈ y × x ∉ z          □
    ]

-- The result of minus is a subset of the original subset.

minus⊆ : ∀ y → minus _≟_ x y ⊆ x
minus⊆ {_≟_} {x} y =
  EC.Very-stable→Stable 0 Very-stable-⊆
    [                        $⟨ M.minus⊆ y ⟩
      M.minus _≟_ x y M.⊆ x  →⟨ subst (M._⊆ _) $ sym $ minus≡minus x y ⟩
      minus _≟_ x y M.⊆ x    ↔⟨ inverse ⊆≃⊆ ⟩□
      minus _≟_ x y ⊆ x      □
    ]

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
minus⊆≃ {_≟_} {x} {z} y =
  EC.Very-stable→Stable 0
    (EC.Very-stable-↝ ext Very-stable-⊆ Very-stable-⊆)
    [ (let _≟′_ = λ x y → Dec→Dec-Erased
                            (_≃_.to EC.Dec-Erased≃Dec (x ≟ y)) in
       minus _≟_ x y ⊆ z       ↝⟨ (≡⇒↝ _ $ cong (_⊆ _) $ cong (λ _≟_ → minus _≟_ x y) $ ⟨ext⟩ λ _ → ⟨ext⟩ λ _ → sym $
                                   _≃_.left-inverse-of EC.Dec-Erased≃Dec _) ⟩
       minus _≟′_ x y ⊆ z      ↝⟨ ≡⇒↝ _ $ cong (_⊆ _) $ minus≡minus x y ⟩
       M.minus _≟′_ x y ⊆ z    ↝⟨ ⊆≃⊆ ⟩
       M.minus _≟′_ x y M.⊆ z  ↝⟨ M.minus⊆≃ y ⟩
       x M.⊆ y ∪ z             ↝⟨ inverse ⊆≃⊆ ⟩□
       x ⊆ y ∪ z               □)
    ]

-- If erased truncated equality is decidable, then elements can be
-- removed from a subset.

delete :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  A → Finite-subset-of A → Finite-subset-of A
delete _≟_ x y = minus _≟_ y (singleton x)

-- In erased contexts delete is pointwise equal to M.delete.

@0 delete≡delete :
  ∀ (_≟_ : (x y : A) → Dec-Erased ∥ x ≡ y ∥) y →
  delete _≟_ x y ≡ M.delete _≟_ x y
delete≡delete {x} _≟_ y = minus≡minus {_≟_ = _≟_} y (singleton x)

-- A lemma characterising delete.

∈delete≃ : ∀ _≟_ → (x ∈ delete _≟_ y z) ≃ (x ≢ y × x ∈ z)
∈delete≃ {x} {y} {z} _≟_ =
  EC.Very-stable→Stable 0
    (EC.Very-stable-↝ ext
       Very-stable-∈
       (EC.Very-stable-× (EC.Very-stable-¬ ext) Very-stable-∈))
    [ x ∈ delete _≟_ y z      ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) $ delete≡delete _≟_ z ⟩
      x ∈ M.delete _≟_ y z    ↝⟨ ∈≃∈ ⟩
      x M.∈ M.delete _≟_ y z  ↝⟨ M.∈delete≃ _≟_ ⟩
      x ≢ y × x M.∈ z         ↝⟨ F.id ×-cong inverse ∈≃∈ ⟩□
      x ≢ y × x ∈ z           □
    ]

-- A deleted element is no longer a member of the set.

∉delete : ∀ _≟_ y → x ∉ delete _≟_ x y
∉delete {x} _≟_ y =
  EC.Very-stable→Stable 0 (EC.Very-stable-¬ ext)
    [ x ∈ delete _≟_ x y      →⟨ subst (_ ∈_) $ delete≡delete _≟_ y ⟩
      x ∈ M.delete _≟_ x y    ↔⟨ ∈≃∈ ⟩
      x M.∈ M.delete _≟_ x y  →⟨ M.∉delete _≟_ y ⟩□
      ⊥                       □
    ]

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
∷-cong-⊆ {y} {z} {x} =
  EC.Very-stable→Stable 0
    (EC.Very-stable-Π ext λ _ → Very-stable-⊆)
    [ y ⊆ z            ↔⟨ ⊆≃⊆ ⟩
      y M.⊆ z          →⟨ M.∷-cong-⊆ ⟩
      x ∷ y M.⊆ x ∷ z  ↔⟨ inverse ⊆≃⊆ ⟩□
      x ∷ y ⊆ x ∷ z    □
    ]

∪-cong-⊆ : x₁ ⊆ x₂ → y₁ ⊆ y₂ → x₁ ∪ y₁ ⊆ x₂ ∪ y₂
∪-cong-⊆ {x₁} {x₂} {y₁} {y₂} =
  curry $
  EC.Very-stable→Stable 0 (EC.Very-stable-Π ext λ _ → Very-stable-⊆)
    [ x₁ ⊆ x₂ × y₁ ⊆ y₂      ↔⟨ ⊆≃⊆ ×-cong ⊆≃⊆ ⟩
      x₁ M.⊆ x₂ × y₁ M.⊆ y₂  →⟨ uncurry M.∪-cong-⊆ ⟩
      x₁ ∪ y₁ M.⊆ x₂ ∪ y₂    ↔⟨ inverse ⊆≃⊆ ⟩□
      x₁ ∪ y₁ ⊆ x₂ ∪ y₂      □
    ]

filter-cong-⊆ :
  ∀ p q →
  (∀ z → T (p z) → T (q z)) →
  x ⊆ y → filter p x ⊆ filter q y
filter-cong-⊆ {x} {y} p q p⇒q =
  EC.Very-stable→Stable 0 (EC.Very-stable-Π ext λ _ → Very-stable-⊆)
    [ x ⊆ y                      ↔⟨ ⊆≃⊆ ⟩
      x M.⊆ y                    →⟨ M.filter-cong-⊆ p q p⇒q ⟩
      filter p x M.⊆ filter q y  ↔⟨ inverse ⊆≃⊆ ⟩□
      filter p x ⊆ filter q y    □
    ]

minus-cong-⊆ : x₁ ⊆ x₂ → y₂ ⊆ y₁ → minus _≟_ x₁ y₁ ⊆ minus _≟_ x₂ y₂
minus-cong-⊆ {x₁} {x₂} {y₂} {y₁} {_≟_} =
  curry $
  EC.Very-stable→Stable 0 (EC.Very-stable-Π ext λ _ → Very-stable-⊆)
    [ x₁ ⊆ x₂ × y₂ ⊆ y₁                        ↔⟨ ⊆≃⊆ ×-cong ⊆≃⊆ ⟩
      x₁ M.⊆ x₂ × y₂ M.⊆ y₁                    →⟨ uncurry M.minus-cong-⊆ ⟩
      M.minus _≟_ x₁ y₁ M.⊆ M.minus _≟_ x₂ y₂  →⟨ subst (λ m → m x₁ y₁ M.⊆ m x₂ y₂)
                                                    (⟨ext⟩ λ x → ⟨ext⟩ λ y → sym $ minus≡minus x y) ⟩
      minus _≟_ x₁ y₁ M.⊆ minus _≟_ x₂ y₂      ↔⟨ inverse ⊆≃⊆ ⟩□
      minus _≟_ x₁ y₁ ⊆ minus _≟_ x₂ y₂        □
    ]

delete-cong-⊆ : ∀ _≟_ → y ⊆ z → delete _≟_ x y ⊆ delete _≟_ x z
delete-cong-⊆ _≟_ y⊆z =
  minus-cong-⊆ {_≟_ = _≟_} y⊆z (⊆-refl {x = singleton _})

------------------------------------------------------------------------
-- Size

-- Size.

infix 4 ∣_∣≡_

∣_∣≡_ : {A : Type a} → Finite-subset-of A → ℕ → Type a
∣ x ∣≡ n = Erased (M.∣ x ∣≡ n)

-- The size predicate is propositional.

∣∣≡-propositional :
  (x : Finite-subset-of A) → Is-proposition (∣ x ∣≡ n)
∣∣≡-propositional {n} x =               $⟨ [ M.∣∣≡-propositional x ] ⟩
  Erased (Is-proposition (M.∣ x ∣≡ n))  →⟨ EC.Erased-H-level↔H-level 1 _ ⟩
  Is-proposition (Erased (M.∣ x ∣≡ n))  ↔⟨⟩
  Is-proposition (∣ x ∣≡ n)             □

-- The size predicate is very stable.

Very-stable-∣∣≡ : (x : Finite-subset-of A) → Very-stable (∣ x ∣≡ n)
Very-stable-∣∣≡ _ = EC.Very-stable-Erased

-- Unit tests documenting the computational behaviour of ∣_∣≡_.

_ : (∣ [] {A = A} ∣≡ n) ≡ Erased (↑ _ (n ≡ 0))
_ = refl _

_ : ∀ {A : Type a} {x : A} {y} →
    (∣ x ∷ y ∣≡ zero) ≡ Erased (x M.∈ y × M.∣ y ∣≡ zero ⊎ ⊥)
_ = refl _

_ : (∣ x ∷ y ∣≡ suc n) ≡
    Erased (x M.∈ y × M.∣ y ∣≡ suc n ⊎ x M.∉ y × M.∣ y ∣≡ n)
_ = refl _

-- The size predicate is functional.

∣∣≡-functional :
  (x : Finite-subset-of A) → ∣ x ∣≡ m → ∣ x ∣≡ n → m ≡ n
∣∣≡-functional x [ ∣x∣≡m ] [ ∣x∣≡n ] =
  EC.Very-stable→Stable 1
    (EC.Decidable-equality→Very-stable-≡ Nat._≟_)
    _ _
    [ M.∣∣≡-functional x ∣x∣≡m ∣x∣≡n ]

-- If truncated equality is decidable (with erased proofs), then one
-- can compute the size of a finite subset.

size :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (x : Finite-subset-of A) → ∃ λ n → ∣ x ∣≡ n
size equal? = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ = 0 , [ lift (refl _) ]

  e .∷ʳ {y} x (n , ∣y∣≡n) =
    case member? equal? x y of λ x∈?y →
        if x∈?y then n else suc n
      , lemma ∣y∣≡n x∈?y
    where
    lemma :
      ∣ y ∣≡ n →
      (x∈?y : Dec (x ∈ y)) →
      ∣ x ∷ y ∣≡ if x∈?y then n else suc n
    lemma [ ∣y∣≡n ] (yes [ x∈y ]) =
      [ inj₁ (x∈y , ∣y∣≡n) ]
    lemma [ ∣y∣≡n ] (no x∉y) =
      [ inj₂ (x∉y ∘ _≃_.from ∈≃∈ , ∣y∣≡n) ]

  e .is-propositionʳ x (m , ∣x∣≡m) (n , ∣x∣≡n) =
    Σ-≡,≡→≡ (m  ≡⟨ ∣∣≡-functional x ∣x∣≡m ∣x∣≡n ⟩∎
             n  ∎)
            (∣∣≡-propositional x _ _)

-- The functions size and M.size are related to each other (in erased
-- contexts).

@0 size≡size : ∀ x → size f x ≡ Σ-map id [_]→ (M.size g x)
size≡size {f} {g} x =
  Σ-≡,≡→≡
    (proj₁ (size f x)    ≡⟨ ∣∣≡-functional x (proj₂ (size f x)) [ proj₂ (M.size g x) ] ⟩∎
     proj₁ (M.size g x)  ∎)
    (∣∣≡-propositional x _ _)

------------------------------------------------------------------------
-- Finite types

-- A type is finite if there is some finite subset of the type for
-- which every element of the type is a member of the subset.

Is-finite : Type a → Type a
Is-finite A = Erased (M.Is-finite A)

-- The Is-finite predicate is propositional.

Is-finite-propositional : Is-proposition (Is-finite A)
Is-finite-propositional {A} =              $⟨ [ M.Is-finite-propositional ] ⟩
  Erased (Is-proposition (M.Is-finite A))  →⟨ EC.Erased-H-level↔H-level 1 _ ⟩
  Is-proposition (Erased (M.Is-finite A))  ↔⟨⟩
  Is-proposition (Is-finite A)             □

-- The Is-finite predicate is pointwise very stable.

Very-stable-Is-finite : Very-stable (Is-finite A)
Very-stable-Is-finite = EC.Very-stable-Erased

------------------------------------------------------------------------
-- Some definitions related to the definitions in Bag-equivalence

-- A lemma characterising from-List (in erased contexts).

@0 ∥∈∥≃∈-from-List : ∥ x BE.∈ ys ∥ ≃ (x ∈ from-List ys)
∥∈∥≃∈-from-List {x} {ys} =
  ∥ x BE.∈ ys ∥       ↝⟨ M.∥∈∥≃∈-from-List ⟩
  x M.∈ from-List ys  ↝⟨ inverse ∈≃∈ ⟩□
  x ∈ from-List ys    □

-- Finite subsets can be expressed as lists quotiented by set
-- equivalence (in erased contexts).

@0 ≃List/∼ : Finite-subset-of A ≃ List A / _∼[ set ]_
≃List/∼ = M.≃List/∼

-- A truncated variant of the proof-relevant membership relation from
-- Bag-equivalence can be expressed in terms of _∈_ (in erased
-- contexts).

@0 ∥∈∥≃∈ : ∥ x BE.∈ ys ∥ ≃ (x ∈ _≃_.from ≃List/∼ Q.[ ys ])
∥∈∥≃∈ {x} {ys} =
  ∥ x BE.∈ ys ∥                      ↝⟨ M.∥∈∥≃∈ ⟩
  x M.∈ _≃_.from M.≃List/∼ Q.[ ys ]  ↔⟨⟩
  x M.∈ _≃_.from ≃List/∼ Q.[ ys ]    ↝⟨ inverse ∈≃∈ ⟩□
  x ∈ _≃_.from ≃List/∼ Q.[ ys ]      □

------------------------------------------------------------------------
-- Fresh numbers

-- One can always find a natural number that is distinct from those in
-- a given finite set of natural numbers.

fresh :
  (ns : Finite-subset-of ℕ) →
  ∃ λ (n : ℕ) → n ∉ ns
fresh = λ ns →
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
  ∷-max-suc {ms} {n} {m} [ ub ] =
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
    0 , [ (λ { _ [ () ] }) ]

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

-- The functions fresh and M.fresh are related to each other (in
-- erased contexts).

@0 fresh≡fresh :
  fresh ns ≡ Σ-map id (_∘ _≃_.to ∈≃∈) (M.fresh ns)
fresh≡fresh {ns} =
  Σ-≡,≡→≡
    (lemma ns)
    (¬-propositional ext _ _)
  where
  lemma : ∀ ns → proj₁ (fresh ns) ≡ proj₁ (M.fresh ns)
  lemma = elim-prop λ @0 where
    .Elim-prop.[]ʳ →
      0  ∎
    .Elim-prop.∷ʳ {y = ns} n →
      proj₁ (fresh ns) ≡ proj₁ (M.fresh ns)              →⟨ cong (Nat.max (suc n)) ⟩

      Nat.max (suc n) (proj₁ (fresh ns)) ≡
      Nat.max (suc n) (proj₁ (M.fresh ns))               ↔⟨⟩

      proj₁ (fresh (n ∷ ns)) ≡ proj₁ (M.fresh (n ∷ ns))  □
    .Elim-prop.is-propositionʳ _ →
      ℕ-set
