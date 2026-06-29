------------------------------------------------------------------------
-- Integers, defined using "erased quotients"
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
import Quotient.Erased.Axiomatised

-- The code is parametrised by an implementation of quotients.

module Integer.Quotient.Erased
  {e⁺}
  (eq : ∀ {a p} → Equality-with-J a p e⁺)
  (open Quotient.Erased.Axiomatised eq)
  (quot : Quotientᴱ)
  where

open Derived-definitions-and-properties eq hiding (elim)
private
  open module Q = Quotientᴱ quot using (_/ᴱ_; [_]; []-respects-relation)

open import Logical-equivalence using (_⇔_)
open import Prelude as P
  hiding (suc) renaming (_+_ to _⊕_; _*_ to _⊛_)

open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_; _≃ᴱ′_)
open import Equivalence-relation eq
open import Erased.Level-1 eq as Erased renaming ([_] to [_]ᴱ)
open import Erased.Stability eq
open import Extensionality eq
open import Function-universe eq hiding (id; _∘_)
open import Group eq using (Group)
open import Group.Erased eq as G using (Groupᴱ; _≃ᴳ_; Group→Groupᴱ)
open import H-level eq
open import H-level.Closure eq
import Integer eq as Data
open import Integer.Quotient.Same-difference eq
open import Nat eq as Nat
  using () renaming (_≤_ to _≤ᴺ_; _<_ to _<ᴺ_)
open import Univalence-axiom eq

private
  module @0 BC {a} =
    Erased.[]-cong₁ (erased-instance-of-[]-cong-axiomatisation {a = a})

private variable
  m m₁ m₂ n n₁ n₂ : ℕ
  p               : Level
  A               : Type _
  i j k           : A

------------------------------------------------------------------------
-- Integers

opaque

  -- Integers.

  ℤ : Type
  ℤ = (ℕ × ℕ) /ᴱ Same-difference

opaque
  unfolding ℤ

  -- Subtracts one natural number from another.

  minus : ℕ × ℕ → ℤ
  minus p = [ p ]

-- Subtracts one natural number from another.

infixl 6 _⊖_

_⊖_ : ℕ → ℕ → ℤ
_⊖_ = curry minus

opaque
  unfolding ℤ

  -- Turns natural numbers into the corresponding integers.

  infix 8 +_

  +_ : ℕ → ℤ
  + n = n ⊖ 0

opaque
  unfolding ℤ

  -- Turns natural numbers into the corresponding negative integers.

  -[_] : ℕ → ℤ
  -[ n ] = 0 ⊖ n

opaque
  unfolding ℤ

  -- The integers form a set.

  @0 ℤ-set : Is-set ℤ
  ℤ-set = Q./ᴱ-is-set

opaque
  unfolding minus

  -- Subtraction of natural numbers respects Same-difference in a
  -- certain way.

  @0 minus-cong : Same-difference i j → minus i ≡ minus j
  minus-cong = []-respects-relation

------------------------------------------------------------------------
-- Some lemmas

opaque
  unfolding Same-difference

  -- A simplification lemma.

  @0 suc-⊖-suc≡ : P.suc m ⊖ P.suc n ≡ m ⊖ n
  suc-⊖-suc≡ {m} = minus-cong (cong P.suc (Nat.+-comm m))

opaque
  unfolding +_ -[_]

  -- The integers + 0 and -[ 0 ] are equal.

  +0≡-0 : + 0 ≡ -[ 0 ]
  +0≡-0 = refl _

opaque
  unfolding Same-difference +_

  -- The integer n ⊖ n is equal to zero.

  @0 ⊖≡0 : n ⊖ n ≡ + 0
  ⊖≡0 = minus-cong (refl _)

------------------------------------------------------------------------
-- Some eliminators

opaque
  unfolding minus-cong

  -- An eliminator.

  elim :
    (P : ℤ → Type p) →
    @0 (∀ i → Is-set (P i)) →
    (f : ∀ i → P (minus i)) →
    @0 (∀ {i j} (s : Same-difference i j) →
        subst P (minus-cong s) (f i) ≡ f j) →
    ∀ i → P i
  elim _ P-set f resp = Q.elim λ where
    .Q.[]ʳ                   → f
    .Q.[]-respects-relationʳ → resp
    .Q.is-setʳ               → P-set

opaque
  unfolding elim

  -- A computation rule for elim.
  --
  -- The computation rule holds by definition if the quotient
  -- eliminator computes for the point constructor.

  elim-minus :
    {P : ℤ → Type p}
    {@0 P-set : ∀ i → Is-set (P i)}
    {f : ∀ i → P (minus i)}
    {@0 resp :
       ∀ {i j} (s : Same-difference i j) →
       subst P (minus-cong s) (f i) ≡ f j} →
    elim P P-set f resp (minus j) ≡ f j
  elim-minus = Q.elim-[]

opaque
  unfolding elim

  -- A recursor.

  rec :
    @0 Is-set A →
    (f : ℕ × ℕ → A) →
    @0 (∀ {i j} → Same-difference i j → f i ≡ f j) →
    ℤ → A
  rec {A} A-set f resp =
    elim _ (λ _ → A-set) f
      (λ {i = i} {j = j} s →
         subst (λ _ → A) (minus-cong s) (f i)  ≡⟨ subst-const _ ⟩
         f i                                   ≡⟨ resp s ⟩∎
         f j                                   ∎)

opaque
  unfolding rec

  -- A computation rule.

  rec-minus :
    {@0 A-set : Is-set A}
    {f : ℕ × ℕ → A}
    {@0 resp : ∀ {i j} (s : Same-difference i j) → f i ≡ f j} →
    rec A-set f resp (minus i) ≡ f i
  rec-minus = elim-minus

opaque
  unfolding elim

  -- An eliminator for propositions.

  elim-prop :
    (P : ℤ → Type p) →
    @0 (∀ i → Is-proposition (P i)) →
    (∀ i → P (minus i)) →
    ∀ i → P i
  elim-prop P P-prop f =
    elim P (mono₁ 1 ∘ P-prop) f (λ _ → P-prop _ _ _)

opaque
  unfolding elim-prop

  -- A computation rule for elim-prop.

  elim-prop-minus :
    {P : ℤ → Type p}
    {@0 P-prop : ∀ i → Is-proposition (P i)}
    {f : ∀ i → P (minus i)} →
    elim-prop P P-prop f (minus i) ≡ f i
  elim-prop-minus = elim-minus

opaque
  unfolding rec

  -- A recursor for propositions.

  rec-prop :
    @0 Is-proposition A →
    (ℕ × ℕ → A) →
    ℤ → A
  rec-prop A-prop f =
    rec (mono₁ 1 A-prop) f (λ _ → A-prop _ _)

opaque
  unfolding rec-prop

  -- A computation rule for rec-prop.

  rec-prop-minus :
    {@0 A-prop : Is-proposition A}
    {f : ℕ × ℕ → A} →
    rec-prop A-prop f (minus i) ≡ f i
  rec-prop-minus = rec-minus

------------------------------------------------------------------------
-- Binary variants of the eliminators

opaque
  unfolding minus-cong

  -- A binary variant of elim.

  elim₂ :
    (P : ℤ → ℤ → Type p) →
    @0 (∀ i j → Is-set (P i j)) →
    (f : ∀ i j → P (minus i) (minus j)) →
    @0 (∀ {i₁ j₁ i₂ j₂}
        (s₁ : Same-difference i₁ j₁)
        (s₂ : Same-difference i₂ j₂) →
        subst (uncurry P) (cong₂ _,_ (minus-cong s₁) (minus-cong s₂))
          (f i₁ i₂) ≡
        f j₁ j₂) →
    ∀ i j → P i j
  elim₂ P P-set = Q.elim₂ P P-set reflexive reflexive
    where
    open Is-equivalence-relation Same-difference-is-equivalence-relation

opaque
  unfolding elim₂

  -- A computation rule for elim₂.

  elim₂-minus :
    {P : ℤ → ℤ → Type p}
    {@0 P-set : ∀ i j → Is-set (P i j)}
    {f : ∀ i j → P (minus i) (minus j)}
    {@0 resp :
       ∀ {i₁ i₂ j₁ j₂}
       (s₁ : Same-difference i₁ j₁)
       (s₂ : Same-difference i₂ j₂) →
       subst (uncurry P) (cong₂ _,_ (minus-cong s₁) (minus-cong s₂))
         (f i₁ i₂) ≡
       f j₁ j₂} →
    elim₂ P P-set f resp (minus i) (minus j) ≡ f i j
  elim₂-minus = Q.elim₂-[]

opaque
  unfolding ℤ

  -- A binary variant of rec.

  rec₂ :
    @0 Is-set A →
    (f : ℕ × ℕ → ℕ × ℕ → A) →
    @0 (∀ {i₁ j₁ i₂ j₂} →
        Same-difference i₁ j₁ →
        Same-difference i₂ j₂ →
        f i₁ i₂ ≡ f j₁ j₂) →
    ℤ → ℤ → A
  rec₂ A-set =
    Q.rec₂ A-set reflexive reflexive
    where
    open Is-equivalence-relation Same-difference-is-equivalence-relation

opaque
  unfolding rec₂ minus

  -- A computation rule for rec₂.

  rec₂-minus :
    {@0 A-set : Is-set A}
    {f : ℕ × ℕ → ℕ × ℕ → A}
    {@0 resp :
        ∀ {i₁ i₂ j₁ j₂} →
        Same-difference i₁ j₁ →
        Same-difference i₂ j₂ →
        f i₁ i₂ ≡ f j₁ j₂} →
    rec₂ A-set f resp (minus i) (minus j) ≡ f i j
  rec₂-minus = Q.rec₂-[]

opaque
  unfolding minus

  -- A binary variant of elim-prop.

  elim-prop₂ :
    (P : ℤ → ℤ → Type p) →
    @0 (∀ i j → Is-proposition (P i j)) →
    (f : ∀ i j → P (minus i) (minus j)) →
    ∀ i j → P i j
  elim-prop₂ = Q.elim-prop₂

opaque
  unfolding elim-prop₂

  -- A computation rule for elim-prop₂.

  elim-prop₂-minus :
    {P : ℤ → ℤ → Type p}
    {@0 P-prop : ∀ i j → Is-proposition (P i j)}
    {f : ∀ i j → P (minus i) (minus j)} →
    elim-prop₂ P P-prop f (minus i) (minus j) ≡ f i j
  elim-prop₂-minus = Q.elim-prop₂-[]

opaque
  unfolding ℤ

  -- A binary variant of rec-prop.

  rec-prop₂ :
    @0 Is-proposition A →
    (ℕ × ℕ → ℕ × ℕ → A) →
    ℤ → ℤ → A
  rec-prop₂ = Q.rec-prop₂

opaque
  unfolding rec-prop₂ minus

  -- A computation rule for rec-prop₂.

  rec-prop₂-minus :
    {@0 A-prop : Is-proposition A}
    {f : ℕ × ℕ → ℕ × ℕ → A} →
    rec-prop₂ A-prop f (minus i) (minus j) ≡ f i j
  rec-prop₂-minus = Q.rec-prop₂-[]

------------------------------------------------------------------------
-- A trinary variant of one eliminator

opaque

  -- A trinary variant of elim-prop.

  elim-prop₃ :
    (P : ℤ → ℤ → ℤ → Type p) →
    @0 (∀ i j k → Is-proposition (P i j k)) →
    (f : ∀ i j k → P (minus i) (minus j) (minus k)) →
    ∀ i j k → P i j k
  elim-prop₃ P P-prop f i j k =
    elim-prop (P i j) (P-prop i j)
      (λ k →
         elim-prop₂ (λ i j → P i j (minus k))
           (λ i j → P-prop i j (minus k)) (λ i j → f i j k) i j)
      k

opaque
  unfolding elim-prop₃

  -- A computation rule for elim-prop₃.

  elim-prop₃-minus :
    {P : ℤ → ℤ → ℤ → Type p}
    {@0 P-prop : ∀ i j k → Is-proposition (P i j k)}
    {f : ∀ i j k → P (minus i) (minus j) (minus k)} →
    elim-prop₃ P P-prop f (minus i) (minus j) (minus k) ≡ f i j k
  elim-prop₃-minus = trans elim-prop-minus elim-prop₂-minus

------------------------------------------------------------------------
-- Functions for defining unary and binary operators

opaque

  -- A function that can be used to define unary operators on
  -- integers.

  unary-operator :
    (f : ℕ × ℕ → ℕ × ℕ) →
    @0 (∀ {i j} →
        Same-difference i j →
        Same-difference (f i) (f j)) →
    ℤ → ℤ
  unary-operator f resp =
    rec ℤ-set (minus ∘ f) (minus-cong ∘ resp)

opaque
  unfolding unary-operator

  -- A computation rule for unary-operator.

  unary-operator-minus :
    {f : ℕ × ℕ → ℕ × ℕ}
    {@0 resp :
       ∀ {i j} →
       Same-difference i j →
       Same-difference (f i) (f j)} →
    unary-operator f resp (minus i) ≡ minus (f i)
  unary-operator-minus = rec-minus

opaque

  -- A function that can be used to define binary operators on
  -- integers.

  binary-operator :
    (f : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ) →
    @0 (∀ {i₁ i₂ j₁ j₂} →
        Same-difference i₁ i₂ →
        Same-difference j₁ j₂ →
        Same-difference (f i₁ j₁) (f i₂ j₂)) →
    ℤ → ℤ → ℤ
  binary-operator f resp =
    rec₂ ℤ-set (λ i j → minus (f i j))
      (λ s₁ s₂ → minus-cong (resp s₁ s₂))

opaque
  unfolding binary-operator

  -- A computation rule for binary-operator.

  binary-operator-minus :
    {f : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ}
    {@0 resp :
       ∀ {i₁ i₂ j₁ j₂} →
       Same-difference i₁ i₂ →
       Same-difference j₁ j₂ →
       Same-difference (f i₁ j₁) (f i₂ j₂)} →
    binary-operator f resp (minus i) (minus j) ≡ minus (f i j)
  binary-operator-minus = rec₂-minus

------------------------------------------------------------------------
-- A one-to-one correspondence between two definitions of integers

opaque
  unfolding Same-difference +_ -[_]

  -- There is an equivalence with one erased proof between the variant
  -- of integers in Integer and the variant defined here.

  ℤ≃ᴱ′ℤ : Data.ℤ ≃ᴱ′ ℤ
  ℤ≃ᴱ′ℤ = EEq.↔→≃ᴱ′ to from to∘from from∘to
    where
    from-lemma₁ :
      m₁ ⊕ P.suc n₂ ≡ m₂ →
      (Data.+ m₁) ≡ Data.+ m₂ +-[1+ n₂ ]
    from-lemma₁ {m₁} {n₂} {m₂ = zero} hyp =
      ⊥-elim $
      Nat.0≢+
        (zero             ≡⟨ sym hyp ⟩
         m₁ ⊕ P.suc n₂    ≡⟨ sym $ Nat.suc+≡+suc m₁ ⟩∎
         P.suc (m₁ ⊕ n₂)  ∎)
    from-lemma₁ {m₁} {n₂ = zero} {m₂ = P.suc m₂} hyp =
      cong (Data.+_) $
      Nat.cancel-suc
        (P.suc m₁  ≡⟨ Nat.+-comm 1 ⟩
         m₁ ⊕ 1    ≡⟨ hyp ⟩∎
         P.suc m₂  ∎)
    from-lemma₁ {m₁} {n₂ = P.suc n₂} {m₂ = P.suc m₂} hyp =
      from-lemma₁ $
      Nat.cancel-suc
        (P.suc (m₁ ⊕ P.suc n₂)  ≡⟨ Nat.suc+≡+suc m₁ ⟩
         m₁ ⊕ P.suc (P.suc n₂)  ≡⟨ hyp ⟩∎
         P.suc m₂               ∎)

    from-lemma₂ :
      m₁ ⊕ zero ≡ P.suc n₁ ⊕ m₂ →
      Data.+ m₁ +-[1+ n₁ ] ≡ Data.+ m₂
    from-lemma₂ {m₁ = zero} hyp =
      ⊥-elim $ Nat.0≢+ hyp
    from-lemma₂ {m₁ = P.suc m₁} {n₁ = zero} {m₂} hyp =
      cong (Data.+_) $
      Nat.cancel-suc
        (P.suc m₁      ≡⟨ sym Nat.+-right-identity ⟩
         P.suc m₁ ⊕ 0  ≡⟨ hyp ⟩∎
         P.suc m₂      ∎)
    from-lemma₂ {m₁ = P.suc m₁} {n₁ = P.suc n₁} hyp =
      from-lemma₂ (Nat.cancel-suc hyp)

    from-lemma₃ :
      ∀ m₁ n₁ m₂ n₂ →
      m₁ ⊕ P.suc n₂ ≡ P.suc n₁ ⊕ m₂ →
      Data.+ m₁ +-[1+ n₁ ] ≡ Data.+ m₂ +-[1+ n₂ ]
    from-lemma₃ (P.suc m₁) (P.suc n₁) m₂ n₂ hyp =
      from-lemma₃ m₁ n₁ m₂ n₂ (Nat.cancel-suc hyp)
    from-lemma₃ m₁ n₁ (P.suc m₂) (P.suc n₂) hyp =
      from-lemma₃ m₁ n₁ m₂ n₂ $
      Nat.cancel-suc
        (P.suc (m₁ ⊕ P.suc n₂)  ≡⟨ Nat.suc+≡+suc m₁ ⟩
         m₁ ⊕ P.suc (P.suc n₂)  ≡⟨ hyp ⟩
         P.suc n₁ ⊕ P.suc m₂    ≡⟨ cong P.suc $ sym $ Nat.suc+≡+suc n₁ ⟩∎
         P.suc (P.suc n₁ ⊕ m₂)  ∎)
    from-lemma₃ zero n₁ zero n₂ hyp =
      cong Data.-[1+_] $
      Nat.cancel-suc
        (P.suc n₁      ≡⟨ sym Nat.+-right-identity ⟩
         P.suc n₁ ⊕ 0  ≡⟨ sym hyp ⟩∎
         P.suc n₂      ∎)
    from-lemma₃ (P.suc m₁) zero (P.suc m₂) zero hyp =
      cong (Data.+_) $
      Nat.cancel-suc $
        (P.suc m₁  ≡⟨ Nat.+-comm 1 ⟩
         m₁ ⊕ 1    ≡⟨ Nat.cancel-suc hyp ⟩∎
         P.suc m₂  ∎)
    from-lemma₃ (P.suc m₁) zero zero n₂ hyp =
      ⊥-elim $ Nat.0≢+
        (0                ≡⟨ sym $ Nat.cancel-suc hyp ⟩
         m₁ ⊕ P.suc n₂    ≡⟨ sym $ Nat.suc+≡+suc m₁ ⟩∎
         P.suc (m₁ ⊕ n₂)  ∎)
    from-lemma₃ zero n₁ (P.suc m₂) zero hyp =
      ⊥-elim $ Nat.0≢+
        (0                ≡⟨ Nat.cancel-suc hyp ⟩
         n₁ ⊕ P.suc m₂    ≡⟨ sym $ Nat.suc+≡+suc n₁ ⟩∎
         P.suc (n₁ ⊕ m₂)  ∎)

    from-lemma :
      ∀ m₁ n₁ m₂ n₂ →
      Same-difference (m₁ , n₁) (m₂ , n₂) →
      Data.+ m₁ Data.- Data.+ n₁ ≡
      Data.+ m₂ Data.- Data.+ n₂
    from-lemma m₁ zero m₂ zero hyp =
      Data.+ (m₁ ⊕ 0)  ≡⟨ cong Data.+_ hyp ⟩
      Data.+ m₂        ≡⟨ cong Data.+_ (sym Nat.+-right-identity) ⟩∎
      Data.+ (m₂ ⊕ 0)  ∎
    from-lemma m₁ zero m₂ (P.suc n₂) hyp =
      Data.+ (m₁ ⊕ 0)       ≡⟨ cong Data.+_ Nat.+-right-identity ⟩
      Data.+ m₁             ≡⟨ from-lemma₁ hyp ⟩∎
      Data.+ m₂ +-[1+ n₂ ]  ∎
    from-lemma m₁ (P.suc n₁) m₂ zero hyp =
      Data.+ m₁ +-[1+ n₁ ]  ≡⟨ from-lemma₂ hyp ⟩
      Data.+ m₂             ≡⟨ cong Data.+_ (sym Nat.+-right-identity) ⟩∎
      Data.+ (m₂ ⊕ 0)       ∎
    from-lemma m₁ (P.suc n₁) m₂ (P.suc n₂) hyp =
      Data.+ m₁ +-[1+ n₁ ]  ≡⟨ from-lemma₃ _ _ _ _ hyp ⟩∎
      Data.+ m₂ +-[1+ n₂ ]  ∎

    from : ℤ → Data.ℤ
    from =
      rec Data.ℤ-set (λ (m , n) → Data.+ m Data.- Data.+ n)
        (λ @0 { {i = m₁ , n₁} {j = m₂ , n₂} → from-lemma m₁ n₁ m₂ n₂ })

    to : Data.ℤ → ℤ
    to (Data.+ n)    = + n
    to Data.-[1+ n ] = -[ P.suc n ]

    from∘to : ∀ i → from (to i) ≡ i
    from∘to (Data.+ n) =
      from (to (Data.+ n))  ≡⟨ rec-minus ⟩
      Data.+ (n ⊕ 0)        ≡⟨ cong Data.+_ Nat.+-right-identity ⟩∎
      Data.+ n              ∎
    from∘to Data.-[1+ n ] =
      from (to Data.-[1+ n ])  ≡⟨ rec-minus ⟩
      Data.-[1+ n ]            ∎

    @0 to-+_+-[1+_] :
      ∀ m n → to (Data.+ m +-[1+ n ]) ≡ m ⊖ P.suc n
    to-+ zero    +-[1+ n ]       = refl _
    to-+ P.suc m +-[1+ zero ]    = sym suc-⊖-suc≡
    to-+ P.suc m +-[1+ P.suc n ] =
      to (Data.+ P.suc m +-[1+ P.suc n ])  ≡⟨⟩
      to (Data.+ m +-[1+ n ])              ≡⟨ to-+ m +-[1+ n ] ⟩
      m ⊖ P.suc n                ≡⟨ sym suc-⊖-suc≡ ⟩∎
      P.suc m ⊖ P.suc (P.suc n)  ∎

    @0 to∘from : ∀ i → to (from i) ≡ i
    to∘from =
      elim-prop _ (λ _ → ℤ-set) λ where
        (m , zero) →
          to (from (+ m))  ≡⟨ cong to rec-minus ⟩
          + (m ⊕ 0)        ≡⟨ cong +_ Nat.+-right-identity ⟩∎
          + m              ∎
        (m , P.suc n) →
          to (from (m ⊖ P.suc n))  ≡⟨ cong to rec-minus ⟩
          to (Data.+ m +-[1+ n ])  ≡⟨ to-+ m +-[1+ n ] ⟩∎
          m ⊖ P.suc n              ∎

opaque
  unfolding ℤ≃ᴱ′ℤ

  -- There is an equivalence with erased proofs between this variant of
  -- integers and the one in Integer.

  ℤ≃ᴱℤ : ℤ ≃ᴱ Data.ℤ
  ℤ≃ᴱℤ = inverse (_≃ᴱ′_.equivalence-with-erased-proofs ℤ≃ᴱ′ℤ)

opaque
  unfolding ℤ≃ᴱℤ

  -- The equivalence is homomorphic with respect to +_/Data.+_.

  ℤ≃ᴱℤ-+ : _≃ᴱ_.to ℤ≃ᴱℤ (+ n) ≡ Data.+ n
  ℤ≃ᴱℤ-+ {n} =
    _≃ᴱ_.to ℤ≃ᴱℤ (+ n)  ≡⟨ rec-minus ⟩
    Data.+ (n ⊕ 0)      ≡⟨ cong Data.+_ Nat.+-right-identity ⟩∎
    Data.+ n            ∎

opaque
  unfolding ℤ≃ᴱℤ -[_]

  -- The bijection is homomorphic with respect to -[_]/Data.-[_].

  ℤ≃ᴱℤ-- : _≃ᴱ_.to ℤ≃ᴱℤ -[ n ] ≡ Data.-[ n ]
  ℤ≃ᴱℤ-- {n = zero} =
    _≃ᴱ_.to ℤ≃ᴱℤ -[ zero ]  ≡⟨ rec-minus ⟩∎
    Data.+ 0                ∎
  ℤ≃ᴱℤ-- {n = P.suc n} =
    _≃ᴱ_.to ℤ≃ᴱℤ -[ P.suc n ]  ≡⟨ rec-minus ⟩∎
    Data.-[1+ n ]              ∎

------------------------------------------------------------------------
-- Negation

opaque

  -- Negation.

  infix 8 -_

  -_ : ℤ → ℤ
  -_ = unary-operator swap Same-difference-swap

opaque
  unfolding -_

  -- A computation rule for -_.

  -⊖ : - (m ⊖ n) ≡ n ⊖ m
  -⊖ = unary-operator-minus

opaque
  unfolding ℤ≃ᴱℤ

  -- The implementation of negation given here matches the one in
  -- Integer.

  -₁≡-₁ : ∀ i → - (_≃ᴱ_.from ℤ≃ᴱℤ i) ≡ _≃ᴱ_.from ℤ≃ᴱℤ (Data.- i)
  -₁≡-₁ (Data.+ zero)      = -⊖
  -₁≡-₁ (Data.+ (P.suc _)) = -⊖
  -₁≡-₁ Data.-[1+ _ ]      = -⊖

opaque
  unfolding +_ -[_]

  -- A simplification lemma.

  -+ : - (+ n) ≡ -[ n ]
  -+ = -⊖

opaque
  unfolding +_ -[_]

  -- A simplification lemma.

  -‿- : - -[ n ] ≡ + n
  -‿- = -⊖

------------------------------------------------------------------------
-- Addition

opaque
  unfolding Same-difference

  -- Addition.

  infixl 6 _+_

  _+_ : ℤ → ℤ → ℤ
  _+_ = binary-operator
    (Σ-zip _⊕_ _⊕_)
    (λ @0 where
       {i₁ = k₁ , k₂} {i₂ = ℓ₁ , ℓ₂} {j₁ = m₁ , m₂} {j₂ = n₁ , n₂}
         hyp₁ hyp₂ →
         (k₁ ⊕ m₁) ⊕ (ℓ₂ ⊕ n₂)  ≡⟨ lemma k₁ ⟩
         (k₁ ⊕ ℓ₂) ⊕ (m₁ ⊕ n₂)  ≡⟨ cong₂ _⊕_ hyp₁ hyp₂ ⟩
         (k₂ ⊕ ℓ₁) ⊕ (m₂ ⊕ n₁)  ≡⟨ lemma k₂ ⟩∎
         (k₂ ⊕ m₂) ⊕ (ℓ₁ ⊕ n₁)  ∎)
    where
    lemma : ∀ a {b c d} → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
    lemma a {b} {c} {d} =
      (a ⊕ b) ⊕ (c ⊕ d)  ≡⟨ sym $ Nat.+-assoc a ⟩
      a ⊕ (b ⊕ (c ⊕ d))  ≡⟨ cong (a ⊕_) $ Nat.+-assoc b ⟩
      a ⊕ ((b ⊕ c) ⊕ d)  ≡⟨ cong ((a ⊕_) ∘ (_⊕ d)) $ Nat.+-comm b ⟩
      a ⊕ ((c ⊕ b) ⊕ d)  ≡⟨ cong (a ⊕_) $ sym $ Nat.+-assoc c ⟩
      a ⊕ (c ⊕ (b ⊕ d))  ≡⟨ Nat.+-assoc a ⟩∎
      (a ⊕ c) ⊕ (b ⊕ d)  ∎

opaque
  unfolding _+_

  -- A computation rule for _+_.

  ⊖+⊖ : (m₁ ⊖ n₁) + (m₂ ⊖ n₂) ≡ (m₁ ⊕ m₂) ⊖ (n₁ ⊕ n₂)
  ⊖+⊖ = binary-operator-minus

opaque
  unfolding +_

  -- A simplification lemma.

  +++ : + m + + n ≡ + (m ⊕ n)
  +++ = ⊖+⊖

opaque
  unfolding +_ -[_]

  -- A simplification lemma.

  ++- : + m + -[ n ] ≡ m ⊖ n
  ++- {m} {n} =
    (m ⊖ 0) + (0 ⊖ n)  ≡⟨ ⊖+⊖ ⟩
    (m ⊕ 0) ⊖ (0 ⊕ n)  ≡⟨ cong (_⊖ _) Nat.+-right-identity ⟩∎
    m ⊖ n              ∎

opaque
  unfolding +_ -[_]

  -- A simplification lemma.

  -++ : -[ m ] + + n ≡ n ⊖ m
  -++ {m} {n} =
    (0 ⊖ m) + (n ⊖ 0)  ≡⟨ ⊖+⊖ ⟩
    (0 ⊕ n) ⊖ (m ⊕ 0)  ≡⟨ cong (_ ⊖_) Nat.+-right-identity ⟩∎
    n ⊖ m              ∎

opaque
  unfolding +_ -[_]

  -- A simplification lemma.

  -+- : -[ m ] + -[ n ] ≡ -[ m ⊕ n ]
  -+- = ⊖+⊖

opaque

  -- Negation commutes with addition.

  -‿commutes‿+ : - i + - j ≡ - (i + j)
  -‿commutes‿+ =
    elim-prop₂ (λ i j → - i + - j ≡ - (i + j))
      (λ _ _ → ℤ-set)
      (λ (m₁ , n₁) (m₂ , n₂) →
         - (m₁ ⊖ n₁) + - (m₂ ⊖ n₂)  ≡⟨ cong₂ _+_ -⊖ -⊖ ⟩
         (n₁ ⊖ m₁) + (n₂ ⊖ m₂)      ≡⟨ ⊖+⊖ ⟩
         (n₁ ⊕ n₂) ⊖ (m₁ ⊕ m₂)      ≡⟨ sym -⊖ ⟩
         - ((m₁ ⊕ m₂) ⊖ (n₁ ⊕ n₂))  ≡⟨ cong -_ (sym ⊖+⊖) ⟩∎
         - ((m₁ ⊖ n₁) + (m₂ ⊖ n₂))  ∎)
      _ _

opaque
  unfolding ℤ≃ᴱℤ

  -- A lemma used in the implementation of +≡+.

  @0 ⊖1+≡++-[1+] : m ⊖ P.suc n ≡ _≃ᴱ_.from ℤ≃ᴱℤ (Data.+ m +-[1+ n ])
  ⊖1+≡++-[1+] {m = zero} {n} =
    0 ⊖ P.suc n  ∎
  ⊖1+≡++-[1+] {m = P.suc m} {n = zero} =
    P.suc m ⊖ 1  ≡⟨ suc-⊖-suc≡ ⟩∎
    m ⊖ 0        ∎
  ⊖1+≡++-[1+] {m = P.suc m} {n = P.suc n} =
    P.suc m ⊖ P.suc (P.suc n)                        ≡⟨ suc-⊖-suc≡ ⟩
    m ⊖ P.suc n                                      ≡⟨ ⊖1+≡++-[1+] ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ (Data.+ m +-[1+ n ])              ≡⟨⟩
    _≃ᴱ_.from ℤ≃ᴱℤ (Data.+ P.suc m +-[1+ P.suc n ])  ∎

opaque
  unfolding ℤ≃ᴱℤ

  -- The implementation of addition given here matches the one in
  -- Integer.

  @0 +≡+ :
    ∀ i →
    (_≃ᴱ_.from ℤ≃ᴱℤ i) + (_≃ᴱ_.from ℤ≃ᴱℤ j) ≡
    _≃ᴱ_.from ℤ≃ᴱℤ (i Data.+ j)
  +≡+ {j = Data.+ n} (Data.+ m) =
    + m + + n  ≡⟨ +++ ⟩∎
    + (m ⊕ n)  ∎
  +≡+ {j = Data.-[1+ n ]} (Data.+ m) =
    + m + -[ P.suc n ]                   ≡⟨ ++- ⟩
    m ⊖ P.suc n                          ≡⟨ ⊖1+≡++-[1+] ⟩∎
    _≃ᴱ_.from ℤ≃ᴱℤ (Data.+ m +-[1+ n ])  ∎
  +≡+ {j = Data.+ n} Data.-[1+ m ] =
    -[ P.suc m ] + + n                   ≡⟨ -++ ⟩
    n ⊖ P.suc m                          ≡⟨ ⊖1+≡++-[1+] ⟩∎
    _≃ᴱ_.from ℤ≃ᴱℤ (Data.+ n +-[1+ m ])  ∎
  +≡+ {j = Data.-[1+ n ]} Data.-[1+ m ] =
    -[ P.suc m ] + -[ P.suc n ]  ≡⟨ -+- ⟩
    -[ P.suc (m ⊕ P.suc n) ]     ≡⟨ cong (-[_] ∘ P.suc) $ sym $ Nat.suc+≡+suc _ ⟩∎
    -[ P.suc (P.suc (m ⊕ n)) ]   ∎

------------------------------------------------------------------------
-- Subtraction

opaque

  -- Subtraction.

  infixl 6 _-_

  _-_ : ℤ → ℤ → ℤ
  i - j = i + - j

opaque
  unfolding _-_

  -- A computation rule for _-_.

  ⊖-⊖ : (m₁ ⊖ n₁) - (m₂ ⊖ n₂) ≡ (m₁ ⊕ n₂) ⊖ (n₁ ⊕ m₂)
  ⊖-⊖ = trans (cong (_+_ _) -⊖) ⊖+⊖

opaque
  unfolding _-_

  -- A simplification lemma.

  +-+ : + m - + n ≡ m ⊖ n
  +-+ {m} {n} =
    + m + - + n   ≡⟨ cong (_+_ _) -+ ⟩
    + m + -[ n ]  ≡⟨ ++- ⟩
    m ⊖ n         ∎

opaque
  unfolding _-_

  -- A simplification lemma.

  +-- : + m - -[ n ] ≡ + (m ⊕ n)
  +-- {m} {n} =
    + m + - -[ n ]  ≡⟨ cong (_+_ _) -‿- ⟩
    + m + + n       ≡⟨ +++ ⟩
    + (m ⊕ n)       ∎

opaque
  unfolding _-_

  -- A simplification lemma.

  -‿-‿+ : -[ m ] - + n ≡ -[ m ⊕ n ]
  -‿-‿+ {m} {n} =
    -[ m ] + - + n   ≡⟨ cong (_+_ _) -+ ⟩
    -[ m ] + -[ n ]  ≡⟨ -+- ⟩
    -[ m ⊕ n ]       ∎

opaque
  unfolding _-_

  -- A simplification lemma.

  -‿-‿- : -[ m ] - -[ n ] ≡ n ⊖ m
  -‿-‿- {m} {n} =
    -[ m ] + - -[ n ]  ≡⟨ cong (_+_ _) -‿- ⟩
    -[ m ] + + n       ≡⟨ -++ ⟩
    n ⊖ m              ∎

opaque
  unfolding _-_

  -- The implementation of subtraction given here matches the one in
  -- Integer.

  @0 -≡- :
    ∀ i j →
    (_≃ᴱ_.from ℤ≃ᴱℤ i) - (_≃ᴱ_.from ℤ≃ᴱℤ j) ≡
    _≃ᴱ_.from ℤ≃ᴱℤ (i Data.- j)
  -≡- i j =
    (_≃ᴱ_.from ℤ≃ᴱℤ i) - (_≃ᴱ_.from ℤ≃ᴱℤ j)       ≡⟨⟩
    (_≃ᴱ_.from ℤ≃ᴱℤ i) + - (_≃ᴱ_.from ℤ≃ᴱℤ j)     ≡⟨ cong (λ j → _≃ᴱ_.from ℤ≃ᴱℤ i + j) $ -₁≡-₁ j ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ i + _≃ᴱ_.from ℤ≃ᴱℤ (Data.- j)  ≡⟨ +≡+ i ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ (i Data.+ Data.- j)            ≡⟨⟩
    _≃ᴱ_.from ℤ≃ᴱℤ (i Data.- j)                   ∎

------------------------------------------------------------------------
-- The successor and predecessor functions

opaque
  unfolding Same-difference

  -- The successor function.

  suc : ℤ → ℤ
  suc =
    unary-operator (Σ-map P.suc id)
      (λ @0 where
         {i = m₁ , m₂} {j = n₁ , n₂} hyp →
           P.suc (m₁ ⊕ n₂)  ≡⟨ cong P.suc hyp ⟩
           P.suc (m₂ ⊕ n₁)  ≡⟨ Nat.suc+≡+suc _ ⟩∎
           m₂ ⊕ P.suc n₁    ∎)

opaque
  unfolding suc

  -- A computation rule for suc.

  suc-⊖ : suc (m ⊖ n) ≡ P.suc m ⊖ n
  suc-⊖ = unary-operator-minus

opaque
  unfolding +_

  -- A simplification lemma.

  suc-+ : suc (+ n) ≡ + P.suc n
  suc-+ = suc-⊖

opaque
  unfolding -[_]

  -- A simplification lemma.

  @0 suc-- : suc -[ P.suc n ] ≡ -[ n ]
  suc-- {n} =
    suc (0 ⊖ P.suc n)  ≡⟨ suc-⊖ ⟩
    1 ⊖ P.suc n        ≡⟨ suc-⊖-suc≡ ⟩∎
    0 ⊖ n              ∎

opaque
  unfolding +_

  -- The function suc adds one to its input.

  suc≡1+ : ∀ i → suc i ≡ + 1 + i
  suc≡1+ =
    elim-prop _ (λ _ → ℤ-set) (λ _ → trans suc-⊖ (sym ⊖+⊖))

opaque
  unfolding Same-difference

  -- The predecessor function.

  pred : ℤ → ℤ
  pred =
    unary-operator (Σ-map id P.suc)
      (λ @0 where
         {i = m₁ , m₂} {j = n₁ , n₂} hyp →
           m₁ ⊕ P.suc n₂    ≡⟨ sym $ Nat.suc+≡+suc _ ⟩
           P.suc (m₁ ⊕ n₂)  ≡⟨ cong P.suc hyp ⟩∎
           P.suc (m₂ ⊕ n₁)  ∎)

opaque
  unfolding pred

  -- A computation rule for pred.

  pred-⊖ : pred (m ⊖ n) ≡ m ⊖ P.suc n
  pred-⊖ = unary-operator-minus

opaque
  unfolding -[_]

  -- A simplification lemma.

  pred-- : pred -[ n ] ≡ -[ P.suc n ]
  pred-- = pred-⊖

opaque
  unfolding +_

  -- A simplification lemma.

  @0 pred-+ : pred (+ P.suc n) ≡ + n
  pred-+ {n} =
    pred (P.suc n ⊖ 0)  ≡⟨ pred-⊖ ⟩
    P.suc n ⊖ 1         ≡⟨ suc-⊖-suc≡ ⟩∎
    n ⊖ 0               ∎

opaque
  unfolding pred -[_]

  -- The function pred subtracts one from its input.

  pred≡-1+ : ∀ i → pred i ≡ -[ 1 ] + i
  pred≡-1+ =
    elim-prop _ (λ _ → ℤ-set) (λ _ → trans pred-⊖ (sym ⊖+⊖))

opaque

  -- An equivalence (with erased proofs) between ℤ and ℤ corresponding
  -- to the successor function.

  successor : ℤ ≃ᴱ ℤ
  successor =
    EEq.↔→≃ᴱ suc pred
      (elim-prop _ (λ _ → ℤ-set)
         (λ i →
            suc (pred (minus i))         ≡⟨ trans (cong suc pred-⊖) suc-⊖ ⟩
            minus (Σ-map P.suc P.suc i)  ≡⟨ suc-⊖-suc≡ ⟩∎
            minus i                      ∎))
      (elim-prop _ (λ _ → ℤ-set)
         (λ i →
            pred (suc (minus i))         ≡⟨ trans (cong pred suc-⊖) pred-⊖ ⟩
            minus (Σ-map P.suc P.suc i)  ≡⟨ suc-⊖-suc≡ ⟩∎
            minus i                      ∎))

------------------------------------------------------------------------
-- Multiplication

opaque

  -- Multiplication.

  infixl 7 _*_

  _*_ : ℤ → ℤ → ℤ
  _*_ = binary-operator mul Same-difference-multiplication-lemma
    where
    mul : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
    mul (m₁ , n₁) (m₂ , n₂) = m₁ ⊛ m₂ ⊕ n₁ ⊛ n₂ , m₁ ⊛ n₂ ⊕ n₁ ⊛ m₂

opaque
  unfolding _*_

  -- A computation rule for _+_.

  ⊖*⊖ :
    (m₁ ⊖ n₁) * (m₂ ⊖ n₂) ≡
    (m₁ ⊛ m₂ ⊕ n₁ ⊛ n₂) ⊖ (m₁ ⊛ n₂ ⊕ n₁ ⊛ m₂)
  ⊖*⊖ = binary-operator-minus

opaque

  -- Multiplication is commutative.

  *-comm : i * j ≡ j * i
  *-comm =
    elim-prop₂ (λ i j → i * j ≡ j * i) (λ _ _ → ℤ-set)
      (λ (m₁ , n₁) (m₂ , n₂) →
         (m₁ ⊖ n₁) * (m₂ ⊖ n₂)                      ≡⟨ ⊖*⊖ ⟩
         (m₁ ⊛ m₂ ⊕ n₁ ⊛ n₂) ⊖ (m₁ ⊛ n₂ ⊕ n₁ ⊛ m₂)  ≡⟨ cong₂ _⊖_ (cong₂ _⊕_ (Nat.*-comm m₁) (Nat.*-comm n₁))
                                                         (trans (cong₂ _⊕_ (Nat.*-comm m₁) (Nat.*-comm n₁))
                                                            (Nat.+-comm (n₂ ⊛ _))) ⟩
         (m₂ ⊛ m₁ ⊕ n₂ ⊛ n₁) ⊖ (m₂ ⊛ n₁ ⊕ n₂ ⊛ m₁)  ≡⟨ sym ⊖*⊖ ⟩∎
         (m₂ ⊖ n₂) * (m₁ ⊖ n₁)                      ∎)
      _ _

opaque
  unfolding +_

  -- + 0 is a left zero for multiplication.

  *-left-zero : + 0 * i ≡ + 0
  *-left-zero =
    elim-prop (λ i → + 0 * i ≡ + 0) (λ _ → ℤ-set)
      (λ (m , n) →
         (0 ⊖ 0) * (m ⊖ n)  ≡⟨ ⊖*⊖ ⟩∎
         0 ⊖ 0              ∎)
      _

opaque

  -- + 0 is a right zero for multiplication.

  *-right-zero : i * + 0 ≡ + 0
  *-right-zero {i} =
    i * + 0  ≡⟨ *-comm ⟩
    + 0 * i  ≡⟨ *-left-zero ⟩
    + 0      ∎

opaque

  -- A lemma relating multiplication and negation.

  *-≡-* : i * - j ≡ - i * j
  *-≡-* =
    elim-prop₂ (λ i j → i * - j ≡ - i * j) (λ _ _ → ℤ-set)
      (λ (m₁ , n₁) (m₂ , n₂) →
         (m₁ ⊖ n₁) * - (m₂ ⊖ n₂)                    ≡⟨ trans (cong (_ *_) -⊖) ⊖*⊖ ⟩
         (m₁ ⊛ n₂ ⊕ n₁ ⊛ m₂) ⊖ (m₁ ⊛ m₂ ⊕ n₁ ⊛ n₂)  ≡⟨ cong₂ _⊖_ (Nat.+-comm (m₁ ⊛ _)) (Nat.+-comm (m₁ ⊛ _)) ⟩
         (n₁ ⊛ m₂ ⊕ m₁ ⊛ n₂) ⊖ (n₁ ⊛ n₂ ⊕ m₁ ⊛ m₂)  ≡⟨ sym (trans (cong (_* _) -⊖) ⊖*⊖) ⟩∎
         - (m₁ ⊖ n₁) * (m₂ ⊖ n₂)                    ∎)
      _ _

opaque

  -- A "computation rule" for multiplication.

  suc-* : suc i * j ≡ j + i * j
  suc-* =
    elim-prop₂ (λ i j → suc i * j ≡ j + i * j) (λ _ _ → ℤ-set)
      (λ (m₁ , n₁) (m₂ , n₂) →
         suc (m₁ ⊖ n₁) * (m₂ ⊖ n₂)                                ≡⟨ trans (cong (_* _) suc-⊖) ⊖*⊖ ⟩
         (P.suc m₁ ⊛ m₂ ⊕ n₁ ⊛ n₂) ⊖ (P.suc m₁ ⊛ n₂ ⊕ n₁ ⊛ m₂)    ≡⟨⟩
         (m₂ ⊕ m₁ ⊛ m₂ ⊕ n₁ ⊛ n₂) ⊖ (n₂ ⊕ m₁ ⊛ n₂ ⊕ n₁ ⊛ m₂)      ≡⟨ sym (cong₂ _⊖_ (Nat.+-assoc m₂) (Nat.+-assoc n₂)) ⟩
         (m₂ ⊕ (m₁ ⊛ m₂ ⊕ n₁ ⊛ n₂)) ⊖ (n₂ ⊕ (m₁ ⊛ n₂ ⊕ n₁ ⊛ m₂))  ≡⟨ sym (trans (cong (_+_ _) ⊖*⊖) ⊖+⊖) ⟩∎
         (m₂ ⊖ n₂) + (m₁ ⊖ n₁) * (m₂ ⊖ n₂)                        ∎)
      _ _

opaque

  -- A "computation rule" for multiplication.

  *-suc : i * suc j ≡ i + i * j
  *-suc {i} {j} =
    i * suc j  ≡⟨ *-comm ⟩
    suc j * i  ≡⟨ suc-* ⟩
    i + j * i  ≡⟨ cong (_+_ _) *-comm ⟩
    i + i * j  ∎

opaque

  -- A "computation rule" for multiplication.

  neg-suc-* : - suc i * j ≡ - j + - i * j
  neg-suc-* {i} {j} =
    - suc i * j    ≡⟨ sym *-≡-* ⟩
    suc i * - j    ≡⟨ suc-* ⟩
    - j + i * - j  ≡⟨ cong (_+_ _) *-≡-* ⟩
    - j + - i * j  ∎

opaque

  -- A "computation rule" for multiplication.

  *-neg-suc : i * - suc j ≡ - i + i * - j
  *-neg-suc {i} {j} =
    i * - suc j    ≡⟨ *-comm ⟩
    - suc j * i    ≡⟨ neg-suc-* ⟩
    - i + - j * i  ≡⟨ cong (_+_ _) *-comm ⟩
    - i + i * - j  ∎

private opaque
  unfolding ℤ≃ᴱℤ

  -- A lemma used in the implementation of *≡*.

  @0 *+≡*+ :
    ∀ {i} n →
    _≃ᴱ_.from ℤ≃ᴱℤ i * + n ≡
    _≃ᴱ_.from ℤ≃ᴱℤ (i Data.*+ n)
  *+≡*+ {i} zero =
    _≃ᴱ_.from ℤ≃ᴱℤ i * + 0  ≡⟨ *-right-zero ⟩
    + 0                     ∎
  *+≡*+ {i} (P.suc n) =
    _≃ᴱ_.from ℤ≃ᴱℤ i * + P.suc n                     ≡⟨ cong (_ *_) (sym suc-+) ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ i * suc (+ n)                     ≡⟨ *-suc ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ i + _≃ᴱ_.from ℤ≃ᴱℤ i * + n        ≡⟨ cong (_+_ _) (*+≡*+ n) ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ i + _≃ᴱ_.from ℤ≃ᴱℤ (i Data.*+ n)  ≡⟨ +≡+ i ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ (i Data.+ i Data.*+ n)            ∎

opaque
  unfolding ℤ≃ᴱℤ

  -- The implementation of multiplication given here matches the one
  -- in Integer.

  @0 *≡* :
    ∀ j →
    _≃ᴱ_.from ℤ≃ᴱℤ i * _≃ᴱ_.from ℤ≃ᴱℤ j ≡ _≃ᴱ_.from ℤ≃ᴱℤ (i Data.* j)
  *≡* (Data.+ n) =
    *+≡*+ n
  *≡* {i} Data.-[1+ n ] =
    _≃ᴱ_.from ℤ≃ᴱℤ i * -[ P.suc n ]                                  ≡⟨ cong (_ *_) (sym -+) ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ i * - (+ P.suc n)                                 ≡⟨ cong ((_ *_) ∘ -_) (sym suc-+) ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ i * - suc (+ n)                                   ≡⟨ *-neg-suc ⟩
    - _≃ᴱ_.from ℤ≃ᴱℤ i + _≃ᴱ_.from ℤ≃ᴱℤ i * - + n                    ≡⟨ cong (_+_ _) *-≡-* ⟩
    - _≃ᴱ_.from ℤ≃ᴱℤ i + - _≃ᴱ_.from ℤ≃ᴱℤ i * + n                    ≡⟨ cong (_+_ _) $ cong (_* _) $ -₁≡-₁ i ⟩
    - _≃ᴱ_.from ℤ≃ᴱℤ i + _≃ᴱ_.from ℤ≃ᴱℤ (Data.- i) * + n             ≡⟨ cong₂ _+_ (-₁≡-₁ i) (*+≡*+ n) ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ (Data.- i) + _≃ᴱ_.from ℤ≃ᴱℤ (Data.- i Data.*+ n)  ≡⟨ +≡+ (Data.- i) ⟩
    _≃ᴱ_.from ℤ≃ᴱℤ (Data.- i Data.+ Data.- i Data.*+ n)              ≡⟨⟩
    _≃ᴱ_.from ℤ≃ᴱℤ (Data.- i Data.*+ P.suc n)                        ∎

------------------------------------------------------------------------
-- Effectiveness

-- One can prove effectiveness using propositional extensionality and
-- function extensionality, but also without those assumptions (see
-- below).

module Effectiveness
  (@0 ext      : Extensionality (lsuc lzero) (lsuc lzero))
  (@0 prop-ext : Propositional-extensionality lzero)
  where

  opaque
    unfolding minus

    -- If minus i is equal to minus j, then i and j have the same
    -- difference.

    minus≡minus→Same-difference :
      minus i ≡ minus j → Same-difference i j
    minus≡minus→Same-difference =
      Q.effective ext prop-ext Same-difference-is-equivalence-relation
        (λ _ _ → Same-difference-propositional) (λ _ → reflexive)
      where
      open Is-equivalence-relation
             Same-difference-is-equivalence-relation

  opaque
    unfolding minus

    -- The Same-difference relation is pointwise equivalent to
    -- equality under minus.

    @0 Same-difference≃minus≡minus :
      Same-difference i j ≃ (minus i ≡ minus j)
    Same-difference≃minus≡minus =
      Q.Truncation-/ᴱ.≃[]≡[] minus≡minus→Same-difference
        Same-difference-propositional

opaque
  unfolding ℤ≃ᴱℤ minus

  -- The Same-difference relation is pointwise equivalent to
  -- equality under minus.

  @0 Same-difference≃minus≡minus :
    Same-difference i j ≃ (minus i ≡ minus j)
  Same-difference≃minus≡minus {i} {j} =
    Q.Truncation-/ᴱ.Split-surjection.≃[]≡[]″
      (×-closure 2 ℕ-set ℕ-set)
      Data.ℤ-set
      (_≃ᴱ_.to ℤ≃ᴱℤ ∘ minus)
      (λ where
         (Data.+ n)    → n , 0
         Data.-[1+ n ] → 0 , P.suc n)
      (λ where
         (Data.+ n) →
           _≃ᴱ_.to ℤ≃ᴱℤ (n ⊖ 0)      ≡⟨ rec-minus ⟩
           Data.+ n Data.- Data.+ 0  ≡⟨ cong Data.+_ Nat.+-right-identity ⟩∎
           Data.+ n                  ∎
         Data.-[1+ n ] →
           _≃ᴱ_.to ℤ≃ᴱℤ (0 ⊖ P.suc n)      ≡⟨ rec-minus ⟩
           Data.+ 0 Data.- Data.+ P.suc n  ≡⟨⟩
           Data.-[1+ n ]                   ∎)
      (λ @0 { {x = i@(m₁ , n₁)} {y = m₂ , n₂} →
              Eq.⇔→≃ (Same-difference-propositional {i = i})
                Data.ℤ-set (cong (_≃ᴱ_.to ℤ≃ᴱℤ) ∘ minus-cong)
                (_≃ᴱ_.to ℤ≃ᴱℤ (m₁ ⊖ n₁) ≡ _≃ᴱ_.to ℤ≃ᴱℤ (m₂ ⊖ n₂)          →⟨ ≡⇒↝ _ (cong₂ _≡_ rec-minus rec-minus) ⟩
                 Data.+ m₁ Data.- Data.+ n₁ ≡ Data.+ m₂ Data.- Data.+ n₂  →⟨ lemma m₁ ⟩
                 Same-difference (m₁ , n₁) (m₂ , n₂)                      □) })
    where
    open Group Data.ℤ-group hiding (_∘_; _⊖_)

    lemma :
      ∀ m₁ {m₂ n₁ n₂} →
      Data.+ m₁ Data.- Data.+ n₁ ≡ Data.+ m₂ Data.- Data.+ n₂ →
      m₁ ⊕ n₂ ≡ n₁ ⊕ m₂
    lemma m₁ {m₂} {n₁} {n₂} hyp =
      Data.+-cancellative
        (Data.+ (m₁ ⊕ n₂)                                    ≡⟨ sym $
                                                                trans (cong (Data._+_ (Data.+ (m₁ ⊕ _))) (left-inverse (Data.+ n₁))) $
                                                                right-identity _ ⟩
         (Data.+ m₁ Data.+ Data.+ n₂) Data.+
         (Data.-[ n₁ ] Data.+ Data.+ n₁)                     ≡⟨ trans
                                                                  (sym (Data.+-assoc (Data.+ _) {j = Data.+ n₂} {k = Data.-[ n₁ ] Data.+ _})) $
                                                                trans
                                                                  (cong (Data._+_ (Data.+ m₁)) $
                                                                   trans (Data.+-assoc (Data.+ n₂) {j = Data.-[ n₁ ]} {k = Data.+ n₁}) $
                                                                   trans
                                                                     (cong (Data._+ (Data.+ n₁)) (Data.+-comm (Data.+ n₂) {j = Data.-[ n₁ ]})) $
                                                                   sym (Data.+-assoc (Data.-[ n₁ ]) {j = Data.+ n₂} {k = Data.+ n₁})) $
                                                                Data.+-assoc (Data.+ m₁) {j = Data.-[ n₁ ]} {k = Data.+ (n₂ ⊕ n₁)} ⟩
         (Data.+ m₁ Data.+ Data.-[ n₁ ]) Data.+
         (Data.+ n₂ Data.+ Data.+ n₁)                        ≡⟨ cong (Data._+ _) hyp ⟩

         (Data.+ m₂ Data.+ Data.-[ n₂ ]) Data.+
         (Data.+ n₂ Data.+ Data.+ n₁)                        ≡⟨ trans
                                                                  (sym (Data.+-assoc (Data.+ m₂) {j = Data.-[ n₂ ]} {k = Data.+ (n₂ ⊕ _)})) $
                                                                cong (Data._+_ (Data.+ _)) (Data.+-assoc Data.-[ n₂ ]) ⟩
         Data.+ m₂ Data.+
         ((Data.-[ n₂ ] Data.+ Data.+ n₂) Data.+ Data.+ n₁)  ≡⟨ cong (Data._+_ (Data.+ m₂)) $
                                                                trans (cong (Data._+ _) (left-inverse (Data.+ n₂))) $
                                                                left-identity (Data.+ _) ⟩

         Data.+ (m₂ ⊕ n₁)                                    ≡⟨ cong Data.+_ (Nat.+-comm m₂) ⟩∎

         Data.+ (n₁ ⊕ m₂)                                    ∎)

opaque

  -- Same-difference can be stated using subtraction.

  @0 Same-difference≃-≡- :
    Same-difference (m₁ , m₂) (n₁ , n₂) ≃
    (+ m₁ - + m₂ ≡ + n₁ - + n₂)
  Same-difference≃-≡- {m₁} {m₂} {n₁} {n₂} =
    Same-difference (m₁ , m₂) (n₁ , n₂)  ↝⟨ Same-difference≃minus≡minus ⟩
    m₁ ⊖ m₂ ≡ n₁ ⊖ n₂                    ↝⟨ ≡⇒↝ _ $ sym $ cong₂ _≡_ +-+ +-+ ⟩□
    + m₁ - + m₂ ≡ + n₁ - + n₂            □

opaque
  unfolding Same-difference +_ -[_]

  -- Non-negative integers are not equal to negative integers.

  +≢-[1+] : + m ≢ -[ P.suc n ]
  +≢-[1+] {m} {n} =
    Stable-¬
      [ + m ≡ -[ P.suc n ]                     ↔⟨⟩
        m ⊖ 0 ≡ 0 ⊖ P.suc n                    ↔⟨ inverse Same-difference≃minus≡minus ⟩
        Same-difference (m , 0) (0 , P.suc n)  ↔⟨⟩
        m ⊕ P.suc n ≡ 0                        →⟨ trans (Nat.suc+≡+suc m) ⟩
        P.suc (m ⊕ n) ≡ 0                      →⟨ Nat.0≢+ ∘ sym ⟩□
        ⊥                                      □
      ]ᴱ

opaque
  unfolding Same-difference +_ -[_]

  -- Non-positive integers are not equal to positive integers.

  +[1+]≢- : + P.suc m ≢ -[ n ]
  +[1+]≢- {m} {n} =
    Stable-¬
      [ + P.suc m ≡ -[ n ]                     ↔⟨⟩
        P.suc m ⊖ 0 ≡ 0 ⊖ n                    ↔⟨ inverse Same-difference≃minus≡minus ⟩
        Same-difference (P.suc m , 0) (0 , n)  ↔⟨⟩
        P.suc m ⊕ n ≡ 0                        →⟨ Nat.0≢+ ∘ sym ⟩□
        ⊥                                      □
      ]ᴱ

opaque
  unfolding Same-difference +_

  -- The +_ "constructor" is injective.

  @0 +-injective : + m ≡ + n → m ≡ n
  +-injective {m} {n} =
    + m ≡ + n      ↔⟨⟩
    m ⊖ 0 ≡ n ⊖ 0  ↔⟨ inverse Same-difference≃minus≡minus ⟩
    m ⊕ 0 ≡ 0 ⊕ n  →⟨ trans (sym Nat.+-right-identity) ⟩□
    m ≡ n          □

opaque

  -- The -[_] "constructor" is injective.

  @0 -[]-injective : -[ m ] ≡ -[ n ] → m ≡ n
  -[]-injective {m} {n} =
    -[ m ] ≡ -[ n ]  →⟨ ≡⇒↝ _ (cong₂ _≡_ -‿- -‿-) ∘ cong (-_) ⟩
    + m ≡ + n        →⟨ +-injective ⟩□
    m ≡ n            □

opaque

  -- Erased equality of integers is decidable (assuming erased
  -- function extensionality).

  decidable-erased-equality :
    @0 Extensionality lzero lzero →
    Decidable-erased-equality ℤ
  decidable-erased-equality ext =
    elim-prop₂ (λ i j → Dec-Erased (i ≡ j))
      (λ _ _ → BC.Is-proposition-Dec-Erased ext ℤ-set)
      (λ _ _ →
         Dec-Erased-map
           (_≃_.logical-equivalence Same-difference≃minus≡minus)
           (Dec→Dec-Erased Same-difference-decidable))

------------------------------------------------------------------------
-- Positive, negative

-- The following definitions make use of certain erased assumptions.
--
-- One could perhaps avoid these assumptions by going via Data.ℤ (see
-- Integer.Quotient for that approach), but here a more direct
-- approach is taken.

module _
  (@0 ext      : Extensionality-ω)
  (@0 prop-ext : Propositional-extensionality lzero)
  where

  private opaque
    unfolding Same-difference

    -- A definition used to implement Positive as well as
    -- Positive-propositional.

    Positive′ : ℤ → Proposition lzero
    Positive′ =
      rec (Is-set-∃-Is-proposition ext prop-ext)
        (λ (m , n) → (n <ᴺ m) , ≤-propositional)
        (λ @0 where
           {i = m₁ , n₁} {j = m₂ , n₂} s →
             _↔_.to
               (ignore-propositional-component
                  (H-level-propositional ext 1))
               (prop-ext ≤-propositional ≤-propositional
                  (n₁ <ᴺ m₁  ↝⟨ record { to   = lemma s
                                       ; from = lemma (trans (Nat.+-comm m₂) (trans (sym s) (Nat.+-comm m₁)))
                                       } ⟩
                   n₂ <ᴺ m₂  □)))
      where
      lemma : m₁ ⊕ n₂ ≡ n₁ ⊕ m₂ → n₁ <ᴺ m₁ → n₂ <ᴺ m₂
      lemma {m₁} {n₂} {n₁} {m₂} eq n₁≤m₁ =
        Nat.+-order-reflectingʳ
          (m₁ ⊕ P.suc n₂  Nat.≡⟨ sym (Nat.suc+≡+suc m₁) ⟩≤
           P.suc m₁ ⊕ n₂  Nat.≡⟨ cong P.suc eq ⟩≤
           P.suc n₁ ⊕ m₂  Nat.≤⟨ n₁≤m₁ Nat.+-mono Nat.≤-refl ⟩∎
           m₁ ⊕ m₂        ∎≤)

  opaque
    unfolding Positive′

    -- The property of being positive.

    Positive : ℤ → Type
    Positive = proj₁ ∘ Positive′

  opaque
    unfolding Positive

    -- A computation rule for Positive.

    Positive-⊖ : Positive (m ⊖ n) ≡ (n <ᴺ m)
    Positive-⊖ = cong proj₁ rec-minus

  opaque
    unfolding Positive

    -- Positive is propositional.

    Positive-propositional : Is-proposition (Positive i)
    Positive-propositional = proj₂ (Positive′ _)

  opaque

    -- The property of being negative.

    Negative : ℤ → Type
    Negative = Positive ∘ -_

  opaque
    unfolding Negative

    -- A computation rule for Negative.

    Negative-⊖ : Negative (m ⊖ n) ≡ (m <ᴺ n)
    Negative-⊖ = trans (cong Positive -⊖) Positive-⊖

  opaque
    unfolding Negative

    -- Negative is propositional.

    Negative-propositional : Is-proposition (Negative i)
    Negative-propositional = Positive-propositional

  opaque

    -- No integer is both positive and negative.

    ¬+- : Positive i → Negative i → ⊥₀
    ¬+- {i} =
      elim-prop (λ i → Positive i → Negative i → ⊥₀)
        (λ _ →
           Π-closure ext 1 λ _ →
           Π-closure ext 1 λ _ →
           ⊥-propositional)
        (λ (m , n) →
           curry
             (Positive (m ⊖ n) × Negative (m ⊖ n)  →⟨ Σ-map (≡⇒↝ _ Positive-⊖) (≡⇒↝ _ Negative-⊖) ⟩
              n <ᴺ m × m <ᴺ n                      →⟨ (λ (n<m , m<n) → Nat.<-irreflexive (Nat.<-trans n<m m<n)) ⟩
              ⊥                                    □))
        i

  opaque
    unfolding Same-difference +_

    -- No integer is both positive and equal to zero.

    ¬+0 : Positive i → i ≡ + 0 → ⊥₀
    ¬+0 {i} pos =
      Stable-¬
        [ elim-prop (λ i → Positive i → i ≡ + 0 → ⊥₀)
            (λ _ →
               Π-closure ext 1 λ _ →
               Π-closure ext 1 λ _ →
               ⊥-propositional)
            (λ (m , n) →
               curry
                 (Positive (m ⊖ n) × m ⊖ n ≡ 0 ⊖ 0  →⟨ Σ-map (≡⇒↝ _ Positive-⊖) (_≃_.from Same-difference≃minus≡minus) ⟩
                  n <ᴺ m × m ⊕ 0 ≡ n ⊕ 0            →⟨ (λ (n<m , eq) → Nat.+≮ 0 (Nat.≤-trans n<m (Nat.≤-refl′ (Nat.+-cancellativeʳ eq)))) ⟩
                  ⊥                                 □))
            i pos
        ]ᴱ

  opaque
    unfolding Negative

    -- No integer is both negative and equal to zero.

    ¬-0 : Negative i → i ≡ + 0 → ⊥₀
    ¬-0 {i} neg ≡0 =
      ¬+0 neg
        (- i     ≡⟨ cong -_ ≡0 ⟩
         - + 0   ≡⟨ -+ ⟩
         -[ 0 ]  ≡⟨ sym +0≡-0 ⟩∎
         + 0     ∎)

  opaque
    unfolding +_

    -- One can decide if an integer is negative, zero or positive.

    -⊎0⊎+ : ∀ i → Negative i ⊎ Erased (i ≡ + 0) ⊎ Positive i
    -⊎0⊎+ =
      elim-prop _
        (λ i →
           ⊎-closure-propositional
             (λ neg →
                Stable-¬ [ P.[ ¬-0 neg ∘ erased , flip ¬+- neg ] ]ᴱ)
             Negative-propositional
             (⊎-closure-propositional
                (λ ≡0 → Stable-¬ [ flip ¬+0 (erased ≡0) ]ᴱ)
                (BC.H-level-Erased 1 ℤ-set)
                Positive-propositional))
        (λ (m , n) →
           case m Nat.<⊎≡⊎> n of λ where
             (inj₁ m<n) →
               inj₁ (_⇔_.from (≡⇒↝ _ Negative-⊖) m<n)
             (inj₂ (inj₁ m≡n)) →
               inj₂ (inj₁
                 [ m ⊖ n  ≡⟨ cong (_⊖ _) m≡n ⟩
                   n ⊖ n  ≡⟨ ⊖≡0 ⟩∎
                   + 0    ∎
                 ]ᴱ)
             (inj₂ (inj₂ m>n)) →
               inj₂ (inj₂ (_⇔_.from (≡⇒↝ _ Positive-⊖) m>n)))

  opaque

    -- If i and j are positive, then i + j is positive.

    >0→>0→+>0 : Positive i → Positive j → Positive (i + j)
    >0→>0→+>0 {i} {j} =
      elim-prop₂ _
        (λ _ _ →
           Π-closure ext 1 λ _ →
           Π-closure ext 1 λ _ →
           Positive-propositional)
        (λ (m₁ , n₁) (m₂ , n₂) →
           curry
             (Positive (m₁ ⊖ n₁) × Positive (m₂ ⊖ n₂)  →⟨ subst id (cong₂ _×_ Positive-⊖ Positive-⊖) ⟩
              n₁ <ᴺ m₁ × n₂ <ᴺ m₂                      →⟨ Σ-map id Nat.<→≤ ⟩
              n₁ <ᴺ m₁ × n₂ ≤ᴺ m₂                      →⟨ uncurry Nat._+-mono_ ⟩
              n₁ ⊕ n₂ <ᴺ m₁ ⊕ m₂                       →⟨ subst id (sym Positive-⊖) ⟩
              Positive ((m₁ ⊕ m₂) ⊖ (n₁ ⊕ n₂))         →⟨ subst Positive (sym ⊖+⊖) ⟩□
              Positive ((m₁ ⊖ n₁) + (m₂ ⊖ n₂))         □))
        i j

  opaque
    unfolding Negative

    -- If i and j are negative, then i + j is negative.

    <0→<0→+<0 : Negative i → Negative j → Negative (i + j)
    <0→<0→+<0 {i} {j} = curry
      (Negative i × Negative j          ↔⟨⟩
       Positive (- i) × Positive (- j)  →⟨ uncurry >0→>0→+>0 ⟩
       Positive (- i + - j)             →⟨ subst Positive -‿commutes‿+ ⟩
       Positive (- (i + j))             ↔⟨⟩
       Negative (i + j)                 □)

------------------------------------------------------------------------
-- The group of integers

opaque
  unfolding Same-difference +_

  -- The group of integers.

  ℤ-group : Groupᴱ lzero
  ℤ-group .Groupᴱ.Carrier        = ℤ
  ℤ-group .Groupᴱ.Carrier-is-set = ℤ-set
  ℤ-group .Groupᴱ._∘_            = _+_
  ℤ-group .Groupᴱ.id             = + 0
  ℤ-group .Groupᴱ._⁻¹            = -_
  ℤ-group .Groupᴱ.assoc          =
    elim-prop₃ _ (λ _ _ _ → ℤ-set) λ (m₁ , n₁) (m₂ , n₂) (m₃ , n₃) →
      (m₁ ⊖ n₁) + ((m₂ ⊖ n₂) + (m₃ ⊖ n₃))  ≡⟨ trans (cong (_+_ _) ⊖+⊖) ⊖+⊖ ⟩
      (m₁ ⊕ (m₂ ⊕ m₃)) ⊖ (n₁ ⊕ (n₂ ⊕ n₃))  ≡⟨ cong₂ _⊖_ (Nat.+-assoc m₁) (Nat.+-assoc n₁) ⟩
      ((m₁ ⊕ m₂) ⊕ m₃) ⊖ ((n₁ ⊕ n₂) ⊕ n₃)  ≡⟨ sym (trans (cong (_+ _) ⊖+⊖) ⊖+⊖) ⟩∎
      ((m₁ ⊖ n₁) + (m₂ ⊖ n₂)) + (m₃ ⊖ n₃)  ∎
  ℤ-group .Groupᴱ.left-identity =
    elim-prop _ (λ _ → ℤ-set) λ (m , n) →
      (0 ⊖ 0) + (m ⊖ n)  ≡⟨ ⊖+⊖ ⟩∎
      m ⊖ n              ∎
  ℤ-group .Groupᴱ.right-identity =
    elim-prop _ (λ _ → ℤ-set) λ (m , n) →
      (m ⊖ n) + (0 ⊖ 0)  ≡⟨ ⊖+⊖ ⟩
      (m ⊕ 0) ⊖ (n ⊕ 0)  ≡⟨ cong₂ _⊖_ Nat.+-right-identity Nat.+-right-identity ⟩∎
      m ⊖ n              ∎
  ℤ-group .Groupᴱ.left-inverse =
    elim-prop _ (λ _ → ℤ-set) λ (m , n) →
      - (m ⊖ n) + (m ⊖ n)  ≡⟨ trans (cong (flip _+_ _) -⊖) ⊖+⊖ ⟩
      (n ⊕ m) ⊖ (m ⊕ n)    ≡⟨ minus-cong (cong (_⊕ 0) (Nat.+-comm n)) ⟩∎
      0 ⊖ 0                ∎
  ℤ-group .Groupᴱ.right-inverse =
    elim-prop _ (λ _ → ℤ-set) λ (m , n) →
      (m ⊖ n) + - (m ⊖ n)  ≡⟨ trans (cong (_+_ _) -⊖) ⊖+⊖ ⟩
      (m ⊕ n) ⊖ (n ⊕ m)    ≡⟨ minus-cong (cong (_⊕ 0) (Nat.+-comm m)) ⟩∎
      0 ⊖ 0                ∎

opaque
  unfolding ℤ-group

  -- ℤ-group is isomorphic to Group→Groupᴱ Data.ℤ-group.

  ℤ≃ᴳℤ : ℤ-group ≃ᴳ Group→Groupᴱ Data.ℤ-group
  ℤ≃ᴳℤ = G.≃ᴳ-sym λ where
    .G.Homomorphic.related         → inverse ℤ≃ᴱℤ
    .G.Homomorphic.homomorphic i _ → sym (+≡+ i)

opaque

  -- ℤ-group is equal to Group→Groupᴱ Data.ℤ-group (assuming function
  -- extensionality and univalence).

  @0 ℤ≡ℤ :
    Extensionality lzero lzero →
    Univalence lzero →
    ℤ-group ≡ Group→Groupᴱ Data.ℤ-group
  ℤ≡ℤ ext univ = _≃_.to (G.≃ᴳ≃≡ ext univ) ℤ≃ᴳℤ
