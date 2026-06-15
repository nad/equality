------------------------------------------------------------------------
-- Integers, defined using a quotient type
------------------------------------------------------------------------

{-# OPTIONS --cubical=erased --safe #-}

import Equality.Path as P

module Integer.Quotient
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Dec
open import Prelude as P
  hiding (suc; _^_)
  renaming (_+_ to _⊕_; _*_ to _⊛_)

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equality.Path.Isomorphisms.Univalence eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence-relation equality-with-J
open import Erased.Cubical eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import Group equality-with-J as G using (Group; Abelian; _≃ᴳ_)
open import Group.Cyclic eq as C using (Generated-by; Cyclic)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq using (∣_∣)
import Integer equality-with-J as Data
open import Integer.Quotient.Same-difference equality-with-J
import Nat equality-with-J as Nat
open import Quotient eq as Q hiding (elim; rec)
open import Univalence-axiom equality-with-J

private
  variable
    m m₁ m₂ n n₁ n₂ : ℕ
    a               : Level
    A               : Type a
    i j p q         : A

------------------------------------------------------------------------
-- Integers

-- Integers.

ℤ : Type
ℤ = (ℕ × ℕ) / Same-difference

-- The integers form a set.

ℤ-set : Is-set ℤ
ℤ-set = /-is-set

-- Turns natural numbers into the corresponding integers.

infix 8 +_

+_ : ℕ → ℤ
+ n = [ (n , 0) ]

-- Turns natural numbers into the corresponding negative integers.

-[_] : ℕ → ℤ
-[ n ] = [ (0 , n) ]

------------------------------------------------------------------------
-- A lemma

opaque
  unfolding Same-difference

  -- Increasing both sides of a pair by one does not affect the value of
  -- the corresponding integer.

  []≡[suc,suc] : _≡_ {A = ℤ} [ (m , n) ] [ (P.suc m , P.suc n) ]
  []≡[suc,suc] {m} {n} = []-respects-relation
    (m ⊕ P.suc n  ≡⟨ sym $ Nat.suc+≡+suc m ⟩
     P.suc m ⊕ n  ≡⟨ Nat.+-comm (P.suc m) ⟩∎
     n ⊕ P.suc m  ∎)

------------------------------------------------------------------------
-- A one-to-one correspondence between two definitions of integers

-- There is a bijection between this variant of integers and the one
-- in Integer.

ℤ↔ℤ : ℤ ↔ Data.ℤ
ℤ↔ℤ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to-lemma₁ : m₁ ⊕ P.suc n₂ ≡ m₂ →
              (Data.+ m₁) ≡ Data.+ m₂ +-[1+ n₂ ]
  to-lemma₁ {m₁} {n₂} {m₂ = zero} hyp =
    ⊥-elim $
    Nat.0≢+
      (zero             ≡⟨ sym hyp ⟩
       m₁ ⊕ P.suc n₂    ≡⟨ sym $ Nat.suc+≡+suc m₁ ⟩∎
       P.suc (m₁ ⊕ n₂)  ∎)
  to-lemma₁ {m₁} {n₂ = zero} {m₂ = P.suc m₂} hyp =
    cong (Data.+_) $
    Nat.cancel-suc
      (P.suc m₁  ≡⟨ Nat.+-comm 1 ⟩
       m₁ ⊕ 1    ≡⟨ hyp ⟩∎
       P.suc m₂  ∎)
  to-lemma₁ {m₁} {n₂ = P.suc n₂} {m₂ = P.suc m₂} hyp =
    to-lemma₁ $
    Nat.cancel-suc
      (P.suc (m₁ ⊕ P.suc n₂)  ≡⟨ Nat.suc+≡+suc m₁ ⟩
       m₁ ⊕ P.suc (P.suc n₂)  ≡⟨ hyp ⟩∎
       P.suc m₂               ∎)

  to-lemma₂ : m₁ ⊕ zero ≡ P.suc n₁ ⊕ m₂ →
              Data.+ m₁ +-[1+ n₁ ] ≡ Data.+ m₂
  to-lemma₂ {m₁ = zero} hyp =
    ⊥-elim $ Nat.0≢+ hyp
  to-lemma₂ {m₁ = P.suc m₁} {n₁ = zero} {m₂} hyp =
    cong (Data.+_) $
    Nat.cancel-suc
      (P.suc m₁      ≡⟨ sym Nat.+-right-identity ⟩
       P.suc m₁ ⊕ 0  ≡⟨ hyp ⟩∎
       P.suc m₂      ∎)
  to-lemma₂ {m₁ = P.suc m₁} {n₁ = P.suc n₁} hyp =
    to-lemma₂ (Nat.cancel-suc hyp)

  to-lemma₃ :
    ∀ m₁ n₁ m₂ n₂ →
    m₁ ⊕ P.suc n₂ ≡ P.suc n₁ ⊕ m₂ →
    Data.+ m₁ +-[1+ n₁ ] ≡ Data.+ m₂ +-[1+ n₂ ]
  to-lemma₃ (P.suc m₁) (P.suc n₁) m₂ n₂ hyp =
    to-lemma₃ m₁ n₁ m₂ n₂ (Nat.cancel-suc hyp)
  to-lemma₃ m₁ n₁ (P.suc m₂) (P.suc n₂) hyp =
    to-lemma₃ m₁ n₁ m₂ n₂ $
    Nat.cancel-suc
      (P.suc (m₁ ⊕ P.suc n₂)  ≡⟨ Nat.suc+≡+suc m₁ ⟩
       m₁ ⊕ P.suc (P.suc n₂)  ≡⟨ hyp ⟩
       P.suc n₁ ⊕ P.suc m₂    ≡⟨ cong P.suc $ sym $ Nat.suc+≡+suc n₁ ⟩∎
       P.suc (P.suc n₁ ⊕ m₂)  ∎)
  to-lemma₃ zero n₁ zero n₂ hyp =
    cong Data.-[1+_] $
    Nat.cancel-suc
      (P.suc n₁      ≡⟨ sym Nat.+-right-identity ⟩
       P.suc n₁ ⊕ 0  ≡⟨ sym hyp ⟩∎
       P.suc n₂      ∎)
  to-lemma₃ (P.suc m₁) zero (P.suc m₂) zero hyp =
    cong (Data.+_) $
    Nat.cancel-suc $
      (P.suc m₁  ≡⟨ Nat.+-comm 1 ⟩
       m₁ ⊕ 1    ≡⟨ Nat.cancel-suc hyp ⟩∎
       P.suc m₂  ∎)
  to-lemma₃ (P.suc m₁) zero zero n₂ hyp =
    ⊥-elim $ Nat.0≢+
      (0                ≡⟨ sym $ Nat.cancel-suc hyp ⟩
       m₁ ⊕ P.suc n₂    ≡⟨ sym $ Nat.suc+≡+suc m₁ ⟩∎
       P.suc (m₁ ⊕ n₂)  ∎)
  to-lemma₃ zero n₁ (P.suc m₂) zero hyp =
    ⊥-elim $ Nat.0≢+
      (0                ≡⟨ Nat.cancel-suc hyp ⟩
       n₁ ⊕ P.suc m₂    ≡⟨ sym $ Nat.suc+≡+suc n₁ ⟩∎
       P.suc (n₁ ⊕ m₂)  ∎)

  opaque
    unfolding Same-difference

    to-lemma :
      ∀ m₁ n₁ m₂ n₂ →
      Same-difference (m₁ , n₁) (m₂ , n₂) →
      Data.+ m₁ Data.- Data.+ n₁ ≡
      Data.+ m₂ Data.- Data.+ n₂
    to-lemma m₁ zero m₂ zero hyp =
      Data.+ (m₁ ⊕ 0)  ≡⟨ cong Data.+_ hyp ⟩
      Data.+ m₂        ≡⟨ cong Data.+_ (sym Nat.+-right-identity) ⟩∎
      Data.+ (m₂ ⊕ 0)  ∎
    to-lemma m₁ zero m₂ (P.suc n₂) hyp =
      Data.+ (m₁ ⊕ 0)       ≡⟨ cong Data.+_ Nat.+-right-identity ⟩
      Data.+ m₁             ≡⟨ to-lemma₁ hyp ⟩∎
      Data.+ m₂ +-[1+ n₂ ]  ∎
    to-lemma m₁ (P.suc n₁) m₂ zero hyp =
      Data.+ m₁ +-[1+ n₁ ]  ≡⟨ to-lemma₂ hyp ⟩
      Data.+ m₂             ≡⟨ cong Data.+_ (sym Nat.+-right-identity) ⟩∎
      Data.+ (m₂ ⊕ 0)       ∎
    to-lemma m₁ (P.suc n₁) m₂ (P.suc n₂) hyp =
      Data.+ m₁ +-[1+ n₁ ]  ≡⟨ to-lemma₃ _ _ _ _ hyp ⟩∎
      Data.+ m₂ +-[1+ n₂ ]  ∎

  to : ℤ → Data.ℤ
  to = Q.rec λ where
    .[]ʳ (m , n) → Data.+ m Data.- Data.+ n

    .[]-respects-relationʳ {x = m₁ , n₁} {y = m₂ , n₂} →
      to-lemma m₁ n₁ m₂ n₂

    .is-setʳ → Data.ℤ-set

  from : Data.ℤ → ℤ
  from (Data.+ n)    = + n
  from Data.-[1+ n ] = [ (0 , P.suc n) ]

  to∘from : ∀ i → to (from i) ≡ i
  to∘from (Data.+ n) =
    to (from (Data.+ n))      ≡⟨⟩
    Data.+ (n ⊕ 0)            ≡⟨ cong Data.+_ Nat.+-right-identity ⟩∎
    Data.+ n                  ∎
  to∘from Data.-[1+ n ] =
    to (from Data.-[1+ n ])  ≡⟨⟩
    Data.-[1+ n ]            ∎

  from-+_+-[1+_] :
    ∀ m n → from (Data.+ m +-[1+ n ]) ≡ [ (m , P.suc n) ]
  from-+ zero    +-[1+ n ]       = refl _
  from-+ P.suc m +-[1+ zero ]    = []≡[suc,suc]
  from-+ P.suc m +-[1+ P.suc n ] =
    from (Data.+ P.suc m +-[1+ P.suc n ])  ≡⟨⟩
    from (Data.+ m +-[1+ n ])              ≡⟨ from-+ m +-[1+ n ] ⟩
    [ (m , P.suc n) ]                      ≡⟨ []≡[suc,suc] ⟩∎
    [ (P.suc m , P.suc (P.suc n)) ]        ∎

  from∘to : ∀ i → from (to i) ≡ i
  from∘to = Q.elim-prop λ where
    .[]ʳ (m , zero) →
      from (to (+ m))  ≡⟨⟩
      + (m ⊕ 0)        ≡⟨ cong +_ Nat.+-right-identity ⟩∎
      + m              ∎
    .[]ʳ (m , P.suc n) →
      from (to [ (m , P.suc n) ])  ≡⟨⟩
      from (Data.+ m +-[1+ n ])    ≡⟨ from-+ m +-[1+ n ] ⟩∎
      [ (m , P.suc n) ]            ∎
    .is-propositionʳ _ → ℤ-set

-- The bijection is homomorphic with respect to +_/Data.+_.

ℤ↔ℤ-+ : _↔_.to ℤ↔ℤ (+ n) ≡ Data.+ n
ℤ↔ℤ-+ {n} =
  Data.+ (n ⊕ 0)  ≡⟨ cong Data.+_ Nat.+-right-identity ⟩∎
  Data.+ n        ∎

-- The bijection is homomorphic with respect to -[_]/Data.-[_].

ℤ↔ℤ--[] : _↔_.to ℤ↔ℤ -[ n ] ≡ Data.-[ n ]
ℤ↔ℤ--[] {n = zero}    = Data.+ 0  ∎
ℤ↔ℤ--[] {n = P.suc n} = Data.-[1+ n ]  ∎

------------------------------------------------------------------------
-- An eliminator and a recursor with poor computational behaviour

module _ where

  private

    -- An eliminator for integers. This eliminator is not exported,
    -- because it is basically just the eliminator for quotients.

    elim :
      (P : ℤ → Type p) →
      (∀ i → Is-set (P i)) →
      (f : ∀ m n → P [ (m , n) ]) →
      (∀ {p q} (s : Same-difference p q) →
       subst P ([]-respects-relation s) (uncurry f p) ≡ uncurry f q) →
      ∀ i → P i
    elim _ P-set f resp = Q.elim λ where
      .[]ʳ                   → uncurry f
      .[]-respects-relationʳ → resp
      .is-setʳ               → P-set

    -- The following computation rule holds by definition.

    elim-[] :
      (P : ℤ → Type p) →
      (P-set : ∀ i → Is-set (P i)) →
      (f : ∀ m n → P [ (m , n) ]) →
      (resp : ∀ {p q} (s : Same-difference p q) →
              subst P ([]-respects-relation s) (uncurry f p) ≡
              uncurry f q) →
      elim P P-set f resp [ (m , n) ] ≡ f m n
    elim-[] _ _ _ _ = refl _

private

  -- A helper function used in the implementation of elim.

  elim′ :
    (P : ℤ → Type p) →
    (∀ n → P (_↔_.from ℤ↔ℤ (Data.+ n))) →
    (∀ n → P (_↔_.from ℤ↔ℤ Data.-[1+ n ])) →
    ∀ i → P (_↔_.from ℤ↔ℤ i)
  elim′ _ p n (Data.+ m)    = p m
  elim′ _ p n Data.-[1+ m ] = n m

-- An eliminator for integers.
--
-- Note that the motive does not have to be a family of sets, and
-- that the function does not need to respect the relation
-- Same-difference.

elim :
  (P : ℤ → Type p) →
  (∀ m n → P [ (m , n) ]) →
  ∀ i → P i
elim P f i =                       $⟨ elim′ P (λ n → f n 0) (λ n → f 0 (P.suc n)) (_↔_.to ℤ↔ℤ i) ⟩
  P (_↔_.from ℤ↔ℤ (_↔_.to ℤ↔ℤ i))  ↝⟨ subst P (_↔_.left-inverse-of ℤ↔ℤ i) ⟩□
  P i                              □

opaque
 unfolding []≡[suc,suc]
 mutual

  -- A "computation" rule for elim.
  --
  -- Here the function is required to respect Same-difference. Note that
  -- this "computation" rule does not (at the time of writing) in
  -- general hold by definition.

  elim-[] :
    {P : ℤ → Type p}
    (f : ∀ m n → P [ (m , n) ]) →
    (∀ {p q} (s : Same-difference p q) →
     subst P ([]-respects-relation s) (uncurry f p) ≡ uncurry f q) →
    elim P f [ (m , n) ] ≡ f m n
  elim-[] f hyp = elim-[]′ f (λ _ _ → hyp _)

  -- A variant of the computation rule in which the requirement to
  -- respect Same-difference has been replaced by a more specific
  -- condition.

  elim-[]′ :
    {P : ℤ → Type p}
    (f : ∀ m n → P [ (m , n) ]) →
    (∀ m n → subst P []≡[suc,suc] (f m n) ≡ f (P.suc m) (P.suc n)) →
    elim P f [ (m , n) ] ≡ f m n
  elim-[]′ {m} {n = zero} {P} f hyp =
    elim P f [ (m , 0) ]                                  ≡⟨⟩
    subst P (cong +_ Nat.+-right-identity) (f (m ⊕ 0) 0)  ≡⟨ sym $ subst-∘ _ _ _ ⟩
    subst (P ∘ +_) Nat.+-right-identity (f (m ⊕ 0) 0)     ≡⟨ elim¹ (λ eq → subst (P ∘ +_) eq (f _ _) ≡ f _ _) (subst-refl _ _) _ ⟩∎
    f m 0                                                 ∎

  elim-[]′ {m} {n = P.suc n} {P} f hyp =
    elim P f [ (m , P.suc n) ]                                          ≡⟨⟩

    subst P (_↔_.left-inverse-of ℤ↔ℤ [ (m , P.suc n) ]) $
      elim′ P (λ n → f n 0) (λ n → f 0 (P.suc n)) (Data.+ m +-[1+ n ])  ≡⟨ lemma m n ⟩∎

    f m (P.suc n)                                                       ∎
    where
    lemma :
      ∀ m n →
      subst P (_↔_.left-inverse-of ℤ↔ℤ [ (m , P.suc n) ])
        (elim′ P (λ n → f n 0) (λ n → f 0 (P.suc n))
           (Data.+ m +-[1+ n ])) ≡
      f m (P.suc n)
    lemma zero n =
      subst P (refl _) (f 0 (P.suc n))  ≡⟨ subst-refl _ _ ⟩∎
      f 0 (P.suc n)                     ∎
    lemma (P.suc m) zero =
      subst P []≡[suc,suc] (f m 0)  ≡⟨ hyp _ _ ⟩∎
      f (P.suc m) 1                 ∎
    lemma (P.suc m) (P.suc n) =
      subst P
        (trans (_↔_.left-inverse-of ℤ↔ℤ [ (m , P.suc n) ])
           []≡[suc,suc])
        (elim′ P (λ n → f n 0) (λ n → f 0 (P.suc n))
           (Data.+ m +-[1+ n ]))                              ≡⟨ sym $ subst-subst _ _ _ _ ⟩

      subst P []≡[suc,suc]
        (subst P (_↔_.left-inverse-of ℤ↔ℤ [ (m , P.suc n) ])
           (elim′ P (λ n → f n 0) (λ n → f 0 (P.suc n))
              (Data.+ m +-[1+ n ])))                          ≡⟨ cong (subst P ([]-respects-relation _)) $
                                                                 lemma m n ⟩

      subst P []≡[suc,suc] (f m (P.suc n))                    ≡⟨ hyp _ _ ⟩∎

      f (P.suc m) (P.suc (P.suc n))                           ∎

private

  -- A helper function used in the implementation of rec.

  rec′ : (ℕ → A) → (ℕ → A) → Data.ℤ → A
  rec′ p n (Data.+ m)    = p m
  rec′ p n Data.-[1+ m ] = n m

-- A recursor for integers.

rec : (ℕ → ℕ → A) → ℤ → A
rec {A} f =
  ℤ       ↔⟨ ℤ↔ℤ ⟩
  Data.ℤ  ↝⟨ rec′ (λ n → f n 0) (λ n → f 0 (P.suc n)) ⟩□
  A       □

-- The recursor could have been defined in terms of the eliminator.
--
-- The recursor is not defined in terms of the eliminator in this way
-- because (in at least some cases) this would lead to different
-- computational behaviour.

rec≡elim : (f : ℕ → ℕ → A) → rec f i ≡ elim (const _) f i
rec≡elim {i} f =
  rec f i                                                               ≡⟨⟩

  rec′ (λ n → f n 0) (λ n → f 0 (P.suc n)) (_↔_.to ℤ↔ℤ i)               ≡⟨ lemma (_↔_.to ℤ↔ℤ i) ⟩

  elim′ (const _) (λ n → f n 0) (λ n → f 0 (P.suc n)) (_↔_.to ℤ↔ℤ i)    ≡⟨ sym $ subst-const _ ⟩

  subst (const _) (_↔_.left-inverse-of ℤ↔ℤ i) $
    elim′ (const _) (λ n → f n 0) (λ n → f 0 (P.suc n)) (_↔_.to ℤ↔ℤ i)  ≡⟨⟩

  elim (const _) f i                                                    ∎
  where
  lemma :
    ∀ i →
    rec′ (λ n → f n 0) (λ n → f 0 (P.suc n)) i ≡
    elim′ (const _) (λ n → f n 0) (λ n → f 0 (P.suc n)) i
  lemma (Data.+ _)    = refl _
  lemma Data.-[1+ _ ] = refl _

-- A "computation" rule for rec.
--
-- Note that this "computation" rule does not (at the time of writing)
-- in general hold by definition.

rec-[] :
  (f : ℕ → ℕ → A) →
  (∀ {p q} → Same-difference p q → uncurry f p ≡ uncurry f q) →
  rec f [ (m , n) ] ≡ f m n
rec-[] {m} {n} f hyp =
  rec f [ (m , n) ]                                         ≡⟨ rec≡elim f ⟩
  elim (const _) f [ (m , n) ]                              ≡⟨ elim-[] f (λ {p q} s →
    subst (const _) ([]-respects-relation s) (uncurry f p)       ≡⟨ subst-const _ ⟩
    uncurry f p                                                  ≡⟨ hyp s ⟩∎
    uncurry f q                                                  ∎) ⟩∎
  f m n                                                     ∎

------------------------------------------------------------------------
-- Negation, addition and subtraction

-- A helper function that can be used to define unary operators on
-- integers.

unary-operator :
  (f : ℕ × ℕ → ℕ × ℕ) →
  (∀ {i j} →
   Same-difference i j →
   Same-difference (f i) (f j)) →
  ℤ → ℤ
unary-operator f resp = Q.rec λ where
  .[]ʳ i                   → [ f i ]
  .[]-respects-relationʳ s → []-respects-relation (resp s)
  .is-setʳ                 → ℤ-set

private

  -- A computation rule for unary-operator.
  --
  -- The function is not defined using the recursor above, but rather
  -- the quotient eliminator, to ensure that this computation rule
  -- holds by definition.

  unary-operator-[] :
    (f : ℕ × ℕ → ℕ × ℕ) →
    (resp : ∀ {i j} →
            Same-difference i j →
            Same-difference (f i) (f j)) →
    ∀ i → unary-operator f resp [ i ] ≡ [ f i ]
  unary-operator-[] _ _ _ = refl _

-- A helper function that can be used to define binary operators on
-- integers.

binary-operator :
  (f : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ) →
  (∀ {i₁ i₂ j₁ j₂} →
   Same-difference i₁ i₂ →
   Same-difference j₁ j₂ →
   Same-difference (f i₁ j₁) (f i₂ j₂)) →
  ℤ → ℤ → ℤ
binary-operator f resp = Q.rec λ where
    .[]ʳ i → Q.rec λ where
      .[]ʳ j → [ f i j ]

      .[]-respects-relationʳ s →
        []-respects-relation (resp reflexive s)

      .is-setʳ → ℤ-set

    .[]-respects-relationʳ s → ⟨ext⟩ $ Q.elim-prop λ where
      .[]ʳ i → []-respects-relation (resp s reflexive)

      .is-propositionʳ _ → +⇒≡ {n = 1} ℤ-set

    .is-setʳ →
      Π-closure ext 2 λ _ →
      ℤ-set
  where
  open Is-equivalence-relation Same-difference-is-equivalence-relation

private

  -- A computation rule for binary-operator.
  --
  -- The function is not defined using the recursor above, but rather
  -- the quotient eliminator, to ensure that this computation rule
  -- holds by definition.

  binary-operator-[] :
    (f : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ) →
    (resp : ∀ {i₁ i₂ j₁ j₂} →
            Same-difference i₁ i₂ →
            Same-difference j₁ j₂ →
            Same-difference (f i₁ j₁) (f i₂ j₂)) →
    ∀ i j → binary-operator f resp [ i ] [ j ] ≡ [ f i j ]
  binary-operator-[] _ _ _ _ = refl _

-- Negation.

infix 8 -_

-_ : ℤ → ℤ
-_ = unary-operator swap Same-difference-swap

-- Addition.

infixl 6 _+_

_+_ : ℤ → ℤ → ℤ
_+_ = binary-operator (Σ-zip _⊕_ _⊕_) Same-difference-+

-- Subtraction.

infixl 6 _-_

_-_ : ℤ → ℤ → ℤ
i - j = i + - j

-- The implementation of negation given here matches the one in
-- Integer.

-₁≡-₁ : ∀ i → - (_↔_.from ℤ↔ℤ i) ≡ _↔_.from ℤ↔ℤ (Data.- i)
-₁≡-₁ (Data.+ zero)      = -[ 0 ]        ∎
-₁≡-₁ (Data.+ (P.suc n)) = -[ P.suc n ]  ∎
-₁≡-₁ Data.-[1+ n ]      = + P.suc n     ∎

-- A lemma used in the implementation of +≡+.

++-[1+]≡++-[1+] : + m + -[ P.suc n ] ≡ _↔_.from ℤ↔ℤ (Data.+ m +-[1+ n ])
++-[1+]≡++-[1+] {m = zero}    {n}        = refl _
++-[1+]≡++-[1+] {m = P.suc m} {n = zero} =
  [ (P.suc (m ⊕ 0) , 1) ]  ≡⟨ cong (Q.[_] ∘ (_, 1) ∘ P.suc) Nat.+-right-identity ⟩
  [ (P.suc m , 1) ]        ≡⟨ sym []≡[suc,suc] ⟩∎
  [ (m , 0) ]              ∎
++-[1+]≡++-[1+] {m = P.suc m} {n = P.suc n} =
  + P.suc m + -[ P.suc (P.suc n) ]               ≡⟨ sym []≡[suc,suc] ⟩
  + m + -[ P.suc n ]                             ≡⟨ ++-[1+]≡++-[1+] ⟩
  _↔_.from ℤ↔ℤ (Data.+ m +-[1+ n ])              ≡⟨⟩
  _↔_.from ℤ↔ℤ (Data.+ P.suc m +-[1+ P.suc n ])  ∎

opaque
  unfolding Same-difference

  -- The implementation of addition given here matches the one in
  -- Integer.

  +≡+ :
    ∀ i →
    (_↔_.from ℤ↔ℤ i) + (_↔_.from ℤ↔ℤ j) ≡ _↔_.from ℤ↔ℤ (i Data.+ j)
  +≡+ {j = Data.+ n}      (Data.+ m) = + (m ⊕ n)  ∎
  +≡+ {j = Data.-[1+ n ]} (Data.+ m) = ++-[1+]≡++-[1+]

  +≡+ {j = Data.+ n} Data.-[1+ m ] =
    -[ P.suc m ] + + n                 ≡⟨ []-respects-relation (
        n ⊕ P.suc m                         ≡⟨ Nat.+-comm n ⟩
        P.suc m ⊕ n                         ≡⟨ sym $ cong₂ _⊕_ (Nat.+-right-identity {n = P.suc m}) Nat.+-right-identity ⟩∎
        P.suc m ⊕ 0 ⊕ (n ⊕ 0)               ∎) ⟩
    + n + -[ P.suc m ]                 ≡⟨ ++-[1+]≡++-[1+] ⟩∎
    _↔_.from ℤ↔ℤ (Data.+ n +-[1+ m ])  ∎

  +≡+ {j = Data.-[1+ n ]} Data.-[1+ m ] =
    -[ P.suc m ⊕ P.suc n ]      ≡⟨ cong (-[_] ∘ P.suc) $ sym $ Nat.suc+≡+suc _ ⟩∎
    -[ P.suc (P.suc (m ⊕ n)) ]  ∎

-- The implementation of subtraction given here matches the one in
-- Integer.

-≡- :
  ∀ i j →
  (_↔_.from ℤ↔ℤ i) - (_↔_.from ℤ↔ℤ j) ≡ _↔_.from ℤ↔ℤ (i Data.- j)
-≡- i j =
  (_↔_.from ℤ↔ℤ i) - (_↔_.from ℤ↔ℤ j)       ≡⟨⟩
  (_↔_.from ℤ↔ℤ i) + - (_↔_.from ℤ↔ℤ j)     ≡⟨ cong (λ j → _↔_.from ℤ↔ℤ i + j) $ -₁≡-₁ j ⟩
  _↔_.from ℤ↔ℤ i + _↔_.from ℤ↔ℤ (Data.- j)  ≡⟨ +≡+ i ⟩
  _↔_.from ℤ↔ℤ (i Data.+ Data.- j)          ≡⟨⟩
  _↔_.from ℤ↔ℤ (i Data.- j)                 ∎

------------------------------------------------------------------------
-- Some lemmas related to equality

opaque
  unfolding Same-difference

  -- The Same-difference relation is pointwise equivalent to equality
  -- under [_].

  Same-difference≃[]≡[] :
    Same-difference i j ≃ (_≡_ {A = ℤ} [ i ] [ j ])
  Same-difference≃[]≡[] =
    Stable→≃[]≡[]
      Same-difference-is-equivalence-relation
      (λ {i} → Same-difference-propositional {i = i})
      (Dec→Stable (_ Nat.≟ _))

opaque

  -- Same-difference can be stated using subtraction.

  Same-difference≃-≡- :
    Same-difference (m₁ , m₂) (n₁ , n₂) ≃
    (+ m₁ - + m₂ ≡ + n₁ - + n₂)
  Same-difference≃-≡- {m₁} {m₂} {n₁} {n₂} =
    Same-difference (m₁ , m₂) (n₁ , n₂)  ↝⟨ Same-difference≃[]≡[] ⟩
    [ (m₁ , m₂) ] ≡ [ (n₁ , n₂) ]        ↝⟨ ≡⇒↝ _ $ sym $
                                            cong₂ (λ m₁ n₁ → _≡_ {A = ℤ} [ (m₁ , _) ] [ (n₁ , _) ])
                                              Nat.+-right-identity
                                              Nat.+-right-identity ⟩
    + m₁ - + m₂ ≡ + n₁ - + n₂            □

opaque
  unfolding Same-difference

  -- Non-negative integers are not equal to negative integers.

  +≢-[1+] : + m ≢ -[ P.suc n ]
  +≢-[1+] {m} {n} =
    + m ≡ -[ P.suc n ]                     ↔⟨⟩
    [ (m , 0) ] ≡ [ (0 , P.suc n) ]        ↔⟨ inverse Same-difference≃[]≡[] ⟩
    Same-difference (m , 0) (0 , P.suc n)  ↔⟨⟩
    m ⊕ P.suc n ≡ 0                        ↝⟨ trans (Nat.suc+≡+suc m) ⟩
    P.suc (m ⊕ n) ≡ 0                      ↝⟨ Nat.0≢+ ∘ sym ⟩□
    ⊥                                      □

opaque
  unfolding Same-difference

  -- Non-positive integers are not equal to positive integers.

  +[1+]≢- : + P.suc m ≢ -[ n ]
  +[1+]≢- {m} {n} =
    + P.suc m ≡ -[ n ]                     ↔⟨⟩
    [ (P.suc m , 0) ] ≡ [ (0 , n) ]        ↔⟨ inverse Same-difference≃[]≡[] ⟩
    Same-difference (P.suc m , 0) (0 , n)  ↔⟨⟩
    P.suc m ⊕ n ≡ 0                        ↝⟨ Nat.0≢+ ∘ sym ⟩□
    ⊥                                      □

opaque
  unfolding Same-difference

  -- The +_ "constructor" is cancellative.

  +-cancellative : + m ≡ + n → m ≡ n
  +-cancellative {m} {n} =
    + m ≡ + n                  ↔⟨⟩
    [ (m , 0) ] ≡ [ (n , 0) ]  ↔⟨ inverse Same-difference≃[]≡[] ⟩
    m ⊕ 0 ≡ 0 ⊕ n              ↝⟨ trans (sym Nat.+-right-identity) ⟩□
    m ≡ n                      □

-- The -[_] "constructor" is cancellative.

-[]-cancellative : -[ m ] ≡ -[ n ] → m ≡ n
-[]-cancellative {m} {n} =
  -[ m ] ≡ -[ n ]  ↝⟨ cong (-_) ⟩
  + m ≡ + n        ↝⟨ +-cancellative ⟩□
  m ≡ n            □

-- Equality of integers is decidable.

infix 4 _≟_

_≟_ : Decidable-equality ℤ
_≟_ = Q.elim-prop λ where
  .[]ʳ _ → Q.elim-prop λ where
     .[]ʳ _ →
       Dec-map (_≃_.logical-equivalence Same-difference≃[]≡[])
         Same-difference-decidable
     .is-propositionʳ _ →
       Dec-closure-propositional ext ℤ-set
  .is-propositionʳ _ →
    Π-closure ext 1 λ _ →
    Dec-closure-propositional ext ℤ-set

------------------------------------------------------------------------
-- The successor and predecessor functions

opaque
  unfolding Same-difference

  -- The successor function.

  suc : ℤ → ℤ
  suc = Q.rec λ where
    .[]ʳ (m , n) → [ (P.suc m , n) ]

    .[]-respects-relationʳ {x = m₁ , m₂} {y = n₁ , n₂} hyp →
      []-respects-relation
        (P.suc (m₁ ⊕ n₂)  ≡⟨ cong P.suc hyp ⟩
         P.suc (m₂ ⊕ n₁)  ≡⟨ Nat.suc+≡+suc _ ⟩∎
         m₂ ⊕ P.suc n₁    ∎ )

    .is-setʳ → ℤ-set

opaque
  unfolding suc

  -- The function suc adds one to its input.

  suc≡1+ : ∀ i → suc i ≡ + 1 + i
  suc≡1+ = elim _ λ _ _ → refl _

opaque
  unfolding Same-difference

  -- The predecessor function.

  pred : ℤ → ℤ
  pred = Q.rec λ where
    .[]ʳ (m , n) → [ (m , P.suc n) ]

    .[]-respects-relationʳ {x = m₁ , m₂} {y = n₁ , n₂} hyp →
      []-respects-relation
        (m₁ ⊕ P.suc n₂    ≡⟨ sym $ Nat.suc+≡+suc _ ⟩
         P.suc (m₁ ⊕ n₂)  ≡⟨ cong P.suc hyp ⟩∎
         P.suc (m₂ ⊕ n₁)  ∎)

    .is-setʳ → ℤ-set

opaque
  unfolding pred

  -- The function pred subtracts one from its input.

  pred≡-1+ : ∀ i → pred i ≡ -[ 1 ] + i
  pred≡-1+ = elim _ λ _ _ → refl _

opaque
  unfolding pred suc

  -- An equivalence between ℤ and ℤ corresponding to the successor
  -- function.

  successor : ℤ ≃ ℤ
  successor = Eq.↔→≃
    suc
    pred
    (elim _ λ m _ → []-respects-relation (cong P.suc (Nat.+-comm m)))
    (elim _ λ m _ → []-respects-relation (cong P.suc (Nat.+-comm m)))

------------------------------------------------------------------------
-- Positive, negative

-- The property of being positive.

Positive : ℤ → Type
Positive = Data.Positive ∘ _↔_.to ℤ↔ℤ

-- Positive is propositional.

Positive-propositional : ∀ i → Is-proposition (Positive i)
Positive-propositional _ = Data.Positive-propositional

-- The property of being negative.

Negative : ℤ → Type
Negative = Data.Negative ∘ _↔_.to ℤ↔ℤ

-- Negative is propositional.

Negative-propositional : ∀ i → Is-proposition (Negative i)
Negative-propositional _ = Data.Negative-propositional

-- No integer is both positive and negative.

¬+- : ∀ i → Positive i → Negative i → ⊥₀
¬+- _ = Data.¬+-

-- No integer is both positive and equal to zero.

¬+0 : Positive i → i ≡ + 0 → ⊥₀
¬+0 pos ≡0 = Data.¬+0 pos (_↔_.from-to ℤ↔ℤ (sym ≡0))

-- No integer is both negative and equal to zero.

¬-0 : Negative i → i ≡ + 0 → ⊥₀
¬-0 neg ≡0 = Data.¬-0 neg (_↔_.from-to ℤ↔ℤ (sym ≡0))

-- One can decide if an integer is negative, zero or positive.

-⊎0⊎+ : ∀ i → Negative i ⊎ i ≡ + 0 ⊎ Positive i
-⊎0⊎+ i =
  ⊎-map id (⊎-map (sym ∘ _↔_.to-from ℤ↔ℤ) id)
    (Data.-⊎0⊎+ $ _↔_.to ℤ↔ℤ i)

-- If i and j are positive, then i + j is positive.

>0→>0→+>0 : ∀ i j → Positive i → Positive j → Positive (i + j)
>0→>0→+>0 i j i+ j+ =                                                   $⟨ Data.>0→>0→+>0 (_↔_.to ℤ↔ℤ i) (_↔_.to ℤ↔ℤ j) i+ j+ ⟩

  Data.Positive (_↔_.to ℤ↔ℤ i Data.+ _↔_.to ℤ↔ℤ j)                      ↝⟨ subst Data.Positive $
                                                                           sym $ _↔_.from-to ℤ↔ℤ $ sym $ +≡+ (_↔_.to ℤ↔ℤ i) ⟩
  Data.Positive (_↔_.to ℤ↔ℤ (_↔_.from ℤ↔ℤ (_↔_.to ℤ↔ℤ i) +
                             _↔_.from ℤ↔ℤ (_↔_.to ℤ↔ℤ j)))              ↔⟨⟩

  Positive (_↔_.from ℤ↔ℤ (_↔_.to ℤ↔ℤ i) + _↔_.from ℤ↔ℤ (_↔_.to ℤ↔ℤ j))  ↝⟨ subst Positive $
                                                                           cong₂ _+_
                                                                             (_↔_.left-inverse-of ℤ↔ℤ i)
                                                                             (_↔_.left-inverse-of ℤ↔ℤ j) ⟩□
  Positive (i + j)                                                      □

-- If i and j are negative, then i + j is negative.

<0→<0→+<0 : ∀ i j → Negative i → Negative j → Negative (i + j)
<0→<0→+<0 i j i- j- =                                                   $⟨ Data.<0→<0→+<0 (_↔_.to ℤ↔ℤ i) (_↔_.to ℤ↔ℤ j) i- j- ⟩

  Data.Negative (_↔_.to ℤ↔ℤ i Data.+ _↔_.to ℤ↔ℤ j)                      ↝⟨ subst Data.Negative $
                                                                           sym $ _↔_.from-to ℤ↔ℤ $ sym $ +≡+ (_↔_.to ℤ↔ℤ i) ⟩
  Data.Negative (_↔_.to ℤ↔ℤ (_↔_.from ℤ↔ℤ (_↔_.to ℤ↔ℤ i) +
                             _↔_.from ℤ↔ℤ (_↔_.to ℤ↔ℤ j)))              ↔⟨⟩

  Negative (_↔_.from ℤ↔ℤ (_↔_.to ℤ↔ℤ i) + _↔_.from ℤ↔ℤ (_↔_.to ℤ↔ℤ j))  ↝⟨ subst Negative $
                                                                           cong₂ _+_
                                                                             (_↔_.left-inverse-of ℤ↔ℤ i)
                                                                             (_↔_.left-inverse-of ℤ↔ℤ j) ⟩□
  Negative (i + j)                                                      □

------------------------------------------------------------------------
-- The group of integers

private opaque
  unfolding Same-difference

  -- A lemma used below.

  Same-difference-⊕-⊕-0-0 :
    ∀ m → Same-difference (m ⊕ n , n ⊕ m) (0 , 0)
  Same-difference-⊕-⊕-0-0 m = cong (_⊕ 0) $ Nat.+-comm m

-- The group of integers.

ℤ-group : Group lzero
ℤ-group .Group.Carrier        = ℤ
ℤ-group .Group.Carrier-is-set = ℤ-set
ℤ-group .Group._∘_            = _+_
ℤ-group .Group.id             = + 0
ℤ-group .Group._⁻¹            = -_
ℤ-group .Group.assoc          =
  elim _ λ m₁ n₁ → elim _ λ _ _ → elim _ λ _ _ →
  cong [_] $ cong₂ _,_
    (Nat.+-assoc m₁)
    (Nat.+-assoc n₁)
ℤ-group .Group.left-identity =
  elim _ λ _ _ → refl _
ℤ-group .Group.right-identity =
  elim _ λ _ _ →
  cong [_] $ cong₂ _,_
        Nat.+-right-identity
        Nat.+-right-identity
ℤ-group .Group.left-inverse =
  elim _ λ _ n →
  []-respects-relation (Same-difference-⊕-⊕-0-0 n)
ℤ-group .Group.right-inverse =
  elim _ λ m _ →
  []-respects-relation (Same-difference-⊕-⊕-0-0 m)

-- ℤ-group is isomorphic to Data.ℤ-group.

ℤ≃ᴳℤ : ℤ-group ≃ᴳ Data.ℤ-group
ℤ≃ᴳℤ = G.≃ᴳ-sym λ where
  .G.Homomorphic.related         → Eq.↔⇒≃ (inverse ℤ↔ℤ)
  .G.Homomorphic.homomorphic i _ → sym (+≡+ i)

-- ℤ-group is equal to Data.ℤ-group (assuming univalence).

ℤ≡ℤ :
  Univalence lzero →
  ℤ-group ≡ Data.ℤ-group
ℤ≡ℤ univ = _≃_.to (G.≃ᴳ≃≡ ext univ) ℤ≃ᴳℤ

-- The group of integers is generated by + 1.

ℤ-generated-by-1 : Generated-by ℤ-group (+ 1)
ℤ-generated-by-1 =
  C.≃ᴳ→Generated-by→Generated-by
    (G.≃ᴳ-sym ℤ≃ᴳℤ)
    C.ℤ-generated-by-1

-- The group of integers is cyclic.

ℤ-cyclic : Cyclic ℤ-group
ℤ-cyclic = ∣ _ , ℤ-generated-by-1 ∣

-- The group of integers is abelian.

ℤ-abelian : Abelian ℤ-group
ℤ-abelian = C.Cyclic→Abelian ℤ-group ℤ-cyclic

-- The direct product of the group of integers and the group of
-- integers is not cyclic.

ℤ×ℤ-not-cyclic : ¬ Cyclic (ℤ-group G.× ℤ-group)
ℤ×ℤ-not-cyclic =
  Cyclic (ℤ-group G.× ℤ-group)            ↝⟨ C.≃ᴳ→Cyclic→Cyclic (G.↝-× ℤ≃ᴳℤ ℤ≃ᴳℤ) ⟩
  Cyclic (Data.ℤ-group G.× Data.ℤ-group)  ↝⟨ C.ℤ×ℤ-not-cyclic ⟩□
  ⊥                                       □

-- The group of integers is not isomorphic to the direct product of
-- the group of integers and the group of integers.

ℤ≄ᴳℤ×ℤ : ¬ ℤ-group ≃ᴳ (ℤ-group G.× ℤ-group)
ℤ≄ᴳℤ×ℤ =
  ℤ-group ≃ᴳ (ℤ-group G.× ℤ-group)                 ↝⟨ G.↝ᴳ-trans (G.≃ᴳ-sym ℤ≃ᴳℤ) ∘ flip G.↝ᴳ-trans (G.↝-× ℤ≃ᴳℤ ℤ≃ᴳℤ) ⟩
  Data.ℤ-group ≃ᴳ (Data.ℤ-group G.× Data.ℤ-group)  ↝⟨ C.ℤ≄ᴳℤ×ℤ ⟩□
  ⊥                                                □

-- The group of integers is not equal to the direct product of the
-- group of integers and the group of integers.

ℤ≢ℤ×ℤ : ℤ-group ≢ (ℤ-group G.× ℤ-group)
ℤ≢ℤ×ℤ =
  ℤ-group ≡ (ℤ-group G.× ℤ-group)   ↝⟨ flip (subst (ℤ-group ≃ᴳ_)) G.↝ᴳ-refl ⟩
  ℤ-group ≃ᴳ (ℤ-group G.× ℤ-group)  ↝⟨ ℤ≄ᴳℤ×ℤ ⟩□
  ⊥                                 □

------------------------------------------------------------------------
-- Multiplication

-- Multiplication.

infixl 7 _*_

_*_ : ℤ → ℤ → ℤ
_*_ = binary-operator mul (λ {i₁ = i₁} → mul-resp i₁ _ _ _)
  where
  mul : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
  mul (m₁ , m₂) (n₁ , n₂) = m₁ ⊛ n₁ ⊕ m₂ ⊛ n₂ , m₁ ⊛ n₂ ⊕ m₂ ⊛ n₁

  opaque

    lemma₁ :
      ∀ a {b} c {d} →
      + (a ⊛ b ⊕ c ⊛ d) - + (a ⊛ d ⊕ c ⊛ b) ≡
      (+ (a ⊛ b) - + (a ⊛ d)) - (+ (c ⊛ b) - + (c ⊛ d))
    lemma₁ a {b} c {d} =
      cong₂ (λ m n → [ (m , n) ])
        ((a ⊛ b ⊕ c ⊛ d) ⊕ 0  ≡⟨ Nat.+-right-identity ⟩
         a ⊛ b ⊕ c ⊛ d        ≡⟨ cong (_⊕ c ⊛ d) $ sym Nat.+-right-identity ⟩
         (a ⊛ b ⊕ 0) ⊕ c ⊛ d  ∎)
        (a ⊛ d ⊕ c ⊛ b        ≡⟨ cong (a ⊛ d ⊕_) $ sym Nat.+-right-identity ⟩
         a ⊛ d ⊕ (c ⊛ b ⊕ 0)  ∎)

    lemma₂ :
      ∀ a b c {d} →
      (a + - b) + - (c + - d) ≡
      a + ((- b + - c) + d)
    lemma₂ a b c {d} =
      (a + - b) + - (c + - d)  ≡⟨ cong (_+_ (a + _)) $ ⊖⁻¹ {p = c} {q = d} ⟩
      (a + - b) + (d + - c)    ≡⟨ cong (_+_ (a + _)) $ ℤ-abelian d _ ⟩
      (a + - b) + (- c + d)    ≡⟨ sym $ assoc a _ _ ⟩
      a + (- b + (- c + d))    ≡⟨ cong (_+_ a) $ assoc (- b) _ _ ⟩
      a + ((- b + - c) + d)    ∎
      where
      open Group ℤ-group

    lemma₃ :
      ∀ a b c d →
      (a - b) - (c - d) ≡
      (a - c) - (b - d)
    lemma₃ a b c d =
      (a + - b) + - (c + - d)  ≡⟨ lemma₂ a b c ⟩
      a + ((- b + - c) + d)    ≡⟨ cong (_+_ a) $ cong {x = - b + _} (_+ _) $
                                  ℤ-abelian (- b) _ ⟩
      a + ((- c + - b) + d)    ≡⟨ sym $ lemma₂ a c b ⟩
      (a + - c) + - (b + - d)  ∎

    opaque
      unfolding Same-difference

      lemma₄ :
        ∀ {a b c d} e →
        Same-difference (a , b) (c , d) →
        + (e ⊛ a) - + (e ⊛ b) ≡ + (e ⊛ c) - + (e ⊛ d)
      lemma₄ {a} {b} {c} {d} e hyp =
        _≃_.to Same-difference≃-≡-
          (e ⊛ a ⊕ e ⊛ d  ≡⟨ sym $ Nat.*-+-distribˡ e ⟩
           e ⊛ (a ⊕ d)    ≡⟨ cong (e ⊛_) hyp ⟩
           e ⊛ (b ⊕ c)    ≡⟨ Nat.*-+-distribˡ e ⟩
           e ⊛ b ⊕ e ⊛ c  ∎)

    lemma₅ :
      ∀ a b {c d e} →
      Same-difference (a , b) (c , d) →
      + (a ⊛ e) - + (b ⊛ e) ≡ + (c ⊛ e) - + (d ⊛ e)
    lemma₅ a b {c} {d} {e} hyp =
      + (a ⊛ e) - + (b ⊛ e)  ≡⟨ cong₂ (λ m n → + m - + n) (Nat.*-comm a) (Nat.*-comm b) ⟩
      + (e ⊛ a) - + (e ⊛ b)  ≡⟨ lemma₄ e hyp ⟩
      + (e ⊛ c) - + (e ⊛ d)  ≡⟨ cong₂ (λ m n → + m - + n) (Nat.*-comm e) (Nat.*-comm e) ⟩
      + (c ⊛ e) - + (d ⊛ e)  ∎

    mul-resp :
      ∀ i₁ i₂ j₁ j₂ →
      Same-difference i₁ i₂ →
      Same-difference j₁ j₂ →
      Same-difference (mul i₁ j₁) (mul i₂ j₂)
    mul-resp (k₁ , k₂) (ℓ₁ , ℓ₂) (m₁ , m₂) (n₁ , n₂) hyp₁ hyp₂ =
      _≃_.from Same-difference≃-≡-
        (+ (k₁ ⊛ m₁ ⊕ k₂ ⊛ m₂) - + (k₁ ⊛ m₂ ⊕ k₂ ⊛ m₁)              ≡⟨ lemma₁ k₁ k₂ ⟩
         (+ (k₁ ⊛ m₁) - + (k₁ ⊛ m₂)) - (+ (k₂ ⊛ m₁) - + (k₂ ⊛ m₂))  ≡⟨ cong₂ _-_ (lemma₄ k₁ hyp₂) (lemma₄ k₂ hyp₂) ⟩
         (+ (k₁ ⊛ n₁) - + (k₁ ⊛ n₂)) - (+ (k₂ ⊛ n₁) - + (k₂ ⊛ n₂))  ≡⟨ lemma₃ (+ _) (+ _) (+ (k₂ ⊛ _)) (+ (k₂ ⊛ _)) ⟩
         (+ (k₁ ⊛ n₁) - + (k₂ ⊛ n₁)) - (+ (k₁ ⊛ n₂) - + (k₂ ⊛ n₂))  ≡⟨ cong₂ _-_ (lemma₅ k₁ k₂ hyp₁) (lemma₅ k₁ k₂ hyp₁) ⟩
         (+ (ℓ₁ ⊛ n₁) - + (ℓ₂ ⊛ n₁)) - (+ (ℓ₁ ⊛ n₂) - + (ℓ₂ ⊛ n₂))  ≡⟨ sym $ lemma₃ (+ _) (+ _) (+ (ℓ₂ ⊛ _)) (+ (ℓ₂ ⊛ _)) ⟩
         (+ (ℓ₁ ⊛ n₁) - + (ℓ₁ ⊛ n₂)) - (+ (ℓ₂ ⊛ n₁) - + (ℓ₂ ⊛ n₂))  ≡⟨ sym $ lemma₁ ℓ₁ ℓ₂ ⟩
         + (ℓ₁ ⊛ n₁ ⊕ ℓ₂ ⊛ n₂) - + (ℓ₁ ⊛ n₂ ⊕ ℓ₂ ⊛ n₁)              ∎)

opaque

  -- Multiplication is commutative.

  *-comm : ∀ i → i * j ≡ j * i
  *-comm {j} =
    elim _
      (λ i₁ i₂ →
         elim (λ j → [ (i₁ , i₂) ] * j ≡ j * [ (i₁ , i₂) ])
           (λ j₁ j₂ →
              cong₂ (λ m n → [ (m , n) ])
                (i₁ ⊛ j₁ ⊕ i₂ ⊛ j₂  ≡⟨ cong₂ _⊕_ (Nat.*-comm i₁) (Nat.*-comm i₂) ⟩
                 j₁ ⊛ i₁ ⊕ j₂ ⊛ i₂  ∎)
                (i₁ ⊛ j₂ ⊕ i₂ ⊛ j₁  ≡⟨ cong₂ _⊕_ (Nat.*-comm i₁) (Nat.*-comm i₂) ⟩
                 j₂ ⊛ i₁ ⊕ j₁ ⊛ i₂  ≡⟨ Nat.+-comm (j₂ ⊛ _) ⟩
                 j₁ ⊛ i₂ ⊕ j₂ ⊛ i₁  ∎))
           j)

opaque

  -- + 0 is a left zero for multiplication.

  *-left-zero : ∀ i → + 0 * i ≡ + 0
  *-left-zero = elim _ (λ _ _ → refl _)

opaque

  -- + 0 is a right zero for multiplication.

  *-right-zero : ∀ i → i * + 0 ≡ + 0
  *-right-zero i =
    i * + 0  ≡⟨ *-comm i ⟩
    + 0 * i  ≡⟨ *-left-zero i ⟩
    + 0      ∎

opaque

  -- A lemma relating multiplication and negation.

  *-≡-* : ∀ i → i * - j ≡ - i * j
  *-≡-* {j} =
    elim _
      (λ i₁ i₂ →
         elim (λ j → [ (i₁ , i₂) ] * - j ≡ - [ (i₁ , i₂) ] * j)
           (λ _ _ →
              cong₂ (λ m n → [ (m , n) ])
                (Nat.+-comm (i₁ ⊛ _))
                (Nat.+-comm (i₁ ⊛ _)))
           j)

opaque
  unfolding suc

  -- A "computation rule" for multiplication.

  suc-* : ∀ i → suc i * j ≡ j + i * j
  suc-* {j} =
    elim _
      (λ i₁ i₂ →
         elim (λ j → suc [ (i₁ , i₂) ] * j ≡ j + [ (i₁ , i₂) ] * j)
           (λ j₁ j₂ →
              cong₂ (λ m n → [ (m , n) ])
                ((j₁ ⊕ i₁ ⊛ j₁) ⊕ i₂ ⊛ j₂  ≡⟨ sym $ Nat.+-assoc j₁ ⟩
                 j₁ ⊕ (i₁ ⊛ j₁ ⊕ i₂ ⊛ j₂)  ∎)
                ((j₂ ⊕ i₁ ⊛ j₂) ⊕ i₂ ⊛ j₁  ≡⟨ sym $ Nat.+-assoc j₂ ⟩
                 j₂ ⊕ (i₁ ⊛ j₂ ⊕ i₂ ⊛ j₁)  ∎))
           j)

opaque

  -- A "computation rule" for multiplication.

  *-suc : ∀ i → i * suc j ≡ i + i * j
  *-suc {j} i =
    i * suc j  ≡⟨ *-comm i ⟩
    suc j * i  ≡⟨ suc-* j ⟩
    i + j * i  ≡⟨ cong (_+_ i) $ *-comm j ⟩
    i + i * j  ∎

opaque

  -- A "computation rule" for multiplication.

  neg-suc-* : ∀ i → - suc i * j ≡ - j + - i * j
  neg-suc-* {j} i =
    - suc i * j    ≡⟨ sym $ *-≡-* (suc i) ⟩
    suc i * - j    ≡⟨ suc-* i ⟩
    - j + i * - j  ≡⟨ cong (_+_ (- j)) $ *-≡-* i ⟩
    - j + - i * j  ∎

opaque

  -- A "computation rule" for multiplication.

  *-neg-suc : ∀ i j → i * - suc j ≡ - i + i * - j
  *-neg-suc i j =
    i * - suc j    ≡⟨ *-comm i ⟩
    - suc j * i    ≡⟨ neg-suc-* j ⟩
    - i + - j * i  ≡⟨ cong (_+_ (- i)) $ *-comm (- j) ⟩
    - i + i * - j  ∎

private opaque
  unfolding suc

  -- A lemma used in the implementation of *≡*.

  *+≡*+ :
    ∀ {i} n →
    _↔_.from ℤ↔ℤ i * + n ≡
    _↔_.from ℤ↔ℤ (i Data.*+ n)
  *+≡*+ {i} zero =
    _↔_.from ℤ↔ℤ i * + 0  ≡⟨ *-right-zero (_↔_.from ℤ↔ℤ i) ⟩
    + 0                   ∎
  *+≡*+ {i} (P.suc n) =
    _↔_.from ℤ↔ℤ i * suc (+ n)                   ≡⟨ *-suc (_↔_.from ℤ↔ℤ i) ⟩
    _↔_.from ℤ↔ℤ i + _↔_.from ℤ↔ℤ i * + n        ≡⟨ cong (_+_ (_↔_.from ℤ↔ℤ i)) $ *+≡*+ n ⟩
    _↔_.from ℤ↔ℤ i + _↔_.from ℤ↔ℤ (i Data.*+ n)  ≡⟨ +≡+ i ⟩
    _↔_.from ℤ↔ℤ (i Data.+ i Data.*+ n)          ∎

opaque
  unfolding suc

  -- The implementation of multiplication given here matches the one
  -- in Integer.

  *≡* :
    ∀ j →
    _↔_.from ℤ↔ℤ i * _↔_.from ℤ↔ℤ j ≡ _↔_.from ℤ↔ℤ (i Data.* j)
  *≡* (Data.+ n) =
    *+≡*+ n
  *≡* {i} Data.-[1+ n ] =
    _↔_.from ℤ↔ℤ i * - suc (+ n)                                 ≡⟨ *-neg-suc (_↔_.from ℤ↔ℤ i) (+ n) ⟩
    - _↔_.from ℤ↔ℤ i + _↔_.from ℤ↔ℤ i * - + n                    ≡⟨ cong (_+_ (- _↔_.from ℤ↔ℤ i)) $ *-≡-* (_↔_.from ℤ↔ℤ i) ⟩
    - _↔_.from ℤ↔ℤ i + - _↔_.from ℤ↔ℤ i * + n                    ≡⟨ cong (_+_ (- _↔_.from ℤ↔ℤ i)) $ cong (_* _) $ -₁≡-₁ i ⟩
    - _↔_.from ℤ↔ℤ i + _↔_.from ℤ↔ℤ (Data.- i) * + n             ≡⟨ cong₂ _+_ (-₁≡-₁ i) (*+≡*+ n) ⟩
    _↔_.from ℤ↔ℤ (Data.- i) + _↔_.from ℤ↔ℤ (Data.- i Data.*+ n)  ≡⟨ +≡+ (Data.- i) ⟩
    _↔_.from ℤ↔ℤ (Data.- i Data.+ Data.- i Data.*+ n)            ≡⟨⟩
    _↔_.from ℤ↔ℤ (Data.- i Data.*+ P.suc n)                      ∎
