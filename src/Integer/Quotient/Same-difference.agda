------------------------------------------------------------------------
-- A relation used to define integers by quotienting
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Integer.Quotient.Same-difference
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Equivalence-relation eq
open import H-level.Closure eq
open import Nat eq
open import Nat.Solver eq

private variable
  m₁ m₂ n₁ n₂ : ℕ
  A           : Type _
  i j         : A

opaque

  -- Two pairs of natural numbers are related if they have the same
  -- difference.

  Same-difference : ℕ × ℕ → ℕ × ℕ → Type
  Same-difference (m₁ , n₁) (m₂ , n₂) = m₁ + n₂ ≡ n₁ + m₂

opaque
  unfolding Same-difference

  -- The relation is pointwise propositional.

  Same-difference-propositional :
    Is-proposition (Same-difference i j)
  Same-difference-propositional = ℕ-set

opaque
  unfolding Same-difference

  -- The relation is an equivalence relation.

  Same-difference-is-equivalence-relation :
    Is-equivalence-relation Same-difference
  Same-difference-is-equivalence-relation = record
    { reflexive  = λ { {m , n} →
                       m + n  ≡⟨ +-comm m ⟩∎
                       n + m  ∎
                     }
    ; symmetric  = λ { {m₁ , n₁} {m₂ , n₂} hyp →
                       m₂ + n₁  ≡⟨ +-comm m₂ ⟩
                       n₁ + m₂  ≡⟨ sym hyp ⟩
                       m₁ + n₂  ≡⟨ +-comm m₁ ⟩∎
                       n₂ + m₁  ∎
                     }
    ; transitive = λ { {m₁ , n₁} {m₂ , n₂} {m₃ , n₃} hyp₁ hyp₂ →
                       +-cancellativeʳ (
                         m₁ + n₃ + m₂    ≡⟨ sym $ +-assoc m₁ ⟩
                         m₁ + (n₃ + m₂)  ≡⟨ cong (m₁ +_) $ +-comm n₃ ⟩
                         m₁ + (m₂ + n₃)  ≡⟨ cong (m₁ +_) hyp₂ ⟩
                         m₁ + (n₂ + m₃)  ≡⟨ +-assoc m₁ ⟩
                         m₁ + n₂ + m₃    ≡⟨ cong (_+ m₃) hyp₁ ⟩
                         n₁ + m₂ + m₃    ≡⟨ sym $ +-assoc n₁ ⟩
                         n₁ + (m₂ + m₃)  ≡⟨ cong (n₁ +_) $ +-comm m₂ ⟩
                         n₁ + (m₃ + m₂)  ≡⟨ +-assoc n₁ ⟩∎
                         n₁ + m₃ + m₂    ∎)
                     }
    }

opaque
  unfolding Same-difference

  -- It is decidable whether the relation holds.

  Same-difference-decidable : Dec (Same-difference i j)
  Same-difference-decidable = _ ≟ _

opaque
  unfolding Same-difference

  -- Same-difference is preserved by addition.

  Same-difference-+ :
    ∀ {i₁ j₁ i₂ j₂} →
    Same-difference i₁ j₁ →
    Same-difference i₂ j₂ →
    Same-difference (Σ-zip _+_ _+_ i₁ i₂) (Σ-zip _+_ _+_ j₁ j₂)
  Same-difference-+
    {i₁ = a , b} {j₁ = c , d} {i₂ = e , f} {j₂ = g , h} eq₁ eq₂ =
    (a + e) + (d + h)  ≡⟨ solve 4 (λ a d e h → (a :+ e) :+ (d :+ h) := (a :+ d) :+ (e :+ h))
                            (refl _) a _ _ _ ⟩
    (a + d) + (e + h)  ≡⟨ cong₂ _+_ eq₁ eq₂ ⟩
    (b + c) + (f + g)  ≡⟨ solve 4 (λ b c f g → (b :+ c) :+ (f :+ g) := (b :+ f) :+ (c :+ g))
                            (refl _) b _ _ _ ⟩∎
    (b + f) + (c + g)  ∎

opaque
  unfolding Same-difference

  -- Same-difference is preserved by multiplication from the left.

  Same-difference-*ˡ :
    ∀ n →
    Same-difference i j →
    Same-difference (Σ-map (n *_) (n *_) i) (Σ-map (n *_) (n *_) j)
  Same-difference-*ˡ {i = m₁ , n₁} {j = m₂ , n₂} k eq =
    k * m₁ + k * n₂  ≡⟨ sym (*-+-distribˡ k) ⟩
    k * (m₁ + n₂)    ≡⟨ cong (k *_) eq ⟩
    k * (n₁ + m₂)    ≡⟨ *-+-distribˡ k ⟩∎
    k * n₁ + k * m₂  ∎

opaque
  unfolding Same-difference

  -- Same-difference is preserved by multiplication from the right.

  Same-difference-*ʳ :
    ∀ n →
    Same-difference i j →
    Same-difference (Σ-map (_* n) (_* n) i) (Σ-map (_* n) (_* n) j)
  Same-difference-*ʳ {i = m₁ , n₁} {j = m₂ , n₂} k eq =
    m₁ * k + n₂ * k  ≡⟨ sym (*-+-distribʳ m₁) ⟩
    (m₁ + n₂) * k    ≡⟨ cong (_* k) eq ⟩
    (n₁ + m₂) * k    ≡⟨ *-+-distribʳ n₁ ⟩∎
    n₁ * k + m₂ * k  ∎

opaque
  unfolding Same-difference

  -- If two pairs have the same difference, then the same applies if
  -- the components of each pair are swapped.

  Same-difference-swap :
    Same-difference (m₁ , n₁) (m₂ , n₂) →
    Same-difference (n₁ , m₁) (n₂ , m₂)
  Same-difference-swap = sym

private opaque
  unfolding Same-difference

  -- A lemma used to prove Same-difference-multiplication-lemma.

  Same-difference-multiplication-lemma′ :
    ∀ a {b c d e f g h} i {j k l m n} o p →
    Same-difference
      (((a + b) + (c + d)) + ((a + e) + (f + g)) ,
       ((h + i) + (e + j)) + ((i + d) + (k + l)))
      (((g + m) + (n + k)) + ((c + h) + (o + n)) ,
       ((o + l) + (f + p)) + ((j + b) + (m + p))) →
    Same-difference (a + b , h + i) (n + k , f + p)
  Same-difference-multiplication-lemma′
    a {b} {c} {d} {e} {f} {g} {h} i {j} {k} {l} {m} {n} o p eq =
    *-cancellativeˡ 1 (+-cancellativeʳ eq′)
    where
    eq′ :
      2 * ((a + b) + (f + p)) + (c + d + e + g + j + l + m + o) ≡
      2 * ((h + i) + (n + k)) + (c + d + e + g + j + l + m + o)
    eq′ =
      2 * ((a + b) + (f + p)) + (c + d + e + g + j + l + m + o)  ≡⟨ solve 12
                                                                      (λ a b c d e f g j l m o p →
                                                                         con 2 :* ((a :+ b) :+ (f :+ p)) :+
                                                                         (c :+ d :+ e :+ g :+ j :+ l :+ m :+ o) :=
                                                                         (((a :+ b) :+ (c :+ d)) :+ ((a :+ e) :+ (f :+ g))) :+
                                                                         (((o :+ l) :+ (f :+ p)) :+ ((j :+ b) :+ (m :+ p))))
                                                                      (refl _) a _ c _ _ _ _ _ _ _ _ _ ⟩
      (((a + b) + (c + d)) + ((a + e) + (f + g))) +
      (((o + l) + (f + p)) + ((j + b) + (m + p)))                ≡⟨ eq ⟩

      (((h + i) + (e + j)) + ((i + d) + (k + l))) +
      (((g + m) + (n + k)) + ((c + h) + (o + n)))                ≡⟨ solve 12
                                                                      (λ c d e g h i j k l m n o →
                                                                         (((h :+ i) :+ (e :+ j)) :+ ((i :+ d) :+ (k :+ l))) :+
                                                                         (((g :+ m) :+ (n :+ k)) :+ ((c :+ h) :+ (o :+ n))) :=
                                                                         con 2 :* ((h :+ i) :+ (n :+ k)) :+
                                                                         (c :+ d :+ e :+ g :+ j :+ l :+ m :+ o))
                                                                      (refl _) c _ _ _ h _ _ k _ _ _ _ ⟩∎
      2 * ((h + i) + (n + k)) + (c + d + e + g + j + l + m + o)  ∎

opaque

  -- A lemma that can be used in the implementation of multiplication.

  Same-difference-multiplication-lemma :
    ∀ {a b c d e f g h} →
    Same-difference (a , b) (c , d) →
    Same-difference (e , f) (g , h) →
    Same-difference
      (a * e + b * f , a * f + b * e)
      (c * g + d * h , c * h + d * g)
  Same-difference-multiplication-lemma
    {a} {b} {c} {d} {e} {f} {g} {h} eq₁ eq₂ =
    Same-difference-multiplication-lemma′
      (a * _) (b * _) (a * _) (d * _) $
    Same-difference-+
      (Same-difference-+
         (Same-difference-+ (Same-difference-*ˡ a eq₂)
            (Same-difference-*ˡ b (Same-difference-swap eq₂)))
         (Same-difference-+ (Same-difference-*ˡ c eq₂)
            (Same-difference-*ˡ d (Same-difference-swap eq₂))))
      (Same-difference-+
         (Same-difference-+ (Same-difference-*ʳ e eq₁)
            (symmetric (Same-difference-*ʳ f eq₁)))
         (Same-difference-+ (symmetric (Same-difference-*ʳ h eq₁))
            (Same-difference-*ʳ g eq₁)))
    where
    open Is-equivalence-relation Same-difference-is-equivalence-relation
