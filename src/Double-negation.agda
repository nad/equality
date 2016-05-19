------------------------------------------------------------------------
-- The double-negation monad
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Double-negation
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude

open Derived-definitions-and-properties eq
open import H-level eq
open import H-level.Closure eq
open import Monad eq

-- The double-negation monad, defined using a wrapper type to make
-- instance resolution easier.

infix 3 ¬¬_

record ¬¬_ {a} (A : Set a) : Set a where
  constructor wrap
  field
    run : ¬ ¬ A

open ¬¬_ public

-- An extra universe-polymorphic variant of map.

map′ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → ¬¬ A → ¬¬ B
run (map′ f ¬¬a) = λ ¬b → run ¬¬a (λ a → ¬b (f a))

-- Instances.

instance

  double-negation-monad : ∀ {ℓ} → Raw-monad (¬¬_ {a = ℓ})
  run (Raw-monad.return double-negation-monad x)   = _$ x
  run (Raw-monad._>>=_  double-negation-monad x f) =
    join (map′ (run ∘ f) x)
    where
    join : ∀ {a} {A : Set a} → ¬¬ ¬ A → ¬ A
    join ¬¬¬a = λ a → run ¬¬¬a (λ ¬a → ¬a a)

private

  proof-irrelevant : ∀ {a} {A : Set a} {x y : ¬¬ A} →
                     Extensionality a lzero → x ≡ y
  proof-irrelevant ext = cong wrap $ ext λ _ →
    _⇔_.to propositional⇔irrelevant ⊥-propositional _ _

monad : ∀ {ℓ} →
        Extensionality ℓ lzero →
        Monad (¬¬_ {a = ℓ})
Monad.raw-monad      (monad _)         = double-negation-monad
Monad.left-identity  (monad ext) _ _   = proof-irrelevant ext
Monad.right-identity (monad ext) _     = proof-irrelevant ext
Monad.associativity  (monad ext) _ _ _ = proof-irrelevant ext

-- The following variant of excluded middle is provable.

excluded-middle : ∀ {a} {A : Set a} → ¬¬ Dec A
run excluded-middle ¬[a⊎¬a] = ¬[a⊎¬a] (no λ a → ¬[a⊎¬a] (yes a))

-- The following variant of Peirce's law is provable.

call/cc : ∀ {a w} {A : Set a} {Whatever : Set w} →
          ((A → Whatever) → ¬¬ A) → ¬¬ A
run (call/cc hyp) ¬a = run (hyp (λ a → ⊥-elim (¬a a))) ¬a
