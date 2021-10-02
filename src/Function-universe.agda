------------------------------------------------------------------------
-- A universe which includes several kinds of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Function-universe
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection using (_↔_; module _↔_)
open Derived-definitions-and-properties eq
open import Embedding eq as Emb using (Is-embedding; Embedding)
open import Equality.Decidable-UIP eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_; module _≃_; Is-equivalence)
import Equivalence.Contractible-preimages eq as CP
open import Equivalence.Erased.Basics eq as EEq using (_≃ᴱ_)
import Equivalence.Half-adjoint eq as HA
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq as Injection using (_↣_; module _↣_; Injective)
open import Logical-equivalence using (_⇔_; module _⇔_)
open import Nat eq hiding (_≟_)
open import Preimage eq using (_⁻¹_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
open import Surjection eq as Surjection using (_↠_; Split-surjective)

------------------------------------------------------------------------
-- The universe

-- The universe includes implications, logical equivalences,
-- injections, embeddings, surjections, bijections, equivalences, and
-- equivalences with erased proofs.

data Kind : Type where
  implication
    logical-equivalence
    injection
    embedding
    surjection
    bijection
    equivalence
    equivalenceᴱ : Kind

-- The interpretation of the universe.

infix 0 _↝[_]_

_↝[_]_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Kind → Type ℓ₂ → Type _
A ↝[ implication         ] B = A → B
A ↝[ logical-equivalence ] B = A ⇔ B
A ↝[ injection           ] B = A ↣ B
A ↝[ embedding           ] B = Embedding A B
A ↝[ surjection          ] B = A ↠ B
A ↝[ bijection           ] B = A ↔ B
A ↝[ equivalence         ] B = A ≃ B
A ↝[ equivalenceᴱ        ] B = A ≃ᴱ B

-- Equivalences can be converted to all kinds of functions.

from-equivalence : ∀ {k a b} {A : Type a} {B : Type b} →
                   A ≃ B → A ↝[ k ] B
from-equivalence {implication}         = _≃_.to
from-equivalence {logical-equivalence} = _≃_.logical-equivalence
from-equivalence {injection}           = _≃_.injection
from-equivalence {embedding}           = Emb.≃→Embedding
from-equivalence {surjection}          = _≃_.surjection
from-equivalence {bijection}           = _≃_.bijection
from-equivalence {equivalence}         = P.id
from-equivalence {equivalenceᴱ}        = EEq.≃→≃ᴱ

-- Bijections can be converted to all kinds of functions.

from-bijection : ∀ {k a b} {A : Type a} {B : Type b} →
                 A ↔ B → A ↝[ k ] B
from-bijection {implication}         = _↔_.to
from-bijection {logical-equivalence} = _↔_.logical-equivalence
from-bijection {injection}           = _↔_.injection
from-bijection {embedding}           = from-equivalence ⊚ Eq.↔⇒≃
from-bijection {surjection}          = _↔_.surjection
from-bijection {bijection}           = P.id
from-bijection {equivalence}         = Eq.↔⇒≃
from-bijection {equivalenceᴱ}        = EEq.≃→≃ᴱ ⊚ Eq.↔⇒≃

-- All kinds of functions can be converted to implications.

to-implication : ∀ {k a b} {A : Type a} {B : Type b} →
                 A ↝[ k ] B → A → B
to-implication {implication}         = P.id
to-implication {logical-equivalence} = _⇔_.to
to-implication {injection}           = _↣_.to
to-implication {embedding}           = Embedding.to
to-implication {surjection}          = _↠_.to
to-implication {bijection}           = _↔_.to
to-implication {equivalence}         = _≃_.to
to-implication {equivalenceᴱ}        = _≃ᴱ_.to

------------------------------------------------------------------------
-- A sub-universe of symmetric kinds of functions

data Symmetric-kind : Type where
  logical-equivalence bijection equivalence equivalenceᴱ :
    Symmetric-kind

⌊_⌋-sym : Symmetric-kind → Kind
⌊ logical-equivalence ⌋-sym = logical-equivalence
⌊ bijection           ⌋-sym = bijection
⌊ equivalence         ⌋-sym = equivalence
⌊ equivalenceᴱ        ⌋-sym = equivalenceᴱ

inverse : ∀ {k a b} {A : Type a} {B : Type b} →
          A ↝[ ⌊ k ⌋-sym ] B → B ↝[ ⌊ k ⌋-sym ] A
inverse {logical-equivalence} = Logical-equivalence.inverse
inverse {bijection}           = Bijection.inverse
inverse {equivalence}         = Eq.inverse
inverse {equivalenceᴱ}        = EEq.inverse

-- If there is a symmetric kind of function from A to B, then A and B
-- are logically equivalent.

sym→⇔ :
  ∀ {k a b} {A : Type a} {B : Type b} →
  A ↝[ ⌊ k ⌋-sym ] B → A ⇔ B
sym→⇔ {k = logical-equivalence} = P.id
sym→⇔ {k = bijection}           = from-bijection
sym→⇔ {k = equivalence}         = from-equivalence
sym→⇔ {k = equivalenceᴱ}        = _≃ᴱ_.logical-equivalence

------------------------------------------------------------------------
-- A sub-universe of isomorphisms

data Isomorphism-kind : Type where
  bijection equivalence : Isomorphism-kind

⌊_⌋-iso : Isomorphism-kind → Kind
⌊ bijection   ⌋-iso = bijection
⌊ equivalence ⌋-iso = equivalence

infix 0 _↔[_]_

_↔[_]_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Isomorphism-kind → Type ℓ₂ → Type _
A ↔[ k ] B = A ↝[ ⌊ k ⌋-iso ] B

from-isomorphism : ∀ {k₁ k₂ a b} {A : Type a} {B : Type b} →
                   A ↔[ k₁ ] B → A ↝[ k₂ ] B
from-isomorphism {bijection}   = from-bijection
from-isomorphism {equivalence} = from-equivalence

-- Lemma: to-implication after from-isomorphism is the same as
-- to-implication.

to-implication∘from-isomorphism :
  ∀ {a b} {A : Type a} {B : Type b} k₁ k₂ {A↔B : A ↔[ k₁ ] B} →
  to-implication A↔B ≡
  to-implication (from-isomorphism {k₂ = k₂} A↔B)
to-implication∘from-isomorphism {A = A} {B} = t∘f
  where
  t∘f : ∀ k₁ k₂ {A↔B : A ↔[ k₁ ] B} →
        to-implication A↔B ≡
        to-implication (from-isomorphism {k₂ = k₂} A↔B)
  t∘f bijection   implication         = refl _
  t∘f bijection   logical-equivalence = refl _
  t∘f bijection   injection           = refl _
  t∘f bijection   embedding           = refl _
  t∘f bijection   surjection          = refl _
  t∘f bijection   bijection           = refl _
  t∘f bijection   equivalence         = refl _
  t∘f bijection   equivalenceᴱ        = refl _
  t∘f equivalence implication         = refl _
  t∘f equivalence logical-equivalence = refl _
  t∘f equivalence injection           = refl _
  t∘f equivalence embedding           = refl _
  t∘f equivalence surjection          = refl _
  t∘f equivalence bijection           = refl _
  t∘f equivalence equivalence         = refl _
  t∘f equivalence equivalenceᴱ        = refl _

------------------------------------------------------------------------
-- Preorder

-- All the different kinds of functions form preorders.

-- Composition.

infixr 9 _∘_

_∘_ : ∀ {k a b c} {A : Type a} {B : Type b} {C : Type c} →
      B ↝[ k ] C → A ↝[ k ] B → A ↝[ k ] C
_∘_ {implication}         = λ f g → f ⊚ g
_∘_ {logical-equivalence} = Logical-equivalence._∘_
_∘_ {injection}           = Injection._∘_
_∘_ {embedding}           = Emb._∘_
_∘_ {surjection}          = Surjection._∘_
_∘_ {bijection}           = Bijection._∘_
_∘_ {equivalence}         = Eq._∘_
_∘_ {equivalenceᴱ}        = EEq._∘_

-- Identity.

id : ∀ {k a} {A : Type a} → A ↝[ k ] A
id {implication}         = P.id
id {logical-equivalence} = Logical-equivalence.id
id {injection}           = Injection.id
id {embedding}           = Emb.id
id {surjection}          = Surjection.id
id {bijection}           = Bijection.id
id {equivalence}         = Eq.id
id {equivalenceᴱ}        = EEq.id

-- "Equational" reasoning combinators.

infix  -1 finally-↝ finally-↔
infix  -1 _□
infixr -2 step-↝ step-↔ _↔⟨⟩_
infix  -3 $⟨_⟩_

-- For an explanation of why step-↝ and step-↔ are defined in this
-- way, see Equality.step-≡.

step-↝ : ∀ {k a b c} (A : Type a) {B : Type b} {C : Type c} →
         B ↝[ k ] C → A ↝[ k ] B → A ↝[ k ] C
step-↝ _ = _∘_

syntax step-↝ A B↝C A↝B = A ↝⟨ A↝B ⟩ B↝C

step-↔ : ∀ {k₁ k₂ a b c} (A : Type a) {B : Type b} {C : Type c} →
         B ↝[ k₂ ] C → A ↔[ k₁ ] B → A ↝[ k₂ ] C
step-↔ _ B↝C A↔B = step-↝ _ B↝C (from-isomorphism A↔B)

syntax step-↔ A B↝C A↔B = A ↔⟨ A↔B ⟩ B↝C

_↔⟨⟩_ : ∀ {k a b} (A : Type a) {B : Type b} →
        A ↝[ k ] B → A ↝[ k ] B
_ ↔⟨⟩ A↝B = A↝B

_□ : ∀ {k a} (A : Type a) → A ↝[ k ] A
A □ = id

finally-↝ : ∀ {k a b} (A : Type a) (B : Type b) →
            A ↝[ k ] B → A ↝[ k ] B
finally-↝ _ _ A↝B = A↝B

syntax finally-↝ A B A↝B = A ↝⟨ A↝B ⟩□ B □

finally-↔ : ∀ {k₁ k₂ a b} (A : Type a) (B : Type b) →
            A ↔[ k₁ ] B → A ↝[ k₂ ] B
finally-↔ _ _ A↔B = from-isomorphism A↔B

syntax finally-↔ A B A↔B = A ↔⟨ A↔B ⟩□ B □

$⟨_⟩_ : ∀ {k a b} {A : Type a} {B : Type b} →
        A → A ↝[ k ] B → B
$⟨ a ⟩ A↝B = to-implication A↝B a

-- Lemma: to-implication maps id to the identity function.

to-implication-id :
  ∀ {a} {A : Type a} k →
  to-implication {k = k} id ≡ id {A = A}
to-implication-id implication         = refl _
to-implication-id logical-equivalence = refl _
to-implication-id injection           = refl _
to-implication-id embedding           = refl _
to-implication-id surjection          = refl _
to-implication-id bijection           = refl _
to-implication-id equivalence         = refl _
to-implication-id equivalenceᴱ        = refl _

-- Lemma: to-implication is homomorphic with respect to _∘_.

to-implication-∘ :
  ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
  (k : Kind) {f : A ↝[ k ] B} {g : B ↝[ k ] C} →
  to-implication (g ∘ f) ≡ to-implication g ∘ to-implication f
to-implication-∘ implication         = refl _
to-implication-∘ logical-equivalence = refl _
to-implication-∘ injection           = refl _
to-implication-∘ embedding           = refl _
to-implication-∘ surjection          = refl _
to-implication-∘ bijection           = refl _
to-implication-∘ equivalence         = refl _
to-implication-∘ equivalenceᴱ        = refl _

-- Lemma: to-implication maps inverse id to the identity function.

to-implication-inverse-id :
  ∀ {a} {A : Type a} k →
  to-implication (inverse {k = k} id) ≡ id {A = A}
to-implication-inverse-id logical-equivalence = refl _
to-implication-inverse-id bijection           = refl _
to-implication-inverse-id equivalence         = refl _
to-implication-inverse-id equivalenceᴱ        = refl _

------------------------------------------------------------------------
-- Conditional extensionality

-- Code that provides support for proving general statements about
-- functions of different kinds, in which the statements involve
-- assumptions of extensionality for some kinds of functions, but not
-- all. For some examples, see ∀-cong and ∀-intro.

-- Kinds for which extensionality is not provided.

data Without-extensionality : Type where
  implication logical-equivalence : Without-extensionality

⌊_⌋-without : Without-extensionality → Kind
⌊ implication         ⌋-without = implication
⌊ logical-equivalence ⌋-without = logical-equivalence

-- Kinds for which extensionality is provided.

data With-extensionality : Type where
  injection embedding surjection bijection equivalence equivalenceᴱ :
    With-extensionality

⌊_⌋-with : With-extensionality → Kind
⌊ injection    ⌋-with = injection
⌊ embedding    ⌋-with = embedding
⌊ surjection   ⌋-with = surjection
⌊ bijection    ⌋-with = bijection
⌊ equivalence  ⌋-with = equivalence
⌊ equivalenceᴱ ⌋-with = equivalenceᴱ

-- Kinds annotated with information about whether extensionality is
-- provided or not.

data Extensionality-kind : Kind → Type where
  without-extensionality : (k : Without-extensionality) →
                           Extensionality-kind ⌊ k ⌋-without
  with-extensionality    : (k : With-extensionality) →
                           Extensionality-kind ⌊ k ⌋-with

-- Is extensionality provided for the given kind?

extensionality? : (k : Kind) → Extensionality-kind k
extensionality? implication         = without-extensionality implication
extensionality? logical-equivalence = without-extensionality
                                        logical-equivalence
extensionality? injection           = with-extensionality injection
extensionality? embedding           = with-extensionality embedding
extensionality? surjection          = with-extensionality surjection
extensionality? bijection           = with-extensionality bijection
extensionality? equivalence         = with-extensionality equivalence
extensionality? equivalenceᴱ        = with-extensionality equivalenceᴱ

-- Extensionality, but only for certain kinds of functions.

Extensionality? : Kind → (a b : Level) → Type (lsuc (a ⊔ b))
Extensionality? k with extensionality? k
... | without-extensionality _ = λ _ _ → ↑ _ ⊤
... | with-extensionality    _ = Extensionality

-- A variant of _↝[_]_. A ↝[ c ∣ d ] B means that A ↝[ k ] B can be
-- proved for all kinds k, in some cases assuming extensionality (for
-- the levels c and d).

infix 0 _↝[_∣_]_

_↝[_∣_]_ :
  ∀ {a b} →
  Type a → (c d : Level) → Type b → Type (a ⊔ b ⊔ lsuc (c ⊔ d))
A ↝[ c ∣ d ] B = ∀ {k} → Extensionality? k c d → A ↝[ k ] B

-- A variant of _↝[_∣_]_ with erased extensionality assumptions.

infix 0 _↝[_∣_]ᴱ_

_↝[_∣_]ᴱ_ :
  ∀ {a b} →
  Type a → (c d : Level) → Type b → Type (a ⊔ b ⊔ lsuc (c ⊔ d))
A ↝[ c ∣ d ]ᴱ B = ∀ {k} → @0 Extensionality? k c d → A ↝[ k ] B

-- Turns extensionality into conditional extensionality.

forget-ext? : ∀ k {a b} → Extensionality a b → Extensionality? k a b
forget-ext? k with extensionality? k
... | without-extensionality _ = _
... | with-extensionality    _ = id

-- A variant of lower-extensionality.

lower-extensionality? :
  ∀ k {a b} â b̂ →
  Extensionality? k (a ⊔ â) (b ⊔ b̂) → Extensionality? k a b
lower-extensionality? k with extensionality? k
... | without-extensionality _ = _
... | with-extensionality    _ = lower-extensionality

-- Some functions that can be used to generalise results.

generalise-ext? :
  ∀ {a b c d} {A : Type a} {B : Type b} →
  A ⇔ B →
  (Extensionality c d → A ↔ B) →
  A ↝[ c ∣ d ] B
generalise-ext? f⇔ f↔ {k = k} with extensionality? k
... | without-extensionality implication         = λ _ → _⇔_.to f⇔
... | without-extensionality logical-equivalence = λ _ → f⇔
... | with-extensionality    _                   = λ ext →
  from-isomorphism (f↔ ext)

generalise-erased-ext? :
  ∀ {a b c d} {A : Type a} {B : Type b} →
  A ⇔ B →
  (@0 Extensionality c d → A ↔ B) →
  A ↝[ c ∣ d ]ᴱ B
generalise-erased-ext? f⇔ f↔ {k = k} with extensionality? k
... | without-extensionality implication         = λ _ → _⇔_.to f⇔
... | without-extensionality logical-equivalence = λ _ → f⇔
... | with-extensionality    _                   = λ ext →
  from-isomorphism (f↔ ext)

generalise-ext?-prop :
  ∀ {a b c d} {A : Type a} {B : Type b} →
  A ⇔ B →
  (Extensionality c d → Is-proposition A) →
  (Extensionality c d → Is-proposition B) →
  A ↝[ c ∣ d ] B
generalise-ext?-prop f⇔ A-prop B-prop =
  generalise-ext?
    f⇔
    (λ ext → _≃_.bijection $
               _↠_.from (Eq.≃↠⇔ (A-prop ext) (B-prop ext)) f⇔)

generalise-erased-ext?-prop :
  ∀ {a b c d} {A : Type a} {B : Type b} →
  A ⇔ B →
  (@0 Extensionality c d → Is-proposition A) →
  (@0 Extensionality c d → Is-proposition B) →
  A ↝[ c ∣ d ]ᴱ B
generalise-erased-ext?-prop f⇔ A-prop B-prop =
  generalise-erased-ext?
    f⇔
    (λ ext → _≃_.bijection $
               _↠_.from (Eq.≃↠⇔ (A-prop ext) (B-prop ext)) f⇔)

generalise-ext?-sym :
  ∀ {a b c d} {A : Type a} {B : Type b} →
  (∀ {k} → Extensionality? ⌊ k ⌋-sym c d → A ↝[ ⌊ k ⌋-sym ] B) →
  A ↝[ c ∣ d ] B
generalise-ext?-sym hyp = generalise-ext? (hyp _) hyp

generalise-erased-ext?-sym :
  ∀ {a b c d} {A : Type a} {B : Type b} →
  (∀ {k} → @0 Extensionality? ⌊ k ⌋-sym c d → A ↝[ ⌊ k ⌋-sym ] B) →
  A ↝[ c ∣ d ]ᴱ B
generalise-erased-ext?-sym hyp = generalise-erased-ext? (hyp _) hyp

-- General results of the kind produced by generalise-ext? are
-- symmetric.

inverse-ext? :
  ∀ {a b c d} {A : Type a} {B : Type b} →
  A ↝[ c ∣ d ] B → B ↝[ c ∣ d ] A
inverse-ext? hyp = generalise-ext?-sym (inverse ⊚ hyp)

inverse-erased-ext? :
  ∀ {a b c d} {A : Type a} {B : Type b} →
  A ↝[ c ∣ d ]ᴱ B → B ↝[ c ∣ d ]ᴱ A
inverse-erased-ext? hyp =
  generalise-erased-ext?-sym (λ ext → inverse (hyp ext))

------------------------------------------------------------------------
-- Lots of properties
------------------------------------------------------------------------

-- Properties of the form A ↝[ k ] B, for arbitrary k, are only stated
-- for bijections or equivalences; converting to the other forms is
-- easy.

------------------------------------------------------------------------
-- Equalities can be converted to all kinds of functions

≡⇒↝ : ∀ k {ℓ} {A B : Type ℓ} → A ≡ B → A ↝[ k ] B
≡⇒↝ k = elim (λ {A B} _ → A ↝[ k ] B) (λ _ → id)

abstract

  -- Some lemmas that can be used to manipulate expressions involving
  -- ≡⇒↝ and refl/sym/trans.

  ≡⇒↝-refl : ∀ {k a} {A : Type a} →
             ≡⇒↝ k (refl A) ≡ id
  ≡⇒↝-refl {k} = elim-refl (λ {A B} _ → A ↝[ k ] B) _

  ≡⇒↝-sym : ∀ k {ℓ} {A B : Type ℓ} {eq : A ≡ B} →
            to-implication (≡⇒↝ ⌊ k ⌋-sym (sym eq)) ≡
            to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym eq))
  ≡⇒↝-sym k {A = A} {eq = eq} = elim¹
    (λ eq → to-implication (≡⇒↝ ⌊ k ⌋-sym (sym eq)) ≡
            to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym eq)))
    (to-implication (≡⇒↝ ⌊ k ⌋-sym (sym (refl A)))      ≡⟨ cong (to-implication ∘ ≡⇒↝ ⌊ k ⌋-sym) sym-refl ⟩
     to-implication (≡⇒↝ ⌊ k ⌋-sym (refl A))            ≡⟨ cong (to-implication {k = ⌊ k ⌋-sym}) ≡⇒↝-refl ⟩
     to-implication {k = ⌊ k ⌋-sym} id                  ≡⟨ to-implication-id ⌊ k ⌋-sym ⟩
     id                                                 ≡⟨ sym $ to-implication-inverse-id k ⟩
     to-implication (inverse {k = k} id)                ≡⟨ cong (to-implication ∘ inverse {k = k}) $ sym ≡⇒↝-refl ⟩∎
     to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym (refl A)))  ∎)
    eq

  ≡⇒↝-trans : ∀ k {ℓ} {A B C : Type ℓ} {A≡B : A ≡ B} {B≡C : B ≡ C} →
              to-implication (≡⇒↝ k (trans A≡B B≡C)) ≡
              to-implication (≡⇒↝ k B≡C ∘ ≡⇒↝ k A≡B)
  ≡⇒↝-trans k {B = B} {A≡B = A≡B} = elim¹
    (λ B≡C → to-implication (≡⇒↝ k (trans A≡B B≡C)) ≡
             to-implication (≡⇒↝ k B≡C ∘ ≡⇒↝ k A≡B))
    (to-implication (≡⇒↝ k (trans A≡B (refl B)))             ≡⟨ cong (to-implication ∘ ≡⇒↝ k) $ trans-reflʳ _ ⟩
     to-implication (≡⇒↝ k A≡B)                              ≡⟨ sym $ cong (λ f → f ∘ to-implication (≡⇒↝ k A≡B)) $ to-implication-id k ⟩
     to-implication {k = k} id ∘ to-implication (≡⇒↝ k A≡B)  ≡⟨ sym $ to-implication-∘ k ⟩
     to-implication (id ∘ ≡⇒↝ k A≡B)                         ≡⟨ sym $ cong (λ f → to-implication (f ∘ ≡⇒↝ k A≡B)) ≡⇒↝-refl ⟩∎
     to-implication (≡⇒↝ k (refl B) ∘ ≡⇒↝ k A≡B)             ∎)
    _

  -- One can sometimes "push" ≡⇒↝ through cong.
  --
  -- This is a generalisation of a lemma due to Thierry Coquand.

  ≡⇒↝-cong : ∀ {k ℓ p A B} {eq : A ≡ B}
             (P : Type ℓ → Type p)
             (P-cong : ∀ {A B} → A ↝[ k ] B → P A ↝[ k ] P B) →
             P-cong (id {A = A}) ≡ id →
             ≡⇒↝ _ (cong P eq) ≡ P-cong (≡⇒↝ _ eq)
  ≡⇒↝-cong {eq = eq} P P-cong P-cong-id = elim¹
    (λ eq → ≡⇒↝ _ (cong P eq) ≡ P-cong (≡⇒↝ _ eq))
    (≡⇒↝ _ (cong P (refl _))  ≡⟨ cong (≡⇒↝ _) $ cong-refl P ⟩
     ≡⇒↝ _ (refl _)           ≡⟨ elim-refl (λ {A B} _ → A ↝[ _ ] B) _ ⟩
     id                       ≡⟨ sym P-cong-id ⟩
     P-cong id                ≡⟨ cong P-cong $ sym $
                                   elim-refl (λ {A B} _ → A ↝[ _ ] B) _ ⟩∎
     P-cong (≡⇒↝ _ (refl _))  ∎)
    eq

  -- One can express ≡⇒↝ in terms of subst.

  ≡⇒↝-in-terms-of-subst :
    ∀ k {ℓ} {A B : Type ℓ} (A≡B : A ≡ B) →
    ≡⇒↝ k A≡B ≡ subst (A ↝[ k ]_) A≡B id
  ≡⇒↝-in-terms-of-subst k {B = B} = elim₁
    (λ {A} A≡B → ≡⇒↝ k A≡B ≡ subst (A ↝[ k ]_) A≡B id)
    (≡⇒↝ k (refl B)                 ≡⟨ ≡⇒↝-refl ⟩
     id                             ≡⟨ sym $ subst-refl _ _ ⟩∎
     subst (B ↝[ k ]_) (refl B) id  ∎)

  ≡⇒↝-in-terms-of-subst-sym :
    ∀ k {ℓ} {A B : Type ℓ} (A≡B : A ≡ B) →
    ≡⇒↝ k A≡B ≡ subst (_↝[ k ] B) (sym A≡B) id
  ≡⇒↝-in-terms-of-subst-sym k {B = B} = elim₁
    (λ {A} A≡B → ≡⇒↝ k A≡B ≡ subst (_↝[ k ] B) (sym A≡B) id)
    (≡⇒↝ k (refl B)                       ≡⟨ ≡⇒↝-refl ⟩
     id                                   ≡⟨ sym $ subst-refl _ _ ⟩
     subst (_↝[ k ] B) (refl B) id        ≡⟨ cong (flip (subst _) _) $ sym sym-refl ⟩∎
     subst (_↝[ k ] B) (sym (refl B)) id  ∎)

  -- One can express subst in terms of ≡⇒↝.

  subst-in-terms-of-≡⇒↝ :
    ∀ k {a p} {A : Type a} {x y} (x≡y : x ≡ y) (P : A → Type p) p →
    subst P x≡y p ≡ to-implication (≡⇒↝ k (cong P x≡y)) p
  subst-in-terms-of-≡⇒↝ k x≡y P p = elim¹

    (λ eq → subst P eq p ≡ to-implication (≡⇒↝ k (cong P eq)) p)

    (subst P (refl _) p                          ≡⟨ subst-refl P p ⟩
     p                                           ≡⟨ sym $ cong (_$ p) (to-implication-id k) ⟩
     to-implication {k = k} id p                 ≡⟨ sym $ cong (λ f → to-implication {k = k} f p) ≡⇒↝-refl ⟩
     to-implication (≡⇒↝ k (refl _)) p           ≡⟨ sym $ cong (λ eq → to-implication (≡⇒↝ k eq) p) $ cong-refl P ⟩∎
     to-implication (≡⇒↝ k (cong P (refl _))) p  ∎)

    x≡y

  subst-in-terms-of-inverse∘≡⇒↝ :
    ∀ k {a p} {A : Type a} {x y} (x≡y : x ≡ y) (P : A → Type p) p →
    subst P (sym x≡y) p ≡
    to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym (cong P x≡y))) p
  subst-in-terms-of-inverse∘≡⇒↝ k x≡y P p =
    subst P (sym x≡y) p                                      ≡⟨ subst-in-terms-of-≡⇒↝ ⌊ k ⌋-sym (sym x≡y) P p ⟩
    to-implication (≡⇒↝ ⌊ k ⌋-sym (cong P (sym x≡y))) p      ≡⟨ cong (λ eq → to-implication (≡⇒↝ ⌊ k ⌋-sym eq) p) (cong-sym P _) ⟩
    to-implication (≡⇒↝ ⌊ k ⌋-sym (sym $ cong P x≡y)) p      ≡⟨ cong (_$ p) (≡⇒↝-sym k) ⟩∎
    to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym (cong P x≡y))) p  ∎

  -- One can express subst id in terms of ≡⇒↝.

  subst-id-in-terms-of-≡⇒↝ :
    ∀ k {a} {A B : Type a} {A≡B : A ≡ B} {x} →
    subst id A≡B x ≡ to-implication (≡⇒↝ k A≡B) x
  subst-id-in-terms-of-≡⇒↝ k {A≡B = A≡B} {x = x} =
    subst id A≡B x                          ≡⟨ subst-in-terms-of-≡⇒↝ k _ _ _ ⟩
    to-implication (≡⇒↝ k (cong id A≡B)) x  ≡⟨ cong (λ eq → to-implication (≡⇒↝ k eq) x) $ sym $ cong-id _ ⟩∎
    to-implication (≡⇒↝ k A≡B) x            ∎

  subst-id-in-terms-of-inverse∘≡⇒↝ :
    ∀ k {a} {A B : Type a} {A≡B : A ≡ B} {y} →
    subst id (sym A≡B) y ≡
    to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym A≡B)) y
  subst-id-in-terms-of-inverse∘≡⇒↝ k {A≡B = A≡B} {y = y} =
    subst id (sym A≡B) y                                      ≡⟨ subst-in-terms-of-inverse∘≡⇒↝ k _ _ _ ⟩
    to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym (cong id A≡B))) y  ≡⟨ cong (λ eq → to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym eq)) y) $ sym $ cong-id _ ⟩∎
    to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym A≡B)) y            ∎

  to-implication-≡⇒↝ :
    ∀ k {ℓ} {A B : Type ℓ} (eq : A ≡ B) →
    to-implication (≡⇒↝ k eq) ≡ ≡⇒↝ implication eq
  to-implication-≡⇒↝ k =
    elim (λ eq → to-implication (≡⇒↝ k eq) ≡ ≡⇒↝ implication eq)
         (λ A → to-implication (≡⇒↝ k (refl A))  ≡⟨ cong to-implication (≡⇒↝-refl {k = k}) ⟩
                to-implication {k = k} id        ≡⟨ to-implication-id k ⟩
                id                               ≡⟨ sym ≡⇒↝-refl ⟩∎
                ≡⇒↝ implication (refl A)         ∎)

------------------------------------------------------------------------
-- _⊎_ is a commutative monoid

-- _⊎_ preserves all kinds of functions.

private

  ⊎-cong-eq : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
                {B₁ : Type b₁} {B₂ : Type b₂} →
              A₁ ⇔ A₂ → B₁ ⇔ B₂ → A₁ ⊎ B₁ ⇔ A₂ ⊎ B₂
  ⊎-cong-eq A₁⇔A₂ B₁⇔B₂ = record
    { to   = ⊎-map (to   A₁⇔A₂) (to   B₁⇔B₂)
    ; from = ⊎-map (from A₁⇔A₂) (from B₁⇔B₂)
    } where open _⇔_

  ⊎-cong-inj : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
                 {B₁ : Type b₁} {B₂ : Type b₂} →
               A₁ ↣ A₂ → B₁ ↣ B₂ → A₁ ⊎ B₁ ↣ A₂ ⊎ B₂
  ⊎-cong-inj A₁↣A₂ B₁↣B₂ = record
    { to        = to′
    ; injective = injective′
    }
    where
    open _↣_

    to′ = ⊎-map (to A₁↣A₂) (to B₁↣B₂)

    abstract
      injective′ : Injective to′
      injective′ {x = inj₁ x} {y = inj₁ y} = cong inj₁ ⊚ injective A₁↣A₂ ⊚ ⊎.cancel-inj₁
      injective′ {x = inj₂ x} {y = inj₂ y} = cong inj₂ ⊚ injective B₁↣B₂ ⊚ ⊎.cancel-inj₂
      injective′ {x = inj₁ x} {y = inj₂ y} = ⊥-elim ⊚ ⊎.inj₁≢inj₂
      injective′ {x = inj₂ x} {y = inj₁ y} = ⊥-elim ⊚ ⊎.inj₁≢inj₂ ⊚ sym

  ⊎-cong-emb : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
                 {B₁ : Type b₁} {B₂ : Type b₂} →
               Embedding A₁ A₂ → Embedding B₁ B₂ →
               Embedding (A₁ ⊎ B₁) (A₂ ⊎ B₂)
  ⊎-cong-emb A₁↣A₂ B₁↣B₂ = record
    { to           = to′
    ; is-embedding = is-embedding′
    }
    where
    open Embedding

    to′ = ⊎-map (to A₁↣A₂) (to B₁↣B₂)

    is-embedding′ : Is-embedding to′
    is-embedding′ (inj₁ x) (inj₁ y) =
      _≃_.is-equivalence $
      Eq.with-other-function
        (inj₁ x ≡ inj₁ y                        ↔⟨ inverse Bijection.≡↔inj₁≡inj₁ ⟩
         x ≡ y                                  ↝⟨ Eq.⟨ _ , is-embedding A₁↣A₂ _ _ ⟩ ⟩
         to A₁↣A₂ x ≡ to A₁↣A₂ y                ↔⟨ Bijection.≡↔inj₁≡inj₁ ⟩□
         inj₁ (to A₁↣A₂ x) ≡ inj₁ (to A₁↣A₂ y)  □)
        _
        (λ eq →
           cong inj₁ (cong (to A₁↣A₂) (⊎.cancel-inj₁ eq))                 ≡⟨ cong-∘ _ _ _ ⟩
           cong (inj₁ ⊚ to A₁↣A₂) (⊎.cancel-inj₁ eq)                      ≡⟨ cong-∘ _ _ _ ⟩
           cong (inj₁ ⊚ to A₁↣A₂ ⊚ [ id , const x ]) eq                   ≡⟨ sym $ trans-reflʳ _ ⟩
           trans (cong (inj₁ ⊚ to A₁↣A₂ ⊚ [ id , const x ]) eq) (refl _)  ≡⟨ cong-respects-relevant-equality
                                                                               {f = inj₁ ⊚ to A₁↣A₂ ⊚ [ id , const x ]}
                                                                               (if_then true else false)
                                                                               [ (λ _ _ → refl _) , (λ _ ()) ] ⟩
           trans (refl _) (cong (⊎-map (to A₁↣A₂) (to B₁↣B₂)) eq)         ≡⟨ trans-reflˡ _ ⟩∎
           cong (⊎-map (to A₁↣A₂) (to B₁↣B₂)) eq                          ∎)

    is-embedding′ (inj₂ x) (inj₂ y) =
      _≃_.is-equivalence $
      Eq.with-other-function
        (inj₂ x ≡ inj₂ y                        ↔⟨ inverse Bijection.≡↔inj₂≡inj₂ ⟩
         x ≡ y                                  ↝⟨ Eq.⟨ _ , is-embedding B₁↣B₂ _ _ ⟩ ⟩
         to B₁↣B₂ x ≡ to B₁↣B₂ y                ↔⟨ Bijection.≡↔inj₂≡inj₂ ⟩□
         inj₂ (to B₁↣B₂ x) ≡ inj₂ (to B₁↣B₂ y)  □)
        _
        (λ eq →
           cong inj₂ (cong (to B₁↣B₂) (⊎.cancel-inj₂ eq))                 ≡⟨ cong-∘ _ _ _ ⟩
           cong (inj₂ ⊚ to B₁↣B₂) (⊎.cancel-inj₂ eq)                      ≡⟨ cong-∘ _ _ _ ⟩
           cong (inj₂ ⊚ to B₁↣B₂ ⊚ [ const x , id ]) eq                   ≡⟨ sym $ trans-reflʳ _ ⟩
           trans (cong (inj₂ ⊚ to B₁↣B₂ ⊚ [ const x , id ]) eq) (refl _)  ≡⟨ cong-respects-relevant-equality
                                                                               {f = inj₂ ⊚ to B₁↣B₂ ⊚ [ const x , id ]}
                                                                               (if_then false else true)
                                                                               [ (λ _ ()) , (λ _ _ → refl _) ] ⟩
           trans (refl _) (cong (⊎-map (to A₁↣A₂) (to B₁↣B₂)) eq)         ≡⟨ trans-reflˡ _ ⟩∎
           cong (⊎-map (to A₁↣A₂) (to B₁↣B₂)) eq                          ∎)

    is-embedding′ (inj₁ x) (inj₂ y) =
      _≃_.is-equivalence $
      Eq.with-other-function
        (inj₁ x ≡ inj₂ y                        ↔⟨ inverse $ Bijection.⊥↔uninhabited ⊎.inj₁≢inj₂ ⟩
         ⊥₀                                     ↔⟨ Bijection.⊥↔uninhabited ⊎.inj₁≢inj₂ ⟩□
         inj₁ (to A₁↣A₂ x) ≡ inj₂ (to B₁↣B₂ y)  □)
        _
        (⊥-elim ⊚ ⊎.inj₁≢inj₂)

    is-embedding′ (inj₂ x) (inj₁ y) =
      _≃_.is-equivalence $
      Eq.with-other-function
        (inj₂ x ≡ inj₁ y                        ↔⟨ inverse $ Bijection.⊥↔uninhabited (⊎.inj₁≢inj₂ ⊚ sym) ⟩
         ⊥₀                                     ↔⟨ Bijection.⊥↔uninhabited (⊎.inj₁≢inj₂ ⊚ sym) ⟩□
         inj₂ (to B₁↣B₂ x) ≡ inj₁ (to A₁↣A₂ y)  □)
        _
        (⊥-elim ⊚ ⊎.inj₁≢inj₂ ⊚ sym)

  ⊎-cong-surj : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
                  {B₁ : Type b₁} {B₂ : Type b₂} →
                A₁ ↠ A₂ → B₁ ↠ B₂ → A₁ ⊎ B₁ ↠ A₂ ⊎ B₂
  ⊎-cong-surj A₁↠A₂ B₁↠B₂ = record
    { logical-equivalence = ⊎-cong-eq (_↠_.logical-equivalence A₁↠A₂)
                                      (_↠_.logical-equivalence B₁↠B₂)
    ; right-inverse-of    =
        [ cong inj₁ ⊚ _↠_.right-inverse-of A₁↠A₂
        , cong inj₂ ⊚ _↠_.right-inverse-of B₁↠B₂
        ]
    }

  ⊎-cong-bij : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
                 {B₁ : Type b₁} {B₂ : Type b₂} →
               A₁ ↔ A₂ → B₁ ↔ B₂ → A₁ ⊎ B₁ ↔ A₂ ⊎ B₂
  ⊎-cong-bij A₁↔A₂ B₁↔B₂ = record
    { surjection      = ⊎-cong-surj (_↔_.surjection A₁↔A₂)
                                    (_↔_.surjection B₁↔B₂)
    ; left-inverse-of =
        [ cong inj₁ ⊚ _↔_.left-inverse-of A₁↔A₂
        , cong inj₂ ⊚ _↔_.left-inverse-of B₁↔B₂
        ]
    }

  ⊎-cong-≃ :
    ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : Type b₁} {B₂ : Type b₂} →
    A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ ⊎ B₁) ≃ (A₂ ⊎ B₂)
  ⊎-cong-≃ A₁≃A₂ B₁≃B₂ =
    from-bijection $ ⊎-cong-bij (from-equivalence A₁≃A₂)
                                (from-equivalence B₁≃B₂)

  ⊎-cong-≃ᴱ :
    ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : Type b₁} {B₂ : Type b₂} →
    A₁ ≃ᴱ A₂ → B₁ ≃ᴱ B₂ → (A₁ ⊎ B₁) ≃ᴱ (A₂ ⊎ B₂)
  ⊎-cong-≃ᴱ f g =
    EEq.[≃]→≃ᴱ (EEq.[proofs] (⊎-cong-≃ (EEq.≃ᴱ→≃ f) (EEq.≃ᴱ→≃ g)))

infixr 1 _⊎-cong_

_⊎-cong_ : ∀ {k a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
             {B₁ : Type b₁} {B₂ : Type b₂} →
           A₁ ↝[ k ] A₂ → B₁ ↝[ k ] B₂ → A₁ ⊎ B₁ ↝[ k ] A₂ ⊎ B₂
_⊎-cong_ {implication}         = ⊎-map
_⊎-cong_ {logical-equivalence} = ⊎-cong-eq
_⊎-cong_ {injection}           = ⊎-cong-inj
_⊎-cong_ {embedding}           = ⊎-cong-emb
_⊎-cong_ {surjection}          = ⊎-cong-surj
_⊎-cong_ {bijection}           = ⊎-cong-bij
_⊎-cong_ {equivalence}         = ⊎-cong-≃
_⊎-cong_ {equivalenceᴱ}        = ⊎-cong-≃ᴱ

-- _⊎_ is commutative.

⊎-comm : ∀ {a b} {A : Type a} {B : Type b} → A ⊎ B ↔ B ⊎ A
⊎-comm = record
  { surjection = record
    { logical-equivalence = record
      { to   = [ inj₂ , inj₁ ]
      ; from = [ inj₂ , inj₁ ]
      }
    ; right-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
    }
  ; left-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
  }

-- _⊎_ is associative.

⊎-assoc : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
          A ⊎ (B ⊎ C) ↔ (A ⊎ B) ⊎ C
⊎-assoc = record
  { surjection = record
    { logical-equivalence = record
      { to   = [ inj₁ ⊚ inj₁ , [ inj₁ ⊚ inj₂ , inj₂ ] ]
      ; from = [ [ inj₁ , inj₂ ⊚ inj₁ ] , inj₂ ⊚ inj₂ ]
      }
    ; right-inverse-of =
        [ [ refl ⊚ inj₁ ⊚ inj₁ , refl ⊚ inj₁ ⊚ inj₂ ] , refl ⊚ inj₂ ]
    }
  ; left-inverse-of =
      [ refl ⊚ inj₁ , [ refl ⊚ inj₂ ⊚ inj₁ , refl ⊚ inj₂ ⊚ inj₂ ] ]
  }

-- ⊥ is a left and right identity of _⊎_.

⊎-left-identity : ∀ {a ℓ} {A : Type a} → ⊥ {ℓ = ℓ} ⊎ A ↔ A
⊎-left-identity = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (inj₁ ()); (inj₂ x) → x }
      ; from = inj₂
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = λ { (inj₁ ()); (inj₂ x) → refl (inj₂ x) }
  }

⊎-right-identity : ∀ {a ℓ} {A : Type a} → A ⊎ ⊥ {ℓ = ℓ} ↔ A
⊎-right-identity {A = A} =
  A ⊎ ⊥  ↔⟨ ⊎-comm ⟩
  ⊥ ⊎ A  ↔⟨ ⊎-left-identity ⟩□
  A      □

-- For logical equivalences _⊎_ is also idempotent. (This lemma could
-- be generalised to cover surjections and implications.)

⊎-idempotent : ∀ {a} {A : Type a} → A ⊎ A ⇔ A
⊎-idempotent = record
  { to   = [ id , id ]
  ; from = inj₁
  }

-- Lemmas that can be used to simplify binary sums where one of the
-- two type arguments is related to the empty type.

drop-⊥-right :
  ∀ {k a b} {A : Type a} {B : Type b} →
  B ↝[ k ] ⊥₀ → A ⊎ B ↝[ k ] A
drop-⊥-right {A = A} {B} B↔⊥ =
  A ⊎ B  ↝⟨ id ⊎-cong B↔⊥ ⟩
  A ⊎ ⊥  ↔⟨ ⊎-right-identity ⟩□
  A      □

drop-⊥-left :
  ∀ {k a b} {A : Type a} {B : Type b} →
  A ↝[ k ] ⊥₀ → A ⊎ B ↝[ k ] B
drop-⊥-left {A = A} {B} A↔⊥ =
  A ⊎ B  ↔⟨ ⊎-comm ⟩
  B ⊎ A  ↝⟨ drop-⊥-right A↔⊥ ⟩□
  B      □

------------------------------------------------------------------------
-- _×_ is a commutative monoid with a zero

-- Σ preserves embeddings. (This definition is used in the proof of
-- _×-cong_.)

Σ-preserves-embeddings :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂}
  (A₁↣A₂ : Embedding A₁ A₂) →
  (∀ x → Embedding (B₁ x) (B₂ (Embedding.to A₁↣A₂ x))) →
  Embedding (Σ A₁ B₁) (Σ A₂ B₂)
Σ-preserves-embeddings {B₁ = B₁} {B₂} A₁↣A₂ B₁↣B₂ = record
  { to           = Σ-map (to A₁↣A₂) (to (B₁↣B₂ _))
  ; is-embedding = λ { (x₁ , x₂) (y₁ , y₂) →
      _≃_.is-equivalence $
      Eq.with-other-function
        ((x₁ , x₂) ≡ (y₁ , y₂)                                   ↝⟨ inverse $ Eq.↔⇒≃ Bijection.Σ-≡,≡↔≡ ⟩

         (∃ λ (eq : x₁ ≡ y₁) → subst B₁ eq x₂ ≡ y₂)              ↝⟨ Eq.Σ-preserves (Embedding.equivalence A₁↣A₂) (λ eq →

             subst B₁ eq x₂ ≡ y₂                                      ↝⟨ Embedding.equivalence (B₁↣B₂ y₁) ⟩

             to (B₁↣B₂ y₁) (subst B₁ eq x₂) ≡ to (B₁↣B₂ y₁) y₂        ↝⟨ ≡⇒↝ _ (cong (_≡ _) $ lemma₁ eq _ y₂) ⟩□

             subst B₂ (cong (to A₁↣A₂) eq) (to (B₁↣B₂ x₁) x₂) ≡
             to (B₁↣B₂ y₁) y₂                                         □) ⟩

         (∃ λ (eq : to A₁↣A₂ x₁ ≡ to A₁↣A₂ y₁) →
            subst B₂ eq (to (B₁↣B₂ x₁) x₂) ≡ to (B₁↣B₂ y₁) y₂)   ↝⟨ Eq.↔⇒≃ Bijection.Σ-≡,≡↔≡ ⟩□

         (to A₁↣A₂ x₁ , to (B₁↣B₂ x₁) x₂) ≡
         (to A₁↣A₂ y₁ , to (B₁↣B₂ y₁) y₂)                        □)
        _
        (elim
          (λ { {y = _ , y₂} eq →
               uncurry Σ-≡,≡→≡
                 (Σ-map (cong (to A₁↣A₂))
                        (_≃_.to (≡⇒↝ _ (cong (_≡ _) $ lemma₁ _ _ y₂)) ⊚
                         cong (to (B₁↣B₂ _)))
                        (Σ-≡,≡←≡ eq)) ≡
               cong (Σ-map (to A₁↣A₂) (to (B₁↣B₂ _))) eq })
          (λ _ →
             uncurry Σ-≡,≡→≡
               (Σ-map (cong (to A₁↣A₂))
                      (_≃_.to (≡⇒↝ _ (cong (_≡ _) $ lemma₁ _ _ _)) ⊚
                       cong (to (B₁↣B₂ _)))
                      (Σ-≡,≡←≡ (refl _)))                                 ≡⟨ cong (λ eq → uncurry Σ-≡,≡→≡
                                                                                            (Σ-map _
                                                                                                   (_≃_.to (≡⇒↝ _ (cong (_≡ _) $ lemma₁ _ _ _)) ⊚
                                                                                                    cong (to (B₁↣B₂ _)))
                                                                                                   eq))
                                                                                  Σ-≡,≡←≡-refl ⟩
             Σ-≡,≡→≡
               (cong (to A₁↣A₂) (refl _))
               (_≃_.to (≡⇒↝ _ (cong (_≡ to (B₁↣B₂ _) _) $ lemma₁ _ _ _))
                  (cong (to (B₁↣B₂ _)) (subst-refl B₁ _)))                ≡⟨ Σ-≡,≡→≡-cong (cong-refl _) (lemma₂ _ _) ⟩

             Σ-≡,≡→≡ (refl _) (subst-refl B₂ _)                           ≡⟨ Σ-≡,≡→≡-refl-subst-refl ⟩

             refl _                                                       ≡⟨ sym $ cong-refl _ ⟩∎

             cong (Σ-map (to A₁↣A₂) (to (B₁↣B₂ _))) (refl _)              ∎)) }
  }
  where
  open Embedding using (to)

  lemma₁ : ∀ {x₁ y₁} (_ : x₁ ≡ y₁) → _
  lemma₁ = elim
    (λ {x₁ y₁} eq → (x₂ : B₁ x₁) (y₂ : B₁ y₁) →
       to (B₁↣B₂ y₁) (subst B₁ eq x₂) ≡
       subst B₂ (cong (to A₁↣A₂) eq) (to (B₁↣B₂ x₁) x₂))
    (λ z₁ x₂ y₂ →
       to (B₁↣B₂ z₁) (subst B₁ (refl z₁) x₂)                    ≡⟨ cong (to (B₁↣B₂ z₁)) $ subst-refl _ _ ⟩
       to (B₁↣B₂ z₁) x₂                                         ≡⟨ sym $ subst-refl _ _ ⟩
       subst B₂ (refl (to A₁↣A₂ z₁)) (to (B₁↣B₂ z₁) x₂)         ≡⟨ cong (λ eq → subst B₂ eq _) (sym $ cong-refl _) ⟩∎
       subst B₂ (cong (to A₁↣A₂) (refl z₁)) (to (B₁↣B₂ z₁) x₂)  ∎)

  lemma₂ = λ x y →
    let eq₁ = cong (flip (subst B₂) _) (sym (cong-refl _))
        eq₂ = cong (to (B₁↣B₂ x)) (subst-refl B₁ y)
    in
    trans eq₁ (_≃_.to (≡⇒↝ _ (cong (_≡ _) $ lemma₁ (refl x) y y)) eq₂)   ≡⟨ cong (λ eq → trans eq₁ (_≃_.to (≡⇒↝ _ (cong (_≡ _) (eq y y))) eq₂)) $
                                                                              elim-refl (λ {x₁ y₁} eq → (x₂ : B₁ x₁) (y₂ : B₁ y₁) →
                                                                                           to (B₁↣B₂ y₁) (subst B₁ eq x₂) ≡
                                                                                           subst B₂ (cong (to A₁↣A₂) eq) (to (B₁↣B₂ x₁) x₂))
                                                                                        _ ⟩
    trans eq₁ (_≃_.to (≡⇒↝ _ $ cong (_≡ _) $
                         trans eq₂ (trans (sym $ subst-refl B₂ _) eq₁))
                 eq₂)                                                    ≡⟨ cong (trans _) $ sym $ subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩

    trans eq₁ (subst (_≡ _)
                 (trans eq₂ (trans (sym $ subst-refl B₂ _) eq₁))
                 eq₂)                                                    ≡⟨ cong (λ eq → trans eq₁ (subst (_≡ _) eq eq₂)) $
                                                                              sym $ sym-sym (trans eq₂ (trans (sym $ subst-refl B₂ _) eq₁)) ⟩
    trans eq₁ (subst (_≡ _)
                 (sym $ sym $
                    trans eq₂ (trans (sym $ subst-refl B₂ _) eq₁))
                 eq₂)                                                    ≡⟨ cong (trans _) $ subst-trans _ ⟩

    trans eq₁ (trans
                 (sym $ trans eq₂ (trans (sym $ subst-refl B₂ _) eq₁))
                 eq₂)                                                    ≡⟨ cong (λ eq → trans eq₁ (trans eq eq₂)) $
                                                                              sym-trans eq₂ (trans (sym $ subst-refl B₂ _) eq₁) ⟩
    trans eq₁ (trans (trans (sym $ trans (sym $ subst-refl B₂ _) eq₁)
                            (sym eq₂))
                     eq₂)                                                ≡⟨ cong (trans _) $ trans-[trans-sym]- _ _ ⟩

    trans eq₁ (sym $ trans (sym $ subst-refl B₂ _) eq₁)                  ≡⟨ cong (trans _) $ sym-trans _ _ ⟩

    trans eq₁ (trans (sym eq₁) (sym $ sym $ subst-refl B₂ _))            ≡⟨ trans--[trans-sym] _ _ ⟩

    sym $ sym $ subst-refl B₂ _                                          ≡⟨ sym-sym _ ⟩∎

    subst-refl B₂ _                                                      ∎

-- _×_ preserves all kinds of functions.

private

  ×-cong-eq : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
                {B₁ : Type b₁} {B₂ : Type b₂} →
              A₁ ⇔ A₂ → B₁ ⇔ B₂ → A₁ × B₁ ⇔ A₂ × B₂
  ×-cong-eq A₁⇔A₂ B₁⇔B₂ = record
    { to   = Σ-map (to   A₁⇔A₂) (to   B₁⇔B₂)
    ; from = Σ-map (from A₁⇔A₂) (from B₁⇔B₂)
    } where open _⇔_

  ×-cong-inj : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
                 {B₁ : Type b₁} {B₂ : Type b₂} →
               A₁ ↣ A₂ → B₁ ↣ B₂ → A₁ × B₁ ↣ A₂ × B₂
  ×-cong-inj {A₁ = A₁} {A₂} {B₁} {B₂} A₁↣A₂ B₁↣B₂ = record
    { to        = to′
    ; injective = injective′
    }
    where
    open _↣_

    to′ : A₁ × B₁ → A₂ × B₂
    to′ = Σ-map (to A₁↣A₂) (to B₁↣B₂)

    abstract
      injective′ : Injective to′
      injective′ to′-x≡to′-y =
        cong₂ _,_ (injective A₁↣A₂ (cong proj₁ to′-x≡to′-y))
                  (injective B₁↣B₂ (cong proj₂ to′-x≡to′-y))

  ×-cong-surj : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
                  {B₁ : Type b₁} {B₂ : Type b₂} →
                A₁ ↠ A₂ → B₁ ↠ B₂ → A₁ × B₁ ↠ A₂ × B₂
  ×-cong-surj A₁↠A₂ B₁↠B₂ = record
    { logical-equivalence = ×-cong-eq (_↠_.logical-equivalence A₁↠A₂)
                                      (_↠_.logical-equivalence B₁↠B₂)
    ; right-inverse-of    = uncurry λ x y →
        cong₂ _,_ (_↠_.right-inverse-of A₁↠A₂ x)
                  (_↠_.right-inverse-of B₁↠B₂ y)
    }

  ×-cong-bij : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
                 {B₁ : Type b₁} {B₂ : Type b₂} →
               A₁ ↔ A₂ → B₁ ↔ B₂ → A₁ × B₁ ↔ A₂ × B₂
  ×-cong-bij A₁↔A₂ B₁↔B₂ = record
    { surjection      = ×-cong-surj (_↔_.surjection A₁↔A₂)
                                    (_↔_.surjection B₁↔B₂)
    ; left-inverse-of = uncurry λ x y →
        cong₂ _,_ (_↔_.left-inverse-of A₁↔A₂ x)
                  (_↔_.left-inverse-of B₁↔B₂ y)
    }

  ×-cong-≃ :
    ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : Type b₁} {B₂ : Type b₂} →
    A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ × B₁) ≃ (A₂ × B₂)
  ×-cong-≃ A₁≃A₂ B₁≃B₂ =
    from-bijection $ ×-cong-bij (from-equivalence A₁≃A₂)
                                (from-equivalence B₁≃B₂)

  ×-cong-≃ᴱ :
    ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : Type b₁} {B₂ : Type b₂} →
    A₁ ≃ᴱ A₂ → B₁ ≃ᴱ B₂ → (A₁ × B₁) ≃ᴱ (A₂ × B₂)
  ×-cong-≃ᴱ f g =
    EEq.[≃]→≃ᴱ (EEq.[proofs] (×-cong-≃ (EEq.≃ᴱ→≃ f) (EEq.≃ᴱ→≃ g)))

infixr 2 _×-cong_

_×-cong_ : ∀ {k a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
             {B₁ : Type b₁} {B₂ : Type b₂} →
           A₁ ↝[ k ] A₂ → B₁ ↝[ k ] B₂ → A₁ × B₁ ↝[ k ] A₂ × B₂
_×-cong_ {implication}         = λ f g → Σ-map f g
_×-cong_ {logical-equivalence} = ×-cong-eq
_×-cong_ {injection}           = ×-cong-inj
_×-cong_ {embedding}           = λ A₁↣A₂ B₁↣B₂ →
                                   Σ-preserves-embeddings
                                     A₁↣A₂ (λ _ → B₁↣B₂)
_×-cong_ {surjection}          = ×-cong-surj
_×-cong_ {bijection}           = ×-cong-bij
_×-cong_ {equivalence}         = ×-cong-≃
_×-cong_ {equivalenceᴱ}        = ×-cong-≃ᴱ

-- The function to-implication is homomorphic with respect to
-- _×-cong_/Σ-map.

to-implication-×-cong :
  ∀ k {a b c d} {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    {A↝B : A ↝[ k ] B} {C↝D : C ↝[ k ] D} →
  to-implication (A↝B ×-cong C↝D) ≡
  Σ-map (to-implication A↝B) (to-implication C↝D)
to-implication-×-cong implication         = refl _
to-implication-×-cong logical-equivalence = refl _
to-implication-×-cong injection           = refl _
to-implication-×-cong embedding           = refl _
to-implication-×-cong surjection          = refl _
to-implication-×-cong bijection           = refl _
to-implication-×-cong equivalence         = refl _
to-implication-×-cong equivalenceᴱ        = refl _

-- _×_ is commutative.

×-comm : ∀ {a b} {A : Type a} {B : Type b} → A × B ↔ B × A
×-comm = record
  { surjection = record
    { logical-equivalence = record
      { to   = uncurry λ x y → (y , x)
      ; from = uncurry λ x y → (y , x)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- Σ is associative.

open Bijection public using (Σ-assoc)

-- _×_ is associative.

×-assoc : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
          A × (B × C) ↔ (A × B) × C
×-assoc = Σ-assoc

-- ⊤ is a left and right identity of _×_ and Σ.

Σ-left-identity : ∀ {a} {A : ⊤ → Type a} → Σ ⊤ A ↔ A tt
Σ-left-identity = record
  { surjection = record
    { logical-equivalence = record
      { to   = proj₂
      ; from = λ x → (tt , x)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

×-left-identity : ∀ {a} {A : Type a} → ⊤ × A ↔ A
×-left-identity = Σ-left-identity

×-right-identity : ∀ {a} {A : Type a} → A × ⊤ ↔ A
×-right-identity {A = A} =
  A × ⊤  ↔⟨ ×-comm ⟩
  ⊤ × A  ↔⟨ ×-left-identity ⟩□
  A      □

-- ⊥ is a left and right zero of _×_ and Σ.

Σ-left-zero : ∀ {ℓ₁ a ℓ₂} {A : ⊥ {ℓ = ℓ₁} → Type a} →
              Σ ⊥ A ↔ ⊥ {ℓ = ℓ₂}
Σ-left-zero = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (() , _) }
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ { (() , _) }
  }

×-left-zero : ∀ {a ℓ₁ ℓ₂} {A : Type a} → ⊥ {ℓ = ℓ₁} × A ↔ ⊥ {ℓ = ℓ₂}
×-left-zero = Σ-left-zero

×-right-zero : ∀ {a ℓ₁ ℓ₂} {A : Type a} → A × ⊥ {ℓ = ℓ₁} ↔ ⊥ {ℓ = ℓ₂}
×-right-zero {A = A} =
  A × ⊥  ↔⟨ ×-comm ⟩
  ⊥ × A  ↔⟨ ×-left-zero ⟩□
  ⊥      □

------------------------------------------------------------------------
-- Some lemmas related to Σ/∃/_×_

-- See also Σ-left-zero and Σ-right-zero above.

-- Σ preserves isomorphisms in its first argument and all kinds of
-- functions in its second argument.

Σ-cong : ∀ {k₁ k₂ a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
           {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
         (A₁↔A₂ : A₁ ↔[ k₁ ] A₂) →
         (∀ x → B₁ x ↝[ k₂ ] B₂ (to-implication A₁↔A₂ x)) →
         Σ A₁ B₁ ↝[ k₂ ] Σ A₂ B₂
Σ-cong {equivalence} {implication}         = λ A₁≃A₂ B₁→B₂ →
                                               Σ-map (from-isomorphism A₁≃A₂) (B₁→B₂ _)
Σ-cong {bijection}   {implication}         = λ A₁↔A₂ B₁→B₂ →
                                               Σ-map (from-isomorphism A₁↔A₂) (B₁→B₂ _)
Σ-cong {equivalence} {logical-equivalence} = Surjection.Σ-cong-⇔       ⊚ from-isomorphism
Σ-cong {bijection}   {logical-equivalence} = Surjection.Σ-cong-⇔       ⊚ from-isomorphism
Σ-cong {equivalence} {injection}           = Eq.∃-preserves-injections
Σ-cong {bijection}   {injection}           = Eq.∃-preserves-injections ⊚ from-isomorphism
Σ-cong {equivalence} {embedding}           = Σ-preserves-embeddings    ⊚ from-isomorphism
Σ-cong {bijection}   {embedding}           = Σ-preserves-embeddings    ⊚ from-isomorphism
Σ-cong {equivalence} {surjection}          = Surjection.Σ-cong         ⊚ from-isomorphism
Σ-cong {bijection}   {surjection}          = Surjection.Σ-cong         ⊚ from-isomorphism
Σ-cong {equivalence} {bijection}           = Eq.∃-preserves-bijections
Σ-cong {bijection}   {bijection}           = Eq.∃-preserves-bijections ⊚ from-isomorphism
Σ-cong {equivalence} {equivalence}         = Eq.Σ-preserves
Σ-cong {bijection}   {equivalence}         = Eq.Σ-preserves            ⊚ from-isomorphism
Σ-cong {equivalence} {equivalenceᴱ}
       {B₂ = B₂}                           = λ f g →
  EEq.[≃]→≃ᴱ
    {to   = λ (x , y) → _≃_.to f x , _≃ᴱ_.to (g x) y}
    {from = λ (x , y) →
                _≃_.from f x
              , _≃ᴱ_.from (g (_≃_.from f x))
                   (subst B₂ (sym (_≃_.right-inverse-of f x)) y)}
    (EEq.[proofs]
       (Eq.Σ-preserves f (EEq.≃ᴱ→≃ ⊚ g)))
Σ-cong {bijection}   {equivalenceᴱ}
       {B₂ = B₂}                           = λ f g →
  EEq.[≃]→≃ᴱ
    {to   = λ (x , y) → _↔_.to f x , _≃ᴱ_.to (g x) y}
    {from = λ (x , y) →
                _↔_.from f x
              , _≃ᴱ_.from (g (_↔_.from f x))
                   (subst B₂
                      (sym (_≃_.right-inverse-of (Eq.↔⇒≃ f) x))
                      y)}
    (EEq.[proofs]
       (Eq.Σ-preserves (from-isomorphism f)
          (EEq.≃ᴱ→≃ ⊚ g)))

-- A variant of Σ-cong.

Σ-cong-contra :
  ∀ {k₁ k₂ a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₂↔A₁ : A₂ ↔[ k₁ ] A₁) →
  (∀ x → B₁ (to-implication A₂↔A₁ x) ↝[ k₂ ] B₂ x) →
  Σ A₁ B₁ ↝[ k₂ ] Σ A₂ B₂
Σ-cong-contra {k₁} {k₂} {A₁ = A₁} {A₂} {B₁} {B₂} A₂↔A₁ B₁↝B₂ =
  Σ-cong A₁↔A₂ B₁↝B₂′
  where
  A₁↔A₂ : A₁ ↔ A₂
  A₁↔A₂ = inverse $ from-isomorphism A₂↔A₁

  B₁↝B₂′ : ∀ x → B₁ x ↝[ k₂ ] B₂ (_↔_.to A₁↔A₂ x)
  B₁↝B₂′ x =
    B₁ x                                        ↝⟨ ≡⇒↝ _ $ cong B₁ $ sym $ _↔_.left-inverse-of A₁↔A₂ _ ⟩
    B₁ (_↔_.from A₁↔A₂ (_↔_.to A₁↔A₂ x))        ↝⟨ ≡⇒↝ _ $ cong (λ f → B₁ (f (_↔_.to A₁↔A₂ x))) $ sym $
                                                     to-implication∘from-isomorphism k₁ bijection ⟩
    B₁ (to-implication A₂↔A₁ (_↔_.to A₁↔A₂ x))  ↝⟨ B₁↝B₂ (_↔_.to A₁↔A₂ x) ⟩□
    B₂ (_↔_.to A₁↔A₂ x)                         □

-- Variants of special cases of Σ-cong-contra.

Σ-cong-contra-→ :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₂↠A₁ : A₂ ↠ A₁) →
  (∀ x → B₁ (_↠_.to A₂↠A₁ x) → B₂ x) →
  Σ A₁ B₁ → Σ A₂ B₂
Σ-cong-contra-→ {B₁ = B₁} A₂↠A₁ B₁→B₂ =
  Σ-map (_↠_.from A₂↠A₁)
        (B₁→B₂ _ ∘ subst B₁ (sym $ _↠_.right-inverse-of A₂↠A₁ _))

Σ-cong-contra-⇔ :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₂↠A₁ : A₂ ↠ A₁) →
  (∀ x → B₁ (_↠_.to A₂↠A₁ x) ⇔ B₂ x) →
  Σ A₁ B₁ ⇔ Σ A₂ B₂
Σ-cong-contra-⇔ A₂↠A₁ B₁⇔B₂ =
  inverse $
  Surjection.Σ-cong-⇔ A₂↠A₁ (inverse ⊚ B₁⇔B₂)

-- ∃ preserves all kinds of functions. One could define
-- ∃-cong = Σ-cong Bijection.id, but the resulting "from" functions
-- would contain an unnecessary use of substitutivity, and I want to
-- avoid that.

private

  ∃-cong-impl : ∀ {a b₁ b₂}
                  {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
                (∀ x → B₁ x → B₂ x) → ∃ B₁ → ∃ B₂
  ∃-cong-impl B₁→B₂ = Σ-map id (λ {x} → B₁→B₂ x)

  ∃-cong-eq : ∀ {a b₁ b₂}
                {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
              (∀ x → B₁ x ⇔ B₂ x) → ∃ B₁ ⇔ ∃ B₂
  ∃-cong-eq B₁⇔B₂ = record
    { to   = ∃-cong-impl (to   ⊚ B₁⇔B₂)
    ; from = ∃-cong-impl (from ⊚ B₁⇔B₂)
    } where open _⇔_

  ∃-cong-surj : ∀ {a b₁ b₂}
                  {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
                (∀ x → B₁ x ↠ B₂ x) → ∃ B₁ ↠ ∃ B₂
  ∃-cong-surj B₁↠B₂ = record
    { logical-equivalence = ∃-cong-eq (_↠_.logical-equivalence ⊚ B₁↠B₂)
    ; right-inverse-of    = uncurry λ x y →
        cong (_,_ x) (_↠_.right-inverse-of (B₁↠B₂ x) y)
    }

  ∃-cong-bij : ∀ {a b₁ b₂}
                 {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
               (∀ x → B₁ x ↔ B₂ x) → ∃ B₁ ↔ ∃ B₂
  ∃-cong-bij B₁↔B₂ = record
    { surjection      = ∃-cong-surj (_↔_.surjection ⊚ B₁↔B₂)
    ; left-inverse-of = uncurry λ x y →
        cong (_,_ x) (_↔_.left-inverse-of (B₁↔B₂ x) y)
    }

  ∃-cong-≃ᴱ :
    ∀ {a b₁ b₂}
      {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
    (∀ x → B₁ x ≃ᴱ B₂ x) → ∃ B₁ ≃ᴱ ∃ B₂
  ∃-cong-≃ᴱ f = EEq.[≃]→≃ᴱ (EEq.[proofs] (Eq.∃-cong (EEq.≃ᴱ→≃ ⊚ f)))

∃-cong : ∀ {k a b₁ b₂}
           {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
         (∀ x → B₁ x ↝[ k ] B₂ x) → ∃ B₁ ↝[ k ] ∃ B₂
∃-cong {implication}         = ∃-cong-impl
∃-cong {logical-equivalence} = ∃-cong-eq
∃-cong {injection}           = Σ-cong Bijection.id
∃-cong {embedding}           = Σ-preserves-embeddings Emb.id
∃-cong {surjection}          = ∃-cong-surj
∃-cong {bijection}           = ∃-cong-bij
∃-cong {equivalence}         = Eq.∃-cong
∃-cong {equivalenceᴱ}        = ∃-cong-≃ᴱ

private

  -- ∃-cong also works for _×_, in which case it is a more general
  -- variant of id ×-cong_:

  ×-cong₂ : ∀ {k a b₁ b₂}
              {A : Type a} {B₁ : Type b₁} {B₂ : Type b₂} →
           (A → B₁ ↝[ k ] B₂) → A × B₁ ↝[ k ] A × B₂
  ×-cong₂ = ∃-cong

-- The following lemma is a more general variant of _×-cong id.

×-cong₁ : ∀ {k a₁ a₂ b}
            {A₁ : Type a₁} {A₂ : Type a₂} {B : Type b} →
          (B → A₁ ↝[ k ] A₂) → A₁ × B ↝[ k ] A₂ × B
×-cong₁ {A₁ = A₁} {A₂} {B} A₁↔A₂ =
  A₁ × B  ↔⟨ ×-comm ⟩
  B × A₁  ↝⟨ ∃-cong A₁↔A₂ ⟩
  B × A₂  ↔⟨ ×-comm ⟩□
  A₂ × B  □

-- Lemmas that can be used to simplify sigma types where one of the
-- two type arguments is (conditionally) related to the unit type.

drop-⊤-right : ∀ {k a b} {A : Type a} {B : A → Type b} →
               ((x : A) → B x ↝[ k ] ⊤) → Σ A B ↝[ k ] A
drop-⊤-right {A = A} {B} B↝⊤ =
  Σ A B  ↝⟨ ∃-cong B↝⊤ ⟩
  A × ⊤  ↔⟨ ×-right-identity ⟩□
  A      □

drop-⊤-left-× : ∀ {k a b} {A : Type a} {B : Type b} →
                (B → A ↝[ k ] ⊤) → A × B ↝[ k ] B
drop-⊤-left-× {A = A} {B} A↝⊤ =
  A × B  ↔⟨ ×-comm ⟩
  B × A  ↝⟨ drop-⊤-right A↝⊤ ⟩□
  B      □

drop-⊤-left-Σ : ∀ {a b} {A : Type a} {B : A → Type b} →
                (A↔⊤ : A ↔ ⊤) →
                Σ A B ↔ B (_↔_.from A↔⊤ tt)
drop-⊤-left-Σ {A = A} {B} A↔⊤ =
  Σ A B                   ↝⟨ inverse $ Σ-cong (inverse A↔⊤) (λ _ → id) ⟩
  Σ ⊤ (B ∘ _↔_.from A↔⊤)  ↝⟨ Σ-left-identity ⟩□
  B (_↔_.from A↔⊤ tt)     □

-- Currying.

currying :
  ∀ {a b c} {A : Type a} {B : A → Type b} {C : Σ A B → Type c} →
  ((p : Σ A B) → C p) ↔ ((x : A) (y : B x) → C (x , y))
currying = record
  { surjection = record
    { logical-equivalence = record { to = curry; from = uncurry }
    ; right-inverse-of    = refl
    }
  ; left-inverse-of = refl
  }

-- Some lemmas relating functions from binary sums and pairs of
-- functions.

Π⊎↠Π×Π :
  ∀ {a b c} {A : Type a} {B : Type b} {C : A ⊎ B → Type c} →
  ((x : A ⊎ B) → C x)
    ↠
  ((x : A) → C (inj₁ x)) × ((y : B) → C (inj₂ y))
Π⊎↠Π×Π = record
  { logical-equivalence = record
    { to   = λ f → f ⊚ inj₁ , f ⊚ inj₂
    ; from = uncurry [_,_]
    }
  ; right-inverse-of = refl
  }

Π⊎↔Π×Π :
  ∀ {a b c} {A : Type a} {B : Type b} {C : A ⊎ B → Type c} →
  ((x : A ⊎ B) → C x)
    ↝[ a ⊔ b ∣ c ]
  ((x : A) → C (inj₁ x)) × ((y : B) → C (inj₂ y))
Π⊎↔Π×Π =
  generalise-ext? (_↠_.logical-equivalence Π⊎↠Π×Π) λ ext → record
    { surjection      = Π⊎↠Π×Π
    ; left-inverse-of = λ _ → apply-ext ext [ refl ⊚ _ , refl ⊚ _ ]
    }

-- ∃ distributes "from the left" over _⊎_.

∃-⊎-distrib-left :
  ∀ {a b c} {A : Type a} {B : A → Type b} {C : A → Type c} →
  (∃ λ x → B x ⊎ C x) ↔ ∃ B ⊎ ∃ C
∃-⊎-distrib-left = record
  { surjection = record
    { logical-equivalence = record
      { to   = uncurry λ x → [ inj₁ ⊚ _,_ x , inj₂ ⊚ _,_ x ]
      ; from = [ Σ-map id inj₁ , Σ-map id inj₂ ]
      }
    ; right-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
    }
  ; left-inverse-of =
      uncurry λ x → [ refl ⊚ _,_ x ⊚ inj₁ , refl ⊚ _,_ x ⊚ inj₂ ]
  }

-- ∃ also distributes "from the right" over _⊎_.

∃-⊎-distrib-right :
  ∀ {a b c} {A : Type a} {B : Type b} {C : A ⊎ B → Type c} →
  Σ (A ⊎ B) C ↔ Σ A (C ⊚ inj₁) ⊎ Σ B (C ⊚ inj₂)
∃-⊎-distrib-right {A = A} {B} {C} = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
    }
  ; left-inverse-of = from∘to
  }
  where
  to : Σ (A ⊎ B) C → Σ A (C ⊚ inj₁) ⊎ Σ B (C ⊚ inj₂)
  to (inj₁ x , y) = inj₁ (x , y)
  to (inj₂ x , y) = inj₂ (x , y)

  from = [ Σ-map inj₁ id , Σ-map inj₂ id ]

  from∘to : ∀ p → from (to p) ≡ p
  from∘to (inj₁ x , y) = refl _
  from∘to (inj₂ x , y) = refl _

-- ∃ is "commutative".

∃-comm : ∀ {a b c} {A : Type a} {B : Type b} {C : A → B → Type c} →
         (∃ λ x → ∃ λ y → C x y) ↔ (∃ λ y → ∃ λ x → C x y)
∃-comm = record
  { surjection = record
    { logical-equivalence = record
      { to   = uncurry λ x → uncurry λ y z → (y , (x , z))
      ; from = uncurry λ x → uncurry λ y z → (y , (x , z))
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- One can introduce an existential by also introducing an equality.

∃-intro : ∀ {a b} {A : Type a} (B : A → Type b) (x : A) →
          B x ↔ ∃ λ y → B y × y ≡ x
∃-intro B x = _≃_.bijection $ Eq.↔→≃
  (λ b → x , b , refl _)
  (λ (y , b , y≡x) → subst B y≡x b)
  (λ (y , b , y≡x) →
     sym $
     Σ-≡,≡→≡
       y≡x
       (subst (λ y → B y × y ≡ x) y≡x (b , y≡x)  ≡⟨ push-subst-, _ _ ⟩
        subst B y≡x b , subst (_≡ x) y≡x y≡x     ≡⟨ cong (_ ,_) subst-trans-sym ⟩
        subst B y≡x b , trans (sym y≡x) y≡x      ≡⟨ cong (_ ,_) $ trans-symˡ _ ⟩∎
        subst B y≡x b , refl x                   ∎))
  (subst-refl B)

-- A variant of ∃-intro.

other-∃-intro :
  ∀ {a b} {A : Type a} (B : A → Type b) (x : A) →
  B x ≃ ∃ λ y → B y × x ≡ y
other-∃-intro B x = Eq.↔→≃
  (λ b → x , b , refl _)
  (λ (y , b , x≡y) → subst B (sym x≡y) b)
  (λ (y , b , x≡y) →
     Σ-≡,≡→≡
       x≡y
       (subst (λ y → B y × x ≡ y) x≡y (subst B (sym x≡y) b , refl x)   ≡⟨ push-subst-, _ _ ⟩
        subst B x≡y (subst B (sym x≡y) b) , subst (x ≡_) x≡y (refl x)  ≡⟨ cong₂ _,_
                                                                            (subst-subst-sym _ _ _)
                                                                            (trans (sym trans-subst) $
                                                                             trans-reflˡ _) ⟩∎
        b , x≡y                                                        ∎))
  (λ b →
     subst B (sym (refl _)) b  ≡⟨ cong (flip (subst B) _) sym-refl ⟩
     subst B (refl _) b        ≡⟨ subst-refl _ _ ⟩∎
     b                         ∎)

-- Another variant of ∃-intro.

∃-introduction :
  ∀ {a b} {A : Type a} {x : A} (B : (y : A) → x ≡ y → Type b) →
  B x (refl x) ↔ ∃ λ y → ∃ λ (x≡y : x ≡ y) → B y x≡y
∃-introduction {x = x} B =
  B x (refl x)                                              ↝⟨ ∃-intro (uncurry B) _ ⟩
  (∃ λ { (y , x≡y) → B y x≡y × (y , x≡y) ≡ (x , refl x) })  ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                  _⇔_.to contractible⇔↔⊤ $
                                                                  ⇒≡ 0 (other-singleton-contractible x)) ⟩
  (∃ λ { (y , x≡y) → B y x≡y × ⊤ })                         ↝⟨ (∃-cong λ _ → ×-right-identity) ⟩
  (∃ λ { (y , x≡y) → B y x≡y })                             ↝⟨ inverse Σ-assoc ⟩□
  (∃ λ y → ∃ λ x≡y → B y x≡y)                               □

-- A non-dependent variant of Σ-≡,≡↔≡.
--
-- This property used to be defined in terms of Σ-≡,≡↔≡, but was
-- changed in order to make it compute in a different way.

≡×≡↔≡ : ∀ {a b} {A : Type a} {B : Type b} {p₁ p₂ : A × B} →
        (proj₁ p₁ ≡ proj₁ p₂ × proj₂ p₁ ≡ proj₂ p₂) ↔ (p₁ ≡ p₂)
≡×≡↔≡ {B = B} {p₁} {p₂} = record
  { surjection = record
    { logical-equivalence = record
      { to   = uncurry (cong₂ _,_)
      ; from = λ eq → cong proj₁ eq , cong proj₂ eq
      }
    ; right-inverse-of = λ eq →
        cong₂ _,_ (cong proj₁ eq) (cong proj₂ eq)  ≡⟨ cong₂-cong-cong _ _ _,_ ⟩
        cong (λ p → proj₁ p , proj₂ p) eq          ≡⟨⟩
        cong id eq                                 ≡⟨ sym $ cong-id _ ⟩∎
        eq                                         ∎
    }
  ; left-inverse-of = λ { (eq₁ , eq₂) →
        cong proj₁ (cong₂ _,_ eq₁ eq₂) , cong proj₂ (cong₂ _,_ eq₁ eq₂)  ≡⟨ cong₂ _,_ (cong-proj₁-cong₂-, eq₁ eq₂) (cong-proj₂-cong₂-, eq₁ eq₂) ⟩∎
        eq₁ , eq₂                                                        ∎
      }
  }

-- If one is given an equality between pairs, where the second
-- components of the pairs are propositional, then one can restrict
-- attention to the first components.

ignore-propositional-component :
  ∀ {a b} {A : Type a} {B : A → Type b} {p q : Σ A B} →
  Is-proposition (B (proj₁ q)) →
  (proj₁ p ≡ proj₁ q) ↔ (p ≡ q)
ignore-propositional-component {B = B} {p₁ , p₂} {q₁ , q₂} Bq₁-prop =
  (p₁ ≡ q₁)                                  ↝⟨ inverse ×-right-identity ⟩
  (p₁ ≡ q₁ × ⊤)                              ↝⟨ ∃-cong (λ _ → inverse $ _⇔_.to contractible⇔↔⊤ (+⇒≡ Bq₁-prop)) ⟩
  (∃ λ (eq : p₁ ≡ q₁) → subst B eq p₂ ≡ q₂)  ↝⟨ Bijection.Σ-≡,≡↔≡ ⟩□
  ((p₁ , p₂) ≡ (q₁ , q₂))                    □

-- Contractible commutes with _×_ (assuming extensionality).

Contractible-commutes-with-× :
  ∀ {x y} {X : Type x} {Y : Type y} →
  Contractible (X × Y) ↝[ x ⊔ y ∣ x ⊔ y ]
  (Contractible X × Contractible Y)
Contractible-commutes-with-× {x = x} {y} =
  generalise-ext?-prop
    (record
       { to = λ cX×Y →
           lemma cX×Y ,
           lemma (H-level.respects-surjection
                    (_↔_.surjection ×-comm) 0 cX×Y)
       ; from = λ { ((x , eq₁) , (y , eq₂)) →
           (x , y) ,
           λ { (x′ , y′) →
             (x  , y)   ≡⟨ cong₂ _,_ (eq₁ x′) (eq₂ y′) ⟩∎
             (x′ , y′)  ∎ } }
       })
    Contractible-propositional
    (λ ext → ×-closure 1 (Contractible-propositional
                            (lower-extensionality y y ext))
                         (Contractible-propositional
                            (lower-extensionality x x ext)))
  where
  lemma : ∀ {x y} {X : Type x} {Y : Type y} →
          Contractible (X × Y) → Contractible X
  lemma ((x , y) , eq) = x , λ x′ →
    x               ≡⟨⟩
    proj₁ (x , y)   ≡⟨ cong proj₁ (eq (x′ , y)) ⟩∎
    proj₁ (x′ , y)  ∎

------------------------------------------------------------------------
-- Some lemmas relating equality of certain kinds of functions to
-- pointwise equality of the underlying functions

-- Equality of equivalences is isomorphic to pointwise equality of the
-- underlying functions (assuming extensionality).

≃-to-≡↔≡ :
  ∀ {a b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  {A : Type a} {B : Type b} {p q : A ≃ B} →
  (∀ x → _≃_.to p x ≡ _≃_.to q x) ↔ p ≡ q
≃-to-≡↔≡ {a} {b} ext {p = p} {q} =
  (∀ x → _≃_.to p x ≡ _≃_.to q x)                                        ↔⟨ Eq.extensionality-isomorphism (lower-extensionality b a ext) ⟩
  _≃_.to p ≡ _≃_.to q                                                    ↝⟨ ignore-propositional-component (Eq.propositional ext _) ⟩
  (_≃_.to p , _≃_.is-equivalence p) ≡ (_≃_.to q , _≃_.is-equivalence q)  ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ Eq.≃-as-Σ) ⟩□
  p ≡ q                                                                  □

-- A variant of the previous result for which both directions compute
-- in certain ways.

≃-to-≡≃≡ :
  ∀ {a b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Extensionality a b →
  {A : Type a} {B : Type b} {p q : A ≃ B} →
  (∀ x → _≃_.to p x ≡ _≃_.to q x) ≃ (p ≡ q)
≃-to-≡≃≡ ext₁ ext₂ {p = p} {q = q} =
  Eq.↔→≃
    (Eq.lift-equality ext₁ ⊚ apply-ext (Eq.good-ext ext₂))
    (flip $ cong ⊚ flip _≃_.to)
    (elim¹
       (λ p≡q →
          Eq.lift-equality ext₁
            (apply-ext (Eq.good-ext ext₂)
               (λ x → cong (λ eq → _≃_.to eq x) p≡q)) ≡
          p≡q)
       (Eq.lift-equality ext₁
          (apply-ext (Eq.good-ext ext₂)
             (λ x → cong (λ eq → _≃_.to eq x) (refl _)))  ≡⟨ (cong (Eq.lift-equality ext₁) $
                                                              cong (apply-ext (Eq.good-ext ext₂)) $
                                                              apply-ext ext₂ λ _ →
                                                              cong-refl _) ⟩
        Eq.lift-equality ext₁
          (apply-ext (Eq.good-ext ext₂) (λ _ → refl _))   ≡⟨ cong (Eq.lift-equality ext₁) $
                                                             Eq.good-ext-refl ext₂ _ ⟩

        Eq.lift-equality ext₁ (refl _)                    ≡⟨ Eq.lift-equality-refl ext₁ ⟩

        cong Eq.⟨ _≃_.to p ,_⟩ _                          ≡⟨ cong (cong Eq.⟨ _≃_.to p ,_⟩) $
                                                             mono₁ 1 (Eq.propositional ext₁ _) _ _ ⟩

        cong Eq.⟨ _≃_.to p ,_⟩ (refl _)                   ≡⟨ cong-refl _ ⟩∎

        refl _                                            ∎))
    (λ p≡q → apply-ext ext₂ λ x →
       cong (λ eq → _≃_.to eq x)
         (Eq.lift-equality ext₁
            (apply-ext (Eq.good-ext ext₂) p≡q))    ≡⟨ elim¹
                                                        (λ {g} p≡g →
                                                           (eq : Is-equivalence g) →
                                                           cong (λ eq → _≃_.to eq x)
                                                             (Eq.lift-equality ext₁ {q = Eq.⟨ _ , eq ⟩} p≡g) ≡
                                                           ext⁻¹ p≡g x)
                                                        (λ eq →
           cong (λ eq → _≃_.to eq x)
             (Eq.lift-equality ext₁ (refl _))              ≡⟨ cong (cong _) $ Eq.lift-equality-refl ext₁ ⟩

           cong (λ eq → _≃_.to eq x)
             (cong Eq.⟨ _≃_.to p ,_⟩ _)                    ≡⟨ cong-∘ _ _ _ ⟩

           cong (const (_≃_.to p x)) _                     ≡⟨ cong-const _ ⟩

           refl _                                          ≡⟨ sym $ cong-refl _ ⟩∎

           ext⁻¹ (refl _) x                                ∎)
                                                        (apply-ext (Eq.good-ext ext₂) p≡q)
                                                        _ ⟩

       ext⁻¹ (apply-ext (Eq.good-ext ext₂) p≡q) x  ≡⟨ cong (_$ x) $
                                                      _≃_.left-inverse-of (Eq.extensionality-isomorphism ext₂) _ ⟩∎
       p≡q x                                       ∎)

-- Equality of equivalences is isomorphic to pointwise equality of the
-- underlying /inverse/ functions (assuming extensionality).

≃-from-≡↔≡ :
  ∀ {a b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  {A : Type a} {B : Type b} {p q : A ≃ B} →
  (∀ x → _≃_.from p x ≡ _≃_.from q x) ↔ p ≡ q
≃-from-≡↔≡ ext {p = p} {q} =
  (∀ x → _≃_.from p x ≡ _≃_.from q x)  ↝⟨ ≃-to-≡↔≡ ext ⟩
  inverse p ≡ inverse q                ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (Eq.inverse-isomorphism ext)) ⟩□
  p ≡ q                                □

-- Equality of bijections between a set and a type is isomorphic to
-- pointwise equality of the underlying functions (assuming
-- extensionality).

↔-to-≡↔≡ :
  ∀ {a b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  {A : Type a} {B : Type b} {p q : A ↔ B} →
  Is-set A →
  (∀ x → _↔_.to p x ≡ _↔_.to q x) ↔ p ≡ q
↔-to-≡↔≡ ext {p = p} {q} A-set =
  (∀ x → _↔_.to p x ≡ _↔_.to q x)                    ↝⟨ id ⟩
  (∀ x → _≃_.to (Eq.↔⇒≃ p) x ≡ _≃_.to (Eq.↔⇒≃ q) x)  ↝⟨ ≃-to-≡↔≡ ext ⟩
  Eq.↔⇒≃ p ≡ Eq.↔⇒≃ q                                ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (Eq.↔↔≃ ext A-set)) ⟩□
  p ≡ q                                              □

-- Equality of bijections between a set and a type is isomorphic to
-- pointwise equality of the underlying /inverse/ functions (assuming
-- extensionality).

↔-from-≡↔≡ :
  ∀ {a b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  {A : Type a} {B : Type b} {p q : A ↔ B} →
  Is-set A →
  (∀ x → _↔_.from p x ≡ _↔_.from q x) ↔ p ≡ q
↔-from-≡↔≡ ext {p = p} {q} A-set =
  (∀ x → _↔_.from p x ≡ _↔_.from q x)                    ↝⟨ id ⟩
  (∀ x → _≃_.from (Eq.↔⇒≃ p) x ≡ _≃_.from (Eq.↔⇒≃ q) x)  ↝⟨ ≃-from-≡↔≡ ext ⟩
  Eq.↔⇒≃ p ≡ Eq.↔⇒≃ q                                    ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (Eq.↔↔≃ ext A-set)) ⟩□
  p ≡ q                                                  □

-- Equality of embeddings is isomorphic to pointwise equality of the
-- underlying functions (assuming extensionality).

Embedding-to-≡↔≡ :
  ∀ {a b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  {A : Type a} {B : Type b} {p q : Embedding A B} →
  (∀ x → Embedding.to p x ≡ Embedding.to q x) ↔ p ≡ q
Embedding-to-≡↔≡ {a} {b} ext {p = p} {q} =
  (∀ x → Embedding.to p x ≡ Embedding.to q x)    ↔⟨ Eq.extensionality-isomorphism (lower-extensionality b a ext) ⟩

  Embedding.to p ≡ Embedding.to q                ↝⟨ ignore-propositional-component (Emb.Is-embedding-propositional ext) ⟩

  (Embedding.to p , Embedding.is-embedding p) ≡
  (Embedding.to q , Embedding.is-embedding q)    ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ Emb.Embedding-as-Σ) ⟩□

  p ≡ q                                          □

------------------------------------------------------------------------
-- Some lemmas related to _≃_

-- Contractibility is isomorphic to equivalence to the unit type
-- (assuming extensionality).

contractible↔≃⊤ :
  ∀ {a} {A : Type a} →
  Extensionality a a →
  Contractible A ↔ (A ≃ ⊤)
contractible↔≃⊤ ext = record
  { surjection = record
    { logical-equivalence = record
      { to   = Eq.↔⇒≃ ∘ _⇔_.to contractible⇔↔⊤
      ; from = _⇔_.from contractible⇔↔⊤ ∘ _≃_.bijection
      }
    ; right-inverse-of = λ _ →
        Eq.lift-equality ext (refl _)
    }
  ; left-inverse-of = λ _ → Contractible-propositional ext _ _
  }

-- Equivalence to the empty type is equivalent to not being inhabited
-- (assuming extensionality).

≃⊥≃¬ :
  ∀ {a ℓ} {A : Type a} →
  Extensionality (a ⊔ ℓ) (a ⊔ ℓ) →
  (A ≃ ⊥ {ℓ = ℓ}) ≃ (¬ A)
≃⊥≃¬ {ℓ = ℓ} {A} ext =
  _↔_.to (Eq.⇔↔≃ ext (Eq.right-closure ext 0 ⊥-propositional)
                     (¬-propositional
                        (lower-extensionality ℓ _ ext))) (record
    { to   = λ eq a → ⊥-elim (_≃_.to eq a)
    ; from = λ ¬a → A  ↔⟨ inverse (Bijection.⊥↔uninhabited ¬a) ⟩□
                    ⊥  □
    })

-- Is-equivalence preserves equality, if we see _≃_ as a form of
-- equality (assuming extensionality).

Is-equivalence-cong :
  ∀ {k a b} {A : Type a} {B : Type b} {f g : A → B} →
  Extensionality? k (a ⊔ b) (a ⊔ b) →
  (∀ x → f x ≡ g x) →
  Is-equivalence f ↝[ k ] Is-equivalence g
Is-equivalence-cong ext f≡g =
  generalise-ext?-prop
    (record
       { to   = Eq.respects-extensional-equality f≡g
       ; from = Eq.respects-extensional-equality (sym ⊚ f≡g)
       })
    (λ ext → Eq.propositional ext _)
    (λ ext → Eq.propositional ext _)
    ext

-- Is-equivalence is pointwise equivalent to CP.Is-equivalence
-- (assuming extensionality).

Is-equivalence≃Is-equivalence-CP :
  ∀ {a b} {A : Type a} {B : Type b} {f : A → B} →
  Is-equivalence f ↝[ a ⊔ b ∣ a ⊔ b ] CP.Is-equivalence f
Is-equivalence≃Is-equivalence-CP =
  generalise-ext?
    HA.Is-equivalence⇔Is-equivalence-CP
    HA.Is-equivalence↔Is-equivalence-CP

-- Two notions of equivalence are pointwise equivalent (assuming
-- extensionality).

≃≃≃-CP :
  ∀ {a b} {A : Type a} {B : Type b} →
  (A ≃ B) ↝[ a ⊔ b ∣ a ⊔ b ] (A CP.≃ B)
≃≃≃-CP {A = A} {B = B} ext =
  A ≃ B                                    ↔⟨ Eq.≃-as-Σ ⟩
  (∃ λ (f : A → B) → Is-equivalence f)     ↝⟨ (∃-cong λ _ → Is-equivalence≃Is-equivalence-CP ext) ⟩□
  (∃ λ (f : A → B) → CP.Is-equivalence f)  □

-- _≃_ is commutative (assuming extensionality).

≃-comm :
  ∀ {a b} {A : Type a} {B : Type b} →
  A ≃ B ↝[ a ⊔ b ∣ a ⊔ b ] B ≃ A
≃-comm =
  generalise-ext?
    Eq.inverse-logical-equivalence
    Eq.inverse-isomorphism

-- Two consequences of the two-out-of-three property.

Is-equivalence≃Is-equivalence-∘ˡ :
  ∀ {a b c} {A : Type a} {B : Type b} {C : Type c}
    {f : B → C} {g : A → B} →
  Is-equivalence f →
  Is-equivalence g ↝[ a ⊔ b ⊔ c ∣ a ⊔ b ⊔ c ] Is-equivalence (f ∘ g)
Is-equivalence≃Is-equivalence-∘ˡ {b = b} {c = c} f-eq =
  generalise-ext?-prop
    (record
       { to   = flip (Eq.Two-out-of-three.f-g (Eq.two-out-of-three _ _))
                  f-eq
       ; from = Eq.Two-out-of-three.g-g∘f (Eq.two-out-of-three _ _) f-eq
       })
    (flip Eq.propositional _ ⊚ lower-extensionality c c)
    (flip Eq.propositional _ ⊚ lower-extensionality b b)

Is-equivalence≃Is-equivalence-∘ʳ :
  ∀ {a b c} {A : Type a} {B : Type b} {C : Type c}
    {f : B → C} {g : A → B} →
  Is-equivalence g →
  Is-equivalence f ↝[ a ⊔ b ⊔ c ∣ a ⊔ b ⊔ c ] Is-equivalence (f ∘ g)
Is-equivalence≃Is-equivalence-∘ʳ {a = a} {b = b} g-eq =
  generalise-ext?-prop
    (record
       { to   = Eq.Two-out-of-three.f-g (Eq.two-out-of-three _ _) g-eq
       ; from = flip
                  (Eq.Two-out-of-three.g∘f-f (Eq.two-out-of-three _ _))
                  g-eq
       })
    (flip Eq.propositional _ ⊚ lower-extensionality a a)
    (flip Eq.propositional _ ⊚ lower-extensionality b b)

------------------------------------------------------------------------
-- _⊎_ and _×_ form a commutative semiring

-- _×_ distributes from the left over _⊎_.

×-⊎-distrib-left : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
                   A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
×-⊎-distrib-left = ∃-⊎-distrib-left

-- _×_ distributes from the right over _⊎_.

×-⊎-distrib-right : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
                    (A ⊎ B) × C ↔ (A × C) ⊎ (B × C)
×-⊎-distrib-right = ∃-⊎-distrib-right

------------------------------------------------------------------------
-- Some lemmas related to functions

-- The non-dependent function space preserves non-dependent functions
-- (contravariantly for the domain).

→-cong-→ : ∀ {a b c d}
             {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
           (B → A) → (C → D) → (A → C) → (B → D)
→-cong-→ B→A C→D = (C→D ∘_) ∘ (_∘ B→A)

private

  -- A lemma used in the implementations of →-cong and →-cong-↠.

  →-cong-⇔ : ∀ {a b c d}
               {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
             A ⇔ B → C ⇔ D → (A → C) ⇔ (B → D)
  →-cong-⇔ A⇔B C⇔D = record
    { to   = →-cong-→ (from A⇔B) (to   C⇔D)
    ; from = →-cong-→ (to   A⇔B) (from C⇔D)
    }
    where open _⇔_

-- The non-dependent function space preserves split surjections
-- (assuming extensionality).

→-cong-↠ : ∀ {a b c d} → Extensionality b d →
           {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
           A ↠ B → C ↠ D → (A → C) ↠ (B → D)
→-cong-↠ {a} {b} {c} {d} ext A↠B C↠D = record
  { logical-equivalence = logical-equiv
  ; right-inverse-of    = right-inv
  }
  where
  open _↠_

  logical-equiv = →-cong-⇔ (_↠_.logical-equivalence A↠B)
                           (_↠_.logical-equivalence C↠D)

  abstract
    right-inv :
      ∀ f → _⇔_.to logical-equiv (_⇔_.from logical-equiv f) ≡ f
    right-inv f = apply-ext ext λ x →
      to C↠D (from C↠D (f (to A↠B (from A↠B x))))  ≡⟨ right-inverse-of C↠D _ ⟩
      f (to A↠B (from A↠B x))                      ≡⟨ cong f $ right-inverse-of A↠B _ ⟩∎
      f x                                          ∎

private

  -- Lemmas used in the implementation of →-cong.

  →-cong-↔ : ∀ {a b c d}
               {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
             Extensionality (a ⊔ b) (c ⊔ d) →
             A ↔ B → C ↔ D → (A → C) ↔ (B → D)
  →-cong-↔ {a} {b} {c} {d} ext A↔B C↔D = record
    { surjection      = surj
    ; left-inverse-of = left-inv
    }
    where
    open _↔_

    surj = →-cong-↠ (lower-extensionality a c ext)
                    (_↔_.surjection A↔B)
                    (_↔_.surjection C↔D)

    abstract
      left-inv :
        ∀ f → _↠_.from surj (_↠_.to surj f) ≡ f
      left-inv f = apply-ext (lower-extensionality b d ext) λ x →
        from C↔D (to C↔D (f (from A↔B (to A↔B x))))  ≡⟨ left-inverse-of C↔D _ ⟩
        f (from A↔B (to A↔B x))                      ≡⟨ cong f $ left-inverse-of A↔B _ ⟩∎
        f x                                          ∎

  →-cong-≃ :
    ∀ {a b c d}
      {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
    Extensionality (a ⊔ b) (c ⊔ d) →
    A ≃ B → C ≃ D → (A → C) ≃ (B → D)
  →-cong-≃ ext A≃B C≃D = record
    { to             = to
    ; is-equivalence = from , proofs
    }
    where
    A→C≃B→D =
      Eq.↔⇒≃ (→-cong-↔ ext (_≃_.bijection A≃B) (_≃_.bijection C≃D))

    to   = _≃_.to   A→C≃B→D
    from = _≃_.from A→C≃B→D

    abstract

      proofs : HA.Proofs to from
      proofs = proj₂ (_≃_.is-equivalence A→C≃B→D)

  →-cong-≃ᴱ :
    ∀ {a b c d}
      {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
    Extensionality (a ⊔ b) (c ⊔ d) →
    A ≃ᴱ B → C ≃ᴱ D → (A → C) ≃ᴱ (B → D)
  →-cong-≃ᴱ ext f g =
    EEq.[≃]→≃ᴱ (EEq.[proofs] (→-cong-≃ ext (EEq.≃ᴱ→≃ f) (EEq.≃ᴱ→≃ g)))

-- The non-dependent function space preserves symmetric kinds of
-- functions (in some cases assuming extensionality).

→-cong : ∀ {k a b c d} →
         Extensionality? ⌊ k ⌋-sym (a ⊔ b) (c ⊔ d) →
         {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
         A ↝[ ⌊ k ⌋-sym ] B → C ↝[ ⌊ k ⌋-sym ] D →
         (A → C) ↝[ ⌊ k ⌋-sym ] (B → D)
→-cong {logical-equivalence} _   = →-cong-⇔
→-cong {bijection}           ext = →-cong-↔  ext
→-cong {equivalence}         ext = →-cong-≃  ext
→-cong {equivalenceᴱ}        ext = →-cong-≃ᴱ ext

-- A variant of →-cong.

→-cong₁ :
  ∀ {k₁ k₂ a b c} →
  Extensionality? k₂ (a ⊔ b) c →
  {A : Type a} {B : Type b} {C : Type c} →
  A ↔[ k₁ ] B → (A → C) ↝[ k₂ ] (B → C)
→-cong₁ ext hyp = generalise-ext?-sym
  (λ ext → →-cong ext (from-bijection (from-isomorphism hyp)) id)
  ext

private

  -- Lemmas used in the implementation of ∀-cong.

  ∀-cong-→ :
    ∀ {a b₁ b₂} {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
    (∀ x → B₁ x → B₂ x) →
    ((x : A) → B₁ x) → ((x : A) → B₂ x)
  ∀-cong-→ B₁→B₂ = B₁→B₂ _ ⊚_

  ∀-cong-⇔ :
    ∀ {a b₁ b₂} {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
    (∀ x → B₁ x ⇔ B₂ x) →
    ((x : A) → B₁ x) ⇔ ((x : A) → B₂ x)
  ∀-cong-⇔ B₁⇔B₂ = record
    { to   = ∀-cong-→ (_⇔_.to   ⊚ B₁⇔B₂)
    ; from = ∀-cong-→ (_⇔_.from ⊚ B₁⇔B₂)
    }

  ∀-cong-bij :
    ∀ {a b₁ b₂} →
    Extensionality a (b₁ ⊔ b₂) →
    {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
    (∀ x → B₁ x ↔ B₂ x) →
    ((x : A) → B₁ x) ↔ ((x : A) → B₂ x)
  ∀-cong-bij {b₂ = b₂} ext B₁↔B₂ = record
    { surjection      = surj
    ; left-inverse-of = left-inverse-of
    }
    where
    surj = Surjection.∀-cong ext (_↔_.surjection ⊚ B₁↔B₂)

    abstract
      left-inverse-of : ∀ f → _↠_.from surj (_↠_.to surj f) ≡ f
      left-inverse-of = λ f →
        apply-ext (lower-extensionality lzero b₂ ext) λ x →
          _↔_.from (B₁↔B₂ x) (_↔_.to (B₁↔B₂ x) (f x))  ≡⟨ _↔_.left-inverse-of (B₁↔B₂ x) (f x) ⟩∎
          f x                                          ∎

  ∀-cong-eq :
    ∀ {a b₁ b₂} →
    Extensionality a (b₁ ⊔ b₂) →
    {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
    (∀ x → B₁ x ≃ B₂ x) →
    ((x : A) → B₁ x) ≃ ((x : A) → B₂ x)
  ∀-cong-eq ext = Eq.↔⇒≃ ⊚ ∀-cong-bij ext ⊚ (_≃_.bijection ⊚_)

  ∀-cong-eqᴱ :
    ∀ {a b₁ b₂} →
    Extensionality a (b₁ ⊔ b₂) →
    {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
    (∀ x → B₁ x ≃ᴱ B₂ x) →
    ((x : A) → B₁ x) ≃ᴱ ((x : A) → B₂ x)
  ∀-cong-eqᴱ ext f =
    EEq.[≃]→≃ᴱ (EEq.[proofs] (∀-cong-eq ext (EEq.≃ᴱ→≃ ⊚ f)))

  ∀-cong-inj :
    ∀ {a b₁ b₂} →
    Extensionality a (b₁ ⊔ b₂) →
    {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
    (∀ x → B₁ x ↣ B₂ x) →
    ((x : A) → B₁ x) ↣ ((x : A) → B₂ x)
  ∀-cong-inj {b₁ = b₁} {b₂} ext B₁↣B₂ = record
    { to        = to
    ; injective = injective
    }
    where
    to = ∀-cong-→ (_↣_.to ⊚ B₁↣B₂)

    abstract
      injective : Injective to
      injective {x = f} {y = g} =
        (λ x → _↣_.to (B₁↣B₂ x) (f x)) ≡ (λ x → _↣_.to (B₁↣B₂ x) (g x))  ↔⟨ inverse $ Eq.extensionality-isomorphism
                                                                                        (lower-extensionality lzero b₁ ext) ⟩
        (∀ x → _↣_.to (B₁↣B₂ x) (f x) ≡ _↣_.to (B₁↣B₂ x) (g x))          ↝⟨ ∀-cong-→ (λ x → _↣_.injective (B₁↣B₂ x)) ⟩
        (∀ x → f x ≡ g x)                                                ↔⟨ Eq.extensionality-isomorphism
                                                                              (lower-extensionality lzero b₂ ext) ⟩□
        f ≡ g                                                            □

  ∀-cong-emb :
    ∀ {a b₁ b₂} →
    Extensionality a (b₁ ⊔ b₂) →
    {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
    (∀ x → Embedding (B₁ x) (B₂ x)) →
    Embedding ((x : A) → B₁ x) ((x : A) → B₂ x)
  ∀-cong-emb {b₁ = b₁} {b₂} ext B₁↣B₂ = record
    { to           = to
    ; is-embedding = is-embedding
    }
    where
    to = ∀-cong-→ (Embedding.to ⊚ B₁↣B₂)

    ext₂ = lower-extensionality lzero b₁ ext

    abstract
      is-embedding : Is-embedding to
      is-embedding f g = _≃_.is-equivalence $
        Eq.with-other-function
          (f ≡ g                                   ↝⟨ inverse $ Eq.extensionality-isomorphism
                                                                  (lower-extensionality lzero b₂ ext) ⟩
           (∀ x → f x ≡ g x)                       ↝⟨ ∀-cong-eq ext (λ x →
                                                        Eq.⟨ _ , Embedding.is-embedding (B₁↣B₂ x) (f x) (g x) ⟩) ⟩
           (∀ x → Embedding.to (B₁↣B₂ x) (f x) ≡
                  Embedding.to (B₁↣B₂ x) (g x))    ↝⟨ Eq.extensionality-isomorphism ext₂ ⟩□

           (λ x → Embedding.to (B₁↣B₂ x) (f x)) ≡
           (λ x → Embedding.to (B₁↣B₂ x) (g x))    □)
          _
          (λ f≡g →
             apply-ext (Eq.good-ext ext₂)
               (λ x → cong (Embedding.to (B₁↣B₂ x)) (ext⁻¹ f≡g x))        ≡⟨⟩

             apply-ext (Eq.good-ext ext₂)
               (λ x → cong (Embedding.to (B₁↣B₂ x)) (cong (_$ x) f≡g))    ≡⟨ cong (apply-ext (Eq.good-ext ext₂)) (apply-ext ext₂ λ _ →
                                                                               cong-∘ _ _ _) ⟩
             apply-ext (Eq.good-ext ext₂)
               (λ x → cong (λ h → Embedding.to (B₁↣B₂ x) (h x)) f≡g)      ≡⟨ cong (apply-ext (Eq.good-ext ext₂)) (apply-ext ext₂ λ _ → sym $
                                                                               cong-∘ _ _ _) ⟩
             apply-ext (Eq.good-ext ext₂)
               (λ x → cong (_$ x)
                        (cong (λ h x → Embedding.to (B₁↣B₂ x) (h x))
                           f≡g))                                          ≡⟨⟩

             apply-ext (Eq.good-ext ext₂)
               (ext⁻¹ (cong (λ h x → Embedding.to (B₁↣B₂ x) (h x)) f≡g))  ≡⟨ _≃_.right-inverse-of (Eq.extensionality-isomorphism ext₂) _ ⟩∎

             cong (λ h x → Embedding.to (B₁↣B₂ x) (h x)) f≡g              ∎)

-- Π preserves all kinds of functions in its second argument (in some
-- cases assuming extensionality).

∀-cong :
  ∀ {k a b₁ b₂} →
  Extensionality? k a (b₁ ⊔ b₂) →
  {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
  (∀ x → B₁ x ↝[ k ] B₂ x) →
  ((x : A) → B₁ x) ↝[ k ] ((x : A) → B₂ x)
∀-cong {implication}         = λ _ → ∀-cong-→
∀-cong {logical-equivalence} = λ _ → ∀-cong-⇔
∀-cong {injection}           = ∀-cong-inj
∀-cong {embedding}           = ∀-cong-emb
∀-cong {surjection}          = Surjection.∀-cong
∀-cong {bijection}           = ∀-cong-bij
∀-cong {equivalence}         = ∀-cong-eq
∀-cong {equivalenceᴱ}        = ∀-cong-eqᴱ

-- The implicit variant of Π preserves all kinds of functions in its
-- second argument (in some cases assuming extensionality).

implicit-∀-cong :
  ∀ {k a b₁ b₂} →
  Extensionality? k a (b₁ ⊔ b₂) →
  {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
  (∀ {x} → B₁ x ↝[ k ] B₂ x) →
  ({x : A} → B₁ x) ↝[ k ] ({x : A} → B₂ x)
implicit-∀-cong ext {A} {B₁} {B₂} B₁↝B₂ =
  ({x : A} → B₁ x)  ↔⟨ Bijection.implicit-Π↔Π ⟩
  ((x : A) → B₁ x)  ↝⟨ ∀-cong ext (λ _ → B₁↝B₂) ⟩
  ((x : A) → B₂ x)  ↔⟨ inverse Bijection.implicit-Π↔Π ⟩□
  ({x : A} → B₂ x)  □

-- Two generalisations of ∀-cong for non-dependent functions.

Π-cong-contra-→ :
  ∀ {a₁ a₂ b₁ b₂}
    {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₂→A₁ : A₂ → A₁) →
  (∀ x → B₁ (A₂→A₁ x) → B₂ x) →
  ((x : A₁) → B₁ x) → ((x : A₂) → B₂ x)
Π-cong-contra-→ {B₁ = B₁} {B₂} A₂→A₁ B₁→B₂ f x =
                $⟨ f (A₂→A₁ x) ⟩
  B₁ (A₂→A₁ x)  ↝⟨ B₁→B₂ x ⟩
  B₂ x          □

Π-cong-→ :
  ∀ {a₁ a₂ b₁ b₂}
    {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₁↠A₂ : A₁ ↠ A₂) →
  (∀ x → B₁ x → B₂ (_↠_.to A₁↠A₂ x)) →
  ((x : A₁) → B₁ x) → ((x : A₂) → B₂ x)
Π-cong-→ {B₁ = B₁} {B₂} A₁↠A₂ B₁→B₂ f x =
                                        $⟨ f (_↠_.from A₁↠A₂ x) ⟩
  B₁ (_↠_.from A₁↠A₂ x)                 ↝⟨ B₁→B₂ (_↠_.from A₁↠A₂ x) ⟩
  B₂ (_↠_.to A₁↠A₂ (_↠_.from A₁↠A₂ x))  ↝⟨ subst B₂ (_↠_.right-inverse-of A₁↠A₂ x) ⟩□
  B₂ x                                  □

-- Two generalisations of ∀-cong for logical equivalences.

Π-cong-⇔ :
  ∀ {a₁ a₂ b₁ b₂}
    {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₁↠A₂ : A₁ ↠ A₂) →
  (∀ x → B₁ x ⇔ B₂ (_↠_.to A₁↠A₂ x)) →
  ((x : A₁) → B₁ x) ⇔ ((x : A₂) → B₂ x)
Π-cong-⇔ {A₁ = A₁} {A₂} {B₁} {B₂} A₁↠A₂ B₁⇔B₂ = record
  { to   = Π-cong-→                A₁↠A₂  (_⇔_.to   ⊚ B₁⇔B₂)
  ; from = Π-cong-contra-→ (_↠_.to A₁↠A₂) (_⇔_.from ⊚ B₁⇔B₂)
  }

Π-cong-contra-⇔ :
  ∀ {a₁ a₂ b₁ b₂}
    {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₂↠A₁ : A₂ ↠ A₁) →
  (∀ x → B₁ (_↠_.to A₂↠A₁ x) ⇔ B₂ x) →
  ((x : A₁) → B₁ x) ⇔ ((x : A₂) → B₂ x)
Π-cong-contra-⇔ {A₁ = A₁} {A₂} {B₁} {B₂} A₂↠A₁ B₁⇔B₂ = record
  { to   = Π-cong-contra-→ (_↠_.to A₂↠A₁) (_⇔_.to   ⊚ B₁⇔B₂)
  ; from = Π-cong-→                A₂↠A₁  (_⇔_.from ⊚ B₁⇔B₂)
  }

-- A generalisation of ∀-cong for split surjections.

Π-cong-↠ :
  ∀ {a₁ a₂ b₁ b₂} →
  Extensionality a₂ b₂ →
  ∀ {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₁↠A₂ : A₁ ↠ A₂) →
  (∀ x → B₁ x ↠ B₂ (_↠_.to A₁↠A₂ x)) →
  ((x : A₁) → B₁ x) ↠ ((x : A₂) → B₂ x)
Π-cong-↠ ext {B₂ = B₂} A₁↠A₂ B₁↠B₂ = record
  { logical-equivalence = equiv
  ; right-inverse-of    = to∘from
  }
  where
  equiv = Π-cong-⇔ A₁↠A₂ (_↠_.logical-equivalence ⊚ B₁↠B₂)

  abstract

    to∘from : ∀ f → _⇔_.to equiv (_⇔_.from equiv f) ≡ f
    to∘from f = apply-ext ext λ x →
      subst B₂ (_↠_.right-inverse-of A₁↠A₂ x)
        (_↠_.to (B₁↠B₂ (_↠_.from A₁↠A₂ x))
           (_↠_.from (B₁↠B₂ (_↠_.from A₁↠A₂ x))
              (f (_↠_.to A₁↠A₂ (_↠_.from A₁↠A₂ x)))))  ≡⟨ cong (subst B₂ (_↠_.right-inverse-of A₁↠A₂ x)) $ _↠_.right-inverse-of (B₁↠B₂ _) _ ⟩

      subst B₂ (_↠_.right-inverse-of A₁↠A₂ x)
        (f (_↠_.to A₁↠A₂ (_↠_.from A₁↠A₂ x)))          ≡⟨ dcong f _ ⟩∎

      f x                                              ∎

-- A generalisation of ∀-cong for injections.

Π-cong-contra-↣ :
  ∀ {a₁ a₂ b₁ b₂} →
  Extensionality a₁ b₁ →
  ∀ {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₂↠A₁ : A₂ ↠ A₁) →
  (∀ x → B₁ (_↠_.to A₂↠A₁ x) ↣ B₂ x) →
  ((x : A₁) → B₁ x) ↣ ((x : A₂) → B₂ x)
Π-cong-contra-↣ ext A₂↠A₁ B₁↣B₂ = record
  { to        = to
  ; injective = injective
  }
  where
  to = Π-cong-contra-→ (_↠_.to A₂↠A₁) (_↣_.to ⊚ B₁↣B₂)

  abstract

    injective : Injective to
    injective {x = f} {y = g} to-f≡to-g = apply-ext ext λ x →

      let x′ = _↠_.to A₂↠A₁ (_↠_.from A₂↠A₁ x) in
                                                       $⟨ to-f≡to-g ⟩
      (λ x → _↣_.to (B₁↣B₂ x) (f (_↠_.to A₂↠A₁ x))) ≡
      (λ x → _↣_.to (B₁↣B₂ x) (g (_↠_.to A₂↠A₁ x)))    ↝⟨ cong (_$ _) ⟩

      _↣_.to (B₁↣B₂ (_↠_.from A₂↠A₁ x)) (f x′) ≡
      _↣_.to (B₁↣B₂ (_↠_.from A₂↠A₁ x)) (g x′)         ↝⟨ _↣_.injective (B₁↣B₂ _) ⟩

      f x′ ≡ g x′                                      ↝⟨ subst (λ x → f x ≡ g x) $ _↠_.right-inverse-of A₂↠A₁ x ⟩□

      f x ≡ g x                                        □

private

  -- Lemmas used in the implementations of Π-cong and Π-cong-contra.

  Π-cong-contra-↠ :
    ∀ {a₁ a₂ b₁ b₂} →
    Extensionality a₂ b₂ →
    ∀ {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
    (A₂≃A₁ : A₂ ≃ A₁) →
    (∀ x → B₁ (_≃_.to A₂≃A₁ x) ↠ B₂ x) →
    ((x : A₁) → B₁ x) ↠ ((x : A₂) → B₂ x)
  Π-cong-contra-↠ ext {B₁ = B₁} A₂≃A₁ B₁↠B₂ = record
    { logical-equivalence = equiv
    ; right-inverse-of    = to∘from
    }
    where
    equiv = Π-cong-contra-⇔ (_≃_.surjection A₂≃A₁)
                            (_↠_.logical-equivalence ⊚ B₁↠B₂)

    abstract

      to∘from : ∀ f → _⇔_.to equiv (_⇔_.from equiv f) ≡ f
      to∘from f = apply-ext ext λ x →
        _↠_.to (B₁↠B₂ x)
          (subst B₁ (_≃_.right-inverse-of A₂≃A₁ (_≃_.to A₂≃A₁ x))
             (_↠_.from (B₁↠B₂ (_≃_.from A₂≃A₁ (_≃_.to A₂≃A₁ x)))
                (f (_≃_.from A₂≃A₁ (_≃_.to A₂≃A₁ x)))))                  ≡⟨ cong (λ eq → _↠_.to (B₁↠B₂ x)
                                                                                           (subst B₁ eq (_↠_.from (B₁↠B₂ _) (f _)))) $ sym $
                                                                              _≃_.left-right-lemma A₂≃A₁ _ ⟩
        _↠_.to (B₁↠B₂ x)
          (subst B₁ (cong (_≃_.to A₂≃A₁) $ _≃_.left-inverse-of A₂≃A₁ x)
             (_↠_.from (B₁↠B₂ (_≃_.from A₂≃A₁ (_≃_.to A₂≃A₁ x)))
                (f (_≃_.from A₂≃A₁ (_≃_.to A₂≃A₁ x)))))                  ≡⟨ cong (_↠_.to (B₁↠B₂ x)) $ sym $ subst-∘ _ _ _ ⟩

        _↠_.to (B₁↠B₂ x)
          (subst (B₁ ∘ _≃_.to A₂≃A₁) (_≃_.left-inverse-of A₂≃A₁ x)
             (_↠_.from (B₁↠B₂ (_≃_.from A₂≃A₁ (_≃_.to A₂≃A₁ x)))
                (f (_≃_.from A₂≃A₁ (_≃_.to A₂≃A₁ x)))))                  ≡⟨ cong (_↠_.to (B₁↠B₂ x)) $
                                                                              dcong (λ x → _↠_.from (B₁↠B₂ x) (f x)) _ ⟩

        _↠_.to (B₁↠B₂ x) (_↠_.from (B₁↠B₂ x) (f x))                      ≡⟨ _↠_.right-inverse-of (B₁↠B₂ x) _ ⟩∎

        f x                                                              ∎

  Π-cong-↔ :
    ∀ {a₁ a₂ b₁ b₂} →
    Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
    ∀ {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
    (A₁≃A₂ : A₁ ≃ A₂) →
    (∀ x → B₁ x ↔ B₂ (_≃_.to A₁≃A₂ x)) →
    ((x : A₁) → B₁ x) ↔ ((x : A₂) → B₂ x)
  Π-cong-↔ {a₁} {a₂} {b₁} {b₂} ext {B₂ = B₂} A₁≃A₂ B₁↔B₂ = record
    { surjection      = surj
    ; left-inverse-of = from∘to
    }
    where
    surj = Π-cong-↠ (lower-extensionality a₁ b₁ ext)
                    (_≃_.surjection A₁≃A₂) (_↔_.surjection ⊚ B₁↔B₂)

    abstract

      from∘to : ∀ f → _↠_.from surj (_↠_.to surj f) ≡ f
      from∘to =
        _↠_.right-inverse-of $
          Π-cong-contra-↠ (lower-extensionality a₂ b₂ ext)
                          {B₁ = B₂}
                          A₁≃A₂
                          (_↔_.surjection ⊚ inverse ⊚ B₁↔B₂)

  Π-cong-contra-↔ :
    ∀ {a₁ a₂ b₁ b₂} →
    Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
    ∀ {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
    (A₂≃A₁ : A₂ ≃ A₁) →
    (∀ x → B₁ (_≃_.to A₂≃A₁ x) ↔ B₂ x) →
    ((x : A₁) → B₁ x) ↔ ((x : A₂) → B₂ x)
  Π-cong-contra-↔ {a₁} {a₂} {b₁} {b₂} ext {B₂ = B₂} A₂≃A₁ B₁↔B₂ = record
    { surjection      = surj
    ; left-inverse-of = from∘to
    }
    where
    surj = Π-cong-contra-↠ (lower-extensionality a₁ b₁ ext)
                           A₂≃A₁ (_↔_.surjection ⊚ B₁↔B₂)

    abstract

      from∘to : ∀ f → _↠_.from surj (_↠_.to surj f) ≡ f
      from∘to =
        _↠_.right-inverse-of $
          Π-cong-↠ (lower-extensionality a₂ b₂ ext)
                   (_≃_.surjection A₂≃A₁)
                   (_↔_.surjection ⊚ inverse ⊚ B₁↔B₂)

  Π-cong-≃ :
    ∀ {a₁ a₂ b₁ b₂} →
    Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
    ∀ {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
    (A₁≃A₂ : A₁ ≃ A₂) →
    (∀ x → B₁ x ≃ B₂ (_≃_.to A₁≃A₂ x)) →
    ((x : A₁) → B₁ x) ≃ ((x : A₂) → B₂ x)
  Π-cong-≃ ext A₁≃A₂ =
    from-isomorphism ⊚ Π-cong-↔ ext A₁≃A₂ ⊚ (from-isomorphism ⊚_)

  Π-cong-≃ᴱ :
    ∀ {a₁ a₂ b₁ b₂} →
    Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
    ∀ {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
    (A₁≃A₂ : A₁ ≃ A₂) →
    (∀ x → B₁ x ≃ᴱ B₂ (_≃_.to A₁≃A₂ x)) →
    ((x : A₁) → B₁ x) ≃ᴱ ((x : A₂) → B₂ x)
  Π-cong-≃ᴱ ext {B₂ = B₂} f g =
    EEq.[≃]→≃ᴱ
      {to   = λ h x → subst B₂ (_≃_.right-inverse-of f x)
                        (_≃ᴱ_.to (g (_≃_.from f x)) (h (_≃_.from f x)))}
      {from = λ h x → _≃ᴱ_.from (g x) (h (_≃_.to f x))}
      (EEq.[proofs] (Π-cong-≃ ext f (EEq.≃ᴱ→≃ ⊚ g)))

  Π-cong-contra-≃ :
    ∀ {a₁ a₂ b₁ b₂} →
    Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
    ∀ {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
    (A₂≃A₁ : A₂ ≃ A₁) →
    (∀ x → B₁ (_≃_.to A₂≃A₁ x) ≃ B₂ x) →
    ((x : A₁) → B₁ x) ≃ ((x : A₂) → B₂ x)
  Π-cong-contra-≃ ext A₂≃A₁ =
    from-isomorphism ⊚ Π-cong-contra-↔ ext A₂≃A₁ ⊚ (from-isomorphism ⊚_)

  Π-cong-contra-≃ᴱ :
    ∀ {a₁ a₂ b₁ b₂} →
    Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
    ∀ {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
    (A₂≃A₁ : A₂ ≃ A₁) →
    (∀ x → B₁ (_≃_.to A₂≃A₁ x) ≃ᴱ B₂ x) →
    ((x : A₁) → B₁ x) ≃ᴱ ((x : A₂) → B₂ x)
  Π-cong-contra-≃ᴱ ext {B₁ = B₁} f g =
    EEq.[≃]→≃ᴱ
      {to   = λ h x → _≃ᴱ_.to (g x) (h (_≃_.to f x))}
      {from = λ h x → subst B₁ (_≃_.right-inverse-of f x)
                        (_≃ᴱ_.from (g (_≃_.from f x))
                           (h (_≃_.from f x)))}
      (EEq.[proofs] (Π-cong-contra-≃ ext f (EEq.≃ᴱ→≃ ⊚ g)))

  Π-cong-↣ :
    ∀ {a₁ a₂ b₁ b₂} →
    Extensionality a₁ b₁ →
    ∀ {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
    (A₁≃A₂ : A₁ ≃ A₂) →
    (∀ x → B₁ x ↣ B₂ (_≃_.to A₁≃A₂ x)) →
    ((x : A₁) → B₁ x) ↣ ((x : A₂) → B₂ x)
  Π-cong-↣ ext {A₁} {A₂} {B₁} {B₂} A₁≃A₂ =
    (∀ x → B₁ x ↣ B₂ (_≃_.to A₁≃A₂ x))                                    ↝⟨ Π-cong-contra-→ (_≃_.from A₁≃A₂) (λ _ → id) ⟩
    (∀ x → B₁ (_≃_.from A₁≃A₂ x) ↣ B₂ (_≃_.to A₁≃A₂ (_≃_.from A₁≃A₂ x)))  ↝⟨ (∀-cong _ λ _ →
                                                                              subst ((B₁ _ ↣_) ⊚ B₂) (_≃_.right-inverse-of A₁≃A₂ _)) ⟩
    (∀ x → B₁ (_≃_.from A₁≃A₂ x) ↣ B₂ x)                                  ↝⟨ Π-cong-contra-↣ ext (_≃_.surjection $ inverse A₁≃A₂) ⟩□
    ((x : A₁) → B₁ x) ↣ ((x : A₂) → B₂ x)                                 □

  Π-cong-contra-Emb :
    ∀ {a₁ a₂ b₁ b₂} →
    Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
    ∀ {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
    (A₂≃A₁ : A₂ ≃ A₁) →
    (∀ x → Embedding (B₁ (_≃_.to A₂≃A₁ x)) (B₂ x)) →
    Embedding ((x : A₁) → B₁ x) ((x : A₂) → B₂ x)
  Π-cong-contra-Emb {a₁} {a₂} {b₁} {b₂} ext A₂≃A₁ B₁↣B₂ = record
    { to           = to
    ; is-embedding = is-embedding
    }
    where

    to = Π-cong-contra-→ (_≃_.to A₂≃A₁) (Embedding.to ⊚ B₁↣B₂)

    abstract

      ext₁₁ : Extensionality a₁ b₁
      ext₁₁ = lower-extensionality a₂ b₂ ext

      ext₂₁ : Extensionality a₂ b₁
      ext₂₁ = lower-extensionality a₁ b₂ ext

      ext₂₂ : Extensionality a₂ b₂
      ext₂₂ = lower-extensionality a₁ b₁ ext

      is-embedding : Is-embedding to
      is-embedding f g =
        _≃_.is-equivalence $
          Eq.with-other-function
            (f ≡ g                                                  ↝⟨ inverse $ Eq.extensionality-isomorphism ext₁₁ ⟩

             (∀ x → f x ≡ g x)                                      ↝⟨ (inverse $ Π-cong-≃ ext A₂≃A₁ λ x →
                                                                        inverse $ Embedding.equivalence (B₁↣B₂ x)) ⟩
             (∀ x → Embedding.to (B₁↣B₂ x) (f (_≃_.to A₂≃A₁ x)) ≡
                    Embedding.to (B₁↣B₂ x) (g (_≃_.to A₂≃A₁ x)))    ↝⟨ Eq.extensionality-isomorphism ext₂₂ ⟩

             (λ {x} → Embedding.to (B₁↣B₂ x)) ⊚ f ⊚ _≃_.to A₂≃A₁ ≡
             (λ {x} → Embedding.to (B₁↣B₂ x)) ⊚ g ⊚ _≃_.to A₂≃A₁    ↔⟨⟩

             to f ≡ to g                                            □)
            _
            (λ f≡g →
               apply-ext (Eq.good-ext ext₂₂)
                 (cong (Embedding.to (B₁↣B₂ _)) ⊚
                    ext⁻¹ f≡g ⊚ _≃_.to A₂≃A₁)                       ≡⟨ sym $ Eq.cong-post-∘-good-ext ext₂₁ ext₂₂ _ ⟩

               cong (Embedding.to (B₁↣B₂ _) ⊚_)
                 (apply-ext (Eq.good-ext ext₂₁)
                    (ext⁻¹ f≡g ⊚ _≃_.to A₂≃A₁))                     ≡⟨ cong (cong (Embedding.to (B₁↣B₂ _) ⊚_)) $ sym $
                                                                       Eq.cong-pre-∘-good-ext ext₂₁ ext₁₁ _ ⟩
               cong (Embedding.to (B₁↣B₂ _) ⊚_)
                 (cong (_⊚ _≃_.to A₂≃A₁)
                   (apply-ext (Eq.good-ext ext₁₁) (ext⁻¹ f≡g)))     ≡⟨ cong-∘ _ _ _ ⟩

               cong to (apply-ext (Eq.good-ext ext₁₁) (ext⁻¹ f≡g))  ≡⟨ cong (cong to) $
                                                                       _≃_.right-inverse-of (Eq.extensionality-isomorphism ext₁₁) _ ⟩∎

               cong to f≡g                                          ∎)

  Π-cong-Emb :
    ∀ {a₁ a₂ b₁ b₂} →
    Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
    ∀ {A₁ : Type a₁} {A₂ : Type a₂}
      {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
    (A₁≃A₂ : A₁ ≃ A₂) →
    (∀ x → Embedding (B₁ x) (B₂ (_≃_.to A₁≃A₂ x))) →
    Embedding ((x : A₁) → B₁ x) ((x : A₂) → B₂ x)
  Π-cong-Emb ext {A₁} {A₂} {B₁} {B₂} A₁≃A₂ =

    (∀ x → Embedding (B₁ x) (B₂ (_≃_.to A₁≃A₂ x)))            ↝⟨ Π-cong-contra-→ (_≃_.from A₁≃A₂) (λ _ → id) ⟩

    (∀ x → Embedding (B₁ (_≃_.from A₁≃A₂ x))
                     (B₂ (_≃_.to A₁≃A₂ (_≃_.from A₁≃A₂ x))))  ↝⟨ (∀-cong _ λ _ → subst (Embedding (B₁ _) ⊚ B₂) (_≃_.right-inverse-of A₁≃A₂ _)) ⟩

    (∀ x → Embedding (B₁ (_≃_.from A₁≃A₂ x)) (B₂ x))          ↝⟨ Π-cong-contra-Emb ext (inverse A₁≃A₂) ⟩□

    Embedding ((x : A₁) → B₁ x) ((x : A₂) → B₂ x)             □

-- A generalisation of ∀-cong.

Π-cong :
  ∀ {k₁ k₂ a₁ a₂ b₁ b₂} →
  Extensionality? k₂ (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
  {A₁ : Type a₁} {A₂ : Type a₂}
  {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₁↔A₂ : A₁ ↔[ k₁ ] A₂) →
  (∀ x → B₁ x ↝[ k₂ ] B₂ (to-implication A₁↔A₂ x)) →
  ((x : A₁) → B₁ x) ↝[ k₂ ] ((x : A₂) → B₂ x)
Π-cong {k₁} {k₂} {a₁} {a₂} {b₁} {b₂}
       ext {A₁} {A₂} {B₁} {B₂} A₁↔A₂ B₁↝B₂ =
  helper k₂ ext (B₁↝B₂′ k₁ A₁↔A₂ B₁↝B₂)
  where
  -- The first four clauses are included as optimisations intended to
  -- make some proof terms easier to work with. These clauses cover
  -- every possible use of B₁↝B₂′ in the expression above.

  B₁↝B₂′ :
    ∀ k₁ (A₁↔A₂ : A₁ ↔[ k₁ ] A₂) →
    (∀ x → B₁ x ↝[ k₂ ] B₂ (to-implication A₁↔A₂ x)) →
    ∀ k x →
    B₁ x ↝[ k₂ ] B₂ (to-implication {k = k} (from-isomorphism A₁↔A₂) x)
  B₁↝B₂′ bijection   _     B₁↝B₂ equivalence = B₁↝B₂
  B₁↝B₂′ bijection   _     B₁↝B₂ surjection  = B₁↝B₂
  B₁↝B₂′ equivalence _     B₁↝B₂ equivalence = B₁↝B₂
  B₁↝B₂′ equivalence _     B₁↝B₂ surjection  = B₁↝B₂
  B₁↝B₂′ k₁          A₁↔A₂ B₁↝B₂ k           = λ x →
    B₁ x                                                    ↝⟨ B₁↝B₂ x ⟩
    B₂ (to-implication A₁↔A₂ x)                             ↝⟨ ≡⇒↝ _ $ cong (λ f → B₂ (f x)) $
                                                                 to-implication∘from-isomorphism k₁ k ⟩□
    B₂ (to-implication {k = k} (from-isomorphism A₁↔A₂) x)  □

  A₁↝A₂ : ∀ {k} → A₁ ↝[ k ] A₂
  A₁↝A₂ = from-isomorphism A₁↔A₂

  l₁ = lower-extensionality a₁ b₁
  l₂ = lower-extensionality a₂ b₂

  helper :
    ∀ k₂ →
    Extensionality? k₂ (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
    (∀ k x → B₁ x ↝[ k₂ ]
             B₂ (to-implication {k = k} (from-isomorphism A₁↔A₂) x)) →
    ((x : A₁) → B₁ x) ↝[ k₂ ] ((x : A₂) → B₂ x)
  helper implication         _   = Π-cong-→          A₁↝A₂ ⊚ (_$ surjection)
  helper logical-equivalence _   = Π-cong-⇔          A₁↝A₂ ⊚ (_$ surjection)
  helper injection           ext = Π-cong-↣ (l₂ ext) A₁↝A₂ ⊚ (_$ equivalence)
  helper embedding           ext = Π-cong-Emb ext    A₁↝A₂ ⊚ (_$ equivalence)
  helper surjection          ext = Π-cong-↠ (l₁ ext) A₁↝A₂ ⊚ (_$ surjection)
  helper bijection           ext = Π-cong-↔  ext     A₁↝A₂ ⊚ (_$ equivalence)
  helper equivalence         ext = Π-cong-≃  ext     A₁↝A₂ ⊚ (_$ equivalence)
  helper equivalenceᴱ        ext = Π-cong-≃ᴱ ext     A₁↝A₂ ⊚ (_$ equivalence)

-- A variant of Π-cong.

Π-cong-contra :
  ∀ {k₁ k₂ a₁ a₂ b₁ b₂} →
  Extensionality? k₂ (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
  {A₁ : Type a₁} {A₂ : Type a₂}
  {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₂↔A₁ : A₂ ↔[ k₁ ] A₁) →
  (∀ x → B₁ (to-implication A₂↔A₁ x) ↝[ k₂ ] B₂ x) →
  ((x : A₁) → B₁ x) ↝[ k₂ ] ((x : A₂) → B₂ x)
Π-cong-contra {k₁} {k₂} {a₁} {a₂} {b₁} {b₂}
              ext {A₁} {A₂} {B₁} {B₂} A₂↔A₁ B₁↝B₂ =
  helper k₂ ext (B₁↝B₂′ k₁ A₂↔A₁ B₁↝B₂)
  where
  -- The first six clauses are included as optimisations intended to
  -- make some proof terms easier to work with. These clauses cover
  -- every possible use of B₁↝B₂′ in the expression above.

  B₁↝B₂′ :
    ∀ k₁ (A₂↔A₁ : A₂ ↔[ k₁ ] A₁) →
    (∀ x → B₁ (to-implication A₂↔A₁ x) ↝[ k₂ ] B₂ x) →
    ∀ k x →
    B₁ (to-implication {k = k} (from-isomorphism A₂↔A₁) x) ↝[ k₂ ] B₂ x
  B₁↝B₂′ bijection   _     B₁↝B₂ equivalence = B₁↝B₂
  B₁↝B₂′ bijection   _     B₁↝B₂ implication = B₁↝B₂
  B₁↝B₂′ bijection   _     B₁↝B₂ surjection  = B₁↝B₂
  B₁↝B₂′ equivalence _     B₁↝B₂ equivalence = B₁↝B₂
  B₁↝B₂′ equivalence _     B₁↝B₂ implication = B₁↝B₂
  B₁↝B₂′ equivalence _     B₁↝B₂ surjection  = B₁↝B₂
  B₁↝B₂′ k₁          A₂↔A₁ B₁↝B₂ k           = λ x →
    B₁ (to-implication {k = k} (from-isomorphism A₂↔A₁) x)  ↝⟨ ≡⇒↝ _ $ cong (λ f → B₁ (f x)) $ sym $ to-implication∘from-isomorphism k₁ k ⟩
    B₁ (to-implication A₂↔A₁ x)                             ↝⟨ B₁↝B₂ x ⟩□
    B₂ x                                                    □

  A₂↝A₁ : ∀ {k} → A₂ ↝[ k ] A₁
  A₂↝A₁ = from-isomorphism A₂↔A₁

  l₁ = lower-extensionality a₁ b₁
  l₂ = lower-extensionality a₂ b₂

  helper :
    ∀ k₂ →
    Extensionality? k₂ (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
    (∀ k x → B₁ (to-implication {k = k} (from-isomorphism A₂↔A₁) x)
               ↝[ k₂ ]
             B₂ x) →
    ((x : A₁) → B₁ x) ↝[ k₂ ] ((x : A₂) → B₂ x)
  helper implication         _   = Π-cong-contra-→          A₂↝A₁ ⊚ (_$ implication)
  helper logical-equivalence _   = Π-cong-contra-⇔          A₂↝A₁ ⊚ (_$ surjection)
  helper injection           ext = Π-cong-contra-↣ (l₂ ext) A₂↝A₁ ⊚ (_$ surjection)
  helper embedding           ext = Π-cong-contra-Emb ext    A₂↝A₁ ⊚ (_$ equivalence)
  helper surjection          ext = Π-cong-contra-↠ (l₁ ext) A₂↝A₁ ⊚ (_$ equivalence)
  helper bijection           ext = Π-cong-contra-↔  ext     A₂↝A₁ ⊚ (_$ equivalence)
  helper equivalence         ext = Π-cong-contra-≃  ext     A₂↝A₁ ⊚ (_$ equivalence)
  helper equivalenceᴱ        ext = Π-cong-contra-≃ᴱ ext     A₂↝A₁ ⊚ (_$ equivalence)

-- A variant of Π-cong for implicit Πs.

implicit-Π-cong :
  ∀ {k₁ k₂ a₁ a₂ b₁ b₂} →
  Extensionality? k₂ (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
  {A₁ : Type a₁} {A₂ : Type a₂}
  {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₁↔A₂ : A₁ ↔[ k₁ ] A₂) →
  (∀ x → B₁ x ↝[ k₂ ] B₂ (to-implication A₁↔A₂ x)) →
  ({x : A₁} → B₁ x) ↝[ k₂ ] ({x : A₂} → B₂ x)
implicit-Π-cong ext {A₁} {A₂} {B₁} {B₂} A₁↔A₂ B₁↝B₂ =
  ({x : A₁} → B₁ x)  ↔⟨ Bijection.implicit-Π↔Π ⟩
  ((x : A₁) → B₁ x)  ↝⟨ Π-cong ext A₁↔A₂ B₁↝B₂ ⟩
  ((x : A₂) → B₂ x)  ↔⟨ inverse Bijection.implicit-Π↔Π ⟩□
  ({x : A₂} → B₂ x)  □

-- A variant of Π-cong-contra for implicit Πs.

implicit-Π-cong-contra :
  ∀ {k₁ k₂ a₁ a₂ b₁ b₂} →
  Extensionality? k₂ (a₁ ⊔ a₂) (b₁ ⊔ b₂) →
  {A₁ : Type a₁} {A₂ : Type a₂}
  {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂} →
  (A₂↔A₁ : A₂ ↔[ k₁ ] A₁) →
  (∀ x → B₁ (to-implication A₂↔A₁ x) ↝[ k₂ ] B₂ x) →
  ({x : A₁} → B₁ x) ↝[ k₂ ] ({x : A₂} → B₂ x)
implicit-Π-cong-contra ext {A₁} {A₂} {B₁} {B₂} A₁↔A₂ B₁↝B₂ =
  ({x : A₁} → B₁ x)  ↔⟨ Bijection.implicit-Π↔Π ⟩
  ((x : A₁) → B₁ x)  ↝⟨ Π-cong-contra ext A₁↔A₂ B₁↝B₂ ⟩
  ((x : A₂) → B₂ x)  ↔⟨ inverse Bijection.implicit-Π↔Π ⟩□
  ({x : A₂} → B₂ x)  □

Π-left-identity : ∀ {a} {A : ⊤ → Type a} → ((x : ⊤) → A x) ↔ A tt
Π-left-identity = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → f tt
      ; from = λ x _ → x
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- A variant of Π-left-identity.

Π-left-identity-↑ :
  ∀ {a ℓ} {A : ↑ ℓ ⊤ → Type a} → ((x : ↑ ℓ ⊤) → A x) ↔ A (lift tt)
Π-left-identity-↑ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → f (lift tt)
      ; from = λ x _ → x
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- A lemma that can be used to simplify a pi type where the domain is
-- isomorphic to the unit type.

drop-⊤-left-Π :
  ∀ {k a b} {A : Type a} {B : A → Type b} →
  Extensionality? k a b →
  (A↔⊤ : A ↔ ⊤) →
  ((x : A) → B x) ↝[ k ] B (_↔_.from A↔⊤ tt)
drop-⊤-left-Π {A = A} {B} ext A↔⊤ =
  ((x : A) → B x)                 ↝⟨ Π-cong-contra ext (inverse A↔⊤) (λ _ → id) ⟩
  ((x : ⊤) → B (_↔_.from A↔⊤ x))  ↔⟨ Π-left-identity ⟩□
  B (_↔_.from A↔⊤ tt)             □

→-right-zero : ∀ {a} {A : Type a} → (A → ⊤) ↔ ⊤
→-right-zero = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ _ → tt
      ; from = λ _ _ → tt
      }
    ; right-inverse-of = λ _ → refl tt
    }
  ; left-inverse-of = λ _ → refl (λ _ → tt)
  }

-- A lemma relating function types with the empty type as domain and
-- the unit type.

Π⊥↔⊤ : ∀ {ℓ a} {A : ⊥ {ℓ = ℓ} → Type a} →
       ((x : ⊥) → A x) ↝[ ℓ ∣ a ] ⊤
Π⊥↔⊤ = generalise-ext? Π⊥⇔⊤ λ ext → record
  { surjection = record
    { logical-equivalence = Π⊥⇔⊤
    ; right-inverse-of    = λ _ → refl _
    }
  ; left-inverse-of = λ _ → apply-ext ext (λ x → ⊥-elim x)
  }
  where
  Π⊥⇔⊤ = record
    { to   = _
    ; from = λ _ x → ⊥-elim x
    }

-- A lemma relating ¬ ⊥ and ⊤.

¬⊥↔⊤ : ∀ {ℓ} → ¬ ⊥ {ℓ = ℓ} ↝[ ℓ ∣ lzero ] ⊤
¬⊥↔⊤ = Π⊥↔⊤

-- Simplification lemmas for types of the form A → A → B.

→→↠→ :
  ∀ {a b} {A : Type a} {B : Type b} →
  (A → A → B) ↠ (A → B)
→→↠→ = record
  { logical-equivalence = record
    { to   = λ f x → f x x
    ; from = λ f x _ → f x
    }
  ; right-inverse-of = refl
  }

→→proposition↔→ :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality a (a ⊔ b) →
  Is-proposition B →
  (A → A → B) ↔ (A → B)
→→proposition↔→ {a} ext B-prop = record
  { surjection      = →→↠→
  ; left-inverse-of = λ f →
      apply-ext ext λ x →
        (Π-closure (lower-extensionality lzero a ext) 1 λ _ →
         B-prop) _ _
  }

-- If A is inhabited, then there is a split surjection from A → B to
-- B.

inhabited→↠ :
  ∀ {a b} {A : Type a} {B : Type b} →
  A → (A → B) ↠ B
inhabited→↠ x = record
  { logical-equivalence = record
    { to   = _$ x
    ; from = const
    }
  ; right-inverse-of = refl
  }

-- If A is inhabited and B is a proposition, then A → B and B are
-- isomorphic (assuming extensionality).

inhabited→proposition↔ :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality a b →
  Is-proposition B →
  A → (A → B) ↔ B
inhabited→proposition↔ ext B-prop x = record
  { surjection      = inhabited→↠ x
  ; left-inverse-of = λ f →
      apply-ext ext λ y →
        f x  ≡⟨ B-prop _ _ ⟩∎
        f y  ∎
  }

-- Π is "commutative".

Π-comm : ∀ {a b c} {A : Type a} {B : Type b} {C : A → B → Type c} →
         (∀ x y → C x y) ↔ (∀ y x → C x y)
Π-comm = record
  { surjection = record
    { logical-equivalence = record { to = flip; from = flip }
    ; right-inverse-of    = refl
    }
  ; left-inverse-of = refl
  }

-- Π and Σ commute (in a certain sense).

open Bijection public using (ΠΣ-comm)

-- The implicit variant of Π and Σ commute (in a certain sense).

implicit-ΠΣ-comm :
  ∀ {a b c} {A : Type a} {B : A → Type b} {C : (x : A) → B x → Type c} →
  (∀ {x} → ∃ λ (y : B x) → C x y)
    ↔
  (∃ λ (f : ∀ {x} → B x) → ∀ {x} → C x f)
implicit-ΠΣ-comm {A = A} {B} {C} =
  (∀ {x} → ∃ λ (y : B x) → C x y)          ↝⟨ Bijection.implicit-Π↔Π ⟩
  (∀ x → ∃ λ (y : B x) → C x y)            ↝⟨ ΠΣ-comm ⟩
  (∃ λ (f : ∀ x → B x) → ∀ x → C x (f x))  ↝⟨ inverse $ Σ-cong Bijection.implicit-Π↔Π (λ _ → Bijection.implicit-Π↔Π) ⟩□
  (∃ λ (f : ∀ {x} → B x) → ∀ {x} → C x f)  □

-- Some variants of De Morgan's laws.

¬⊎↠¬×¬ :
  ∀ {a b} {A : Type a} {B : Type b} →
  ¬ (A ⊎ B) ↠ ¬ A × ¬ B
¬⊎↠¬×¬ = record
  { logical-equivalence = record
    { to   = λ ¬[A⊎B] → ¬[A⊎B] ∘ inj₁ , ¬[A⊎B] ∘ inj₂
    ; from = λ (¬A , ¬B) → [ ¬A , ¬B ]
    }
  ; right-inverse-of = refl
  }

¬⊎↔¬×¬ :
  ∀ {a b} {A : Type a} {B : Type b} →
  ¬ (A ⊎ B) ↝[ a ⊔ b ∣ lzero ] ¬ A × ¬ B
¬⊎↔¬×¬ = generalise-ext?
  (_↠_.logical-equivalence ¬⊎↠¬×¬)
  (λ ext → record
     { surjection      = ¬⊎↠¬×¬
     ; left-inverse-of = λ _ →
         apply-ext ext [ (λ _ → refl _) , (λ _ → refl _) ]
     })

¬⊎¬→×¬ :
  ∀ {a b} {A : Type a} {B : Type b} →
  ¬ A ⊎ ¬ B → ¬ (A × B)
¬⊎¬→×¬ = [ (_∘ proj₁) , (_∘ proj₂) ]

¬⊎¬⇔¬× :
  ∀ {a b} {A : Type a} {B : Type b} →
  Dec (¬ A) → Dec (¬ B) →
  ¬ A ⊎ ¬ B ⇔ ¬ (A × B)
¬⊎¬⇔¬× (yes ¬A) _ = record
  { to   = ¬⊎¬→×¬
  ; from = λ _ → inj₁ ¬A
  }
¬⊎¬⇔¬× _ (yes ¬B) = record
  { to   = ¬⊎¬→×¬
  ; from = λ _ → inj₂ ¬B
  }
¬⊎¬⇔¬× (no ¬¬A) (no ¬¬B) = record
  { to   = ¬⊎¬→×¬
  ; from = λ ¬[A×B] →
             ⊥-elim $
             ¬¬A λ a →
             ¬¬B λ b →
             ¬[A×B] (a , b)
  }

¬⊎¬↠¬× :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) lzero →
  Dec (¬ A) → Dec (¬ B) →
  ¬ A ⊎ ¬ B ↠ ¬ (A × B)
¬⊎¬↠¬× ext dec-¬A dec-¬B = record
  { logical-equivalence = ¬⊎¬⇔¬× dec-¬A dec-¬B
  ; right-inverse-of    = λ _ → ¬-propositional ext _ _
  }

-- A variant of extensionality-isomorphism for functions with implicit
-- arguments.

implicit-extensionality-isomorphism :
  ∀ {k a b} →
  Extensionality a b →
  {A : Type a} {B : A → Type b} {f g : {x : A} → B x} →
  (∀ x → f {x} ≡ g {x}) ↔[ k ] ((λ {x} → f {x}) ≡ g)
implicit-extensionality-isomorphism ext {f = f} {g} =
  (∀ x → f {x} ≡ g {x})            ↔⟨ Eq.extensionality-isomorphism ext ⟩
  ((λ x → f {x}) ≡ (λ x → g {x}))  ↔⟨ inverse $ Eq.≃-≡ (Eq.↔⇒≃ (inverse Bijection.implicit-Π↔Π)) ⟩□
  ((λ {x} → f {x}) ≡ g)            □

private

  -- The forward direction of
  -- implicit-extensionality-isomorphism {k = bijection} computes in a
  -- certain way.
  --
  -- Note that (at the time of writing) the proof below fails if the
  -- two occurrences of "inverse" in the previous proof are removed.

  to-implicit-extensionality-isomorphism :
    ∀ {a b}
    (ext : Extensionality a b) {A : Type a} {B : A → Type b}
    {f g : {x : A} → B x} (f≡g : ∀ x → f {x} ≡ g {x}) →
    _↔_.to (implicit-extensionality-isomorphism ext) f≡g
      ≡
    implicit-extensionality (Eq.good-ext ext) f≡g
  to-implicit-extensionality-isomorphism _ _ = refl _

-- The Yoneda lemma, as given in the HoTT book, but specialised to the
-- opposite of the category of sets and functions, and with some
-- naturality properties omitted. (The proof uses extensionality.)

yoneda :
  ∀ {a b X} →
  Extensionality (lsuc a) (lsuc a ⊔ b) →
  (F : Set a → Set b) →
  (map : ∀ {A B} → (⌞ A ⌟ → ⌞ B ⌟) → ⌞ F A ⌟ → ⌞ F B ⌟) →
  (∀ {A} {x : ⌞ F A ⌟} → map id x ≡ x) →
  (∀ {A B C f g x} →
   (map {A = B} {B = C} f ∘ map {A = A} g) x ≡ map (f ∘ g) x) →

  ⌞ F X ⌟
    ↔
  ∃ λ (γ : ∀ Y → (⌞ X ⌟ → ⌞ Y ⌟) → ⌞ F Y ⌟) →
    ∀ Y₁ Y₂ f g → map f (γ Y₁ g) ≡ γ Y₂ (f ∘ g)

yoneda {a} {X = X} ext F map map-id map-∘ = record
  { surjection = record
    { logical-equivalence = record
      { to = λ x → (λ _ f → map f x) , λ _ _ f g →
          map f (map g x)  ≡⟨ map-∘ ⟩∎
          map (f ∘ g) x    ∎
      ; from = λ { (γ , _) → γ X id }
      }
    ; right-inverse-of = λ { (γ , h) → Σ-≡,≡→≡

        ((λ _ f → map f (γ X id))  ≡⟨ (apply-ext (lower-extensionality lzero (lsuc a) ext) λ Y →
                                       apply-ext (lower-extensionality _     (lsuc a) ext) λ f →
                                       h X Y f id) ⟩∎
         (λ Y f → γ Y f)           ∎)

        ((Π-closure                                      ext  1 λ _  →
          Π-closure (lower-extensionality lzero (lsuc a) ext) 1 λ Y₂ →
          Π-closure (lower-extensionality _     (lsuc a) ext) 1 λ _  →
          Π-closure (lower-extensionality _     (lsuc a) ext) 1 λ _  →
          proj₂ (F Y₂)) _ _) }
    }
  ; left-inverse-of = λ x →
      map id x  ≡⟨ map-id ⟩∎
      x         ∎
  }

-- There is a (split) surjection from products of equality
-- isomorphisms to equalities.

Π≡↔≡-↠-≡ : ∀ k {a} {A : Type a} (x y : A) →
           (∀ z → (z ≡ x) ↔[ k ] (z ≡ y)) ↠ (x ≡ y)
Π≡↔≡-↠-≡ k x y = record
  { logical-equivalence = record { to = to; from = from }
  ; right-inverse-of    = to∘from
  }
  where
  to : (∀ z → (z ≡ x) ↔[ k ] (z ≡ y)) → x ≡ y
  to f = to-implication (f x) (refl x)

  from′ : x ≡ y → ∀ z → (z ≡ x) ↔ (z ≡ y)
  from′ x≡y z = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ z≡x → trans z≡x      x≡y
        ; from = λ z≡y → trans z≡y (sym x≡y)
        }
      ; right-inverse-of = λ z≡y → trans-[trans-sym]- z≡y x≡y
      }
    ; left-inverse-of = λ z≡x → trans-[trans]-sym z≡x x≡y
    }

  from : x ≡ y → ∀ z → (z ≡ x) ↔[ k ] (z ≡ y)
  from x≡y z = from-bijection (from′ x≡y z)

  abstract
    to∘from : ∀ x≡y → to (from x≡y) ≡ x≡y
    to∘from x≡y =
      to (from x≡y)       ≡⟨ sym $ cong (λ f → f (refl x)) $ to-implication∘from-isomorphism bijection ⌊ k ⌋-iso ⟩
      trans (refl x) x≡y  ≡⟨ trans-reflˡ _ ⟩∎
      x≡y                 ∎

-- Products of equivalences of equalities are isomorphic to equalities
-- (assuming extensionality).

Π≡≃≡-↔-≡ :
  ∀ {a} {A : Type a} (x y : A) →
  (∀ z → (z ≡ x) ≃ (z ≡ y)) ↝[ a ∣ a ] (x ≡ y)
Π≡≃≡-↔-≡ {a = a} x y =
  generalise-ext? (_↠_.logical-equivalence surj)
                  (λ ext → record
                     { surjection      = surj
                     ; left-inverse-of = from∘to ext
                     })
  where
  surj = Π≡↔≡-↠-≡ equivalence x y

  open _↠_ surj

  abstract
    from∘to :
      Extensionality a a →
      ∀ f → from (to f) ≡ f
    from∘to ext f =
      apply-ext ext λ z → Eq.lift-equality ext $ apply-ext ext λ z≡x →
        trans z≡x (_≃_.to (f x) (refl x))  ≡⟨ elim (λ {u v} u≡v →
                                                      (f : ∀ z → (z ≡ v) ≃ (z ≡ y)) →
                                                      trans u≡v (_≃_.to (f v) (refl v)) ≡
                                                      _≃_.to (f u) u≡v)
                                                   (λ _ _ → trans-reflˡ _)
                                                   z≡x f ⟩∎
        _≃_.to (f z) z≡x                   ∎

-- One can introduce a universal quantifier by also introducing an
-- equality (perhaps assuming extensionality).

∀-intro :
  ∀ {a b} {A : Type a} {x : A} (B : (y : A) → x ≡ y → Type b) →
  B x (refl x) ↝[ a ∣ a ⊔ b ] (∀ y (x≡y : x ≡ y) → B y x≡y)
∀-intro B = generalise-ext? (∀-intro-⇔ B) (λ ext → ∀-intro-↔ ext B)
  where
  ∀-intro-⇔ : ∀ {a b} {A : Type a} {x : A}
              (B : (y : A) → x ≡ y → Type b) →
              B x (refl x) ⇔ (∀ y (x≡y : x ≡ y) → B y x≡y)
  ∀-intro-⇔ {x = x} B = record
    { to   = λ b y x≡y →
               subst (uncurry B)
                     (proj₂ (other-singleton-contractible x) (y , x≡y))
                     b
    ; from = λ f → f x (refl x)
    }

  ∀-intro-↔ : ∀ {a b} →
              Extensionality a (a ⊔ b) →
              {A : Type a} {x : A} (B : (y : A) → x ≡ y → Type b) →
              B x (refl x) ↔ (∀ y (x≡y : x ≡ y) → B y x≡y)
  ∀-intro-↔ {a} ext {x = x} B = record
    { surjection = record
      { logical-equivalence = ∀-intro-⇔ B
      ; right-inverse-of    = to∘from
      }
    ; left-inverse-of = from∘to
    }
    where

    abstract

      from∘to :
        ∀ b → _⇔_.from (∀-intro-⇔ B) (_⇔_.to (∀-intro-⇔ B) b) ≡ b
      from∘to b =
        subst (uncurry B)
              (proj₂ (other-singleton-contractible x) (x , refl x)) b  ≡⟨ cong (λ eq → subst (uncurry B) eq b) $
                                                                               other-singleton-contractible-refl x ⟩
        subst (uncurry B) (refl (x , refl x)) b                        ≡⟨ subst-refl (uncurry B) _ ⟩∎
        b                                                              ∎

      to∘from :
        ∀ b → _⇔_.to (∀-intro-⇔ B) (_⇔_.from (∀-intro-⇔ B) b) ≡ b
      to∘from f =
        apply-ext ext λ y →
        apply-ext (lower-extensionality lzero a ext) λ x≡y →
          elim¹ (λ {y} x≡y →
                   subst (uncurry B)
                         (proj₂ (other-singleton-contractible x)
                                (y , x≡y))
                         (f x (refl x)) ≡
                   f y x≡y)
                (subst (uncurry B)
                       (proj₂ (other-singleton-contractible x)
                              (x , refl x))
                       (f x (refl x))                           ≡⟨ from∘to (f x (refl x)) ⟩∎
                 f x (refl x)                                   ∎)
                x≡y

private

  -- The following proof is perhaps easier to follow, but the
  -- resulting "from" functions are more complicated than the one used
  -- in ∀-intro. (If subst reduced in the usual way when applied to
  -- refl, then the two functions would perhaps be definitionally
  -- equal.)
  --
  -- This proof is based on one presented by Egbert Rijke in "A type
  -- theoretical Yoneda lemma"
  -- (http://homotopytypetheory.org/2012/05/02/a-type-theoretical-yoneda-lemma/).

  ∀-intro′ :
    ∀ {a b} {A : Type a} {x : A} (B : (y : A) → x ≡ y → Type b) →
    B x (refl x) ↝[ a ∣ a ⊔ b ] (∀ y (x≡y : x ≡ y) → B y x≡y)
  ∀-intro′ {a = a} {x = x} B {k = k} ext =
    B x (refl x)                        ↔⟨ inverse Π-left-identity ⟩
    (⊤ → B x (refl x))                  ↝⟨ Π-cong-contra (lower-extensionality? k lzero a ext)
                                                         (_⇔_.to contractible⇔↔⊤ c) (λ _ → id) ⟩
    ((∃ λ y → x ≡ y) → B x (refl x))    ↔⟨ currying ⟩
    (∀ y (x≡y : x ≡ y) → B x (refl x))  ↝⟨ (∀-cong ext λ y →
                                            ∀-cong (lower-extensionality? k lzero a ext) λ x≡y → from-isomorphism $
                                              Eq.subst-as-equivalence (uncurry B) (proj₂ c (y , x≡y))) ⟩□
    (∀ y (x≡y : x ≡ y) → B y x≡y)       □
    where
    c : Contractible (∃ λ y → x ≡ y)
    c = other-singleton-contractible x

-- One can introduce a (non-dependent) function argument of the same
-- type as another one if the codomain is propositional (assuming
-- extensionality).

→-intro :
  ∀ {a p} {A : Type a} {P : A → Type p} →
  Extensionality a (a ⊔ p) →
  (∀ x → Is-proposition (P x)) →
  (∀ x → P x) ↔ (A → ∀ x → P x)
→-intro {a = a} ext P-prop = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f _ x → f x
      ; from = λ f x → f x x
      }
    ; right-inverse-of = λ _ →
        (Π-closure ext                            1 λ _ →
         Π-closure (lower-extensionality a a ext) 1 λ _ →
         P-prop _) _ _
    }
  ; left-inverse-of = refl
  }

-- Logical equivalences can be expressed as pairs of functions.

⇔↔→×→ :
  ∀ {a b} {A : Type a} {B : Type b} →
  (A ⇔ B) ↔ (A → B) × (B → A)
⇔↔→×→ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → _⇔_.to f , _⇔_.from f
      ; from = λ { (to , from) → record { to = to; from = from } }
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

------------------------------------------------------------------------
-- Lemmas related to _⇔_

-- _⇔_ preserves logical equivalences.

⇔-cong-⇔ :
  ∀ {a b c d} {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
  A ⇔ B → C ⇔ D → (A ⇔ C) ⇔ (B ⇔ D)
⇔-cong-⇔ {A = A} {B = B} {C = C} {D = D} A⇔B C⇔D = record
  { to   = λ A⇔C →
             B  ↝⟨ inverse A⇔B ⟩
             A  ↝⟨ A⇔C ⟩
             C  ↝⟨ C⇔D ⟩□
             D  □
  ; from = λ B⇔D →
             A  ↝⟨ A⇔B ⟩
             B  ↝⟨ B⇔D ⟩
             D  ↝⟨ inverse C⇔D ⟩□
             C  □
  }

------------------------------------------------------------------------
-- Lemmas related to _↠_

-- An alternative characterisation of split surjections.

↠↔∃-Split-surjective :
  ∀ {a b} {A : Type a} {B : Type b} →
  (A ↠ B) ↔ ∃ λ (f : A → B) → Split-surjective f
↠↔∃-Split-surjective = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → _↠_.to f , _↠_.split-surjective f
      ; from = λ { (f , s) → record
          { logical-equivalence = record
            { to   = f
            ; from = proj₁ ⊚ s
            }
          ; right-inverse-of = proj₂ ⊚ s
          } }
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

------------------------------------------------------------------------
-- Lemmas related to _↣_

-- An alternative characterisation of injections.

↣↔∃-Injective :
  ∀ {a b} {A : Type a} {B : Type b} →
  (A ↣ B) ↔ ∃ λ (f : A → B) → Injective f
↣↔∃-Injective = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → _↣_.to f , _↣_.injective f
      ; from = λ (f , i) → record
          { to        = f
          ; injective = i
          }
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

------------------------------------------------------------------------
-- Lemmas related to _≡_

-- Equality is commutative.

open Bijection public using (≡-comm)

-- The following two lemmas are based on Example 2.4.8 in the HoTT
-- book.

-- The function trans x≡y is the to component of an isomorphism.

trans-isomorphism :
  ∀ {a} {A : Type a} {x y z : A} →
  x ≡ y → y ≡ z ↔ x ≡ z
trans-isomorphism x≡y = record
  { surjection = record
    { logical-equivalence = record
      { to   = trans x≡y
      ; from = trans (sym x≡y)
      }
    ; right-inverse-of = trans--[trans-sym] _
    }
  ; left-inverse-of = trans-sym-[trans] _
  }

-- The function flip trans x≡y is the to component of an isomorphism.

flip-trans-isomorphism :
  ∀ {a} {A : Type a} {x y z : A} →
  x ≡ y → z ≡ x ↔ z ≡ y
flip-trans-isomorphism x≡y = record
  { surjection = record
    { logical-equivalence = record
      { to   = flip trans x≡y
      ; from = flip trans (sym x≡y)
      }
    ; right-inverse-of = λ _ → trans-[trans-sym]- _ _
    }
  ; left-inverse-of = λ _ → trans-[trans]-sym _ _
  }

-- Equality expression rearrangement lemmas.

from≡↔≡to : ∀ {a b} →
            {A : Type a} {B : Type b}
            (A≃B : A ≃ B) {x : B} {y : A} →
            (_≃_.from A≃B x ≡ y) ↔ (x ≡ _≃_.to A≃B y)
from≡↔≡to A≃B {x} {y} =
  (_≃_.from A≃B x ≡ y)                          ↔⟨ inverse $ Eq.≃-≡ A≃B ⟩
  (_≃_.to A≃B (_≃_.from A≃B x) ≡ _≃_.to A≃B y)  ↝⟨ ≡⇒↝ _ $ cong (λ z → z ≡ _≃_.to A≃B y) $ _≃_.right-inverse-of A≃B x ⟩□
  (x ≡ _≃_.to A≃B y)                            □

to∘≡↔≡from∘ : ∀ {a b c} →
              Extensionality a (b ⊔ c) →
              {A : Type a} {B : A → Type b} {C : A → Type c}
              (B≃C : ∀ {x} → B x ≃ C x)
              {f : (x : A) → B x} {g : (x : A) → C x} →
              (_≃_.to B≃C ⊚ f ≡ g) ↔ (f ≡ _≃_.from B≃C ⊚ g)
to∘≡↔≡from∘ ext B≃C =
  from≡↔≡to (∀-cong ext (λ _ → inverse B≃C))

∘from≡↔≡∘to : ∀ {a b c} →
              Extensionality (a ⊔ b) c →
              {A : Type a} {B : Type b} {C : Type c}
              (A≃B : A ≃ B) {f : A → C} {g : B → C} →
              (f ∘ _≃_.from A≃B ≡ g) ↔ (f ≡ g ∘ _≃_.to A≃B)
∘from≡↔≡∘to ext A≃B = from≡↔≡to (→-cong₁ ext (inverse A≃B))

∘from≡↔≡∘to′ :
  ∀ {a b c} →
  Extensionality (a ⊔ b) c →
  {A : Type a} {B : Type b} {C : A → Type c}
  (A≃B : A ≃ B)
  {f : (x : A) → C x} {g : (x : B) → C (_≃_.from A≃B x)} →
  (f ⊚ _≃_.from A≃B ≡ g) ↔
  (f ≡ subst C (_≃_.left-inverse-of A≃B _) ⊚ g ⊚ _≃_.to A≃B)
∘from≡↔≡∘to′ {a = a} {b = b} ext {C = C} A≃B {f = f} {g = g} =
  f ⊚ _≃_.from A≃B ≡ g                                                  ↝⟨ ≡⇒↝ _ $ cong (_≡ g) $ apply-ext (lower-extensionality a lzero ext)
                                                                           lemma ⟩
  subst (C ⊚ _≃_.from A≃B) (_≃_.right-inverse-of A≃B _) ⊚
    _≃_.from (≡⇒↝ _ $ cong C (_≃_.left-inverse-of A≃B _)) ⊚
    f ⊚ _≃_.from A≃B ≡
  g                                                                     ↝⟨ from≡↔≡to
                                                                             (Π-cong-contra ext A≃B λ x →
                                                                                ≡⇒↝ _ $ cong C (_≃_.left-inverse-of A≃B x)) ⟩
  f ≡
  _≃_.to (≡⇒↝ _ $ cong C (_≃_.left-inverse-of A≃B _)) ⊚ g ⊚ _≃_.to A≃B  ↝⟨ (≡⇒↝ _ $ cong (f ≡_) $ apply-ext (lower-extensionality b lzero ext) λ _ →
                                                                            sym $ subst-in-terms-of-≡⇒↝ equivalence _ _ _) ⟩□
  f ≡ subst C (_≃_.left-inverse-of A≃B _) ⊚ g ⊚ _≃_.to A≃B              □
  where
  lemma : ∀ _ → _
  lemma x =
    f (_≃_.from A≃B x)                                          ≡⟨ sym $ _≃_.right-inverse-of equiv _ ⟩

    _≃_.to equiv (_≃_.from equiv (f (_≃_.from A≃B x)))          ≡⟨ sym $ subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩

    subst C (_≃_.left-inverse-of A≃B (_≃_.from A≃B x))
      (_≃_.from equiv (f (_≃_.from A≃B x)))                     ≡⟨ cong (λ eq → subst C eq (_≃_.from equiv (f (_≃_.from A≃B x)))) $ sym $
                                                                   _≃_.right-left-lemma A≃B _ ⟩
    subst C (cong (_≃_.from A≃B) (_≃_.right-inverse-of A≃B x))
      (_≃_.from equiv (f (_≃_.from A≃B x)))                     ≡⟨ sym $ subst-∘ _ _ (_≃_.right-inverse-of A≃B x) ⟩∎

    subst (C ⊚ _≃_.from A≃B) (_≃_.right-inverse-of A≃B x)
      (_≃_.from equiv (f (_≃_.from A≃B x)))                     ∎
    where
    equiv = ≡⇒↝ _ $ cong C (_≃_.left-inverse-of A≃B (_≃_.from A≃B x))

------------------------------------------------------------------------
-- Some lemmas related to _⁻¹_

-- A fibre of a composition can be expressed as a pair of fibres.

∘⁻¹≃ :
  ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} {z} →
  (f : B → C) (g : A → B) →
  f ∘ g ⁻¹ z ≃ ∃ λ ((y , _) : f ⁻¹ z) → g ⁻¹ y
∘⁻¹≃ {z = z} f g =
  f ∘ g ⁻¹ z                                  ↔⟨⟩
  (∃ λ a → f (g a) ≡ z)                       ↔⟨ (∃-cong λ _ → other-∃-intro _ _) ⟩
  (∃ λ a → ∃ λ y → f y ≡ z × g a ≡ y)         ↔⟨ (∃-cong λ _ → Σ-assoc) ⟩
  (∃ λ a → ∃ λ ((y , _) : f ⁻¹ z) → g a ≡ y)  ↔⟨ ∃-comm ⟩□
  (∃ λ ((y , _) : f ⁻¹ z) → g ⁻¹ y)           □

-- The type of fibres of Σ-map P.id f over a pair is equivalent to the
-- fibres of f over the pair's second component.
--
-- This is Theorem 4.7.6 from the HoTT book.

Σ-map-id-⁻¹≃⁻¹ :
  ∀ {a p q} {A : Type a} {P : A → Type p} {Q : A → Type q}
    {f : ∀ {x} → P x → Q x} {x : A} {y : Q x} →
  Σ-map P.id f ⁻¹ _,_ {B = Q} x y ≃ f ⁻¹ y
Σ-map-id-⁻¹≃⁻¹ {Q = Q} {f = f} {x = x} {y = y} =
  Σ-map P.id f ⁻¹ (x , y)                                        ↔⟨⟩
  (∃ λ (u , v) → (u , f v) ≡ (x , y))                            ↔⟨ inverse Bijection.Σ-assoc ⟩
  (∃ λ u → ∃ λ v → (u , f v) ≡ (x , y))                          ↔⟨ (∃-cong λ _ → ∃-cong λ _ → inverse
                                                                     Bijection.Σ-≡,≡↔≡) ⟩
  (∃ λ u → ∃ λ v → ∃ λ (p : u ≡ x) → subst Q p (f v) ≡ y)        ↔⟨ (∃-cong λ _ → ∃-comm) ⟩
  (∃ λ u → ∃ λ (p : u ≡ x) → ∃ λ v → subst Q p (f v) ≡ y)        ↔⟨ Bijection.Σ-assoc ⟩
  (∃ λ ((_ , p) : ∃ λ u → u ≡ x) → ∃ λ v → subst Q p (f v) ≡ y)  ↔⟨ drop-⊤-left-Σ $
                                                                    _⇔_.to contractible⇔↔⊤ $
                                                                    singleton-contractible _ ⟩
  (∃ λ v → subst Q (refl _) (f v) ≡ y)                           ↝⟨ (∃-cong λ _ → ≡⇒↝ _ $ cong (_≡ _) $
                                                                     subst-refl _ _) ⟩
  (∃ λ v → f v ≡ y)                                              ↔⟨⟩
  f ⁻¹ y                                                         □

------------------------------------------------------------------------
-- Lemmas related to ↑

-- ↑ _ preserves all kinds of functions.

private

  ↑-cong-→ :
    ∀ {a b c} {B : Type b} {C : Type c} →
    (B → C) → ↑ a B → ↑ a C
  ↑-cong-→ B→C = lift ⊚ B→C ⊚ lower

  ↑-cong-⇔ :
    ∀ {a b c} {B : Type b} {C : Type c} →
    B ⇔ C → ↑ a B ⇔ ↑ a C
  ↑-cong-⇔ B⇔C = record
    { to   = ↑-cong-→ to
    ; from = ↑-cong-→ from
    } where open _⇔_ B⇔C

  ↑-cong-↣ :
    ∀ {a b c} {B : Type b} {C : Type c} →
    B ↣ C → ↑ a B ↣ ↑ a C
  ↑-cong-↣ {a} B↣C = record
    { to        = to′
    ; injective = injective′
    }
    where
    open _↣_ B↣C

    to′ = ↑-cong-→ {a = a} to

    abstract
      injective′ : Injective to′
      injective′ = cong lift ⊚ injective ⊚ cong lower

  ↑-cong-Embedding :
    ∀ {a b c} {B : Type b} {C : Type c} →
    Embedding B C → Embedding (↑ a B) (↑ a C)
  ↑-cong-Embedding {a} {B = B} B↣C = record
    { to           = ↑-cong-→ to
    ; is-embedding = λ x y →
        _≃_.is-equivalence $
        Eq.with-other-function
          (x ≡ y                                      ↔⟨⟩
           lift (lower x) ≡ lift (lower y)            ↔⟨ inverse lift-lemma ⟩
           lower x ≡ lower y                          ↝⟨ Eq.⟨ _ , is-embedding _ _ ⟩ ⟩
           to (lower x) ≡ to (lower y)                ↔⟨ lift-lemma ⟩□
           lift (to (lower x)) ≡ lift (to (lower y))  □)
          _
          (λ p → cong lift (cong to (cong lower p))  ≡⟨ cong-∘ _ _ _ ⟩
                 cong (lift ⊚ to) (cong lower p)     ≡⟨ cong-∘ _ _ _ ⟩∎
                 cong (lift ⊚ to ⊚ lower) p          ∎)
    }
    where
    open Embedding B↣C

    lift-lemma : ∀ {ℓ a} {A : Type a} {x y : A} →
                 (x ≡ y) ↔ (lift {ℓ = ℓ} x ≡ lift y)
    lift-lemma {ℓ} = record
      { surjection = record
        { logical-equivalence = record
          { to   = cong lift
          ; from = cong lower
          }
        ; right-inverse-of = λ eq →
            cong lift (cong lower eq)  ≡⟨ cong-∘ _ _ _ ⟩
            cong (lift ⊚ lower) eq     ≡⟨ sym (cong-id _) ⟩∎
            eq                         ∎
        }
      ; left-inverse-of = λ eq →
          cong lower (cong lift eq)       ≡⟨ cong-∘ _ _ _ ⟩
          cong (lower {ℓ = ℓ} ⊚ lift) eq  ≡⟨ sym (cong-id _) ⟩∎
          eq                              ∎
      }

  ↑-cong-↠ :
    ∀ {a b c} {B : Type b} {C : Type c} →
    B ↠ C → ↑ a B ↠ ↑ a C
  ↑-cong-↠ {a} B↠C = record
    { logical-equivalence = logical-equivalence′
    ; right-inverse-of    = right-inverse-of′
    }
    where
    open _↠_ B↠C renaming (logical-equivalence to logical-equiv)

    logical-equivalence′ = ↑-cong-⇔ {a = a} logical-equiv

    abstract
      right-inverse-of′ : ∀ x →
                          _⇔_.to logical-equivalence′
                            (_⇔_.from logical-equivalence′ x) ≡
                          x
      right-inverse-of′ = cong lift ⊚ right-inverse-of ⊚ lower

  ↑-cong-↔ :
    ∀ {a b c} {B : Type b} {C : Type c} →
    B ↔ C → ↑ a B ↔ ↑ a C
  ↑-cong-↔ {a} B↔C = record
    { surjection      = surjection′
    ; left-inverse-of = left-inverse-of′
    }
    where
    open _↔_ B↔C renaming (surjection to surj)

    surjection′ = ↑-cong-↠ {a = a} surj

    abstract
      left-inverse-of′ :
        ∀ x → _↠_.from surjection′ (_↠_.to surjection′ x) ≡ x
      left-inverse-of′ = cong lift ⊚ left-inverse-of ⊚ lower

  ↑-cong-≃ :
    ∀ {a b c} {B : Type b} {C : Type c} →
    B ≃ C → ↑ a B ≃ ↑ a C
  ↑-cong-≃ = from-bijection ∘ ↑-cong-↔ ∘ from-equivalence

  ↑-cong-≃ᴱ :
    ∀ {a b c} {B : Type b} {C : Type c} →
    B ≃ᴱ C → ↑ a B ≃ᴱ ↑ a C
  ↑-cong-≃ᴱ f = EEq.[≃]→≃ᴱ (EEq.[proofs] (↑-cong-≃ (EEq.≃ᴱ→≃ f)))

↑-cong : ∀ {k a b c} {B : Type b} {C : Type c} →
           B ↝[ k ] C → ↑ a B ↝[ k ] ↑ a C
↑-cong {implication}         = ↑-cong-→
↑-cong {logical-equivalence} = ↑-cong-⇔
↑-cong {injection}           = ↑-cong-↣
↑-cong {embedding}           = ↑-cong-Embedding
↑-cong {surjection}          = ↑-cong-↠
↑-cong {bijection}           = ↑-cong-↔
↑-cong {equivalence}         = ↑-cong-≃
↑-cong {equivalenceᴱ}        = ↑-cong-≃ᴱ

------------------------------------------------------------------------
-- Lemmas related to unit types

-- The type of equalities tt ≡ tt is isomorphic to the unit type.

tt≡tt↔⊤ : tt ≡ tt ↔ ⊤
tt≡tt↔⊤ = _⇔_.to contractible⇔↔⊤ $
            propositional⇒inhabited⇒contractible
              (mono (zero≤ 2) ⊤-contractible) (refl _)

-- Unit is equivalent to ⊤.
--
-- The forward direction of the equivalence returns the supplied value
-- of type Unit.

Unit≃⊤ : Unit → Unit ≃ ⊤
Unit≃⊤ x =
  Eq.↔→≃ _ (λ _ → x) refl
    (λ { ⊠ → unblock x (_≡ ⊠) (refl _) })

------------------------------------------------------------------------
-- Lemmas related to ⊥

-- All instances of ⊥ are isomorphic.

⊥↔⊥ : ∀ {ℓ₁ ℓ₂} → ⊥ {ℓ = ℓ₁} ↔ ⊥ {ℓ = ℓ₂}
⊥↔⊥ = Bijection.⊥↔uninhabited ⊥-elim

-- All instances of A → ⊥ are isomorphic to ¬ A.

¬↔→⊥ : ∀ {a ℓ} {A : Type a} →
       ¬ A ↝[ a ∣ ℓ ] (A → ⊥ {ℓ = ℓ})
¬↔→⊥ {A = A} ext =
  (A → ⊥₀)  ↝⟨ (∀-cong ext λ _ → from-isomorphism ⊥↔⊥) ⟩□
  (A → ⊥)   □

-- A type cannot be logically equivalent to its own negation.

¬[⇔¬] : ∀ {a} {A : Type a} → ¬ (A ⇔ ¬ A)
¬[⇔¬] {A = A} =
  A ⇔ ¬ A          ↝⟨ (λ eq → (λ a → _⇔_.to eq a a) , eq) ⟩
  ¬ A × (A ⇔ ¬ A)  ↝⟨ (λ { (¬a , eq) → ¬a , _⇔_.from eq ¬a }) ⟩
  ¬ A × A          ↝⟨ uncurry _$_ ⟩□
  ⊥                □

-- If two types are logically equivalent, then their negations are
-- equivalent (assuming extensionality).

¬-cong-⇔ :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) lzero →
  A ⇔ B → (¬ A) ≃ (¬ B)
¬-cong-⇔ {a} {b} ext A⇔B =
  _↠_.from
    (Eq.≃↠⇔ (¬-propositional (lower-extensionality b lzero ext))
            (¬-propositional (lower-extensionality a lzero ext)))
    (→-cong _ A⇔B id)

-- Symmetric kinds of functions are preserved by ¬_ (assuming
-- extensionality).

¬-cong :
  ∀ {k a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) lzero →
  A ↝[ ⌊ k ⌋-sym ] B → (¬ A) ↝[ ⌊ k ⌋-sym ] (¬ B)
¬-cong ext A↝B = from-equivalence (¬-cong-⇔ ext (sym→⇔ A↝B))

-- If B can be decided, given that A is inhabited, then A → B is
-- logically equivalent to ¬ B → ¬ A.

→⇔¬→¬ :
  ∀ {a b} {A : Type a} {B : Type b} →
  (A → Dec B) →
  (A → B) ⇔ (¬ B → ¬ A)
→⇔¬→¬ _   ._⇔_.to           = flip _∘_
→⇔¬→¬ dec ._⇔_.from ¬B→¬A A with dec A
… | yes B = B
… | no ¬B = ⊥-elim $ ¬B→¬A ¬B A

-- If B is additionally a proposition (assuming that A is inhabited),
-- then the two types are equivalent (assuming extensionality).

→≃¬→¬ :
  ∀ {a b} {A : Type a} {B : Type b} →
  (Extensionality (a ⊔ b) (a ⊔ b) → A → Is-proposition B) →
  (A → Dec B) →
  (A → B) ↝[ a ⊔ b ∣ a ⊔ b ] (¬ B → ¬ A)
→≃¬→¬ {a = a} {b = b} prop dec =
  generalise-ext?-prop
    (→⇔¬→¬ dec)
    (λ ext → Π-closure (lower-extensionality b a ext) 1 (prop ext))
    (λ ext → Π-closure (lower-extensionality a b ext) 1 λ _ →
             ¬-propositional (lower-extensionality b _ ext))

------------------------------------------------------------------------
-- Lemmas related to H-level

-- H-level and H-level′ are pointwise isomorphic (assuming
-- extensionality).

H-level↔H-level′ :
  ∀ {a} {A : Type a} {n} →
  H-level n A ↝[ a ∣ a ] H-level′ n A
H-level↔H-level′ {n = n} =
  generalise-ext?-prop
    H-level⇔H-level′
    (λ ext → H-level-propositional  ext _)
    (λ ext → H-level′-propositional ext n)

-- H-level n preserves isomorphisms (assuming extensionality).

H-level-cong :
  ∀ {k₁ k₂ a b} {A : Type a} {B : Type b} →
  Extensionality? k₂ (a ⊔ b) (a ⊔ b) →
  ∀ n → A ↔[ k₁ ] B → H-level n A ↝[ k₂ ] H-level n B
H-level-cong {a = a} {b} ext n A↔B′ =
  generalise-ext?-prop
    (record
       { to   = respects-surjection (_↔_.surjection          A↔B)  n
       ; from = respects-surjection (_↔_.surjection (inverse A↔B)) n
       })
    (λ ext → H-level-propositional (lower-extensionality b b ext) n)
    (λ ext → H-level-propositional (lower-extensionality a a ext) n)
    ext
  where
  A↔B = from-isomorphism A↔B′

-- H-level′ n preserves isomorphisms (assuming extensionality).

H-level′-cong :
  ∀ {k₁ k₂ a b} {A : Type a} {B : Type b} →
  Extensionality? k₂ (a ⊔ b) (a ⊔ b) →
  ∀ n → A ↔[ k₁ ] B → H-level′ n A ↝[ k₂ ] H-level′ n B
H-level′-cong {k₂ = k₂} {a = a} {b = b} {A = A} {B = B} ext n A↔B =
  H-level′ n A  ↝⟨ inverse-ext? H-level↔H-level′ (lower-extensionality? k₂ b b ext) ⟩
  H-level n A   ↝⟨ H-level-cong ext n A↔B ⟩
  H-level n B   ↝⟨ H-level↔H-level′ (lower-extensionality? k₂ a a ext) ⟩□
  H-level′ n B  □

-- There is an isomorphism between (x y : A) → H-level n (x ≡ y) and
-- H-level (suc n) A (assuming extensionality).

≡↔+ :
  ∀ {a} {A : Type a} n →
  ((x y : A) → H-level n (x ≡ y)) ↝[ a ∣ a ] H-level (suc n) A
≡↔+ {A = A} n ext =
  ((x y : A) → H-level  n (x ≡ y))  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → H-level↔H-level′ ext) ⟩
  ((x y : A) → H-level′ n (x ≡ y))  ↔⟨⟩
  H-level′ (suc n) A                ↝⟨ inverse-ext? H-level↔H-level′ ext ⟩□
  H-level  (suc n) A                □

-- Some lemmas relating equivalences A ≃ B with types of the form
-- ∀ C → H-level n C → (A → C) ≃ (B → C).

→≃→↠≃ :
  ∀ n {ℓ} {A B : Type ℓ} →
  Extensionality ℓ ℓ →
  (hA : H-level n A) (hB : H-level n B) →
  (∃ λ (f : (C : Type ℓ) → H-level n C → (A → C) ≃ (B → C)) →
     ((C : Type ℓ) (hC : H-level n C) (g : A → C) →
        g ∘ _≃_.to (f A hA) id ≡ _≃_.to (f C hC) g) ×
     ((C : Type ℓ) (hC : H-level n C) (g : B → C) →
        g ∘ _≃_.from (f B hB) id ≡ _≃_.from (f C hC) g))
    ↠
  (A ≃ B)
→≃→↠≃ _ {A = A} {B} ext hA hB = record
  { logical-equivalence = record
    { from = λ A≃B → (λ _ _ → →-cong₁ ext A≃B)
                   , (λ _ _ g → refl (g ∘ _≃_.from A≃B))
                   , (λ _ _ g → refl (g ∘ _≃_.to   A≃B))
    ; to   = λ { (A→≃B→ , ∘to≡ , ∘from≡) → Eq.↔⇒≃ (record
      { surjection = record
        { logical-equivalence = record
          { to   = _≃_.from (A→≃B→ B hB) id
          ; from = _≃_.to   (A→≃B→ A hA) id
          }
        ; right-inverse-of = λ x →
            _≃_.from (A→≃B→ B hB) id (_≃_.to (A→≃B→ A hA) id x)    ≡⟨⟩
            (_≃_.from (A→≃B→ B hB) id ∘ _≃_.to (A→≃B→ A hA) id) x  ≡⟨ cong (_$ x) $ ∘to≡ _ _ _ ⟩
            (_≃_.to (A→≃B→ B hB) (_≃_.from (A→≃B→ B hB) id)) x     ≡⟨ cong (_$ x) $ _≃_.right-inverse-of (A→≃B→ B hB) _ ⟩∎
            x                                                      ∎
        }
      ; left-inverse-of = λ x →
          _≃_.to (A→≃B→ A hA) id (_≃_.from (A→≃B→ B hB) id x)    ≡⟨⟩
          (_≃_.to (A→≃B→ A hA) id ∘ _≃_.from (A→≃B→ B hB) id) x  ≡⟨ cong (_$ x) $ ∘from≡ _ _ _ ⟩
          (_≃_.from (A→≃B→ A hA) (_≃_.to (A→≃B→ A hA) id)) x     ≡⟨ cong (_$ x) $ _≃_.left-inverse-of (A→≃B→ A hA) _ ⟩∎
          x                                                      ∎
      }) }
    }
  ; right-inverse-of = λ A≃B → _↔_.to (≃-to-≡↔≡ ext) λ x →
      refl (_≃_.to A≃B x)
  }

-- The following property can be generalised.

→≃→↔≃ :
  ∀ {ℓ} {A B : Type ℓ} →
  Extensionality (lsuc ℓ) ℓ →
  (hA : Is-set A) (hB : Is-set B) →
  (∃ λ (f : (C : Type ℓ) → Is-set C → (A → C) ≃ (B → C)) →
     ((C : Type ℓ) (hC : Is-set C) (g : A → C) →
        g ∘ _≃_.to (f A hA) id ≡ _≃_.to (f C hC) g) ×
     ((C : Type ℓ) (hC : Is-set C) (g : B → C) →
        g ∘ _≃_.from (f B hB) id ≡ _≃_.from (f C hC) g))
    ↔
  (A ≃ B)
→≃→↔≃ {A = A} {B} ext hA hB = record
  { surjection      = →≃→↠≃ 2 ext′ hA hB
  ; left-inverse-of = λ { (A→≃B→ , ∘to≡ , _) →
      Σ-≡,≡→≡
        (apply-ext ext  λ C  →
         apply-ext ext′ λ hC →
         _↔_.to (≃-to-≡↔≡ ext′) λ f →
           f ∘ _≃_.to (A→≃B→ A hA) id   ≡⟨ ∘to≡ _ _ _ ⟩∎
           _≃_.to (A→≃B→ C (hC {_})) f  ∎)
        ((×-closure 1
            (Π-closure ext  1 λ _  →
             Π-closure ext′ 1 λ hC →
             Π-closure ext′ 1 λ _ →
             Π-closure ext′ 2 λ _ → hC {_})
            (Π-closure ext  1 λ _  →
             Π-closure ext′ 1 λ hC →
             Π-closure ext′ 1 λ _ →
             Π-closure ext′ 2 λ _ → hC {_})) _ _) }
  }
  where
  ext′ = lower-extensionality _ lzero ext

------------------------------------------------------------------------
-- Lemmas related to Dec

-- A preservation lemma for Dec.

Dec-cong :
  ∀ {k a b} {A : Type a} {B : Type b} →
  Extensionality? ⌊ k ⌋-sym (a ⊔ b) lzero →
  A ↝[ ⌊ k ⌋-sym ] B →
  Dec A ↝[ ⌊ k ⌋-sym ] Dec B
Dec-cong {A = A} {B = B} ext A↝B =
  A ⊎ ¬ A  ↝⟨ A↝B ⊎-cong →-cong ext A↝B id ⟩□
  B ⊎ ¬ B  □

-- A preservation lemma for Decidable.

Decidable-cong :
  ∀ {k₁ k₂ k₃ a₁ b₁ p₁ a₂ b₂ p₂}
    {A₁ : Type a₁} {B₁ : Type b₁} {P₁ : A₁ → B₁ → Type p₁}
    {A₂ : Type a₂} {B₂ : Type b₂} {P₂ : A₂ → B₂ → Type p₂} →
  Extensionality? ⌊ k₃ ⌋-sym (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ p₁ ⊔ p₂)
                             (b₁ ⊔ b₂ ⊔ p₁ ⊔ p₂) →
  (A₁↔A₂ : A₁ ↔[ k₁ ] A₂)
  (B₁↔B₂ : B₁ ↔[ k₂ ] B₂) →
  (∀ x y →
     P₁ x y
       ↝[ ⌊ k₃ ⌋-sym ]
     P₂ (to-implication A₁↔A₂ x) (to-implication B₁↔B₂ y)) →
  Decidable P₁ ↝[ ⌊ k₃ ⌋-sym ] Decidable P₂
Decidable-cong
  {k₃ = k₃} {a₁} {b₁} {p₁} {a₂} {b₂} {p₂} {P₁ = P₁} {P₂ = P₂}
  ext A₁↔A₂ B₁↔B₂ P₁↝P₂ =

  (∀ x y → Dec (P₁ x y))  ↝⟨ (Π-cong   (lower-extensionality? ⌊ k₃ ⌋-sym (b₁ ⊔ b₂ ⊔ p₁ ⊔ p₂) lzero     ext) A₁↔A₂ λ x →
                              Π-cong   (lower-extensionality? ⌊ k₃ ⌋-sym (a₁ ⊔ a₂ ⊔ p₁ ⊔ p₂) (b₁ ⊔ b₂) ext) B₁↔B₂ λ y →
                              Dec-cong (lower-extensionality? ⌊ k₃ ⌋-sym (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂) _         ext) (P₁↝P₂ x y)) ⟩□
  (∀ x y → Dec (P₂ x y))  □

-- A preservation lemma for Decidable-equality.

Decidable-equality-cong :
  ∀ {k₁ k₂ a b} {A : Type a} {B : Type b} →
  Extensionality? k₂ (a ⊔ b) (a ⊔ b) →
  A ↔[ k₁ ] B →
  Decidable-equality A ↝[ k₂ ] Decidable-equality B
Decidable-equality-cong ext A↔B =
  generalise-ext?
    (Decidable-cong _ A≃B A≃B lemma)
    (λ ext → Decidable-cong ext A≃B A≃B lemma)
    ext
  where
  A≃B = from-isomorphism A↔B

  lemma : ∀ {k} _ _ → _ ↝[ k ] _
  lemma x y =
    x ≡ y                        ↔⟨ inverse $ Eq.≃-≡ A≃B ⟩□
    _≃_.to A≃B x ≡ _≃_.to A≃B y  □

------------------------------------------------------------------------
-- Lemmas related to if

-- A generalisation of if-encoding (which is defined below).

if-lemma : ∀ {a b p} {A : Type a} {B : Type b} (P : Bool → Type p) →
           A ↔ P true → B ↔ P false →
           ∀ b → T b × A ⊎ T (not b) × B ↔ P b
if-lemma {A = A} {B} P A↔ B↔ true =
  ⊤ × A ⊎ ⊥ × B  ↔⟨ ×-left-identity ⊎-cong ×-left-zero ⟩
  A ⊎ ⊥₀         ↔⟨ ⊎-right-identity ⟩
  A              ↔⟨ A↔ ⟩
  P true         □
if-lemma {A = A} {B} P A↔ B↔ false =
  ⊥ × A ⊎ ⊤ × B  ↔⟨ ×-left-zero ⊎-cong ×-left-identity ⟩
  ⊥₀ ⊎ B         ↔⟨ ⊎-left-identity ⟩
  B              ↔⟨ B↔ ⟩
  P false        □

-- An encoding of if_then_else_ in terms of _⊎_, _×_, T and not.

if-encoding : ∀ {ℓ} {A B : Type ℓ} →
              ∀ b → (if b then A else B) ↔ T b × A ⊎ T (not b) × B
if-encoding {A = A} {B} =
  inverse ⊚ if-lemma (λ b → if b then A else B) id id

------------------------------------------------------------------------
-- Properties related to ℕ

-- The natural numbers are isomorphic to the natural numbers extended
-- with another element.

ℕ↔ℕ⊎⊤ : ℕ ↔ ℕ ⊎ ⊤
ℕ↔ℕ⊎⊤ = record
  { surjection = record
    { logical-equivalence = record
      { to   = ℕ-rec (inj₂ tt) (λ n _ → inj₁ n)
      ; from = [ suc , const zero ]
      }
    ; right-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
    }
  ; left-inverse-of = ℕ-rec (refl 0) (λ n _ → refl (suc n))
  }

private

  -- Two consequences of ℕ↔ℕ⊎⊤.

  Σℕ≃′ :
    ∀ {p} {P : ℕ → Type p} →
    (∃ λ n → P n) ≃ (P zero ⊎ ∃ λ n → P (suc n))
  Σℕ≃′ {P = P} =
    (∃ λ n → P n)                             ↝⟨ (Σ-cong-contra (inverse ℕ↔ℕ⊎⊤) λ _ → id) ⟩
    (∃ λ (x : ℕ ⊎ ⊤) → P (_↔_.from ℕ↔ℕ⊎⊤ x))  ↔⟨ ∃-⊎-distrib-right ⟩
    (∃ λ (n : ℕ) → P (suc n)) ⊎ ⊤ × P zero    ↔⟨ ⊎-comm ⟩
    ⊤ × P zero ⊎ (∃ λ (n : ℕ) → P (suc n))    ↔⟨ ×-left-identity ⊎-cong id ⟩□
    P zero ⊎ (∃ λ (n : ℕ) → P (suc n))        □

  Πℕ≃′ :
    ∀ {p} {P : ℕ → Type p} →
    (∀ n → P n) ↝[ lzero ∣ p ] (P zero × ∀ n → P (suc n))
  Πℕ≃′ {P = P} ext =
    (∀ n → P n)                           ↝⟨ (Π-cong-contra ext (inverse ℕ↔ℕ⊎⊤) λ _ → id) ⟩
    ((x : ℕ ⊎ ⊤) → P (_↔_.from ℕ↔ℕ⊎⊤ x))  ↝⟨ Π⊎↔Π×Π ext ⟩
    ((n : ℕ) → P (suc n)) × (⊤ → P zero)  ↔⟨ ×-comm ⟩
    (⊤ → P zero) × ((n : ℕ) → P (suc n))  ↔⟨ Π-left-identity ×-cong id ⟩□
    P zero × ((n : ℕ) → P (suc n))        □

-- Variants of Σℕ≃′ and Πℕ≃′ which, at the time of writing, have
-- "better" computational behaviour.

Σℕ≃ :
  ∀ {p} {P : ℕ → Type p} →
  (∃ λ n → P n) ≃ (P zero ⊎ ∃ λ n → P (suc n))
Σℕ≃ {P = P} = Eq.↔→≃
  (λ where
      (zero  , p) → inj₁ p
      (suc n , p) → inj₂ (n , p))
  [ (zero ,_) , Σ-map suc id ]
  [ (λ _ → refl _) , (λ _ → refl _) ]
  (λ where
      (zero  , _) → refl _
      (suc _ , _) → refl _)

Πℕ≃ :
  ∀ {p} {P : ℕ → Type p} →
  (∀ n → P n) ↝[ lzero ∣ p ] (P zero × ∀ n → P (suc n))
Πℕ≃ {P = P} =
  generalise-ext?
    Πℕ⇔
    (λ ext → record
       { surjection = record
         { logical-equivalence = Πℕ⇔
         ; right-inverse-of    = refl
         }
       ; left-inverse-of = λ _ →
           apply-ext ext $
           ℕ-case (refl _) (λ _ → refl _)
       })
  where
  Πℕ⇔ : _ ⇔ _
  Πℕ⇔ ._⇔_.to f = f zero , f ⊚ suc
  Πℕ⇔ ._⇔_.from = uncurry ℕ-case

-- ℕ is isomorphic to ℕ ⊎ ℕ.

ℕ↔ℕ⊎ℕ : ℕ ↔ ℕ ⊎ ℕ
ℕ↔ℕ⊎ℕ = record
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
  step : ℕ ⊎ ℕ → ℕ ⊎ ℕ
  step = [ inj₂ , inj₁ ∘ suc ]

  to : ℕ → ℕ ⊎ ℕ
  to zero    = inj₁ zero
  to (suc n) = step (to n)

  double : ℕ → ℕ
  double zero    = zero
  double (suc n) = suc (suc (double n))

  from : ℕ ⊎ ℕ → ℕ
  from = [ double , suc ∘ double ]

  from∘to : ∀ n → from (to n) ≡ n
  from∘to zero    = zero ∎
  from∘to (suc n) with to n | from∘to n
  ... | inj₁ m | eq =
    suc (double m)  ≡⟨ cong suc eq ⟩∎
    suc n          ∎
  ... | inj₂ m | eq =
    suc (suc (double m))  ≡⟨ cong suc eq ⟩∎
    suc n                ∎

  to∘double : ∀ n → to (double n) ≡ inj₁ n
  to∘double zero    = inj₁ zero ∎
  to∘double (suc n) =
    to (double (suc n))          ≡⟨⟩
    to (suc (suc (double n)))    ≡⟨⟩
    step (step (to (double n)))  ≡⟨ cong (step ∘ step) (to∘double n) ⟩
    step (step (inj₁ n))         ≡⟨⟩
    inj₁ (suc n)                 ∎

  to∘from : ∀ x → to (from x) ≡ x
  to∘from =
    [ to∘double
    , (λ n →
         to (from (inj₂ n))    ≡⟨⟩
         to (suc (double n))   ≡⟨⟩
         step (to (double n))  ≡⟨ cong step (to∘double n) ⟩
         step (inj₁ n)         ≡⟨⟩
         inj₂ n                ∎)
    ]

-- ℕ is isomorphic to ℕ².

ℕ↔ℕ² : ℕ ↔ ℕ × ℕ
ℕ↔ℕ² = record
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
  step : ℕ × ℕ → ℕ × ℕ
  step (m , zero)  = (zero , suc m)
  step (m , suc n) = (suc m , n)

  to : ℕ → ℕ × ℕ
  to zero    = (zero , zero)
  to (suc n) = step (to n)

  -- The function from′ is defined by lexicographic induction on first
  -- sum, and then m.

  from′ : (m n sum : ℕ) → n + m ≡ sum → ℕ
  from′ zero    zero    _ _          = zero
  from′ zero    (suc n) zero      eq = ⊥-elim (0≢+ (sym eq))
  from′ zero    (suc n) (suc sum) eq = suc (from′ n zero sum (cancel-suc
                                              (suc n        ≡⟨ cong suc (sym +-right-identity) ⟩
                                               suc (n + 0)  ≡⟨ eq ⟩∎
                                               suc sum      ∎)))
  from′ (suc m) n       sum       eq = suc (from′ m (suc n) sum
                                              (suc n + m  ≡⟨ suc+≡+suc n ⟩
                                               n + suc m  ≡⟨ eq ⟩∎
                                               sum        ∎))

  from : ℕ × ℕ → ℕ
  from (m , n) = from′ m n _ (refl _)

  from′-irr : ∀ m {n sum₁ eq₁ sum₂ eq₂} →
              from′ m n sum₁ eq₁ ≡ from′ m n sum₂ eq₂
  from′-irr m {n} {sum₁} {eq₁} {sum₂} {eq₂} =
    from′ m n sum₁ eq₁  ≡⟨ cong (uncurry (from′ m n)) (Σ-≡,≡→≡ lemma (ℕ-set _ _)) ⟩∎
    from′ m n sum₂ eq₂  ∎
    where
    lemma =
      sum₁   ≡⟨ sym eq₁ ⟩
      n + m  ≡⟨ eq₂ ⟩∎
      sum₂   ∎

  from∘step : ∀ p → from (step p) ≡ suc (from p)
  from∘step (m , zero)  = from (zero , suc m)    ≡⟨ cong suc (from′-irr m) ⟩∎
                          suc (from (m , zero))  ∎
  from∘step (m , suc n) = from (suc m , n)        ≡⟨ cong suc (from′-irr m) ⟩∎
                          suc (from (m , suc n))  ∎

  from∘to : ∀ n → from (to n) ≡ n
  from∘to zero    = refl _
  from∘to (suc n) =
    from (to (suc n))   ≡⟨⟩
    from (step (to n))  ≡⟨ from∘step (to n) ⟩
    suc (from (to n))   ≡⟨ cong suc (from∘to n) ⟩∎
    suc n               ∎

  to∘from′ : ∀ m n sum eq → to (from′ m n sum eq) ≡ (m , n)
  to∘from′ zero zero    _ _          = refl _
  to∘from′ zero (suc n) zero      eq = ⊥-elim (0≢+ (sym eq))
  to∘from′ zero (suc n) (suc sum) eq =
    step (to (from′ n zero _ _))  ≡⟨ cong step (to∘from′ n zero sum _) ⟩
    step (n , zero)               ≡⟨⟩
    (zero , suc n)                ∎

  to∘from′ (suc m) n sum eq =
    step (to (from′ m (suc n) _ _))  ≡⟨ cong step (to∘from′ m (suc n) sum _) ⟩
    step (m , suc n)                 ≡⟨⟩
    (suc m , n)                      ∎

  to∘from : ∀ p → to (from p) ≡ p
  to∘from _ = to∘from′ _ _ _ _

-- Some isomorphisms related to equality of natural numbers.

zero≡zero↔ : zero ≡ zero ↔ ⊤
zero≡zero↔ =
  _≃_.bijection $
  _↠_.from (Eq.≃↠⇔ ℕ-set (mono₁ 0 ⊤-contractible)) $
  record { to = _; from = λ _ → refl _ }

zero≡suc↔ : ∀ {n} → zero ≡ suc n ↔ ⊥₀
zero≡suc↔ =
  _≃_.bijection $
  _↠_.from (Eq.≃↠⇔ ℕ-set ⊥-propositional) $
  record { to = 0≢+; from = ⊥-elim }

suc≡zero↔ : ∀ {m} → suc m ≡ zero ↔ ⊥₀
suc≡zero↔ {m} =
  suc m ≡ zero  ↝⟨ ≡-comm ⟩
  zero ≡ suc m  ↝⟨ zero≡suc↔ ⟩□
  ⊥             □

suc≡suc↔ : ∀ {m n} → suc m ≡ suc n ↔ m ≡ n
suc≡suc↔ =
  _≃_.bijection $
  _↠_.from (Eq.≃↠⇔ ℕ-set ℕ-set) $
  record { to = cancel-suc; from = cong suc }

-- The equality test Nat._==_ gives the right result.

T[==]↔≡ : {m n : ℕ} → T (m == n) ↔ m ≡ n
T[==]↔≡ {m = zero} {n = zero} =
  T (zero == zero)  ↔⟨⟩
  ⊤                 ↝⟨ inverse zero≡zero↔ ⟩□
  zero ≡ zero       □

T[==]↔≡ {m = zero} {n = suc n} =
  T (zero == suc n)  ↔⟨⟩
  ⊥                  ↝⟨ inverse zero≡suc↔ ⟩□
  zero ≡ suc n       □

T[==]↔≡ {m = suc m} {n = zero} =
  T (suc m == zero)  ↔⟨⟩
  ⊥                  ↝⟨ inverse suc≡zero↔ ⟩□
  suc m ≡ zero       □

T[==]↔≡ {m = suc m} {n = suc n} =
  T (suc m == suc n)  ↔⟨⟩
  T (m == n)          ↝⟨ T[==]↔≡ ⟩
  m ≡ n               ↝⟨ inverse suc≡suc↔ ⟩□
  suc m ≡ suc n       □

-- Some isomorphisms related to the ordering of natural numbers.

zero≤↔ : ∀ {n} → zero ≤ n ↔ ⊤
zero≤↔ =
  _≃_.bijection $
  _↠_.from (Eq.≃↠⇔ ≤-propositional (mono₁ 0 ⊤-contractible)) $
  record { to = _; from = λ _ → zero≤ _ }

<zero↔ : ∀ {n} → n < zero ↔ ⊥
<zero↔ =
  _≃_.bijection $
  _↠_.from (Eq.≃↠⇔ ≤-propositional ⊥-propositional) $
  record { to = ≮0 _; from = ⊥-elim }

suc≤suc↔ : ∀ {m n} → suc m ≤ suc n ↔ m ≤ n
suc≤suc↔ =
  _≃_.bijection $
  _↠_.from (Eq.≃↠⇔ ≤-propositional ≤-propositional) $
  record { to = suc≤suc⁻¹; from = suc≤suc }

≤↔<⊎≡ : ∀ {m n} → m ≤ n ↔ m < n ⊎ m ≡ n
≤↔<⊎≡ =
  _≃_.bijection $
  _↠_.from (Eq.≃↠⇔ ≤-propositional
                   (⊎-closure-propositional
                      <→≢ ≤-propositional ℕ-set)) $
  record { to = ≤→<⊎≡; from = [ <→≤ , ≤-refl′ ] }

≤↔≡0⊎0<×≤ : ∀ {m n} → m ≤ n ↔ m ≡ 0 ⊎ 0 < m × m ≤ n
≤↔≡0⊎0<×≤ {zero} {n} =
  0 ≤ n                  ↝⟨ zero≤↔ ⟩
  ⊤                      ↝⟨ inverse ⊎-right-identity ⟩
  ⊤ ⊎ ⊥₀                 ↝⟨ id ⊎-cong inverse ×-left-zero ⟩
  ⊤ ⊎ (⊥ × 0 ≤ n)        ↝⟨ inverse (_⇔_.to contractible⇔↔⊤ (propositional⇒inhabited⇒contractible ℕ-set (refl _)))
                              ⊎-cong
                            inverse <zero↔ ×-cong id ⟩□
  0 ≡ 0 ⊎ 0 < 0 × 0 ≤ n  □

≤↔≡0⊎0<×≤ {suc m} {n} =
  m < n                          ↝⟨ inverse ×-left-identity ⟩
  ⊤ × m < n                      ↝⟨ inverse zero≤↔ ×-cong id ⟩
  0 ≤ m × m < n                  ↝⟨ inverse ⊎-left-identity ⟩
  ⊥₀ ⊎ 0 ≤ m × m < n             ↝⟨ Bijection.⊥↔uninhabited (0≢+ ∘ sym) ⊎-cong inverse suc≤suc↔ ×-cong id ⟩□
  1 + m ≡ 0 ⊎ 0 < 1 + m × m < n  □

≤↔min≡ : ∀ {m n} → m ≤ n ↔ min m n ≡ m
≤↔min≡ =
  _≃_.bijection $
  _↠_.from (Eq.≃↠⇔ ≤-propositional ℕ-set) $
  ≤⇔min≡

≤↔max≡ : ∀ {m n} → m ≤ n ↔ max m n ≡ n
≤↔max≡ =
  _≃_.bijection $
  _↠_.from (Eq.≃↠⇔ ≤-propositional ℕ-set) $
  ≤⇔max≡

∃0<↔∃suc :
  ∀ {p} {P : ℕ → Type p} →
  (∃ λ n → 0 < n × P n) ↔ (∃ λ n → P (suc n))
∃0<↔∃suc {P = P} = record
  { surjection = record
    { logical-equivalence = record
      { to   = Σ-map pred λ where
                 {zero}  (0<0 , _) → ⊥-elim (≮0 _ 0<0)
                 {suc _} (_   , p) → p
      ; from = Σ-map suc (λ p → suc≤suc (zero≤ _) , p)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = λ where
      (zero  , 0<0 , p) → ⊥-elim (≮0 _ 0<0)
      (suc n , 0<+ , p) →
        Σ-≡,≡→≡ (refl _)
          (trans (subst-refl _ _)
             (_↔_.to ≡×≡↔≡
                ( ≤-propositional _ _
                , refl _
                )))
  }

∃<↔∃0<×≤ : ∀ {n} → (∃ λ m → m < n) ↔ (∃ λ m → 0 < m × m ≤ n)
∃<↔∃0<×≤ {n} =
  (∃ λ m → m < n)          ↔⟨⟩
  (∃ λ m → suc m ≤ n)      ↝⟨ inverse ∃0<↔∃suc ⟩□
  (∃ λ m → 0 < m × m ≤ n)  □

-- The ordering test Nat._<=_ gives the right result.

T[<=]↔≤ : {m n : ℕ} → T (m <= n) ↔ m ≤ n
T[<=]↔≤ {m = zero} {n = n} =
  T (zero <= n)  ↔⟨⟩
  ⊤              ↝⟨ inverse zero≤↔ ⟩□
  zero ≤ n       □

T[<=]↔≤ {m = suc m} {n = zero} =
  T (suc m <= zero)  ↔⟨⟩
  ⊥                  ↝⟨ inverse <zero↔ ⟩□
  suc m ≤ zero       □

T[<=]↔≤ {m = suc m} {n = suc n} =
  T (suc m <= suc n)  ↔⟨⟩
  T (m <= n)          ↝⟨ T[<=]↔≤ ⟩
  m ≤ n               ↝⟨ inverse suc≤suc↔ ⟩□
  suc m ≤ suc n       □

-- Equality or distinctness of two natural numbers is isomorphic to
-- the unit type.

≡⊎Distinct↔⊤ : ∀ m n → m ≡ n ⊎ Distinct m n ↔ ⊤
≡⊎Distinct↔⊤ m n =
  _⇔_.to contractible⇔↔⊤ $
  propositional⇒inhabited⇒contractible
    (⊎-closure-propositional
       (λ m≡n m≢n → _⇔_.to Distinct⇔≢ m≢n m≡n)
       ℕ-set
       (Distinct-propositional m n))
    (≡⊎Distinct m n)

-- Distinct is pointwise logically equivalent to _≢_, and in the
-- presence of extensionality the two definitions are pointwise
-- isomorphic.

Distinct↔≢ : ∀ {m n} → Distinct m n ↝[ lzero ∣ lzero ] m ≢ n
Distinct↔≢ {m = m} {n} =
  generalise-ext? Distinct⇔≢ λ ext →
    from-isomorphism $
    _↔_.to (Eq.⇔↔≃ ext (Distinct-propositional m n)
                       (¬-propositional ext))
           Distinct⇔≢

------------------------------------------------------------------------
-- Left cancellation for _⊎_

-- In general _⊎_ is not left cancellative.

¬-⊎-left-cancellative :
  ∀ k → ¬ ((A B C : Type) → A ⊎ B ↝[ k ] A ⊎ C → B ↝[ k ] C)
¬-⊎-left-cancellative k cancel =
  ¬B→C $ to-implication $ cancel A B C (from-bijection A⊎B↔A⊎C)
  where
  A = ℕ
  B = ⊤
  C = ⊥

  A⊎B↔A⊎C : A ⊎ B ↔ A ⊎ C
  A⊎B↔A⊎C =
    ℕ ⊎ ⊤  ↔⟨ inverse ℕ↔ℕ⊎⊤ ⟩
    ℕ      ↔⟨ inverse ⊎-right-identity ⟩
    ℕ ⊎ ⊥  □

  ¬B→C : ¬ (B → C)
  ¬B→C B→C = B→C tt

-- However, it is left cancellative for certain well-behaved
-- bijections.

-- A function is "well-behaved" if any "left" element which is the
-- image of a "right" element is in turn not mapped to another "left"
-- element.

Well-behaved : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
               (A ⊎ B → A ⊎ C) → Type _
Well-behaved f =
  ∀ {b a a′} → f (inj₂ b) ≡ inj₁ a → f (inj₁ a) ≢ inj₁ a′

private

  -- Some helper functions.

  module ⊎-left-cancellative
    {a b c} {A : Type a} {B : Type b} {C : Type c}
    (f : A ⊎ B → A ⊎ C)
    (hyp : Well-behaved f)
    where

    mutual

      g : B → C
      g b = g′ (inspect (f (inj₂ b)))

      g′ : ∀ {b} → Other-singleton (f (inj₂ b)) → C
      g′ (inj₂ c , _)  = c
      g′ (inj₁ a , eq) = g″ eq (inspect (f (inj₁ a)))

      g″ : ∀ {a b} →
           f (inj₂ b) ≡ inj₁ a → Other-singleton (f (inj₁ a)) → C
      g″ _   (inj₂ c , _)   = c
      g″ eq₁ (inj₁ _ , eq₂) = ⊥-elim $ hyp eq₁ eq₂

⊎-left-cancellative :
  ∀ {a b c} {A : Type a} {B : Type b} {C : Type c}
  (f : A ⊎ B ↔ A ⊎ C) →
  Well-behaved (_↔_.to   f) →
  Well-behaved (_↔_.from f) →
  B ↔ C
⊎-left-cancellative {A = A} = λ inv to-hyp from-hyp → record
  { surjection = record
    { logical-equivalence = record
      { to   = g (to   inv) to-hyp
      ; from = g (from inv) from-hyp
      }
    ; right-inverse-of = g∘g (inverse inv) from-hyp to-hyp
    }
  ; left-inverse-of    = g∘g          inv  to-hyp from-hyp
  }
  where
  open _↔_
  open ⊎-left-cancellative

  abstract

    g∘g : ∀ {b c} {B : Type b} {C : Type c}
          (f : A ⊎ B ↔ A ⊎ C) →
          (to-hyp   : Well-behaved (to   f)) →
          (from-hyp : Well-behaved (from f)) →
          ∀ b → g (from f) from-hyp (g (to f) to-hyp b) ≡ b
    g∘g f to-hyp from-hyp b = g∘g′
      where
      g∘g′ : g (from f) from-hyp (g (to f) to-hyp b) ≡ b
      g∘g′ with inspect (to f (inj₂ b))
      g∘g′ | inj₂ c , eq₁ with inspect (from f (inj₂ c))
      g∘g′ | inj₂ c , eq₁ | inj₂ b′ , eq₂ = ⊎.cancel-inj₂ (
                                              inj₂ b′          ≡⟨ sym eq₂ ⟩
                                              from f (inj₂ c)  ≡⟨ to-from f eq₁ ⟩∎
                                              inj₂ b           ∎)
      g∘g′ | inj₂ c , eq₁ | inj₁ a  , eq₂ = ⊥-elim $ ⊎.inj₁≢inj₂ (
                                              inj₁ a           ≡⟨ sym eq₂ ⟩
                                              from f (inj₂ c)  ≡⟨ to-from f eq₁ ⟩∎
                                              inj₂ b           ∎)
      g∘g′ | inj₁ a , eq₁ with inspect (to f (inj₁ a))
      g∘g′ | inj₁ a , eq₁ | inj₁ a′ , eq₂ = ⊥-elim $ to-hyp eq₁ eq₂
      g∘g′ | inj₁ a , eq₁ | inj₂ c  , eq₂ with inspect (from f (inj₂ c))
      g∘g′ | inj₁ a , eq₁ | inj₂ c  , eq₂ | inj₂ b′ , eq₃ = ⊥-elim $ ⊎.inj₁≢inj₂ (
                                                              inj₁ a           ≡⟨ sym $ to-from f eq₂ ⟩
                                                              from f (inj₂ c)  ≡⟨ eq₃ ⟩∎
                                                              inj₂ b′          ∎)
      g∘g′ | inj₁ a , eq₁ | inj₂ c  , eq₂ | inj₁ a′ , eq₃ with inspect (from f (inj₁ a′))
      g∘g′ | inj₁ a , eq₁ | inj₂ c  , eq₂ | inj₁ a′ , eq₃ | inj₁ a″ , eq₄ = ⊥-elim $ from-hyp eq₃ eq₄
      g∘g′ | inj₁ a , eq₁ | inj₂ c  , eq₂ | inj₁ a′ , eq₃ | inj₂ b′ , eq₄ = ⊎.cancel-inj₂ (
        let lemma =
              inj₁ a′          ≡⟨ sym eq₃ ⟩
              from f (inj₂ c)  ≡⟨ to-from f eq₂ ⟩∎
              inj₁ a           ∎
        in
        inj₂ b′           ≡⟨ sym eq₄ ⟩
        from f (inj₁ a′)  ≡⟨ cong (from f ⊚ inj₁) $ ⊎.cancel-inj₁ lemma ⟩
        from f (inj₁ a)   ≡⟨ to-from f eq₁ ⟩∎
        inj₂ b            ∎)

-- _⊎_ is left cancellative (for bijections) if the left argument is
-- the unit type.

⊎-left-cancellative-⊤ :
  ∀ {a b} {A : Type a} {B : Type b} →
  (⊤ ⊎ A) ↔ (⊤ ⊎ B) → A ↔ B
⊎-left-cancellative-⊤ = λ ⊤⊎A↔⊤⊎B →
  ⊎-left-cancellative               ⊤⊎A↔⊤⊎B
                      (wb           ⊤⊎A↔⊤⊎B)
                      (wb $ inverse ⊤⊎A↔⊤⊎B)
  where
  open _↔_

  abstract

    wb : ∀ {a b} {A : Type a} {B : Type b}
         (⊤⊎A↔⊤⊎B : (⊤ ⊎ A) ↔ (⊤ ⊎ B)) →
         Well-behaved (_↔_.to ⊤⊎A↔⊤⊎B)
    wb ⊤⊎A↔⊤⊎B {b = b} eq₁ eq₂ = ⊎.inj₁≢inj₂ (
      inj₁ tt                 ≡⟨ sym $ to-from ⊤⊎A↔⊤⊎B eq₂ ⟩
      from ⊤⊎A↔⊤⊎B (inj₁ tt)  ≡⟨ to-from ⊤⊎A↔⊤⊎B eq₁ ⟩∎
      inj₂ b                  ∎)

-- If the codomain of ⊎-left-cancellative-⊤ is paired up with a value
-- in ⊤ ⊎ B, then the function can be strengthened to a bijection
-- (assuming both decidability of equality of values in B and
-- extensionality).

[⊤⊎↔⊤⊎]↔[⊤⊎×↔] :
  ∀ {a b} {A : Type a} {B : Type b} →
  Decidable-equality B →
  ((⊤ ⊎ A) ↔ (⊤ ⊎ B)) ↝[ a ⊔ b ∣ a ⊔ b ] (⊤ ⊎ B) × (A ↔ B)
[⊤⊎↔⊤⊎]↔[⊤⊎×↔] {a = a} {b = b} {A = A} {B = B} _≟B_ ext =
  generalise-ext?
    [⊤⊎↔⊤⊎]⇔[⊤⊎×↔]
    (λ ext → record
       { surjection = record
         { logical-equivalence = [⊤⊎↔⊤⊎]⇔[⊤⊎×↔]
         ; right-inverse-of    = to∘from ext
         }
       ; left-inverse-of = from∘to ext
       })
    ext
  where
  _≟_ : Decidable-equality (⊤ ⊎ B)
  _≟_ = ⊎.Dec._≟_ ⊤._≟_ _≟B_

  if-not : ∀ {a p} {A : Type a} {P : Type p} (d : Dec P) (t e : A) →
           ¬ P → if d then t else e ≡ e
  if-not (yes p) t e ¬p = ⊥-elim (¬p p)
  if-not (no  _) t e ¬p = refl _

  to : (⊤ ⊎ A) ↔ (⊤ ⊎ B) → (⊤ ⊎ B) × (A ↔ B)
  to ⊤⊎A↔⊤⊎B = _↔_.to ⊤⊎A↔⊤⊎B (inj₁ tt) , ⊎-left-cancellative-⊤ ⊤⊎A↔⊤⊎B

  from : (⊤ ⊎ B) × (A ↔ B) → (⊤ ⊎ A) ↔ (⊤ ⊎ B)
  from (⊤⊎B , A↔B) = record
    { surjection = record
      { logical-equivalence = record
        { to   = t ⊤⊎B
        ; from = f ⊤⊎B
        }
      ; right-inverse-of = t∘f ⊤⊎B
      }
    ; left-inverse-of = f∘t ⊤⊎B
    }
    where
    t : ⊤ ⊎ B → ⊤ ⊎ A → ⊤ ⊎ B
    t ⊤⊎B (inj₁ tt) = ⊤⊎B
    t ⊤⊎B (inj₂ a)  =
      let b = inj₂ (_↔_.to A↔B a) in
      if b ≟ ⊤⊎B then inj₁ tt else b

    f : ⊤ ⊎ B → ⊤ ⊎ B → ⊤ ⊎ A
    f ⊤⊎B (inj₁ tt) = [ const (inj₁ tt) , inj₂ ∘ _↔_.from A↔B ] ⊤⊎B
    f ⊤⊎B (inj₂ b)  =
      if ⊤⊎B ≟ inj₂ b then inj₁ tt else inj₂ (_↔_.from A↔B b)

    abstract

      t∘f : ∀ ⊤⊎B x → t ⊤⊎B (f ⊤⊎B x) ≡ x
      t∘f (inj₁ tt) (inj₁ tt) = refl _
      t∘f (inj₁ tt) (inj₂ b′) = inj₂ (_↔_.to A↔B (_↔_.from A↔B b′))  ≡⟨ cong inj₂ $ _↔_.right-inverse-of A↔B _ ⟩∎
                                inj₂ b′                              ∎
      t∘f (inj₂ b)  (inj₁ tt) with _↔_.to A↔B (_↔_.from A↔B b) ≟B b
      t∘f (inj₂ b)  (inj₁ tt) | yes _   = refl _
      t∘f (inj₂ b)  (inj₁ tt) | no  b≢b = ⊥-elim $ b≢b (
                                            _↔_.to A↔B (_↔_.from A↔B b)  ≡⟨ _↔_.right-inverse-of A↔B _ ⟩∎
                                            b                            ∎)
      t∘f (inj₂ b)  (inj₂ b′) with b ≟B b′
      t∘f (inj₂ b)  (inj₂ b′) | yes b≡b′ = inj₂ b  ≡⟨ cong inj₂ b≡b′ ⟩∎
                                           inj₂ b′ ∎
      t∘f (inj₂ b)  (inj₂ b′) | no  b≢b′ =
        t (inj₂ b) (inj₂ (_↔_.from A↔B b′))                           ≡⟨⟩

        if inj₂ (_↔_.to A↔B (_↔_.from A↔B b′)) ≟ inj₂ b then inj₁ tt
          else inj₂ (_↔_.to A↔B (_↔_.from A↔B b′))                    ≡⟨ cong (λ b′ → if inj₂ b′ ≟ inj₂ b then inj₁ tt else inj₂ b′) $
                                                                           _↔_.right-inverse-of A↔B _ ⟩
        if inj₂ b′ ≟ inj₂ b then inj₁ tt else inj₂ b′                 ≡⟨ if-not (inj₂ b′ ≟ inj₂ b) (inj₁ tt) _ (b≢b′ ∘ sym ∘ ⊎.cancel-inj₂) ⟩∎

        inj₂ b′                                                       ∎

      f∘t : ∀ ⊤⊎B x → f ⊤⊎B (t ⊤⊎B x) ≡ x
      f∘t (inj₁ tt) (inj₁ tt) = refl _
      f∘t (inj₁ tt) (inj₂ a)  = inj₂ (_↔_.from A↔B (_↔_.to A↔B a))  ≡⟨ cong inj₂ $ _↔_.left-inverse-of A↔B _ ⟩∎
                                inj₂ a                              ∎
      f∘t (inj₂ b)  (inj₁ tt) with b ≟B b
      f∘t (inj₂ b)  (inj₁ tt) | yes _   = refl _
      f∘t (inj₂ b)  (inj₁ tt) | no  b≢b = ⊥-elim $ b≢b (refl _)
      f∘t (inj₂ b)  (inj₂ a)  with _↔_.to A↔B a ≟B b
      f∘t (inj₂ b)  (inj₂ a)  | yes to-a≡b = inj₂ (_↔_.from A↔B b)  ≡⟨ cong inj₂ $ _↔_.to-from A↔B to-a≡b ⟩∎
                                             inj₂ a                 ∎
      f∘t (inj₂ b)  (inj₂ a)  | no  to-a≢b with b ≟B _↔_.to A↔B a
      f∘t (inj₂ b)  (inj₂ a)  | no  to-a≢b | yes b≡to-a = ⊥-elim $ to-a≢b
                                                            (_↔_.to A↔B a  ≡⟨ sym b≡to-a ⟩∎
                                                             b             ∎)
      f∘t (inj₂ b)  (inj₂ a)  | no  to-a≢b | no  b≢to-a =
        inj₂ (_↔_.from A↔B (_↔_.to A↔B a))  ≡⟨ cong inj₂ $ _↔_.left-inverse-of A↔B _ ⟩∎
        inj₂ a                              ∎

  [⊤⊎↔⊤⊎]⇔[⊤⊎×↔] : ((⊤ ⊎ A) ↔ (⊤ ⊎ B)) ⇔ (⊤ ⊎ B) × (A ↔ B)
  [⊤⊎↔⊤⊎]⇔[⊤⊎×↔] = record
    { to   = to
    ; from = from
    }

  to∘from :
    Extensionality (a ⊔ b) (a ⊔ b) →
    ∀ x → to (from x) ≡ x
  to∘from ext (⊤⊎B , A↔B) =
    cong (⊤⊎B ,_) (_↔_.to (↔-to-≡↔≡ ext A-set) (lemma ⊤⊎B))
    where
    A-set : Is-set A
    A-set =                 $⟨ _≟B_ ⟩
      Decidable-equality B  ↝⟨ decidable⇒set ⟩
      Is-set B              ↝⟨ H-level.respects-surjection
                                 (_↔_.surjection $ inverse A↔B) 2 ⟩□
      Is-set A              □

    lemma :
      ∀ ⊤⊎B a →
      _↔_.to (⊎-left-cancellative-⊤ (from (⊤⊎B , A↔B))) a ≡ _↔_.to A↔B a
    lemma (inj₁ tt) a = refl _
    lemma (inj₂ b)  a with inspect (_↔_.to (from (inj₂ b , A↔B))
                                           (inj₂ a))
    lemma (inj₂ b)  a | (inj₁ tt , eq) with _↔_.to A↔B a ≟B b
    lemma (inj₂ b)  a | (inj₁ tt , eq) | yes to-a≡b = sym to-a≡b
    lemma (inj₂ b)  a | (inj₁ tt , eq) | no  _      = ⊥-elim $ ⊎.inj₁≢inj₂ $ sym eq
    lemma (inj₂ b)  a | (inj₂ _  , eq) with _↔_.to A↔B a ≟B b
    lemma (inj₂ b)  a | (inj₂ _  , eq) | yes _ = ⊥-elim $ ⊎.inj₁≢inj₂ eq
    lemma (inj₂ b)  a | (inj₂ _  , eq) | no  _ = ⊎.cancel-inj₂ $ sym eq

  from∘to :
    Extensionality (a ⊔ b) (a ⊔ b) →
    ∀ x → from (to x) ≡ x
  from∘to ext ⊤⊎A↔⊤⊎B = _↔_.to (↔-to-≡↔≡ ext ⊤⊎A-set) lemma₁
    where
    open ⊎-left-cancellative

    ⊤⊎A-set : Is-set (⊤ ⊎ A)
    ⊤⊎A-set =               $⟨ _≟B_ ⟩
      Decidable-equality B  ↝⟨ decidable⇒set ⟩
      Is-set B              ↝⟨ ⊎-closure 0 (mono (zero≤ 2) ⊤-contractible) ⟩
      Is-set (⊤ ⊎ B)        ↝⟨ H-level.respects-surjection
                                 (_↔_.surjection $ inverse ⊤⊎A↔⊤⊎B) 2 ⟩□
      Is-set (⊤ ⊎ A)        □

    mutual

      lemma₁ : ∀ ⊤⊎A →
               _↔_.to (from (to ⊤⊎A↔⊤⊎B)) ⊤⊎A ≡ _↔_.to ⊤⊎A↔⊤⊎B ⊤⊎A
      lemma₁ (inj₁ tt) = refl _
      lemma₁ (inj₂ a)  = lemma₂ (inspect _) (inspect _)

      lemma₂ :
        ∀ {a} {wb : Well-behaved (_↔_.to ⊤⊎A↔⊤⊎B)}
        (x : Other-singleton (_↔_.to ⊤⊎A↔⊤⊎B (inj₂ a)))
        (y : Other-singleton (_↔_.to ⊤⊎A↔⊤⊎B (inj₁ tt))) →
        let b = g′ (_↔_.to ⊤⊎A↔⊤⊎B) wb x in
        if inj₂ b ≟ proj₁ y then inj₁ tt else inj₂ b ≡ proj₁ x
      lemma₂ {a} (inj₁ tt , eq₁) (inj₁ tt , eq₂) = ⊥-elim $ ⊎.inj₁≢inj₂ (
        inj₁ tt                                      ≡⟨ sym $ _↔_.left-inverse-of ⊤⊎A↔⊤⊎B _ ⟩
        _↔_.from ⊤⊎A↔⊤⊎B (_↔_.to ⊤⊎A↔⊤⊎B (inj₁ tt))  ≡⟨ cong (_↔_.from ⊤⊎A↔⊤⊎B) eq₂ ⟩
        _↔_.from ⊤⊎A↔⊤⊎B (inj₁ tt)                   ≡⟨ cong (_↔_.from ⊤⊎A↔⊤⊎B) $ sym eq₁ ⟩
        _↔_.from ⊤⊎A↔⊤⊎B (_↔_.to ⊤⊎A↔⊤⊎B (inj₂ a))   ≡⟨ _↔_.left-inverse-of ⊤⊎A↔⊤⊎B _ ⟩∎
        inj₂ a                                       ∎)
      lemma₂     (inj₁ tt , eq₁) (inj₂ b′ , eq₂) = lemma₃ eq₁ (inspect _) eq₂ (inj₂ _ ≟ inj₂ b′)
      lemma₂     (inj₂ b  , eq₁) (inj₁ tt , eq₂) = refl _
      lemma₂     (inj₂ b  , eq₁) (inj₂ b′ , eq₂) with b ≟B b′
      lemma₂     (inj₂ b  , eq₁) (inj₂ b′ , eq₂) | no  _    = refl _
      lemma₂ {a} (inj₂ b  , eq₁) (inj₂ b′ , eq₂) | yes b≡b′ =
        ⊥-elim $ ⊎.inj₁≢inj₂ (
          inj₁ tt                                      ≡⟨ sym $ _↔_.left-inverse-of ⊤⊎A↔⊤⊎B _ ⟩
          _↔_.from ⊤⊎A↔⊤⊎B (_↔_.to ⊤⊎A↔⊤⊎B (inj₁ tt))  ≡⟨ cong (_↔_.from ⊤⊎A↔⊤⊎B) eq₂ ⟩
          _↔_.from ⊤⊎A↔⊤⊎B (inj₂ b′)                   ≡⟨ cong (_↔_.from ⊤⊎A↔⊤⊎B ∘ inj₂) $ sym b≡b′ ⟩
          _↔_.from ⊤⊎A↔⊤⊎B (inj₂ b)                    ≡⟨ cong (_↔_.from ⊤⊎A↔⊤⊎B) $ sym eq₁ ⟩
          _↔_.from ⊤⊎A↔⊤⊎B (_↔_.to ⊤⊎A↔⊤⊎B (inj₂ a))   ≡⟨ _↔_.left-inverse-of ⊤⊎A↔⊤⊎B _ ⟩∎
          inj₂ a                                       ∎)

      lemma₃ :
        ∀ {a b′} {wb : Well-behaved (_↔_.to ⊤⊎A↔⊤⊎B)}
        (eq : _↔_.to ⊤⊎A↔⊤⊎B (inj₂ a) ≡ inj₁ tt)
        (x : Other-singleton (_↔_.to ⊤⊎A↔⊤⊎B (inj₁ tt))) →
        proj₁ x ≡ inj₂ b′ →
        let b = g″ (_↔_.to ⊤⊎A↔⊤⊎B) wb eq x in
        (d : Dec (inj₂ {A = ⊤} b ≡ inj₂ b′)) →
        if d then inj₁ tt else inj₂ b ≡ inj₁ tt
      lemma₃ eq₁ (inj₁ _  , eq₂) eq₃ _           = ⊥-elim $ ⊎.inj₁≢inj₂ eq₃
      lemma₃ eq₁ (inj₂ b″ , eq₂) eq₃ (yes b″≡b′) = refl _
      lemma₃ eq₁ (inj₂ b″ , eq₂) eq₃ (no  b″≢b′) = ⊥-elim $ b″≢b′ eq₃
