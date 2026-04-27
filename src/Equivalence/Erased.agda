------------------------------------------------------------------------
-- Equivalences with erased "proofs"
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Equivalence.Erased
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id; [_,_]) renaming (_∘_ to _⊚_)

open import Bijection eq using (_↔_)
open import Embedding eq using (Embedding)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
import Equivalence.Contractible-preimages eq as CP
open import Equivalence.Erased.Contractible-preimages eq as ECP
  using (_⁻¹ᴱ_; Contractibleᴱ)
import Equivalence.Half-adjoint eq as HA
open import Equivalence.Path-split eq using (_-Nullᴱ_)
open import Erased.Level-1 eq as Erased
  hiding (module []-cong; module []-cong₁; module []-cong₂-⊔)
open import Extensionality eq
open import Function-universe eq as F
  hiding (id; _∘_; inverse; from-isomorphism;
          step-↔; _↔⟨⟩_; _□; finally-↔; $⟨_⟩_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (_↣_)
import Nat eq as Nat
open import Preimage eq as Preimage using (_⁻¹_)
open import Surjection eq as Surjection using (_↠_; Split-surjective)
open import Tactic.Sigma-cong eq
open import Univalence-axiom eq

private
  variable
    a b d ℓ ℓ₁ ℓ₂ q : Level
    A B C D         : Type a
    c k k′ p x y    : A
    P Q             : A → Type p
    f f⁻¹ g         : (x : A) → P x

------------------------------------------------------------------------
-- Some basic stuff

open import Equivalence.Erased.Basics eq public

private
  variable
    A≃B : A ≃ᴱ B

------------------------------------------------------------------------
-- More conversion lemmas

-- In an erased context Is-equivalence and Is-equivalenceᴱ are
-- pointwise equivalent.

@0 Is-equivalence≃Is-equivalenceᴱ :
  {A : Type a} {B : Type b} {f : A → B} →
  Is-equivalence f ≃ Is-equivalenceᴱ f
Is-equivalence≃Is-equivalenceᴱ {f} =
  (∃ λ f⁻¹ → HA.Proofs f f⁻¹)           F.↔⟨ (∃-cong λ _ → F.inverse $ erased Erased↔) ⟩□
  (∃ λ f⁻¹ → Erased (HA.Proofs f f⁻¹))  □

_ :
  _≃_.to Is-equivalence≃Is-equivalenceᴱ p ≡
  Is-equivalence→Is-equivalenceᴱ p
_ = refl _

@0 _ :
  _≃_.from Is-equivalence≃Is-equivalenceᴱ p ≡
  Is-equivalenceᴱ→Is-equivalence p
_ = refl _

-- In an erased context _≃_ and _≃ᴱ_ are pointwise equivalent.

@0 ≃≃≃ᴱ : (A ≃ B) ≃ (A ≃ᴱ B)
≃≃≃ᴱ {A} {B} =
  A ≃ B                        F.↔⟨ Eq.≃-as-Σ ⟩
  (∃ λ f → Is-equivalence f)   ↝⟨ (∃-cong λ _ → Is-equivalence≃Is-equivalenceᴱ) ⟩
  (∃ λ f → Is-equivalenceᴱ f)  F.↔⟨ Eq.inverse ≃ᴱ-as-Σ ⟩□
  A ≃ᴱ B                       □

_ : _≃_.to ≃≃≃ᴱ p ≡ ≃→≃ᴱ p
_ = refl _

@0 _ : _≃_.from ≃≃≃ᴱ p ≡ ≃ᴱ→≃ p
_ = refl _

-- A variant of F.from-isomorphism with erased type arguments.

from-isomorphism :
  {@0 A : Type a} {@0 B : Type b} →
  A ↔[ k ] B → A ≃ᴱ B
from-isomorphism {k = equivalence} = ≃→≃ᴱ
from-isomorphism {k = bijection}   = λ A↔B →
  let record
        { surjection = record
          { logical-equivalence = record
            { to   = to
            ; from = from
            }
          }
        } = A↔B
  in
  ↔→≃ᴱ
    to
    from
    (_↔_.right-inverse-of A↔B)
    (_↔_.left-inverse-of  A↔B)

------------------------------------------------------------------------
-- "Equational" reasoning combinators with erased type arguments

infix  -1 finally-≃ᴱ finally-↔
infix  -1 _□
infixr -2 step-≃ᴱ step-↔ _↔⟨⟩_
infix  -3 $⟨_⟩_

-- For an explanation of why step-≃ᴱ and step-↔ are defined in this
-- way, see Equality.step-≡.

step-≃ᴱ :
  (@0 A : Type a) {@0 B : Type b} {@0 C : Type c} →
  B ≃ᴱ C → A ≃ᴱ B → A ≃ᴱ C
step-≃ᴱ _ = _∘_

syntax step-≃ᴱ A B≃ᴱC A≃ᴱB = A ≃ᴱ⟨ A≃ᴱB ⟩ B≃ᴱC

step-↔ :
  (@0 A : Type a) {@0 B : Type b} {@0 C : Type c} →
  B ≃ᴱ C → A ↔[ k ] B → A ≃ᴱ C
step-↔ _ B≃ᴱC A↔B = step-≃ᴱ _ B≃ᴱC (from-isomorphism A↔B)

syntax step-↔ A B≃ᴱC A↔B = A ↔⟨ A↔B ⟩ B≃ᴱC

_↔⟨⟩_ : (@0 A : Type a) {@0 B : Type b} → A ≃ᴱ B → A ≃ᴱ B
_ ↔⟨⟩ A≃ᴱB = A≃ᴱB

_□ : (@0 A : Type a) → A ≃ᴱ A
A □ = id

finally-≃ᴱ : (@0 A : Type a) (@0 B : Type b) → A ≃ᴱ B → A ≃ᴱ B
finally-≃ᴱ _ _ A≃ᴱB = A≃ᴱB

syntax finally-≃ᴱ A B A≃ᴱB = A ≃ᴱ⟨ A≃ᴱB ⟩□ B □

finally-↔ : (@0 A : Type a) (@0 B : Type b) → A ↔[ k ] B → A ≃ᴱ B
finally-↔ _ _ A↔B = from-isomorphism A↔B

syntax finally-↔ A B A↔B = A ↔⟨ A↔B ⟩□ B □

$⟨_⟩_ : {@0 A : Type a} {@0 B : Type b} → A → A ≃ᴱ B → B
$⟨ a ⟩ A≃ᴱB = _≃ᴱ_.to A≃ᴱB a

------------------------------------------------------------------------
-- Is-equivalenceᴱ is sometimes propositional

-- In an erased context Is-equivalenceᴱ f is a proposition (assuming
-- extensionality).
--
-- See also Is-equivalenceᴱ-propositional-for-Erased below.

@0 Is-equivalenceᴱ-propositional :
  {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  (f : A → B) → Is-proposition (Is-equivalenceᴱ f)
Is-equivalenceᴱ-propositional ext f =
  H-level.respects-surjection
    (_≃_.surjection $ Is-equivalence≃Is-equivalenceᴱ)
    1
    (Is-equivalence-propositional ext)

-- P -Nullᴱ B is a proposition in erased contexts (assuming
-- extensionality).

@0 Nullᴱ-propositional :
  {A : Type a} {P : A → Type p} {B : Type b} →
  Extensionality (a ⊔ p ⊔ b) (p ⊔ b) →
  Is-proposition (P -Nullᴱ B)
Nullᴱ-propositional {a} {p} {b} ext =
  Π-closure (lower-extensionality (p ⊔ b) lzero ext) 1 λ _ →
  Is-equivalenceᴱ-propositional (lower-extensionality a lzero ext) _

------------------------------------------------------------------------
-- More conversion lemmas, and a related result

-- Is-equivalenceᴱ f is equivalent (with erased proofs) to
-- ECP.Is-equivalenceᴱ f (assuming extensionality).

Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  Is-equivalenceᴱ f ≃ᴱ ECP.Is-equivalenceᴱ f
Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext =
  let record { to = to; from = from } =
        Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP
  in
  ⇔→≃ᴱ
    (Is-equivalenceᴱ-propositional ext _)
    (ECP.Is-equivalenceᴱ-propositional ext _)
    to
    from

-- A ≃ᴱ B is equivalent (with erased proofs) to A ECP.≃ᴱ B (assuming
-- extensionality).

≃ᴱ≃ᴱ≃ᴱ-CP :
  {A : Type a} {B : Type b} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  (A ≃ᴱ B) ≃ᴱ (A ECP.≃ᴱ B)
≃ᴱ≃ᴱ≃ᴱ-CP {A} {B} ext =
  A ≃ᴱ B                                 ↔⟨ ≃ᴱ-as-Σ ⟩
  (∃ λ (f : A → B) → Is-equivalenceᴱ f)  ↝⟨ (∃-cong λ _ → Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext) ⟩□
  A ECP.≃ᴱ B                             □

-- When proving that a function is an equivalence (with erased proofs)
-- one can assume that the codomain is inhabited.

[inhabited→Is-equivalenceᴱ]→Is-equivalenceᴱ :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
  (B → Is-equivalenceᴱ f) → Is-equivalenceᴱ f
[inhabited→Is-equivalenceᴱ]→Is-equivalenceᴱ hyp =
  let record { to = to; from = from } =
        Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP
  in
  from (λ x → to (hyp x) x)

------------------------------------------------------------------------
-- Some preservation lemmas

-- A variant of _×-cong_ for _≃ᴱ_. Note that all the type arguments
-- are erased.

infixr 2 _×-cong-≃ᴱ_

_×-cong-≃ᴱ_ :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} {@0 D : Type d} →
  A ≃ᴱ C → B ≃ᴱ D → (A × B) ≃ᴱ (C × D)
A≃ᴱC ×-cong-≃ᴱ B≃ᴱD = ↔→≃ᴱ
  (Σ-map (_≃ᴱ_.to A≃ᴱC)   (_≃ᴱ_.to B≃ᴱD))
  (Σ-map (_≃ᴱ_.from A≃ᴱC) (_≃ᴱ_.from B≃ᴱD))
  (λ _ →
     cong₂ _,_
       (_≃ᴱ_.right-inverse-of A≃ᴱC _)
       (_≃ᴱ_.right-inverse-of B≃ᴱD _))
  (λ _ →
     cong₂ _,_
       (_≃ᴱ_.left-inverse-of A≃ᴱC _)
       (_≃ᴱ_.left-inverse-of B≃ᴱD _))

-- A variant of ∃-cong for _≃ᴱ_. Note that all the type arguments are
-- erased.

∃-cong-≃ᴱ :
  {@0 A : Type a} {@0 P : A → Type p} {@0 Q : A → Type q} →
  (∀ x → P x ≃ᴱ Q x) → ∃ P ≃ᴱ ∃ Q
∃-cong-≃ᴱ P≃ᴱQ = ↔→≃ᴱ
  (λ (x , y) → x , _≃ᴱ_.to   (P≃ᴱQ x) y)
  (λ (x , y) → x , _≃ᴱ_.from (P≃ᴱQ x) y)
  (λ (x , y) → cong (x ,_) $ _≃ᴱ_.right-inverse-of (P≃ᴱQ x) y)
  (λ (x , y) → cong (x ,_) $ _≃ᴱ_.left-inverse-of  (P≃ᴱQ x) y)

-- A preservation lemma related to Σ.
--
-- Note that the third argument is not marked as erased. The from
-- argument of [≃]→≃ᴱ (which Agda can infer in this case, at least at
-- the time of writing) is included explicitly to show where the third
-- argument is used in a (potentially) non-erased context.
--
-- See also Σ-cong-≃ᴱ-Erased below.

Σ-cong-≃ᴱ :
  {@0 A : Type a} {@0 P : A → Type p}
  (f : A → B) (g : B → A) →
  (∀ x → f (g x) ≡ x) →
  @0 (∀ x → g (f x) ≡ x) →
  (∀ x → P x ≃ᴱ Q (f x)) →
  Σ A P ≃ᴱ Σ B Q
Σ-cong-≃ᴱ {Q} f g f-g g-f P≃Q =
  [≃]→≃ᴱ
    {from = λ (x , y) →
                g x
              , _≃ᴱ_.from (P≃Q (g x)) (subst Q (sym (f-g x)) y)}
    ([proofs] (Σ-cong (Eq.↔→≃ f g f-g g-f) (≃ᴱ→≃ ⊚ P≃Q)))

-- Another preservation lemma related to Σ.
--
-- See also Σ-cong-contra-≃ᴱ-Erased below.

Σ-cong-contra-≃ᴱ :
  {@0 B : Type b} {@0 Q : B → Type q}
  (f : B → A) (g : A → B) →
  (∀ x → f (g x) ≡ x) →
  @0 (∀ x → g (f x) ≡ x) →
  (∀ x → P (f x) ≃ᴱ Q x) →
  Σ A P ≃ᴱ Σ B Q
Σ-cong-contra-≃ᴱ f g f-g g-f P≃Q =
  inverse $ Σ-cong-≃ᴱ f g f-g g-f (inverse ⊚ P≃Q)

-- Yet another preservation lemma related to Σ.

Σ-cong-≃ᴱ′ :
  {@0 A : Type a} {@0 B : Type b}
  {@0 P : A → Type p} {@0 Q : B → Type q}
  (A≃ᴱB : A ≃ᴱ B)
  (P→Q : ∀ x → P x → Q (_≃ᴱ_.to A≃ᴱB x))
  (Q→P : ∀ x → Q x → P (_≃ᴱ_.from A≃ᴱB x))
  (@0 eq : ∀ x → Is-equivalence (P→Q x)) →
  @0 (∀ x y →
      Q→P x y ≡
      _≃_.from Eq.⟨ P→Q (_≃ᴱ_.from A≃ᴱB x) , eq (_≃ᴱ_.from A≃ᴱB x) ⟩
        (subst Q (sym (_≃ᴱ_.right-inverse-of A≃ᴱB x)) y)) →
  Σ A P ≃ᴱ Σ B Q
Σ-cong-≃ᴱ′ {A} {B} {P} {Q} A≃B P→Q Q→P eq hyp =
  [≃]→≃ᴱ ([proofs] ΣAP≃ΣBQ)
  where
  @0 ΣAP≃ΣBQ : Σ A P ≃ Σ B Q
  ΣAP≃ΣBQ =
    Eq.with-other-inverse
      (Σ-cong (≃ᴱ→≃ A≃B) (λ x → Eq.⟨ P→Q x , eq x ⟩))
      (λ (x , y) → _≃ᴱ_.from A≃B x , Q→P x y)
      (λ (x , y) → cong (_ ,_) (sym (hyp x y)))

-- Three preservation lemmas related to Π.
--
-- See also Π-cong-≃ᴱ′-≃ᴱ, Π-cong-≃ᴱ′-≃ᴱ′, Π-cong-≃ᴱ-Erased and
-- Π-cong-contra-≃ᴱ-Erased below.

Π-cong-≃ᴱ :
  {@0 A : Type a} {B : Type b} {@0 P : A → Type p} {Q : B → Type q} →
  @0 Extensionality (a ⊔ b) (p ⊔ q) →
  (f : A → B) (g : B → A) →
  (∀ x → f (g x) ≡ x) →
  @0 (∀ x → g (f x) ≡ x) →
  (∀ x → P x ≃ᴱ Q (f x)) →
  ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
Π-cong-≃ᴱ {Q} ext f g f-g g-f P≃Q =
  [≃]→≃ᴱ
    {to = λ h x → subst Q (f-g x) (_≃ᴱ_.to (P≃Q (g x)) (h (g x)))}
    ([proofs] (Π-cong ext {B₂ = Q} (Eq.↔→≃ f g f-g g-f) (≃ᴱ→≃ ⊚ P≃Q)))

Π-cong-contra-≃ᴱ :
  {A : Type a} {@0 B : Type b} {P : A → Type p} {@0 Q : B → Type q} →
  @0 Extensionality (a ⊔ b) (p ⊔ q) →
  (f : B → A) (g : A → B) →
  (∀ x → f (g x) ≡ x) →
  @0 (∀ x → g (f x) ≡ x) →
  (∀ x → P (f x) ≃ᴱ Q x) →
  ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
Π-cong-contra-≃ᴱ ext f g f-g g-f P≃Q =
  inverse $ Π-cong-≃ᴱ ext f g f-g g-f (inverse ⊚ P≃Q)

Π-cong-≃ᴱ′ :
  {@0 A : Type a} {@0 B : Type b}
  {@0 P : A → Type p} {@0 Q : B → Type q} →
  @0 Extensionality (a ⊔ b) (p ⊔ q) →
  (A≃ᴱB : A ≃ᴱ B)
  (P→Q : ∀ x → P (_≃ᴱ_.from A≃ᴱB x) → Q x)
  (Q→P : ∀ x → Q (_≃ᴱ_.to A≃ᴱB x) → P x)
  (@0 eq : ∀ x → Is-equivalence (Q→P x)) →
  @0 ((f : (x : A) → P x) (y : B) →
      let x = _≃ᴱ_.from A≃ᴱB y in
      P→Q y (f x) ≡
      subst Q (_≃ᴱ_.right-inverse-of A≃ᴱB y)
        (_≃_.from Eq.⟨ Q→P x , eq x ⟩ (f x))) →
  ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
Π-cong-≃ᴱ′ {a} {p} {A} {B} {P} {Q} ext A≃B P→Q Q→P eq hyp =
  [≃]→≃ᴱ ([proofs] ΠAP≃ΠBQ)
  where
  @0 ΠAP≃ΠBQ : ((x : A) → P x) ≃ ((x : B) → Q x)
  ΠAP≃ΠBQ =
    Eq.with-other-function
      (Π-cong ext (≃ᴱ→≃ A≃B) (λ x → Eq.inverse Eq.⟨ Q→P x , eq x ⟩))
      (λ f x → P→Q x (f (_≃ᴱ_.from A≃B x)))
      (λ f → apply-ext (lower-extensionality a p ext) λ x →
         sym (hyp f x))

-- A variant of ∀-cong for _≃ᴱ_.

∀-cong-≃ᴱ :
  {@0 A : Type a} {@0 P : A → Type p} {@0 Q : A → Type q} →
  @0 Extensionality a (p ⊔ q) →
  (∀ x → P x ≃ᴱ Q x) →
  ((x : A) → P x) ≃ᴱ ((x : A) → Q x)
∀-cong-≃ᴱ ext P≃Q = [≃]→≃ᴱ ([proofs] (∀-cong ext (≃ᴱ→≃ ⊚ P≃Q)))

-- Is-equivalenceᴱ f is equivalent (with erased proofs) to
-- Is-equivalenceᴱ g if f and g are pointwise equal (assuming
-- extensionality).
--
-- See also Is-equivalenceᴱ-cong below.

Is-equivalenceᴱ-cong-≃ᴱ :
  {@0 A : Type a} {@0 B : Type b} {@0 f g : A → B} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  @0 (∀ x → f x ≡ g x) →
  Is-equivalenceᴱ f ≃ᴱ Is-equivalenceᴱ g
Is-equivalenceᴱ-cong-≃ᴱ ext f≡g =
  ∃-cong-≃ᴱ λ _ → Erased-cong-≃ᴱ (≃→≃ᴱ $ Proofs-cong ext f≡g)

-- The _≃ᴱ_ operator preserves equivalences with erased proofs
-- (assuming extensionality).

≃ᴱ-cong :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} {@0 D : Type d} →
  @0 Extensionality (a ⊔ b ⊔ c ⊔ d) (a ⊔ b ⊔ c ⊔ d) →
  A ≃ᴱ B → C ≃ᴱ D → (A ≃ᴱ C) ≃ᴱ (B ≃ᴱ D)
≃ᴱ-cong {A} {B} {C} {D} ext A≃B C≃D =
  [≃]→≃ᴱ ([proofs] lemma)
  where
  @0 lemma : (A ≃ᴱ C) ≃ (B ≃ᴱ D)
  lemma =
    A ≃ᴱ C  ↝⟨ F.inverse ≃≃≃ᴱ ⟩
    A ≃ C   ↝⟨ Eq.≃-preserves ext (≃ᴱ→≃ A≃B) (≃ᴱ→≃ C≃D) ⟩
    B ≃ D   ↝⟨ ≃≃≃ᴱ ⟩□
    B ≃ᴱ D  □

-- A variant of ↑-cong for _≃ᴱ_.

↑-cong-≃ᴱ :
  {@0 B : Type b} {@0 C : Type c} →
  B ≃ᴱ C → ↑ a B ≃ᴱ ↑ a C
↑-cong-≃ᴱ B≃ᴱC = ↔→≃ᴱ
  (λ (lift x) → lift (_≃ᴱ_.to   B≃ᴱC x))
  (λ (lift x) → lift (_≃ᴱ_.from B≃ᴱC x))
  (λ _ → cong lift (_≃ᴱ_.right-inverse-of B≃ᴱC _))
  (λ _ → cong lift (_≃ᴱ_.left-inverse-of  B≃ᴱC _))

------------------------------------------------------------------------
-- Variants of some lemmas from Function-universe

-- A variant of drop-⊤-left-Σ.
--
-- See also drop-⊤-left-Σ-≃ᴱ-Erased below.

drop-⊤-left-Σ-≃ᴱ :
  {@0 A : Type a} {P : A → Type p}
  (A≃⊤ : A ≃ᴱ ⊤) →
  (∀ x y → P x ≃ᴱ P y) →
  Σ A P ≃ᴱ P (_≃ᴱ_.from A≃⊤ tt)
drop-⊤-left-Σ-≃ᴱ {A} {P} A≃⊤ P≃P =
  Σ A P                            ≃ᴱ⟨ Σ-cong-≃ᴱ
                                         _
                                         (_≃ᴱ_.from A≃⊤)
                                         refl
                                         (_≃ᴱ_.left-inverse-of A≃⊤)
                                         (λ _ → P≃P _ _) ⟩
  Σ ⊤ (λ x → P (_≃ᴱ_.from A≃⊤ x))  ↔⟨ Σ-left-identity ⟩□
  P (_≃ᴱ_.from A≃⊤ tt)             □

-- A variant of drop-⊤-left-Π.
--
-- See also drop-⊤-left-Π-≃ᴱ-Erased below.

drop-⊤-left-Π-≃ᴱ :
  {@0 A : Type a} {P : A → Type p} →
  @0 Extensionality a p →
  (A≃⊤ : A ≃ᴱ ⊤) →
  (∀ x y → P x ≃ᴱ P y) →
  ((x : A) → P x) ≃ᴱ P (_≃ᴱ_.from A≃⊤ tt)
drop-⊤-left-Π-≃ᴱ {A} {P} ext A≃⊤ P≃P =
  ((x : A) → P x)                  ≃ᴱ⟨ Π-cong-≃ᴱ
                                         ext
                                         _
                                         (_≃ᴱ_.from A≃⊤)
                                         refl
                                         (_≃ᴱ_.left-inverse-of A≃⊤)
                                         (λ _ → P≃P _ _) ⟩
  ((x : ⊤) → P (_≃ᴱ_.from A≃⊤ x))  ↔⟨ Π-left-identity ⟩□
  P (_≃ᴱ_.from A≃⊤ tt)             □

------------------------------------------------------------------------
-- A lemma related to Eq.≃-≡

-- A variant of Eq.≃-≡.
--
-- See also to≡to≃ᴱ≡-Erased below.

@0 to≡to≃ᴱ≡ :
  (A≃ᴱB : A ≃ᴱ B) →
  (_≃ᴱ_.to A≃ᴱB x ≡ _≃ᴱ_.to A≃ᴱB y) ≃ᴱ (x ≡ y)
to≡to≃ᴱ≡ {x} {y} A≃ᴱB =
  _≃ᴱ_.to A≃ᴱB x ≡ _≃ᴱ_.to A≃ᴱB y              F.↔⟨⟩
  _≃_.to (≃ᴱ→≃ A≃ᴱB) x ≡ _≃_.to (≃ᴱ→≃ A≃ᴱB) y  F.↔⟨ Eq.≃-≡ (≃ᴱ→≃ A≃ᴱB) ⟩□
  x ≡ y                                        □

------------------------------------------------------------------------
-- Lemmas relating equality between equivalences (with erased proofs)
-- to equality between the forward directions of the equivalences

-- In an erased context two equivalences are equal if the underlying
-- functions are equal (assuming extensionality).
--
-- See also to≡to→≡-Erased below.

@0 to≡to→≡ :
  {A : Type a} {B : Type b} {p q : A ≃ᴱ B} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  _≃ᴱ_.to p ≡ _≃ᴱ_.to q → p ≡ q
to≡to→≡ ext p≡q =
  _≃_.to (Eq.≃-≡ (Eq.inverse ≃≃≃ᴱ))
    (Eq.lift-equality ext p≡q)

-- A variant of ≃-to-≡↔≡.

@0 to≡to≃≡ :
  {A : Type a} {B : Type b} {p q : A ≃ᴱ B} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  (∀ x → _≃ᴱ_.to p x ≡ _≃ᴱ_.to q x) ≃ (p ≡ q)
to≡to≃≡ {p} {q} ext =
  (∀ x → _≃ᴱ_.to p x ≡ _≃ᴱ_.to q x)                                F.↔⟨⟩
  (∀ x → _≃_.to (_≃_.from ≃≃≃ᴱ p) x ≡ _≃_.to (_≃_.from ≃≃≃ᴱ q) x)  F.↔⟨ ≃-to-≡↔≡ ext ⟩
  _≃_.from ≃≃≃ᴱ p ≡ _≃_.from ≃≃≃ᴱ q                                ↝⟨ Eq.≃-≡ (Eq.inverse ≃≃≃ᴱ) ⟩□
  p ≡ q                                                            □

------------------------------------------------------------------------
-- Some definitions related to Dec-Erased

-- A preservation lemma for Dec-Erased.

Dec-Erased-cong-≃ᴱ :
  {A : Type a} {B : Type b} →
  @0 Extensionality (a ⊔ b) lzero →
  @0 A ≃ᴱ B → Dec-Erased A ≃ᴱ Dec-Erased B
Dec-Erased-cong-≃ᴱ ext A≃B =
  Erased-cong-≃ᴱ A≃B ⊎-cong Erased-cong-≃ᴱ (→-cong [ ext ] A≃B F.id)

-- A rearrangement lemma for subst and Dec-Erased-map.

subst-Dec-Erased-map :
  {A⇔B : A ⇔ B} {B≡C : B ≡ C}
  (x : Dec-Erased A) →
  subst (λ A → Dec-Erased A) B≡C (Dec-Erased-map A⇔B x) ≡
  Dec-Erased-map (subst (_⇔_ _) B≡C A⇔B) x
subst-Dec-Erased-map {A⇔B} {B≡C} x =
  elim¹
    (λ B≡C →
       subst (λ A → Dec-Erased A) B≡C (Dec-Erased-map A⇔B x) ≡
       Dec-Erased-map (subst (_⇔_ _) B≡C A⇔B) x)
    (trans (subst-refl _ _) $
     sym (cong (λ A⇔B → Dec-Erased-map A⇔B x) (subst-refl _ _)))
    B≡C

-- A map function for Decidable-erased-equality.

Decidable-erased-equality-map-≃ᴱ :
  A ≃ᴱ B →
  Decidable-erased-equality A → Decidable-erased-equality B
Decidable-erased-equality-map-≃ᴱ A≃ᴱB _≟_ x y =     F.$⟨ _≃ᴱ_.from A≃ᴱB x ≟ _≃ᴱ_.from A≃ᴱB y ⟩
  Dec-Erased (_≃ᴱ_.from A≃ᴱB x ≡ _≃ᴱ_.from A≃ᴱB y)  F.↝⟨ Dec-Erased-map (_≃ᴱ_.logical-equivalence (to≡to≃ᴱ≡ (inverse A≃ᴱB))) ⟩□
  Dec-Erased (x ≡ y)                                □

private

  -- A lemma used below.

  subst-⇔ :
    {A : Type a} {B C : Type ℓ}
    {A⇔B : A ⇔ B} {B≡C : B ≡ C} →
    Extensionality (a ⊔ ℓ) (a ⊔ ℓ) →
    subst (A ⇔_) B≡C A⇔B ≡
    record
      { to   = subst P.id B≡C ⊚ _⇔_.to A⇔B
      ; from = _⇔_.from A⇔B ⊚ subst P.id (sym B≡C)
      }
  subst-⇔ {a} {ℓ} {A} {A⇔B} {B≡C} ext =
    elim¹
      (λ B≡C →
         subst (A ⇔_) B≡C A⇔B ≡
         record
           { to   = subst P.id B≡C ⊚ _⇔_.to A⇔B
           ; from = _⇔_.from A⇔B ⊚ subst P.id (sym B≡C)
           })
      (trans (subst-refl _ _) $ sym $
       cong₂ (λ f g → record { to = f; from = g })
         (apply-ext (lower-extensionality ℓ a ext) λ _ →
          subst-refl _ _)
         (apply-ext (lower-extensionality a ℓ ext) λ _ →
          cong (_⇔_.from A⇔B) $
          trans (cong (flip (subst P.id) _) sym-refl) $
          subst-refl _ _))
      B≡C

-- A preservation lemma for Decidable-erased-equality.
--
-- Perhaps this proof could be simplified. A proof below, implemented
-- using []-cong, is arguably much nicer.

Decidable-erased-equality-cong-≃ᴱ :
  {A : Type a} {B : Type b} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  A ≃ᴱ B →
  Decidable-erased-equality A ≃ᴱ Decidable-erased-equality B
Decidable-erased-equality-cong-≃ᴱ {a} {b} {A} {B} ext A≃ᴱB =
  [≃]→≃ᴱ
    ([proofs]
       (Eq.with-other-function
          (Π-cong ext (≃ᴱ→≃ A≃ᴱB) λ _ →
           Π-cong ext (≃ᴱ→≃ A≃ᴱB) λ _ →
           let eq = Eq.≃-≡ (≃ᴱ→≃ A≃ᴱB) in
           F.inverse $
           Erased-cong-≃ eq
             ⊎-cong
           Erased-cong-≃
             (→-cong (lower-extensionality lzero _ ext) eq F.id))
          (Decidable-erased-equality-map-≃ᴱ A≃ᴱB)
          (λ f →
             apply-ext extᵇᵇ λ x →
             apply-ext extᵇᵇ λ y →

             subst (λ x → ∀ y → Dec-Erased (x ≡ y))
               (_≃ᴱ_.right-inverse-of A≃ᴱB x)
               (λ y →
                  subst
                    (λ y →
                       Dec-Erased (_≃ᴱ_.to A≃ᴱB (_≃ᴱ_.from A≃ᴱB x) ≡ y))
                    (_≃ᴱ_.right-inverse-of A≃ᴱB y)
                    (Dec-Erased-map
                       (F.inverse $ _≃ᴱ_.logical-equivalence $
                        to≡to≃ᴱ≡ A≃ᴱB)
                       (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))))
               y                                                          ≡⟨ sym $ push-subst-application _ _ ⟩

             subst (λ x → Dec-Erased (x ≡ y))
               (_≃ᴱ_.right-inverse-of A≃ᴱB x)
               (subst
                  (λ y →
                     Dec-Erased (_≃ᴱ_.to A≃ᴱB (_≃ᴱ_.from A≃ᴱB x) ≡ y))
                  (_≃ᴱ_.right-inverse-of A≃ᴱB y)
                  (Dec-Erased-map
                     (F.inverse $ _≃ᴱ_.logical-equivalence $
                      to≡to≃ᴱ≡ A≃ᴱB)
                     (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))))          ≡⟨ cong₂
                                                                               (λ eq₁ eq₂ →
                                                                                  subst (λ x → Dec-Erased (x ≡ y))
                                                                                    eq₁
                                                                                    (subst
                                                                                       (λ y →
                                                                                          Dec-Erased (_≃ᴱ_.to A≃ᴱB (_≃ᴱ_.from A≃ᴱB x) ≡ y))
                                                                                       eq₂
                                                                                       (Dec-Erased-map
                                                                                          (F.inverse $ _≃ᴱ_.logical-equivalence $
                                                                                           to≡to≃ᴱ≡ A≃ᴱB)
                                                                                          (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))))
                                                                               (sym $ cong (_$ x) $
                                                                                _≃_.left-inverse-of (Eq.extensionality-isomorphism extᵇᵇ) _)
                                                                               (sym $ cong (_$ y) $
                                                                                _≃_.left-inverse-of (Eq.extensionality-isomorphism extᵇᵇ) _) ⟩
             subst (λ x → Dec-Erased (x ≡ y))
               (ext⁻¹ (apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB)) x)
               (subst
                  (λ y →
                     Dec-Erased (_≃ᴱ_.to A≃ᴱB (_≃ᴱ_.from A≃ᴱB x) ≡ y))
                  (ext⁻¹ (apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB))
                     y)
                  (Dec-Erased-map
                     (F.inverse $ _≃ᴱ_.logical-equivalence $
                      to≡to≃ᴱ≡ A≃ᴱB)
                     (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))))          ≡⟨ elim₁
                                                                               (λ {x = g} eq →
                                                                                  (z : Dec-Erased (g x ≡ g y)) →
                                                                                  subst (λ x → Dec-Erased (x ≡ y))
                                                                                    (ext⁻¹ eq x)
                                                                                    (subst (λ y → Dec-Erased (g x ≡ y))
                                                                                       (ext⁻¹ eq y)
                                                                                       z) ≡
                                                                                  subst (λ g → Dec-Erased (g x ≡ g y)) eq z)
                                                                               (λ z →
               subst (λ x → Dec-Erased (x ≡ y)) (ext⁻¹ (refl F.id) x)
                 (subst (λ y → Dec-Erased (x ≡ y))
                    (ext⁻¹ (refl F.id) y) z)                                      ≡⟨ cong₂
                                                                                       (λ eq₁ eq₂ →
                                                                                          subst (λ x → Dec-Erased (x ≡ y)) eq₁
                                                                                            (subst (λ y → Dec-Erased (x ≡ y)) eq₂ z))
                                                                                       (ext⁻¹-refl _)
                                                                                       (ext⁻¹-refl _) ⟩
               subst (λ x → Dec-Erased (x ≡ y)) (refl x)
                 (subst (λ y → Dec-Erased (x ≡ y)) (refl y) z)                    ≡⟨ trans (subst-refl _ _) (subst-refl _ _) ⟩

               z                                                                  ≡⟨ sym (subst-refl _ _) ⟩∎

               subst (λ g → Dec-Erased (g x ≡ g y)) (refl F.id) z                 ∎)
                                                                               (apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB))
                                                                               (Dec-Erased-map
                                                                                  (F.inverse $ _≃ᴱ_.logical-equivalence $ to≡to≃ᴱ≡ A≃ᴱB)
                                                                                  (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))) ⟩
             subst (λ g → Dec-Erased (g x ≡ g y))
               (apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB))
               (Dec-Erased-map
                  (F.inverse (_≃ᴱ_.logical-equivalence (to≡to≃ᴱ≡ A≃ᴱB)))
                  (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))              ≡⟨⟩

             subst (λ g → Dec-Erased (g x ≡ g y))
               (apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB))
               (Dec-Erased-map
                  (record
                     { to   = cong (_≃ᴱ_.to A≃ᴱB)
                     ; from =
                         λ eq →
                           trans
                             (sym $
                              _≃ᴱ_.left-inverse-of A≃ᴱB
                                (_≃ᴱ_.from A≃ᴱB x))
                             (trans (cong (_≃ᴱ_.from A≃ᴱB) eq)
                                (_≃ᴱ_.left-inverse-of A≃ᴱB
                                   (_≃ᴱ_.from A≃ᴱB y)))
                     })
                  (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))              ≡⟨ cong₂
                                                                               (λ eq₁ eq₂ →
                                                                                  subst (λ g → Dec-Erased (g x ≡ g y))
                                                                                    (apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB))
                                                                                    (Dec-Erased-map
                                                                                       (record
                                                                                          { to   = cong (_≃ᴱ_.to A≃ᴱB)
                                                                                          ; from =
                                                                                              λ eq →
                                                                                                trans (sym eq₁)
                                                                                                  (trans (cong (_≃ᴱ_.from A≃ᴱB) eq) eq₂)
                                                                                          })
                                                                                       (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))))
                                                                               (sym (_≃ᴱ_.right-left-lemma A≃ᴱB _))
                                                                               (sym (_≃ᴱ_.right-left-lemma A≃ᴱB _)) ⟩
             subst (λ g → Dec-Erased (g x ≡ g y))
               (apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB))
               (Dec-Erased-map
                  (record
                     { to   = cong (_≃ᴱ_.to A≃ᴱB)
                     ; from =
                         λ eq →
                           trans
                             (sym $ cong (_≃ᴱ_.from A≃ᴱB) $
                              _≃ᴱ_.right-inverse-of A≃ᴱB x)
                             (trans (cong (_≃ᴱ_.from A≃ᴱB) eq)
                                (cong (_≃ᴱ_.from A≃ᴱB) $
                                 _≃ᴱ_.right-inverse-of A≃ᴱB y))
                     })
                  (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))              ≡⟨ cong
                                                                               (λ eq →
                                                                                  subst (λ g → Dec-Erased (g x ≡ g y))
                                                                                    (apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB))
                                                                                    (Dec-Erased-map
                                                                                       (record
                                                                                          { to   = cong (_≃ᴱ_.to A≃ᴱB)
                                                                                          ; from = eq
                                                                                          })
                                                                                       (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))))
                                                                               (apply-ext (lower-extensionality a b ext) λ eq →
                                                                                trans
                                                                                  (cong₂ trans
                                                                                     (sym (cong-sym _ _))
                                                                                     (sym (cong-trans _ _ _))) $
                                                                                trans (sym (cong-trans _ _ _)) $
                                                                                cong₂
                                                                                  (λ eq₁ eq₂ →
                                                                                     cong (_≃ᴱ_.from A≃ᴱB) $
                                                                                     trans (sym eq₁) (trans eq eq₂))
                                                                                  (sym $ cong (_$ x) $
                                                                                   _≃_.left-inverse-of
                                                                                     (Eq.extensionality-isomorphism extᵇᵇ) _)
                                                                                  (sym $ cong (_$ y) $
                                                                                   _≃_.left-inverse-of
                                                                                     (Eq.extensionality-isomorphism extᵇᵇ) _)) ⟩
             (let eq = apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB) in
              subst (λ g → Dec-Erased (g x ≡ g y)) eq
                (Dec-Erased-map
                   (record
                      { to   = cong (_≃ᴱ_.to A≃ᴱB)
                      ; from =
                          λ eq′ →
                            cong (_≃ᴱ_.from A≃ᴱB) $
                            trans (sym (ext⁻¹ eq x))
                              (trans eq′ (ext⁻¹ eq y))
                      })
                   (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))))            ≡⟨ subst-∘ _ _ _ ⟩

             (let eq = apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB) in
              subst (λ A → Dec-Erased A) (cong (λ g → g x ≡ g y) eq)
                (Dec-Erased-map
                   (record
                      { to   = cong (_≃ᴱ_.to A≃ᴱB)
                      ; from =
                          λ eq′ →
                            cong (_≃ᴱ_.from A≃ᴱB) $
                            trans (sym (ext⁻¹ eq x))
                              (trans eq′ (ext⁻¹ eq y))
                      })
                   (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))))            ≡⟨ subst-Dec-Erased-map (f _ _) ⟩

             (let eq = apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB) in
              Dec-Erased-map
                (subst (_⇔_ _) (cong (λ g → g x ≡ g y) eq) $
                 record
                   { to   = cong (_≃ᴱ_.to A≃ᴱB)
                   ; from =
                       λ eq′ →
                         cong (_≃ᴱ_.from A≃ᴱB) $
                         trans (sym (ext⁻¹ eq x))
                           (trans eq′ (ext⁻¹ eq y))
                   })
                (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))                ≡⟨ cong
                                                                               (λ eq →
                                                                                  Dec-Erased-map eq
                                                                                    (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))) $
                                                                             subst-⇔ ext ⟩
             (let eq = apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB) in
              Dec-Erased-map
                (record
                   { to =
                       subst P.id (cong (λ g → g x ≡ g y) eq) ⊚
                       cong (_≃ᴱ_.to A≃ᴱB)
                   ; from =
                       λ eq′ →
                         cong (_≃ᴱ_.from A≃ᴱB) $
                         trans (sym (ext⁻¹ eq x))
                           (trans
                              (subst P.id
                                 (sym (cong (λ g → g x ≡ g y) eq)) eq′)
                              (ext⁻¹ eq y))
                   })
                (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))                ≡⟨ (let eq = apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB) in
                                                                              cong₂
                                                                                (λ g h →
                                                                                   Dec-Erased-map (record { to = g; from = h })
                                                                                     (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))
                                                                                (apply-ext extᵃᵇ λ eq′ →
                                                                                 sym (subst-∘ _ _ _ {p = cong (_≃ᴱ_.to A≃ᴱB) eq′}))
                                                                                (apply-ext extᵇᵃ λ eq′ →
                                                                                   cong (cong (_≃ᴱ_.from A≃ᴱB)) $
                                                                                   elim₁
                                                                                     (λ {x = x} eq′ →
                                                                                        trans (sym (ext⁻¹ eq x))
                                                                                          (trans (subst P.id (sym (cong (λ g → g x ≡ g y) eq)) eq′)
                                                                                             (ext⁻¹ eq y)) ≡
                                                                                        eq′)
                                                                                     (
               trans (sym (ext⁻¹ eq y))
                 (trans
                    (subst P.id (sym (cong (λ g → g y ≡ g y) eq))
                       (refl y))
                    (ext⁻¹ eq y))                                                     ≡⟨ cong (trans _) $
                                                                                         trans
                                                                                           (cong (flip trans _) $
                                                                                            elim₁
                                                                                              (λ {x = f} eq →
                                                                                                 subst P.id
                                                                                                   (sym (cong (λ g → g y ≡ g y) eq)) (refl y) ≡
                                                                                                 refl (f y))
                                                                                              (trans
                                                                                                 (cong (flip (subst P.id) _) $
                                                                                                  trans (cong sym (cong-refl _))
                                                                                                  sym-refl) $
                                                                                               subst-refl _ _)
                                                                                              eq) $
                                                                                         trans-reflˡ _ ⟩

               trans (sym (ext⁻¹ eq y)) (ext⁻¹ eq y)                                  ≡⟨ trans-symˡ _ ⟩∎

               refl y                                                                 ∎)
                                                                                     eq′)) ⟩
             (let eq = apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB) in
              Dec-Erased-map
                (record
                   { to =
                       subst (λ g → g x ≡ g y) eq ⊚ cong (_≃ᴱ_.to A≃ᴱB)
                   ; from = cong (_≃ᴱ_.from A≃ᴱB)
                   })
                (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))                ≡⟨ cong
                                                                               (λ g →
                                                                                  Dec-Erased-map
                                                                                    (record
                                                                                       { to   = g
                                                                                       ; from = cong (_≃ᴱ_.from A≃ᴱB)
                                                                                       })
                                                                                    (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))
                                                                               (apply-ext extᵃᵇ λ eq →
                                                                                subst-in-terms-of-trans-and-cong {fx≡gx = cong (_≃ᴱ_.to A≃ᴱB) eq}) ⟩
             (let eq = apply-ext extᵇᵇ (_≃ᴱ_.right-inverse-of A≃ᴱB) in
              Dec-Erased-map
                (record
                   { to =
                       λ eq′ →
                         trans (sym (ext⁻¹ eq x))
                           (trans (cong (_≃ᴱ_.to A≃ᴱB) eq′)
                              (ext⁻¹ eq y))
                   ; from = cong (_≃ᴱ_.from A≃ᴱB)
                   })
                (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))                ≡⟨ cong₂
                                                                               (λ eq₁ eq₂ →
                                                                                  Dec-Erased-map
                                                                                    (record
                                                                                       { to =
                                                                                           λ eq →
                                                                                             trans (sym eq₁)
                                                                                               (trans (cong (_≃ᴱ_.to A≃ᴱB) eq)
                                                                                                  eq₂)
                                                                                       ; from = cong (_≃ᴱ_.from A≃ᴱB)
                                                                                       })
                                                                                    (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y)))
                                                                               (cong (_$ x) $
                                                                                _≃_.left-inverse-of (Eq.extensionality-isomorphism extᵇᵇ) _)
                                                                               (cong (_$ y) $
                                                                                _≃_.left-inverse-of (Eq.extensionality-isomorphism extᵇᵇ) _) ⟩
             Dec-Erased-map
               (record
                  { to =
                      λ eq →
                        trans (sym (_≃ᴱ_.right-inverse-of A≃ᴱB x))
                          (trans (cong (_≃ᴱ_.to A≃ᴱB) eq)
                             (_≃ᴱ_.right-inverse-of A≃ᴱB y))
                  ; from = cong (_≃ᴱ_.from A≃ᴱB)
                  })
               (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))                  ≡⟨⟩

             Dec-Erased-map
               (_≃ᴱ_.logical-equivalence (to≡to≃ᴱ≡ (inverse A≃ᴱB)))
               (f (_≃ᴱ_.from A≃ᴱB x) (_≃ᴱ_.from A≃ᴱB y))                  ∎)))
  where
  open module @0 E =
         Erased-cong erased-instance-of-[]-cong-axiomatisation
           erased-instance-of-[]-cong-axiomatisation

  @0 extᵃᵇ : Extensionality a b
  extᵃᵇ = lower-extensionality b a ext

  @0 extᵇᵃ : Extensionality b a
  extᵇᵃ = lower-extensionality a b ext

  @0 extᵇᵇ : Extensionality b b
  extᵇᵇ = lower-extensionality a a ext

------------------------------------------------------------------------
-- A variant of _≃ᴱ_

-- Half adjoint equivalences with certain erased proofs.

private
 module Dummy where

  infix 4 _≃ᴱ′_

  record _≃ᴱ′_ (A : Type a) (B : Type b) : Type (a ⊔ b) where
    no-eta-equality
    pattern
    field
      to            : A → B
      from          : B → A
      @0 to-from    : ∀ x → to (from x) ≡ x
      from-to       : ∀ x → from (to x) ≡ x
      @0 to-from-to : ∀ x → cong to (from-to x) ≡ to-from (to x)

open Dummy public using (_≃ᴱ′_) hiding (module _≃ᴱ′_)

-- Some definitions used in _≃ᴱ′_.

private module _≃ᴱ″_ {@0 A : Type a} {@0 B : Type b} where

  -- Variants of the projections.

  to : A ≃ᴱ′ B → A → B
  to (record { to = to }) = to

  from : A ≃ᴱ′ B → B → A
  from (record { from = from }) = from

  @0 to-from : ∀ A≃B x → to A≃B (from A≃B x) ≡ x
  to-from (record { to-from = to-from }) = to-from

  from-to : ∀ A≃B x → from A≃B (to A≃B x) ≡ x
  from-to (record { from-to = from-to }) = from-to

  @0 to-from-to :
    ∀ A≃B x → cong (to A≃B) (from-to A≃B x) ≡ to-from A≃B (to A≃B x)
  to-from-to (record { to-from-to = to-from-to }) = to-from-to

-- Note that the type arguments A and B are erased. This is not the
-- case for the record module Dummy._≃ᴱ′_.

module _≃ᴱ′_ {@0 A : Type a} {@0 B : Type b} (A≃B : A ≃ᴱ′ B) where

  -- Variants of the projections.

  to : A → B
  to = _≃ᴱ″_.to A≃B

  from : B → A
  from = _≃ᴱ″_.from A≃B

  @0 to-from : ∀ x → to (from x) ≡ x
  to-from = _≃ᴱ″_.to-from A≃B

  from-to : ∀ x → from (to x) ≡ x
  from-to = _≃ᴱ″_.from-to A≃B

  @0 to-from-to : ∀ x → cong to (from-to x) ≡ to-from (to x)
  to-from-to = _≃ᴱ″_.to-from-to A≃B

  -- Half adjoint equivalences with certain erased proofs are
  -- equivalences with erased proofs.

  equivalence-with-erased-proofs : A ≃ᴱ B
  equivalence-with-erased-proofs =
    ⟨ to , (from , [ to-from , from-to , to-from-to ]) ⟩₀

  -- A coherence property.

  @0 from-to-from : ∀ x → cong from (to-from x) ≡ from-to (from x)
  from-to-from = _≃ᴱ_.right-left-lemma equivalence-with-erased-proofs

-- Data corresponding to the erased proofs of an equivalence with
-- certain erased proofs.

record Erased-proofs′
         {A : Type a} {B : Type b}
         (to : A → B) (from : B → A)
         (from-to : ∀ x → from (to x) ≡ x) :
         Type (a ⊔ b) where
  field
    to-from    : ∀ x → to (from x) ≡ x
    to-from-to : ∀ x → cong to (from-to x) ≡ to-from (to x)

-- Extracts "erased proofs" from a regular equivalence.

[proofs′] :
  {@0 A : Type a} {@0 B : Type b}
  (A≃B : A ≃ B) →
  Erased-proofs′ (_≃_.to A≃B) (_≃_.from A≃B) (_≃_.left-inverse-of A≃B)
[proofs′] A≃B .Erased-proofs′.to-from =
  let record { is-equivalence = _ , to-from , _ } = A≃B in
  to-from
[proofs′] A≃B .Erased-proofs′.to-from-to =
  let record { is-equivalence = _ , _ , _ , to-from-to } = A≃B in
  to-from-to

-- Converts two functions, one proof and some erased proofs to an
-- equivalence with certain erased proofs.

[≃]→≃ᴱ′ :
  {@0 A : Type a} {@0 B : Type b}
  {to : A → B} {from : B → A} {from-to : ∀ x → from (to x) ≡ x} →
  @0 Erased-proofs′ to from from-to →
  A ≃ᴱ′ B
[≃]→≃ᴱ′ {to} {from} {from-to} ep = record
  { to         = to
  ; from       = from
  ; to-from    = ep .Erased-proofs′.to-from
  ; from-to    = from-to
  ; to-from-to = ep .Erased-proofs′.to-from-to
  }

-- A function with a quasi-inverse with one proof and one erased proof
-- can be turned into an equivalence with certain erased proofs.

↔→≃ᴱ′ :
  {@0 A : Type a} {@0 B : Type b}
  (f : A → B) (g : B → A) →
  @0 (∀ x → f (g x) ≡ x) →
  (∀ x → g (f x) ≡ x) →
  A ≃ᴱ′ B
↔→≃ᴱ′ {A} {B} to from to-from from-to =
  [≃]→≃ᴱ′ ([proofs′] equiv)
  where
  @0 equiv : A ≃ B
  equiv =
    Eq.⟨ to
       , HA.↔→Is-equivalenceˡ (record
           { surjection = record
             { logical-equivalence = record
               { to   = to
               ; from = from
               }
             ; right-inverse-of = to-from
             }
           ; left-inverse-of = from-to
           })
       ⟩

-- If f is an equivalence with certain erased proofs, then there is an
-- equivalence with certain erased proofs from x ≡ y to f x ≡ f y.

≡≃ᴱ′to≡to :
  (A≃ᴱ′B : A ≃ᴱ′ B) →
  (x ≡ y) ≃ᴱ′ (_≃ᴱ′_.to A≃ᴱ′B x ≡ _≃ᴱ′_.to A≃ᴱ′B y)
≡≃ᴱ′to≡to {x} {y} A≃ᴱ′B =
  ↔→≃ᴱ′
    (_↠_.from ≡↠≡)
    (_↠_.to   ≡↠≡)
    (λ eq →
       _↠_.from ≡↠≡ (_↠_.to ≡↠≡ eq)                                          ≡⟨⟩

       cong to (trans (sym (from-to x)) (trans (cong from eq) (from-to y)))  ≡⟨ cong-trans _ _ _ ⟩

       trans (cong to (sym (from-to x)))
         (cong to (trans (cong from eq) (from-to y)))                        ≡⟨ cong₂ trans
                                                                                  (cong-sym _ _)
                                                                                  (cong-trans _ _ _) ⟩
       trans (sym (cong to (from-to x)))
         (trans (cong to (cong from eq)) (cong to (from-to y)))              ≡⟨ cong₂ (λ p q → trans (sym p) (trans (cong to (cong from eq)) q))
                                                                                  (to-from-to _)
                                                                                  (to-from-to _) ⟩
       trans (sym (to-from (to x)))
         (trans (cong to (cong from eq)) (to-from (to y)))                   ≡⟨⟩

       _↠_.to ≡↠≡′ (_↠_.from ≡↠≡′ eq)                                        ≡⟨ _↠_.right-inverse-of ≡↠≡′ eq ⟩∎

       eq                                                                    ∎)
    (_↠_.right-inverse-of ≡↠≡)
  where
  open _≃ᴱ′_ A≃ᴱ′B

  ≡↠≡ : (to x ≡ to y) ↠ (x ≡ y)
  ≡↠≡ = Surjection.↠-≡ (record
    { logical-equivalence = record
      { to   = from
      ; from = to
      }
    ; right-inverse-of = from-to
    })

  @0 ≡↠≡′ : ∀ {x y} → (from x ≡ from y) ↠ (x ≡ y)
  ≡↠≡′ = Surjection.↠-≡ (record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to-from
    })

-- If f is an equivalence with certain erased proofs, then x ≡ y is
-- equivalent (with erased proofs) to f x ≡ f y.
--
-- See also to≡to≃ᴱ≡-Erased below.

≡≃ᴱto≡to :
  (A≃ᴱ′B : A ≃ᴱ′ B) →
  (x ≡ y) ≃ᴱ (_≃ᴱ′_.to A≃ᴱ′B x ≡ _≃ᴱ′_.to A≃ᴱ′B y)
≡≃ᴱto≡to = _≃ᴱ′_.equivalence-with-erased-proofs ⊚ ≡≃ᴱ′to≡to

-- Two preservation lemmas related to Π.

Π-cong-≃ᴱ′-≃ᴱ :
  {@0 A : Type a} {B : Type b} {@0 P : A → Type p} {Q : B → Type q} →
  @0 Extensionality (a ⊔ b) (p ⊔ q) →
  (B≃A : B ≃ᴱ′ A) →
  (∀ x → P x ≃ᴱ Q (_≃ᴱ′_.from B≃A x)) →
  ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
Π-cong-≃ᴱ′-≃ᴱ ext B≃A =
  Π-cong-≃ᴱ
    ext
    (_≃ᴱ′_.from B≃A)
    (_≃ᴱ′_.to B≃A)
    (_≃ᴱ′_.from-to B≃A)
    (_≃ᴱ′_.to-from B≃A)

Π-cong-≃ᴱ′-≃ᴱ′ :
  {A : Type a} {@0 B : Type b} {P : A → Type p} {@0 Q : B → Type q} →
  Extensionality (a ⊔ b) (p ⊔ q) →
  (A≃B : A ≃ᴱ′ B) →
  (∀ x → P (_≃ᴱ′_.from A≃B x) ≃ᴱ′ Q x) →
  ((x : A) → P x) ≃ᴱ′ ((x : B) → Q x)
Π-cong-≃ᴱ′-≃ᴱ′ {a} {b} {p} {q} {A} {B} {P} {Q} ext A≃B P≃Q =
  ↔→≃ᴱ′
    (λ f x → _≃ᴱ′_.to (P≃Q x) (f (_≃ᴱ′_.from A≃B x)))
    (λ f x →
       subst P (_≃ᴱ′_.from-to A≃B x)
         (_≃ᴱ′_.from (P≃Q (_≃ᴱ′_.to A≃B x)) (f (_≃ᴱ′_.to A≃B x))))
    (λ f → apply-ext (lower-extensionality a p ext) λ x →
       _≃ᴱ′_.to (P≃Q x)
          (subst P (_≃ᴱ′_.from-to A≃B (_≃ᴱ′_.from A≃B x))
             (_≃ᴱ′_.from (P≃Q (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))
                (f (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))))            ≡⟨ cong (_≃ᴱ′_.to (P≃Q x) ⊚ flip (subst P) _) $ sym $
                                                                      _≃ᴱ′_.from-to-from A≃B _ ⟩
       _≃ᴱ′_.to (P≃Q x)
          (subst P (cong (_≃ᴱ′_.from A≃B) (_≃ᴱ′_.to-from A≃B x))
             (_≃ᴱ′_.from (P≃Q (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))
                (f (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))))            ≡⟨ elim¹
                                                                        (λ {y} eq →
                                                                           _≃ᴱ′_.to (P≃Q y)
                                                                             (subst P (cong (_≃ᴱ′_.from A≃B) eq)
                                                                                (_≃ᴱ′_.from (P≃Q (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))
                                                                                   (f (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x))))) ≡
                                                                           f y)
                                                                        (
         _≃ᴱ′_.to (P≃Q (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))
           (subst P (cong (_≃ᴱ′_.from A≃B) (refl _))
              (_≃ᴱ′_.from (P≃Q (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))
                 (f (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))))                 ≡⟨ cong (_≃ᴱ′_.to (P≃Q (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))) $
                                                                            trans (cong (flip (subst P) _) $ cong-refl _) $
                                                                            subst-refl _ _ ⟩
         _≃ᴱ′_.to (P≃Q (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))
           (_≃ᴱ′_.from (P≃Q (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x)))
              (f (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x))))                     ≡⟨ _≃ᴱ′_.to-from (P≃Q _) _ ⟩∎

         f (_≃ᴱ′_.to A≃B (_≃ᴱ′_.from A≃B x))                             ∎)
                                                                        _ ⟩∎
       f x                                                         ∎)
    (λ f → apply-ext (lower-extensionality b q ext) λ x →
       subst P (_≃ᴱ′_.from-to A≃B x)
         (_≃ᴱ′_.from (P≃Q (_≃ᴱ′_.to A≃B x))
            (_≃ᴱ′_.to (P≃Q (_≃ᴱ′_.to A≃B x))
               (f (_≃ᴱ′_.from A≃B (_≃ᴱ′_.to A≃B x)))))    ≡⟨ elim¹
                                                               (λ {y} eq →
                                                                  subst P eq
                                                                    (_≃ᴱ′_.from (P≃Q (_≃ᴱ′_.to A≃B x))
                                                                       (_≃ᴱ′_.to (P≃Q (_≃ᴱ′_.to A≃B x))
                                                                          (f (_≃ᴱ′_.from A≃B (_≃ᴱ′_.to A≃B x))))) ≡
                                                                  f y)
                                                               (
         subst P (refl _)
           (_≃ᴱ′_.from (P≃Q (_≃ᴱ′_.to A≃B x))
              (_≃ᴱ′_.to (P≃Q (_≃ᴱ′_.to A≃B x))
                 (f (_≃ᴱ′_.from A≃B (_≃ᴱ′_.to A≃B x)))))         ≡⟨ subst-refl _ _ ⟩

         _≃ᴱ′_.from (P≃Q (_≃ᴱ′_.to A≃B x))
           (_≃ᴱ′_.to (P≃Q (_≃ᴱ′_.to A≃B x))
              (f (_≃ᴱ′_.from A≃B (_≃ᴱ′_.to A≃B x))))             ≡⟨ _≃ᴱ′_.from-to (P≃Q _) _ ⟩∎

         f (_≃ᴱ′_.from A≃B (_≃ᴱ′_.to A≃B x))                     ∎)
                                                               _ ⟩∎

       f x                                                ∎)

------------------------------------------------------------------------
-- Some results related to Contractibleᴱ

-- Two types that are contractible (with erased proofs) are equivalent
-- (with erased proofs).

Contractibleᴱ→≃ᴱ :
  {@0 A : Type a} {@0 B : Type b} →
  Contractibleᴱ A → Contractibleᴱ B → A ≃ᴱ B
Contractibleᴱ→≃ᴱ (a , [ irrA ]) (b , [ irrB ]) = ↔→≃ᴱ
  (const b)
  (const a)
  irrB
  irrA

-- There is a logical equivalence between Contractibleᴱ A and A ≃ᴱ ⊤.

Contractibleᴱ⇔≃ᴱ⊤ :
  {@0 A : Type a} →
  Contractibleᴱ A ⇔ A ≃ᴱ ⊤
Contractibleᴱ⇔≃ᴱ⊤ = record
  { to   = flip Contractibleᴱ→≃ᴱ Contractibleᴱ-⊤
  ; from = λ A≃⊤ →
      ECP.Contractibleᴱ-respects-surjection
        (_≃ᴱ_.from A≃⊤)
        (λ a → tt
             , (_≃ᴱ_.from A≃⊤ tt               ≡⟨⟩
                _≃ᴱ_.from A≃⊤ (_≃ᴱ_.to A≃⊤ a)  ≡⟨ _≃ᴱ_.left-inverse-of A≃⊤ _ ⟩∎
                a                              ∎))
        Contractibleᴱ-⊤
  }
  where
  Contractibleᴱ-⊤ = ECP.Contractible→Contractibleᴱ ⊤-contractible

-- There is an equivalence with erased proofs between Contractibleᴱ A
-- and A ≃ᴱ ⊤ (assuming extensionality).

Contractibleᴱ≃ᴱ≃ᴱ⊤ :
  {@0 A : Type a} →
  @0 Extensionality a a →
  Contractibleᴱ A ≃ᴱ (A ≃ᴱ ⊤)
Contractibleᴱ≃ᴱ≃ᴱ⊤ ext =
  let record { to = to; from = from } = Contractibleᴱ⇔≃ᴱ⊤ in
  ↔→≃ᴱ
    to
    from
    (λ _ → to≡to→≡ ext (refl _))
    (λ _ → ECP.Contractibleᴱ-propositional ext _ _)

-- If an inhabited type comes with an erased proof of
-- propositionality, then it is equivalent (with erased proofs) to the
-- unit type.

inhabited→Is-proposition→≃ᴱ⊤ :
  {@0 A : Type a} →
  A → @0 Is-proposition A → A ≃ᴱ ⊤
inhabited→Is-proposition→≃ᴱ⊤ x prop =
  let record { to = to } = Contractibleᴱ⇔≃ᴱ⊤ in
  to (ECP.inhabited→Is-proposition→Contractibleᴱ x prop)

-- Contractibleᴱ commutes with _×_ (up to _≃ᴱ_, assuming
-- extensionality).

Contractibleᴱ-commutes-with-× :
  {@0 A : Type a} {@0 B : Type b} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  Contractibleᴱ (A × B) ≃ᴱ (Contractibleᴱ A × Contractibleᴱ B)
Contractibleᴱ-commutes-with-× {A} {B} ext =
  [≃]→≃ᴱ ([proofs] lemma)
  where
  @0 lemma : _
  lemma =
    Contractibleᴱ (A × B)                ↝⟨ F.inverse ECP.Contractible≃Contractibleᴱ ⟩
    Contractible (A × B)                 ↝⟨ Contractible-commutes-with-× ext ⟩
    (Contractible A × Contractible B)    ↝⟨ ECP.Contractible≃Contractibleᴱ ×-cong
                                            ECP.Contractible≃Contractibleᴱ ⟩□
    (Contractibleᴱ A × Contractibleᴱ B)  □

------------------------------------------------------------------------
-- Groupoid laws and related properties

module Groupoid where

  -- In an erased context the groupoid laws hold for id and _∘_.
  --
  -- TODO: Is it possible to prove the first three results in a
  -- non-erased context?

  @0 left-identity :
    {A : Type a} {B : Type b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    (f : A ≃ᴱ B) → id ∘ f ≡ f
  left-identity ext _ = to≡to→≡ ext (refl _)

  @0 right-identity :
    {A : Type a} {B : Type b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    (f : A ≃ᴱ B) → f ∘ id ≡ f
  right-identity ext _ = to≡to→≡ ext (refl _)

  @0 associativity :
    {A : Type a} {D : Type d} →
    Extensionality (a ⊔ d) (a ⊔ d) →
    (f : C ≃ᴱ D) (g : B ≃ᴱ C) (h : A ≃ᴱ B) →
    f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
  associativity ext _ _ _ = to≡to→≡ ext (refl _)

  @0 left-inverse :
    {A : Type a} →
    Extensionality a a →
    (f : A ≃ᴱ B) → inverse f ∘ f ≡ id
  left-inverse ext f =
    to≡to→≡ ext $ apply-ext ext $
    _≃_.left-inverse-of (≃ᴱ→≃ f)

  @0 right-inverse :
    {B : Type b} →
    Extensionality b b →
    (f : A ≃ᴱ B) → f ∘ inverse f ≡ id
  right-inverse ext f =
    to≡to→≡ ext $ apply-ext ext $
    _≃_.right-inverse-of (≃ᴱ→≃ f)

-- Inverse is a logical equivalence.

inverse-logical-equivalence :
  {@0 A : Type a} {@0 B : Type b} →
  A ≃ᴱ B ⇔ B ≃ᴱ A
inverse-logical-equivalence = record
  { to   = inverse
  ; from = inverse
  }

-- Inverse is an equivalence with erased proofs (assuming
-- extensionality).

inverse-equivalence :
  {@0 A : Type a} {@0 B : Type b} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  (A ≃ᴱ B) ≃ᴱ (B ≃ᴱ A)
inverse-equivalence ext = ↔→≃ᴱ
  inverse
  inverse
  (λ _ → to≡to→≡ ext (refl _))
  (λ _ → to≡to→≡ ext (refl _))

------------------------------------------------------------------------
-- Some results that depend on univalence

-- A variant of ≃⇒≡.

@0 ≃ᴱ→≡ :
  {A B : Type a} →
  Univalence a →
  A ≃ᴱ B → A ≡ B
≃ᴱ→≡ univ = ≃⇒≡ univ ⊚ ≃ᴱ→≃

-- A variant of ≡≃≃.

@0 ≡≃≃ᴱ :
  {A B : Type a} →
  Univalence a →
  (A ≡ B) ≃ (A ≃ᴱ B)
≡≃≃ᴱ {A} {B} univ =
  Eq.with-other-function
    (A ≡ B   ↝⟨ ≡≃≃ univ ⟩
     A ≃ B   ↝⟨ ≃≃≃ᴱ ⟩□
     A ≃ᴱ B  □)
    (≡⇒↝ _)
    (elim₁ (λ eq → ≃→≃ᴱ (≡⇒≃ eq) ≡ ≡⇒↝ _ eq)
       (≃→≃ᴱ (≡⇒≃ (refl _))  ≡⟨ cong ≃→≃ᴱ ≡⇒≃-refl ⟩
        ≃→≃ᴱ Eq.id           ≡⟨⟩
        id                   ≡⟨ sym ≡⇒↝-refl ⟩∎
        ≡⇒↝ _ (refl _)       ∎))

@0 _ :
  {univ : Univalence a} →
  _≃_.from (≡≃≃ᴱ {A = A} {B = B} univ) ≡ ≃ᴱ→≡ univ
_ = refl _

-- A variant of ≃⇒≡-id.

@0 ≃ᴱ→≡-id :
  {A : Type a} →
  Extensionality a a →
  (univ : Univalence a) →
  ≃ᴱ→≡ univ id ≡ refl A
≃ᴱ→≡-id ext univ =
  ≃⇒≡ univ (≃ᴱ→≃ id)  ≡⟨ cong (≃⇒≡ univ) $ Eq.lift-equality ext (refl _) ⟩
  ≃⇒≡ univ Eq.id      ≡⟨ ≃⇒≡-id univ ⟩∎
  refl _              ∎

-- A variant of ≃⇒≡-inverse.

@0 ≃ᴱ→≡-inverse :
  Extensionality a a →
  (univ : Univalence a)
  (A≃B : A ≃ᴱ B) →
  ≃ᴱ→≡ univ (inverse A≃B) ≡ sym (≃ᴱ→≡ univ A≃B)
≃ᴱ→≡-inverse ext univ A≃B =
  ≃⇒≡ univ (≃ᴱ→≃ (inverse A≃B))     ≡⟨ cong (≃⇒≡ univ) $ Eq.lift-equality ext (refl _) ⟩
  ≃⇒≡ univ (Eq.inverse (≃ᴱ→≃ A≃B))  ≡⟨ ≃⇒≡-inverse univ ext _ ⟩∎
  sym (≃⇒≡ univ (≃ᴱ→≃ A≃B))         ∎

-- A variant of ≃⇒≡-∘.

@0 ≃ᴱ→≡-∘ :
  Extensionality a a →
  (univ : Univalence a)
  (A≃B : A ≃ᴱ B) (B≃C : B ≃ᴱ C) →
  ≃ᴱ→≡ univ (B≃C ∘ A≃B) ≡ trans (≃ᴱ→≡ univ A≃B) (≃ᴱ→≡ univ B≃C)
≃ᴱ→≡-∘ ext univ A≃B B≃C =
  ≃⇒≡ univ (≃ᴱ→≃ (B≃C ∘ A≃B))                        ≡⟨ cong (≃⇒≡ univ) $ Eq.lift-equality ext (refl _) ⟩
  ≃⇒≡ univ (≃ᴱ→≃ B≃C Eq.∘ ≃ᴱ→≃ A≃B)                  ≡⟨ ≃⇒≡-∘ univ ext _ _ ⟩
  trans (≃⇒≡ univ (≃ᴱ→≃ A≃B)) (≃⇒≡ univ (≃ᴱ→≃ B≃C))  ∎

-- Singletons expressed using equivalences with erased proofs instead
-- of equalities are equivalent (with erased proofs) to the unit type
-- (assuming extensionality and univalence).

singleton-with-≃ᴱ-≃ᴱ-⊤ :
  ∀ a {B : Type b} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  @0 Univalence (a ⊔ b) →
  (∃ λ (A : Type (a ⊔ b)) → A ≃ᴱ B) ≃ᴱ ⊤
singleton-with-≃ᴱ-≃ᴱ-⊤ {b} a {B} ext univ =
  [≃]→≃ᴱ ([proofs] lemma)
  where
  @0 lemma : (∃ λ (A : Type (a ⊔ b)) → A ≃ᴱ B) ≃ ⊤
  lemma =
    (∃ λ (A : Type (a ⊔ b)) → A ≃ᴱ B)  ↝⟨ (∃-cong λ _ → F.inverse ≃≃≃ᴱ) ⟩
    (∃ λ (A : Type (a ⊔ b)) → A ≃ B)   F.↔⟨ singleton-with-≃-↔-⊤ {a = a} ext univ ⟩□
    ⊤                                  □

other-singleton-with-≃ᴱ-≃ᴱ-⊤ :
  ∀ b {A : Type a} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  @0 Univalence (a ⊔ b) →
  (∃ λ (B : Type (a ⊔ b)) → A ≃ᴱ B) ≃ᴱ ⊤
other-singleton-with-≃ᴱ-≃ᴱ-⊤ b {A} ext univ =
  (∃ λ B → A ≃ᴱ B)  ≃ᴱ⟨ (∃-cong λ _ → inverse-equivalence ext) ⟩
  (∃ λ B → B ≃ᴱ A)  ≃ᴱ⟨ singleton-with-≃ᴱ-≃ᴱ-⊤ b ext univ ⟩□
  ⊤                 □

-- Variants of the two lemmas above.

singleton-with-Π-≃ᴱ-≃ᴱ-⊤ :
  {A : Type a} {Q : A → Type q} →
  @0 Extensionality a (lsuc q) →
  @0 Univalence q →
  (∃ λ (P : A → Type q) → ∀ x → P x ≃ᴱ Q x) ≃ᴱ ⊤
singleton-with-Π-≃ᴱ-≃ᴱ-⊤ {a} {q} {A} {Q} ext univ =
  [≃]→≃ᴱ ([proofs] lemma)
  where
  @0 ext′ : Extensionality a q
  ext′ = lower-extensionality lzero _ ext

  @0 lemma : (∃ λ (P : A → Type q) → ∀ x → P x ≃ᴱ Q x) ≃ ⊤
  lemma =
    (∃ λ (P : A → Type q) → ∀ x → P x ≃ᴱ Q x)  ↝⟨ (∃-cong λ _ → ∀-cong ext′ λ _ → F.inverse ≃≃≃ᴱ) ⟩
    (∃ λ (P : A → Type q) → ∀ x → P x ≃ Q x)   F.↔⟨ singleton-with-Π-≃-≃-⊤ ext univ ⟩□
    ⊤                                          □

other-singleton-with-Π-≃ᴱ-≃ᴱ-⊤ :
  {A : Type a} {P : A → Type p} →
  @0 Extensionality (a ⊔ p) (lsuc p) →
  @0 Univalence p →
  (∃ λ (Q : A → Type p) → ∀ x → P x ≃ᴱ Q x) ≃ᴱ ⊤
other-singleton-with-Π-≃ᴱ-≃ᴱ-⊤ {a} {p} {A} {P} ext univ =
  (∃ λ (Q : A → Type p) → ∀ x → P x ≃ᴱ Q x)  ≃ᴱ⟨ (∃-cong λ _ → ∀-cong-≃ᴱ ext₁ λ _ → inverse-equivalence ext₂) ⟩
  (∃ λ (Q : A → Type p) → ∀ x → Q x ≃ᴱ P x)  ≃ᴱ⟨ singleton-with-Π-≃ᴱ-≃ᴱ-⊤ ext₃ univ ⟩□
  ⊤                                          □
  where
  @0 ext₁ : Extensionality a p
  ext₁ = lower-extensionality p _ ext

  @0 ext₂ : Extensionality p p
  ext₂ = lower-extensionality a _ ext

  @0 ext₃ : Extensionality a (lsuc p)
  ext₃ = lower-extensionality p lzero ext

-- ∃ Contractibleᴱ is equivalent (with erased proofs) to the unit type
-- (assuming extensionality and univalence).

∃Contractibleᴱ≃ᴱ⊤ :
  @0 Extensionality a a →
  @0 Univalence a →
  (∃ λ (A : Type a) → Contractibleᴱ A) ≃ᴱ ⊤
∃Contractibleᴱ≃ᴱ⊤ ext univ =
  (∃ λ A → Contractibleᴱ A)  ≃ᴱ⟨ (∃-cong λ _ → Contractibleᴱ≃ᴱ≃ᴱ⊤ ext) ⟩
  (∃ λ A → A ≃ᴱ ⊤)           ≃ᴱ⟨ singleton-with-≃ᴱ-≃ᴱ-⊤ _ ext univ ⟩□
  ⊤                          □

------------------------------------------------------------------------
-- Some simplification lemmas

-- Two simplification lemmas for id.

right-inverse-of-id :
  _≃ᴱ_.right-inverse-of id x ≡ refl x
right-inverse-of-id = refl _

@0 left-inverse-of-id :
  _≃ᴱ_.left-inverse-of id x ≡ refl x
left-inverse-of-id {x} =
  left-inverse-of x               ≡⟨⟩
  left-inverse-of (P.id x)        ≡⟨ sym $ right-left-lemma x ⟩
  cong P.id (right-inverse-of x)  ≡⟨ sym $ cong-id _ ⟩
  right-inverse-of x              ≡⟨ right-inverse-of-id ⟩∎
  refl x                          ∎
  where
  open _≃ᴱ_ id

-- Two simplification lemmas for inverse.

@0 right-inverse-of∘inverse :
  (A≃B : A ≃ᴱ B) →
  _≃ᴱ_.right-inverse-of (inverse A≃B) x ≡
  _≃ᴱ_.left-inverse-of A≃B x
right-inverse-of∘inverse _ = refl _

@0 left-inverse-of∘inverse :
  (A≃B : A ≃ᴱ B) →
  _≃ᴱ_.left-inverse-of (inverse A≃B) x ≡
  _≃ᴱ_.right-inverse-of A≃B x
left-inverse-of∘inverse {A} {B} {x} A≃B =
  subst (λ x → _≃ᴱ_.left-inverse-of (inverse A≃B) x ≡
               right-inverse-of x)
        (right-inverse-of x)
        (_≃ᴱ_.left-inverse-of (inverse A≃B) (to (from x))        ≡⟨ sym $ _≃ᴱ_.right-left-lemma (inverse A≃B) (from x) ⟩
         cong to (_≃ᴱ_.right-inverse-of (inverse A≃B) (from x))  ≡⟨ cong (cong to) $ right-inverse-of∘inverse A≃B ⟩
         cong to (left-inverse-of (from x))                      ≡⟨ left-right-lemma (from x) ⟩∎
         right-inverse-of (to (from x))                          ∎)
  where
  open _≃ᴱ_ A≃B

-- Two simplification lemmas for subst.

to-subst :
  {eq : x ≡ y} {f : P x ≃ᴱ Q x} →
  _≃ᴱ_.to (subst (λ x → P x ≃ᴱ Q x) eq f) ≡
  subst (λ x → P x → Q x) eq (_≃ᴱ_.to f)
to-subst {P} {Q} {eq} {f} = elim¹
  (λ eq →
     _≃ᴱ_.to (subst (λ x → P x ≃ᴱ Q x) eq f) ≡
     subst (λ x → P x → Q x) eq (_≃ᴱ_.to f))
  (_≃ᴱ_.to (subst (λ x → P x ≃ᴱ Q x) (refl _) f)  ≡⟨ cong _≃ᴱ_.to $ subst-refl _ _ ⟩
   _≃ᴱ_.to f                                      ≡⟨ sym $ subst-refl _ _ ⟩∎
   subst (λ x → P x → Q x) (refl _) (_≃ᴱ_.to f)   ∎)
  eq

from-subst :
  {eq : x ≡ y} {f : P x ≃ᴱ Q x} →
  _≃ᴱ_.from (subst (λ x → P x ≃ᴱ Q x) eq f) ≡
  subst (λ x → Q x → P x) eq (_≃ᴱ_.from f)
from-subst {P} {Q} {eq} {f} = elim¹
  (λ eq →
     _≃ᴱ_.from (subst (λ x → P x ≃ᴱ Q x) eq f) ≡
     subst (λ x → Q x → P x) eq (_≃ᴱ_.from f))
  (_≃ᴱ_.from (subst (λ x → P x ≃ᴱ Q x) (refl _) f)  ≡⟨ cong _≃ᴱ_.from $ subst-refl _ _ ⟩
   _≃ᴱ_.from f                                      ≡⟨ sym $ subst-refl _ _ ⟩∎
   subst (λ x → Q x → P x) (refl _) (_≃ᴱ_.from f)   ∎)
  eq

------------------------------------------------------------------------
-- The two-out-of-three properties

-- If f and g are equivalences with erased proofs, then g ⊚ f is also
-- an equivalence with erased proofs.

12→3 :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c}
  {@0 f : A → B} {@0 g : B → C} →
  Is-equivalenceᴱ f → Is-equivalenceᴱ g → Is-equivalenceᴱ (g ⊚ f)
12→3 p q =
    proj₁₀ p ⊚ proj₁₀ q
  , [ _≃ᴱ_.is-equivalence (⟨ _ , q ⟩₀ ∘ ⟨ _ , p ⟩₀) .proj₂ .erased ]

-- If g and g ⊚ f are equivalences with erased proofs, then f is
-- also an equivalence with erased proofs.

23→1 :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c}
  {@0 f : A → B} {g : B → C} →
  @0 Is-equivalenceᴱ g → Is-equivalenceᴱ (g ⊚ f) → Is-equivalenceᴱ f
23→1 {f} {g} q r =
  let record { to = to } =
        Is-equivalenceᴱ-cong-⇔ λ x →
          _≃ᴱ_.from ⟨ g , q ⟩ (g (f x))  ≡⟨ _≃ᴱ_.left-inverse-of ⟨ g , q ⟩ (f x) ⟩∎
          f x                            ∎
  in
  to ( proj₁₀ r ⊚ g
     , [ _≃ᴱ_.is-equivalence (inverse ⟨ _ , q ⟩₀ ∘ ⟨ _ , r ⟩₀)
           .proj₂ .erased
       ]
     )

-- If g ⊚ f and f are equivalences with erased proofs, then g is
-- also an equivalence with erased proofs.

31→2 :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c}
  {f : A → B} {@0 g : B → C} →
  Is-equivalenceᴱ (g ⊚ f) → @0 Is-equivalenceᴱ f → Is-equivalenceᴱ g
31→2 {f} {g} r p =
  let record { to = to } =
        Is-equivalenceᴱ-cong-⇔ λ x →
          g (f (_≃ᴱ_.from ⟨ f , p ⟩ x))  ≡⟨ cong g (_≃ᴱ_.right-inverse-of ⟨ f , p ⟩ x) ⟩∎
          g x                            ∎
  in
  to ( f ⊚ proj₁₀ r
     , [ _≃ᴱ_.is-equivalence (⟨ _ , r ⟩₀ ∘ inverse ⟨ _ , p ⟩₀)
           .proj₂ .erased
       ]
     )

-- Some consequences of the two-out-of-three properties.

Is-equivalenceᴱ⇔Is-equivalenceᴱ-∘ˡ :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c}
  {f : B → C} {@0 g : A → B} →
  Is-equivalenceᴱ f →
  Is-equivalenceᴱ g ⇔ Is-equivalenceᴱ (f ⊚ g)
Is-equivalenceᴱ⇔Is-equivalenceᴱ-∘ˡ f-eq = record
  { to   = flip 12→3 f-eq
  ; from = 23→1 f-eq
  }

Is-equivalenceᴱ⇔Is-equivalenceᴱ-∘ʳ :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c}
  {@0 f : B → C} {g : A → B} →
  Is-equivalenceᴱ g →
  Is-equivalenceᴱ f ⇔ Is-equivalenceᴱ (f ⊚ g)
Is-equivalenceᴱ⇔Is-equivalenceᴱ-∘ʳ g-eq = record
  { to   = 12→3 g-eq
  ; from = λ f∘g-eq → 31→2 f∘g-eq g-eq
  }

Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-∘ˡ :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c}
  {f : B → C} {@0 g : A → B} →
  @0 Extensionality (a ⊔ b ⊔ c) (a ⊔ b ⊔ c) →
  Is-equivalenceᴱ f →
  Is-equivalenceᴱ g ≃ᴱ Is-equivalenceᴱ (f ⊚ g)
Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-∘ˡ {b} {c} ext f-eq = ⇔→≃ᴱ
  (Is-equivalenceᴱ-propositional (lower-extensionality c c ext) _)
  (Is-equivalenceᴱ-propositional (lower-extensionality b b ext) _)
  (flip 12→3 f-eq)
  (23→1 f-eq)

Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-∘ʳ :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c}
  {@0 f : B → C} {g : A → B} →
  @0 Extensionality (a ⊔ b ⊔ c) (a ⊔ b ⊔ c) →
  Is-equivalenceᴱ g →
  Is-equivalenceᴱ f ≃ᴱ Is-equivalenceᴱ (f ⊚ g)
Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-∘ʳ {a} {b} ext g-eq = ⇔→≃ᴱ
  (Is-equivalenceᴱ-propositional (lower-extensionality a a ext) _)
  (Is-equivalenceᴱ-propositional (lower-extensionality b b ext) _)
  (12→3 g-eq)
  (λ f∘g-eq → 31→2 f∘g-eq g-eq)

------------------------------------------------------------------------
-- Results that depend on an axiomatisation of []-cong (for a single
-- universe level)

module []-cong₁ (ax : []-cong-axiomatisation ℓ) where

  open Erased.[]-cong₁ ax

  ----------------------------------------------------------------------
  -- More preservation lemmas

  -- Equivalences with erased proofs are in some cases preserved by Σ
  -- (assuming extensionality). Note the type of Q.

  Σ-cong-≃ᴱ-Erased :
    {@0 A : Type a} {@0 B : Type ℓ}
    {@0 P : A → Type p} {Q : @0 B → Type q}
    (A≃B : A ≃ᴱ B) →
    (∀ x → P x ≃ᴱ Q (_≃ᴱ_.to A≃B x)) →
    Σ A P ≃ᴱ Σ B (λ x → Q x)
  Σ-cong-≃ᴱ-Erased {A} {B} {P} {Q} A≃B P≃Q =
    [≃]→≃ᴱ ([proofs] ΣAP≃ΣBQ)
    where
    @0 ΣAP≃ΣBQ : Σ A P ≃ Σ B (λ x → Q x)
    ΣAP≃ΣBQ =
      Eq.with-other-inverse
        (Σ-cong (≃ᴱ→≃ A≃B) (λ x → ≃ᴱ→≃ (P≃Q x)))
        (λ (x , y) →
             _≃ᴱ_.from A≃B x
           , _≃ᴱ_.from (P≃Q (_≃ᴱ_.from A≃B x))
               (substᴱ Q (sym (_≃ᴱ_.right-inverse-of A≃B x)) y))
        (λ (x , y) →
           cong (λ y → _ , _≃ᴱ_.from (P≃Q (_≃ᴱ_.from A≃B x)) y) (
             subst (λ x → Q x) (sym (_≃ᴱ_.right-inverse-of A≃B x)) y  ≡⟨ sym substᴱ≡subst ⟩∎
             substᴱ Q (sym (_≃ᴱ_.right-inverse-of A≃B x)) y           ∎))

  -- A variant of Σ-cong-≃ᴱ-Erased.

  Σ-cong-contra-≃ᴱ-Erased :
    {@0 A : Type ℓ} {@0 B : Type b}
    {P : @0 A → Type p} {@0 Q : B → Type q}
    (B≃A : B ≃ᴱ A) →
    (∀ x → P (_≃ᴱ_.to B≃A x) ≃ᴱ Q x) →
    Σ A (λ x → P x) ≃ᴱ Σ B Q
  Σ-cong-contra-≃ᴱ-Erased {P} {Q} B≃A P≃Q = ↔→≃ᴱ
    (λ (x , y) →
         _≃ᴱ_.from B≃A x
       , _≃ᴱ_.to (P≃Q (_≃ᴱ_.from B≃A x))
            (substᴱ P (sym (_≃ᴱ_.right-inverse-of B≃A x)) y))
    (λ (x , y) → _≃ᴱ_.to B≃A x , _≃ᴱ_.from (P≃Q x) y)
    (λ (x , y) → Σ-≡,≡→≡
       (_≃ᴱ_.left-inverse-of B≃A x)
       (subst Q (_≃ᴱ_.left-inverse-of B≃A x)
          (_≃ᴱ_.to (P≃Q _)
             (substᴱ P (sym (_≃ᴱ_.right-inverse-of B≃A _))
                (_≃ᴱ_.from (P≃Q x) y)))                                  ≡⟨ cong (λ eq → subst Q (_≃ᴱ_.left-inverse-of B≃A x) (_≃ᴱ_.to (P≃Q _) eq))
                                                                            substᴱ≡subst ⟩
        subst Q (_≃ᴱ_.left-inverse-of B≃A x)
          (_≃ᴱ_.to (P≃Q _)
             (subst (λ x → P x) (sym (_≃ᴱ_.right-inverse-of B≃A _))
                (_≃ᴱ_.from (P≃Q x) y)))                                  ≡⟨ cong (λ eq → subst Q (_≃ᴱ_.left-inverse-of B≃A x)
                                                                                           (_≃ᴱ_.to (P≃Q _)
                                                                                              (subst (λ x → P x) (sym eq) _))) $ sym $
                                                                            _≃ᴱ_.left-right-lemma B≃A _ ⟩
        subst Q (_≃ᴱ_.left-inverse-of B≃A x)
          (_≃ᴱ_.to (P≃Q (_≃ᴱ_.from B≃A (_≃ᴱ_.to B≃A x)))
             (subst (λ x → P x)
                (sym (cong (_≃ᴱ_.to B≃A) (_≃ᴱ_.left-inverse-of B≃A _)))
                (_≃ᴱ_.from (P≃Q x) y)))                                  ≡⟨ elim₁
                                                                              (λ eq → subst Q eq
                                                                                        (_≃ᴱ_.to (P≃Q _)
                                                                                           (subst (λ x → P x)
                                                                                              (sym (cong (_≃ᴱ_.to B≃A) eq))
                                                                                              (_≃ᴱ_.from (P≃Q x) y))) ≡
                                                                                      y)
                                                                              (
            subst Q (refl _)
              (_≃ᴱ_.to (P≃Q x)
                 (subst (λ x → P x)
                    (sym (cong (_≃ᴱ_.to B≃A) (refl _)))
                    (_≃ᴱ_.from (P≃Q x) y)))                                    ≡⟨ subst-refl _ _ ⟩

            _≃ᴱ_.to (P≃Q x)
              (subst (λ x → P x)
                 (sym (cong (_≃ᴱ_.to B≃A) (refl _)))
                 (_≃ᴱ_.from (P≃Q x) y))                                        ≡⟨ cong (λ eq → _≃ᴱ_.to (P≃Q _) (subst (λ x → P x) (sym eq) _)) $
                                                                                  cong-refl _ ⟩
            _≃ᴱ_.to (P≃Q x)
              (subst (λ x → P x)
                 (sym (refl _)) (_≃ᴱ_.from (P≃Q x) y))                         ≡⟨ cong (λ eq → _≃ᴱ_.to (P≃Q _) (subst (λ x → P x) eq _))
                                                                                  sym-refl ⟩
            _≃ᴱ_.to (P≃Q x)
              (subst (λ x → P x)
                 (refl _) (_≃ᴱ_.from (P≃Q x) y))                               ≡⟨ cong (λ eq → _≃ᴱ_.to (P≃Q _) eq) $
                                                                                  subst-refl _ _ ⟩

            _≃ᴱ_.to (P≃Q x) (_≃ᴱ_.from (P≃Q x) y)                              ≡⟨ _≃ᴱ_.right-inverse-of (P≃Q x) _ ⟩∎

            y                                                                  ∎)
                                                                              (_≃ᴱ_.left-inverse-of B≃A x) ⟩∎
        y                                                                ∎))
    (λ (x , y) → Σ-≡,≡→≡
       (_≃ᴱ_.right-inverse-of B≃A x)
       (subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x)
          (_≃ᴱ_.from (P≃Q _)
             (_≃ᴱ_.to (P≃Q _)
                (substᴱ P (sym (_≃ᴱ_.right-inverse-of B≃A _)) y)))   ≡⟨ cong (subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x)) $
                                                                        _≃ᴱ_.left-inverse-of (P≃Q _) _ ⟩
        subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x)
          (substᴱ P (sym (_≃ᴱ_.right-inverse-of B≃A _)) y)           ≡⟨ cong (subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x))
                                                                        substᴱ≡subst ⟩
        subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x)
          (subst (λ x → P x) (sym (_≃ᴱ_.right-inverse-of B≃A _)) y)  ≡⟨ subst-subst-sym _ _ _ ⟩∎

        y                                                            ∎))

  -- Equivalences with erased proofs are in some cases preserved by Π
  -- (assuming extensionality). Note the type of Q.

  Π-cong-≃ᴱ-Erased :
    {@0 A : Type a} {@0 B : Type ℓ}
    {@0 P : A → Type p} {Q : @0 B → Type q} →
    @0 Extensionality (a ⊔ ℓ) (p ⊔ q) →
    (A≃B : A ≃ᴱ B) →
    (∀ x → P x ≃ᴱ Q (_≃ᴱ_.to A≃B x)) →
    ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
  Π-cong-≃ᴱ-Erased {a} {p} {A} {B} {P} {Q} ext A≃B P≃Q =
    [≃]→≃ᴱ ([proofs] ΠAP≃ΠBQ)
    where
    @0 ΠAP≃ΠBQ : ((x : A) → P x) ≃ ((x : B) → Q x)
    ΠAP≃ΠBQ =
      Eq.with-other-function
        (Π-cong ext (≃ᴱ→≃ A≃B) (λ x → ≃ᴱ→≃ (P≃Q x)))
        (λ f x → substᴱ Q
                   (_≃ᴱ_.right-inverse-of A≃B x)
                   (_≃ᴱ_.to (P≃Q (_≃ᴱ_.from A≃B x))
                       (f (_≃ᴱ_.from A≃B x))))
        (λ f → apply-ext (lower-extensionality a p ext) λ x →
           subst (λ x → Q x) (_≃ᴱ_.right-inverse-of A≃B x)
              (_≃ᴱ_.to (P≃Q (_≃ᴱ_.from A≃B x)) (f (_≃ᴱ_.from A≃B x)))  ≡⟨ sym substᴱ≡subst ⟩∎

           substᴱ Q
             (_≃ᴱ_.right-inverse-of A≃B x)
             (_≃ᴱ_.to (P≃Q (_≃ᴱ_.from A≃B x)) (f (_≃ᴱ_.from A≃B x)))   ∎)

  -- A variant of Π-cong-≃ᴱ-Erased.

  Π-cong-contra-≃ᴱ-Erased :
    {@0 A : Type ℓ} {@0 B : Type b}
    {P : @0 A → Type p} {@0 Q : B → Type q} →
    @0 Extensionality (b ⊔ ℓ) (p ⊔ q) →
    (B≃A : B ≃ᴱ A) →
    (∀ x → P (_≃ᴱ_.to B≃A x) ≃ᴱ Q x) →
    ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
  Π-cong-contra-≃ᴱ-Erased {b} {q} {A} {B} {P} {Q} ext B≃A P≃Q =
    [≃]→≃ᴱ ([proofs] ΠAP≃ΠBQ)
    where
    @0 ΠAP≃ΠBQ : ((x : A) → P x) ≃ ((x : B) → Q x)
    ΠAP≃ΠBQ =
      Eq.with-other-inverse
        (Π-cong-contra ext (≃ᴱ→≃ B≃A) (λ x → ≃ᴱ→≃ (P≃Q x)))
        (λ f x → substᴱ P
                   (_≃ᴱ_.right-inverse-of B≃A x)
                   (_≃ᴱ_.from (P≃Q (_≃ᴱ_.from B≃A x))
                      (f (_≃ᴱ_.from B≃A x))))
        (λ f → apply-ext (lower-extensionality b q ext) λ x →
           subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x)
              (_≃ᴱ_.from (P≃Q (_≃ᴱ_.from B≃A x)) (f (_≃ᴱ_.from B≃A x)))  ≡⟨ sym substᴱ≡subst ⟩∎

           substᴱ P
             (_≃ᴱ_.right-inverse-of B≃A x)
             (_≃ᴱ_.from (P≃Q (_≃ᴱ_.from B≃A x)) (f (_≃ᴱ_.from B≃A x)))   ∎)

  -- Contractibleᴱ preserves equivalences with erased proofs (assuming
  -- extensionality).

  Contractibleᴱ-cong-≃ᴱ :
    {A : Type a} {B : Type ℓ} →
    @0 Extensionality (a ⊔ ℓ) (a ⊔ ℓ) →
    A ≃ᴱ B → Contractibleᴱ A ≃ᴱ Contractibleᴱ B
  Contractibleᴱ-cong-≃ᴱ {A} {B} ext A≃ᴱB =
    (∃ λ (x : A) → Erased ((y : A) → x ≡ y))  ↝⟨ (Σ-cong-≃ᴱ-Erased A≃ᴱB λ _ →
                                                  Erased-cong-≃ᴱ
                                                    (let A≃B = ≃ᴱ→≃ A≃ᴱB in
                                                     Π-cong [ ext ] A≃B λ _ →
                                                     from-equivalence $ F.inverse $ Eq.≃-≡ A≃B)) ⟩□
    (∃ λ (x : B) → Erased ((y : B) → x ≡ y))  □

  ----------------------------------------------------------------------
  -- Variants of Σ-cong, Σ-cong-contra, Π-cong and Π-cong-contra

  -- A preservation lemma for Σ. Note the type of Q.
  --
  -- For this lemma it would suffice if ΠΣ-cong-domain implication
  -- were implication.

  Σ-cong-Erased :
    {A : Type a} {B : Type ℓ} {P : A → Type p} {Q : @0 B → Type q} →
    (A↝B : A ↝[ ΠΣ-cong-domain k ] B) →
    (∀ x → P x ↝[ k ] Q (to-implication A↝B x)) →
    Σ A P ↝[ k ] Σ B (λ x → Q x)
  Σ-cong-Erased {k = implication} A↠B P→Q =
    Σ-map (_↠_.to A↠B) (P→Q _)
  Σ-cong-Erased {k = logical-equivalence} =
    Surjection.Σ-cong-⇔
  Σ-cong-Erased {k = equivalenceᴱ} =
    Σ-cong-≃ᴱ-Erased
  Σ-cong-Erased {k = injection}   = Σ-cong
  Σ-cong-Erased {k = embedding}   = Σ-cong
  Σ-cong-Erased {k = surjection}  = Σ-cong
  Σ-cong-Erased {k = bijection}   = Σ-cong
  Σ-cong-Erased {k = equivalence} = Σ-cong

  -- Another preservation lemma for Σ. Note the type of P.

  Σ-cong-contra-Erased :
    {A : Type ℓ} {B : Type b} {P : @0 A → Type p} {Q : B → Type q} →
    (B↝A : B ↝[ ΠΣ-cong-domain k ] A) →
    (∀ x → P (to-implication B↝A x) ↝[ k ] Q x) →
    Σ A (λ x → P x) ↝[ k ] Σ B Q
  Σ-cong-contra-Erased {k = implication} =
    Σ-cong-contra-→
  Σ-cong-contra-Erased {k = logical-equivalence} =
    Σ-cong-contra-⇔
  Σ-cong-contra-Erased {k = equivalenceᴱ} =
    Σ-cong-contra-≃ᴱ-Erased
  Σ-cong-contra-Erased {k = injection}   = Σ-cong-contra
  Σ-cong-contra-Erased {k = embedding}   = Σ-cong-contra
  Σ-cong-contra-Erased {k = surjection}  = Σ-cong-contra
  Σ-cong-contra-Erased {k = bijection}   = Σ-cong-contra
  Σ-cong-contra-Erased {k = equivalence} = Σ-cong-contra

  -- A variant of Σ-cong-Erased that is formulated using
  -- _↝[_∣_]-ΠΣ-cong_.

  Σ-cong-Erased′ :
    {A : Type a} {B : Type ℓ} {P : A → Type p} {Q : @0 B → Type q} →
    Extensionality? k c d →
    (A↝B : A ↝[ c ∣ d ]-ΠΣ-cong B) →
    (∀ x → P x ↝[ k ] Q (A↝B .proj₁ x)) →
    Σ A P ↝[ k ] Σ B (λ x → Q x)
  Σ-cong-Erased′ {k = implication} ext A↝B =
    Σ-cong-Erased (↝-ΠΣ-cong→↝ {k = implication} A↝B ext)
  Σ-cong-Erased′ {k = logical-equivalence} ext A↝B =
    Σ-cong-Erased (↝-ΠΣ-cong→↝ {k = logical-equivalence} A↝B ext)
  Σ-cong-Erased′ {k = injection} ext A↝B =
    Σ-cong-Erased (↝-ΠΣ-cong→↝ {k = injection} A↝B ext)
  Σ-cong-Erased′ {k = embedding} ext A↝B =
    Σ-cong-Erased (↝-ΠΣ-cong→↝ {k = embedding} A↝B ext)
  Σ-cong-Erased′ {k = surjection} ext A↝B =
    Σ-cong-Erased (↝-ΠΣ-cong→↝ {k = surjection} A↝B ext)
  Σ-cong-Erased′ {k = bijection} ext A↝B =
    Σ-cong-Erased (↝-ΠΣ-cong→↝ {k = bijection} A↝B ext)
  Σ-cong-Erased′ {k = equivalence} ext A↝B =
    Σ-cong-Erased (↝-ΠΣ-cong→↝ {k = equivalence} A↝B ext)
  Σ-cong-Erased′ {k = equivalenceᴱ} ext A↝B =
    Σ-cong-Erased (↝-ΠΣ-cong→↝ {k = equivalenceᴱ} A↝B ext)

  -- A variant of Σ-cong-contra-Erased that is formulated using
  -- _↝[_∣_]-ΠΣ-cong_.

  Σ-cong-contra-Erased′ :
    {A : Type ℓ} {B : Type b} {P : @0 A → Type p} {Q : B → Type q} →
    Extensionality? k c d →
    (B↝A : B ↝[ c ∣ d ]-ΠΣ-cong A) →
    (∀ x → P (B↝A .proj₁ x) ↝[ k ] Q x) →
    Σ A (λ x → P x) ↝[ k ] Σ B Q
  Σ-cong-contra-Erased′ {k = implication} ext B↝A =
    Σ-cong-contra-Erased (↝-ΠΣ-cong→↝ {k = implication} B↝A ext)
  Σ-cong-contra-Erased′ {k = logical-equivalence} ext B↝A =
    Σ-cong-contra-Erased (↝-ΠΣ-cong→↝ {k = logical-equivalence} B↝A ext)
  Σ-cong-contra-Erased′ {k = injection} ext B↝A =
    Σ-cong-contra-Erased (↝-ΠΣ-cong→↝ {k = injection} B↝A ext)
  Σ-cong-contra-Erased′ {k = embedding} ext B↝A =
    Σ-cong-contra-Erased (↝-ΠΣ-cong→↝ {k = embedding} B↝A ext)
  Σ-cong-contra-Erased′ {k = surjection} ext B↝A =
    Σ-cong-contra-Erased (↝-ΠΣ-cong→↝ {k = surjection} B↝A ext)
  Σ-cong-contra-Erased′ {k = bijection} ext B↝A =
    Σ-cong-contra-Erased (↝-ΠΣ-cong→↝ {k = bijection} B↝A ext)
  Σ-cong-contra-Erased′ {k = equivalence} ext B↝A =
    Σ-cong-contra-Erased (↝-ΠΣ-cong→↝ {k = equivalence} B↝A ext)
  Σ-cong-contra-Erased′ {k = equivalenceᴱ} ext B↝A =
    Σ-cong-contra-Erased (↝-ΠΣ-cong→↝ {k = equivalenceᴱ} B↝A ext)

  -- A "computation rule" for Σ-cong-Erased′.

  to-implication-Σ-cong-Erased′ :
    ∀ {A : Type a} {B : Type ℓ} {P : A → Type p} {Q : @0 B → Type q}
      {A↝B : A ↝[ c ∣ d ]-ΠΣ-cong B}
      {P↝Q : ∀ x → P x ↝[ k ] Q (A↝B .proj₁ x)} {x} →
    (ext : Extensionality? k c d) →
    to-implication (Σ-cong-Erased′ {Q = Q} ext A↝B P↝Q) x ≡
    Σ-map (A↝B .proj₁) (to-implication (P↝Q _)) x
  to-implication-Σ-cong-Erased′ {k} _ with k
  … | implication         = refl _
  … | logical-equivalence = refl _
  … | injection           = refl _
  … | embedding           = refl _
  … | surjection          = refl _
  … | bijection           = refl _
  … | equivalence         = refl _
  … | equivalenceᴱ        = refl _

  -- A "computation rule" for Σ-cong-contra-Erased′.

  to-implication-Σ-cong-contra-Erased′ :
    ∀ {A : Type ℓ} {B : Type b} {P : @0 A → Type p} {Q : B → Type q}
      {B↝A : B ↝[ c ∣ d ]-ΠΣ-cong A}
      {P↝Q : ∀ x → P (B↝A .proj₁ x) ↝[ k ] Q x} {x} →
    (ext : Extensionality? k c d) →
    let (from , [ right-inverse-of ]) =
          ↝-ΠΣ-cong-right-inverse B↝A ext in
    to-implication (Σ-cong-contra-Erased′ {P = P} ext B↝A P↝Q) x ≡
    Σ-map from
      (to-implication (P↝Q _) ⊚ substᴱ P (sym (right-inverse-of _)))
      x
  to-implication-Σ-cong-contra-Erased′
    {k = implication} {P} {B↝A} {P↝Q} {x = x , y} _ =
      _↠_.from B↝A′ x
    , P↝Q (_↠_.from B↝A′ x)
        (subst (λ x → P x) (sym (_↠_.right-inverse-of B↝A′ x)) y)  ≡⟨ cong ((_ ,_) ⊚ P↝Q _) $ sym $ substᴱ≡subst ⟩∎

      _↠_.from B↝A′ x
    , P↝Q (_↠_.from B↝A′ x)
        (substᴱ P (sym (_↠_.right-inverse-of B↝A′ x)) y)           ∎
    where
    B↝A′ = ↝-ΠΣ-cong→↝ {k = implication} B↝A _
  to-implication-Σ-cong-contra-Erased′
    {k = logical-equivalence} {P↝Q} _ =
    cong ((_ ,_) ⊚ _⇔_.to (P↝Q _)) $ sym $ substᴱ≡subst
  to-implication-Σ-cong-contra-Erased′
    {k = injection} {P} {B↝A} {P↝Q} {x = x , y} _ =
      _≃_.from B↝A′ x
    , _↣_.to (P↝Q (_≃_.from B↝A′ x))
        (_↣_.to
           (≡⇒↝ injection
              (cong {x = _≃_.to B↝A′}
                 (λ f → P (f (_≃_.from B↝A′ x))) (sym (refl _))))
           (_↣_.to
              (≡⇒↝ injection
                 (cong (λ x → P x) (sym (_≃_.right-inverse-of B↝A′ _))))
              y))                                                         ≡⟨ cong ((_ ,_) ⊚ _↣_.to (P↝Q _) ⊚ flip _↣_.to _) $
                                                                             trans
                                                                               (cong (≡⇒↝ _) $
                                                                                trans (cong (cong _) sym-refl) $
                                                                                cong-refl _)
                                                                             ≡⇒↝-refl ⟩
      _≃_.from B↝A′ x
    , _↣_.to (P↝Q (_≃_.from B↝A′ x))
        (_↣_.to
           (≡⇒↝ injection
              (cong (λ x → P x) (sym (_≃_.right-inverse-of B↝A′ _))))
           y)                                                             ≡⟨ cong ((_ ,_) ⊚ _↣_.to (P↝Q _)) $ sym $
                                                                             subst-in-terms-of-≡⇒↝ injection _ _ _ ⟩
      _≃_.from B↝A′ x
    , _↣_.to (P↝Q (_≃_.from B↝A′ x))
        (subst (λ x → P x) (sym (_≃_.right-inverse-of B↝A′ x)) y)         ≡⟨ cong ((_ ,_) ⊚ _↣_.to (P↝Q _)) $ sym
                                                                             substᴱ≡subst ⟩∎
      _≃_.from B↝A′ x
    , _↣_.to (P↝Q (_≃_.from B↝A′ x))
        (substᴱ P (sym (_≃_.right-inverse-of B↝A′ x)) y)                  ∎
    where
    B↝A′ = ↝-ΠΣ-cong→↝ {k = injection} B↝A _
  to-implication-Σ-cong-contra-Erased′ {k = embedding} {P↝Q} _ =
    trans
      (cong ((_ ,_) ⊚ Embedding.to (P↝Q _) ⊚ flip Embedding.to _) $
       trans
         (cong (≡⇒↝ _) $
          trans (cong (cong _) sym-refl) $
          cong-refl _) $
       ≡⇒↝-refl)
      (trans
         (cong ((_ ,_) ⊚ Embedding.to (P↝Q _)) $ sym $
          subst-in-terms-of-≡⇒↝ embedding _ _ _)
         (cong ((_ ,_) ⊚ Embedding.to (P↝Q _)) $ sym
          substᴱ≡subst))
  to-implication-Σ-cong-contra-Erased′ {k = surjection} {P↝Q} _ =
    trans
      (cong ((_ ,_) ⊚ _↠_.to (P↝Q _) ⊚ flip _↠_.to _) $
       trans
         (cong (≡⇒↝ _) $
          trans (cong (cong _) sym-refl) $
          cong-refl _) $
       ≡⇒↝-refl)
      (trans
         (cong ((_ ,_) ⊚ _↠_.to (P↝Q _)) $ sym $
          subst-in-terms-of-≡⇒↝ surjection _ _ _)
         (cong ((_ ,_) ⊚ _↠_.to (P↝Q _)) $ sym
          substᴱ≡subst))
  to-implication-Σ-cong-contra-Erased′ {k = bijection} {P↝Q} _ =
    cong ((_ ,_) ⊚ _↔_.to (P↝Q _)) $ sym $ substᴱ≡subst
  to-implication-Σ-cong-contra-Erased′ {k = equivalence} {P↝Q} _ =
    cong ((_ ,_) ⊚ _≃_.to (P↝Q _)) $ sym $ substᴱ≡subst
  to-implication-Σ-cong-contra-Erased′ {k = equivalenceᴱ} _ =
    refl _

  -- A preservation lemma for Π. Note the type of Q.

  Π-cong-Erased :
    {A : Type a} {B : Type ℓ} {P : A → Type p} {Q : @0 B → Type q} →
    Extensionality? k (a ⊔ ℓ) (p ⊔ q) →
    (A↝B : A ↝[ ΠΣ-cong-domain k ] B) →
    (∀ x → P x ↝[ k ] Q (to-implication A↝B x)) →
    ((x : A) → P x) ↝[ k ] ((x : B) → Q x)
  Π-cong-Erased {k = implication} _ =
    Π-cong-→
  Π-cong-Erased {k = logical-equivalence} _ =
    Π-cong-⇔
  Π-cong-Erased {k = equivalenceᴱ} [ ext ] =
    Π-cong-≃ᴱ-Erased ext
  Π-cong-Erased {k = injection}   ext = Π-cong ext
  Π-cong-Erased {k = embedding}   ext = Π-cong ext
  Π-cong-Erased {k = surjection}  ext = Π-cong ext
  Π-cong-Erased {k = bijection}   ext = Π-cong ext
  Π-cong-Erased {k = equivalence} ext = Π-cong ext

  -- Another preservation lemma for Π. Note the type of P.

  Π-cong-contra-Erased :
    {A : Type ℓ} {B : Type b} {P : @0 A → Type p} {Q : B → Type q} →
    Extensionality? k (b ⊔ ℓ) (p ⊔ q) →
    (B↝A : B ↝[ ΠΣ-cong-domain k ] A) →
    (∀ x → P (to-implication B↝A x) ↝[ k ] Q x) →
    ((x : A) → P x) ↝[ k ] ((x : B) → Q x)
  Π-cong-contra-Erased {k = implication} _ B↠A =
    Π-cong-contra-→ (_↠_.to B↠A)
  Π-cong-contra-Erased {k = logical-equivalence} _ =
    Π-cong-contra-⇔
  Π-cong-contra-Erased {k = equivalenceᴱ} [ ext ] =
    Π-cong-contra-≃ᴱ-Erased ext
  Π-cong-contra-Erased {k = injection}   ext = Π-cong-contra ext
  Π-cong-contra-Erased {k = embedding}   ext = Π-cong-contra ext
  Π-cong-contra-Erased {k = surjection}  ext = Π-cong-contra ext
  Π-cong-contra-Erased {k = bijection}   ext = Π-cong-contra ext
  Π-cong-contra-Erased {k = equivalence} ext = Π-cong-contra ext

  -- A variant of Π-cong-Erased that is formulated using
  -- _↝[_∣_]-ΠΣ-cong_.

  Π-cong-Erased′ :
    {A : Type a} {B : Type ℓ} {P : A → Type p} {Q : @0 B → Type q} →
    Extensionality? k (a ⊔ c ⊔ ℓ) (d ⊔ p ⊔ q) →
    (A↝B : A ↝[ c ∣ d ]-ΠΣ-cong B) →
    (∀ x → P x ↝[ k ] Q (A↝B .proj₁ x)) →
    ((x : A) → P x) ↝[ k ] ((x : B) → Q x)
  Π-cong-Erased′ {a} {p} {q} {c} {d} {A} {B} {P} {Q} ext A↝B =
    lemma _
      (lower-extensionality? _ c d ext)
      (lower-extensionality? _ (a ⊔ ℓ) (p ⊔ q) ext)
    where
    lemma :
      ∀ k →
      Extensionality? k (a ⊔ ℓ) (p ⊔ q) →
      Extensionality? k c d →
      (∀ x → P x ↝[ k ] Q (A↝B .proj₁ x)) →
      ((x : A) → P x) ↝[ k ] ((x : B) → Q x)
    lemma implication ext₁ ext₂ =
      Π-cong-Erased ext₁ (↝-ΠΣ-cong→↝ {k = implication} A↝B ext₂)
    lemma logical-equivalence ext₁ ext₂ =
      Π-cong-Erased ext₁
        (↝-ΠΣ-cong→↝ {k = logical-equivalence} A↝B ext₂)
    lemma injection ext₁ ext₂ =
      Π-cong-Erased ext₁ (↝-ΠΣ-cong→↝ {k = injection} A↝B ext₂)
    lemma embedding ext₁ ext₂ =
      Π-cong-Erased ext₁ (↝-ΠΣ-cong→↝ {k = embedding} A↝B ext₂)
    lemma surjection ext₁ ext₂ =
      Π-cong-Erased ext₁ (↝-ΠΣ-cong→↝ {k = surjection} A↝B ext₂)
    lemma bijection ext₁ ext₂ =
      Π-cong-Erased ext₁ (↝-ΠΣ-cong→↝ {k = bijection} A↝B ext₂)
    lemma equivalence ext₁ ext₂ =
      Π-cong-Erased ext₁ (↝-ΠΣ-cong→↝ {k = equivalence} A↝B ext₂)
    lemma equivalenceᴱ ext₁ ext₂ =
      Π-cong-Erased ext₁ (↝-ΠΣ-cong→↝ {k = equivalenceᴱ} A↝B ext₂)

  -- A variant of Π-cong-contra-Erased that is formulated using
  -- _↝[_∣_]-ΠΣ-cong_.

  Π-cong-contra-Erased′ :
    {A : Type ℓ} {B : Type b} {P : @0 A → Type p} {Q : B → Type q} →
    Extensionality? k (b ⊔ c ⊔ ℓ) (d ⊔ p ⊔ q) →
    (B↝A : B ↝[ c ∣ d ]-ΠΣ-cong A) →
    (∀ x → P (B↝A .proj₁ x) ↝[ k ] Q x) →
    ((x : A) → P x) ↝[ k ] ((x : B) → Q x)
  Π-cong-contra-Erased′ {b} {p} {q} {c} {d} {A} {B} {P} {Q} ext B↝A =
    lemma _
      (lower-extensionality? _ c d ext)
      (lower-extensionality? _ (b ⊔ ℓ) (p ⊔ q) ext)
    where
    lemma :
      ∀ k →
      Extensionality? k (b ⊔ ℓ) (p ⊔ q) →
      Extensionality? k c d →
      (∀ x → P (B↝A .proj₁ x) ↝[ k ] Q x) →
      ((x : A) → P x) ↝[ k ] ((x : B) → Q x)
    lemma implication ext₁ ext₂ =
      Π-cong-contra-Erased ext₁ (↝-ΠΣ-cong→↝ {k = implication} B↝A ext₂)
    lemma logical-equivalence ext₁ ext₂ =
      Π-cong-contra-Erased ext₁
        (↝-ΠΣ-cong→↝ {k = logical-equivalence} B↝A ext₂)
    lemma injection ext₁ ext₂ =
      Π-cong-contra-Erased ext₁ (↝-ΠΣ-cong→↝ {k = injection} B↝A ext₂)
    lemma embedding ext₁ ext₂ =
      Π-cong-contra-Erased ext₁ (↝-ΠΣ-cong→↝ {k = embedding} B↝A ext₂)
    lemma surjection ext₁ ext₂ =
      Π-cong-contra-Erased ext₁ (↝-ΠΣ-cong→↝ {k = surjection} B↝A ext₂)
    lemma bijection ext₁ ext₂ =
      Π-cong-contra-Erased ext₁ (↝-ΠΣ-cong→↝ {k = bijection} B↝A ext₂)
    lemma equivalence ext₁ ext₂ =
      Π-cong-contra-Erased ext₁ (↝-ΠΣ-cong→↝ {k = equivalence} B↝A ext₂)
    lemma equivalenceᴱ ext₁ ext₂ =
      Π-cong-contra-Erased ext₁
        (↝-ΠΣ-cong→↝ {k = equivalenceᴱ} B↝A ext₂)

  ----------------------------------------------------------------------
  -- Variants of other lemmas from Function-universe

  -- A variant of drop-⊤-left-Σ.

  drop-⊤-left-Σ-≃ᴱ-Erased :
    {@0 A : Type ℓ} {P : @0 A → Type p} →
    (A≃⊤ : A ≃ᴱ ⊤) → Σ A (λ x → P x) ≃ᴱ P (_≃ᴱ_.from A≃⊤ tt)
  drop-⊤-left-Σ-≃ᴱ-Erased {A} {P} A≃⊤ =
    Σ A (λ x → P x)                  ≃ᴱ⟨ inverse $ Σ-cong-≃ᴱ-Erased (inverse A≃⊤) (λ _ → F.id) ⟩
    Σ ⊤ (λ x → P (_≃ᴱ_.from A≃⊤ x))  ↔⟨ Σ-left-identity ⟩□
    P (_≃ᴱ_.from A≃⊤ tt)             □

  -- A variant of drop-⊤-left-Π.

  drop-⊤-left-Π-≃ᴱ-Erased :
    {@0 A : Type ℓ} {P : @0 A → Type p} →
    @0 Extensionality ℓ p →
    (A≃⊤ : A ≃ᴱ ⊤) →
    ((x : A) → P x) ≃ᴱ P (_≃ᴱ_.from A≃⊤ tt)
  drop-⊤-left-Π-≃ᴱ-Erased {A} {P} ext A≃⊤ =
    ((x : A) → P x)                  ≃ᴱ⟨ Π-cong-contra-≃ᴱ-Erased ext (inverse A≃⊤) (λ _ → F.id) ⟩
    ((x : ⊤) → P (_≃ᴱ_.from A≃⊤ x))  ↔⟨ Π-left-identity ⟩□
    P (_≃ᴱ_.from A≃⊤ tt)             □

  ----------------------------------------------------------------------
  -- A definition related to Decidable-erased-equality

  private

    -- A preservation lemma for Decidable-erased-equality.
    --
    -- Compare to Decidable-erased-equality-cong-≃ᴱ above.

    Decidable-erased-equality-cong-≃ᴱ′ :
      {A : Type a} {B : Type ℓ} →
      @0 Extensionality (a ⊔ ℓ) (a ⊔ ℓ) →
      A ≃ᴱ B →
      Decidable-erased-equality A ≃ᴱ Decidable-erased-equality B
    Decidable-erased-equality-cong-≃ᴱ′ ext A≃ᴱB =
      Π-cong-≃ᴱ-Erased ext A≃ᴱB λ _ →
      Π-cong-≃ᴱ-Erased ext A≃ᴱB λ _ →
      Dec-Erased-cong-≃ᴱ (lower-extensionality lzero _ ext)
        (inverse (to≡to≃ᴱ≡ A≃ᴱB))

  ----------------------------------------------------------------------
  -- A variant of a lemma proved above

  -- If f is an equivalence (with erased proofs) from Erased A to B,
  -- then x ≡ y is equivalent (with erased proofs) to f x ≡ f y.

  to≡to≃ᴱ≡-Erased :
    ∀ {@0 A : Type ℓ} {x y}
    (A≃B : Erased A ≃ᴱ B) →
    (_≃ᴱ_.to A≃B x ≡ _≃ᴱ_.to A≃B y) ≃ᴱ (x ≡ y)
  to≡to≃ᴱ≡-Erased {B} {A} {x = x@([ _ ])} {y = y@([ _ ])} A≃B =
    [≃]→≃ᴱ ([proofs] ≡≃≡)
    where
    @0 ≡≃≡ : (_≃ᴱ_.to A≃B x ≡ _≃ᴱ_.to A≃B y) ≃ (x ≡ y)
    ≡≃≡ =
      Eq.with-other-function
        (Eq.≃-≡ (≃ᴱ→≃ A≃B))
        (λ eq →
           x                                           ≡⟨ sym $ []-cong [ cong erased (_≃ᴱ_.left-inverse-of A≃B x) ] ⟩
           [ erased (_≃ᴱ_.from A≃B (_≃ᴱ_.to A≃B x)) ]  ≡⟨ []-cong [ cong erased (cong (_≃ᴱ_.from A≃B) eq) ] ⟩
           [ erased (_≃ᴱ_.from A≃B (_≃ᴱ_.to A≃B y)) ]  ≡⟨ []-cong [ cong erased (_≃ᴱ_.left-inverse-of A≃B y) ] ⟩∎
           y                                           ∎)
        (λ eq →
           let f = _≃ᴱ_.left-inverse-of A≃B in
           trans (sym (f x)) (trans (cong (_≃ᴱ_.from A≃B) eq) (f y))      ≡⟨ sym $ _≃_.right-inverse-of ≡≃[]≡[] _ ⟩

           []-cong
             [ cong erased
                 (trans (sym (f x))
                    (trans (cong (_≃ᴱ_.from A≃B) eq) (f y))) ]            ≡⟨ cong []-cong $ []-cong [ cong-trans _ _ _ ] ⟩

           []-cong
             [ trans (cong erased (sym (f x)))
                 (cong erased
                    (trans (cong (_≃ᴱ_.from A≃B) eq) (f y))) ]            ≡⟨ cong []-cong $
                                                                             []-cong [ cong₂ trans (cong-sym _ _) (cong-trans _ _ _) ] ⟩
           []-cong
             [ trans (sym (cong erased (f x)))
                 (trans (cong erased (cong (_≃ᴱ_.from A≃B) eq))
                    (cong erased (f y))) ]                                ≡⟨ []-cong-trans ⟩

           trans ([]-cong [ sym (cong erased (f x)) ])
              ([]-cong
                 [ trans (cong erased (cong (_≃ᴱ_.from A≃B) eq))
                     (cong erased (f y)) ])                               ≡⟨ cong₂ trans []-cong-sym []-cong-trans ⟩∎

           trans (sym ([]-cong [ cong erased (f x) ]))
              (trans ([]-cong [ cong erased (cong (_≃ᴱ_.from A≃B) eq) ])
                 ([]-cong [ cong erased (f y) ]))                         ∎)

------------------------------------------------------------------------
-- Results that follow if the []-cong axioms hold for the maximum of
-- two universe levels (as well as for the two universe levels)

module []-cong₂-⊔
  (ax₁ : []-cong-axiomatisation ℓ₁)
  (ax₂ : []-cong-axiomatisation ℓ₂)
  (ax  : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
  where

  open Erased-cong ax ax
  open Erased.[]-cong₁ ax
  open Erased.[]-cong₂-⊔ ax₁ ax₂ ax
  open []-cong₁ ax

  ----------------------------------------------------------------------
  -- More preservation lemmas

  private

    -- Is-equivalenceᴱ f is equivalent to Is-equivalenceᴱ g if f and g
    -- are pointwise equal (assuming extensionality).

    Is-equivalenceᴱ-cong′ :
      {A : Type a} {B : Type b} {@0 f g : A → B} →
      []-cong-axiomatisation (a ⊔ b) →
      @0 Extensionality? k (a ⊔ b) (a ⊔ b) →
      @0 (∀ x → f x ≡ g x) →
      Is-equivalenceᴱ f ↝[ k ] Is-equivalenceᴱ g
    Is-equivalenceᴱ-cong′ {f} {g} ax ext f≡g =
      generalise-erased-ext?
        (Is-equivalenceᴱ-cong-⇔ f≡g)
        (λ ext →
           (∃ λ f⁻¹ → Erased (HA.Proofs f f⁻¹))  F.↔⟨ (∃-cong λ _ → Erased.Erased-cong.Erased-cong-≃ ax ax (Proofs-cong ext f≡g)) ⟩□
           (∃ λ f⁻¹ → Erased (HA.Proofs g f⁻¹))  □)
        ext

  -- Is-equivalenceᴱ f is equivalent to Is-equivalenceᴱ g if f and g
  -- are pointwise equal (assuming extensionality).

  Is-equivalenceᴱ-cong :
    {A : Type ℓ₁} {B : Type ℓ₂} {@0 f g : A → B} →
    @0 Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    @0 (∀ x → f x ≡ g x) →
    Is-equivalenceᴱ f ↝[ k ] Is-equivalenceᴱ g
  Is-equivalenceᴱ-cong = Is-equivalenceᴱ-cong′ ax

  -- The operator _-Nullᴱ_ preserves equivalences with erased proofs
  -- (assuming extensionality).

  Nullᴱ-cong :
    {A : Type a} {B : Type b} {C : Type ℓ₁}
    {P : A → Type ℓ₂} {Q : A → Type q} →
    @0 Extensionality (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ q) (b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ q) →
    (∀ x → P x ≃ᴱ Q x) → B ≃ᴱ C → P -Nullᴱ B ≃ᴱ Q -Nullᴱ C
  Nullᴱ-cong {a} {b} {q} {B} {C} {P} {Q} ext P≃ᴱQ B≃ᴱC =
    P -Nullᴱ B                                                            ↔⟨⟩

    (∀ x → Is-equivalenceᴱ (const ⦂ (B → P x → B)))                       ↝⟨ (∀-cong [ ext′ ] λ x →
                                                                              Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-∘ʳ ext″ $
                                                                              _≃ᴱ_.is-equivalence $ inverse B≃ᴱC) ⟩

    (∀ x → Is-equivalenceᴱ ((const ⦂ (B → P x → B)) ⊚ _≃ᴱ_.from B≃ᴱC))    ↝⟨ (∀-cong [ ext′ ] λ x →
                                                                              Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-∘ˡ ext″ $
                                                                              _≃ᴱ_.is-equivalence $
                                                                              ∀-cong [ lower-extensionality (a ⊔ b ⊔ ℓ₁ ⊔ q) (ℓ₂ ⊔ q) ext ] λ _ →
                                                                              B≃ᴱC) ⟩
    (∀ x →
       Is-equivalenceᴱ
         ((_≃ᴱ_.to B≃ᴱC ⊚_) ⊚ (const ⦂ (B → P x → B)) ⊚ _≃ᴱ_.from B≃ᴱC))  ↝⟨ (∀-cong [ lower-extensionality (b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ q) (b ⊔ q) ext ] λ x →
                                                                              Is-equivalenceᴱ-cong′ ax
                                                                                [ lower-extensionality (a ⊔ b ⊔ q) (b ⊔ q) ext ] λ y →
      const (_≃ᴱ_.to B≃ᴱC (_≃ᴱ_.from B≃ᴱC y))                                   ≡⟨ cong const $ _≃ᴱ_.right-inverse-of B≃ᴱC _ ⟩∎
      const y                                                                   ∎) ⟩

    (∀ x → Is-equivalenceᴱ (const ⦂ (C → P x → C)))                       ↝⟨ (∀-cong [ lower-extensionality (b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ q) b ext ] λ x →
                                                                              Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-∘ˡ
                                                                                (lower-extensionality (a ⊔ b) b ext) $
                                                                                _≃ᴱ_.is-equivalence $
                                                                                →-cong
                                                                                  [ lower-extensionality (a ⊔ b ⊔ ℓ₁) (b ⊔ ℓ₂ ⊔ q) ext ]
                                                                                  (P≃ᴱQ x) F.id) ⟩
    (∀ x →
       Is-equivalenceᴱ
         ((_⊚ _≃ᴱ_.from (P≃ᴱQ x)) ⊚ (const ⦂ (C → P x → C))))             ↔⟨⟩

    (∀ x → Is-equivalenceᴱ (const ⦂ (C → Q x → C)))                       ↔⟨⟩

    Q -Nullᴱ C                                                            □
    where
    @0 ext′ : _
    ext′ = lower-extensionality (b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ q) q ext
    @0 ext″ : _
    ext″ = lower-extensionality (a ⊔ q)           q ext

  ----------------------------------------------------------------------
  -- More conversion lemmas

  -- Some equivalences relating Is-equivalenceᴱ to Is-equivalence.
  --
  -- See also Is-equivalenceᴱ↔Is-equivalence below.

  Erased-Is-equivalenceᴱ≃Erased-Is-equivalence :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 f : A → B} →
    Erased (Is-equivalenceᴱ f) ≃ Erased (Is-equivalence f)
  Erased-Is-equivalenceᴱ≃Erased-Is-equivalence {f} =
    Erased (∃ λ f⁻¹ → Erased (HA.Proofs f f⁻¹))  ↝⟨ Erased-cong-≃ (∃-cong λ _ → Eq.↔⇒≃ $ erased Erased↔) ⟩□
    Erased (∃ λ f⁻¹ → HA.Proofs f f⁻¹)           □

  Erased-Is-equivalence≃Is-equivalenceᴱ :
    {@0 A : Type ℓ₁} {B : Type ℓ₂} {@0 f : Erased A → B} →
    Erased (Is-equivalence f) ↝[ ℓ₂ ∣ ℓ₁ ] Is-equivalenceᴱ f
  Erased-Is-equivalence≃Is-equivalenceᴱ {A} {B} {f} ext =
    Erased (Is-equivalence f)                              F.↔⟨⟩

    Erased (∃ λ (f⁻¹ : B → Erased A) → HA.Proofs f f⁻¹)    ↝⟨ lemma₂ ext ⟩

    Erased (∃ λ (f⁻¹ : B → A) → HA.Proofs f ([_]→ ⊚ f⁻¹))  F.↔⟨ Erased-Σ↔Σ ⟩

    (∃ λ (f⁻¹ : Erased (B → A)) →
     Erased (HA.Proofs f (λ x → map (_$ x) f⁻¹)))          ↝⟨ lemma₃ ext ⟩

    (∃ λ (f⁻¹ : B → Erased A) → Erased (HA.Proofs f f⁻¹))  F.↔⟨⟩

    Is-equivalenceᴱ f                                      F.□
    where
    @0 lemma₁ :
      HA.Proofs f f⁻¹ →
      HA.Proofs f ([_]→ ⊚ erased ⊚ f⁻¹)
    lemma₁ (f-f⁻¹ , f⁻¹-f , f-f⁻¹-f) =
        (λ _ → trans (cong f Erased-η) (f-f⁻¹ _))
      , (λ _ → trans Erased-η (f⁻¹-f _))
      , (λ x →
           cong f (trans Erased-η (f⁻¹-f x))           ≡⟨ cong-trans _ _ _ ⟩
           trans (cong f Erased-η) (cong f (f⁻¹-f x))  ≡⟨ cong (trans _) (f-f⁻¹-f _) ⟩∎
           trans (cong f Erased-η) (f-f⁻¹ (f x))       ∎)

    lemma₂ :
      Erased (∃ λ (f⁻¹ : B → Erased A) → HA.Proofs f f⁻¹) ↝[ ℓ₂ ∣ ℓ₁ ]ᴱ
      Erased (∃ λ (f⁻¹ : B → A) → HA.Proofs f ([_]→ ⊚ f⁻¹))
    lemma₂ = generalise-erased-ext?
      (Erased-cong-⇔ record
         { to   = Σ-map (erased ⊚_) lemma₁
         ; from = Σ-map ([_]→   ⊚_) P.id
         })
      (λ ext →
         Erased-cong-↔ (Σ-cong (∀-cong ext λ _ → erased Erased↔) λ _ →
         ≡⇒↝ _ $ cong (HA.Proofs _) $ sym $ apply-ext ext λ _ →
         Erased-η))

    lemma₃ :
      (∃ λ (f⁻¹ : Erased (B → A)) →
       Erased (HA.Proofs f (λ x → map (_$ x) f⁻¹))) ↝[ ℓ₂ ∣ ℓ₁ ]
      (∃ λ (f⁻¹ : B → Erased A) → Erased (HA.Proofs f f⁻¹))
    lemma₃ = generalise-ext?′
      (record
         { to   = Σ-map (_⇔_.to   (Erased-Π↔Π _)) P.id
         ; from = Σ-map (_⇔_.from (Erased-Π↔Π _)) (map lemma₁)
         })
      (λ ext → F.Σ-cong (Erased-Π↔Π {k = bijection} ext) λ _ → F.id)
      (λ ext → Σ-cong-≃ᴱ-Erased (Erased-Π↔Π [ ext ]) λ _ → F.id)

  ----------------------------------------------------------------------
  -- Variants of some lemmas proved above

  -- Is-equivalenceᴱ f is a proposition if the domain of f is Erased A
  -- (assuming extensionality).

  Is-equivalenceᴱ-propositional-for-Erased :
    {@0 A : Type ℓ₁} {B : Type ℓ₂} {@0 f : Erased A → B} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Is-proposition (Is-equivalenceᴱ f)
  Is-equivalenceᴱ-propositional-for-Erased {f} ext =
                                                F.$⟨ H-level-Erased 1 (Is-equivalence-propositional ext) ⟩
    Is-proposition (Erased (Is-equivalence f))  ↝⟨ H-level.respects-surjection (Erased-Is-equivalence≃Is-equivalenceᴱ ext′) 1 ⟩□
    Is-proposition (Is-equivalenceᴱ f)          □
    where
    ext′ = lower-extensionality ℓ₁ ℓ₂ ext

  -- A variant of to≡to→≡ that is not defined in an erased context.
  -- Note that one side of the equivalence is Erased A.

  to≡to→≡-Erased :
    {@0 A : Type ℓ₁} {B : Type ℓ₂} {p q : Erased A ≃ᴱ B} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    _≃ᴱ_.to p ≡ _≃ᴱ_.to q → p ≡ q
  to≡to→≡-Erased {p = ⟨ f , f-eq ⟩} {q = ⟨ g , g-eq ⟩} ext f≡g =
    elim (λ {f g} f≡g → ∀ f-eq g-eq → ⟨ f , f-eq ⟩ ≡ ⟨ g , g-eq ⟩)
         (λ f _ _ →
            cong ⟨ f ,_⟩
              (Is-equivalenceᴱ-propositional-for-Erased ext _ _))
         f≡g f-eq g-eq

  ----------------------------------------------------------------------
  -- More lemmas

  -- An equivalence relating Is-equivalenceᴱ to Is-equivalence.

  Is-equivalenceᴱ↔Is-equivalence :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 f : A → B} →
    Is-equivalenceᴱ (map f) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ]
    Is-equivalence (map f)
  Is-equivalenceᴱ↔Is-equivalence {f} =
    generalise-ext?-prop
      (Is-equivalenceᴱ (map f)                                        ↝⟨ Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP ⟩
       (∀ y → Contractibleᴱ (map f ⁻¹ᴱ y))                            F.↔⟨⟩
       (∀ y → Contractibleᴱ (∃ λ x → Erased ([ f (erased x) ] ≡ y)))  ↝⟨ (∀-cong _ λ _ → ECP.[]-cong₂.Contractibleᴱ-cong ax ax _ $ Eq.↔⇒≃ $
                                                                          F.inverse Erased-Σ↔Σ) ⟩
       (∀ y → Contractibleᴱ (Erased (∃ λ x → [ f x ] ≡ y)))           ↝⟨ (∀-cong _ λ _ →
                                                                          ECP.[]-cong₁.Contractibleᴱ-Erased↔Contractible-Erased ax _) ⟩
       (∀ y → Contractible (Erased (∃ λ x → [ f x ] ≡ y)))            ↝⟨ (∀-cong _ λ _ → H-level-cong _ 0 Erased-Σ↔Σ) ⟩
       (∀ y → Contractible (∃ λ x → Erased (map f x ≡ y)))            F.↔⟨⟩
       (∀ y → Contractible (map f ⁻¹ᴱ y))                             ↝⟨ (∀-cong _ λ { [ _ ] → H-level-cong _ 0 $ ECP.[]-cong₁.⁻¹ᴱ[]↔⁻¹[] ax₂ }) ⟩
       (∀ y → Contractible (map f ⁻¹ y))                              ↝⟨ inverse-ext? Is-equivalence≃Is-equivalence-CP _ ⟩□
       Is-equivalence (map f)                                         □)
      (λ ext → Is-equivalenceᴱ-propositional-for-Erased ext)
      Is-equivalence-propositional

  -- Erased "commutes" with Is-equivalenceᴱ (assuming extensionality).

  Erased-Is-equivalenceᴱ↔Is-equivalenceᴱ :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 f : A → B} →
    Erased (Is-equivalenceᴱ f) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ]
    Is-equivalenceᴱ (map f)
  Erased-Is-equivalenceᴱ↔Is-equivalenceᴱ {f} {k} ext =
    Erased (Is-equivalenceᴱ f)          F.↔⟨ Erased-Is-equivalenceᴱ≃Erased-Is-equivalence ⟩
    Erased (Is-equivalence f)           F.↔⟨ F.inverse Erased-Erased↔Erased ⟩
    Erased (Erased (Is-equivalence f))  ↝⟨ Erased-cong? Erased-Is-equivalence↔Is-equivalence ext ⟩
    Erased (Is-equivalence (map f))     ↝⟨ Erased-Is-equivalence≃Is-equivalenceᴱ (lower-extensionality? k ℓ₁ ℓ₂ ext) ⟩□
    Is-equivalenceᴱ (map f)             □

------------------------------------------------------------------------
-- Results that depend on an axiomatisation of []-cong (for all
-- universe levels)

module []-cong (ax : ∀ {ℓ} → []-cong-axiomatisation ℓ) where

  private
    open module BC₁ {ℓ} =
      []-cong₁ (ax {ℓ = ℓ})
      public
    open module BC₂ {ℓ₁ ℓ₂} =
      []-cong₂-⊔ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) (ax {ℓ = ℓ₁ ⊔ ℓ₂})
      public
