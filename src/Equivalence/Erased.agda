------------------------------------------------------------------------
-- Equivalences with erased "proofs"
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Equivalence.Erased
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id; [_,_]) renaming (_∘_ to _⊚_)

open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
import Equivalence.Contractible-preimages eq as CP
open import Equivalence.Erased.Contractible-preimages eq as ECP
  using (_⁻¹ᴱ_; Contractibleᴱ)
import Equivalence.Half-adjoint eq as HA
open import Erased.Level-1 eq as Erased
open import Function-universe eq as F hiding (id; _∘_; inverse)
open import H-level eq as H-level
open import H-level.Closure eq
import Nat eq as Nat
open import Preimage eq as Preimage using (_⁻¹_)
open import Surjection eq as Surjection using (_↠_; Split-surjective)
open import Univalence-axiom eq

private
  variable
    a b d ℓ q    : Level
    A B C        : Type a
    c k k′ p x y : A
    P Q          : A → Type p
    f g          : (x : A) → P x

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
Is-equivalence≃Is-equivalenceᴱ {f = f} =
  (∃ λ f⁻¹ → HA.Proofs f f⁻¹)           ↔⟨ (∃-cong λ _ → F.inverse $ erased Erased↔) ⟩□
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
≃≃≃ᴱ {A = A} {B = B} =
  A ≃ B                        ↔⟨ Eq.≃-as-Σ ⟩
  (∃ λ f → Is-equivalence f)   ↝⟨ (∃-cong λ _ → Is-equivalence≃Is-equivalenceᴱ) ⟩
  (∃ λ f → Is-equivalenceᴱ f)  ↔⟨ Eq.inverse ≃ᴱ-as-Σ ⟩□
  A ≃ᴱ B                       □

_ : _≃_.to ≃≃≃ᴱ p ≡ ≃→≃ᴱ p
_ = refl _

@0 _ : _≃_.from ≃≃≃ᴱ p ≡ ≃ᴱ→≃ p
_ = refl _

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
    (Eq.propositional ext f)

------------------------------------------------------------------------
-- Even more conversion lemmas, and a related result

-- Is-equivalenceᴱ f is logically equivalent to ECP.Is-equivalenceᴱ f.

Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP :
  Is-equivalenceᴱ f ⇔ ECP.Is-equivalenceᴱ f
Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP {f = f} =
  record { to = to; from = from }
  where
  to : Is-equivalenceᴱ f → ECP.Is-equivalenceᴱ f
  to eq y =
      (proj₁ eq y , [ erased (proj₂ $ proj₁ eq′) ])
    , [ erased (proj₂ eq′) ]
    where
    @0 eq′ : Contractibleᴱ (f ⁻¹ᴱ y)
    eq′ =
      ECP.Is-equivalence→Is-equivalenceᴱ
        (_⇔_.to HA.Is-equivalence⇔Is-equivalence-CP $
         Is-equivalenceᴱ→Is-equivalence eq)
        y

  from : ECP.Is-equivalenceᴱ f → Is-equivalenceᴱ f
  from eq =
      proj₁ ⊚ proj₁ ⊚ eq
    , [ erased $ proj₂ $
        Is-equivalence→Is-equivalenceᴱ $
        _⇔_.from HA.Is-equivalence⇔Is-equivalence-CP $
        ECP.Is-equivalenceᴱ→Is-equivalence eq
      ]

-- Is-equivalenceᴱ f is equivalent (with erased proofs) to
-- ECP.Is-equivalenceᴱ f (assuming extensionality).

Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP :
  {A : Type a} {B : Type b} {f : A → B} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  Is-equivalenceᴱ f ≃ᴱ ECP.Is-equivalenceᴱ f
Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext = ⇔→≃ᴱ
  (Is-equivalenceᴱ-propositional ext _)
  (ECP.Is-equivalenceᴱ-propositional ext _)
  (_⇔_.to Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP)
  (_⇔_.from Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP)

-- When proving that a function is an equivalence (with erased proofs)
-- one can assume that the codomain is inhabited.

[inhabited→Is-equivalenceᴱ]→Is-equivalenceᴱ :
  {f : A → B} →
  (B → Is-equivalenceᴱ f) → Is-equivalenceᴱ f
[inhabited→Is-equivalenceᴱ]→Is-equivalenceᴱ hyp =
  _⇔_.from Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP $ λ x →
  _⇔_.to Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP (hyp x) x

------------------------------------------------------------------------
-- Some preservation lemmas

-- A preservation lemma related to Σ.
--
-- Note that the third argument is not marked as erased. The from
-- argument of [≃]→≃ᴱ (which Agda can infer in this case, at least at
-- the time of writing) is included explicitly to show where the third
-- argument is used in a (potentially) non-erased context.
--
-- See also Σ-cong-≃ᴱ-Erased below.

Σ-cong-≃ᴱ :
  (f : A → B) (g : B → A)
  (f-g : ∀ x → f (g x) ≡ x) →
  @0 (∀ x → g (f x) ≡ x) →
  (∀ x → P x ≃ᴱ Q (f x)) →
  Σ A P ≃ᴱ Σ B Q
Σ-cong-≃ᴱ {Q = Q} f g f-g g-f P≃Q =
  [≃]→≃ᴱ
    {from = λ p → g (proj₁ p)
                , _≃ᴱ_.from (P≃Q (g (proj₁ p)))
                    (subst Q (sym (f-g (proj₁ p))) (proj₂ p))}
    ([proofs] (Σ-cong (Eq.↔→≃ f g f-g g-f) (≃ᴱ→≃ ⊚ P≃Q)))

-- Another preservation lemma related to Σ.
--
-- See also Σ-cong-contra-≃ᴱ-Erased below.

Σ-cong-contra-≃ᴱ :
  (f : B → A) (g : A → B) →
  (∀ x → f (g x) ≡ x) →
  @0 (∀ x → g (f x) ≡ x) →
  (∀ x → P (f x) ≃ᴱ Q x) →
  Σ A P ≃ᴱ Σ B Q
Σ-cong-contra-≃ᴱ f g f-g g-f P≃Q =
  inverse $ Σ-cong-≃ᴱ f g f-g g-f (inverse ⊚ P≃Q)

-- Yet another preservation lemma related to Σ.

Σ-cong-≃ᴱ′ :
  (A≃ᴱB : A ≃ᴱ B)
  (P→Q : ∀ x → P x → Q (_≃ᴱ_.to A≃ᴱB x))
  (Q→P : ∀ x → Q x → P (_≃ᴱ_.from A≃ᴱB x))
  (@0 eq : ∀ x → Is-equivalence (P→Q x)) →
  @0 (∀ x y →
      Q→P x y ≡
      _≃_.from Eq.⟨ P→Q (_≃ᴱ_.from A≃ᴱB x) , eq (_≃ᴱ_.from A≃ᴱB x) ⟩
        (subst Q (sym (_≃ᴱ_.right-inverse-of A≃ᴱB x)) y)) →
  Σ A P ≃ᴱ Σ B Q
Σ-cong-≃ᴱ′ {A = A} {B = B} {P = P} {Q = Q} A≃B P→Q Q→P eq hyp =
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
-- See also Π-cong-≃ᴱ-Erased and Π-cong-contra-≃ᴱ-Erased below.

Π-cong-≃ᴱ :
  {A : Type a} {B : Type b} {P : A → Type p} {Q : B → Type q} →
  @0 Extensionality (a ⊔ b) (p ⊔ q) →
  (f : A → B) (g : B → A) →
  (∀ x → f (g x) ≡ x) →
  @0 (∀ x → g (f x) ≡ x) →
  (∀ x → P x ≃ᴱ Q (f x)) →
  ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
Π-cong-≃ᴱ {Q = Q} ext f g f-g g-f P≃Q =
  [≃]→≃ᴱ
    {to = λ h x → subst Q (f-g x) (_≃ᴱ_.to (P≃Q (g x)) (h (g x)))}
    ([proofs] (Π-cong ext (Eq.↔→≃ f g f-g g-f) (≃ᴱ→≃ ⊚ P≃Q)))

Π-cong-contra-≃ᴱ :
  {A : Type a} {B : Type b} {P : A → Type p} {Q : B → Type q} →
  @0 Extensionality (a ⊔ b) (p ⊔ q) →
  (f : B → A) (g : A → B) →
  (∀ x → f (g x) ≡ x) →
  @0 (∀ x → g (f x) ≡ x) →
  (∀ x → P (f x) ≃ᴱ Q x) →
  ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
Π-cong-contra-≃ᴱ ext f g f-g g-f P≃Q =
  inverse $ Π-cong-≃ᴱ ext f g f-g g-f (inverse ⊚ P≃Q)

Π-cong-≃ᴱ′ :
  {A : Type a} {B : Type b} {P : A → Type p} {Q : B → Type q} →
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
Π-cong-≃ᴱ′ {a = a} {p = p} {A = A} {B = B} {P = P} {Q = Q}
           ext A≃B P→Q Q→P eq hyp =
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
  {A : Type a} {P : A → Type p} {Q : A → Type q} →
  @0 Extensionality a (p ⊔ q) →
  (∀ x → P x ≃ᴱ Q x) →
  ((x : A) → P x) ≃ᴱ ((x : A) → Q x)
∀-cong-≃ᴱ ext P≃Q = [≃]→≃ᴱ ([proofs] (∀-cong ext (≃ᴱ→≃ ⊚ P≃Q)))

-- The _≃ᴱ_ operator preserves equivalences with erased proofs
-- (assuming extensionality).

≃ᴱ-cong :
  {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
  @0 Extensionality (a ⊔ b ⊔ c ⊔ d) (a ⊔ b ⊔ c ⊔ d) →
  A ≃ᴱ B → C ≃ᴱ D → (A ≃ᴱ C) ≃ᴱ (B ≃ᴱ D)
≃ᴱ-cong {A = A} {B = B} {C = C} {D = D} ext A≃B C≃D =
  [≃]→≃ᴱ ([proofs] lemma)
  where
  @0 lemma : (A ≃ᴱ C) ≃ (B ≃ᴱ D)
  lemma =
    A ≃ᴱ C  ↝⟨ F.inverse ≃≃≃ᴱ ⟩
    A ≃ C   ↝⟨ Eq.≃-preserves ext (≃ᴱ→≃ A≃B) (≃ᴱ→≃ C≃D) ⟩
    B ≃ D   ↝⟨ ≃≃≃ᴱ ⟩□
    B ≃ᴱ D  □

------------------------------------------------------------------------
-- Variants of some lemmas from Function-universe

-- A variant of drop-⊤-left-Σ.
--
-- See also drop-⊤-left-Σ-≃ᴱ-Erased below.

drop-⊤-left-Σ-≃ᴱ :
  (A≃⊤ : A ≃ᴱ ⊤) →
  (∀ x y → P x ≃ᴱ P y) →
  Σ A P ≃ᴱ P (_≃ᴱ_.from A≃⊤ tt)
drop-⊤-left-Σ-≃ᴱ {A = A} {P = P} A≃⊤ P≃P =
  Σ A P                            ↝⟨ Σ-cong-≃ᴱ
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
  {A : Type a} {P : A → Type p} →
  @0 Extensionality a p →
  (A≃⊤ : A ≃ᴱ ⊤) →
  (∀ x y → P x ≃ᴱ P y) →
  ((x : A) → P x) ≃ᴱ P (_≃ᴱ_.from A≃⊤ tt)
drop-⊤-left-Π-≃ᴱ {A = A} {P = P} ext A≃⊤ P≃P =
  ((x : A) → P x)                  ↝⟨ Π-cong-≃ᴱ
                                        ext
                                        _
                                        (_≃ᴱ_.from A≃⊤)
                                        refl
                                        (_≃ᴱ_.left-inverse-of A≃⊤)
                                        (λ _ → P≃P _ _) ⟩
  ((x : ⊤) → P (_≃ᴱ_.from A≃⊤ x))  ↔⟨ Π-left-identity ⟩□
  P (_≃ᴱ_.from A≃⊤ tt)             □

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
to≡to≃≡ {p = p} {q = q} ext =
  (∀ x → _≃ᴱ_.to p x ≡ _≃ᴱ_.to q x)                                ↔⟨⟩
  (∀ x → _≃_.to (_≃_.from ≃≃≃ᴱ p) x ≡ _≃_.to (_≃_.from ≃≃≃ᴱ q) x)  ↔⟨ ≃-to-≡↔≡ ext ⟩
  _≃_.from ≃≃≃ᴱ p ≡ _≃_.from ≃≃≃ᴱ q                                ↝⟨ Eq.≃-≡ (Eq.inverse ≃≃≃ᴱ) ⟩□
  p ≡ q                                                            □

------------------------------------------------------------------------
-- A lemma that is related to Eq.≃-≡

-- If f is a half adjoint equivalence with certain erased proofs, then
-- x ≡ y is equivalent (with erased proofs) to f x ≡ f y.
--
-- (Perhaps it is possible to prove a similar lemma which returns a
-- half adjoint equivalence where the "left-inverse-of" part is not
-- erased.)
--
-- See also to≡to≃ᴱ≡-Erased below.

≡≃ᴱto≡to :
  (f : A → B) (g : B → A)
  (@0 f∘g : ∀ y → f (g y) ≡ y)
  (g∘f : ∀ x → g (f x) ≡ x) →
  @0 (∀ x → cong f (g∘f x) ≡ f∘g (f x)) →
  (x ≡ y) ≃ᴱ (f x ≡ f y)
≡≃ᴱto≡to {x = x} {y = y} f g f∘g g∘f coh = ↔→≃ᴱ
  (_↠_.from ≡↠≡)
  (_↠_.to   ≡↠≡)
  (λ eq →
     _↠_.from ≡↠≡ (_↠_.to ≡↠≡ eq)                              ≡⟨⟩

     cong f (trans (sym (g∘f x)) (trans (cong g eq) (g∘f y)))  ≡⟨ cong-trans _ _ _ ⟩

     trans (cong f (sym (g∘f x)))
       (cong f (trans (cong g eq) (g∘f y)))                    ≡⟨ cong₂ trans
                                                                    (cong-sym _ _)
                                                                    (cong-trans _ _ _) ⟩
     trans (sym (cong f (g∘f x)))
       (trans (cong f (cong g eq)) (cong f (g∘f y)))           ≡⟨ cong₂ (λ p q → trans (sym p) (trans (cong f (cong g eq)) q))
                                                                    (coh _)
                                                                    (coh _) ⟩
     trans (sym (f∘g (f x)))
       (trans (cong f (cong g eq)) (f∘g (f y)))                ≡⟨⟩

     _↠_.to ≡↠≡′ (_↠_.from ≡↠≡′ eq)                            ≡⟨ _↠_.right-inverse-of ≡↠≡′ eq ⟩∎

     eq                                                        ∎)
  (_↠_.right-inverse-of ≡↠≡)
  where
  ≡↠≡ : (f x ≡ f y) ↠ (x ≡ y)
  ≡↠≡ = Surjection.↠-≡ (record
    { logical-equivalence = record
      { to   = g
      ; from = f
      }
    ; right-inverse-of = g∘f
    })

  @0 ≡↠≡′ : ∀ {x y} → (g x ≡ g y) ↠ (x ≡ y)
  ≡↠≡′ = Surjection.↠-≡ (record
    { logical-equivalence = record
      { to   = f
      ; from = g
      }
    ; right-inverse-of = f∘g
    })

------------------------------------------------------------------------
-- Some results related to Contractibleᴱ

-- Two types that are contractible (with erased proofs) are equivalent
-- (with erased proofs).

Contractibleᴱ→≃ᴱ : Contractibleᴱ A → Contractibleᴱ B → A ≃ᴱ B
Contractibleᴱ→≃ᴱ (a , [ irrA ]) (b , [ irrB ]) = ↔→≃ᴱ
  (const b)
  (const a)
  irrB
  irrA

-- There is a logical equivalence between Contractibleᴱ A and A ≃ᴱ ⊤.

Contractibleᴱ⇔≃ᴱ⊤ : Contractibleᴱ A ⇔ A ≃ᴱ ⊤
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
  {A : Type a} →
  @0 Extensionality a a →
  Contractibleᴱ A ≃ᴱ (A ≃ᴱ ⊤)
Contractibleᴱ≃ᴱ≃ᴱ⊤ ext = ↔→≃ᴱ
  (_⇔_.to   Contractibleᴱ⇔≃ᴱ⊤)
  (_⇔_.from Contractibleᴱ⇔≃ᴱ⊤)
  (λ _ → to≡to→≡ ext (refl _))
  (λ _ → ECP.Contractibleᴱ-propositional ext _ _)

-- If an inhabited type comes with an erased proof of
-- propositionality, then it is equivalent (with erased proofs) to the
-- unit type.

inhabited→Is-proposition→≃ᴱ⊤ :
  A → @0 Is-proposition A → A ≃ᴱ ⊤
inhabited→Is-proposition→≃ᴱ⊤ x prop =
  _⇔_.to Contractibleᴱ⇔≃ᴱ⊤
    (ECP.inhabited→Is-proposition→Contractibleᴱ x prop)

-- Contractibleᴱ commutes with _×_ (up to _≃ᴱ_, assuming
-- extensionality).

Contractibleᴱ-commutes-with-× :
  {A : Type a} {B : Type b} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  Contractibleᴱ (A × B) ≃ᴱ (Contractibleᴱ A × Contractibleᴱ B)
Contractibleᴱ-commutes-with-× {a = a} {b = b} {A = A} {B = B} ext =
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

inverse-logical-equivalence : A ≃ᴱ B ⇔ B ≃ᴱ A
inverse-logical-equivalence = record
  { to   = inverse
  ; from = inverse
  }

-- Inverse is an equivalence with erased proofs (assuming
-- extensionality).

inverse-equivalence :
  {A : Type a} {B : Type b} →
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
≡≃≃ᴱ {A = A} {B = B} univ =
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
singleton-with-≃ᴱ-≃ᴱ-⊤ {b = b} a {B = B} ext univ =
  [≃]→≃ᴱ ([proofs] lemma)
  where
  @0 lemma : (∃ λ (A : Type (a ⊔ b)) → A ≃ᴱ B) ≃ ⊤
  lemma =
    (∃ λ (A : Type (a ⊔ b)) → A ≃ᴱ B)  ↝⟨ (∃-cong λ _ → F.inverse ≃≃≃ᴱ) ⟩
    (∃ λ (A : Type (a ⊔ b)) → A ≃ B)   ↔⟨ singleton-with-≃-↔-⊤ {a = a} ext univ ⟩□
    ⊤                                  □

other-singleton-with-≃ᴱ-≃ᴱ-⊤ :
  ∀ b {A : Type a} →
  @0 Extensionality (a ⊔ b) (a ⊔ b) →
  @0 Univalence (a ⊔ b) →
  (∃ λ (B : Type (a ⊔ b)) → A ≃ᴱ B) ≃ᴱ ⊤
other-singleton-with-≃ᴱ-≃ᴱ-⊤ b {A = A} ext univ =
  (∃ λ B → A ≃ᴱ B)  ↝⟨ (∃-cong λ _ → inverse-equivalence ext) ⟩
  (∃ λ B → B ≃ᴱ A)  ↝⟨ singleton-with-≃ᴱ-≃ᴱ-⊤ b ext univ ⟩□
  ⊤                 □

-- Variants of the two lemmas above.

singleton-with-Π-≃ᴱ-≃ᴱ-⊤ :
  {A : Type a} {Q : A → Type q} →
  @0 Extensionality a (lsuc q) →
  @0 Univalence q →
  (∃ λ (P : A → Type q) → ∀ x → P x ≃ᴱ Q x) ≃ᴱ ⊤
singleton-with-Π-≃ᴱ-≃ᴱ-⊤ {a = a} {q = q} {A = A} {Q = Q} ext univ =
  [≃]→≃ᴱ ([proofs] lemma)
  where
  @0 ext′ : Extensionality a q
  ext′ = lower-extensionality lzero _ ext

  @0 lemma : (∃ λ (P : A → Type q) → ∀ x → P x ≃ᴱ Q x) ≃ ⊤
  lemma =
    (∃ λ (P : A → Type q) → ∀ x → P x ≃ᴱ Q x)  ↝⟨ (∃-cong λ _ → ∀-cong ext′ λ _ → F.inverse ≃≃≃ᴱ) ⟩
    (∃ λ (P : A → Type q) → ∀ x → P x ≃ Q x)   ↔⟨ singleton-with-Π-≃-≃-⊤ ext univ ⟩□
    ⊤                                          □

other-singleton-with-Π-≃ᴱ-≃ᴱ-⊤ :
  {A : Type a} {P : A → Type p} →
  @0 Extensionality (a ⊔ p) (lsuc p) →
  @0 Univalence p →
  (∃ λ (Q : A → Type p) → ∀ x → P x ≃ᴱ Q x) ≃ᴱ ⊤
other-singleton-with-Π-≃ᴱ-≃ᴱ-⊤ {a = a} {p = p} {A = A} {P = P}
                               ext univ =
  (∃ λ (Q : A → Type p) → ∀ x → P x ≃ᴱ Q x)  ↝⟨ (∃-cong λ _ → ∀-cong-≃ᴱ ext₁ λ _ → inverse-equivalence ext₂) ⟩
  (∃ λ (Q : A → Type p) → ∀ x → Q x ≃ᴱ P x)  ↝⟨ singleton-with-Π-≃ᴱ-≃ᴱ-⊤ ext₃ univ ⟩□
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
  ∀ {a} →
  @0 Extensionality a a →
  @0 Univalence a →
  (∃ λ (A : Type a) → Contractibleᴱ A) ≃ᴱ ⊤
∃Contractibleᴱ≃ᴱ⊤ ext univ =
  (∃ λ A → Contractibleᴱ A)  ↝⟨ (∃-cong λ _ → Contractibleᴱ≃ᴱ≃ᴱ⊤ ext) ⟩
  (∃ λ A → A ≃ᴱ ⊤)           ↝⟨ singleton-with-≃ᴱ-≃ᴱ-⊤ _ ext univ ⟩□
  ⊤                          □

------------------------------------------------------------------------
-- Some simplification lemmas

-- Two simplification lemmas for id.

right-inverse-of-id :
  _≃ᴱ_.right-inverse-of id x ≡ refl x
right-inverse-of-id = refl _

@0 left-inverse-of-id :
  _≃ᴱ_.left-inverse-of id x ≡ refl x
left-inverse-of-id {x = x} =
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
left-inverse-of∘inverse {A = A} {B = B} {x = x} A≃B =
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
to-subst {P = P} {Q = Q} {eq = eq} {f = f} = elim¹
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
from-subst {P = P} {Q = Q} {eq = eq} {f = f} = elim¹
  (λ eq →
     _≃ᴱ_.from (subst (λ x → P x ≃ᴱ Q x) eq f) ≡
     subst (λ x → Q x → P x) eq (_≃ᴱ_.from f))
  (_≃ᴱ_.from (subst (λ x → P x ≃ᴱ Q x) (refl _) f)  ≡⟨ cong _≃ᴱ_.from $ subst-refl _ _ ⟩
   _≃ᴱ_.from f                                      ≡⟨ sym $ subst-refl _ _ ⟩∎
   subst (λ x → Q x → P x) (refl _) (_≃ᴱ_.from f)   ∎)
  eq

------------------------------------------------------------------------
-- One of the two-out-of-three properties

-- If f and g are equivalences with erased proofs, then g ⊚ f is also
-- an equivalence with erased proofs.

12→3 : Is-equivalenceᴱ f → Is-equivalenceᴱ g → Is-equivalenceᴱ (g ⊚ f)
12→3 p q = _≃ᴱ_.is-equivalence (⟨ _ , q ⟩ ∘ ⟨ _ , p ⟩)

------------------------------------------------------------------------
-- Results that depend on an axiomatisation of []-cong

module []-cong (ax : ∀ {a} → []-cong-axiomatisation a) where

  open Erased.[]-cong₃ ax

  ----------------------------------------------------------------------
  -- More preservation lemmas

  -- Equivalences with erased proofs are in some cases preserved by Σ
  -- (assuming extensionality). Note the type of Q.

  Σ-cong-≃ᴱ-Erased :
    {Q : @0 B → Type q}
    (A≃B : A ≃ᴱ B) →
    (∀ x → P x ≃ᴱ Q (_≃ᴱ_.to A≃B x)) →
    Σ A P ≃ᴱ Σ B (λ x → Q x)
  Σ-cong-≃ᴱ-Erased {B = B} {A = A} {P = P} {Q = Q} A≃B P≃Q =
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
    {P : @0 A → Type p}
    (B≃A : B ≃ᴱ A) →
    (∀ x → P (_≃ᴱ_.to B≃A x) ≃ᴱ Q x) →
    Σ A (λ x → P x) ≃ᴱ Σ B Q
  Σ-cong-contra-≃ᴱ-Erased {Q = Q} {P = P} B≃A P≃Q = ↔→≃ᴱ
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
    {A : Type a} {B : Type b} {P : A → Type p} {Q : @0 B → Type q} →
    @0 Extensionality (a ⊔ b) (p ⊔ q) →
    (A≃B : A ≃ᴱ B) →
    (∀ x → P x ≃ᴱ Q (_≃ᴱ_.to A≃B x)) →
    ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
  Π-cong-≃ᴱ-Erased
    {a = a} {p = p} {A = A} {B = B} {P = P} {Q = Q} ext A≃B P≃Q =
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
    {A : Type a} {B : Type b} {P : @0 A → Type p} {Q : B → Type q} →
    @0 Extensionality (a ⊔ b) (p ⊔ q) →
    (B≃A : B ≃ᴱ A) →
    (∀ x → P (_≃ᴱ_.to B≃A x) ≃ᴱ Q x) →
    ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
  Π-cong-contra-≃ᴱ-Erased
    {b = b} {q = q} {A = A} {B = B} {P = P} {Q = Q} ext B≃A P≃Q =
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

  -- Is-equivalenceᴱ f is equivalent to Is-equivalenceᴱ g if f and g
  -- are pointwise equal (assuming extensionality).

  Is-equivalenceᴱ-cong :
    {A : Type a} {B : Type b} {@0 f g : A → B} →
    @0 Extensionality? k (a ⊔ b) (a ⊔ b) →
    @0 (∀ x → f x ≡ g x) →
    Is-equivalenceᴱ f ↝[ k ] Is-equivalenceᴱ g
  Is-equivalenceᴱ-cong
    {a = a} {b = b} {f = f} {g = g} ext f≡g =
    generalise-erased-ext?
      (record { to = to f≡g; from = to (sym ⊚ f≡g) })
      (λ ext →
         (∃ λ f⁻¹ → Erased (HA.Proofs f f⁻¹))  ↝⟨ (∃-cong λ _ → Erased-cong-↔ (lemma₁ _ ext)) ⟩□
         (∃ λ f⁻¹ → Erased (HA.Proofs g f⁻¹))  □)
      ext
    where
    to :
      ∀ {a b} {A : Type a} {B : Type b} {@0 f g : A → B} →
      @0 (∀ x → f x ≡ g x) →
      Is-equivalenceᴱ f → Is-equivalenceᴱ g
    to f≡g f-eq@(f⁻¹ , _) =
      ( f⁻¹
      , [ erased $ proj₂ $
          Is-equivalence→Is-equivalenceᴱ $
          Eq.respects-extensional-equality f≡g $
          Is-equivalenceᴱ→Is-equivalence f-eq
        ]
      )

    @0 lemma₂ :
      ∀ f⁻¹ f-f⁻¹ f⁻¹-f f≡g →
      (cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x))
        ≡
      (trans (ext⁻¹ f≡g (f⁻¹ (g x)))
         (cong g (trans (sym (cong f⁻¹ (ext⁻¹ f≡g x))) (f⁻¹-f x))) ≡
       f-f⁻¹ (g x))
    lemma₂ {x = x} f⁻¹ f-f⁻¹ f⁻¹-f = elim¹
      (λ {g} f≡g →
         (cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x))
           ≡
         (trans (ext⁻¹ f≡g (f⁻¹ (g x)))
            (cong g (trans (sym (cong f⁻¹ (ext⁻¹ f≡g x))) (f⁻¹-f x))) ≡
          f-f⁻¹ (g x)))
      (cong (_≡ f-f⁻¹ (f x))
         (cong f (f⁻¹-f x)                                                  ≡⟨ cong (cong f) $ sym $
                                                                               trans (cong (flip trans _) $
                                                                                      trans (cong sym $ cong-refl _) $
                                                                                      sym-refl) $
                                                                               trans-reflˡ _ ⟩

          cong f (trans (sym (cong f⁻¹ (refl (f x)))) (f⁻¹-f x))            ≡⟨ sym $ trans-reflˡ _ ⟩

          trans (refl (f (f⁻¹ (f x))))
            (cong f (trans (sym (cong f⁻¹ (refl (f x)))) (f⁻¹-f x)))        ≡⟨ sym $
                                                                               cong₂ (λ p q →
                                                                                        trans p (cong f (trans (sym (cong f⁻¹ q)) (f⁻¹-f x))))
                                                                                 (ext⁻¹-refl _)
                                                                                 (ext⁻¹-refl _) ⟩∎
          trans (ext⁻¹ (refl f) (f⁻¹ (f x)))
            (cong f (trans (sym (cong f⁻¹ (ext⁻¹ (refl f) x))) (f⁻¹-f x)))  ∎))

    @0 lemma₁ :
      ∀ f⁻¹ →
      Extensionality (a ⊔ b) (a ⊔ b) →
      HA.Proofs f f⁻¹ ↔ HA.Proofs g f⁻¹
    lemma₁ f⁻¹ ext =
      Σ-cong (∀-cong (lower-extensionality a a ext) λ _ →
              ≡⇒≃ $ cong (_≡ _) $ f≡g _) λ f-f⁻¹ →
      Σ-cong (∀-cong (lower-extensionality b b ext) λ _ →
              ≡⇒≃ $ cong (_≡ _) $ cong f⁻¹ $ f≡g _) λ f⁻¹-f →
      ∀-cong (lower-extensionality b a ext) λ x → ≡⇒↝ _
        (cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x)                             ≡⟨ lemma₂ f⁻¹ f-f⁻¹ f⁻¹-f _ ⟩

         trans (ext⁻¹ (ext″ f≡g) (f⁻¹ (g x)))
           (cong g (trans (sym (cong f⁻¹ (ext⁻¹ (ext″ f≡g) x)))
                      (f⁻¹-f x))) ≡
         f-f⁻¹ (g x)                                                ≡⟨ cong (_≡ _) $
                                                                       cong₂ (λ p q →
                                                                                trans (p (f⁻¹ (g x)))
                                                                                  (cong g (trans (sym (cong f⁻¹ (q x))) (f⁻¹-f x))))
                                                                         (_≃_.left-inverse-of (Eq.extensionality-isomorphism ext′) f≡g)
                                                                         (_≃_.left-inverse-of (Eq.extensionality-isomorphism ext′) f≡g) ⟩
         trans (f≡g (f⁻¹ (g x)))
           (cong g (trans (sym (cong f⁻¹ (f≡g x))) (f⁻¹-f x))) ≡
         f-f⁻¹ (g x)                                                ≡⟨ [trans≡]≡[≡trans-symˡ] _ _ _ ⟩

         cong g (trans (sym (cong f⁻¹ (f≡g x))) (f⁻¹-f x)) ≡
         trans (sym (f≡g (f⁻¹ (g x)))) (f-f⁻¹ (g x))                ≡⟨ sym $ cong₂ (λ p q → cong g p ≡ q)
                                                                         subst-trans-sym
                                                                         subst-trans-sym ⟩
         cong g (subst (_≡ x) (cong f⁻¹ (f≡g x)) (f⁻¹-f x)) ≡
         subst (_≡ g x) (f≡g (f⁻¹ (g x))) (f-f⁻¹ (g x))             ≡⟨ cong₂ (λ p q → cong g p ≡ q)
                                                                         (subst-in-terms-of-≡⇒↝ equivalence _ _ _)
                                                                         (subst-in-terms-of-≡⇒↝ equivalence _ _ _) ⟩∎
         cong g (≡⇒→ (cong (_≡ x) (cong f⁻¹ (f≡g x))) (f⁻¹-f x)) ≡
         ≡⇒→ (cong (_≡ g x) (f≡g (f⁻¹ (g x)))) (f-f⁻¹ (g x))        ∎)
      where
      ext′ = lower-extensionality b a ext
      ext″ = apply-ext $ Eq.good-ext ext′

  ----------------------------------------------------------------------
  -- The remaining two-out-of-three properties

  -- If g and g ⊚ f are equivalences with erased proofs, then f is
  -- also an equivalence with erased proofs.

  23→1 :
    Is-equivalenceᴱ g → Is-equivalenceᴱ (g ⊚ f) → Is-equivalenceᴱ f
  23→1 {g = g} {f = f} q r =
    Is-equivalenceᴱ-cong
      _
      (λ x →
         _≃ᴱ_.from ⟨ g , q ⟩ (g (f x))  ≡⟨ _≃ᴱ_.left-inverse-of ⟨ g , q ⟩ (f x) ⟩∎
         f x                            ∎)
      (_≃ᴱ_.is-equivalence (inverse ⟨ _ , q ⟩ ∘ ⟨ _ , r ⟩))

  -- If g ⊚ f and f are equivalences with erased proofs, then g is
  -- also an equivalence with erased proofs.

  31→2 :
    Is-equivalenceᴱ (g ⊚ f) → Is-equivalenceᴱ f → Is-equivalenceᴱ g
  31→2 {g = g} {f = f} r p =
    Is-equivalenceᴱ-cong
      _
      (λ x →
         g (f (_≃ᴱ_.from ⟨ f , p ⟩ x))  ≡⟨ cong g (_≃ᴱ_.right-inverse-of ⟨ f , p ⟩ x) ⟩∎
         g x                            ∎)
      (_≃ᴱ_.is-equivalence (⟨ _ , r ⟩ ∘ inverse ⟨ _ , p ⟩))

  ----------------------------------------------------------------------
  -- The left-to-right and right-to-left components of an equivalence
  -- with erased proofs can be replaced with extensionally equal
  -- functions

  -- The forward direction of an equivalence with erased proofs can be
  -- replaced by an extensionally equal function.

  with-other-function :
    (A≃B : A ≃ᴱ B) (f : A → B) →
    @0 (∀ x → _≃ᴱ_.to A≃B x ≡ f x) →
    A ≃ᴱ B
  with-other-function ⟨ g , is-equivalence ⟩ f g≡f =
    ⟨ f
    , Is-equivalenceᴱ-cong _ g≡f is-equivalence
    ⟩

  _ : _≃ᴱ_.to (with-other-function A≃B f p) ≡ f
  _ = refl _

  _ : _≃ᴱ_.from (with-other-function A≃B f p) ≡ _≃ᴱ_.from A≃B
  _ = refl _

  -- The same applies to the other direction.

  with-other-inverse :
    (A≃B : A ≃ᴱ B) (g : B → A) →
    @0 (∀ x → _≃ᴱ_.from A≃B x ≡ g x) →
    A ≃ᴱ B
  with-other-inverse A≃B g ≡g =
    inverse $ with-other-function (inverse A≃B) g ≡g

  _ : _≃ᴱ_.from (with-other-inverse A≃B g p) ≡ g
  _ = refl _

  _ : _≃ᴱ_.to (with-other-inverse A≃B f p) ≡ _≃ᴱ_.to A≃B
  _ = refl _

  ----------------------------------------------------------------------
  -- Variants of some lemmas from Function-universe

  -- A variant of drop-⊤-left-Σ.

  drop-⊤-left-Σ-≃ᴱ-Erased :
    {P : @0 A → Type p} →
    (A≃⊤ : A ≃ᴱ ⊤) → Σ A (λ x → P x) ≃ᴱ P (_≃ᴱ_.from A≃⊤ tt)
  drop-⊤-left-Σ-≃ᴱ-Erased {A = A} {P = P} A≃⊤ =
    Σ A (λ x → P x)                  ↝⟨ inverse $ Σ-cong-≃ᴱ-Erased (inverse A≃⊤) (λ _ → F.id) ⟩
    Σ ⊤ (λ x → P (_≃ᴱ_.from A≃⊤ x))  ↔⟨ Σ-left-identity ⟩□
    P (_≃ᴱ_.from A≃⊤ tt)             □

  -- A variant of drop-⊤-left-Π.

  drop-⊤-left-Π-≃ᴱ-Erased :
    {A : Type a} {P : @0 A → Type p} →
    @0 Extensionality a p →
    (A≃⊤ : A ≃ᴱ ⊤) →
    ((x : A) → P x) ≃ᴱ P (_≃ᴱ_.from A≃⊤ tt)
  drop-⊤-left-Π-≃ᴱ-Erased {A = A} {P = P} ext A≃⊤ =
    ((x : A) → P x)                  ↝⟨ Π-cong-contra-≃ᴱ-Erased ext (inverse A≃⊤) (λ _ → F.id) ⟩
    ((x : ⊤) → P (_≃ᴱ_.from A≃⊤ x))  ↔⟨ Π-left-identity ⟩□
    P (_≃ᴱ_.from A≃⊤ tt)             □

  ----------------------------------------------------------------------
  -- More conversion lemmas

  -- Some equivalences relating Is-equivalenceᴱ to Is-equivalence.
  --
  -- See also Is-equivalenceᴱ↔Is-equivalence below.

  Erased-Is-equivalenceᴱ≃Erased-Is-equivalence :
    {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
    Erased (Is-equivalenceᴱ f) ≃ Erased (Is-equivalence f)
  Erased-Is-equivalenceᴱ≃Erased-Is-equivalence {f = f} =
    Erased (∃ λ f⁻¹ → Erased (HA.Proofs f f⁻¹))  ↝⟨ Erased-cong-≃ (∃-cong λ _ → Eq.↔⇒≃ $ erased Erased↔) ⟩□
    Erased (∃ λ f⁻¹ → HA.Proofs f f⁻¹)           □

  Erased-Is-equivalence≃Is-equivalenceᴱ :
    {@0 A : Type a} {B : Type b} {@0 f : Erased A → B} →
    Erased (Is-equivalence f) ≃ Is-equivalenceᴱ f
  Erased-Is-equivalence≃Is-equivalenceᴱ {A = A} {B = B} {f = f} =
    Erased (Is-equivalence f)                                  ↔⟨ Erased-cong-↔ (F.inverse $ drop-⊤-right λ _ →
                                                                  _⇔_.to contractible⇔↔⊤ $ other-singleton-contractible _) ⟩
    Erased
      (∃ λ ((f⁻¹′ , _) : Is-equivalence f) →
       ∃ λ (f⁻¹ : B → A) → erased ⊚ f⁻¹′ ≡ f⁻¹)                ↝⟨ Erased-cong-≃ (∃-cong λ _ → ∃-cong λ _ → F.inverse $
                                                                  Eq.≃-≡ →≃→Erased) ⟩
    Erased
      (∃ λ ((f⁻¹′ , _) : Is-equivalence f) →
       ∃ λ (f⁻¹ : B → A) → [_]→ ⊚ erased ⊚ f⁻¹′ ≡ [_]→ ⊚ f⁻¹)  ↔⟨⟩

    Erased
      (∃ λ ((f⁻¹′ , _) : Is-equivalence f) →
       ∃ λ (f⁻¹ : B → A) → f⁻¹′ ≡ [_]→ ⊚ f⁻¹)                  ↔⟨ Erased-cong-↔ ∃-comm ⟩

    Erased
      (∃ λ (f⁻¹ : B → A) →
       ∃ λ ((f⁻¹′ , _) : Is-equivalence f) →
       f⁻¹′ ≡ [_]→ ⊚ f⁻¹)                                      ↔⟨ Erased-cong-↔ (∃-cong λ _ →
                                                                  Σ-assoc F.∘
                                                                  (∃-cong λ _ → ×-comm) F.∘
                                                                  F.inverse Σ-assoc) ⟩
    Erased
      (∃ λ (f⁻¹ : B → A) →
       ∃ λ ((f⁻¹′ , _) :
            ∃ λ (f⁻¹′ : B → Erased A) → f⁻¹′ ≡ [_]→ ⊚ f⁻¹) →
       HA.Proofs f f⁻¹′)                                       ↝⟨ Erased-cong-≃ (∃-cong λ _ → ∃-cong λ (_ , eq) →
                                                                  ≡⇒↝ _ $ cong (HA.Proofs _) eq) ⟩
    Erased
      (∃ λ (f⁻¹ : B → A) →
       (∃ λ (f⁻¹′ : B → Erased A) → f⁻¹′ ≡ [_]→ ⊚ f⁻¹) ×
       HA.Proofs f (λ x → [ f⁻¹ x ]))                          ↔⟨ Erased-cong-↔ (∃-cong λ _ → drop-⊤-left-× λ _ →
                                                                  _⇔_.to contractible⇔↔⊤ $ singleton-contractible _) ⟩

    Erased (∃ λ (f⁻¹ : B → A) → HA.Proofs f ([_]→ ⊚ f⁻¹))      ↔⟨ Erased-Σ↔Σ ⟩

    (∃ λ (f⁻¹ : Erased (B → A)) →
     Erased (HA.Proofs f (λ x → map (_$ x) f⁻¹)))              ↝⟨ (F.Σ-cong Erased-Π↔Π λ _ → F.id) ⟩

    (∃ λ (f⁻¹ : B → Erased A) → Erased (HA.Proofs f f⁻¹))      ↔⟨⟩

    Is-equivalenceᴱ f                                          □
    where
    @0 →≃→Erased : (B → A) ≃ (B → Erased A)
    →≃→Erased = Eq.↔→≃
      (λ f x → [ f x ])
      (λ f x → erased (f x))
      refl
      refl

  ----------------------------------------------------------------------
  -- Variants of some lemmas proved above

  -- Is-equivalenceᴱ f is a proposition if the domain of f is Erased A
  -- (assuming extensionality).

  Is-equivalenceᴱ-propositional-for-Erased :
    @0 Extensionality (a ⊔ b) (a ⊔ b) →
    {@0 A : Type a} {B : Type b} (@0 f : Erased A → B) →
    Is-proposition (Is-equivalenceᴱ f)
  Is-equivalenceᴱ-propositional-for-Erased ext f =
                                                $⟨ H-level-Erased 1 (Eq.propositional ext _) ⟩
    Is-proposition (Erased (Is-equivalence f))  ↝⟨ H-level-cong _ 1 Erased-Is-equivalence≃Is-equivalenceᴱ ⦂ (_ → _) ⟩□
    Is-proposition (Is-equivalenceᴱ f)          □

  -- A variant of to≡to→≡ that is not defined in an erased context.
  -- Note that one side of the equivalence is Erased A.

  to≡to→≡-Erased :
    {@0 A : Type a} {B : Type b} {p q : Erased A ≃ᴱ B} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    _≃ᴱ_.to p ≡ _≃ᴱ_.to q → p ≡ q
  to≡to→≡-Erased {p = ⟨ f , f-eq ⟩} {q = ⟨ g , g-eq ⟩} ext f≡g =
    elim (λ {f g} f≡g → ∀ f-eq g-eq → ⟨ f , f-eq ⟩ ≡ ⟨ g , g-eq ⟩)
         (λ f _ _ →
            cong ⟨ f ,_⟩
              (Is-equivalenceᴱ-propositional-for-Erased ext _ _ _))
         f≡g f-eq g-eq

  -- If f is an equivalence (with erased proofs) from Erased A to B,
  -- then x ≡ y is equivalent (with erased proofs) to f x ≡ f y.

  to≡to≃ᴱ≡-Erased :
    (A≃B : Erased A ≃ᴱ B) →
    (_≃ᴱ_.to A≃B x ≡ _≃ᴱ_.to A≃B y) ≃ᴱ (x ≡ y)
  to≡to≃ᴱ≡-Erased {A = A} {B = B} {x = x} {y = y} A≃B =
    [≃]→≃ᴱ ([proofs] ≡≃≡)
    where
    @0 ≡≃≡ : (_≃ᴱ_.to A≃B x ≡ _≃ᴱ_.to A≃B y) ≃ (x ≡ y)
    ≡≃≡ =
      Eq.with-other-function
        (Eq.≃-≡ (≃ᴱ→≃ A≃B))
        (λ eq →
           x                              ≡⟨ sym $ []-cong [ cong erased (_≃ᴱ_.left-inverse-of A≃B x) ] ⟩
           _≃ᴱ_.from A≃B (_≃ᴱ_.to A≃B x)  ≡⟨ cong (_≃ᴱ_.from A≃B) eq ⟩
           _≃ᴱ_.from A≃B (_≃ᴱ_.to A≃B y)  ≡⟨ []-cong [ cong erased (_≃ᴱ_.left-inverse-of A≃B y) ] ⟩∎
           y                              ∎)
        (λ eq →
           let f = _≃ᴱ_.left-inverse-of A≃B in
           trans (sym (f x)) (trans (cong (_≃ᴱ_.from A≃B) eq) (f y))  ≡⟨ cong₂ (λ p q → trans (sym p) (trans (cong (_≃ᴱ_.from A≃B) eq) q))
                                                                           (sym $ _≃_.right-inverse-of ≡≃[]≡[] _)
                                                                           (sym $ _≃_.right-inverse-of ≡≃[]≡[] _) ⟩∎
           trans (sym ([]-cong [ cong erased (f x) ]))
              (trans (cong (_≃ᴱ_.from A≃B) eq)
                 ([]-cong [ cong erased (f y) ]))                     ∎)

  ----------------------------------------------------------------------
  -- More lemmas

  -- An equivalence relating Is-equivalenceᴱ to Is-equivalence.

  Is-equivalenceᴱ↔Is-equivalence :
    {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    Is-equivalenceᴱ (map f) ↝[ k ] Is-equivalence (map f)
  Is-equivalenceᴱ↔Is-equivalence
    {a = a} {k = k} {f = f} =
    generalise-ext?-prop
      (Is-equivalenceᴱ (map f)                                        ↝⟨ Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP ⟩
       (∀ y → Contractibleᴱ (map f ⁻¹ᴱ y))                            ↔⟨⟩
       (∀ y → Contractibleᴱ (∃ λ x → Erased ([ f (erased x) ] ≡ y)))  ↝⟨ (∀-cong _ λ _ → ECP.[]-cong.Contractibleᴱ-cong ax _ (Eq.↔⇒≃ $ F.inverse Erased-Σ↔Σ)) ⟩
       (∀ y → Contractibleᴱ (Erased (∃ λ x → [ f x ] ≡ y)))           ↝⟨ (∀-cong _ λ _ → ECP.[]-cong.Contractibleᴱ-Erased↔Contractible-Erased ax _) ⟩
       (∀ y → Contractible (Erased (∃ λ x → [ f x ] ≡ y)))            ↝⟨ (∀-cong _ λ _ → H-level-cong _ 0 Erased-Σ↔Σ) ⟩
       (∀ y → Contractible (∃ λ x → Erased (map f x ≡ y)))            ↔⟨⟩
       (∀ y → Contractible (map f ⁻¹ᴱ y))                             ↝⟨ (∀-cong _ λ _ → H-level-cong _ 0 $ ECP.[]-cong.⁻¹ᴱ[]↔⁻¹[] ax) ⟩
       (∀ y → Contractible (map f ⁻¹ y))                              ↝⟨ inverse-ext? Is-equivalence≃Is-equivalence-CP _ ⟩□
       Is-equivalence (map f)                                         □)
      (λ ext → Is-equivalenceᴱ-propositional-for-Erased ext _)
      (λ ext → Eq.propositional ext _)

  -- Erased "commutes" with Is-equivalenceᴱ (assuming extensionality).

  Erased-Is-equivalenceᴱ↔Is-equivalenceᴱ :
    {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
    @0 Extensionality? k (a ⊔ b) (a ⊔ b) →
    Erased (Is-equivalenceᴱ f) ↝[ k ] Is-equivalenceᴱ (map f)
  Erased-Is-equivalenceᴱ↔Is-equivalenceᴱ
    {a = a} {b = b} {k = k} {A = A} {B = B} {f = f} ext =
    Erased (Is-equivalenceᴱ f)                                          ↔⟨ Erased-Is-equivalenceᴱ≃Erased-Is-equivalence ⟩

    Erased (Is-equivalence f)                                           ↝⟨ Erased-cong? (lemma _) ext ⟩

    Erased (Is-equivalence (map f))                                     ↔⟨⟩

    Erased (∃ λ (f⁻¹ : Erased B → Erased A) → HA.Proofs (map f) f⁻¹)    ↔⟨ Erased-cong-↔ (Σ-cong (F.inverse Erased-Π↔Π-Erased) λ _ → F.id) ⟩

    Erased (∃ λ (f⁻¹ : Erased (B → A)) →
              HA.Proofs (map f) (map (erased f⁻¹)))                     ↔⟨ Erased-cong-↔ (Σ-cong (erased Erased↔) λ _ → F.id) ⟩

    Erased (∃ λ (f⁻¹ : B → A) → HA.Proofs (map f) (map f⁻¹))            ↔⟨ Erased-Σ↔Σ ⟩

    (∃ λ (f⁻¹ : Erased (B → A)) →
       Erased (HA.Proofs (map f) (map (erased f⁻¹))))                   ↔⟨ (Σ-cong Erased-Π↔Π-Erased λ _ → Eq.id) ⟩

    (∃ λ (f⁻¹ : Erased B → Erased A) → Erased (HA.Proofs (map f) f⁻¹))  ↔⟨⟩

    Is-equivalenceᴱ (map f)                                             □
    where
    @0 lemma : ∀ k → Extensionality? k (a ⊔ b) (a ⊔ b) → _ ↝[ k ] _
    lemma k ext =
      Is-equivalence f                              ↝⟨ Is-equivalence≃Is-equivalence-CP ext ⟩
      ((y : B) → Contractible (f ⁻¹ y))             ↝⟨ (Π-cong (lower-extensionality? k a lzero ext)
                                                          (F.inverse $ erased Erased↔) λ _ →
                                                        H-level-cong ext 0 $
                                                        Σ-cong (F.inverse $ erased Erased↔) λ _ →
                                                        ≡≃[]≡[]) ⟩
      ((y : Erased B) → Contractible (map f ⁻¹ y))  ↝⟨ inverse-ext? Is-equivalence≃Is-equivalence-CP ext ⟩
      Is-equivalence (map f)                        □
