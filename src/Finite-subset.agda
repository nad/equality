------------------------------------------------------------------------
-- Finite subsets
------------------------------------------------------------------------

-- Based on Frumin, Geuvers, Gondelman and van der Weide's "Finite
-- Sets in Homotopy Type Theory".

{-# OPTIONS --cubical --safe #-}

open import Equality

module Finite-subset {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq hiding (elim)

import Equality.Path as P
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; ∣_∣)
open import Monad eq as M using (Raw-monad; Monad)
open import Surjection eq using (_↠_)
import Univalence-axiom eq as Univ

private
  variable
    a b p     : Level
    A B       : Set a
    P         : A → Set p
    f g       : (x : A) → P x
    l H x y z : A
    m n       : ℕ

------------------------------------------------------------------------
-- Kuratowski finite subsets

-- Kuratowski finite subsets of a given type.

infixr 5 _∪_

data Finite-subset-of (A : Set a) : Set a where
  ∅         : Finite-subset-of A
  singleton : A → Finite-subset-of A
  _∪_       : Finite-subset-of A → Finite-subset-of A →
              Finite-subset-of A
  ∅∪ᴾ       : ∅ ∪ x P.≡ x
  idem-sᴾ   : singleton x ∪ singleton x P.≡ singleton x
  assocᴾ    : x ∪ (y ∪ z) P.≡ (x ∪ y) ∪ z
  commᴾ     : x ∪ y P.≡ y ∪ x
  is-setᴾ   : P.Is-set (Finite-subset-of A)

-- Variants of some of the constructors.

∅∪ : ∅ ∪ x ≡ x
∅∪ = _↔_.from ≡↔≡ ∅∪ᴾ

idem-s : singleton x ∪ singleton x ≡ singleton x
idem-s = _↔_.from ≡↔≡ idem-sᴾ

assoc : x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
assoc = _↔_.from ≡↔≡ assocᴾ

comm : x ∪ y ≡ y ∪ x
comm = _↔_.from ≡↔≡ commᴾ

is-set : Is-set (Finite-subset-of A)
is-set = _↔_.from (H-level↔H-level 2) is-setᴾ

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ {A : Set a} (P : Finite-subset-of A → Set p) :
             Set (a ⊔ p) where
  field
    ∅ʳ         : P ∅
    singletonʳ : ∀ x → P (singleton x)
    ∪ʳ         : P x → P y → P (x ∪ y)
    ∅∪ʳ        : (p : P x) →
                 P.[ (λ i → P (∅∪ᴾ {x = x} i)) ] ∪ʳ ∅ʳ p ≡ p
    idem-sʳ    : ∀ x →
                 P.[ (λ i → P (idem-sᴾ {x = x} i)) ]
                   ∪ʳ (singletonʳ x) (singletonʳ x) ≡ singletonʳ x
    assocʳ     : (p : P x) (q : P y) (r : P z) →
                 P.[ (λ i → P (assocᴾ {x = x} {y = y} {z = z} i)) ]
                   ∪ʳ p (∪ʳ q r) ≡ ∪ʳ (∪ʳ p q) r
    commʳ      : (p : P x) (q : P y) →
                 P.[ (λ i → P (commᴾ {x = x} {y = y} i)) ]
                   ∪ʳ p q ≡ ∪ʳ q p
    is-setʳ    : ∀ x → P.Is-set (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : Finite-subset-of A) → P x
elimᴾ {A = A} {P = P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : Finite-subset-of A) → P x
  helper ∅                                  = E.∅ʳ
  helper (singleton x)                      = E.singletonʳ x
  helper (x ∪ y)                            = E.∪ʳ (helper x) (helper y)
  helper (∅∪ᴾ {x = x} i)                    = E.∅∪ʳ (helper x) i
  helper (idem-sᴾ i)                        = E.idem-sʳ _ i
  helper (assocᴾ {x = x} {y = y} {z = z} i) = E.assocʳ
                                                (helper x) (helper y)
                                                (helper z) i
  helper (commᴾ {x = x} {y = y} i)          = E.commʳ
                                                (helper x) (helper y) i
  helper (is-setᴾ x y i j)                  =
    P.heterogeneous-UIP E.is-setʳ (is-setᴾ x y)
      (λ i → helper (x i)) (λ i → helper (y i)) i j

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    ∅ʳ         : B
    singletonʳ : A → B
    ∪ʳ         : Finite-subset-of A → Finite-subset-of A → B → B → B
    ∅∪ʳ        : ∀ x p → ∪ʳ ∅ x ∅ʳ p P.≡ p
    idem-sʳ    : ∀ x →
                 ∪ʳ (singleton x) (singleton x)
                    (singletonʳ x) (singletonʳ x) P.≡
                 singletonʳ x
    assocʳ     : ∀ p q r →
                 ∪ʳ x (y ∪ z) p (∪ʳ y z q r) P.≡
                 ∪ʳ (x ∪ y) z (∪ʳ x y p q) r
    commʳ      : ∀ p q → ∪ʳ x y p q P.≡ ∪ʳ y x q p
    is-setʳ    : P.Is-set B

open Recᴾ public

recᴾ : Recᴾ A B → Finite-subset-of A → B
recᴾ r = elimᴾ e
  where
  module R = Recᴾ r

  e : Elimᴾ _
  e .∅ʳ                 = R.∅ʳ
  e .singletonʳ         = R.singletonʳ
  e .∪ʳ {x = x} {y = y} = R.∪ʳ x y
  e .∅∪ʳ {x = x}        = R.∅∪ʳ x
  e .idem-sʳ            = R.idem-sʳ
  e .assocʳ             = R.assocʳ
  e .commʳ              = R.commʳ
  e .is-setʳ _          = R.is-setʳ

-- A dependent eliminator, expressed using equality.

record Elim {A : Set a} (P : Finite-subset-of A → Set p) :
            Set (a ⊔ p) where
  field
    ∅ʳ         : P ∅
    singletonʳ : ∀ x → P (singleton x)
    ∪ʳ         : P x → P y → P (x ∪ y)
    ∅∪ʳ        : (p : P x) → subst P (∅∪ {x = x}) (∪ʳ ∅ʳ p) ≡ p
    idem-sʳ    : ∀ x →
                 subst P (idem-s {x = x})
                         (∪ʳ (singletonʳ x) (singletonʳ x)) ≡
                 singletonʳ x
    assocʳ     : (p : P x) (q : P y) (r : P z) →
                 subst P (assoc {x = x} {y = y} {z = z})
                         (∪ʳ p (∪ʳ q r)) ≡
                 ∪ʳ (∪ʳ p q) r
    commʳ      : (p : P x) (q : P y) →
                 subst P (comm {x = x} {y = y}) (∪ʳ p q) ≡ ∪ʳ q p
    is-setʳ    : ∀ x → Is-set (P x)

open Elim public

elim : Elim P → (x : Finite-subset-of A) → P x
elim e = elimᴾ e′
  where
  module E = Elim e

  e′ : Elimᴾ _
  e′ .∅ʳ           = E.∅ʳ
  e′ .singletonʳ   = E.singletonʳ
  e′ .∪ʳ           = E.∪ʳ
  e′ .∅∪ʳ p        = subst≡→[]≡ (E.∅∪ʳ p)
  e′ .idem-sʳ x    = subst≡→[]≡ (E.idem-sʳ x)
  e′ .assocʳ p q r = subst≡→[]≡ (E.assocʳ p q r)
  e′ .commʳ p q    = subst≡→[]≡ (E.commʳ p q)
  e′ .is-setʳ x    = _↔_.to (H-level↔H-level 2) (E.is-setʳ x)

-- A non-dependent eliminator, expressed using equality.

record Rec (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    ∅ʳ         : B
    singletonʳ : A → B
    ∪ʳ         : Finite-subset-of A → Finite-subset-of A → B → B → B
    ∅∪ʳ        : ∀ x p → ∪ʳ ∅ x ∅ʳ p ≡ p
    idem-sʳ    : ∀ x →
                 ∪ʳ (singleton x) (singleton x)
                    (singletonʳ x) (singletonʳ x) ≡
                 singletonʳ x
    assocʳ     : ∀ p q r →
                 ∪ʳ x (y ∪ z) p (∪ʳ y z q r) ≡
                 ∪ʳ (x ∪ y) z (∪ʳ x y p q) r
    commʳ      : ∀ p q → ∪ʳ x y p q ≡ ∪ʳ y x q p
    is-setʳ    : Is-set B

open Rec public

rec : Rec A B → Finite-subset-of A → B
rec r = recᴾ r′
  where
  module R = Rec r

  r′ : Recᴾ _ _
  r′ .∅ʳ           = R.∅ʳ
  r′ .singletonʳ   = R.singletonʳ
  r′ .∪ʳ           = R.∪ʳ
  r′ .∅∪ʳ x p      = _↔_.to ≡↔≡ (R.∅∪ʳ x p)
  r′ .idem-sʳ x    = _↔_.to ≡↔≡ (R.idem-sʳ x)
  r′ .assocʳ p q r = _↔_.to ≡↔≡ (R.assocʳ p q r)
  r′ .commʳ p q    = _↔_.to ≡↔≡ (R.commʳ p q)
  r′ .is-setʳ      = _↔_.to (H-level↔H-level 2) R.is-setʳ

-- A dependent eliminator for propositions.

record Elim-prop {A : Set a} (P : Finite-subset-of A → Set p) :
                 Set (a ⊔ p) where
  field
    ∅ʳ              : P ∅
    singletonʳ      : ∀ x → P (singleton x)
    ∪ʳ              : P x → P y → P (x ∪ y)
    is-propositionʳ : ∀ x → Is-proposition (P x)

open Elim-prop public

elim-prop : Elim-prop P → (x : Finite-subset-of A) → P x
elim-prop e = elim e′
  where
  module E = Elim-prop e

  e′ : Elim _
  e′ .∅ʳ           = E.∅ʳ
  e′ .singletonʳ   = E.singletonʳ
  e′ .∪ʳ           = E.∪ʳ
  e′ .∅∪ʳ _        = E.is-propositionʳ _ _ _
  e′ .idem-sʳ _    = E.is-propositionʳ _ _ _
  e′ .assocʳ _ _ _ = E.is-propositionʳ _ _ _
  e′ .commʳ _ _    = E.is-propositionʳ _ _ _
  e′ .is-setʳ _    = mono₁ 1 (E.is-propositionʳ _)

-- A non-dependent eliminator for propositions.

record Rec-prop (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    ∅ʳ              : B
    singletonʳ      : A → B
    ∪ʳ              : Finite-subset-of A → Finite-subset-of A →
                      B → B → B
    is-propositionʳ : Is-proposition B

open Rec-prop public

rec-prop : Rec-prop A B → Finite-subset-of A → B
rec-prop r = elim-prop e
  where
  module R = Rec-prop r

  e : Elim-prop _
  e .∅ʳ                 = R.∅ʳ
  e .singletonʳ         = R.singletonʳ
  e .∪ʳ {x = x} {y = y} = R.∪ʳ x y
  e .is-propositionʳ _  = R.is-propositionʳ

------------------------------------------------------------------------
-- Some derived laws

-- ∅ is a right identity for _∪_.

∪∅ : x ∪ ∅ ≡ x
∪∅ {x = x} =
  x ∪ ∅  ≡⟨ comm ⟩
  ∅ ∪ x  ≡⟨ ∅∪ ⟩∎
  x      ∎

-- Union is idempotent.

idem : x ∪ x ≡ x
idem {x = x} = elim-prop e x
  where
  e : Elim-prop (λ x → x ∪ x ≡ x)
  e .∅ʳ =
    ∅ ∪ ∅  ≡⟨ ∅∪ ⟩∎
    ∅      ∎

  e .singletonʳ x =
    singleton x ∪ singleton x  ≡⟨ idem-s ⟩∎
    singleton x                ∎

  e .∪ʳ {x = x} {y = y} p q =
    (x ∪ y) ∪ (x ∪ y)  ≡⟨ sym assoc ⟩
    x ∪ (y ∪ (x ∪ y))  ≡⟨ cong (x ∪_) assoc ⟩
    x ∪ ((y ∪ x) ∪ y)  ≡⟨ cong ((x ∪_) ∘ (_∪ y)) comm ⟩
    x ∪ ((x ∪ y) ∪ y)  ≡⟨ cong (x ∪_) (sym assoc) ⟩
    x ∪ (x ∪ (y ∪ y))  ≡⟨ assoc ⟩
    (x ∪ x) ∪ (y ∪ y)  ≡⟨ cong₂ _∪_ p q ⟩∎
    x ∪ y              ∎

  e .is-propositionʳ = λ _ → is-set

------------------------------------------------------------------------
-- Some operations

-- A map function.

map : (A → B) → Finite-subset-of A → Finite-subset-of B
map f = recᴾ r
  where
  r : Recᴾ _ _
  r .∅ʳ           = ∅
  r .singletonʳ x = singleton (f x)
  r .∪ʳ _ _       = _∪_
  r .∅∪ʳ _ _      = ∅∪ᴾ
  r .idem-sʳ _    = idem-sᴾ
  r .assocʳ _ _ _ = assocᴾ
  r .commʳ _ _    = commᴾ
  r .is-setʳ      = is-setᴾ

-- A filter function.

filter : (A → Bool) → Finite-subset-of A → Finite-subset-of A
filter p = rec r
  where
  r : Rec _ _
  r .∅ʳ           = ∅
  r .singletonʳ x = if p x then singleton x else ∅
  r .∪ʳ _ _       = _∪_
  r .∅∪ʳ _ _      = ∅∪
  r .idem-sʳ _    = idem
  r .assocʳ _ _ _ = assoc
  r .commʳ _ _    = comm
  r .is-setʳ      = is-set

-- Join.

join : Finite-subset-of (Finite-subset-of A) → Finite-subset-of A
join = rec r
  where
  r : Rec _ _
  r .∅ʳ           = ∅
  r .singletonʳ   = id
  r .∪ʳ _ _       = _∪_
  r .∅∪ʳ _ _      = ∅∪
  r .idem-sʳ _    = idem
  r .assocʳ _ _ _ = assoc
  r .commʳ _ _    = comm
  r .is-setʳ      = is-set

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ :
  Finite-subset-of A → (A → Finite-subset-of B) → Finite-subset-of B
x >>=′ f = join (map f x)

-- Bind distributes from the right over union.

_ : (x ∪ y) >>=′ f ≡ (x >>=′ f) ∪ (y >>=′ f)
_ = refl _

-- Bind distributes from the left over union.

>>=-left-distributive :
  ∀ x → (x >>=′ λ x → f x ∪ g x) ≡ (x >>=′ f) ∪ (x >>=′ g)
>>=-left-distributive {f = f} {g = g} = elim-prop e
  where
  e : Elim-prop _
  e .∅ʳ                           = ∅      ≡⟨ sym idem ⟩∎
                                    ∅ ∪ ∅  ∎
  e .singletonʳ _                 = refl _
  e .is-propositionʳ _            = is-set
  e .∪ʳ {x = x} {y = y} hyp₁ hyp₂ =
    (x ∪ y) >>=′ (λ x → f x ∪ g x)                         ≡⟨⟩
    (x >>=′ λ x → f x ∪ g x) ∪ (y >>=′ λ x → f x ∪ g x)    ≡⟨ cong₂ _∪_ hyp₁ hyp₂ ⟩
    ((x >>=′ f) ∪ (x >>=′ g)) ∪ ((y >>=′ f) ∪ (y >>=′ g))  ≡⟨ sym assoc ⟩
    (x >>=′ f) ∪ ((x >>=′ g) ∪ ((y >>=′ f) ∪ (y >>=′ g)))  ≡⟨ cong ((x >>=′ f) ∪_) assoc ⟩
    (x >>=′ f) ∪ (((x >>=′ g) ∪ (y >>=′ f)) ∪ (y >>=′ g))  ≡⟨ cong (((x >>=′ f) ∪_) ∘ (_∪ (y >>=′ g))) comm ⟩
    (x >>=′ f) ∪ (((y >>=′ f) ∪ (x >>=′ g)) ∪ (y >>=′ g))  ≡⟨ cong ((x >>=′ f) ∪_) (sym assoc) ⟩
    (x >>=′ f) ∪ ((y >>=′ f) ∪ ((x >>=′ g) ∪ (y >>=′ g)))  ≡⟨ assoc ⟩
    ((x >>=′ f) ∪ (y >>=′ f)) ∪ ((x >>=′ g) ∪ (y >>=′ g))  ≡⟨⟩
    ((x ∪ y) >>=′ f) ∪ ((x ∪ y) >>=′ g)                    ∎

-- Monad laws.

_ : singleton x >>=′ f ≡ f x
_ = refl _

>>=-singleton : x >>=′ singleton ≡ x
>>=-singleton = elim-prop e _
  where
  e : Elim-prop (λ x → x >>=′ singleton ≡ x)
  e .∅ʳ                           = refl _
  e .singletonʳ _                 = refl _
  e .is-propositionʳ _            = is-set
  e .∪ʳ {x = x} {y = y} hyp₁ hyp₂ =
    (x ∪ y) >>=′ singleton                   ≡⟨⟩
    (x >>=′ singleton) ∪ (y >>=′ singleton)  ≡⟨ cong₂ _∪_ hyp₁ hyp₂ ⟩∎
    x ∪ y                                    ∎

>>=-assoc : ∀ x → x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
>>=-assoc {f = f} {g = g} = elim-prop e
  where
  e : Elim-prop _
  e .∅ʳ                           = refl _
  e .singletonʳ _                 = refl _
  e .is-propositionʳ _            = is-set
  e .∪ʳ {x = x} {y = y} hyp₁ hyp₂ =
    (x ∪ y) >>=′ (λ x → f x >>=′ g)                        ≡⟨⟩
    (x >>=′ λ x → f x >>=′ g) ∪ (y >>=′ λ x → f x >>=′ g)  ≡⟨ cong₂ _∪_ hyp₁ hyp₂ ⟩
    (x >>=′ f >>=′ g) ∪ (y >>=′ f >>=′ g)                  ≡⟨⟩
    (x ∪ y) >>=′ f >>=′ g                                  ∎

-- A monad instance.

instance

  raw-monad : Raw-monad {d = a} Finite-subset-of
  raw-monad .M.return = singleton
  raw-monad .M._>>=_  = _>>=′_

  monad : Monad {d = a} Finite-subset-of
  monad .M.Monad.raw-monad           = raw-monad
  monad .M.Monad.left-identity _ _   = refl _
  monad .M.Monad.right-identity _    = >>=-singleton
  monad .M.Monad.associativity x _ _ = >>=-assoc x

------------------------------------------------------------------------
-- Membership

private

  -- Membership is used to define _∈_ and ∈-propositional below.

  Membership : {A : Set a} → A → Finite-subset-of A → Proposition a
  Membership x = rec r
    where
    r : Rec _ _
    r .∅ʳ = ⊥ , ⊥-propositional

    r .singletonʳ y = ∥ x ≡ y ∥ , Trunc.truncation-is-proposition

    r .∪ʳ _ _ (x∈₁ , _) (x∈₂ , _) =
      ∥ x∈₁ ⊎ x∈₂ ∥ , Trunc.truncation-is-proposition

    r .∅∪ʳ x (P , P-prop) =
      _↔_.to (ignore-propositional-component
                (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ
        (∥ ⊥ ⊎ P ∥  ↔⟨ Trunc.∥∥-cong ⊎-left-identity ⟩
         ∥ P ∥      ↔⟨ Trunc.∥∥↔ P-prop ⟩□
         P          □)

    r .idem-sʳ y =
      _↔_.to (ignore-propositional-component
                (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ
        (∥ ∥ x ≡ y ∥ ⊎ ∥ x ≡ y ∥ ∥  ↔⟨ Trunc.idempotent ⟩
         ∥ ∥ x ≡ y ∥ ∥              ↔⟨ Trunc.flatten ⟩□
         ∥ x ≡ y ∥                  □)

    r .assocʳ (P , P-prop) (Q , Q-prop) (R , R-prop) =
      _↔_.to (ignore-propositional-component
                (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ
        (∥ P ⊎ ∥ Q ⊎ R ∥ ∥  ↔⟨ Trunc.flatten′ (λ F → P ⊎ F (Q ⊎ R))
                                              (λ f → ⊎-map id f)
                                              [ ∣_∣ ∘ inj₁ , Trunc.∥∥-map inj₂ ] ⟩
         ∥ P ⊎ (Q ⊎ R) ∥    ↔⟨ Trunc.∥∥-cong ⊎-assoc ⟩
         ∥ (P ⊎ Q) ⊎ R ∥    ↔⟨ inverse $ Trunc.flatten′ (λ F → F (P ⊎ Q) ⊎ R)
                                                        (λ f → ⊎-map f id)
                                                        [ Trunc.∥∥-map inj₁ , ∣_∣ ∘ inj₂ ] ⟩□
         ∥ ∥ P ⊎ Q ∥ ⊎ R ∥  □)

    r .commʳ (P , P-prop) (Q , Q-prop) =
      _↔_.to (ignore-propositional-component
                (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ
        (∥ P ⊎ Q ∥  ↔⟨ Trunc.∥∥-cong ⊎-comm ⟩□
         ∥ Q ⊎ P ∥  □)

    r .is-setʳ = Univ.∃-H-level-H-level-1+ ext univ 1

-- Membership.

infix 4 _∈_

_∈_ : {A : Set a} → A → Finite-subset-of A → Set a
x ∈ y = proj₁ (Membership x y)

-- Membership is propositional.

∈-propositional : ∀ y → Is-proposition (x ∈ y)
∈-propositional y = proj₂ (Membership _ y)

-- Some unit tests documenting the computational behaviour of _∈_.

_ : (x ∈ ∅) ≡ ⊥
_ = refl _

_ : (x ∈ singleton y) ≡ ∥ x ≡ y ∥
_ = refl _

_ : (x ∈ y ∪ z) ≡ ∥ x ∈ y ⊎ x ∈ z ∥
_ = refl _

-- If truncated equality is decidable, then membership is also
-- decidable.

member? :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x : A) (y : Finite-subset-of A) → Dec (x ∈ y)
member? equal? x = elim-prop e
  where
  e : Elim-prop _
  e .∅ʳ                   = no λ ()
  e .singletonʳ           = equal? x
  e .∪ʳ {x = y₁} {y = y₂} =
    [ (λ x∈y₁ _ → yes ∣ inj₁ x∈y₁ ∣)
    , (λ x∉y₁ →
         [ (λ x∈y₂ → yes ∣ inj₂ x∈y₂ ∣)
         , (λ x∉y₂ → no (
              x ∈ y₁ ∪ y₂          ↔⟨⟩
              ∥ x ∈ y₁ ⊎ x ∈ y₂ ∥  ↝⟨ Trunc.∥∥-map [ x∉y₁ , x∉y₂ ] ⟩
              ∥ ⊥ ∥                ↔⟨ Trunc.not-inhabited⇒∥∥↔⊥ id ⟩□
              ⊥                    □))
         ])
    ]
  e .is-propositionʳ y =
    Dec-closure-propositional ext (∈-propositional y)

-- Subsets.

_⊆_ : {A : Set a} → Finite-subset-of A → Finite-subset-of A → Set a
x ⊆ y = ∀ z → z ∈ x → z ∈ y

-- The subset property can be expressed using _∪_ and _≡_.

⊆≃∪≡ : (x ⊆ y) ≃ (x ∪ y ≡ y)
⊆≃∪≡ {x = x} {y = y} =
  _↠_.from
    (Eq.≃↠⇔
       (Π-closure ext 1 λ _ →
        Π-closure ext 1 λ _ →
        ∈-propositional y)
       is-set)
    (record
       { from = λ p z →
           z ∈ x      ↝⟨ ∣_∣ ∘ inj₁ ⟩
           z ∈ x ∪ y  ↝⟨ ≡⇒↝ _ (cong (z ∈_) p) ⟩□
           z ∈ y      □
       ; to = elim-prop e _
       })
  where
  e′ : Elim-prop (λ y → ∀ x → x ∈ y → singleton x ∪ y ≡ y)
  e′ .singletonʳ y x =
    Trunc.rec is-set λ x≡y →
      singleton x ∪ singleton y  ≡⟨ cong (λ x → singleton x ∪ _) x≡y ⟩
      singleton y ∪ singleton y  ≡⟨ idem-s ⟩∎
      singleton y                ∎

  e′ .∪ʳ {x = y₁} {y = y₂} hyp₁ hyp₂ z =
    Trunc.rec is-set
      [ (λ z∈y₁ →
           singleton z ∪ (y₁ ∪ y₂)  ≡⟨ assoc ⟩
           (singleton z ∪ y₁) ∪ y₂  ≡⟨ cong (_∪ _) (hyp₁ z z∈y₁) ⟩∎
           y₁ ∪ y₂                  ∎)
      , (λ z∈y₂ →
           singleton z ∪ (y₁ ∪ y₂)  ≡⟨ assoc ⟩
           (singleton z ∪ y₁) ∪ y₂  ≡⟨ cong (_∪ y₂) comm ⟩
           (y₁ ∪ singleton z) ∪ y₂  ≡⟨ sym assoc ⟩
           y₁ ∪ (singleton z ∪ y₂)  ≡⟨ cong (_ ∪_) (hyp₂ z z∈y₂) ⟩∎
           y₁ ∪ y₂                  ∎)
      ]

  e′ .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    is-set

  e : Elim-prop (λ x → x ⊆ y → x ∪ y ≡ y)
  e .∅ʳ _ =
    ∅ ∪ y  ≡⟨ ∅∪ ⟩∎
    y      ∎

  e .singletonʳ x x⊆y =
    singleton x ∪ y  ≡⟨ elim-prop e′ y x (x⊆y x ∣ refl _ ∣) ⟩∎
    y                ∎

  e .∪ʳ {x = x₁} {y = x₂} hyp₁ hyp₂ x₁∪x₂⊆y =
    (x₁ ∪ x₂) ∪ y  ≡⟨ sym assoc ⟩
    x₁ ∪ (x₂ ∪ y)  ≡⟨ cong (x₁ ∪_) (hyp₂ (λ z → x₁∪x₂⊆y z ∘ ∣_∣ ∘ inj₂)) ⟩
    x₁ ∪ y         ≡⟨ hyp₁ (λ z → x₁∪x₂⊆y z ∘ ∣_∣ ∘ inj₁) ⟩∎
    y              ∎

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    is-set

-- Extensionality.

extensionality :
  (x ≡ y) ≃ (∀ z → z ∈ x ⇔ z ∈ y)
extensionality {x = x} {y = y} =
  _↠_.from
    (Eq.≃↠⇔
       is-set
       (Π-closure ext 1 λ _ →
        ⇔-closure ext 1
          (∈-propositional x)
          (∈-propositional y)))
    (record
       { to   = λ x≡y z → ≡⇒↝ _ (cong (z ∈_) x≡y)
       ; from =
           (∀ z → z ∈ x ⇔ z ∈ y)  ↝⟨ (λ p → _⇔_.to ∘ p , _⇔_.from ∘ p) ⟩
           x ⊆ y × y ⊆ x          ↔⟨ ⊆≃∪≡ ×-cong ⊆≃∪≡ ⟩
           x ∪ y ≡ y × y ∪ x ≡ x  ↝⟨ (λ (p , q) → trans (sym q) (trans comm p)) ⟩□
           x ≡ y                  □
       })

------------------------------------------------------------------------
-- Listed finite subsets

-- The following definitions are not exported, they are used to define
-- a new eliminator for Finite-subset-of.

private

  -- Listed finite subsets of a given type.

  infixr 5 _∷_

  data Listed-finite-subset-of (A : Set a) : Set a where
    []      : Listed-finite-subset-of A
    _∷_     : A → Listed-finite-subset-of A → Listed-finite-subset-of A
    dropᴸᴾ  : x ∷ x ∷ y P.≡ x ∷ y
    swapᴸᴾ  : x ∷ y ∷ z P.≡ y ∷ x ∷ z
    is-setᴾ : P.Is-set (Listed-finite-subset-of A)

  -- Some laws.

  dropᴸ :
    {x : A} {y : Listed-finite-subset-of A} →
    x ∷ x ∷ y ≡ x ∷ y
  dropᴸ = _↔_.from ≡↔≡ dropᴸᴾ

  swapᴸ :
    {x y : A} {z : Listed-finite-subset-of A} →
    x ∷ y ∷ z ≡ y ∷ x ∷ z
  swapᴸ = _↔_.from ≡↔≡ swapᴸᴾ

  is-setᴸ : Is-set (Listed-finite-subset-of A)
  is-setᴸ =
    _↔_.from (H-level↔H-level 2) Listed-finite-subset-of.is-setᴾ

  -- A dependent eliminator, expressed using paths.

  record Elimᴸᴾ {A : Set a} (P : Listed-finite-subset-of A → Set p) :
                Set (a ⊔ p) where
    field
      []ʳ     : P []
      ∷ʳ      : ∀ x → P y → P (x ∷ y)
      dropʳ   : ∀ x (p : P y) →
                P.[ (λ i → P (dropᴸᴾ {x = x} {y = y} i)) ]
                  ∷ʳ x (∷ʳ x p) ≡ ∷ʳ x p
      swapʳ   : ∀ x y (p : P z) →
                P.[ (λ i → P (swapᴸᴾ {x = x} {y = y} {z = z} i)) ]
                  ∷ʳ x (∷ʳ y p) ≡ ∷ʳ y (∷ʳ x p)
      is-setʳ : ∀ x → P.Is-set (P x)

  open Elimᴸᴾ

  elimᴸᴾ : Elimᴸᴾ P → (x : Listed-finite-subset-of A) → P x
  elimᴸᴾ {A = A} {P = P} e = helper
    where
    module E = Elimᴸᴾ e

    helper : (x : Listed-finite-subset-of A) → P x
    helper []      = E.[]ʳ
    helper (x ∷ y) = E.∷ʳ x (helper y)

    helper (dropᴸᴾ {x = x} {y = y} i) =
      E.dropʳ x (helper y) i

    helper (swapᴸᴾ {x = x} {y = y} {z = z} i) =
      E.swapʳ x y (helper z) i

    helper (is-setᴾ x y i j) =
      P.heterogeneous-UIP
        E.is-setʳ (Listed-finite-subset-of.is-setᴾ x y)
        (λ i → helper (x i)) (λ i → helper (y i)) i j

  -- A non-dependent eliminator, expressed using paths.

  record Recᴸᴾ (A : Set a) (B : Set b) : Set (a ⊔ b) where
    field
      []ʳ     : B
      ∷ʳ      : A → Listed-finite-subset-of A → B → B
      dropʳ   : ∀ x y p →
                ∷ʳ x (x ∷ y) (∷ʳ x y p) P.≡ ∷ʳ x y p
      swapʳ   : ∀ x y z p →
                ∷ʳ x (y ∷ z) (∷ʳ y z p) P.≡ ∷ʳ y (x ∷ z) (∷ʳ x z p)
      is-setʳ : P.Is-set B

  open Recᴸᴾ

  recᴸᴾ : Recᴸᴾ A B → Listed-finite-subset-of A → B
  recᴸᴾ r = elimᴸᴾ e
    where
    module R = Recᴸᴾ r

    e : Elimᴸᴾ _
    e .[]ʳ               = R.[]ʳ
    e .∷ʳ {y = y} x      = R.∷ʳ x y
    e .dropʳ {y = y} x   = R.dropʳ x y
    e .swapʳ {z = z} x y = R.swapʳ x y z
    e .is-setʳ _         = R.is-setʳ

  -- A dependent eliminator, expressed using equality.

  record Elimᴸ {A : Set a} (P : Listed-finite-subset-of A → Set p) :
               Set (a ⊔ p) where
    field
      []ʳ     : P []
      ∷ʳ      : ∀ x → P y → P (x ∷ y)
      dropʳ   : ∀ x (p : P y) →
                subst P (dropᴸ {x = x} {y = y}) (∷ʳ x (∷ʳ x p)) ≡
                ∷ʳ x p
      swapʳ   : ∀ x y (p : P z) →
                subst P (swapᴸ {x = x} {y = y} {z = z})
                        (∷ʳ x (∷ʳ y p)) ≡
                ∷ʳ y (∷ʳ x p)
      is-setʳ : ∀ x → Is-set (P x)

  open Elimᴸ

  elimᴸ : Elimᴸ P → (x : Listed-finite-subset-of A) → P x
  elimᴸ e = elimᴸᴾ e′
    where
    module E = Elimᴸ e

    e′ : Elimᴸᴾ _
    e′ .[]ʳ         = E.[]ʳ
    e′ .∷ʳ          = E.∷ʳ
    e′ .dropʳ x p   = subst≡→[]≡ (E.dropʳ x p)
    e′ .swapʳ x y p = subst≡→[]≡ (E.swapʳ x y p)
    e′ .is-setʳ x   = _↔_.to (H-level↔H-level 2) (E.is-setʳ x)

  -- A non-dependent eliminator, expressed using equality.

  record Recᴸ (A : Set a) (B : Set b) : Set (a ⊔ b) where
    field
      []ʳ     : B
      ∷ʳ      : A → Listed-finite-subset-of A → B → B
      dropʳ   : ∀ x y p →
                ∷ʳ x (x ∷ y) (∷ʳ x y p) ≡ ∷ʳ x y p
      swapʳ   : ∀ x y z p →
                ∷ʳ x (y ∷ z) (∷ʳ y z p) ≡ ∷ʳ y (x ∷ z) (∷ʳ x z p)
      is-setʳ : Is-set B

  open Recᴸ

  recᴸ : Recᴸ A B → Listed-finite-subset-of A → B
  recᴸ r = recᴸᴾ r′
    where
    module R = Recᴸ r

    r′ : Recᴸᴾ _ _
    r′ .[]ʳ           = R.[]ʳ
    r′ .∷ʳ            = R.∷ʳ
    r′ .dropʳ x y p   = _↔_.to ≡↔≡ (R.dropʳ x y p)
    r′ .swapʳ x y z p = _↔_.to ≡↔≡ (R.swapʳ x y z p)
    r′ .is-setʳ       = _↔_.to (H-level↔H-level 2) R.is-setʳ

  -- A dependent eliminator for propositions.

  record Elimᴸ-prop
           {A : Set a} (P : Listed-finite-subset-of A → Set p) :
           Set (a ⊔ p) where
    field
      []ʳ             : P []
      ∷ʳ              : ∀ x → P y → P (x ∷ y)
      is-propositionʳ : ∀ x → Is-proposition (P x)

  open Elimᴸ-prop

  elimᴸ-prop : Elimᴸ-prop P → (x : Listed-finite-subset-of A) → P x
  elimᴸ-prop e = elimᴸ e′
    where
    module E = Elimᴸ-prop e

    e′ : Elimᴸ _
    e′ .[]ʳ         = E.[]ʳ
    e′ .∷ʳ          = E.∷ʳ
    e′ .dropʳ _ _   = E.is-propositionʳ _ _ _
    e′ .swapʳ _ _ _ = E.is-propositionʳ _ _ _
    e′ .is-setʳ _   = mono₁ 1 (E.is-propositionʳ _)

  -- Union for listed finite subsets.

  infixr 5 _∪ᴸ_

  _∪ᴸ_ :
    Listed-finite-subset-of A → Listed-finite-subset-of A →
    Listed-finite-subset-of A
  [] ∪ᴸ y      = y
  (x ∷ y) ∪ᴸ z = x ∷ (y ∪ᴸ z)

  dropᴸᴾ {x = x} {y = y} i ∪ᴸ z =
    dropᴸᴾ {x = x} {y = y ∪ᴸ z} i

  swapᴸᴾ {x = x} {y = y} {z = z} i ∪ᴸ u =
    swapᴸᴾ {x = x} {y = y} {z = z ∪ᴸ u} i

  is-setᴾ x y i j ∪ᴸ z =
    is-setᴾ (λ i → x i ∪ᴸ z) (λ i → y i ∪ᴸ z) i j

  -- Some properties of _∪ᴸ_.

  ∪ᴸ[] :
    (x : Listed-finite-subset-of A) →
    x ∪ᴸ [] ≡ x
  ∪ᴸ[] = elimᴸ-prop e
    where
    e : Elimᴸ-prop _
    e .is-propositionʳ _ = is-setᴸ
    e .[]ʳ               = refl _
    e .∷ʳ {y = y} x hyp  =
      x ∷ y ∪ᴸ []  ≡⟨ cong (x ∷_) hyp ⟩∎
      x ∷ y        ∎

  ∪ᴸ∷ :
    ∀ (x : Listed-finite-subset-of A) y z →
    x ∪ᴸ (y ∷ z) ≡ y ∷ x ∪ᴸ z
  ∪ᴸ∷ = elimᴸ-prop e
    where
    e : Elimᴸ-prop _
    e .is-propositionʳ _ =
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      is-setᴸ

    e .[]ʳ _ _ = refl _

    e .∷ʳ {y = y} x hyp z u =
      (x ∷ y) ∪ᴸ (z ∷ u)  ≡⟨⟩
      x ∷ y ∪ᴸ (z ∷ u)    ≡⟨ cong (x ∷_) (hyp z u) ⟩
      x ∷ z ∷ y ∪ᴸ u      ≡⟨ swapᴸ ⟩
      z ∷ x ∷ y ∪ᴸ u      ≡⟨⟩
      z ∷ (x ∷ y) ∪ᴸ u    ∎

  ∪ᴸ-assoc :
    (x y z : Listed-finite-subset-of A) →
    x ∪ᴸ (y ∪ᴸ z) ≡ (x ∪ᴸ y) ∪ᴸ z
  ∪ᴸ-assoc = elimᴸ-prop e
    where
    e : Elimᴸ-prop _
    e .is-propositionʳ _ =
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      is-setᴸ

    e .[]ʳ _ _ = refl _

    e .∷ʳ {y = y} x hyp z u =
      x ∷ y ∪ᴸ (z ∪ᴸ u)  ≡⟨ cong (x ∷_) (hyp z u) ⟩∎
      x ∷ (y ∪ᴸ z) ∪ᴸ u  ∎

  ∪ᴸ-comm :
    (x y : Listed-finite-subset-of A) →
    x ∪ᴸ y ≡ y ∪ᴸ x
  ∪ᴸ-comm = elimᴸ-prop e
    where
    e : Elimᴸ-prop _
    e .is-propositionʳ _ =
      Π-closure ext 1 λ _ →
      is-setᴸ

    e .[]ʳ y =
      [] ∪ᴸ y  ≡⟨⟩
      y        ≡⟨ sym (∪ᴸ[] y) ⟩∎
      y ∪ᴸ []  ∎

    e .∷ʳ {y = y} x hyp z =
      x ∷ y ∪ᴸ z    ≡⟨ cong (x ∷_) (hyp z) ⟩
      x ∷ z ∪ᴸ y    ≡⟨ sym (∪ᴸ∷ z x y) ⟩∎
      z ∪ᴸ (x ∷ y)  ∎

  -- Listed finite subsets are equivalent to Kuratowski finite
  -- subsets.

  Listed≃ : Listed-finite-subset-of A ≃ Finite-subset-of A
  Listed≃ {A = A} = from-bijection (record
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
    to : Listed-finite-subset-of A → Finite-subset-of A
    to []      = ∅
    to (x ∷ y) = singleton x ∪ to y

    to (dropᴸᴾ {x = x} {y = y} i) =
      (singleton x ∪ (singleton x ∪ to y)  P.≡⟨ assocᴾ ⟩
       (singleton x ∪ singleton x) ∪ to y  P.≡⟨ P.cong (_∪ to y) idem-sᴾ ⟩∎
       singleton x ∪ to y                  ∎) i

    to (swapᴸᴾ {x = x} {y = y} {z = z} i) =
      (singleton x ∪ (singleton y ∪ to z)  P.≡⟨ assocᴾ ⟩
       (singleton x ∪ singleton y) ∪ to z  P.≡⟨ P.cong (_∪ to z) commᴾ ⟩
       (singleton y ∪ singleton x) ∪ to z  P.≡⟨ P.sym assocᴾ ⟩∎
       singleton y ∪ (singleton x ∪ to z)  ∎) i

    to (is-setᴾ x y i j) =
      is-setᴾ (λ i → to (x i)) (λ i → to (y i)) i j

    from : Finite-subset-of A → Listed-finite-subset-of A
    from ∅             = []
    from (singleton x) = x ∷ []
    from (x ∪ y)       = from x ∪ᴸ from y

    from (∅∪ᴾ {x = x} _) = from x

    from (idem-sᴾ {x = x} i) = dropᴸᴾ {x = x} {y = []} i

    from (assocᴾ {x = x} {y = y} {z = z} i) =
      _↔_.to ≡↔≡ (∪ᴸ-assoc (from x) (from y) (from z)) i

    from (commᴾ {x = x} {y = y} i) =
      _↔_.to ≡↔≡ (∪ᴸ-comm (from x) (from y)) i

    from (is-setᴾ x y i j) =
      is-setᴾ (λ i → from (x i)) (λ i → from (y i)) i j

    to-∪ᴸ : ∀ x y → to (x ∪ᴸ y) ≡ to x ∪ to y
    to-∪ᴸ = elimᴸ-prop e
      where
      e : Elimᴸ-prop _
      e .is-propositionʳ _ =
        Π-closure ext 1 λ _ →
        is-set

      e .[]ʳ y =
        to y      ≡⟨ sym ∅∪ ⟩∎
        ∅ ∪ to y  ∎

      e .∷ʳ {y = y} x hyp z =
        singleton x ∪ to (y ∪ᴸ z)    ≡⟨ cong (singleton x ∪_) (hyp z) ⟩
        singleton x ∪ (to y ∪ to z)  ≡⟨ assoc ⟩∎
        (singleton x ∪ to y) ∪ to z  ∎

    to∘from : ∀ x → to (from x) ≡ x
    to∘from = elim-prop e
      where
      e : Elim-prop _
      e .is-propositionʳ _            = is-set
      e .∅ʳ                           = refl _
      e .singletonʳ _                 = ∪∅
      e .∪ʳ {x = x} {y = y} hyp₁ hyp₂ =
        to (from x ∪ᴸ from y)      ≡⟨ to-∪ᴸ (from x) (from y) ⟩
        to (from x) ∪ to (from y)  ≡⟨ cong₂ _∪_ hyp₁ hyp₂ ⟩∎
        x ∪ y                      ∎

    from∘to : ∀ x → from (to x) ≡ x
    from∘to = elimᴸ-prop e
      where
      e : Elimᴸ-prop _
      e .is-propositionʳ _ = is-setᴸ
      e .[]ʳ               = refl _
      e .∷ʳ {y = y} x hyp  =
        x ∷ from (to y)  ≡⟨ cong (x ∷_) hyp ⟩∎
        x ∷ y            ∎

-- A list-like dependent eliminator for Finite-subset-of, for
-- propositions.

record List-elim-prop
         {A : Set a} (P : Finite-subset-of A → Set p) :
         Set (a ⊔ p) where
  field
    []ʳ             : P ∅
    ∷ʳ              : ∀ x → P y → P (singleton x ∪ y)
    is-propositionʳ : ∀ x → Is-proposition (P x)

open List-elim-prop public

list-elim-prop : List-elim-prop P → (x : Finite-subset-of A) → P x
list-elim-prop {P = P} l x =
  subst P (_≃_.right-inverse-of Listed≃ x)
    (elimᴸ-prop e (_≃_.from Listed≃ x))
  where
  module L = List-elim-prop l

  e : Elimᴸ-prop (P ∘ _≃_.to Listed≃)
  e .[]ʳ               = L.[]ʳ
  e .∷ʳ x              = L.∷ʳ x
  e .is-propositionʳ _ = L.is-propositionʳ _

-- A list-like non-dependent eliminator for Finite-subset-of,
-- expressed using paths.

record List-recᴾ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    []ʳ     : B
    ∷ʳ      : A → Finite-subset-of A → B → B
    dropʳ   : ∀ x y p →
              ∷ʳ x (singleton x ∪ y) (∷ʳ x y p) P.≡ ∷ʳ x y p
    swapʳ   : ∀ x y z p →
              ∷ʳ x (singleton y ∪ z) (∷ʳ y z p) P.≡
              ∷ʳ y (singleton x ∪ z) (∷ʳ x z p)
    is-setʳ : P.Is-set B

open List-recᴾ public

list-recᴾ : List-recᴾ A B → Finite-subset-of A → B
list-recᴾ l = recᴸᴾ r ∘ _≃_.from Listed≃
  where
  module L = List-recᴾ l

  r : Recᴸᴾ _ _
  r .[]ʳ         = L.[]ʳ
  r .∷ʳ x y      = L.∷ʳ x (_≃_.to Listed≃ y)
  r .dropʳ x y   = L.dropʳ x (_≃_.to Listed≃ y)
  r .swapʳ x y z = L.swapʳ x y (_≃_.to Listed≃ z)
  r .is-setʳ     = L.is-setʳ

-- Unit tests documenting some of the computational behaviour of
-- list-recᴾ.

_ : list-recᴾ l ∅ ≡ l .[]ʳ
_ = refl _

_ : list-recᴾ l (singleton x) ≡ l .∷ʳ x ∅ (l .[]ʳ)
_ = refl _

_ : list-recᴾ l (singleton x ∪ y) ≡
    l .∷ʳ x (_≃_.to Listed≃ (_≃_.from Listed≃ y)) (list-recᴾ l y)
_ = refl _

-- A list-like non-dependent eliminator for Finite-subset-of,
-- expressed using equality.

record List-rec (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    []ʳ     : B
    ∷ʳ      : A → Finite-subset-of A → B → B
    dropʳ   : ∀ x y p →
              ∷ʳ x (singleton x ∪ y) (∷ʳ x y p) ≡ ∷ʳ x y p
    swapʳ   : ∀ x y z p →
              ∷ʳ x (singleton y ∪ z) (∷ʳ y z p) ≡
              ∷ʳ y (singleton x ∪ z) (∷ʳ x z p)
    is-setʳ : Is-set B

open List-rec public

list-rec : List-rec A B → Finite-subset-of A → B
list-rec l = list-recᴾ l′
  where
  module L = List-rec l

  l′ : List-recᴾ _ _
  l′ .[]ʳ           = L.[]ʳ
  l′ .∷ʳ            = L.∷ʳ
  l′ .dropʳ x y p   = _↔_.to ≡↔≡ (L.dropʳ x y p)
  l′ .swapʳ x y z p = _↔_.to ≡↔≡ (L.swapʳ x y z p)
  l′ .is-setʳ       = _↔_.to (H-level↔H-level 2) L.is-setʳ

-- Unit tests documenting some of the computational behaviour of
-- list-rec.

_ : list-rec l ∅ ≡ l .[]ʳ
_ = refl _

_ : list-rec l (singleton x) ≡ l .∷ʳ x ∅ (l .[]ʳ)
_ = refl _

_ : list-rec l (singleton x ∪ y) ≡
    l .∷ʳ x (_≃_.to Listed≃ (_≃_.from Listed≃ y)) (list-rec l y)
_ = refl _

------------------------------------------------------------------------
-- Size

private

  -- This definition is used to define ∣_∣≡ and ∣∣≡-propositional
  -- below.
  --
  -- This definition is not taken from "Finite Sets in Homotopy Type
  -- Theory", but it is based on the size function in that paper.

  Size : {A : Set a} → Finite-subset-of A → ℕ → Proposition a
  Size {a = a} {A = A} = list-rec lr
    where

    mutual

      -- The size of singleton x ∪ y is equal to the size of y if x is
      -- a member of y, and otherwise it is equal to the successor of
      -- the size of y.

      Cons′ :
        A → Finite-subset-of A →
        (ℕ → Proposition a) → (ℕ → Set a)
      Cons′ x y ∣y∣≡ n =
        x ∈ y × proj₁ (∣y∣≡ n)
          ⊎
        Cons″ x y ∣y∣≡ n

      Cons″ :
        A → Finite-subset-of A →
        (ℕ → Proposition a) → (ℕ → Set a)
      Cons″ x y ∣y∣≡ zero    = ⊥
      Cons″ x y ∣y∣≡ (suc n) = ¬ x ∈ y × proj₁ (∣y∣≡ n)

    Cons′-propositional :
      ∀ x y Hyp n → Is-proposition (Cons′ x y Hyp n)
    Cons′-propositional x y Hyp zero =
      ⊎-closure-propositional
        (λ _ ())
        (×-closure 1 (∈-propositional y) (proj₂ (Hyp 0)))
        ⊥-propositional
    Cons′-propositional x y Hyp (suc n) =
      ⊎-closure-propositional
        (λ (x∈y , _) (x∉y , _) → x∉y x∈y)
        (×-closure 1 (∈-propositional y) (proj₂ (Hyp (suc n))))
        (×-closure 1 (¬-propositional ext) (proj₂ (Hyp n)))

    Cons :
      A → Finite-subset-of A →
      (ℕ → Proposition a) → (ℕ → Proposition a)
    Cons x y Hyp n =
        Cons′               x y Hyp n
      , Cons′-propositional x y Hyp n

    drop-lemma :
      Cons′ x (singleton x ∪ y) (Cons x y H) n ≃
      Cons′ x y H n
    drop-lemma {x = x} {y = y} {H = H} {n = n} =
      Cons′ x (singleton x ∪ y) (Cons x y H) n   ↔⟨⟩
      x ∈ singleton x ∪ y × Cons′ x y H n ⊎ C n  ↔⟨ drop-⊥-right (C↔⊥ n) ⟩
      x ∈ singleton x ∪ y × Cons′ x y H n        ↔⟨ drop-⊤-left-× (λ _ → x∈x∪y↔⊤) ⟩
      Cons′ x y H n                              □
      where
      C = Cons″ x (singleton x ∪ y) (Cons x y H)

      x∈x∪y↔⊤ : x ∈ singleton x ∪ y ↔ ⊤
      x∈x∪y↔⊤ =
        x ∈ singleton x ∪ y    ↔⟨⟩
        ∥ ∥ x ≡ x ∥ ⊎ x ∈ y ∥  ↝⟨ Trunc.∥∥-cong (Trunc.inhabited⇒∥∥↔⊤ ∣ refl _ ∣ ⊎-cong F.id) ⟩
        ∥ ⊤ ⊎ x ∈ y ∥          ↝⟨ Trunc.inhabited⇒∥∥↔⊤ ∣ inj₁ tt ∣ ⟩□
        ⊤                      □

      C↔⊥ : ∀ n → C n ↔ ⊥
      C↔⊥ zero    = ⊥↔⊥
      C↔⊥ (suc n) =
        ¬ x ∈ singleton x ∪ y × Cons′ x y H n  ↝⟨ →-cong ext x∈x∪y↔⊤ F.id ×-cong F.id ⟩
        ¬ ⊤ × Cons′ x y H n                    ↝⟨ inverse (Bijection.⊥↔uninhabited (_$ _)) ×-cong F.id ⟩
        ⊥₀ × Cons′ x y H n                     ↝⟨ ×-left-zero ⟩□
        ⊥                                      □

    swap-lemma′ :
      ∀ n →

      x ∈ singleton y ∪ z × Cons′ y z H n ⊎
      Cons″ x (singleton y ∪ z) (Cons y z H) n →

      y ∈ singleton x ∪ z × Cons′ x z H n ⊎
      Cons″ y (singleton x ∪ z) (Cons x z H) n
    swap-lemma′ {x = x} {y = y} {z = z} {H = H} = λ where
      n (inj₁ (x∈y∪z , inj₁ (y∈z , p))) →
        inj₁ ( ∣ inj₂ y∈z ∣
             , inj₁
                 ( (                       $⟨ x∈y∪z ⟩
                    x ∈ singleton y ∪ z    ↔⟨⟩
                    ∥ ∥ x ≡ y ∥ ⊎ x ∈ z ∥  ↔⟨ Trunc.flatten′ (λ F → F (x ≡ y) ⊎ x ∈ z) (λ f → ⊎-map f id) [ Trunc.∥∥-map inj₁ , ∣_∣ ∘ inj₂ ] ⟩
                    ∥ x ≡ y ⊎ x ∈ z ∥      ↝⟨ Trunc.∥∥-map [ (flip (subst (_∈ z)) y∈z ∘ sym) , id ] ⟩
                    ∥ x ∈ z ∥              ↔⟨ Trunc.∥∥↔ (∈-propositional z) ⟩□
                    x ∈ z                  □)
                 , p
                 )
             )

      (suc n) (inj₁ (x∈y∪z , inj₂ (y∉z , p))) →
        let prop = Cons′-propositional
                     y (singleton x ∪ z) (Cons x z H) (suc n) in
        Trunc.rec prop
          [ Trunc.rec prop (λ x≡y →
              inj₁ ( ∣ inj₁ ∣ sym x≡y ∣ ∣
                   , inj₂ ( (x ∈ z  ↝⟨ subst (_∈ z) x≡y ⟩
                             y ∈ z  ↝⟨ y∉z ⟩□
                             ⊥      □)
                          , p
                          )
                   ))
          , (λ x∈z →
               inj₂ ( (y ∈ singleton x ∪ z    ↔⟨⟩
                       ∥ ∥ y ≡ x ∥ ⊎ y ∈ z ∥  ↔⟨ Trunc.flatten′ (λ F → F (y ≡ x) ⊎ y ∈ z) (λ f → ⊎-map f id) [ Trunc.∥∥-map inj₁ , ∣_∣ ∘ inj₂ ] ⟩
                       ∥ y ≡ x ⊎ y ∈ z ∥      ↝⟨ Trunc.∥∥-map [ flip (subst (_∈ z)) x∈z ∘ sym , id ] ⟩
                       ∥ y ∈ z ∥              ↝⟨ Trunc.∥∥-map y∉z ⟩
                       ∥ ⊥ ∥                  ↔⟨ Trunc.∥∥↔ ⊥-propositional ⟩□
                       ⊥                      □)
                    , inj₁ (x∈z , p)
                    ))
          ]
          x∈y∪z

      (suc n) (inj₂ (x∉y∪z , inj₁ (y∈z , p))) →
        inj₁ ( ∣ inj₂ y∈z ∣
             , inj₂ ( (x ∈ z                ↝⟨ ∣_∣ ∘ inj₂ ⟩
                       x ∈ singleton y ∪ z  ↝⟨ x∉y∪z ⟩□
                       ⊥                    □)
                    , p
                    )
             )

      (suc (suc n)) (inj₂ (x∉y∪z , inj₂ (y∉z , p))) →
        inj₂ ( (y ∈ singleton x ∪ z              ↔⟨⟩
                ∥ ∥ y ≡ x ∥ ⊎ y ∈ z ∥            ↝⟨ Trunc.∥∥-map (⊎-map (∣_∣ ∘ inj₁ ∘ Trunc.∥∥-map sym) id) ⟩
                ∥ x ∈ singleton y ∪ z ⊎ y ∈ z ∥  ↝⟨ Trunc.∥∥-map [ x∉y∪z , y∉z ] ⟩
                ∥ ⊥ ∥                            ↔⟨ Trunc.∥∥↔ ⊥-propositional ⟩□
                ⊥                                □)
             , inj₂ ( (x ∈ z                ↝⟨ ∣_∣ ∘ inj₂ ⟩
                       x ∈ singleton y ∪ z  ↝⟨ x∉y∪z ⟩□
                       ⊥                    □)
                    , p
                    )
             )

    swap-lemma :
      Cons′ x (singleton y ∪ z) (Cons y z H) n ≃
      Cons′ y (singleton x ∪ z) (Cons x z H) n
    swap-lemma {x = x} {y = y} {z = z} {H = H} {n = n} =
      _↠_.from
        (Eq.≃↠⇔
           (Cons′-propositional x (singleton y ∪ z) (Cons y z H) n)
           (Cons′-propositional y (singleton x ∪ z) (Cons x z H) n))
        (record { to = swap-lemma′ _; from = swap-lemma′ _ })

    lr : List-rec A (ℕ → Proposition a)
    lr .[]ʳ n = ↑ _ (n ≡ 0) , ↑-closure 1 ℕ-set

    lr .∷ʳ = Cons

    lr .dropʳ x y Hyp = ⟨ext⟩ λ _ →
      _↔_.to (ignore-propositional-component
             (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ drop-lemma

    lr .swapʳ x y z Hyp = ⟨ext⟩ λ _ →
      _↔_.to (ignore-propositional-component
             (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ swap-lemma

    lr .is-setʳ =
      Π-closure ext 2 λ _ →
      Univ.∃-H-level-H-level-1+ ext univ 1

-- Size.

infix 4 ∣_∣≡_

∣_∣≡_ : {A : Set a} → Finite-subset-of A → ℕ → Set a
∣ x ∣≡ n = proj₁ (Size x n)

-- The size predicate is propositional.

∣∣≡-propositional :
  (x : Finite-subset-of A) → Is-proposition (∣ x ∣≡ n)
∣∣≡-propositional x = proj₂ (Size x _)

-- Unit tests documenting some of the computational behaviour of
-- ∣_∣≡_.

_ : (∣ ∅ {A = A} ∣≡ n) ≡ ↑ _ (n ≡ 0)
_ = refl _

_ : ∀ {A : Set a} {x : A} {y} →
    let y′ = _≃_.to Listed≃ (_≃_.from Listed≃ y) in

    (∣ singleton x ∪ y ∣≡ zero) ≡
    (x ∈ y′ × ∣ y ∣≡ zero ⊎ ⊥)
_ = refl _

_ : let y′ = _≃_.to Listed≃ (_≃_.from Listed≃ y) in

    (∣ singleton x ∪ y ∣≡ suc n) ≡
    (x ∈ y′ × ∣ y ∣≡ suc n ⊎ ¬ x ∈ y′ × ∣ y ∣≡ n)
_ = refl _

-- The size predicate is functional.

∣∣≡-functional :
  (x : Finite-subset-of A) → ∣ x ∣≡ m → ∣ x ∣≡ n → m ≡ n
∣∣≡-functional x = list-elim-prop e x _ _
  where
  e : List-elim-prop (λ x → ∀ m n → ∣ x ∣≡ m → ∣ x ∣≡ n → m ≡ n)
  e .[]ʳ m n (lift m≡0) (lift n≡0) =
    m  ≡⟨ m≡0 ⟩
    0  ≡⟨ sym n≡0 ⟩∎
    n  ∎

  e .∷ʳ {y = y} x hyp = λ where
    m n (inj₁ (x∈y , ∣y∣≡m)) (inj₁ (x∈y′ , ∣y∣≡n)) →
      hyp m n ∣y∣≡m ∣y∣≡n

    (suc m) (suc n) (inj₂ (x∉y , ∣y∣≡m)) (inj₂ (x∉y′ , ∣y∣≡n)) →
      cong suc (hyp m n ∣y∣≡m ∣y∣≡n)

    _ (suc _) (inj₁ (x∈y , _)) (inj₂ (x∉y , _)) → ⊥-elim (x∉y x∈y)
    (suc _) _ (inj₂ (x∉y , _)) (inj₁ (x∈y , _)) → ⊥-elim (x∉y x∈y)

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    ℕ-set

-- If truncated equality is decidable, then one can compute the size
-- of a finite subset.

size :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x : Finite-subset-of A) → ∃ λ n → ∣ x ∣≡ n
size equal? = list-elim-prop e
  where
  e : List-elim-prop _
  e .[]ʳ = 0 , lift (refl _)

  e .∷ʳ {y = y} x (n , ∣y∣≡n) =
    case member? equal? x y of λ x∈?y →
        if x∈?y then n else suc n
      , lemma ∣y∣≡n x∈?y
    where
    lemma :
      ∣ y ∣≡ n →
      (x∈?y : Dec (x ∈ y)) →
      ∣ singleton x ∪ y ∣≡ if x∈?y then n else suc n
    lemma ∣y∣≡n (yes x∈y) =
      inj₁ ( subst (_ ∈_) (sym $ _≃_.right-inverse-of Listed≃ y) x∈y
           , ∣y∣≡n
           )

    lemma ∣y∣≡n (no x∉y) =
      inj₂ ( x∉y ∘ subst (_ ∈_) (_≃_.right-inverse-of Listed≃ y)
           , ∣y∣≡n
           )

  e .is-propositionʳ x (m , ∣x∣≡m) (n , ∣x∣≡n) =
    Σ-≡,≡→≡ (m  ≡⟨ ∣∣≡-functional x ∣x∣≡m ∣x∣≡n ⟩∎
             n  ∎)
            (∣∣≡-propositional x _ _)
