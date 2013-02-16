------------------------------------------------------------------------
-- Examples related to Univalence-axiom.Isomorphism-is-equality.More
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Note that this module uses ordinary propositional equality, with a
-- computing J rule.

-- This module has been developed in collaboration with Thierry
-- Coquand.

module Univalence-axiom.Isomorphism-is-equality.More.Examples where

open import Equality.Propositional renaming (equality-with-J to eq)

open import Equivalence eq hiding (id)
open import Function-universe eq hiding (id)
open import H-level eq using (Is-proposition; Is-set)
open import H-level.Closure eq
open import Prelude hiding (id)
open import Univalence-axiom.Isomorphism-is-equality.More

------------------------------------------------------------------------
-- Magmas

magma : Code
magma = ε ▻ A-type ▻ N-ary [0] 2

Magma : Set₁
Magma = ⟦ magma ⟧

private

  -- An unfolding of Magma.

  Magma-unfolded :
    Magma ≡ Σ (Σ (↑ _ ⊤) λ _ →
    Set                    ) λ { (_ , A) →
    ↑ _ A → ↑ _ A → ↑ _ A }
  Magma-unfolded = refl

  -- An unfolding of Isomorphic magma.

  Isomorphic-magma-unfolded :
    ∀ {ass A₁ f₁ A₂ f₂} →
    Isomorphic ass magma ((_ , A₁) , f₁) ((_ , A₂) , f₂) ≡
    Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ≃ A₂)                             ) λ { (_ , lift A₁≃A₂) →
      let open _≃_ (↑-cong A₁≃A₂) in
        ∀ x y → to (f₁ x y) ≡ f₂ (to x) (to y) }
  Isomorphic-magma-unfolded = refl

------------------------------------------------------------------------
-- Semigroups

-- Note that one axiom states that the underlying type is a set. This
-- assumption is used to prove that the other axiom is propositional.

semigroup : Code
semigroup =
  ε

  ▻ A-type

  ▻ Is-a-set [0]

  ▻ N-ary (1+ [0]) 2

  ▻ Proposition
      (λ { (_ , _∙_) →
           ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })
      assoc-prop

  where
  assoc-prop = λ { ass ((_ , A-set) , _) →
    let open Assumptions ass in
    Π-closure ext₁ 1 λ _ →
    Π-closure ext₁ 1 λ _ →
    Π-closure ext₁ 1 λ _ →
    A-set _ _ }

Semigroup : Set₁
Semigroup = ⟦ semigroup ⟧

private

  -- An unfolding of Semigroup.

  Semigroup-unfolded :
    Semigroup ≡ Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                                  ) λ {  (_ , A) →
      Is-set (↑ _ A)                      }) λ { ((_ , A) , _) →
      ↑ _ A → ↑ _ A → ↑ _ A               }) λ { (_ , _∙_) →
      ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z }
  Semigroup-unfolded = refl

  -- An unfolding of Isomorphic semigroup.

  Isomorphic-semigroup-unfolded :
    ∀ {ass A₁ is₁ _∙₁_ assoc₁ A₂ is₂ _∙₂_ assoc₂} →
    Isomorphic ass semigroup ((((_ , A₁) , is₁) , _∙₁_) , assoc₁)
                             ((((_ , A₂) , is₂) , _∙₂_) , assoc₂) ≡
    Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ≃ A₂)                         ) λ { _ →
      ↑ _ ⊤                                }) λ { ((_ , lift A₁≃A₂) , _) →
      let open _≃_ (↑-cong A₁≃A₂) in
        ∀ x y → to (x ∙₁ y) ≡ to x ∙₂ to y }) λ { _ →
      ↑ _ ⊤                                }
  Isomorphic-semigroup-unfolded = refl

------------------------------------------------------------------------
-- Sets with fixed-point operators

set-with-fixed-point-operator : Code
set-with-fixed-point-operator =
  ε

  ▻ A-type

  ▻ Is-a-set [0]

  ▻ Simple ((base (1+ [0]) ⟶ base (1+ [0])) ⟶ base (1+ [0]))

  ▻ Proposition
      (λ { (_ , fix) →
           ∀ f → fix f ≡ f (fix f) })
      fix-point-prop

  where
  fix-point-prop = λ { ass ((_ , A-set) , _) →
    let open Assumptions ass in
    Π-closure ext₁ 1 λ _ →
    A-set _ _ }

Set-with-fixed-point-operator : Set₁
Set-with-fixed-point-operator = ⟦ set-with-fixed-point-operator ⟧

private

  -- An unfolding of Set-with-fixed-point-operator.

  Set-with-fixed-point-operator-unfolded :
    Set-with-fixed-point-operator ≡ Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                      ) λ {  (_ , A) →
      Is-set (↑ _ A)          }) λ { ((_ , A) , _) →
      (↑ _ A → ↑ _ A) → ↑ _ A }) λ { (_ , fix) →
      ∀ f → fix f ≡ f (fix f) }
  Set-with-fixed-point-operator-unfolded = refl

  -- An unfolding of Isomorphic set-with-fixed-point-operator.

  Isomorphic-set-with-fixed-point-operator-unfolded :
    ∀ {ass A₁ is₁ fix₁ fixed-point₁ A₂ is₂ fix₂ fixed-point₂} →
    Isomorphic ass set-with-fixed-point-operator
               ((((_ , A₁) , is₁) , fix₁) , fixed-point₁)
               ((((_ , A₂) , is₂) , fix₂) , fixed-point₂) ≡
    Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ≃ A₂)                             ) λ { _ →
      ↑ _ ⊤                                    }) λ { ((_ , lift A₁≃A₂) , _) →
      let open _≃_ (↑-cong A₁≃A₂) in
        ∀ f g →
        (∀ x y → to x ≡ y → to (f x) ≡ g y) →
        to (fix₁ f) ≡ fix₂ g                   }) λ { _ →
      ↑ _ ⊤                                    }
  Isomorphic-set-with-fixed-point-operator-unfolded = refl

------------------------------------------------------------------------
-- Abelian groups

abelian-group : Code
abelian-group =
  ε

  -- The underlying type.
  ▻ A-type

  -- The underlying type is a set.
  ▻ Is-a-set [0]

  -- The binary group operation.
  ▻ N-ary (1+ [0]) 2

  -- Commutativity.
  ▻ Comm

  -- Associativity.
  ▻ Assoc

  -- Identity.
  ▻ N-ary (1+ 1+ 1+ 1+ [0]) 0

  -- Left identity.
  ▻ Left-identity

  -- Right identity.
  ▻ Right-identity

  -- Inverse.
  ▻ N-ary (1+ 1+ 1+ 1+ 1+ 1+ 1+ [0]) 1

  -- Left inverse.
  ▻ Left-inverse

  -- Right inverse.
  ▻ Right-inverse

  where
  bin = ε ▻ A-type ▻ Is-a-set [0] ▻ N-ary (1+ [0]) 2

  Comm = Proposition {bin}
    (λ { (_ , _∙_) →
       ∀ x y → x ∙ y ≡ y ∙ x })

    (λ { ass ((_ , A-set) , _) →
       let open Assumptions ass in
       Π-closure ext₁ 1 λ _ →
       Π-closure ext₁ 1 λ _ →
       A-set _ _
     })

  comm = bin ▻ Comm

  Assoc = Proposition {comm}
    (λ { ((_ , _∙_) , _) →
         ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })

    (λ { ass (((_ , A-set) , _) , _) →
       let open Assumptions ass in
       Π-closure ext₁ 1 λ _ →
       Π-closure ext₁ 1 λ _ →
       Π-closure ext₁ 1 λ _ →
       A-set _ _
     })

  identity = comm ▻ Assoc ▻ N-ary (1+ 1+ 1+ 1+ [0]) 0

  Left-identity = Proposition {identity}
    (λ { ((((_ , _∙_) , _) , _) , e) →
         ∀ x → e ∙ x ≡ x })

    (λ { ass (((((_ , A-set) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure ext₁ 1 λ _ →
       A-set _ _
     })

  left-identity = identity ▻ Left-identity

  Right-identity = Proposition {left-identity}
    (λ { (((((_ , _∙_) , _) , _) , e) , _) →
         ∀ x → x ∙ e ≡ x })

    (λ { ass ((((((_ , A-set) , _) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure ext₁ 1 λ _ →
       A-set _ _
     })

  inv = left-identity ▻ Right-identity ▻
        N-ary (1+ 1+ 1+ 1+ 1+ 1+ 1+ [0]) 1

  Left-inverse = Proposition {inv}
    (λ { (((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) →
         ∀ x → (x ⁻¹) ∙ x ≡ e })

    (λ { ass ((((((((_ , A-set) , _) , _) , _) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure ext₁ 1 λ _ →
       A-set _ _
     })

  left-inverse = inv ▻ Left-inverse

  Right-inverse = Proposition {left-inverse}
    (λ { ((((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) , _) →
         ∀ x → x ∙ (x ⁻¹) ≡ e })

    (λ { ass (((((((((_ , A-set) , _) , _) , _) , _) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure ext₁ 1 λ _ →
       A-set _ _
     })

Abelian-group : Set₁
Abelian-group = ⟦ abelian-group ⟧

private

  -- An unfolding of Abelian-group. Note that the inner structure is
  -- left-nested.

  Abelian-group-unfolded :
    Abelian-group ≡ Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                                  ) λ {        (_ , A) →
      Is-set (↑ _ A)                      }) λ {       ((_ , A) , _) →
      ↑ _ A → ↑ _ A → ↑ _ A               }) λ {                  (_ , _∙_) →
      ∀ x y → x ∙ y ≡ y ∙ x               }) λ {                 ((_ , _∙_) , _) →
      ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z }) λ {    (((((_ , A) , _) , _  ) , _) , _) →
      ↑ _ A                               }) λ {               ((((_ , _∙_) , _) , _) , e) →
      ∀ x → e ∙ x ≡ x                     }) λ {              (((((_ , _∙_) , _) , _) , e) , _) →
      ∀ x → x ∙ e ≡ x                     }) λ { ((((((((_ , A) , _) , _  ) , _) , _) , _) , _) , _) →
      ↑ _ A → ↑ _ A                       }) λ {            (((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) →
      ∀ x → (x ⁻¹) ∙ x ≡ e                }) λ {           ((((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) , _) →
      ∀ x → x ∙ (x ⁻¹) ≡ e                }
  Abelian-group-unfolded = refl

  -- An unfolding of Isomorphic abelian-group.

  Isomorphic-abelian-group-unfolded :
    ∀ {ass A₁ is₁ _∙₁_ comm₁ assoc₁ e₁ lid₁ rid₁ _⁻¹₁ linv₁ rinv₁
           A₂ is₂ _∙₂_ comm₂ assoc₂ e₂ lid₂ rid₂ _⁻¹₂ linv₂ rinv₂} →
    Isomorphic ass abelian-group
      (((((((((((_ , A₁) , is₁) , _∙₁_) , comm₁) ,
       assoc₁) , e₁) , lid₁) , rid₁) , _⁻¹₁) , linv₁) , rinv₁)
      (((((((((((_ , A₂) , is₂) , _∙₂_) , comm₂) ,
       assoc₂) , e₂) , lid₂) , rid₂) , _⁻¹₂) , linv₂) , rinv₂) ≡
    Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ≃ A₂)                         ) λ { _ →
      ↑ _ ⊤                                }) λ {       ((_ , lift A₁≃A₂) , _) →
      let open _≃_ (↑-cong A₁≃A₂) in
        ∀ x y → to (x ∙₁ y) ≡ to x ∙₂ to y }) λ { _ →
      ↑ _ ⊤                                }) λ { _ →
      ↑ _ ⊤                                }) λ {    (((((_ , lift A₁≃A₂) , _) , _) , _) , _) →
      let open _≃_ (↑-cong A₁≃A₂) in
        to e₁ ≡ e₂                         }) λ { _ →
      ↑ _ ⊤                                }) λ { _ →
      ↑ _ ⊤                                }) λ { ((((((((_ , lift A₁≃A₂) , _) , _) , _) , _) , _) , _) , _) →
      let open _≃_ (↑-cong A₁≃A₂) in
        ∀ x → to (x ⁻¹₁) ≡ to x ⁻¹₂        }) λ { _ →
      ↑ _ ⊤                                }) λ { _ →
      ↑ _ ⊤                                }
  Isomorphic-abelian-group-unfolded = refl

------------------------------------------------------------------------
-- Church-encoded natural numbers for which we can do induction

-- Church-encoded natural numbers.

Nat : Set₁
Nat = (A : Set) → ↑ (# 1) A → (↑ (# 1) A → ↑ (# 1) A) → ↑ (# 1) A

-- Zero and successor.

Zero : Nat
Zero = λ A z s → z

Suc : Nat → Nat
Suc = λ n A z s → s (n A z s)

-- The code.

inductive-natural-numbers : Code
inductive-natural-numbers =
  ε

  ▻ Dep (Π set (Π (base ⟨0⟩)
                  (Π (Π (base (1+ ⟨0⟩)) (base (1+ 1+ ⟨0⟩)))
                     (base (1+ 1+ ⟨0⟩)))))

  ▻ Proposition
      (λ { (_ , n) →
           (P : Nat → Set) →
           Is-proposition (P n) →
           P Zero →
           (∀ m → P m → P (Suc m)) →
           P n })
      (λ ass _ →
           let open Assumptions ass in
           Π-closure ext₁ 1 λ _ →
           Π-closure (lower-extensionality (# 1) (# 0) ext₁) 1 λ Pn-prop →
           Π-closure (lower-extensionality (# 1) (# 0) ext₁) 1 λ _ →
           Π-closure (lower-extensionality (# 0) (# 1) ext₁) 1 λ _ →
           Pn-prop)

  where open Dependent

private

  -- The usual unfolding lemmas.

  ⟦inductive-natural-numbers⟧ :

    ⟦ inductive-natural-numbers ⟧
      ≡
    Σ (Σ (↑ _ ⊤) λ _ →
      Nat                        ) λ { (_ , n) →
      (P : Nat → Set) →
      Is-proposition (P n) →
      P Zero →
      (∀ m → P m → P (Suc m)) →
      P n                       }
  ⟦inductive-natural-numbers⟧ = refl

  -- Due to performance issues I have not been able to type-check the
  -- following lemma. /NAD

  -- Isomorphic-inductive-natural-numbers :
  --   ∀ {ass : Assumptions}
  --     {n₁ n₂ : Nat}
  --     {prop₁ : (P : Nat → Set) → Is-proposition (P n₁) →
  --              P Zero → (∀ m → P m → P (Suc m)) → P n₁}
  --     {prop₂ : (P : Nat → Set) → Is-proposition (P n₂) →
  --              P Zero → (∀ m → P m → P (Suc m)) → P n₂} →

  --   Isomorphic ass inductive-natural-numbers
  --                  ((_ , n₁) , prop₁) ((_ , n₂) , prop₂)
  --     ≡
  --   Σ (Σ (↑ (# 1) ⊤) λ _ →
  --   ((A₁ A₂ : Set) → (A₁≃A₂ : ↑ (# 1) (A₁ ≃ A₂)) →
  --    let cast = _≃_.from (↑-cong (lower A₁≃A₂)) in
  --    (z₁ : ↑ (# 1) A₁) (z₂ : ↑ (# 1) A₂) →
  --      z₁ ≡ cast z₂ →
  --    (s₁ : ↑ (# 1) A₁ → ↑ (# 1) A₁) (s₂ : ↑ (# 1) A₂ → ↑ (# 1) A₂) →
  --      (∀ n₁ n₂ → n₁ ≡ cast n₂ → s₁ n₁ ≡ cast (s₂ n₂)) →
  --    n₁ A₁ z₁ s₁ ≡ cast (n₂ A₂ z₂ s₂))) λ _ →
  --   ↑ (# 1) ⊤

  -- Isomorphic-inductive-natural-numbers = refl
