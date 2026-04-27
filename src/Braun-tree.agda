------------------------------------------------------------------------
-- Braun trees
------------------------------------------------------------------------

-- Partly following Okasaki's "Three algorithms on Braun trees".

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Braun-tree
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equivalence.Erased eq as EEq using (_≃ᴱ_)
open import Erased.Level-1 eq as Erased
open import H-level.Closure eq
open import Nat eq
open import Vec.Data eq

private variable
  a          : Level
  A          : Type _
  x x₁ x₂    : A
  @0 n n₁ n₂ : ℕ
  @0 eq₁ eq₂ : n₁ ≡ n₂
  ax         : []-cong-axiomatisation _

------------------------------------------------------------------------
-- An invariant

opaque

  -- The invariant.

  @0 Invariant : ℕ → ℕ → Type
  Invariant n₁ n₂ = n₁ ≡ n₂ ⊎ n₁ ≡ suc n₂

  -- Invariant is propositional.

  @0 Invariant-propositional :
    Is-proposition (Invariant n₁ n₂)
  Invariant-propositional (inj₁ _) (inj₁ _) =
    cong inj₁ (ℕ-set _ _)
  Invariant-propositional (inj₁ eq₁) (inj₂ eq₂) =
    ⊥-elim (<→≢ ≤-refl (trans (sym eq₁) eq₂))
  Invariant-propositional (inj₂ eq₁) (inj₁ eq₂) =
    ⊥-elim (<→≢ ≤-refl (trans (sym eq₂) eq₁))
  Invariant-propositional (inj₂ _) (inj₂ _) =
    cong inj₂ (ℕ-set _ _)

  -- A lemma related to the invariant.

  @0 Invariant-zero : Invariant zero n ⇔ 0 ≡ n
  Invariant-zero = record
    { to   = Prelude.[ id , ⊥-elim ∘ 0≢+ ]
    ; from = inj₁
    }

  -- A lemma related to the invariant.

  @0 Invariant-suc : Invariant (suc n₁) n₂ ⇔ Invariant n₂ n₁
  Invariant-suc {n₁} {n₂} = record
    { to   = Prelude.[ inj₂ ∘ sym , inj₁ ∘ sym ∘ cancel-suc ]
    ; from = Prelude.[ inj₂ ∘ sym ∘ cong suc , inj₁ ∘ sym ]
    }

------------------------------------------------------------------------
-- The type

-- Braun trees.

data Tree (A : Type a) : @0 ℕ → Type a where
  leaf : Tree A 0
  node : A → Tree A n₁ → Tree A n₂ →
         @0 Invariant n₁ n₂ →
         @0 n ≡ n₁ + n₂ →
         Tree A (suc n)

pattern non-empty {n} = node {n = n} _ _ _ _ _

private variable
  t t₁ t₁₁ t₁₂ t₂ t₂₁ t₂₂ : Tree _ n
  @0 inv inv₁ inv₂        : Invariant n₁ n₂

------------------------------------------------------------------------
-- Some lemmas

opaque

  -- A congruence lemma.

  node-cong :
    []-cong-axiomatisation lzero →
    x₁ ≡ x₂ → t₁₁ ≡ t₁₂ → t₂₁ ≡ t₂₂ →
    node x₁ t₁₁ t₂₁ inv₁ eq₁ ≡ node x₂ t₁₂ t₂₂ inv₂ eq₂
  node-cong {eq₁} {eq₂} ax x-eq t₁-eq t₂-eq =
    cong
      (λ (x , t₁ , t₂ , inv , eq) →
         node x t₁ t₂ (erased inv) (erased eq))
      (cong₂ _,_ x-eq $
       cong₂ _,_ t₁-eq $
       cong₂ _,_ t₂-eq $
       cong₂ _,_
         ([]-cong [ Invariant-propositional _ _ ])
         ([]-cong [ ℕ-set eq₁ eq₂ ]))
    where
    open Erased.[]-cong₁ ax

opaque

  -- A lemma related to substᴱ and leaf.

  substᴱ-leaf :
    {@0 eq : 0 ≡ 0}
    (ax : []-cong-axiomatisation lzero) →
    let open Erased.[]-cong₁ ax in
    substᴱ (Tree A) eq leaf ≡
    leaf
  substᴱ-leaf ax =
    substᴱ (Tree _) _ leaf         ≡⟨ congᴱ (λ eq → substᴱ (Tree _) eq _) (ℕ-set _ _) ⟩
    substᴱ (Tree _) (refl _) leaf  ≡⟨ substᴱ-refl {P = Tree _} ⟩∎
    leaf                           ∎
    where
    open Erased.[]-cong₁ ax

opaque

  -- A lemma related to substᴱ and node.

  substᴱ-node :
    {@0 eq₁ : suc n₁ ≡ suc n₂}
    (ax : []-cong-axiomatisation lzero) →
    let open Erased.[]-cong₁ ax in
    substᴱ (Tree A) eq₁ (node x t₁ t₂ inv eq₂) ≡
    node x t₁ t₂ inv (trans (sym (cancel-suc eq₁)) eq₂)
  substᴱ-node {A} {x} {t₁} {t₂} {inv} {eq₂} {eq₁} ax =
    substᴱ (Tree A) eq₁ (node x t₁ t₂ inv eq₂)                       ≡⟨ congᴱ (λ eq → substᴱ (Tree _) eq _) (ℕ-set _ _) ⟩

    substᴱ (Tree A) (cong suc (cancel-suc eq₁))
      (node x t₁ t₂ inv eq₂)                                         ≡⟨ sym (substᴱ-∘ (Tree _)) ⟩

    substᴱ (λ n → Tree A (suc n)) (cancel-suc eq₁)
      (node x t₁ t₂ inv eq₂)                                         ≡⟨ elim¹ᴱ
                                                                          (λ eq₁ →
                                                                             substᴱ (λ n → Tree A (suc n)) eq₁ (node x t₁ t₂ inv eq₂) ≡
                                                                             node x t₁ t₂ inv (trans (sym eq₁) eq₂))
                                                                          (
      substᴱ (λ n → Tree A (suc n)) (refl _) (node x t₁ t₂ inv eq₂)        ≡⟨ substᴱ-refl ⟩
      node x t₁ t₂ inv eq₂                                                 ≡⟨ node-cong ax (refl _) (refl _) (refl _) ⟩∎
      node x t₁ t₂ inv (trans (sym (refl _)) eq₂)                          ∎)
                                                                          _ ⟩∎
    node x t₁ t₂ inv (trans (sym (cancel-suc eq₁)) eq₂)              ∎
    where
    open Erased.[]-cong₁ ax
    open Erased.[]-cong₂ ax ax

------------------------------------------------------------------------
-- Empty

opaque

  -- An empty tree.

  empty : {@0 A : Type a} → Tree A 0
  empty = leaf

------------------------------------------------------------------------
-- Cons

opaque

  -- Inserts an element into a tree.

  cons : A → Tree A n → Tree A (suc n)
  cons x leaf =
    node x leaf leaf (_⇔_.from Invariant-zero (refl _)) (refl _)
  cons {n} x (node {n₁} {n₂} y t₁ t₂ inv eq) =
    node x (cons y t₂) t₁ inv′ eq′
    where
    opaque

      @0 inv′ : Invariant (suc n₂) n₁
      inv′ = _⇔_.from Invariant-suc inv

      @0 eq′ : n ≡ 1 + n₂ + n₁
      eq′ =
        n            ≡⟨ cong suc eq ⟩
        1 + n₁ + n₂  ≡⟨ cong suc (+-comm n₁) ⟩∎
        1 + n₂ + n₁  ∎

opaque

  -- A lemma related to substᴱ and cons.

  substᴱ-cons :
    (ax : []-cong-axiomatisation lzero) →
    let open Erased.[]-cong₁ ax in
    substᴱ (Tree A) eq₁ (cons x t) ≡
    cons x (substᴱ (Tree A) eq₂ t)
  substᴱ-cons {A} {eq₁} {x} {t} {eq₂} ax =
    substᴱ (Tree A) eq₁ (cons x t)                  ≡⟨ congᴱ (λ eq → substᴱ (Tree _) eq _) (ℕ-set _ _) ⟩
    substᴱ (Tree A) (cong suc eq₂) (cons x t)       ≡⟨ elim¹ᴱ
                                                         (λ eq₂ →
                                                            substᴱ (Tree A) (cong suc eq₂) (cons x t) ≡
                                                            cons x (substᴱ (Tree A) eq₂ t))
                                                         (
      substᴱ (Tree A) (cong suc (refl _)) (cons x t)      ≡⟨ congᴱ (λ eq → substᴱ (Tree _) eq (cons _ _)) (ℕ-set _ _) ⟩
      substᴱ (Tree A) (refl _) (cons x t)                 ≡⟨ substᴱ-refl {P = Tree _} ⟩
      cons x t                                            ≡⟨ cong (cons _) (sym substᴱ-refl) ⟩∎
      cons x (substᴱ (Tree A) (refl _) t)                 ∎)
                                                         _ ⟩∎
    cons x (substᴱ (Tree A) eq₂ t)                  ∎
    where
    open Erased.[]-cong₁ ax

------------------------------------------------------------------------
-- Uncons

opaque

  -- Removes the "first" element from the tree and returns "the rest"
  -- of the tree.
  --
  -- One could perhaps avoid substᴱ by defining Tree using (more)
  -- "fording".

  uncons :
    []-cong-axiomatisation lzero →
    Tree A (suc n) → A × Tree A n
  uncons ax (node {n₂} {n} x leaf t inv eq) =
    x , substᴱ (Tree _) 0≡n leaf
    where
    open Erased.[]-cong₁ ax

    opaque

      @0 0≡n : 0 ≡ n
      0≡n =
        0   ≡⟨ _⇔_.to Invariant-zero inv ⟩
        n₂  ≡⟨ sym eq ⟩∎
        n   ∎
  uncons {n} ax (node {n₂} x t₁@(non-empty {n = n₁}) t₂ inv eq) =
    x ,
    (case uncons ax t₁ of λ
       (y , t₁) →
     substᴱ (Tree _) eq′ (node y t₂ t₁ inv′ (refl _)))
    where
    open Erased.[]-cong₁ ax

    opaque

      @0 inv′ : Invariant n₂ n₁
      inv′ = _⇔_.to Invariant-suc inv

      @0 eq′ : suc (n₂ + n₁) ≡ n
      eq′ =
        suc (n₂ + n₁)  ≡⟨ cong suc (+-comm n₂) ⟩
        suc (n₁ + n₂)  ≡⟨ sym eq ⟩∎
        n              ∎

------------------------------------------------------------------------
-- An equivalence (with erased proofs)

opaque
  unfolding cons uncons

  -- The function uncons ax is a left inverse of uncurry cons.

  uncons-cons : uncons ax (cons x t) ≡ (x , t)
  uncons-cons {ax} {t = leaf} =
    cong (_,_ _)
      (substᴱ (Tree _) _ leaf         ≡⟨ congᴱ (λ eq → substᴱ (Tree _) eq _) (ℕ-set _ _) ⟩
       substᴱ (Tree _) (refl _) leaf  ≡⟨ substᴱ-refl {P = Tree _} ⟩∎
       leaf                           ∎)
    where
    open Erased.[]-cong₁ ax
  uncons-cons {ax} {t = node y t₁ t₂ inv eq}
    with cons y t₂ | uncons-cons {ax = ax} {x = y} {t = t₂}
  … | t₂′@non-empty | ih =
    cong (_,_ _)
      (let y′ , t₂″ = uncons ax t₂′ in
       substᴱ (Tree _) _ (node y′ t₁ t₂″ _ _)  ≡⟨ substᴱ-node ax ⟩
       node y′ t₁ t₂″ _ _                      ≡⟨ node-cong ax (cong proj₁ ih) (refl _) (cong proj₂ ih) ⟩
       node y t₁ t₂ inv eq                     ∎)
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding cons uncons

  -- The function uncons ax is a right inverse of uncurry cons (in
  -- erased contexts).
  --
  -- I made this proof erased due to Agda issue #8534.

  @0 cons-uncons : uncurry cons (uncons ax t) ≡ t
  cons-uncons {ax} {t = node y leaf leaf inv eq} =
    cons y (substᴱ (Tree _) _ leaf)                 ≡⟨ cong (λ eq → cons _ (substᴱ (Tree _) eq _)) (ℕ-set _ _) ⟩
    cons y (substᴱ (Tree _) (sym eq) leaf)          ≡⟨ elim₁ (λ eq → cons y (substᴱ (Tree _) (sym eq) leaf) ≡ node y leaf leaf inv eq)
                                                         (
      cons y (substᴱ (Tree _) (sym (refl 0)) leaf)        ≡⟨ cong (λ eq → cons _ (substᴱ (Tree _) eq _)) (ℕ-set _ _) ⟩
      cons y (substᴱ (Tree _) (refl 0) leaf)              ≡⟨ cong (cons _) (substᴱ-refl {P = Tree _}) ⟩
      cons y leaf                                         ≡⟨ node-cong ax (refl _) (refl _) (refl _) ⟩∎
      node y leaf leaf inv (refl 0)                       ∎)
                                                         _ ⟩∎
    node y leaf leaf inv eq                         ∎
    where
    open Erased.[]-cong₁ ax
  cons-uncons {t = node _ leaf non-empty inv _} =
    ⊥-elim (0≢+ (_⇔_.to Invariant-zero inv))
  cons-uncons {ax} {t = node y t₁@non-empty t₂ inv eq} =
    let z , t₁′ = uncons ax t₁
        eq′     = _
    in
    cons y (substᴱ (Tree _) eq′ (node z t₂ t₁′ _ _))             ≡⟨ sym (substᴱ-cons ax) ⟩
    substᴱ (Tree _) (cong suc eq′) (cons y (node z t₂ t₁′ _ _))  ≡⟨⟩
    substᴱ (Tree _) (cong suc eq′) (node y (cons z t₁′) t₂ _ _)  ≡⟨ substᴱ-node ax ⟩
    node y (cons z t₁′) t₂ _ _                                   ≡⟨ node-cong ax (refl _) cons-uncons (refl _) ⟩
    node y t₁ t₂ inv eq                                          ∎
    where
    open Erased.[]-cong₁ ax

opaque

  -- Tree A (suc n) is equivalent (with erased proofs) to A × Tree A n,
  -- for an erased n, given a certain assumption.

  Tree-suc :
    []-cong-axiomatisation lzero →
    Tree A (suc n) ≃ᴱ (A × Tree A n)
  Tree-suc ax =
    EEq.↔→≃ᴱ (uncons ax) (uncurry cons) (λ _ → uncons-cons)
      (λ _ → cons-uncons)

------------------------------------------------------------------------
-- Conversion to and from vectors

opaque

  -- Converts a vector to a tree.
  --
  -- This implementation could perhaps be improved, following Okasaki's
  -- text.

  from-Vec : Vec A n → Tree A n
  from-Vec []       = empty
  from-Vec (x ∷ xs) = cons x (from-Vec xs)

opaque

  -- Converts a tree to a vector.
  --
  -- This implementation could perhaps be improved, following "Proof
  -- Pearl: Braun Trees" by Nipkow and Sewell.

  to-Vec :
    []-cong-axiomatisation lzero →
    Tree A n → Vec A n
  to-Vec _  leaf        = []
  to-Vec ax t@non-empty with uncons ax t
  … | x , t = x ∷ to-Vec ax t

opaque
  unfolding cons to-Vec uncons

  -- A lemma related to to-Vec and cons.

  to-Vec-cons :
    to-Vec ax (cons x t) ≡ x ∷ to-Vec ax t
  to-Vec-cons {ax} {x} {t = leaf} =
    x ∷ to-Vec ax (substᴱ (Tree _) _ leaf)  ≡⟨ cong (λ t → _ ∷ to-Vec _ t) $
                                               substᴱ-leaf ax ⟩
    x ∷ to-Vec ax leaf                      ∎
    where
    open Erased.[]-cong₁ ax
  to-Vec-cons {ax} {x} {t = t@non-empty} =
    let x′ , t′ = uncons ax (cons x t)
        lemma   = uncons-cons {t = t}
    in
    x′ ∷ to-Vec ax t′  ≡⟨ cong₂ _∷_ (cong proj₁ lemma) (cong (to-Vec _) (cong proj₂ lemma)) ⟩∎
    x ∷ to-Vec ax t    ∎

opaque
  unfolding empty from-Vec to-Vec

  -- The type Tree A n is equivalent (with erased proofs) to Vec A n,
  -- for an erased n, given a certain assumption.

  Tree≃ᴱVec :
    []-cong-axiomatisation lzero →
    Tree A n ≃ᴱ Vec A n
  Tree≃ᴱVec ax = EEq.↔→≃ᴱ (to-Vec ax) from-Vec to-from from-to
    where
    opaque

      to-from : (xs : Vec A n) → to-Vec ax (from-Vec xs) ≡ xs
      to-from []       = refl _
      to-from (x ∷ xs) =
        to-Vec ax (cons x (from-Vec xs))  ≡⟨ to-Vec-cons ⟩
        x ∷ to-Vec ax (from-Vec xs)       ≡⟨ cong (_∷_ _) (to-from _) ⟩
        x ∷ xs                            ∎

      @0 from-to : (t : Tree A n) → from-Vec (to-Vec ax t) ≡ t
      from-to leaf                    = refl _
      from-to t@(node x t₁ t₂ inv eq) =
        let y , t′ = uncons ax t in
        cons y (from-Vec (to-Vec ax t′))  ≡⟨ cong (cons _) (from-to _) ⟩
        cons y t′                         ≡⟨⟩
        uncurry cons (uncons ax t)        ≡⟨ cons-uncons ⟩∎
        t                                 ∎
