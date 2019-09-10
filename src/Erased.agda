------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality

module Erased
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

import Equality.Path as P
open import Logical-equivalence using (_⇔_)
open import Prelude hiding ([_,_])

open import Bijection eq using (_↔_)
open import Embedding eq as Emb using (Embedding; Is-embedding)
import Embedding P.equality-with-J as PE
open import Equality.Path.Isomorphisms eq
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq
open import H-level eq as H-level
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
  using (Surjective)
open import Injection eq using (_↣_)
open import Monad eq
open import Surjection eq using (_↠_)

private
  variable
    a b ℓ p : Level
    A       : Set a
    k x y   : A
    n       : ℕ

------------------------------------------------------------------------
-- The type

-- Erased A is like A, but the values are (supposed to be) erased at
-- run-time.

record Erased (@0 A : Set a) : Set a where
  constructor [_]
  field
    @0 erased : A

open Erased public

------------------------------------------------------------------------
-- Erased is a monad

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ :
  {@0 A : Set a} {@0 B : Set b} →
  Erased A → (A → Erased B) → Erased B
[ x ] >>=′ f = [ erased (f x) ]

instance

  -- Erased is a monad.

  raw-monad : Raw-monad {c = ℓ} Erased
  Raw-monad.return raw-monad = [_]
  Raw-monad._>>=_  raw-monad = _>>=′_

  monad : Monad {c = ℓ} Erased
  Monad.raw-monad      monad = raw-monad
  Monad.left-identity  monad = λ _ _ → refl _
  Monad.right-identity monad = λ _ → refl _
  Monad.associativity  monad = λ _ _ _ → refl _

------------------------------------------------------------------------
-- Some isomorphisms

-- In an erased context Erased A is always isomorphic to A.

Erased↔ : {@0 A : Set a} → Erased (Erased A ↔ A)
Erased↔ = [ record
  { surjection = record
    { logical-equivalence = record
      { to   = erased
      ; from = [_]
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  } ]

-- Erased ⊤ is isomorphic to ⊤.

Erased-⊤↔⊤ : Erased ⊤ ↔ ⊤
Erased-⊤↔⊤ = record
  { surjection = record
    { right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

-- Erased ⊥ is isomorphic to ⊥.

Erased-⊥↔⊥ : Erased (⊥ {ℓ = ℓ}) ↔ ⊥ {ℓ = ℓ}
Erased-⊥↔⊥ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { [ () ] }
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ { [ () ] }
  }

-- Erased commutes with Π A.

Erased-Π↔Π :
  {@0 P : A → Set p} →
  Erased ((x : A) → P x) ↔ ((x : A) → Erased (P x))
Erased-Π↔Π = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { [ f ] x → [ f x ] }
      ; from = λ f → [ (λ x → erased (f x)) ]
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

-- Erased commutes with Σ.

Erased-Σ↔Σ :
  {@0 A : Set a} {@0 P : A → Set p} →
  Erased (Σ A P) ↔ Σ (Erased A) (λ x → Erased (P (erased x)))
Erased-Σ↔Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { [ p ] → [ proj₁ p ] , [ proj₂ p ] }
      ; from = λ { ([ x ] , [ y ]) → [ x , y ] }
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

-- There is a bijection between erased paths and paths between
-- erased values.

Erased-Path↔Path-[]-[] :
  {@0 A : Set a} {@0 x y : A} →
  Erased (x P.≡ y) ↔ [ x ] P.≡ [ y ]
Erased-Path↔Path-[]-[] = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { [ eq ] i → [ eq i ] }
      ; from = λ eq → [ P.cong erased eq ]
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

-- Given an erased proof of equality of x and y one can show that
-- [ x ] is equal to [ y ].

[]-cong : {@0 A : Set a} {@0 x y : A} →
          Erased (x ≡ y) → [ x ] ≡ [ y ]
[]-cong {x = x} {y = y} =
  Erased (x ≡ y)    ↝⟨ (λ { [ eq ] → [ _↔_.to ≡↔≡ eq ] }) ⟩
  Erased (x P.≡ y)  ↔⟨ Erased-Path↔Path-[]-[] ⟩
  [ x ] P.≡ [ y ]   ↔⟨ inverse ≡↔≡ ⟩□
  [ x ] ≡ [ y ]     □

-- Erased commutes with W.

Erased-W↔W :
  {@0 A : Set a} {@0 P : A → Set p} →
  Erased (W A P) ↔ W (Erased A) (λ x → Erased (P (erased x)))
Erased-W↔W {A = A} {P = P} = record
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
  to : Erased (W A P) → W (Erased A) (λ x → Erased (P (erased x)))
  to [ sup x f ] = sup [ x ] λ { [ y ] → to [ f y ] }

  from : W (Erased A) (λ x → Erased (P (erased x))) → Erased (W A P)
  from (sup [ x ] f) = [ sup x (λ y → erased (from (f [ y ]))) ]

  to∘from :
    (x : W (Erased A) (λ x → Erased (P (erased x)))) →
    to (from x) ≡ x
  to∘from (sup [ x ] f) =
    cong (sup [ x ]) (⟨ext⟩ λ { [ y ] →
      to∘from (f [ y ]) })

  from∘to : (x : Erased (W A P)) → from (to x) ≡ x
  from∘to [ sup x f ] =
    []-cong [ cong (sup x) (⟨ext⟩ λ y →
      cong erased (from∘to [ f y ])) ]

-- Erased commutes with ↑ ℓ.

Erased-↑↔↑ :
  {@0 A : Set a} →
  Erased (↑ ℓ A) ↔ ↑ ℓ (Erased A)
Erased-↑↔↑ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { [ x ] → lift [ lower x ] }
      ; from = λ { (lift [ x ]) → [ lift x ] }
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

------------------------------------------------------------------------
-- Erased preserves all kinds of functions

private

  -- The following lemmas are not exported, but Erased-cong (defined
  -- below) is.

  module _ {@0 A : Set a} {@0 B : Set b} where

    Erased-cong-→ : @0 (A → B) → Erased A → Erased B
    Erased-cong-→ A→B [ x ] = [ A→B x ]

  module _ {@0 A : Set a} {@0 B : Set b} where

    Erased-cong-⇔ : @0 (A ⇔ B) → Erased A ⇔ Erased B
    Erased-cong-⇔ A⇔B = record
      { to   = Erased-cong-→ (_⇔_.to   A⇔B)
      ; from = Erased-cong-→ (_⇔_.from A⇔B)
      }

    Erased-cong-↠ : @0 A ↠ B → Erased A ↠ Erased B
    Erased-cong-↠ A↠B = record
      { logical-equivalence = Erased-cong-⇔
                                (_↠_.logical-equivalence A↠B)
      ; right-inverse-of    = λ { [ x ] →
          []-cong [ _↠_.right-inverse-of A↠B x ] }
      }

    Erased-cong-↔ : @0 A ↔ B → Erased A ↔ Erased B
    Erased-cong-↔ A↔B = record
      { surjection      = Erased-cong-↠ (_↔_.surjection A↔B)
      ; left-inverse-of = λ { [ x ] →
          []-cong [ _↔_.left-inverse-of A↔B x ] }
      }

    Erased-cong-≃ : @0 A ≃ B → Erased A ≃ Erased B
    Erased-cong-≃ A≃B =
      from-isomorphism (Erased-cong-↔ (from-isomorphism A≃B))

-- There is a bijection between erased equality proofs and equalities
-- between erased values.

Erased-≡↔[]≡[] :
  {@0 A : Set a} {@0 x y : A} →
  Erased (x ≡ y) ↔ [ x ] ≡ [ y ]
Erased-≡↔[]≡[] {x = x} {y = y} =
  Erased (x ≡ y)    ↝⟨ Erased-cong-↔ ≡↔≡ ⟩
  Erased (x P.≡ y)  ↝⟨ Erased-Path↔Path-[]-[] ⟩
  [ x ] P.≡ [ y ]   ↝⟨ inverse ≡↔≡ ⟩□
  [ x ] ≡ [ y ]     □

-- Some lemmas related to Erased-≡↔[]≡[].

to-Erased-≡↔[]≡[] :
  {A : Set a} {x y : A} {x≡y : x ≡ y} →
  _↔_.to Erased-≡↔[]≡[] [ x≡y ] ≡ cong [_] x≡y
to-Erased-≡↔[]≡[] {x≡y = x≡y} =
  _↔_.from ≡↔≡ (P.cong [_] (_↔_.to ≡↔≡ x≡y))  ≡⟨ sym cong≡cong ⟩
  cong [_] (_↔_.from ≡↔≡ (_↔_.to ≡↔≡ x≡y))    ≡⟨ cong (cong [_]) $ _↔_.left-inverse-of ≡↔≡ x≡y ⟩∎
  cong [_] x≡y                                ∎

from-Erased-≡↔[]≡[] :
  {@0 A : Set a} {@0 x y : A} {@0 x≡y : [ x ] ≡ [ y ]} →
  _↔_.from Erased-≡↔[]≡[] x≡y ≡ [ cong erased x≡y ]
from-Erased-≡↔[]≡[] {x≡y = x≡y} = []-cong
  [ _↔_.from ≡↔≡ (P.cong erased (_↔_.to ≡↔≡ x≡y))  ≡⟨ sym cong≡cong ⟩
    cong erased (_↔_.from ≡↔≡ (_↔_.to ≡↔≡ x≡y))    ≡⟨ cong (cong erased) $ _↔_.left-inverse-of ≡↔≡ x≡y ⟩∎
    cong erased x≡y                                ∎
  ]

module _ {@0 A : Set a} {@0 B : Set b} where

  private

    -- The following lemmas are not exported, but Erased-cong (defined
    -- below) is.

    Erased-cong-↣ : @0 A ↣ B → Erased A ↣ Erased B
    Erased-cong-↣ A↣B = record
      { to        = Erased-cong-→ (_↣_.to A↣B)
      ; injective = λ { {x = [ x ]} {y = [ y ]} →
          [ _↣_.to A↣B x ] ≡ [ _↣_.to A↣B y ]   ↔⟨ inverse Erased-≡↔[]≡[] ⟩
          Erased (_↣_.to A↣B x ≡ _↣_.to A↣B y)  ↝⟨ Erased-cong-→ (_↣_.injective A↣B) ⟩
          Erased (x ≡ y)                        ↔⟨ Erased-≡↔[]≡[] ⟩□
          [ x ] ≡ [ y ]                         □ }
      }

    Erased-cong-Embedding :
      @0 Embedding A B → Embedding (Erased A) (Erased B)
    Erased-cong-Embedding A↣B =
      _↔_.from Embedding↔Embedding
        (Erased-cong-Embedding′
           (_↔_.to Embedding↔Embedding A↣B))
      where
      Erased-cong-Embedding′ :
        @0 PE.Embedding A B → PE.Embedding (Erased A) (Erased B)
      Erased-cong-Embedding′ A↣B = record
        { to           = Erased-cong-→ (M.to A↣B)
        ; is-embedding = λ { [ x ] [ y ] →
            _↔_.to Is-equivalence↔Is-equivalence $
            _≃_.is-equivalence (
              [ x ] P.≡ [ y ]                     ↔⟨ inverse Erased-Path↔Path-[]-[] ⟩
              Erased (x P.≡ y)                    ↝⟨ Erased-cong-≃ (_↔_.from ≃↔≃ $ M.equivalence A↣B) ⟩
              Erased (M.to A↣B x P.≡ M.to A↣B y)  ↔⟨ Erased-Path↔Path-[]-[] ⟩□
              [ M.to A↣B x ] P.≡ [ M.to A↣B y ]   □) }
        }
        where
        module M = PE.Embedding

  -- Erased preserves all kinds of functions.

  Erased-cong : @0 A ↝[ k ] B → Erased A ↝[ k ] Erased B
  Erased-cong {k = implication}         = Erased-cong-→
  Erased-cong {k = logical-equivalence} = Erased-cong-⇔
  Erased-cong {k = injection}           = Erased-cong-↣
  Erased-cong {k = embedding}           = Erased-cong-Embedding
  Erased-cong {k = surjection}          = Erased-cong-↠
  Erased-cong {k = bijection}           = Erased-cong-↔
  Erased-cong {k = equivalence}         = Erased-cong-≃

------------------------------------------------------------------------
-- All h-levels are closed under Erased

private

  -- The following two lemmas are not used below, they are included to
  -- illustrate a somewhat different proof technique that works for
  -- individual h-levels (given by closed natural numbers).

  -- Is-proposition is closed under Erased.

  Is-proposition-closure :
    {@0 A : Set a} →
    @0 Is-proposition A → Is-proposition (Erased A)
  Is-proposition-closure {A = A} prop =
    _↔_.from (H-level↔H-level 1)
      (Is-proposition-closure′
         (_↔_.to (H-level↔H-level 1) prop))
    where
    Is-proposition-closure′ :
      @0 P.Is-proposition A → P.Is-proposition (Erased A)
    Is-proposition-closure′ prop x y = λ i →
      [ prop (erased x) (erased y) i ]

  -- Is-set is closed under Erased.

  Is-set-closure :
    {@0 A : Set a} →
    @0 Is-set A → Is-set (Erased A)
  Is-set-closure {A = A} set =
    _↔_.from (H-level↔H-level 2)
      (Is-set-closure′
         (_↔_.to (H-level↔H-level 2) set))
    where
    Is-set-closure′ : @0 P.Is-set A → P.Is-set (Erased A)
    Is-set-closure′ set p q = λ i j →
      [ set (P.cong erased p) (P.cong erased q) i j ]

  -- Erased commutes with H-level′ n (in one direction).

  Erased-H-level′ :
    {@0 A : Set a} →
    Erased (H-level′ n A) → H-level′ n (Erased A)
  Erased-H-level′ {n = zero} [ h ] =
      [ proj₁ h ]
    , λ { [ x ] → []-cong [ proj₂ h x ] }
  Erased-H-level′ {n = suc n} [ h ] [ x ] [ y ] =
                                 $⟨ Erased-H-level′ [ h x y ] ⟩
    H-level′ n (Erased (x ≡ y))  ↝⟨ H-level.respects-surjection′ (_↔_.surjection Erased-≡↔[]≡[]) n ⟩□
    H-level′ n ([ x ] ≡ [ y ])   □

  -- Erased commutes with H-level n (in one direction).

  Erased-H-level :
    {@0 A : Set a} →
    Erased (H-level n A) → H-level n (Erased A)
  Erased-H-level {n = n} {A = A} =
    Erased (H-level n A)   ↝⟨ _⇔_.to $ Erased-cong H-level⇔H-level′ ⟩
    Erased (H-level′ n A)  ↝⟨ Erased-H-level′ ⟩
    H-level′ n (Erased A)  ↝⟨ _⇔_.from H-level⇔H-level′ ⟩□
    H-level n (Erased A)   □

-- H-level n is closed under Erased.

H-level-Erased :
  {@0 A : Set a} →
  ∀ n → @0 H-level n A → H-level n (Erased A)
H-level-Erased _ h = Erased-H-level [ h ]

-- Erased commutes with H-level′ n.

Erased-H-level′↔H-level′ :
  {@0 A : Set a} →
  Erased (H-level′ n A) ↔ H-level′ n (Erased A)
Erased-H-level′↔H-level′ {n = n} {A = A} =
  from-isomorphism $
  _↠_.from (Eq.≃↠⇔ (H-level-Erased 1 (H-level′-propositional ext _))
                   (H-level′-propositional ext _)) $
  record
    { to   = Erased-H-level′
    ; from = λ h →
       [                        $⟨ h ⟩
         H-level′ n (Erased A)  ↝⟨ _⇔_.from H-level⇔H-level′ ⟩
         H-level n (Erased A)   ↝⟨ H-level-cong _ n (erased Erased↔) ⟩
         H-level n A            ↝⟨ _⇔_.to H-level⇔H-level′ ⟩□
         H-level′ n A           □
       ]
    }

-- Erased commutes with H-level n.

Erased-H-level↔H-level :
  {@0 A : Set a} →
  Erased (H-level n A) ↔ H-level n (Erased A)
Erased-H-level↔H-level {n = n} {A = A} =
  Erased (H-level n A)   ↝⟨ Erased-cong (H-level↔H-level′ ext) ⟩
  Erased (H-level′ n A)  ↝⟨ Erased-H-level′↔H-level′ ⟩
  H-level′ n (Erased A)  ↝⟨ inverse (H-level↔H-level′ ext) ⟩□
  H-level n (Erased A)   □

------------------------------------------------------------------------
-- [_] is sometimes an embedding and/or surjective

-- See also Very-stable→Is-embedding-[] and Very-stable→Surjective-[]
-- in Erased.Stability.

-- If A is a proposition, then [_] {A = A} is an embedding.

Is-proposition→Is-embedding-[] :
  Is-proposition A → Is-embedding ([_] {A = A})
Is-proposition→Is-embedding-[] prop =
  _≃_.to (Emb.Injective≃Is-embedding ext set (H-level-Erased 2 set) [_])
    (λ _ → prop _ _)
  where
  set = mono₁ 1 prop

-- In an erased context [_] is always an embedding.

Erased-Is-embedding-[] :
  {@0 A : Set a} → Erased (Is-embedding ([_] {A = A}))
Erased-Is-embedding-[] =
  [ (λ x y → _≃_.is-equivalence (
       x ≡ y          ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ $ inverse $ erased Erased↔ ⟩□
       [ x ] ≡ [ y ]  □))
  ]

-- In an erased context [_] is always surjective.

Erased-Surjective-[] :
  {@0 A : Set a} → Erased (Surjective ([_] {A = A}))
Erased-Surjective-[] =
  [ (λ { [ x ] → Trunc.∣ x , refl _ ∣ }) ]

------------------------------------------------------------------------
-- Another lemma

-- [_] can be "pushed" through subst.

push-subst-[] :
  {@0 P : A → Set p} {@0 p : P x} {x≡y : x ≡ y} →
  subst (λ x → Erased (P x)) x≡y [ p ] ≡ [ subst P x≡y p ]
push-subst-[] {P = P} {p = p} = elim¹
  (λ x≡y → subst (λ x → Erased (P x)) x≡y [ p ] ≡ [ subst P x≡y p ])
  (subst (λ x → Erased (P x)) (refl _) [ p ]  ≡⟨ subst-refl _ _ ⟩
   [ p ]                                      ≡⟨ []-cong [ sym $ subst-refl _ _ ] ⟩∎
   [ subst P (refl _) p ]                     ∎)
  _

private

  -- One can prove the previous lemma very easily when path equality
  -- is used.

  push-subst-[]′ :
    {@0 P : A → Set p} {@0 p : P x} {x≡y : x P.≡ y} →
    P.subst (λ x → Erased (P x)) x≡y [ p ] ≡ [ P.subst P x≡y p ]
  push-subst-[]′ = refl _
