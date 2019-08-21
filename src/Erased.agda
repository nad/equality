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

open import Bijection eq as Bijection using (_↔_)
open import Embedding eq as Emb using (Embedding; Is-embedding)
import Embedding P.equality-with-J as PE
open import Equality.Decidable-UIP eq
open import Equality.Decision-procedures eq
open import Equality.Path.Isomorphisms eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
import Equivalence P.equality-with-J as PEq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; Surjective)
open import Injection eq using (_↣_)
import List eq as L
open import Monad eq
import Nat eq as Nat
open import Surjection eq using (_↠_)

private
  variable
    a b ℓ p : Level
    A B     : Set a
    P       : A → Set p
    k x y   : A
    n       : ℕ
    A↠B     : A ↠ B

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

private

  -- The following two lemmas are not exported, but Erased-≡↔[]≡[]
  -- (defined below) is.

  -- There is a bijection between erased paths and paths between
  -- erased values.

  Erased-≡↔[]≡[]′ :
    {@0 A : Set a} {@0 x y : A} →
    Erased (x P.≡ y) ↔ [ x ] P.≡ [ y ]
  Erased-≡↔[]≡[]′ = record
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
    Erased (x P.≡ y)  ↔⟨ Erased-≡↔[]≡[]′ ⟩
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
  Erased (x P.≡ y)  ↝⟨ Erased-≡↔[]≡[]′ ⟩
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
              [ x ] P.≡ [ y ]                     ↔⟨ inverse Erased-≡↔[]≡[]′ ⟩
              Erased (x P.≡ y)                    ↝⟨ Erased-cong-≃ (_↔_.from ≃↔≃ $ M.equivalence A↣B) ⟩
              Erased (M.to A↣B x P.≡ M.to A↣B y)  ↔⟨ Erased-≡↔[]≡[]′ ⟩□
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
  Is-set-closure {A = A} prop =
    _↔_.from (H-level↔H-level 2)
      (Is-set-closure′
         (_↔_.to (H-level↔H-level 2) prop))
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
-- Stability

mutual

  -- A type is stable if Erased A implies A.

  Stable : Set a → Set a
  Stable = Stable-[ implication ]

  -- A generalisation of Stable.

  Stable-[_] : Kind → Set a → Set a
  Stable-[ k ] A = Erased A ↝[ k ] A

-- A special case of Stable-[ equivalence ].

Very-stable : Set a → Set a
Very-stable A = Is-equivalence ([_] {A = A})

-- Variants of the definitions above for equality.

mutual

  Stable-≡ : Set a → Set a
  Stable-≡ A = Stable-≡-[ implication ] A

  Stable-≡-[_] : Kind → Set a → Set a
  Stable-≡-[ k ] A = {x y : A} → Stable-[ k ] (x ≡ y)

Very-stable-≡ : Set a → Set a
Very-stable-≡ A = {x y : A} → Very-stable (x ≡ y)

-- Very-stable is propositional.

Very-stable-propositional : Is-proposition (Very-stable A)
Very-stable-propositional = Eq.propositional ext _

-- Very-stable-≡ is propositional.

Very-stable-≡-propositional : Is-proposition (Very-stable-≡ A)
Very-stable-≡-propositional =
  implicit-Π-closure ext 1 λ _ →
  implicit-Π-closure ext 1 λ _ →
  Very-stable-propositional

-- Very stable types are stable.

Very-stable→Stable : Very-stable A → Stable-[ k ] A
Very-stable→Stable {A = A} {k = k} =
  Very-stable A             ↝⟨ Eq.⟨ _ ,_⟩ ⟩
  A ≃ Erased A              ↝⟨ inverse ⟩
  Erased A ≃ A              ↔⟨⟩
  Stable-[ equivalence ] A  ↝⟨ from-equivalence ⟩□
  Stable-[ k ] A            □

-- The function obtained from Very-stable→Stable (for k = implication)
-- maps [ x ] to x.
--
-- This seems to imply that (say) the booleans can not be proved to be
-- very stable (assuming that Agda is consistent), because
-- implementing a function that resurrects a boolean, given no
-- information about what the boolean was, is impossible. However, the
-- booleans are stable: this follows from Dec→Stable below. Thus it
-- seems as if one can not prove that all stable types are very
-- stable.

Very-stable→Stable-[]≡id :
  (s : Very-stable A) →
  Very-stable→Stable s [ x ] ≡ x
Very-stable→Stable-[]≡id {x = x} s =
  Very-stable→Stable s [ x ]   ≡⟨⟩
  _≃_.from Eq.⟨ _ , s ⟩ [ x ]  ≡⟨ _≃_.left-inverse-of Eq.⟨ _ , s ⟩ x ⟩∎
  x                            ∎

-- Erased A is very stable.

Very-stable-Erased :
  {@0 A : Set a} → Very-stable (Erased A)
Very-stable-Erased {A = A} =
  _≃_.is-equivalence (            $⟨ Erased↔ ⟩
    Erased (Erased A ↔ A)         ↝⟨ (λ hyp → Erased-cong (erased hyp)) ⟩
    Erased (Erased A) ↔ Erased A  ↝⟨ Eq.↔⇒≃ ∘ inverse ⟩□
    Erased A ≃ Erased (Erased A)  □)

-- In an erased context every type is very stable.
--
-- Presumably "not in an erased context" is not expressible
-- internally, so it seems as if it should not be possible to prove
-- that any type is /not/ very stable (in an empty, non-erased
-- context).

Erased-Very-stable :
  {@0 A : Set a} → Erased (Very-stable A)
Erased-Very-stable {A = A} =
  [ _≃_.is-equivalence (    $⟨ Erased↔ ⟩
      Erased (Erased A ↔ A) ↝⟨ erased ⟩
      Erased A ↔ A          ↝⟨ Eq.↔⇒≃ ∘ inverse ⟩□
      A ≃ Erased A          □)
  ]

-- If A is stable, then A is "logical equivalence stable".

Stable→Stable⇔ :
  {@0 A : Set a} → Stable A → Stable-[ logical-equivalence ] A
Stable→Stable⇔ stable = record
  { from = [_]
  ; to   = stable
  }

-- If A is a stable proposition, then A is very stable.

Stable-proposition→Very-stable :
  Stable A → Is-proposition A → Very-stable A
Stable-proposition→Very-stable {A = A} s prop =
  _≃_.is-equivalence (inverse lemma)
  where
  lemma =                             $⟨ s ⟩
    Stable A                          ↝⟨ Stable→Stable⇔ ⟩
    Stable-[ logical-equivalence ] A  ↝⟨ _↠_.from (Eq.≃↠⇔ (H-level-Erased 1 prop) prop) ⟩□
    Stable-[ equivalence ] A          □

-- Erased A implies ¬ ¬ A.

Erased→¬¬ : {@0 A : Set a} → Erased A → ¬ ¬ A
Erased→¬¬ [ x ] f = _↔_.to Erased-⊥↔⊥ [ f x ]

-- Types that are stable for double negation are stable for Erased.

¬¬-Stable→Stable : {@0 A : Set a} → (¬ ¬ A → A) → Stable A
¬¬-Stable→Stable ¬¬-Stable x = ¬¬-Stable (Erased→¬¬ x)

-- Types for which it is known whether or not they are inhabited are
-- stable.

Dec→Stable : {@0 A : Set a} → Dec A → Stable A
Dec→Stable (yes x) _ = x
Dec→Stable (no ¬x) x with Erased→¬¬ x ¬x
... | ()

-- If equality is decidable for A, then equality is very stable for A.

Decidable-equality→Very-stable-≡ :
  Decidable-equality A → Very-stable-≡ A
Decidable-equality→Very-stable-≡ dec =
  Stable-proposition→Very-stable
    (Dec→Stable (dec _ _))
    (decidable⇒set dec)

------------------------------------------------------------------------
-- Preservation lemmas related to Stable, Stable-[_] and Very-stable

-- A kind of map function for Stable-[_].

Stable-map :
  A ↝[ k ] B → @0 B ↝[ k ] A → Stable-[ k ] A → Stable-[ k ] B
Stable-map {A = A} {B = B} A↝B B↝A s =
  Erased B  ↝⟨ Erased-cong B↝A ⟩
  Erased A  ↝⟨ s ⟩
  A         ↝⟨ A↝B ⟩□
  B         □

-- A variant of Stable-map.

Stable-map-↔ : A ↔ B → Stable-[ k ] A → Stable-[ k ] B
Stable-map-↔ A↔B =
  Stable-map (from-isomorphism A↔B) (from-isomorphism $ inverse A↔B)

-- Stable preserves some kinds of functions (those that are
-- "symmetric").

Stable-cong : A ↝[ ⌊ k ⌋-sym ] B → Stable A ↝[ ⌊ k ⌋-sym ] Stable B
Stable-cong {A = A} {k = k} {B = B} A↝B =
  Stable A        ↔⟨⟩
  (Erased A → A)  ↝⟨ →-cong (forget-ext? ⌊ k ⌋-sym ext) (Erased-cong A↝B) A↝B ⟩
  (Erased B → B)  ↔⟨⟩
  Stable B        □

-- Stable-[ logical-equivalence ] preserves logical equivalences.

Stable-⇔-cong :
  A ⇔ B →
  Stable-[ logical-equivalence ] A ⇔ Stable-[ logical-equivalence ] B
Stable-⇔-cong {A = A} {B = B} A⇔B =
  Stable-[ logical-equivalence ] A  ↔⟨⟩
  Erased A ⇔ A                      ↝⟨ ⇔-cong-⇔ (Erased-cong A⇔B) A⇔B ⟩
  Erased B ⇔ B                      ↔⟨⟩
  Stable-[ logical-equivalence ] B  □

-- Stable-[ equivalence ] preserves equivalences.

Stable-≃-cong :
  A ≃ B → Stable-[ equivalence ] A ≃ Stable-[ equivalence ] B
Stable-≃-cong {A = A} {B = B} A≃B =
  Stable-[ equivalence ] A  ↔⟨⟩
  Erased A ≃ A              ↝⟨ Eq.≃-preserves ext (Erased-cong A≃B) A≃B ⟩
  Erased B ≃ B              ↔⟨⟩
  Stable-[ equivalence ] B  □

-- Very-stable preserves equivalences.

Very-stable-cong : A ≃ B → Very-stable A ≃ Very-stable B
Very-stable-cong A≃B =
  _↠_.from (Eq.≃↠⇔ (Eq.propositional ext _)
                   (Eq.propositional ext _))
    (record
       { to   = lemma A≃B
       ; from = lemma (inverse A≃B)
       })
  where
  lemma : A ≃ B → Very-stable A → Very-stable B
  lemma {A = A} {B = B} A≃B s = _≃_.is-equivalence $
    Eq.with-other-function
      (B         ↝⟨ inverse A≃B ⟩
       A         ↝⟨ Eq.⟨ [_] , s ⟩ ⟩
       Erased A  ↝⟨ Erased-cong-≃ A≃B ⟩□
       Erased B  □)
      [_]
      (λ x →
         [ _≃_.to A≃B (_≃_.from A≃B x) ]  ≡⟨ cong [_] (_≃_.right-inverse-of A≃B x) ⟩∎
         [ x ]                            ∎)

------------------------------------------------------------------------
-- Closure properties related to Stable, Stable-[_] and Very-stable

-- A closure property for _≡_.

Stable→Stable-≡ :
  (s : Stable A) →
  (∀ x → s [ x ] ≡ x) →
  Stable-≡ A
Stable→Stable-≡ s hyp {x = x} {y = y} =
  Erased (x ≡ y)     ↔⟨ Erased-≡↔[]≡[] ⟩
  [ x ] ≡ [ y ]      ↝⟨ cong s ⟩
  s [ x ] ≡ s [ y ]  ↝⟨ (λ eq → trans (sym (hyp x)) (trans eq (hyp y))) ⟩□
  x ≡ y              □

private

  -- If A is very stable, then the types of paths between values of
  -- type A are very stable.

  Very-stable→Very-stable-≡′ :
    {x y : A} → Very-stable A → Very-stable (x P.≡ y)
  Very-stable→Very-stable-≡′ {x = x} {y = y} s = _≃_.is-equivalence (
    x P.≡ y           ↝⟨ inverse $ _↔_.from ≃↔≃ $ PEq.≃-≡ $ _↔_.to ≃↔≃ $ Eq.⟨ _ , s ⟩ ⟩
    [ x ] P.≡ [ y ]   ↔⟨ inverse Erased-≡↔[]≡[]′ ⟩□
    Erased (x P.≡ y)  □)

-- If A is very stable, then the types of equalities between values of
-- type A are very stable.

Very-stable→Very-stable-≡ : Very-stable A → Very-stable-≡ A
Very-stable→Very-stable-≡ s {x = x} {y = y} =
  _≃_.is-equivalence $
  Eq.with-other-function
    (x ≡ y             ↔⟨ ≡↔≡ ⟩
     x P.≡ y           ↝⟨ inverse $ Very-stable→Stable (Very-stable→Very-stable-≡′ s) ⟩
     Erased (x P.≡ y)  ↔⟨ Erased-cong (inverse ≡↔≡) ⟩□
     Erased (x ≡ y)    □)
    [_]
    (λ eq →
      [ _↔_.from ≡↔≡ (_↔_.to ≡↔≡ eq) ]  ≡⟨ cong [_] (_↔_.left-inverse-of ≡↔≡ eq) ⟩∎
      [ eq ]                            ∎)

private

  -- Some examples showing how Very-stable→Very-stable-≡ can be used.

  -- Equalities between erased values are very stable.

  Very-stable-≡₀ : {@0 A : Set a} → Very-stable-≡ (Erased A)
  Very-stable-≡₀ = Very-stable→Very-stable-≡ Very-stable-Erased

  -- Equalities between equalities between erased values are very
  -- stable.

  Very-stable-≡₁ :
    {@0 A : Set a} {x y : Erased A} →
    Very-stable-≡ (x ≡ y)
  Very-stable-≡₁ = Very-stable→Very-stable-≡ Very-stable-≡₀

  -- And so on…

-- ⊤ is very stable.

Very-stable-⊤ : Very-stable ⊤
Very-stable-⊤ =
  Stable-proposition→Very-stable
    (Dec→Stable (yes tt))
    (mono₁ 0 ⊤-contractible)

-- ⊥ is very stable.

Very-stable-⊥ : Very-stable (⊥ {ℓ = ℓ})
Very-stable-⊥ =
  Stable-proposition→Very-stable
    (Dec→Stable (no λ ()))
    ⊥-propositional

-- Stable-[ k ] is closed under Π A.

Stable-Π : (∀ x → Stable-[ k ] (P x)) → Stable-[ k ] ((x : A) → P x)
Stable-Π {k = k} {P = P} s =
  Erased (∀ x → P x)    ↔⟨ Erased-Π↔Π ⟩
  (∀ x → Erased (P x))  ↝⟨ ∀-cong (forget-ext? k ext) s ⟩□
  (∀ x → P x)           □

-- A variant for equality.

Stable-≡-Π :
  {f g : (x : A) → P x} →
  (∀ x → Stable-[ k ] (f x ≡ g x)) →
  Stable-[ k ] (f ≡ g)
Stable-≡-Π {k = k} {f = f} {g = g} =
  (∀ x → Stable-[ k ] (f x ≡ g x))  ↝⟨ Stable-Π ⟩
  Stable-[ k ] (∀ x → f x ≡ g x)    ↝⟨ Stable-map-↔ (_≃_.bijection $ Eq.extensionality-isomorphism ext) ⟩□
  Stable-[ k ] (f ≡ g)              □

-- Very-stable is closed under Π A.

Very-stable-Π : (∀ x → Very-stable (P x)) → Very-stable ((x : A) → P x)
Very-stable-Π s = _≃_.is-equivalence $
  inverse $ Stable-Π $ λ x → inverse Eq.⟨ _ , s x ⟩

-- A variant for equality.

Very-stable-≡-Π :
  {f g : (x : A) → P x} →
  (∀ x → Very-stable (f x ≡ g x)) →
  Very-stable (f ≡ g)
Very-stable-≡-Π {f = f} {g = g} =
  (∀ x → Very-stable (f x ≡ g x))  ↝⟨ Very-stable-Π ⟩
  Very-stable (∀ x → f x ≡ g x)    ↔⟨ Very-stable-cong (Eq.extensionality-isomorphism ext) ⟩□
  Very-stable (f ≡ g)              □

-- Some closure properties for Σ.

Very-stable-Stable-Σ :
  Very-stable A →
  (∀ x → Stable-[ k ] (P x)) →
  Stable-[ k ] (Σ A P)
Very-stable-Stable-Σ {A = A} {P = P} s s′ =
  Erased (Σ A P)                              ↔⟨ Erased-Σ↔Σ ⟩
  Σ (Erased A) (λ x → Erased (P (erased x)))  ↝⟨ Σ-cong-contra Eq.⟨ _ , s ⟩ s′ ⟩□
  Σ A P                                       □

Very-stable-Stable-≡-Σ :
  {p q : Σ A P} →
  Very-stable (proj₁ p ≡ proj₁ q) →
  (∀ eq → Stable-[ k ] (subst P eq (proj₂ p) ≡ proj₂ q)) →
  Stable-[ k ] (p ≡ q)
Very-stable-Stable-≡-Σ {P = P} {k = k} {p = p} {q = q} = curry (
  Very-stable (proj₁ p ≡ proj₁ q) ×
  (∀ eq → Stable-[ k ] (subst P eq (proj₂ p) ≡ proj₂ q))  ↝⟨ uncurry Very-stable-Stable-Σ ⟩

  Stable-[ k ] (∃ λ (eq : proj₁ p ≡ proj₁ q) →
                    subst P eq (proj₂ p) ≡ proj₂ q)       ↝⟨ Stable-map-↔ Bijection.Σ-≡,≡↔≡ ⟩□

  Stable-[ k ] (p ≡ q)                                    □)

Stable-Σ :
  {@0 A : Set a} {@0 P : A → Set p}
  (s : Stable A) →
  (∀ x → Erased (P (erased x)) → P (s x)) →
  Stable (Σ A P)
Stable-Σ s₁ s₂ [ p ] =
  s₁ [ proj₁ p ] , s₂ [ proj₁ p ] [ proj₂ p ]

Stable-≡-Σ :
  {p q : Σ A P} →
  (s : Stable (proj₁ p ≡ proj₁ q)) →
  (∀ eq →
   Erased (subst P (erased eq) (proj₂ p) ≡ proj₂ q) →
   subst P (s eq) (proj₂ p) ≡ proj₂ q) →
  Stable (p ≡ q)
Stable-≡-Σ {P = P} {p = p} {q = q} = curry (
  (∃ λ (s : Stable (proj₁ p ≡ proj₁ q)) →
     ∀ eq → Erased (subst P (erased eq) (proj₂ p) ≡ proj₂ q) →
            subst P (s eq) (proj₂ p) ≡ proj₂ q)                 ↝⟨ uncurry Stable-Σ ⟩

  Stable (∃ λ (eq : proj₁ p ≡ proj₁ q) →
              subst P eq (proj₂ p) ≡ proj₂ q)                   ↝⟨ Stable-map-↔ Bijection.Σ-≡,≡↔≡ ⟩□

  Stable (p ≡ q)                                                □)

-- Very-stable is closed under Σ.

Very-stable-Σ :
  Very-stable A →
  (∀ x → Very-stable (P x)) →
  Very-stable (Σ A P)
Very-stable-Σ {A = A} {P = P} s s′ = _≃_.is-equivalence (
  Σ A P                                       ↝⟨ Σ-cong Eq.⟨ _ , s ⟩ (λ x → Eq.⟨ _ , s′ x ⟩) ⟩
  Σ (Erased A) (λ x → Erased (P (erased x)))  ↔⟨ inverse Erased-Σ↔Σ ⟩□
  Erased (Σ A P)                              □)

-- A variant for equality.

Very-stable-≡-Σ :
  {p q : Σ A P} →
  Very-stable (proj₁ p ≡ proj₁ q) →
  (∀ eq → Very-stable (subst P eq (proj₂ p) ≡ proj₂ q)) →
  Very-stable (p ≡ q)
Very-stable-≡-Σ {P = P} {p = p} {q = q} = curry (
  Very-stable (proj₁ p ≡ proj₁ q) ×
  (∀ eq → Very-stable (subst P eq (proj₂ p) ≡ proj₂ q))  ↝⟨ uncurry Very-stable-Σ ⟩

  Very-stable (∃ λ (eq : proj₁ p ≡ proj₁ q) →
                   subst P eq (proj₂ p) ≡ proj₂ q)       ↔⟨ Very-stable-cong $ Eq.↔⇒≃ Bijection.Σ-≡,≡↔≡ ⟩□

  Very-stable (p ≡ q)                                    □)

-- Stable-[ k ] is closed under _×_.

Stable-× : Stable-[ k ] A → Stable-[ k ] B → Stable-[ k ] (A × B)
Stable-× {A = A} {B = B} s s′ =
  Erased (A × B)       ↔⟨ Erased-Σ↔Σ ⟩
  Erased A × Erased B  ↝⟨ s ×-cong s′ ⟩□
  A × B                □

-- A variant for equality.

Stable-≡-× :
  {p q : A × B} →
  Stable-[ k ] (proj₁ p ≡ proj₁ q) →
  Stable-[ k ] (proj₂ p ≡ proj₂ q) →
  Stable-[ k ] (p ≡ q)
Stable-≡-× {k = k} {p = p} {q = q} = curry (
  Stable-[ k ] (proj₁ p ≡ proj₁ q) × Stable-[ k ] (proj₂ p ≡ proj₂ q)  ↝⟨ uncurry Stable-× ⟩
  Stable-[ k ] (proj₁ p ≡ proj₁ q × proj₂ p ≡ proj₂ q)                 ↝⟨ Stable-map-↔ ≡×≡↔≡ ⟩□
  Stable-[ k ] (p ≡ q)                                                 □)

-- Very-stable is closed under _×_.

Very-stable-× : Very-stable A → Very-stable B → Very-stable (A × B)
Very-stable-× s s′ = _≃_.is-equivalence $
  inverse $ Stable-× (inverse Eq.⟨ _ , s ⟩) (inverse Eq.⟨ _ , s′ ⟩)

-- A variant for equality.

Very-stable-≡-× :
  {p q : A × B} →
  Very-stable (proj₁ p ≡ proj₁ q) →
  Very-stable (proj₂ p ≡ proj₂ q) →
  Very-stable (p ≡ q)
Very-stable-≡-× {p = p} {q = q} = curry (
  Very-stable (proj₁ p ≡ proj₁ q) × Very-stable (proj₂ p ≡ proj₂ q)  ↝⟨ uncurry Very-stable-× ⟩
  Very-stable (proj₁ p ≡ proj₁ q × proj₂ p ≡ proj₂ q)                ↔⟨ Very-stable-cong $ Eq.↔⇒≃ ≡×≡↔≡ ⟩□
  Very-stable (p ≡ q)                                                □)

-- Very-stable is closed under W.

Very-stable-W : Very-stable A → Very-stable (W A P)
Very-stable-W {A = A} {P = P} s =
  _≃_.is-equivalence $
  Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = [_]
        ; from = from
        }
      ; right-inverse-of = []∘from
      }
    ; left-inverse-of = from∘[]
    })
  where
  module E = _≃_ Eq.⟨ _ , s ⟩

  from : Erased (W A P) → W A P
  from [ sup x f ] = sup
    (E.from [ x ])
    (λ y → from [ f (subst P (E.left-inverse-of x) y) ])

  from∘[] : ∀ x → from [ x ] ≡ x
  from∘[] (sup x f) = curry (_↠_.to (W-≡,≡↠≡ ext))
    (E.left-inverse-of x)
    (λ y → from∘[] (f (subst P (E.left-inverse-of x) y)))

  []∘from : ∀ x → [ from x ] ≡ x
  []∘from [ x ] = []-cong [ from∘[] x ]

-- A variant for equality.

Very-stable-≡-W :
  {x y : W A P} →
  Very-stable (headᵂ x ≡ headᵂ y) →
  (∀ eq → Very-stable (∀ i → tailᵂ x i ≡ tailᵂ y (subst P eq i))) →
  Very-stable (x ≡ y)
Very-stable-≡-W {P = P} {x = sup x f} {y = sup y g} = curry (
  Very-stable (x ≡ y) ×
  (∀ eq → Very-stable (∀ i → f i ≡ g (subst P eq i)))            ↝⟨ uncurry Very-stable-Σ ⟩

  Very-stable (∃ λ (eq : x ≡ y) → ∀ i → f i ≡ g (subst P eq i))  ↔⟨ Very-stable-cong $ Eq.W-≡,≡≃≡ ext ⟩□

  Very-stable (sup x f ≡ sup y g)                                □)

-- If equality is stable for A and B, then it is stable for A ⊎ B.

Stable-≡-⊎ :
  Stable-≡-[ k ] A →
  Stable-≡-[ k ] B →
  Stable-≡-[ k ] (A ⊎ B)
Stable-≡-⊎ s₁ s₂ {x = inj₁ x} {y = inj₁ y} =
  Erased (inj₁ x ≡ inj₁ y)  ↔⟨ Erased-cong $ inverse Bijection.≡↔inj₁≡inj₁ ⟩
  Erased (x ≡ y)            ↝⟨ s₁ ⟩
  x ≡ y                     ↔⟨ Bijection.≡↔inj₁≡inj₁ ⟩□
  inj₁ x ≡ inj₁ y           □

Stable-≡-⊎ s₁ s₂ {x = inj₁ x} {y = inj₂ y} =
  Erased (inj₁ x ≡ inj₂ y)  ↔⟨ Erased-cong Bijection.≡↔⊎ ⟩
  Erased ⊥                  ↝⟨ Very-stable→Stable Very-stable-⊥ ⟩
  ⊥                         ↔⟨ inverse Bijection.≡↔⊎ ⟩□
  inj₁ x ≡ inj₂ y           □

Stable-≡-⊎ s₁ s₂ {x = inj₂ x} {y = inj₁ y} =
  Erased (inj₂ x ≡ inj₁ y)  ↔⟨ Erased-cong Bijection.≡↔⊎ ⟩
  Erased ⊥                  ↝⟨ Very-stable→Stable Very-stable-⊥ ⟩
  ⊥                         ↔⟨ inverse Bijection.≡↔⊎ ⟩□
  inj₂ x ≡ inj₁ y           □

Stable-≡-⊎ s₁ s₂ {x = inj₂ x} {y = inj₂ y} =
  Erased (inj₂ x ≡ inj₂ y)  ↔⟨ Erased-cong $ inverse Bijection.≡↔inj₂≡inj₂ ⟩
  Erased (x ≡ y)            ↝⟨ s₂ ⟩
  x ≡ y                     ↔⟨ Bijection.≡↔inj₂≡inj₂ ⟩□
  inj₂ x ≡ inj₂ y           □

-- If equality is very stable for A and B, then it is very stable for
-- A ⊎ B.

Very-stable-≡-⊎ :
  Very-stable-≡ A →
  Very-stable-≡ B →
  Very-stable-≡ (A ⊎ B)
Very-stable-≡-⊎ s₁ s₂ =
  _≃_.is-equivalence $
  Eq.with-other-function
    (inverse $ Stable-≡-⊎ (inverse Eq.⟨ _ , s₁ ⟩)
                          (inverse Eq.⟨ _ , s₂ ⟩))
    [_]
    (lemma _ _)
  where
  lemma :
    ∀ x y (eq : x ≡ y) →
    _≃_.from (Stable-≡-⊎ (inverse Eq.⟨ _ , s₁ ⟩)
                         (inverse Eq.⟨ _ , s₂ ⟩)) eq ≡
    [ eq ]
  lemma (inj₁ _) (inj₁ _) eq =
    [ cong inj₁ (⊎.cancel-inj₁ eq) ]  ≡⟨ cong [_] $ _↔_.right-inverse-of Bijection.≡↔inj₁≡inj₁ eq ⟩∎
    [ eq ]                            ∎
  lemma (inj₁ _) (inj₂ _) eq = ⊥-elim (⊎.inj₁≢inj₂ eq)
  lemma (inj₂ _) (inj₁ _) eq = ⊥-elim (⊎.inj₁≢inj₂ (sym eq))
  lemma (inj₂ _) (inj₂ _) eq =
    [ cong inj₂ (⊎.cancel-inj₂ eq) ]  ≡⟨ cong [_] $ _↔_.right-inverse-of Bijection.≡↔inj₂≡inj₂ eq ⟩∎
    [ eq ]                            ∎

-- If equality is stable for A, then it is stable for List A.

Stable-≡-List :
  Stable-≡-[ k ] A →
  Stable-≡-[ k ] (List A)
Stable-≡-List {k = k} s {x = []} {y = []} =
  Erased ([] ≡ [])            ↔⟨ Erased-cong $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩
  Erased (inj₁ tt ≡ inj₁ tt)  ↔⟨ Erased-cong $ inverse Bijection.≡↔inj₁≡inj₁ ⟩
  Erased (tt ≡ tt)            ↝⟨ Very-stable→Stable $ Very-stable→Very-stable-≡ Very-stable-⊤ ⟩
  tt ≡ tt                     ↔⟨ Bijection.≡↔inj₁≡inj₁ ⟩
  inj₁ tt ≡ inj₁ tt           ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩□
  [] ≡ []                     □

Stable-≡-List s {x = []} {y = y ∷ ys} =
  Erased ([] ≡ y ∷ ys)              ↔⟨ Erased-cong $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩
  Erased (inj₁ tt ≡ inj₂ (y , ys))  ↔⟨ Erased-cong Bijection.≡↔⊎ ⟩
  Erased ⊥                          ↝⟨ Very-stable→Stable Very-stable-⊥ ⟩
  ⊥                                 ↔⟨ inverse Bijection.≡↔⊎ ⟩
  inj₁ tt ≡ inj₂ (y , ys)           ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩□
  [] ≡ y ∷ ys                       □

Stable-≡-List s {x = x ∷ xs} {y = []} =
  Erased (x ∷ xs ≡ [])              ↔⟨ Erased-cong $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩
  Erased (inj₂ (x , xs) ≡ inj₁ tt)  ↔⟨ Erased-cong Bijection.≡↔⊎ ⟩
  Erased ⊥                          ↝⟨ Very-stable→Stable Very-stable-⊥ ⟩
  ⊥                                 ↔⟨ inverse Bijection.≡↔⊎ ⟩
  inj₂ (x , xs) ≡ inj₁ tt           ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩□
  x ∷ xs ≡ []                       □

Stable-≡-List s {x = x ∷ xs} {y = y ∷ ys} =
  Erased (x ∷ xs ≡ y ∷ ys)                ↔⟨ Erased-cong $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩
  Erased (inj₂ (x , xs) ≡ inj₂ (y , ys))  ↔⟨ Erased-cong $ inverse Bijection.≡↔inj₂≡inj₂ ⟩
  Erased ((x , xs) ≡ (y , ys))            ↝⟨ Stable-≡-× s (Stable-≡-List s) ⟩
  (x , xs) ≡ (y , ys)                     ↔⟨ Bijection.≡↔inj₂≡inj₂ ⟩
  inj₂ (x , xs) ≡ inj₂ (y , ys)           ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ L.List↔Maybe[×List] ⟩□
  x ∷ xs ≡ y ∷ ys                         □

-- If equality is very stable for A, then it is very stable for
-- List A.

Very-stable-≡-List :
  Very-stable-≡ A →
  Very-stable-≡ (List A)
Very-stable-≡-List {A = A} s =
  _≃_.is-equivalence $
  Eq.with-other-function
    (inverse s′)
    [_]
    (lemma _ _)
  where
  s′ : Stable-≡-[ equivalence ] (List A)
  s′ = Stable-≡-List (inverse Eq.⟨ _ , s ⟩)

  lemma :
    ∀ xs ys (eq : xs ≡ ys) →
    _≃_.from s′ eq ≡ [ eq ]
  lemma [] [] _ = cong [_] (prop _ _)
    where
    prop : Is-proposition ([] ≡ [])
    prop =                                $⟨ mono (Nat.zero≤ 2) ⊤-contractible ⟩
      Is-proposition (tt ≡ tt)            ↝⟨ H-level-cong _ 1 Bijection.≡↔inj₁≡inj₁ ⟩
      Is-proposition (inj₁ tt ≡ inj₁ tt)  ↝⟨ H-level-cong _ 1 (Eq.≃-≡ (Eq.↔⇒≃ L.List↔Maybe[×List])) ⦂ (_ → _) ⟩□
      Is-proposition ([] ≡ [])            □

  lemma [] (_ ∷ _) = ⊥-elim ∘ List.[]≢∷

  lemma (_ ∷ _) [] = ⊥-elim ∘ List.[]≢∷ ∘ sym

  lemma (_ ∷ xs) (_ ∷ ys) eq = []-cong [
    _≃_.to iso₁ (_↔_.to iso₂ (_↔_.to iso₃
      (Σ-map id (erased ∘ _≃_.from s′)
         (_↔_.from iso₃ (_↔_.from iso₂ (_≃_.from iso₁ eq))))))    ≡⟨ cong (λ f → _≃_.to iso₁ (_↔_.to iso₂ (_↔_.to iso₃
                                                                                 (Σ-map id (erased ∘ f)
                                                                                    (_↔_.from iso₃ (_↔_.from iso₂ (_≃_.from iso₁ eq))))))) $
                                                                     ⟨ext⟩ (lemma xs ys) ⟩
    _≃_.to iso₁ (_↔_.to iso₂ (_↔_.to iso₃
      (_↔_.from iso₃ (_↔_.from iso₂ (_≃_.from iso₁ eq)))))
                                                                  ≡⟨ cong (λ eq → _≃_.to iso₁ (_↔_.to iso₂ eq)) $
                                                                     _↔_.right-inverse-of iso₃ _ ⟩

    _≃_.to iso₁ (_↔_.to iso₂ (_↔_.from iso₂ (_≃_.from iso₁ eq)))  ≡⟨ cong (_≃_.to iso₁) $ _↔_.right-inverse-of iso₂ _ ⟩

    _≃_.to iso₁ (_≃_.from iso₁ eq)                                ≡⟨ _≃_.right-inverse-of iso₁ _ ⟩∎

    eq                                                            ∎ ]
    where
    iso₁ = Eq.≃-≡ (Eq.↔⇒≃ L.List↔Maybe[×List])
    iso₂ = Bijection.≡↔inj₂≡inj₂
    iso₃ = ≡×≡↔≡

-- Stable-[ k ] is closed under ↑ ℓ.

Stable-↑ : Stable-[ k ] A → Stable-[ k ] (↑ ℓ A)
Stable-↑ {A = A} s =
  Erased (↑ _ A)  ↔⟨ Erased-↑↔↑ ⟩
  ↑ _ (Erased A)  ↝⟨ ↑-cong s ⟩□
  ↑ _ A           □

-- A variant for equality.

Stable-≡-↑ :
  Stable-[ k ] (lower {ℓ = ℓ} x ≡ lower y) →
  Stable-[ k ] (x ≡ y)
Stable-≡-↑ {k = k} {x = x} {y = y} =
  Stable-[ k ] (lower x ≡ lower y)  ↝⟨ Stable-map-↔ (_≃_.bijection $ Eq.≃-≡ $ Eq.↔⇒≃ $ Bijection.↑↔) ⟩□
  Stable-[ k ] (x ≡ y)              □

-- Very-stable is closed under ↑ ℓ.

Very-stable-↑ : Very-stable A → Very-stable (↑ ℓ A)
Very-stable-↑ s = _≃_.is-equivalence $
  inverse $ Stable-↑ $ inverse Eq.⟨ _ , s ⟩

-- A variant for equality.

Very-stable-≡-↑ :
  Very-stable (lower {ℓ = ℓ} x ≡ lower y) →
  Very-stable (x ≡ y)
Very-stable-≡-↑ {x = x} {y = y} =
  Very-stable (lower x ≡ lower y)  ↔⟨ Very-stable-cong (Eq.≃-≡ $ Eq.↔⇒≃ $ Bijection.↑↔) ⟩□
  Very-stable (x ≡ y)              □

-- If A is very stable, then H-level′ n A is very stable.

Very-stable-H-level′ :
  Very-stable A → Very-stable (H-level′ n A)
Very-stable-H-level′ {n = zero} s =
  Very-stable-Σ s λ _ →
  Very-stable-Π λ _ →
  Very-stable→Very-stable-≡ s
Very-stable-H-level′ {n = suc n} s =
  Very-stable-Π λ _ →
  Very-stable-Π λ _ →
  Very-stable-H-level′ (Very-stable→Very-stable-≡ s)

-- If A is very stable, then H-level n A is very stable.

Very-stable-H-level :
  Very-stable A → Very-stable (H-level n A)
Very-stable-H-level {A = A} {n = n} =
  Very-stable A               ↝⟨ Very-stable-H-level′ ⟩
  Very-stable (H-level′ n A)  ↔⟨ inverse $ Very-stable-cong (H-level↔H-level′ ext) ⟩□
  Very-stable (H-level n A)   □

------------------------------------------------------------------------
-- [_] is sometimes an embedding

-- If A is a proposition, then [_] {A = A} is an embedding.

Is-proposition→Is-embedding-[] :
  Is-proposition A → Is-embedding ([_] {A = A})
Is-proposition→Is-embedding-[] prop =
  _≃_.to (Emb.Injective≃Is-embedding ext set (H-level-Erased 2 set) [_])
    (λ _ → prop _ _)
  where
  set = mono₁ 1 prop

-- If A is very stable, then [_] {A = A} is an embedding.

Very-stable→Is-embedding-[] :
  Very-stable A → Is-embedding ([_] {A = A})
Very-stable→Is-embedding-[] {A = A} =
  Very-stable A                      ↔⟨ inverse Trunc.surjective×embedding≃equivalence ⟩
  Surjective [_] × Is-embedding [_]  ↝⟨ proj₂ ⟩□
  Is-embedding [_]                   □

-- In an erased context [_] is always an embedding.

Erased-Is-embedding-[] :
  {@0 A : Set a} → Erased (Is-embedding ([_] {A = A}))
Erased-Is-embedding-[] =
  [ Very-stable→Is-embedding-[] (erased Erased-Very-stable) ]

------------------------------------------------------------------------
-- [_] is sometimes surjective

-- If A is very stable, then [_] {A = A} is surjective.

Very-stable→Surjective-[] :
  Very-stable A → Surjective ([_] {A = A})
Very-stable→Surjective-[] {A = A} =
  Very-stable A                      ↔⟨ inverse Trunc.surjective×embedding≃equivalence ⟩
  Surjective [_] × Is-embedding [_]  ↝⟨ proj₁ ⟩□
  Surjective [_]                     □

-- In an erased context [_] is always surjective.

Erased-Surjective-[] :
  {@0 A : Set a} → Erased (Surjective ([_] {A = A}))
Erased-Surjective-[] =
  [ Very-stable→Surjective-[] (erased Erased-Very-stable) ]

------------------------------------------------------------------------
-- Erased singletons

-- A variant of the Singleton type family with erased equality proofs.

Erased-singleton : {A : Set a} → @0 A → Set a
Erased-singleton x = ∃ λ y → Erased (y ≡ x)

-- The type of triples consisting of two values of type A, one erased,
-- and an erased proof of equality of the two values is isomorphic to
-- A.

Σ-Erased-Erased-singleton↔ :
  (∃ λ (x : Erased A) → Erased-singleton (erased x)) ↔ A
Σ-Erased-Erased-singleton↔ {A = A} =
  (∃ λ (x : Erased A) → ∃ λ y → Erased (y ≡ erased x))  ↝⟨ ∃-comm ⟩
  (∃ λ y → ∃ λ (x : Erased A) → Erased (y ≡ erased x))  ↝⟨ (∃-cong λ _ → inverse Erased-Σ↔Σ) ⟩
  (∃ λ y → Erased (∃ λ (x : A) → y ≡ x))                ↝⟨ (∃-cong λ _ → Erased-cong (_⇔_.to contractible⇔↔⊤ (other-singleton-contractible _))) ⟩
  A × Erased ⊤                                          ↝⟨ drop-⊤-right (λ _ → Erased-⊤↔⊤) ⟩□
  A                                                     □

-- If equality is very stable for A, then Erased-singleton x is
-- contractible for x : A.

erased-singleton-contractible :
  {x : A} →
  Very-stable-≡ A →
  Contractible (Erased-singleton x)
erased-singleton-contractible {x = x} s =
                                     $⟨ singleton-contractible x ⟩
  Contractible (Singleton x)         ↝⟨ H-level-cong _ 0 (∃-cong λ _ → Eq.⟨ _ , s ⟩) ⦂ (_ → _) ⟩□
  Contractible (Erased-singleton x)  □

-- If equality is very stable for A, and x : A is erased, then
-- Erased-singleton x is a proposition.

erased-singleton-with-erased-center-propositional :
  {@0 x : A} →
  Very-stable-≡ A →
  Is-proposition (Erased-singleton x)
erased-singleton-with-erased-center-propositional {x = x} s =
                                                 $⟨ [ erased-singleton-contractible s ] ⟩
  Erased (Contractible (Erased-singleton x))     ↝⟨ Erased-cong (mono₁ 0) ⟩
  Erased (Is-proposition (Erased-singleton x))   ↝⟨ (λ hyp p q → (_$ q) ∘ (_$ p) ⟨$⟩ hyp) ⟩
  ((p q : Erased-singleton x) → Erased (p ≡ q))  ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → Very-stable→Stable $
                                                     Very-stable-≡-Σ s λ _ → Very-stable→Very-stable-≡ Very-stable-Erased) ⟩□
  Is-proposition (Erased-singleton x)            □

-- If A is very stable, and x : A is erased, then Erased-singleton x
-- is contractible.

erased-singleton-with-erased-center-contractible :
  {@0 x : A} →
  Very-stable A →
  Contractible (Erased-singleton x)
erased-singleton-with-erased-center-contractible {x = x} s =
                                     $⟨ [ x , [ refl _ ] ] ⟩
  Erased (Erased-singleton x)        ↝⟨ Very-stable→Stable (Very-stable-Σ s λ _ → Very-stable-Erased) ⟩
  Erased-singleton x                 ↝⟨ propositional⇒inhabited⇒contractible $
                                        erased-singleton-with-erased-center-propositional $
                                        Very-stable→Very-stable-≡ s ⟩□
  Contractible (Erased-singleton x)  □

-- A corollary of erased-singleton-with-erased-center-propositional.

↠→↔Erased-singleton :
  {@0 y : B}
  (A↠B : A ↠ B) →
  Very-stable-≡ B →
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ ↔ Erased-singleton y
↠→↔Erased-singleton {A = A} {y = y} A↠B s =
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥  ↝⟨ Trunc.∥∥-cong-⇔ (Eq.∃-preserves-logical-equivalences A↠B λ _ → F.id) ⟩
  ∥ Erased-singleton y ∥                         ↝⟨ Trunc.∥∥↔ (erased-singleton-with-erased-center-propositional s) ⟩□
  Erased-singleton y                             □

-- The right-to-left direction of the previous lemma does not depend
-- on the assumption of stability.

↠→Erased-singleton→ :
  {@0 y : B}
  (A↠B : A ↠ B) →
  Erased-singleton y →
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥
↠→Erased-singleton→ {A = A} {y = y} A↠B =
  Erased-singleton y                             ↝⟨ Trunc.∣_∣ ⟩
  ∥ Erased-singleton y ∥                         ↝⟨ _≃_.from $ Trunc.∥∥-cong-⇔ (Eq.∃-preserves-logical-equivalences A↠B λ _ → F.id) ⟩□
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥  □

private

  -- The function that is obtained from ↠→↔Erased-singleton is
  -- definitionally equal to the corresponding application of
  -- ↠→Erased-singleton→.

  from-↠→↔Erased-singleton≡↠→Erased-singleton→ :
    {s : Very-stable-≡ B} →
    _↔_.from (↠→↔Erased-singleton A↠B s) x ≡ ↠→Erased-singleton→ A↠B x
  from-↠→↔Erased-singleton≡↠→Erased-singleton→ = refl _

-- A corollary of Σ-Erased-Erased-singleton↔ and ↠→↔Erased-singleton.

Σ-Erased-∥-Σ-Erased-≡-∥↔ :
  (A↠B : A ↠ B) →
  Very-stable-≡ B →
  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥) ↔
  B
Σ-Erased-∥-Σ-Erased-≡-∥↔ {A = A} {B = B} A↠B s =
  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥)  ↝⟨ (∃-cong λ _ → ↠→↔Erased-singleton A↠B s) ⟩

  (∃ λ (x : Erased B) → Erased-singleton (erased x))        ↝⟨ Σ-Erased-Erased-singleton↔ ⟩□

  B                                                         □

-- Again the right-to-left direction of the previous lemma does not
-- depend on the assumption of stability.

→Σ-Erased-∥-Σ-Erased-≡-∥ :
  (A↠B : A ↠ B) →
  B →
  ∃ λ (x : Erased B) →
    ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥
→Σ-Erased-∥-Σ-Erased-≡-∥ {A = A} {B = B} A↠B =
  B                                                         ↔⟨ inverse Σ-Erased-Erased-singleton↔ ⟩

  (∃ λ (x : Erased B) → Erased-singleton (erased x))        ↝⟨ (∃-cong λ _ → ↠→Erased-singleton→ A↠B) ⟩□

  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥)  □

private

  -- The function that is obtained from Σ-Erased-∥-Σ-Erased-≡-∥↔ is
  -- definitionally equal to the corresponding application of
  -- →Σ-Erased-∥-Σ-Erased-≡-∥.

  from-Σ-Erased-∥-Σ-Erased-≡-∥↔≡→Σ-Erased-∥-Σ-Erased-≡-∥ :
    {s : Very-stable-≡ B} →
    _↔_.from (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) x ≡
    →Σ-Erased-∥-Σ-Erased-≡-∥ A↠B x
  from-Σ-Erased-∥-Σ-Erased-≡-∥↔≡→Σ-Erased-∥-Σ-Erased-≡-∥ = refl _

-- In an erased context the left-to-right direction of
-- Σ-Erased-∥-Σ-Erased-≡-∥↔ returns the erased first component.

@0 to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡ :
  ∀ (A↠B : A ↠ B) (s : Very-stable-≡ B) x →
  _↔_.to (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) x ≡ erased (proj₁ x)
to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡ A↠B s (x , y) =
  _↔_.to (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) (x , y)  ≡⟨⟩
  proj₁ (_↔_.to (↠→↔Erased-singleton A↠B s) y)     ≡⟨ erased (proj₂ (_↔_.to (↠→↔Erased-singleton A↠B s) y)) ⟩∎
  erased x                                         ∎

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
