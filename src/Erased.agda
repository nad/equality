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
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
import Equivalence P.equality-with-J as PEq
open import Function-universe eq hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
  using (Surjective; ∣_∣)
open import Injection eq using (_↣_)
open import Monad eq
open import Surjection eq using (_↠_)

private
  variable
    a b ℓ p : Level
    A B     : Set a
    P       : A → Set p
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

_>>=′_ : Erased A → (A → Erased B) → Erased B
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

Erased↔ : Erased (Erased A ↔ A)
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

Erased-Π↔Π : Erased ((x : A) → P x) ↔ ((x : A) → Erased (P x))
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

Erased-Σ↔Σ : Erased (Σ A P) ↔ Σ (Erased A) (λ x → Erased (P (erased x)))
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

Erased-W↔W : Erased (W A P) ↔ W (Erased A) (λ x → Erased (P (erased x)))
Erased-W↔W = record
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

Erased-↑↔↑ : Erased (↑ ℓ A) ↔ ↑ ℓ (Erased A)
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

-- Very stable types are stable.

Very-stable→Stable : Very-stable A → Stable-[ k ] A
Very-stable→Stable {A = A} {k = k} =
  Very-stable A             ↝⟨ Eq.⟨ _ ,_⟩ ⟩
  A ≃ Erased A              ↝⟨ inverse ⟩
  Erased A ≃ A              ↔⟨⟩
  Stable-[ equivalence ] A  ↝⟨ from-equivalence ⟩□
  Stable-[ k ] A            □

-- Erased A is very stable.

Very-stable-Erased : Very-stable (Erased A)
Very-stable-Erased {A = A} =
  _≃_.is-equivalence (            $⟨ Erased↔ ⟩
    Erased (Erased A ↔ A)         ↝⟨ (λ hyp → Erased-cong (erased hyp)) ⟩
    Erased (Erased A) ↔ Erased A  ↝⟨ Eq.↔⇒≃ ∘ inverse ⟩□
    Erased A ≃ Erased (Erased A)  □)

-- In an erased context every type is very stable.

Erased-Very-stable : Erased (Very-stable A)
Erased-Very-stable {A = A} =
  [ _≃_.is-equivalence (    $⟨ Erased↔ ⟩
      Erased (Erased A ↔ A) ↝⟨ erased ⟩
      Erased A ↔ A          ↝⟨ Eq.↔⇒≃ ∘ inverse ⟩□
      A ≃ Erased A          □)
  ]

-- Erased A implies ¬ ¬ A.

Erased→¬¬ : Erased A → ¬ ¬ A
Erased→¬¬ {A = A} = curry (
  Erased A × ¬ A  ↝⟨ (λ { (x , f) → x >>=′ return ∘ f }) ⟩
  Erased ⊥        ↔⟨ Erased-⊥↔⊥ ⟩□
  ⊥               □)

-- Types for which it is known whether or not they are inhabited are
-- stable.

Dec→Stable : Dec A → Stable A
Dec→Stable {A = A} = curry (
  Dec A × Erased A  ↝⟨ Σ-map id Erased→¬¬ ⟩
  Dec A × ¬ ¬ A     ↝⟨ uncurry (⊎-map id) ∘ swap ⟩
  A ⊎ ⊥             ↝⟨ Prelude.[ id , ⊥-elim ] ⟩□
  A                 □)

-- Types that are stable for double negation are stable for Erased.

¬¬-Stable→Stable : (¬ ¬ A → A) → Stable A
¬¬-Stable→Stable {A = A} ¬¬-Stable =
  Erased A  ↝⟨ Erased→¬¬ ⟩
  ¬ ¬ A     ↝⟨ ¬¬-Stable ⟩□
  A         □

-- If A is stable, then A is "logical equivalence stable".

Stable→Stable⇔ : Stable A → Stable-[ logical-equivalence ] A
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

------------------------------------------------------------------------
-- Preservation lemmas related to Stable, Stable-[_] and Very-stable

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

-- Very-stable is closed under Π A.

Very-stable-Π : (∀ x → Very-stable (P x)) → Very-stable ((x : A) → P x)
Very-stable-Π s = _≃_.is-equivalence $
  inverse $ Stable-Π $ λ x → inverse Eq.⟨ _ , s x ⟩

-- Some closure properties for Σ.

Very-stable-Stable-Σ :
  Very-stable A →
  (∀ x → Stable-[ k ] (P x)) →
  Stable-[ k ] (Σ A P)
Very-stable-Stable-Σ {A = A} {P = P} s s′ =
  Erased (Σ A P)                              ↔⟨ Erased-Σ↔Σ ⟩
  Σ (Erased A) (λ x → Erased (P (erased x)))  ↝⟨ Σ-cong-contra Eq.⟨ _ , s ⟩ s′ ⟩□
  Σ A P                                       □

Stable-Σ :
  (s : Stable A) →
  (∀ x → Erased (P (erased x)) → P (s x)) →
  Stable (Σ A P)
Stable-Σ {A = A} {P = P} s s′ =
  Erased (Σ A P)                              ↔⟨ Erased-Σ↔Σ ⟩
  Σ (Erased A) (λ x → Erased (P (erased x)))  ↝⟨ Σ-map s (s′ _) ⟩□
  Σ A P                                       □

-- Very-stable is closed under Σ.

Very-stable-Σ :
  Very-stable A →
  (∀ x → Very-stable (P x)) →
  Very-stable (Σ A P)
Very-stable-Σ {A = A} {P = P} s s′ = _≃_.is-equivalence (
  Σ A P                                       ↝⟨ Σ-cong Eq.⟨ _ , s ⟩ (λ x → Eq.⟨ _ , s′ x ⟩) ⟩
  Σ (Erased A) (λ x → Erased (P (erased x)))  ↔⟨ inverse Erased-Σ↔Σ ⟩□
  Erased (Σ A P)                              □)

-- Stable-[ k ] is closed under _×_.

Stable-× : Stable-[ k ] A → Stable-[ k ] B → Stable-[ k ] (A × B)
Stable-× {A = A} {B = B} s s′ =
  Erased (A × B)       ↔⟨ Erased-Σ↔Σ ⟩
  Erased A × Erased B  ↝⟨ s ×-cong s′ ⟩□
  A × B                □

-- Very-stable is closed under _×_.

Very-stable-× : Very-stable A → Very-stable B → Very-stable (A × B)
Very-stable-× s s′ = _≃_.is-equivalence $
  inverse $ Stable-× (inverse Eq.⟨ _ , s ⟩) (inverse Eq.⟨ _ , s′ ⟩)

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

-- Stable-[ k ] is closed under ↑ ℓ.

Stable-↑ : Stable-[ k ] A → Stable-[ k ] (↑ ℓ A)
Stable-↑ {A = A} s =
  Erased (↑ _ A)  ↔⟨ Erased-↑↔↑ ⟩
  ↑ _ (Erased A)  ↝⟨ ↑-cong s ⟩□
  ↑ _ A           □

-- Very-stable is closed under ↑ ℓ.

Very-stable-↑ : Very-stable A → Very-stable (↑ ℓ A)
Very-stable-↑ s = _≃_.is-equivalence $
  inverse $ Stable-↑ $ inverse Eq.⟨ _ , s ⟩

private

  -- If A is very stable, then the types of paths between values of
  -- type A are very stable.

  Very-stable-≡′ : {x y : A} → Very-stable A → Very-stable (x P.≡ y)
  Very-stable-≡′ {x = x} {y = y} s = _≃_.is-equivalence (
    x P.≡ y           ↝⟨ inverse $ _↔_.from ≃↔≃ $ PEq.≃-≡ $ _↔_.to ≃↔≃ $ Eq.⟨ _ , s ⟩ ⟩
    [ x ] P.≡ [ y ]   ↔⟨ inverse Erased-≡↔[]≡[]′ ⟩□
    Erased (x P.≡ y)  □)

-- If A is very stable, then the types of equalities between values of
-- type A are very stable.

Very-stable-≡ : {x y : A} → Very-stable A → Very-stable (x ≡ y)
Very-stable-≡ {x = x} {y = y} s =
  _≃_.is-equivalence $
  Eq.with-other-function
    (x ≡ y             ↔⟨ ≡↔≡ ⟩
     x P.≡ y           ↝⟨ inverse $ Very-stable→Stable (Very-stable-≡′ s) ⟩
     Erased (x P.≡ y)  ↔⟨ Erased-cong (inverse ≡↔≡) ⟩□
     Erased (x ≡ y)    □)
    [_]
    (λ eq →
      [ _↔_.from ≡↔≡ (_↔_.to ≡↔≡ eq) ]  ≡⟨ cong [_] (_↔_.left-inverse-of ≡↔≡ eq) ⟩∎
      [ eq ]                            ∎)

private

  -- Some examples showing how Very-stable-≡ can be used.

  -- Equalities between erased values are very stable.

  Very-stable-≡₀ : {x y : Erased A} → Very-stable (x ≡ y)
  Very-stable-≡₀ = Very-stable-≡ Very-stable-Erased

  -- Equalities between equalities between erased values are very
  -- stable.

  Very-stable-≡₁ :
    {x y : Erased A} {p q : x ≡ y} →
    Very-stable (p ≡ q)
  Very-stable-≡₁ = Very-stable-≡ Very-stable-≡₀

  -- And so on…

-- If A is very stable, then H-level′ n A is very stable.

Very-stable-H-level′ :
  Very-stable A → Very-stable (H-level′ n A)
Very-stable-H-level′ {n = zero} s =
  Very-stable-Σ s λ _ →
  Very-stable-Π λ _ →
  Very-stable-≡ s
Very-stable-H-level′ {n = suc n} s =
  Very-stable-Π λ _ →
  Very-stable-Π λ _ →
  Very-stable-H-level′ (Very-stable-≡ s)

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

Erased-Is-embedding-[] : Erased (Is-embedding ([_] {A = A}))
Erased-Is-embedding-[] {A = A} =
                             $⟨ Erased-Very-stable ⟩
  Erased (Very-stable A)     ↝⟨ Very-stable→Is-embedding-[] ⟨$⟩_ ⦂ (_ → _) ⟩□
  Erased (Is-embedding [_])  □

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

Erased-Surjective-[] : Erased (Surjective ([_] {A = A}))
Erased-Surjective-[] {A = A} =
                           $⟨ Erased-Very-stable ⟩
  Erased (Very-stable A)   ↝⟨ Very-stable→Surjective-[] ⟨$⟩_ ⦂ (_ → _) ⟩□
  Erased (Surjective [_])  □
