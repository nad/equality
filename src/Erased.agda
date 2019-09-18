------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Erased
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude hiding ([_,_])

open import Bijection eq using (_↔_)
open import Embedding eq as Emb using (Embedding; Is-embedding)
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (_↣_)
open import Monad eq
open import Surjection eq using (_↠_; Split-surjective)

private
  variable
    a b ℓ p : Level
    A B     : Set a
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
x >>=′ f = [ erased (f (erased x)) ]

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
      ; from = [_]
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
-- Erased preserves some kinds of functions

-- Erased preserves functions.

Erased-cong-→ :
  {@0 A : Set a} {@0 B : Set b} →
  @0 (A → B) → Erased A → Erased B
Erased-cong-→ A→B [ x ] = [ A→B x ]

-- Erased preserves logical equivalences.

Erased-cong-⇔ :
  {@0 A : Set a} {@0 B : Set b} →
  @0 A ⇔ B → Erased A ⇔ Erased B
Erased-cong-⇔ A⇔B = record
  { to   = Erased-cong-→ (_⇔_.to   A⇔B)
  ; from = Erased-cong-→ (_⇔_.from A⇔B)
  }

------------------------------------------------------------------------
-- Some results that follow if "[]-cong" can be defined

module []-cong
  ([]-cong : ∀ {a} {@0 A : Set a} {@0 x y : A} →
             Erased (x ≡ y) → [ x ] ≡ [ y ])
  where

  -- Erased commutes with W (assuming extensionality).

  Erased-W↔W :
    {@0 A : Set a} {@0 P : A → Set p} →
    Extensionality p (a ⊔ p) →
    Erased (W A P) ↔ W (Erased A) (λ x → Erased (P (erased x)))
  Erased-W↔W {A = A} {P = P} ext = record
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
      cong (sup [ x ]) (apply-ext ext λ { [ y ] →
        to∘from (f [ y ]) })

    from∘to : (x : Erased (W A P)) → from (to x) ≡ x
    from∘to [ sup x f ] =
      []-cong [ cong (sup x) (apply-ext ext λ y →
        cong erased (from∘to [ f y ])) ]

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

  -- Erased preserves some kinds of functions.

  module _ {@0 A : Set a} {@0 B : Set b} where

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

------------------------------------------------------------------------
-- Some results that follow if "Erased-≡↔[]≡[]" can be defined

module Erased-≡↔[]≡[]₁
  (Erased-≡↔[]≡[] :
    ∀ {a} {@0 A : Set a} {@0 x y : A} →
    Erased (x ≡ y) ↔ [ x ] ≡ [ y ])
  where

  -- Given an erased proof of equality of x and y one can show that
  -- [ x ] is equal to [ y ].

  []-cong :
    {@0 A : Set a} {@0 x y : A} →
    Erased (x ≡ y) → [ x ] ≡ [ y ]
  []-cong = _↔_.to Erased-≡↔[]≡[]

  private
    module []-cong′ = []-cong []-cong
  open []-cong′ public

  -- Erased preserves injections.

  Erased-cong-↣ :
    {@0 A : Set a} {@0 B : Set b} →
    @0 A ↣ B → Erased A ↣ Erased B
  Erased-cong-↣ A↣B = record
    { to        = Erased-cong-→ (_↣_.to A↣B)
    ; injective = λ { {x = [ x ]} {y = [ y ]} →
        [ _↣_.to A↣B x ] ≡ [ _↣_.to A↣B y ]   ↔⟨ inverse Erased-≡↔[]≡[] ⟩
        Erased (_↣_.to A↣B x ≡ _↣_.to A↣B y)  ↝⟨ Erased-cong-→ (_↣_.injective A↣B) ⟩
        Erased (x ≡ y)                        ↔⟨ Erased-≡↔[]≡[] ⟩□
        [ x ] ≡ [ y ]                         □ }
    }

  ----------------------------------------------------------------------
  -- All h-levels are closed under Erased

  private

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
      Erased (H-level n A)   ↝⟨ _⇔_.to $ Erased-cong-⇔ H-level⇔H-level′ ⟩
      Erased (H-level′ n A)  ↝⟨ Erased-H-level′ ⟩
      H-level′ n (Erased A)  ↝⟨ _⇔_.from H-level⇔H-level′ ⟩□
      H-level n (Erased A)   □

  -- H-level n is closed under Erased.

  H-level-Erased :
    {@0 A : Set a} →
    ∀ n → @0 H-level n A → H-level n (Erased A)
  H-level-Erased _ h = Erased-H-level [ h ]

  -- Erased commutes with H-level′ n (assuming extensionality).

  Erased-H-level′↔H-level′ :
    {@0 A : Set a} →
    Extensionality? k a a →
    Erased (H-level′ n A) ↝[ k ] H-level′ n (Erased A)
  Erased-H-level′↔H-level′ {n = n} {A = A} =
    generalise-ext?-prop
      (record
         { to   = Erased-H-level′
         ; from = λ h →
            [                        $⟨ h ⟩
              H-level′ n (Erased A)  ↝⟨ _⇔_.from H-level⇔H-level′ ⟩
              H-level n (Erased A)   ↝⟨ H-level-cong _ n (erased Erased↔) ⟩
              H-level n A            ↝⟨ _⇔_.to H-level⇔H-level′ ⟩□
              H-level′ n A           □
            ]
         })
      (λ ext → H-level-Erased 1 (H-level′-propositional ext n))
      (λ ext → H-level′-propositional ext n)

  -- Erased commutes with H-level n (assuming extensionality).

  Erased-H-level↔H-level :
    {@0 A : Set a} →
    Extensionality? k a a →
    Erased (H-level n A) ↝[ k ] H-level n (Erased A)
  Erased-H-level↔H-level {n = n} {A = A} ext =
    Erased (H-level n A)   ↝⟨ generalise-ext?
                                (Erased-cong-⇔ (H-level↔H-level′ _))
                                (λ ext → Erased-cong-↔ (H-level↔H-level′ ext))
                                ext ⟩
    Erased (H-level′ n A)  ↝⟨ Erased-H-level′↔H-level′ ext ⟩
    H-level′ n (Erased A)  ↝⟨ inverse-ext? H-level↔H-level′ ext ⟩□
    H-level n (Erased A)   □

  ----------------------------------------------------------------------
  -- A lemma

  -- If A is a proposition, then [_] {A = A} is an embedding (assuming
  -- extensionality).
  --
  -- See also Erased-Is-embedding-[] and Erased-Split-surjective-[]
  -- below as well as Very-stable→Is-embedding-[] and
  -- Very-stable→Split-surjective-[] in Erased.Stability and
  -- Injective-[] and Is-embedding-[] in Erased.With-K.

  Is-proposition→Is-embedding-[] :
    {A : Set a} →
    Extensionality a a →
    Is-proposition A → Is-embedding ([_] {A = A})
  Is-proposition→Is-embedding-[] ext prop =
    _≃_.to (Emb.Injective≃Is-embedding
              ext set (H-level-Erased 2 set) [_])
      (λ _ → prop _ _)
    where
    set = mono₁ 1 prop

------------------------------------------------------------------------
-- More lemmas

-- In an erased context [_] is always an embedding.

Erased-Is-embedding-[] :
  {@0 A : Set a} → Erased (Is-embedding ([_] {A = A}))
Erased-Is-embedding-[] =
  [ (λ x y → _≃_.is-equivalence (
       x ≡ y          ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ $ inverse $ erased Erased↔ ⟩□
       [ x ] ≡ [ y ]  □))
  ]

-- In an erased context [_] is always split surjective.

Erased-Split-surjective-[] :
  {@0 A : Set a} → Erased (Split-surjective ([_] {A = A}))
Erased-Split-surjective-[] = [ (λ { [ x ] → x , refl _ }) ]

------------------------------------------------------------------------
-- Some results that follow if "Erased-≡↔[]≡[]" can be defined in a
-- certain way

module Erased-≡↔[]≡[]₂
  (Erased-≡↔[]≡[] :
    ∀ {a} {@0 A : Set a} {@0 x y : A} →
    Erased (x ≡ y) ↔ [ x ] ≡ [ y ])
  (to-Erased-≡↔[]≡[]-[refl] :
    ∀ {a} {A : Set a} {x : A} →
    _↔_.to Erased-≡↔[]≡[] [ refl x ] ≡ refl [ x ])
  where

  open Erased-≡↔[]≡[]₁ Erased-≡↔[]≡[] public

  ----------------------------------------------------------------------
  -- Some definitions directly related to Erased-≡↔[]≡[]

  -- Rearrangement lemmas for Erased-≡↔[]≡[].

  to-Erased-≡↔[]≡[] :
    ∀ {a} {A : Set a} {x y : A} {x≡y : x ≡ y} →
    _↔_.to Erased-≡↔[]≡[] [ x≡y ] ≡ cong [_] x≡y
  to-Erased-≡↔[]≡[] {x = x} {x≡y = x≡y} = elim¹
    (λ x≡y → _↔_.to Erased-≡↔[]≡[] [ x≡y ] ≡ cong [_] x≡y)
    (_↔_.to Erased-≡↔[]≡[] [ refl x ]  ≡⟨ to-Erased-≡↔[]≡[]-[refl] ⟩
     refl [ x ]                        ≡⟨ sym $ cong-refl _ ⟩∎
     cong [_] (refl x)                 ∎)
    x≡y

  from-Erased-≡↔[]≡[] :
    {@0 A : Set a} {@0 x y : A} {@0 x≡y : [ x ] ≡ [ y ]} →
    _↔_.from Erased-≡↔[]≡[] x≡y ≡ [ cong erased x≡y ]
  from-Erased-≡↔[]≡[] {x≡y = x≡y} = []-cong
    [ erased (_↔_.from Erased-≡↔[]≡[] x≡y)  ≡⟨ cong erased (_↔_.from (from≡↔≡to $ Eq.↔⇒≃ Erased-≡↔[]≡[]) lemma) ⟩
      erased [ cong erased x≡y ]            ≡⟨⟩
      cong erased x≡y                       ∎
    ]
    where
    @0 lemma : _
    lemma =
      x≡y                          ≡⟨ cong-id _ ⟩
      cong id x≡y                  ≡⟨⟩
      cong ([_] ∘ erased) x≡y      ≡⟨ sym $ cong-∘ _ _ _ ⟩
      cong [_] (cong erased x≡y)   ≡⟨ sym to-Erased-≡↔[]≡[] ⟩∎
      []-cong [ cong erased x≡y ]  ∎

  -- A "computation rule" for []-cong.

  []-cong-refl :
    {@0 A : Set a} {@0 x : A} →
    []-cong [ refl x ] ≡ refl [ x ]
  []-cong-refl {A = A} {x = x} =
    sym $ _↔_.to (from≡↔≡to $ Eq.↔⇒≃ Erased-≡↔[]≡[]) (
      _↔_.from Erased-≡↔[]≡[] (refl [ x ])  ≡⟨ from-Erased-≡↔[]≡[] ⟩
      [ cong erased (refl [ x ]) ]          ≡⟨ []-cong [ cong-refl _ ] ⟩∎
      [ refl x ]                            ∎)

  ----------------------------------------------------------------------
  -- Erased preserves all kinds of functions

  module _ {@0 A : Set a} {@0 B : Set b} where

    -- Erased preserves embeddings.

    Erased-cong-Embedding :
      @0 Embedding A B → Embedding (Erased A) (Erased B)
    Erased-cong-Embedding A↣B = record
      { to           = Erased-cong-→ (M.to A↣B)
      ; is-embedding = λ { [ x ] [ y ] →
          _≃_.is-equivalence $
          Eq.with-other-function
            ([ x ] ≡ [ y ]                     ↔⟨ inverse Erased-≡↔[]≡[] ⟩
             Erased (x ≡ y)                    ↝⟨ Erased-cong-≃ (M.equivalence A↣B) ⟩
             Erased (M.to A↣B x ≡ M.to A↣B y)  ↔⟨ Erased-≡↔[]≡[] ⟩□
             [ M.to A↣B x ] ≡ [ M.to A↣B y ]   □)
            (cong (Erased-cong-→ (M.to A↣B)))
            lemma }
      }
      where
      module M = Embedding

      lemma : ∀ {@0 x y} (eq : [ x ] ≡ [ y ]) → _
      lemma eq =
        []-cong
          [ cong (M.to A↣B) (erased (_↔_.from Erased-≡↔[]≡[] eq)) ]  ≡⟨ cong []-cong $
                                                                        []-cong [ cong (cong (M.to A↣B) ∘ erased) from-Erased-≡↔[]≡[] ] ⟩

        []-cong [ cong (M.to A↣B) (cong erased eq) ]                 ≡⟨ cong []-cong $ []-cong [ cong-∘ _ _ _ ] ⟩

        []-cong [ cong (M.to A↣B ∘ erased) eq ]                      ≡⟨ elim₁ (λ eq → []-cong [ cong (M.to A↣B ∘ erased) eq ] ≡ _)
                                                                              (
            []-cong [ cong (M.to A↣B ∘ erased) (refl _) ]                       ≡⟨ cong []-cong $ []-cong [ cong-refl _ ] ⟩
            []-cong [ refl _ ]                                                  ≡⟨ []-cong-refl ⟩
            refl _                                                              ≡⟨ sym $ cong-refl _ ⟩∎
            cong (Erased-cong-→ (M.to A↣B)) (refl _)                            ∎)
                                                                              eq ⟩∎
        cong (Erased-cong-→ (M.to A↣B)) eq                           ∎

    -- Erased preserves all kinds of functions.

    Erased-cong : @0 A ↝[ k ] B → Erased A ↝[ k ] Erased B
    Erased-cong {k = implication}         = Erased-cong-→
    Erased-cong {k = logical-equivalence} = Erased-cong-⇔
    Erased-cong {k = injection}           = Erased-cong-↣
    Erased-cong {k = embedding}           = Erased-cong-Embedding
    Erased-cong {k = surjection}          = Erased-cong-↠
    Erased-cong {k = bijection}           = Erased-cong-↔
    Erased-cong {k = equivalence}         = Erased-cong-≃
