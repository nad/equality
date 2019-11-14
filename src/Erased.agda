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

open import Bijection eq as Bijection using (_↔_; Has-quasi-inverse)
open import Embedding eq as Emb using (Embedding; Is-embedding)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (_↣_; Injective)
open import Monad eq hiding (map; map-id; map-∘)
open import Preimage eq using (_⁻¹_)
open import Surjection eq using (_↠_; Split-surjective)

private
  variable
    a b c ℓ p : Level
    A B       : Set a
    P         : A → Set p
    k k′ x y  : A
    n         : ℕ

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
-- Erased preserves some kinds of functions

-- Erased preserves dependent functions.

map :
  {@0 A : Set a} {@0 P : A → Set b} →
  @0 ((x : A) → P x) → (x : Erased A) → Erased (P (erased x))
map f [ x ] = [ f x ]

-- Erased is functorial for dependent functions.

map-id : {@0 A : Set a} → map id ≡ id {A = Erased A}
map-id = refl _

map-∘ :
  {@0 A : Set a} {@0 P : A → Set b} {@0 Q : {x : A} → P x → Set c}
  (@0 f : ∀ {x} (y : P x) → Q y) (@0 g : (x : A) → P x) →
  map (f ∘ g) ≡ map f ∘ map g
map-∘ _ _ = refl _

-- Erased preserves logical equivalences.

Erased-cong-⇔ :
  {@0 A : Set a} {@0 B : Set b} →
  @0 A ⇔ B → Erased A ⇔ Erased B
Erased-cong-⇔ A⇔B = record
  { to   = map (_⇔_.to   A⇔B)
  ; from = map (_⇔_.from A⇔B)
  }

-- Erased is functorial for logical equivalences.

Erased-cong-⇔-id :
  {@0 A : Set a} →
  Erased-cong-⇔ F.id ≡ F.id {A = Erased A}
Erased-cong-⇔-id = refl _

Erased-cong-⇔-∘ :
  {@0 A : Set a} {@0 B : Set b} {@0 C : Set c}
  (@0 f : B ⇔ C) (@0 g : A ⇔ B) →
  Erased-cong-⇔ (f F.∘ g) ≡ Erased-cong-⇔ f F.∘ Erased-cong-⇔ g
Erased-cong-⇔-∘ _ _ = refl _

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

-- The following result is based on a result in Mishra-Linger's PhD
-- thesis (see Section 5.4.4).

-- Erased (Erased A) is isomorphic to Erased A.

Erased-Erased↔Erased :
  {@0 A : Set a} →
  Erased (Erased A) ↔ Erased A
Erased-Erased↔Erased = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ x → [ erased (erased x) ]
      ; from = [_]
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

-- Erased ⊤ is isomorphic to ⊤.

Erased-⊤↔⊤ : Erased ⊤ ↔ ⊤
Erased-⊤↔⊤ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ _ → tt
      ; from = [_]
      }
    ; right-inverse-of = λ _ → refl _
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

-- Erased commutes with Π.

Erased-Π↔Π-Erased :
  {@0 A : Set a} {@0 P : A → Set p} →
  Erased ((x : A) → P x) ↔ ((x : Erased A) → Erased (P (erased x)))
Erased-Π↔Π-Erased = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ ([ f ]) → map f
      ; from = λ f → [ (λ x → erased (f [ x ])) ]
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

-- Erased commutes with ¬_ (assuming extensionality).

Erased-¬↔¬ :
  {@0 A : Set a} →
  Extensionality? k a lzero →
  Erased (¬ A) ↝[ k ] ¬ Erased A
Erased-¬↔¬ {A = A} ext =
  Erased (A → ⊥)         ↔⟨ Erased-Π↔Π-Erased ⟩
  (Erased A → Erased ⊥)  ↝⟨ (∀-cong ext λ _ → from-isomorphism Erased-⊥↔⊥) ⟩□
  (Erased A → ⊥)         □

-- The following two results are inspired by a result in
-- Mishra-Linger's PhD thesis (see Section 5.4.1).
--
-- See also Π-Erased↔Π0[], Π-Erased≃Π0[], Π-Erased↔Π0 and Π-Erased≃Π0
-- in Erased.Cubical and Erased.With-K.

-- There is a logical equivalence between
-- (x : Erased A) → P (erased x) and (@0 x : A) → P x.

Π-Erased⇔Π0 :
  {@0 A : Set a} {@0 P : A → Set p} →
  ((x : Erased A) → P (erased x)) ⇔ ((@0 x : A) → P x)
Π-Erased⇔Π0 = record
  { to   = λ f x → f [ x ]
  ; from = λ f ([ x ]) → f x
  }

-- There is a bijection between (x : Erased A) → P x and
-- (@0 x : A) → P [ x ].

Π-Erased↔Π0[] : ((x : Erased A) → P x) ↔ ((@0 x : A) → P [ x ])
Π-Erased↔Π0[] = record
  { surjection = record
    { logical-equivalence = Π-Erased⇔Π0
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

------------------------------------------------------------------------
-- A variant of Dec ∘ Erased

-- Dec-Erased A means that either we have A (erased), or we have ¬ A
-- (also erased).

Dec-Erased : @0 Set ℓ → Set ℓ
Dec-Erased A = Erased A ⊎ Erased (¬ A)

-- Dec-Erased A is isomorphic to Dec (Erased A) (assuming
-- extensionality).

Dec-Erased↔Dec-Erased :
  {@0 A : Set a} →
  Extensionality? k a lzero →
  Dec-Erased A ↝[ k ] Dec (Erased A)
Dec-Erased↔Dec-Erased {A = A} ext =
  Erased A ⊎ Erased (¬ A)  ↝⟨ F.id ⊎-cong Erased-¬↔¬ ext ⟩□
  Erased A ⊎ ¬ Erased A    □

-- A map function for Dec-Erased.

Dec-Erased-map :
  {@0 A : Set a} {@0 B : Set b} →
  @0 A ⇔ B → Dec-Erased A → Dec-Erased B
Dec-Erased-map A⇔B =
  ⊎-map (map (_⇔_.to A⇔B))
        (map (_∘ _⇔_.from A⇔B))

-- Dec-Erased preserves logical equivalences.

Dec-Erased-cong-⇔ :
  {@0 A : Set a} {@0 B : Set b} →
  @0 A ⇔ B → Dec-Erased A ⇔ Dec-Erased B
Dec-Erased-cong-⇔ A⇔B = record
  { to   = Dec-Erased-map A⇔B
  ; from = Dec-Erased-map (inverse A⇔B)
  }

------------------------------------------------------------------------
-- Some results that follow if "[]-cong" can be defined

module []-cong₁
  ([]-cong :
     ∀ {a} {@0 A : Set a} {@0 x y : A} →
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
    to [ sup x f ] = sup [ x ] (λ ([ y ]) → to [ f y ])

    from : W (Erased A) (λ x → Erased (P (erased x))) → Erased (W A P)
    from (sup [ x ] f) = [ sup x (λ y → erased (from (f [ y ]))) ]

    to∘from :
      (x : W (Erased A) (λ x → Erased (P (erased x)))) →
      to (from x) ≡ x
    to∘from (sup [ x ] f) =
      cong (sup [ x ]) (apply-ext ext (λ ([ y ]) →
        to∘from (f [ y ])))

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

    -- A variant of Erased-cong (which is defined below).

    Erased-cong? :
      @0 (∀ {k} → Extensionality? k a b → A ↝[ k ] B) →
      Extensionality? k a b → Erased A ↝[ k ] Erased B
    Erased-cong? hyp = generalise-ext?
      (Erased-cong-⇔ (hyp _))
      (λ ext → Erased-cong-↔ (hyp ext))

  -- Erased commutes with _⇔_.

  Erased-⇔↔⇔ :
    {@0 A : Set a} {@0 B : Set b} →
    Erased (A ⇔ B) ↔ (Erased A ⇔ Erased B)
  Erased-⇔↔⇔ {A = A} {B = B} =
    Erased (A ⇔ B)                                 ↝⟨ Erased-cong-↔ ⇔↔→×→ ⟩
    Erased ((A → B) × (B → A))                     ↝⟨ Erased-Σ↔Σ ⟩
    Erased (A → B) × Erased (B → A)                ↝⟨ Erased-Π↔Π-Erased ×-cong Erased-Π↔Π-Erased ⟩
    (Erased A → Erased B) × (Erased B → Erased A)  ↝⟨ inverse ⇔↔→×→ ⟩□
    (Erased A ⇔ Erased B)                          □

------------------------------------------------------------------------
-- Some results that follow if "[]-cong" is an equivalence

module []-cong₂
  ([]-cong :
     ∀ {a} {@0 A : Set a} {@0 x y : A} →
     Erased (x ≡ y) → [ x ] ≡ [ y ])
  ([]-cong-equivalence :
     ∀ {a} {@0 A : Set a} {@0 x y : A} →
     Is-equivalence ([]-cong {x = x} {y = y}))
  where

  open []-cong₁ []-cong public

  -- There is a bijection between erased equality proofs and
  -- equalities between erased values.

  Erased-≡↔[]≡[] :
    {@0 A : Set a} {@0 x y : A} →
    Erased (x ≡ y) ↔ [ x ] ≡ [ y ]
  Erased-≡↔[]≡[] = _≃_.bijection Eq.⟨ _ , []-cong-equivalence ⟩

  -- The inverse of []-cong.

  []-cong⁻¹ :
    {@0 A : Set a} {@0 x y : A} →
    [ x ] ≡ [ y ] → Erased (x ≡ y)
  []-cong⁻¹ = _↔_.from Erased-≡↔[]≡[]

  ----------------------------------------------------------------------
  -- All h-levels are closed under Erased

  -- Erased commutes with H-level′ n (assuming extensionality).

  Erased-H-level′↔H-level′ :
    {@0 A : Set a} →
    Extensionality? k a a →
    ∀ n → Erased (H-level′ n A) ↝[ k ] H-level′ n (Erased A)
  Erased-H-level′↔H-level′ {A = A} ext zero =
    Erased (H-level′ zero A)                                              ↔⟨⟩
    Erased (∃ λ (x : A) → (y : A) → x ≡ y)                                ↔⟨ Erased-Σ↔Σ ⟩
    (∃ λ (x : Erased A) → Erased ((y : A) → erased x ≡ y))                ↔⟨ (∃-cong λ _ → Erased-Π↔Π-Erased) ⟩
    (∃ λ (x : Erased A) → (y : Erased A) → Erased (erased x ≡ erased y))  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → from-isomorphism Erased-≡↔[]≡[]) ⟩
    (∃ λ (x : Erased A) → (y : Erased A) → x ≡ y)                         ↔⟨⟩
    H-level′ zero (Erased A)                                              □
  Erased-H-level′↔H-level′ {A = A} ext (suc n) =
    Erased (H-level′ (suc n) A)                                      ↔⟨⟩
    Erased ((x y : A) → H-level′ n (x ≡ y))                          ↔⟨ Erased-Π↔Π-Erased ⟩
    ((x : Erased A) → Erased ((y : A) → H-level′ n (erased x ≡ y)))  ↝⟨ (∀-cong ext λ _ → from-isomorphism Erased-Π↔Π-Erased) ⟩
    ((x y : Erased A) → Erased (H-level′ n (erased x ≡ erased y)))   ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Erased-H-level′↔H-level′ ext n) ⟩
    ((x y : Erased A) → H-level′ n (Erased (erased x ≡ erased y)))   ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → H-level′-cong ext n Erased-≡↔[]≡[]) ⟩
    ((x y : Erased A) → H-level′ n (x ≡ y))                          ↔⟨⟩
    H-level′ (suc n) (Erased A)                                      □

  -- Erased commutes with H-level n (assuming extensionality).

  Erased-H-level↔H-level :
    {@0 A : Set a} →
    Extensionality? k a a →
    ∀ n → Erased (H-level n A) ↝[ k ] H-level n (Erased A)
  Erased-H-level↔H-level {A = A} ext n =
    Erased (H-level n A)   ↝⟨ Erased-cong? H-level↔H-level′ ext ⟩
    Erased (H-level′ n A)  ↝⟨ Erased-H-level′↔H-level′ ext n ⟩
    H-level′ n (Erased A)  ↝⟨ inverse-ext? H-level↔H-level′ ext ⟩□
    H-level n (Erased A)   □

  -- H-level n is closed under Erased.

  H-level-Erased :
    {@0 A : Set a} →
    ∀ n → @0 H-level n A → H-level n (Erased A)
  H-level-Erased n h = Erased-H-level↔H-level _ n [ h ]

  ----------------------------------------------------------------------
  -- Erased is a modality

  -- The terminology here roughly follows that of "Modalities in
  -- Homotopy Type Theory" by Rijke, Shulman and Spitters.

  -- Erased is the modal operator of a uniquely eliminating modality
  -- with [_] as the modal unit.

  uniquely-eliminating-modality :
    Is-equivalence
      (λ (f : (x : Erased A) → Erased (P x)) → f ∘ [_] {A = A})
  uniquely-eliminating-modality {A = A} {P = P} =
    _≃_.is-equivalence
      (((x : Erased A) → Erased (P x))  ↔⟨ inverse Erased-Π↔Π-Erased ⟩
       Erased ((x : A) → (P [ x ]))     ↔⟨ Erased-Π↔Π ⟩
       ((x : A) → Erased (P [ x ]))     □)

  -- Erased is a lex modality (see Theorem 3.1, case (i) in the paper
  -- by Rijke et al. for the definition used here).

  lex-modality :
    {x y : A} → Contractible (Erased A) → Contractible (Erased (x ≡ y))
  lex-modality {A = A} {x = x} {y = y} =
    Contractible (Erased A)        ↝⟨ _⇔_.from (Erased-H-level↔H-level _ 0) ⟩
    Erased (Contractible A)        ↝⟨ map (⇒≡ 0) ⟩
    Erased (Contractible (x ≡ y))  ↝⟨ Erased-H-level↔H-level _ 0 ⟩□
    Contractible (Erased (x ≡ y))  □

  ----------------------------------------------------------------------
  -- Some isomorphisms

  -- Erased "commutes" with _⁻¹_.

  Erased-⁻¹ :
    {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} {@0 y : B} →
    Erased (f ⁻¹ y) ↔ map f ⁻¹ [ y ]
  Erased-⁻¹ {f = f} {y = y} =
    Erased (∃ λ x → f x ≡ y)             ↝⟨ Erased-Σ↔Σ ⟩
    (∃ λ x → Erased (f (erased x) ≡ y))  ↝⟨ (∃-cong λ _ → Erased-≡↔[]≡[]) ⟩□
    (∃ λ x → map f x ≡ [ y ])            □

  -- Erased "commutes" with Is-equivalence.

  Erased-Is-equivalence↔Is-equivalence :
    {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    Erased (Is-equivalence f) ↝[ k ] Is-equivalence (map f)
  Erased-Is-equivalence↔Is-equivalence {a = a} {k = k} {f = f} ext =
    Erased (∀ x → Contractible (f ⁻¹ x))           ↔⟨ Erased-Π↔Π-Erased ⟩
    (∀ x → Erased (Contractible (f ⁻¹ erased x)))  ↝⟨ (∀-cong ext′ λ _ → Erased-H-level↔H-level ext 0) ⟩
    (∀ x → Contractible (Erased (f ⁻¹ erased x)))  ↝⟨ (∀-cong ext′ λ _ → H-level-cong ext 0 Erased-⁻¹) ⟩□
    (∀ x → Contractible (map f ⁻¹ x))              □
    where
    ext′ = lower-extensionality? k a lzero ext

  -- Erased "commutes" with Split-surjective.

  Erased-Split-surjective↔Split-surjective :
    {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} →
    Extensionality? k b (a ⊔ b) →
    Erased (Split-surjective f) ↝[ k ]
    Split-surjective (map f)
  Erased-Split-surjective↔Split-surjective {f = f} ext =
    Erased (∀ y → ∃ λ x → f x ≡ y)                    ↔⟨ Erased-Π↔Π-Erased ⟩
    (∀ y → Erased (∃ λ x → f x ≡ erased y))           ↝⟨ (∀-cong ext λ _ → from-isomorphism Erased-Σ↔Σ) ⟩
    (∀ y → ∃ λ x → Erased (f (erased x) ≡ erased y))  ↝⟨ (∀-cong ext λ _ → ∃-cong λ _ → from-isomorphism Erased-≡↔[]≡[]) ⟩
    (∀ y → ∃ λ x → [ f (erased x) ] ≡ y)              ↔⟨⟩
    (∀ y → ∃ λ x → map f x ≡ y)                       □

  -- Erased "commutes" with Has-quasi-inverse.

  Erased-Has-quasi-inverse↔Has-quasi-inverse :
    {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    Erased (Has-quasi-inverse f) ↝[ k ]
    Has-quasi-inverse (map f)
  Erased-Has-quasi-inverse↔Has-quasi-inverse
    {A = A} {B = B} {f = f} ext =

    Erased (∃ λ g → (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x))            ↔⟨ Erased-Σ↔Σ ⟩

    (∃ λ g →
       Erased ((∀ x → f (erased g x) ≡ x) × (∀ x → erased g (f x) ≡ x)))  ↝⟨ (∃-cong λ _ → from-isomorphism Erased-Σ↔Σ) ⟩

    (∃ λ g →
       Erased (∀ x → f (erased g x) ≡ x) ×
       Erased (∀ x → erased g (f x) ≡ x))                                 ↝⟨ Σ-cong Erased-Π↔Π-Erased (λ g →
                                                                             lemma ext f (erased g) ×-cong lemma ext (erased g) f) ⟩□
    (∃ λ g → (∀ x → map f (g x) ≡ x) × (∀ x → g (map f x) ≡ x))           □
    where
    lemma :
      {@0 A : Set a} {@0 B : Set b} →
      Extensionality? k (a ⊔ b) (a ⊔ b) →
      (@0 f : A → B) (@0 g : B → A) → _ ↝[ k ] _
    lemma {a = a} {k = k} ext f g =
      Erased (∀ x → f (g x) ≡ x)                    ↔⟨ Erased-Π↔Π-Erased ⟩
      (∀ x → Erased (f (g (erased x)) ≡ erased x))  ↝⟨ (∀-cong (lower-extensionality? k a a ext) λ _ → from-isomorphism Erased-≡↔[]≡[]) ⟩
      (∀ x → [ f (g (erased x)) ] ≡ x)              ↔⟨⟩
      (∀ x → map (f ∘ g) x ≡ x)                     □

  -- Erased "commutes" with Injective.

  Erased-Injective↔Injective :
    {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    Erased (Injective f) ↝[ k ] Injective (map f)
  Erased-Injective↔Injective {a = a} {b = b} {k = k} {f = f} ext =
    Erased (∀ {x y} → f x ≡ f y → x ≡ y)                          ↔⟨ Erased-cong-↔ Bijection.implicit-Π↔Π ⟩

    Erased (∀ x {y} → f x ≡ f y → x ≡ y)                          ↝⟨ Erased-cong? (λ {k} ext → ∀-cong (lower-extensionality? k b lzero ext) λ _ →
                                                                     from-isomorphism Bijection.implicit-Π↔Π) ext ⟩

    Erased (∀ x y → f x ≡ f y → x ≡ y)                            ↔⟨ Erased-Π↔Π-Erased ⟩

    (∀ x → Erased (∀ y → f (erased x) ≡ f y → erased x ≡ y))      ↝⟨ (∀-cong ext′ λ _ → from-isomorphism Erased-Π↔Π-Erased) ⟩

    (∀ x y →
     Erased (f (erased x) ≡ f (erased y) → erased x ≡ erased y))  ↝⟨ (∀-cong ext′ λ _ → ∀-cong ext′ λ _ → from-isomorphism Erased-Π↔Π-Erased) ⟩

    (∀ x y →
     Erased (f (erased x) ≡ f (erased y)) →
     Erased (erased x ≡ erased y))                                ↝⟨ (∀-cong ext′ λ _ → ∀-cong ext′ λ _ →
                                                                      generalise-ext?-sym
                                                                        (λ {k} ext → →-cong (lower-extensionality? ⌊ k ⌋-sym a b ext)
                                                                                            (from-isomorphism Erased-≡↔[]≡[])
                                                                                            (from-isomorphism Erased-≡↔[]≡[]))
                                                                        ext) ⟩

    (∀ x y → [ f (erased x) ] ≡ [ f (erased y) ] → x ≡ y)         ↝⟨ (∀-cong ext′ λ _ → from-isomorphism $ inverse Bijection.implicit-Π↔Π) ⟩

    (∀ x {y} → [ f (erased x) ] ≡ [ f (erased y) ] → x ≡ y)       ↔⟨ inverse Bijection.implicit-Π↔Π ⟩□

    (∀ {x y} → [ f (erased x) ] ≡ [ f (erased y) ] → x ≡ y)       □
    where
    ext′ = lower-extensionality? k b lzero ext

  -- Erased preserves injections.

  Erased-cong-↣ :
    {@0 A : Set a} {@0 B : Set b} →
    @0 A ↣ B → Erased A ↣ Erased B
  Erased-cong-↣ A↣B = record
    { to        = map (_↣_.to A↣B)
    ; injective = Erased-Injective↔Injective _ [ _↣_.injective A↣B ]
    }

  ----------------------------------------------------------------------
  -- A lemma

  -- If A is a proposition, then [_] {A = A} is an embedding.
  --
  -- See also Erased-Is-embedding-[] and Erased-Split-surjective-[]
  -- below as well as Very-stable→Is-embedding-[] and
  -- Very-stable→Split-surjective-[] in Erased.Stability and
  -- Injective-[] and Is-embedding-[] in Erased.With-K.

  Is-proposition→Is-embedding-[] :
    Is-proposition A → Is-embedding ([_] {A = A})
  Is-proposition→Is-embedding-[] prop =
    _⇔_.to (Emb.Injective⇔Is-embedding
              set (H-level-Erased 2 set) [_])
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
Erased-Split-surjective-[] = [ (λ ([ x ]) → x , refl _) ]

------------------------------------------------------------------------
-- Some results that follow if "[]-cong" is an equivalence that maps
-- [ refl x ] to refl [ x ]

module []-cong₃
  ([]-cong :
     ∀ {a} {@0 A : Set a} {@0 x y : A} →
     Erased (x ≡ y) → [ x ] ≡ [ y ])
  ([]-cong-equivalence :
     ∀ {a} {@0 A : Set a} {@0 x y : A} →
     Is-equivalence ([]-cong {x = x} {y = y}))
  ([]-cong-[refl]′ :
    ∀ {a} {A : Set a} {x : A} →
    []-cong [ refl x ] ≡ refl [ x ])
  where

  open []-cong₂ []-cong []-cong-equivalence public

  ----------------------------------------------------------------------
  -- Some definitions directly related to []-cong and []-cong⁻¹

  -- Rearrangement lemmas for []-cong and []-cong⁻¹.

  []-cong-[]≡cong-[] :
    ∀ {a} {A : Set a} {x y : A} {x≡y : x ≡ y} →
    []-cong [ x≡y ] ≡ cong [_] x≡y
  []-cong-[]≡cong-[] {x = x} {x≡y = x≡y} = elim¹
    (λ x≡y → []-cong [ x≡y ] ≡ cong [_] x≡y)
    ([]-cong [ refl x ]  ≡⟨ []-cong-[refl]′ ⟩
     refl [ x ]          ≡⟨ sym $ cong-refl _ ⟩∎
     cong [_] (refl x)   ∎)
    x≡y

  []-cong⁻¹≡[cong-erased] :
    {@0 A : Set a} {@0 x y : A} {@0 x≡y : [ x ] ≡ [ y ]} →
    []-cong⁻¹ x≡y ≡ [ cong erased x≡y ]
  []-cong⁻¹≡[cong-erased] {x≡y = x≡y} = []-cong
    [ erased ([]-cong⁻¹ x≡y)      ≡⟨ cong erased (_↔_.from (from≡↔≡to $ Eq.↔⇒≃ Erased-≡↔[]≡[]) lemma) ⟩
      erased [ cong erased x≡y ]  ≡⟨⟩
      cong erased x≡y             ∎
    ]
    where
    @0 lemma : _
    lemma =
      x≡y                          ≡⟨ cong-id _ ⟩
      cong id x≡y                  ≡⟨⟩
      cong ([_] ∘ erased) x≡y      ≡⟨ sym $ cong-∘ _ _ _ ⟩
      cong [_] (cong erased x≡y)   ≡⟨ sym []-cong-[]≡cong-[] ⟩∎
      []-cong [ cong erased x≡y ]  ∎

  -- A "computation rule" for []-cong⁻¹.

  []-cong⁻¹-refl :
    {@0 A : Set a} {@0 x : A} →
    []-cong⁻¹ (refl [ x ]) ≡ [ refl x ]
  []-cong⁻¹-refl {x = x} =
    []-cong⁻¹ (refl [ x ])        ≡⟨ []-cong⁻¹≡[cong-erased] ⟩
    [ cong erased (refl [ x ]) ]  ≡⟨ []-cong [ cong-refl _ ] ⟩∎
    [ refl x ]                    ∎

  -- A stronger variant of []-cong-[refl]′.

  []-cong-[refl] :
    {@0 A : Set a} {@0 x : A} →
    []-cong [ refl x ] ≡ refl [ x ]
  []-cong-[refl] {A = A} {x = x} =
    sym $ _↔_.to (from≡↔≡to $ Eq.↔⇒≃ Erased-≡↔[]≡[]) (
      []-cong⁻¹ (refl [ x ])  ≡⟨ []-cong⁻¹-refl ⟩∎
      [ refl x ]              ∎)

  -- The function map (cong f) can be expressed in terms of
  -- cong (map f) (up to pointwise equality).

  map-cong≡cong-map :
    {@0 A : Set a} {@0 B : Set b} {@0 x y : A}
    {@0 f : A → B} {x≡y : Erased (x ≡ y)} →
    map (cong f) x≡y ≡ []-cong⁻¹ (cong (map f) ([]-cong x≡y))
  map-cong≡cong-map {f = f} {x≡y = [ x≡y ]} =
    [ cong f x≡y ]                                    ≡⟨⟩
    [ cong (erased ∘ map f ∘ [_]) x≡y ]               ≡⟨ []-cong [ sym $ cong-∘ _ _ _ ] ⟩
    [ cong (erased ∘ map f) (cong [_] x≡y) ]          ≡⟨ []-cong [ cong (cong _) $ sym []-cong-[]≡cong-[] ] ⟩
    [ cong (erased ∘ map f) ([]-cong [ x≡y ]) ]       ≡⟨ []-cong [ sym $ cong-∘ _ _ _ ] ⟩
    [ cong erased (cong (map f) ([]-cong [ x≡y ])) ]  ≡⟨ sym []-cong⁻¹≡[cong-erased] ⟩∎
    []-cong⁻¹ (cong (map f) ([]-cong [ x≡y ]))        ∎

  ----------------------------------------------------------------------
  -- Erased commutes with all kinds of functions (in some cases
  -- assuming extensionality)

  -- Erased "commutes" with Is-embedding.

  Erased-Is-embedding↔Is-embedding :
    {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    Erased (Is-embedding f) ↝[ k ] Is-embedding (map f)
  Erased-Is-embedding↔Is-embedding {b = b} {k = k} {f = f} ext =
    Erased (∀ x y → Is-equivalence (cong f))                       ↔⟨ Erased-Π↔Π-Erased ⟩

    (∀ x → Erased (∀ y → Is-equivalence (cong f)))                 ↝⟨ (∀-cong ext′ λ _ → from-isomorphism Erased-Π↔Π-Erased) ⟩

    (∀ x y → Erased (Is-equivalence (cong f)))                     ↝⟨ (∀-cong ext′ λ _ → ∀-cong ext′ λ _ →
                                                                       Erased-Is-equivalence↔Is-equivalence ext) ⟩

    (∀ x y → Is-equivalence (map (cong f)))                        ↝⟨ (∀-cong ext′ λ x → ∀-cong ext′ λ y →
                                                                       Is-equivalence-cong ext λ _ → map-cong≡cong-map) ⟩

    (∀ x y → Is-equivalence ([]-cong⁻¹ ∘ cong (map f) ∘ []-cong))  ↝⟨ (∀-cong ext′ λ _ → ∀-cong ext′ λ _ →
                                                                       generalise-ext?-prop
                                                                         (record { to = to; from = from })
                                                                         (λ ext → Eq.propositional ext _)
                                                                         (λ ext → Eq.propositional ext _)
                                                                         ext) ⟩□
    (∀ x y → Is-equivalence (cong (map f)))                        □
    where
    ext′ = lower-extensionality? k b lzero ext

    to :
      {g : x ≡ y → map f x ≡ map f y} →
      Is-equivalence ([]-cong⁻¹ ∘ g ∘ []-cong) →
      Is-equivalence g
    to hyp =
      Eq.Two-out-of-three.g∘f-f
        (Eq.two-out-of-three _ _)
        (Eq.Two-out-of-three.g-g∘f
           (Eq.two-out-of-three _ _)
           (_≃_.is-equivalence $ from-isomorphism $
            inverse Erased-≡↔[]≡[])
           hyp)
        []-cong-equivalence

    from :
      {g : x ≡ y → map f x ≡ map f y} →
      Is-equivalence g →
      Is-equivalence ([]-cong⁻¹ ∘ g ∘ []-cong)
    from hyp =
      Eq.Two-out-of-three.f-g
        (Eq.two-out-of-three _ _)
        (Eq.Two-out-of-three.f-g
           (Eq.two-out-of-three _ _)
           []-cong-equivalence
           hyp)
        (_≃_.is-equivalence $ from-isomorphism $
         inverse Erased-≡↔[]≡[])

  -- Erased commutes with all kinds of functions (assuming
  -- extensionality).

  Erased-↝↝↝ :
    {@0 A : Set a} {@0 B : Set b} →
    Extensionality? k′ (a ⊔ b) (a ⊔ b) →
    Erased (A ↝[ k ] B) ↝[ k′ ] (Erased A ↝[ k ] Erased B)
  Erased-↝↝↝ {k = implication} _ = from-isomorphism Erased-Π↔Π-Erased

  Erased-↝↝↝ {k = logical-equivalence} _ = from-isomorphism Erased-⇔↔⇔

  Erased-↝↝↝ {k = injection} {A = A} {B = B} ext =
    Erased (A ↣ B)                                              ↔⟨ Erased-cong-↔ ↣↔∃-Injective ⟩
    Erased (∃ λ (f : A → B) → Injective f)                      ↔⟨ Erased-Σ↔Σ ⟩
    (∃ λ (f : Erased (A → B)) → Erased (Injective (erased f)))  ↝⟨ Σ-cong Erased-Π↔Π-Erased (λ _ → Erased-Injective↔Injective ext) ⟩
    (∃ λ (f : Erased A → Erased B) → Injective f)               ↔⟨ inverse ↣↔∃-Injective ⟩□
    Erased A ↣ Erased B                                         □

  Erased-↝↝↝ {k = embedding} {A = A} {B = B} ext =
    Erased (Embedding A B)                                         ↔⟨ Erased-cong-↔ Emb.Embedding-as-Σ ⟩
    Erased (∃ λ (f : A → B) → Is-embedding f)                      ↔⟨ Erased-Σ↔Σ ⟩
    (∃ λ (f : Erased (A → B)) → Erased (Is-embedding (erased f)))  ↝⟨ Σ-cong Erased-Π↔Π-Erased (λ _ → Erased-Is-embedding↔Is-embedding ext) ⟩
    (∃ λ (f : Erased A → Erased B) → Is-embedding f)               ↔⟨ inverse Emb.Embedding-as-Σ ⟩□
    Embedding (Erased A) (Erased B)                                □

  Erased-↝↝↝ {a = a} {k′ = k′} {k = surjection} {A = A} {B = B} ext =
    Erased (A ↠ B)                                                     ↔⟨ Erased-cong-↔ ↠↔∃-Split-surjective ⟩
    Erased (∃ λ (f : A → B) → Split-surjective f)                      ↔⟨ Erased-Σ↔Σ ⟩
    (∃ λ (f : Erased (A → B)) → Erased (Split-surjective (erased f)))  ↝⟨ Σ-cong Erased-Π↔Π-Erased (λ _ →
                                                                          Erased-Split-surjective↔Split-surjective
                                                                            (lower-extensionality? k′ a lzero ext)) ⟩
    (∃ λ (f : Erased A → Erased B) → Split-surjective f)               ↔⟨ inverse ↠↔∃-Split-surjective ⟩□
    Erased A ↠ Erased B                                                □

  Erased-↝↝↝ {k = bijection} {A = A} {B = B} ext =
    Erased (A ↔ B)                                                      ↔⟨ Erased-cong-↔ Bijection.↔-as-Σ ⟩
    Erased (∃ λ (f : A → B) → Has-quasi-inverse f)                      ↔⟨ Erased-Σ↔Σ ⟩
    (∃ λ (f : Erased (A → B)) → Erased (Has-quasi-inverse (erased f)))  ↝⟨ (Σ-cong Erased-Π↔Π-Erased λ _ →
                                                                            Erased-Has-quasi-inverse↔Has-quasi-inverse ext) ⟩
    (∃ λ (f : Erased A → Erased B) → Has-quasi-inverse f)               ↔⟨ inverse Bijection.↔-as-Σ ⟩□
    Erased A ↔ Erased B                                                 □

  Erased-↝↝↝ {k = equivalence} {A = A} {B = B} ext =
    Erased (A ≃ B)                                                   ↔⟨ Erased-cong-↔ Eq.≃-as-Σ ⟩
    Erased (∃ λ (f : A → B) → Is-equivalence f)                      ↔⟨ Erased-Σ↔Σ ⟩
    (∃ λ (f : Erased (A → B)) → Erased (Is-equivalence (erased f)))  ↝⟨ Σ-cong Erased-Π↔Π-Erased (λ _ → Erased-Is-equivalence↔Is-equivalence ext) ⟩
    (∃ λ (f : Erased A → Erased B) → Is-equivalence f)               ↔⟨ inverse Eq.≃-as-Σ ⟩□
    Erased A ≃ Erased B                                              □

  -- Erased commutes with all kinds of functions (in some cases
  -- assuming extensionality).

  Erased-↝↔↝ :
    {@0 A : Set a} {@0 B : Set b} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    Erased (A ↝[ k ] B) ↔ (Erased A ↝[ k ] Erased B)
  Erased-↝↔↝ {k = implication}         = λ _ → Erased-Π↔Π-Erased
  Erased-↝↔↝ {k = logical-equivalence} = λ _ → Erased-⇔↔⇔
  Erased-↝↔↝ {k = injection}           = Erased-↝↝↝
  Erased-↝↔↝ {k = embedding}           = Erased-↝↝↝
  Erased-↝↔↝ {k = surjection}          = Erased-↝↝↝
  Erased-↝↔↝ {k = bijection}           = Erased-↝↝↝
  Erased-↝↔↝ {k = equivalence}         = Erased-↝↝↝

  -- Erased-↝↔↝ and Erased-↝↝↝ produce equal functions.

  to-Erased-↝↔↝≡to-Erased-↝↝↝ :
    ∀ {@0 A : Set a} {@0 B : Set b}
    (ext : Extensionality? k (a ⊔ b) (a ⊔ b))
    (ext′ : Extensionality? k′ (a ⊔ b) (a ⊔ b)) →
    _↔_.to (Erased-↝↔↝ {k = k} {A = A} {B = B} ext) ≡
    to-implication (Erased-↝↝↝ {k′ = k′} {k = k} {A = A} {B = B} ext′)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = implication}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = logical-equivalence} _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = injection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = embedding}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = surjection}          _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = bijection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = equivalence}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = implication}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = logical-equivalence} _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = injection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = embedding}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = surjection}          _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = bijection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = equivalence}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = implication}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = logical-equivalence} _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = injection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = embedding}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = surjection}          _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = bijection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = equivalence}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = implication}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = logical-equivalence} _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = injection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = embedding}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = surjection}          _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = bijection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = equivalence}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = implication}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = logical-equivalence} _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = injection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = embedding}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = surjection}          _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = bijection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = equivalence}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = implication}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = logical-equivalence} _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = injection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = embedding}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = surjection}          _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = bijection}           _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = equivalence}         _   _ = refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = implication}         ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = logical-equivalence} ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = injection}           ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = embedding}           ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = surjection}          ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = bijection}           ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = equivalence}         ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _

  -- Erased preserves all kinds of functions.

  Erased-cong :
    {@0 A : Set a} {@0 B : Set b} →
    @0 A ↝[ k ] B → Erased A ↝[ k ] Erased B
  Erased-cong A↝B = Erased-↝↝↝ _ [ A↝B ]

  -- Dec-Erased preserves symmetric kinds of functions (in some cases
  -- assuming extensionality).

  Dec-Erased-cong :
    {@0 A : Set a} {@0 B : Set b} →
    Extensionality? ⌊ k ⌋-sym (a ⊔ b) lzero →
    @0 A ↝[ ⌊ k ⌋-sym ] B →
    Dec-Erased A ↝[ ⌊ k ⌋-sym ] Dec-Erased B
  Dec-Erased-cong ext A↝B =
    Erased-cong A↝B ⊎-cong Erased-cong (→-cong ext A↝B F.id)
