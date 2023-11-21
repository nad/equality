------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

-- Most of the definitions in this module are reexported, in one way
-- or another, from Erased.

-- This module imports Function-universe, but not Equivalence.Erased.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Erased.Level-1
  {e⁺} (eq-J : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq-J

open import Logical-equivalence using (_⇔_)
open import Prelude hiding ([_,_])

open import Accessibility eq-J as A using (Acc; Well-founded)
open import Bijection eq-J as Bijection using (_↔_; Has-quasi-inverse)
open import Embedding eq-J as Emb using (Embedding; Is-embedding)
open import Equality.Decidable-UIP eq-J
open import Equivalence eq-J as Eq using (_≃_; Is-equivalence)
import Equivalence.Contractible-preimages eq-J as CP
open import Equivalence.Erased.Basics eq-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
import Equivalence.Half-adjoint eq-J as HA
open import Equivalence-relation eq-J
open import Extensionality eq-J hiding (module Extensionality)
open import Function-universe eq-J as F hiding (id; _∘_)
open import H-level eq-J as H-level
open import H-level.Closure eq-J
open import Injection eq-J using (_↣_; Injective)
open import Modality.Basics eq-J
  using (Uniquely-eliminating-modality; Left-exact; Cotopological)
open import Monad eq-J hiding (map; map-id; map-∘)
open import Preimage eq-J using (_⁻¹_)
open import Surjection eq-J as Surjection using (_↠_; Split-surjective)
open import Univalence-axiom eq-J as U using (Univalence; ≡⇒→; _²/≡)

private
  variable
    a b c d ℓ ℓ₁ ℓ₂ p₁ p₂ q r : Level
    A B                       : Type a
    eq k k′ p x y             : A
    P                         : A → Type p
    f g                       : A → B
    n                         : ℕ

------------------------------------------------------------------------
-- Some basic definitions

open import Erased.Basics                       public
open import Erased.Box-cong-axiomatisation eq-J public

------------------------------------------------------------------------
-- Stability

-- A generalisation of Stable.

Stable-[_] : Kind → Type a → Type a
Stable-[ k ] A = Erased A ↝[ k ] A

-- A variant of Stable-[ equivalence ].

Very-stable : Type a → Type a
Very-stable A = Is-equivalence [ A ∣_]→

-- A variant of Stable-[ equivalenceᴱ ].

Very-stableᴱ : Type a → Type a
Very-stableᴱ A = Is-equivalenceᴱ [ A ∣_]→

-- Variants of the definitions above for equality.

Stable-≡ : Type a → Type a
Stable-≡ = For-iterated-equality 1 Stable

Stable-≡-[_] : Kind → Type a → Type a
Stable-≡-[ k ] = For-iterated-equality 1 Stable-[ k ]

Very-stable-≡ : Type a → Type a
Very-stable-≡ = For-iterated-equality 1 Very-stable

Very-stableᴱ-≡ : Type a → Type a
Very-stableᴱ-≡ = For-iterated-equality 1 Very-stableᴱ

------------------------------------------------------------------------
-- Propositional η-equality for Erased

-- The record type Erased is defined without definitional η-equality,
-- but propositional η-equality holds.

Erased-η :
  {@0 A : Type a} {x : Erased A} → [ erased x ] ≡ x
Erased-η {x = [ _ ]} = refl _

-- The type [ erased x ] ≡ [ erased y ] is equivalent to x ≡ y.

[erased]≡[erased]≃≡ :
  {@0 A : Type a} {x y : Erased A} →
  ([ erased x ] ≡ [ erased y ]) ≃ (x ≡ y)
[erased]≡[erased]≃≡ {x = [ _ ]} {y = [ _ ]} = F.id

------------------------------------------------------------------------
-- Erased is a monad

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ :
  {@0 A : Type a} {@0 B : Type b} →
  Erased A → (A → Erased B) → Erased B
x >>=′ f = [ erased (f (erased x)) ]

instance

  -- Erased is a monad.

  raw-monad : Raw-monad (λ (A : Type a) → Erased A)
  Raw-monad.return raw-monad = [_]→
  Raw-monad._>>=_  raw-monad = _>>=′_

  monad : Monad (λ (A : Type a) → Erased A)
  Monad.raw-monad      monad = raw-monad
  Monad.left-identity  monad = λ _ _ → Erased-η
  Monad.right-identity monad = λ _ → Erased-η
  Monad.associativity  monad = λ _ _ _ → refl _

------------------------------------------------------------------------
-- Erased preserves some kinds of functions

-- The function map id is pointwise equal to the identity function.

map-id : {@0 A : Type a} {x : Erased A} → map id x ≡ id x
map-id = Erased-η

-- The function map commutes with composition.

map-∘ :
  {@0 A : Type a} {@0 P : A → Type b} {@0 Q : {x : A} → P x → Type c}
  (@0 f : ∀ {x} (y : P x) → Q y) (@0 g : (x : A) → P x) →
  map (f ∘ g) ≡ map f ∘ map g
map-∘ _ _ = refl _

-- Erased preserves logical equivalences.

Erased-cong-⇔ :
  {@0 A : Type a} {@0 B : Type b} →
  @0 A ⇔ B → Erased A ⇔ Erased B
Erased-cong-⇔ A⇔B = record
  { to   = map (_⇔_.to   A⇔B)
  ; from = map (_⇔_.from A⇔B)
  }

-- The function Erased-cong-⇔ F.id is equal to F.id (assuming function
-- extensionality).

Erased-cong-⇔-id :
  {@0 A : Type a} →
  Extensionality a a →
  Erased-cong-⇔ F.id ≡ F.id {A = Erased A}
Erased-cong-⇔-id ext =
  cong₂ (λ f g → record { to = f; from = g })
    (apply-ext ext λ _ → map-id)
    (apply-ext ext λ _ → map-id)

-- Erased-cong-⇔ commutes with composition.

Erased-cong-⇔-∘ :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c}
  (@0 f : B ⇔ C) (@0 g : A ⇔ B) →
  Erased-cong-⇔ (f F.∘ g) ≡ Erased-cong-⇔ f F.∘ Erased-cong-⇔ g
Erased-cong-⇔-∘ _ _ = refl _

-- Erased preserves equivalences with erased proofs.

Erased-cong-≃ᴱ :
  {@0 A : Type a} {@0 B : Type b} →
  @0 A ≃ᴱ B → Erased A ≃ᴱ Erased B
Erased-cong-≃ᴱ A≃ᴱB = EEq.↔→≃ᴱ
  (map (_≃ᴱ_.to   A≃ᴱB))
  (map (_≃ᴱ_.from A≃ᴱB))
  (λ @0 { ([ x ]) → cong [_]→ (_≃ᴱ_.right-inverse-of A≃ᴱB x) })
  (λ @0 { ([ x ]) → cong [_]→ (_≃ᴱ_.left-inverse-of  A≃ᴱB x) })

------------------------------------------------------------------------
-- Some isomorphisms

-- In an erased context Erased A is always isomorphic to A.

Erased↔ : {@0 A : Type a} → Erased (Erased A ↔ A)
Erased↔ = [ record
  { surjection = record
    { logical-equivalence = record
      { to   = erased
      ; from = [_]→
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → Erased-η
  } ]

-- Erased ⊤ is isomorphic to ⊤.

Erased-⊤↔⊤ : Erased ⊤ ↔ ⊤
Erased-⊤↔⊤ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ _ → tt
      ; from = [_]→
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → Erased-η
  }

-- Erased ⊥ is isomorphic to ⊥.

Erased-⊥↔⊥ : Erased (⊥ {ℓ = ℓ}) ↔ ⊥ {ℓ = ℓ}
Erased-⊥↔⊥ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { [ () ] }
      ; from = [_]→
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ { [ () ] }
  }

-- Erased commutes with Π A (assuming function extensionality).

Π≃Erased-Π :
  {A : Type a} {@0 P : A → Type p} →
  ((x : A) → Erased (P x)) ↝[ a ∣ p ]-ΠΣ-cong Erased ((x : A) → P x)
Π≃Erased-Π = generalise-ext?-ΠΣ-cong
  (record
     { logical-equivalence = record
       { to   = λ f → [ (λ x → erased (f x)) ]
       ; from = λ f x → [ erased f x ]
       }
     ; right-inverse-of = λ { [ _ ] → refl _ }
     })
  (λ ext _ → apply-ext ext λ _ → Erased-η)

-- Erased commutes with Π A (assuming function extensionality).

Erased-Π↔Π :
  {A : Type a} {@0 P : A → Type p} →
  Erased ((x : A) → P x) ↝[ a ∣ p ] ((x : A) → Erased (P x))
Erased-Π↔Π = inverse-ext? (↝-ΠΣ-cong→↝[∣] Π≃Erased-Π)

-- A variant of Erased-Π↔Π.

Erased-Π≃ᴱΠ :
  {@0 A : Type a} {@0 P : A → Type p} →
  @0 Extensionality a p →
  Erased ((x : A) → P x) ≃ᴱ ((x : A) → Erased (P x))
Erased-Π≃ᴱΠ ext =
  EEq.[≃]→≃ᴱ (EEq.[proofs] $ from-bijection $ Erased-Π↔Π ext)

-- Erased commutes with Π (assuming function extensionality).

Π-Erased≃Erased-Π :
  {@0 A : Type a} {@0 P : A → Type p} →
  ((x : Erased A) → Erased (P (erased x))) ↝[ a ∣ p ]-ΠΣ-cong
  Erased ((x : A) → P x)
Π-Erased≃Erased-Π = generalise-ext?-ΠΣ-cong
  (record
     { logical-equivalence = record
       { to   = λ f → [ (λ x → erased (f [ x ])) ]
       ; from = λ ([ f ]) → map f
       }
     ; right-inverse-of = λ { [ _ ] → refl _ }
     })
  (λ ext _ → apply-ext ext λ { [ _ ] → Erased-η })

-- Erased commutes with Π (assuming function extensionality).

Erased-Π↔Π-Erased :
  {@0 A : Type a} {@0 P : A → Type p} →
  Erased ((x : A) → P x) ↝[ a ∣ p ]
  ((x : Erased A) → Erased (P (erased x)))
Erased-Π↔Π-Erased = inverse-ext? (↝-ΠΣ-cong→↝[∣] Π-Erased≃Erased-Π)

-- Erased commutes with Σ.

Erased-Σ↔Σ :
  {@0 A : Type a} {@0 P : A → Type p} →
  Erased (Σ A P) ↔ Σ (Erased A) (λ x → Erased (P (erased x)))
Erased-Σ↔Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { [ p ] → [ proj₁ p ] , [ proj₂ p ] }
      ; from = λ { ([ x ] , [ y ]) → [ x , y ] }
      }
    ; right-inverse-of = λ { ([ _ ] , [ _ ]) → refl _ }
    }
  ; left-inverse-of = λ { [ _ ] → refl _ }
  }

-- Erased commutes with ↑ ℓ.

Erased-↑↔↑ :
  {@0 A : Type a} →
  Erased (↑ ℓ A) ↔ ↑ ℓ (Erased A)
Erased-↑↔↑ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { [ x ] → lift [ lower x ] }
      ; from = λ { (lift [ x ]) → [ lift x ] }
      }
    ; right-inverse-of = λ { (lift [ _ ]) → refl _ }
    }
  ; left-inverse-of = λ { [ _ ] → refl _ }
  }

-- Erased commutes with ¬_ (assuming extensionality).

Erased-¬↔¬ :
  {@0 A : Type a} →
  Erased (¬ A) ↝[ a ∣ lzero ] ¬ Erased A
Erased-¬↔¬ {A} ext =
  Erased (A → ⊥)         ↝⟨ Erased-Π↔Π-Erased ext ⟩
  (Erased A → Erased ⊥)  ↝⟨ (∀-cong ext λ _ → from-isomorphism Erased-⊥↔⊥) ⟩□
  (Erased A → ⊥)         □

-- Erased can be dropped under ¬_ (assuming extensionality).

¬-Erased↔¬ :
  {A : Type a} →
  ¬ Erased A ↝[ a ∣ lzero ] ¬ A
¬-Erased↔¬ {a} {A} =
  generalise-ext?-prop
    (record
       { to   = λ ¬[a] a → ¬[a] [ a ]
       ; from = λ ¬a ([ a ]) → _↔_.to Erased-⊥↔⊥ [ ¬a a ]
       })
    ¬-propositional
    ¬-propositional

----------------------------------------------------------------------
-- Erased is a modality

-- The function λ A → Erased A is the modal operator of a uniquely
-- eliminating modality with [_]→ as the modal unit (assuming function
-- extensionality).
--
-- The terminology here roughly follows that of "Modalities in
-- Homotopy Type Theory" by Rijke, Shulman and Spitters.

uniquely-eliminating :
  {A : Type a} {@0 P : Erased A → Type p} →
  Extensionality a p →
  Is-equivalence
    (λ (f : (x : Erased A) → Erased (P x)) → f ∘ [ A ∣_]→)
uniquely-eliminating {A} {P} ext =
  _≃_.is-equivalence $
  Eq.with-other-function
    (((x : Erased A) → Erased (P x))             ↝⟨ (∀-cong ext λ { [ _ ] → F.id }) ⟩
     ((x : Erased A) → Erased (P [ erased x ]))  ↝⟨ inverse-ext? Erased-Π↔Π-Erased ext ⟩
     Erased ((x : A) → (P [ x ]))                ↝⟨ Erased-Π↔Π ext ⟩
     ((x : A) → Erased (P [ x ]))                □)
    _
    (λ _ → apply-ext ext λ _ → Erased-η)

-- The function λ A → Erased A is the modal operator of a uniquely
-- eliminating modality with [_]→ as the modal unit (assuming function
-- extensionality).

uniquely-eliminating-modality :
  Extensionality a a →
  Uniquely-eliminating-modality a
uniquely-eliminating-modality ext = λ where
    .Uniquely-eliminating-modality.◯ A                  → Erased A
    .Uniquely-eliminating-modality.η                    → [_]→
    .Uniquely-eliminating-modality.uniquely-eliminating →
      uniquely-eliminating ext

-- Two results that are closely related to uniquely-eliminating.
--
-- These results are based on the Coq source code accompanying
-- "Modalities in Homotopy Type Theory" by Rijke, Shulman and
-- Spitters.

-- Precomposition with [_]→ is injective for functions from Erased A
-- to Erased B (assuming function extensionality).

∘-[]-injective :
  {A : Type a} {@0 B : Type b} →
  Extensionality a b →
  Injective (λ (f : Erased A → Erased B) → f ∘ [_]→)
∘-[]-injective ext = _≃_.injective Eq.⟨ _ , uniquely-eliminating ext ⟩

-- A rearrangement lemma for ext⁻¹ and ∘-[]-injective.

ext⁻¹-∘-[]-injective :
  {@0 B : Type b} {ext : Extensionality a b}
  {f g : Erased A → Erased B} {p : f ∘ [_]→ ≡ g ∘ [_]→} →
  ext⁻¹ (∘-[]-injective ext {x = f} {y = g} p) [ x ] ≡ ext⁻¹ p x
ext⁻¹-∘-[]-injective {x} {ext} {f} {g} {p} =
  ext⁻¹ (∘-[]-injective ext p) [ x ]               ≡⟨ elim₁
                                                        (λ p → ext⁻¹ p [ x ] ≡ ext⁻¹ (_≃_.from equiv p) x) (
      ext⁻¹ (refl g) [ x ]                                 ≡⟨ cong-refl (_$ [ x ]) ⟩
      refl (g [ x ])                                       ≡⟨ sym $ cong-refl _ ⟩
      ext⁻¹ (refl (g ∘ [_]→)) x                            ≡⟨ cong (λ p → ext⁻¹ p x) $ sym $ cong-refl _ ⟩∎
      ext⁻¹ (_≃_.from equiv (refl g)) x                    ∎)
                                                        (∘-[]-injective ext p) ⟩
  ext⁻¹ (_≃_.from equiv (∘-[]-injective ext p)) x  ≡⟨ cong (flip ext⁻¹ x) $ _≃_.left-inverse-of equiv _ ⟩∎
  ext⁻¹ p x                                        ∎
  where
  equiv = Eq.≃-≡ Eq.⟨ _ , uniquely-eliminating ext ⟩

-- In erased contexts the function λ (A : Type a) → Erased A is the
-- modal operator of a cotopological modality.

@0 cotopological-modality : Cotopological (λ (A : Type a) → Erased A)
cotopological-modality =
    (λ {A x y} →
       Contractible (Erased A)        →⟨ H-level-cong _ 0 $ Erased↔ .erased ⟩
       Contractible A                 →⟨ H-level.⇒≡ 0 ⟩
       Contractible (x ≡ y)           →⟨ H-level-cong _ 0 $ inverse $ Erased↔ .erased ⟩□
       Contractible (Erased (x ≡ y))  □)
  , (λ {A} _ →
       Contractible (Erased A)  →⟨ H-level-cong _ 0 $ Erased↔ .erased ⟩□
       Contractible A           □)

----------------------------------------------------------------------
-- Some lemmas related to functions with erased domains

-- The following three results are inspired by a result in
-- Mishra-Linger's PhD thesis (see Section 5.4.1).
--
-- See also Π-Erased≃Π0[] below as well as
-- Π-Erased↔Π0[], Π-Erased≃Π0[], Π-Erased↔Π0 and Π-Erased≃Π0 in
-- Erased.Cubical and Erased.With-K.

-- There is a logical equivalence between
-- (x : Erased A) → P (erased x) and (@0 x : A) → P x.

Π-Erased⇔Π0 :
  {@0 A : Type a} {@0 P : A → Type p} →
  ((x : Erased A) → P (erased x)) ⇔ ((@0 x : A) → P x)
Π-Erased⇔Π0 = record
  { to   = λ f x → f [ x ]
  ; from = λ f ([ x ]) → f x
  }

-- A variant of Π-Erased⇔Π0.

Π-Erased⇔Π0[] :
  {@0 A : Type a} {@0 P : Erased A → Type p} →
  ((x : Erased A) → P x) ⇔ ((@0 x : A) → P [ x ])
Π-Erased⇔Π0[] = record
  { to   = λ f x → f [ x ]
  ; from = λ { f [ x ] → f x }
  }

-- There is an equivalence between (x : Erased A) → P (erased x) and
-- (@0 x : A) → P x (assuming function extensionality).

Π-Erased≃Π0 :
  {@0 A : Type a} {P : @0 A → Type p} →
  ((x : Erased A) → P (erased x)) ↝[ a ∣ p ] ((@0 x : A) → P x)
Π-Erased≃Π0 = generalise-ext?
  Π-Erased⇔Π0
  (λ ext →
       (λ _ → refl _)
     , (λ _ → apply-ext ext λ { [ _ ] → refl _ }))

-- A variant of H-level.Π-closure for function spaces with erased
-- explicit domains. Note the type of P.

Πᴱ-closure :
  {@0 A : Type a} {P : @0 A → Type p} →
  Extensionality a p →
  ∀ n →
  ((@0 x : A) → H-level n (P x)) →
  H-level n ((@0 x : A) → P x)
Πᴱ-closure {P} ext n =
  (∀ (@0 x) → H-level n (P x))       →⟨ Eq._≃₀_.from (Π-Erased≃Π0 ext) ⟩
  (∀ x → H-level n (P (x .erased)))  →⟨ Π-closure ext n ⟩
  H-level n (∀ x → P (x .erased))    →⟨ H-level-cong _ n (Π-Erased≃Π0 {k = equivalence} ext) ⟩□
  H-level n (∀ (@0 x) → P x)         □

-- A variant of H-level.Π-closure for function spaces with erased
-- implicit domains. Note the type of P.

implicit-Πᴱ-closure :
  {@0 A : Type a} {P : @0 A → Type p} →
  Extensionality a p →
  ∀ n →
  ((@0 x : A) → H-level n (P x)) →
  H-level n ({@0 x : A} → P x)
implicit-Πᴱ-closure {A} {P} ext n =
  (∀ (@0 x) → H-level n (P x))  →⟨ Πᴱ-closure ext n ⟩
  H-level n (∀ (@0 x) → P x)    →⟨ H-level-cong _ n $ inverse
                                   Bijection.implicit-Πᴱ↔Πᴱ′ ⟩□
  H-level n (∀ {@0 x} → P x)    □

-- Extensionality implies extensionality for some functions with
-- erased arguments (note the type of P).

apply-extᴱ :
  {@0 A : Type a} {P : @0 A → Type p} {f g : (@0 x : A) → P x} →
  Extensionality a p →
  ((@0 x : A) → f x ≡ g x) →
  f ≡ g
apply-extᴱ {A} {f} {g} ext =
  ((@0 x : A) → f x ≡ g x)                          →⟨ Eq._≃₀_.from (Π-Erased≃Π0 ext) ⟩
  ((x : Erased A) → f (x .erased) ≡ g (x .erased))  →⟨ apply-ext ext ⟩
  (λ x → f (x .erased)) ≡ (λ x → g (x .erased))     →⟨ cong (Eq._≃₀_.to (Π-Erased≃Π0 ext)) ⟩□
  f ≡ g                                             □

-- Extensionality implies extensionality for some functions with
-- implicit erased arguments (note the type of P).

implicit-apply-extᴱ :
  {@0 A : Type a} {P : @0 A → Type p} {f g : {@0 x : A} → P x} →
  Extensionality a p →
  ((@0 x : A) → f {x = x} ≡ g {x = x}) →
  _≡_ {A = {@0 x : A} → P x} f g
implicit-apply-extᴱ {A} {P} {f} {g} ext =
  ((@0 x : A) → f {x = x} ≡ g {x = x})             →⟨ apply-extᴱ ext ⟩
  (λ (@0 x) → f {x = x}) ≡ (λ (@0 x) → g {x = x})  →⟨ cong {B = {@0 x : A} → P x} (λ f {x = x} → f x) ⟩□
  _≡_ {A = {@0 x : A} → P x} f g                   □

-- A variant of ∀-cong for function spaces with erased explicit
-- domains.

∀ᴱ-cong :
  {@0 A : Type a} {P₁ : @0 A → Type p₁} {P₂ : @0 A → Type p₂} →
  Extensionality? k a (p₁ ⊔ p₂) →
  (∀ (@0 x) → P₁ x ↝[ k ] P₂ x) →
  ((@0 x : A) → P₁ x) ↝[ k ] ((@0 x : A) → P₂ x)
∀ᴱ-cong {p₁} {p₂} {k} {A} {P₁} {P₂} ext hyp =
  ((@0 x : A) → P₁ x)            ↝⟨ inverse-ext? Π-Erased≃Π0 (lower-extensionality? k lzero p₂ ext) ⟩
  ((([ x ]) : Erased A) → P₁ x)  ↝⟨ (∀-cong ext λ _ → hyp _) ⟩
  ((([ x ]) : Erased A) → P₂ x)  ↝⟨ Π-Erased≃Π0 (lower-extensionality? k lzero p₁ ext) ⟩□
  ((@0 x : A) → P₂ x)            □

-- A variant of Π-Erased≃Π0.
--
-- This lemma is inspired by a result in Mishra-Linger's PhD thesis
-- (see Section 5.4.1).

Π-Erased≃Π0[] :
  {@0 A : Type a} {P : Erased A → Type p} →
  ((x : Erased A) → P x) ↝[ a ∣ p ] ((@0 x : A) → P [ x ])
Π-Erased≃Π0[] = generalise-ext?
  Π-Erased⇔Π0[]
  (λ ext →
       (λ _ → apply-extᴱ ext λ _ → refl _)
     , (λ _ → apply-ext ext λ { [ _ ] → refl _ }))

------------------------------------------------------------------------
-- A variant of Dec ∘ Erased

-- Dec-Erased A means that either we have A (erased), or we have ¬ A
-- (also erased).

Dec-Erased : @0 Type ℓ → Type ℓ
Dec-Erased A = Erased A ⊎ Erased (¬ A)

-- Dec A implies Dec-Erased A.

Dec→Dec-Erased :
  {@0 A : Type a} → Dec A → Dec-Erased A
Dec→Dec-Erased (yes a) = yes [ a ]
Dec→Dec-Erased (no ¬a) = no [ ¬a ]

-- In erased contexts Dec-Erased A is equivalent to Dec A.

@0 Dec-Erased≃Dec :
  {@0 A : Type a} → Dec-Erased A ≃ Dec A
Dec-Erased≃Dec {A} =
  Eq.with-other-inverse
    (Erased A ⊎ Erased (¬ A)  ↔⟨ erased Erased↔ ⊎-cong erased Erased↔ ⟩□
     A ⊎ ¬ A                  □)
    Dec→Dec-Erased
    Prelude.[ (λ _ → refl _) , (λ _ → refl _) ]

-- Dec-Erased A is isomorphic to Dec (Erased A) (assuming
-- extensionality).

Dec-Erased↔Dec-Erased :
  {@0 A : Type a} →
  Dec-Erased A ↝[ a ∣ lzero ] Dec (Erased A)
Dec-Erased↔Dec-Erased {A} ext =
  Erased A ⊎ Erased (¬ A)  ↝⟨ F.id ⊎-cong Erased-¬↔¬ ext ⟩□
  Erased A ⊎ ¬ Erased A    □

-- A map function for Dec-Erased.

Dec-Erased-map :
  {@0 A : Type a} {@0 B : Type b} →
  @0 A ⇔ B → Dec-Erased A → Dec-Erased B
Dec-Erased-map A⇔B =
  ⊎-map (map (_⇔_.to A⇔B))
        (map (_∘ _⇔_.from A⇔B))

-- Dec-Erased preserves logical equivalences.

Dec-Erased-cong-⇔ :
  {@0 A : Type a} {@0 B : Type b} →
  @0 A ⇔ B → Dec-Erased A ⇔ Dec-Erased B
Dec-Erased-cong-⇔ A⇔B = record
  { to   = Dec-Erased-map A⇔B
  ; from = Dec-Erased-map (inverse A⇔B)
  }

-- If A and B are decided (with erased proofs), then A × B is.

Dec-Erased-× :
  {@0 A : Type a} {@0 B : Type b} →
  Dec-Erased A → Dec-Erased B → Dec-Erased (A × B)
Dec-Erased-× (no [ ¬a ]) _           = no [ ¬a ∘ proj₁ ]
Dec-Erased-× _           (no [ ¬b ]) = no [ ¬b ∘ proj₂ ]
Dec-Erased-× (yes [ a ]) (yes [ b ]) = yes [ a , b ]

-- If A and B are decided (with erased proofs), then A ⊎ B is.

Dec-Erased-⊎ :
  {@0 A : Type a} {@0 B : Type b} →
  Dec-Erased A → Dec-Erased B → Dec-Erased (A ⊎ B)
Dec-Erased-⊎ (yes [ a ]) _           = yes [ inj₁ a ]
Dec-Erased-⊎ (no [ ¬a ]) (yes [ b ]) = yes [ inj₂ b ]
Dec-Erased-⊎ (no [ ¬a ]) (no [ ¬b ]) = no [ Prelude.[ ¬a , ¬b ] ]

-- A variant of Equality.Decision-procedures.×.dec⇒dec⇒dec.

dec-erased⇒dec-erased⇒×-dec-erased :
  {@0 A : Type a} {@0 B : Type b} {@0 x₁ x₂ : A} {@0 y₁ y₂ : B} →
  Dec-Erased (x₁ ≡ x₂) →
  Dec-Erased (y₁ ≡ y₂) →
  Dec-Erased ((x₁ , y₁) ≡ (x₂ , y₂))
dec-erased⇒dec-erased⇒×-dec-erased = λ where
  (no  [ x₁≢x₂ ]) _               → no [ x₁≢x₂ ∘ cong proj₁ ]
  _               (no  [ y₁≢y₂ ]) → no [ y₁≢y₂ ∘ cong proj₂ ]
  (yes [ x₁≡x₂ ]) (yes [ y₁≡y₂ ]) → yes [ cong₂ _,_ x₁≡x₂ y₁≡y₂ ]

-- A variant of Equality.Decision-procedures.Σ.set⇒dec⇒dec⇒dec.
--
-- See also set⇒dec-erased⇒dec-erased⇒Σ-dec-erased below.

set⇒dec⇒dec-erased⇒Σ-dec-erased :
  {@0 A : Type a} {@0 P : A → Type p}
  {@0 x₁ x₂ : A} {@0 y₁ : P x₁} {@0 y₂ : P x₂} →
  @0 Is-set A →
  Dec (x₁ ≡ x₂) →
  (∀ eq → Dec-Erased (subst P eq y₁ ≡ y₂)) →
  Dec-Erased ((x₁ , y₁) ≡ (x₂ , y₂))
set⇒dec⇒dec-erased⇒Σ-dec-erased _ (no x₁≢x₂) _ =
  no [ x₁≢x₂ ∘ cong proj₁ ]
set⇒dec⇒dec-erased⇒Σ-dec-erased {P} {y₁} {y₂} set₁ (yes x₁≡x₂) dec₂ =
  ⊎-map
    (map (Σ-≡,≡→≡ x₁≡x₂))
    (map λ cast-y₁≢y₂ eq →
                                             $⟨ proj₂ (Σ-≡,≡←≡ eq) ⟩
       subst P (proj₁ (Σ-≡,≡←≡ eq)) y₁ ≡ y₂  ↝⟨ subst (λ p → subst _ p _ ≡ _) (set₁ _ _) ⟩
       subst P x₁≡x₂ y₁ ≡ y₂                 ↝⟨ cast-y₁≢y₂ ⟩□
       ⊥                                     □)
    (dec₂ x₁≡x₂)

-- A variant of Equality.Decision-procedures.Σ.decidable⇒dec⇒dec.
--
-- See also decidable-erased⇒dec-erased⇒Σ-dec-erased below.

decidable⇒dec-erased⇒Σ-dec-erased :
  {@0 A : Type a} {@0 P : A → Type p}
  {x₁ x₂ : A} {@0 y₁ : P x₁} {@0 y₂ : P x₂} →
  Decidable-equality A →
  (∀ eq → Dec-Erased (subst P eq y₁ ≡ y₂)) →
  Dec-Erased ((x₁ , y₁) ≡ (x₂ , y₂))
decidable⇒dec-erased⇒Σ-dec-erased dec =
  set⇒dec⇒dec-erased⇒Σ-dec-erased
    (decidable⇒set dec)
    (dec _ _)

------------------------------------------------------------------------
-- Decidable erased equality

-- A variant of Decidable-equality that is defined using Dec-Erased.

Decidable-erased-equality : Type ℓ → Type ℓ
Decidable-erased-equality A = (x y : A) → Dec-Erased (x ≡ y)

-- Decidable equality implies decidable erased equality.

Decidable-equality→Decidable-erased-equality :
  {@0 A : Type a} →
  Decidable-equality A →
  Decidable-erased-equality A
Decidable-equality→Decidable-erased-equality dec x y =
  Dec→Dec-Erased (dec x y)

-- In erased contexts Decidable-erased-equality A is equivalent to
-- Decidable-equality A (assuming extensionality).

@0 Decidable-erased-equality≃Decidable-equality :
  {A : Type a} →
  Decidable-erased-equality A ↝[ a ∣ a ] Decidable-equality A
Decidable-erased-equality≃Decidable-equality {A} ext =
  ((x y : A) → Dec-Erased (x ≡ y))  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → from-equivalence Dec-Erased≃Dec) ⟩□
  ((x y : A) → Dec (x ≡ y))         □

-- A map function for Decidable-erased-equality.

Decidable-erased-equality-map :
  A ↠ B →
  Decidable-erased-equality A → Decidable-erased-equality B
Decidable-erased-equality-map A↠B _≟_ x y =     $⟨ _↠_.from A↠B x ≟ _↠_.from A↠B y ⟩
  Dec-Erased (_↠_.from A↠B x ≡ _↠_.from A↠B y)  ↝⟨ Dec-Erased-map (_↠_.logical-equivalence $ Surjection.↠-≡ A↠B) ⟩□
  Dec-Erased (x ≡ y)                            □

-- A variant of Equality.Decision-procedures.×.Dec._≟_.

decidable-erased⇒decidable-erased⇒×-decidable-erased :
  {@0 A : Type a} {@0 B : Type b} →
  Decidable-erased-equality A →
  Decidable-erased-equality B →
  Decidable-erased-equality (A × B)
decidable-erased⇒decidable-erased⇒×-decidable-erased decA decB _ _ =
  dec-erased⇒dec-erased⇒×-dec-erased (decA _ _) (decB _ _)

-- A variant of Equality.Decision-procedures.Σ.Dec._≟_.
--
-- See also decidable-erased⇒decidable-erased⇒Σ-decidable-erased
-- below.

decidable⇒decidable-erased⇒Σ-decidable-erased :
  Decidable-equality A →
  ({x : A} → Decidable-erased-equality (P x)) →
  Decidable-erased-equality (Σ A P)
decidable⇒decidable-erased⇒Σ-decidable-erased
  {P} decA decP (_ , x₂) (_ , y₂) =
  decidable⇒dec-erased⇒Σ-dec-erased
    decA
    (λ eq → decP (subst P eq x₂) y₂)

------------------------------------------------------------------------
-- Erased binary relations

-- Lifts binary relations from A to Erased A.

Erasedᴾ :
  {@0 A : Type a} {@0 B : Type b} →
  @0 (A → B → Type r) →
  (Erased A → Erased B → Type r)
Erasedᴾ R x y = Erased (R (erased x) (erased y))

-- Erasedᴾ preserves Is-equivalence-relation.

Erasedᴾ-preserves-Is-equivalence-relation :
  {@0 A : Type a} {@0 R : A → A → Type r} →
  @0 Is-equivalence-relation R →
  Is-equivalence-relation (Erasedᴾ R)
Erasedᴾ-preserves-Is-equivalence-relation equiv = λ where
  .Is-equivalence-relation.reflexive →
    [ equiv .Is-equivalence-relation.reflexive ]
  .Is-equivalence-relation.symmetric →
    map (equiv .Is-equivalence-relation.symmetric)
  .Is-equivalence-relation.transitive →
    zip (equiv .Is-equivalence-relation.transitive)

------------------------------------------------------------------------
-- Some results that hold in erased contexts

-- In an erased context there is an equivalence between equality of
-- "boxed" values and equality of values.

@0 []≡[]≃≡ : ([ x ] ≡ [ y ]) ≃ (x ≡ y)
[]≡[]≃≡ {x} = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = cong erased
      ; from = cong [_]→
      }
    ; right-inverse-of = λ eq →
        cong erased (cong [_]→ eq)  ≡⟨ cong-∘ _ _ _ ⟩
        cong id eq                  ≡⟨ sym $ cong-id _ ⟩∎
        eq                          ∎
    }
  ; left-inverse-of = elim¹
      (λ { {y = [ _ ]} eq → cong [_]→ (cong erased eq) ≡ eq })
      (cong [_]→ (cong erased (refl [ x ]))  ≡⟨ cong (cong _) $ cong-refl _ ⟩
       cong [_]→ (refl x)                    ≡⟨ cong-refl _ ⟩∎
       refl [ x ]                            ∎)
  })

-- A variant of []≡[]≃≡.

@0 ≡≃erased≡erased : (x ≡ y) ≃ (erased x ≡ erased y)
≡≃erased≡erased {x = [ _ ]} {y = [ _ ]} = []≡[]≃≡

-- In an erased context [_]→ is always an embedding.

Erased-Is-embedding-[] :
  {@0 A : Type a} → Erased (Is-embedding [ A ∣_]→)
Erased-Is-embedding-[] =
  [ (λ x y → _≃_.is-equivalence (
       x ≡ y          ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ $ inverse $ erased Erased↔ ⟩□
       [ x ] ≡ [ y ]  □))
  ]

-- In an erased context [_]→ is always split surjective.

Erased-Split-surjective-[] :
  {@0 A : Type a} → Erased (Split-surjective [ A ∣_]→)
Erased-Split-surjective-[] = [ (λ @0 { [ x ] → x , refl _ }) ]

-- In erased contexts the type ∃ λ (A : Type a) → Erased (H-level n A)
-- has h-level 1 + n (assuming function extensionality and
-- univalence).

@0 H-level-1+-∃-H-level-Erased :
  Extensionality a a →
  Univalence a →
  ∀ n → H-level (1 + n) (∃ λ (A : Type a) → Erased (H-level n A))
H-level-1+-∃-H-level-Erased ext univ n =          $⟨ U.∃-H-level-H-level-1+ ext univ n ⟩
  H-level (1 + n) (∃ λ A → H-level n A)           →⟨ H-level-cong _ (1 + n) (∃-cong λ _ → inverse $ Erased↔ .erased) ⟩□
  H-level (1 + n) (∃ λ A → Erased (H-level n A))  □

------------------------------------------------------------------------
-- An alternative to []-cong-axiomatisation

-- If x and y have type Erased A, and x ≡ y, then
-- Erased (erased x ≡ erased y).

≡→Erased[erased≡erased] :
  {x y : Erased A} →
  x ≡ y → Erased (erased x ≡ erased y)
≡→Erased[erased≡erased] eq = [ cong erased eq ]

-- An alternative to []-cong-axiomatisation is to state that equality
-- on Erased A is "defined" by the function above, in the sense that
-- the function is an equivalence for all relevant arguments.
--
-- See also
-- []-cong-axiomatisation≃≡→Erased[erased≡erased]-axiomatisation
-- below.

≡→Erased[erased≡erased]-axiomatisation : (ℓ : Level) → Type (lsuc ℓ)
≡→Erased[erased≡erased]-axiomatisation ℓ =
  {A : Type ℓ} {x y : Erased A} →
  Is-equivalence
    (≡→Erased[erased≡erased] ⦂ (x ≡ y → Erased (erased x ≡ erased y)))

-- The type ≡→Erased[erased≡erased]-axiomatisation ℓ is propositional
-- (assuming function extensionality).

≡→Erased[erased≡erased]-axiomatisation-propositional :
  Extensionality (lsuc ℓ) ℓ →
  Is-proposition (≡→Erased[erased≡erased]-axiomatisation ℓ)
≡→Erased[erased≡erased]-axiomatisation-propositional {ℓ} ext =
  implicit-Π-closure ext 1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  Is-equivalence-propositional ext′
  where
  ext′ : Extensionality ℓ ℓ
  ext′ = lower-extensionality _ lzero ext

------------------------------------------------------------------------
-- A variant of []-cong-axiomatisation

-- A variant of []-cong-axiomatisation where some erased arguments
-- have been replaced with non-erased ones.

record []-cong-axiomatisation′ a : Type (lsuc a) where
  field
    []-cong :
      {A : Type a} {x y : A} →
      Erased (x ≡ y) → [ x ] ≡ [ y ]
    []-cong-[refl] :
      []-cong [ refl x ] ≡ refl [ x ]

-- When implementing the []-cong axioms it suffices to prove "weaker"
-- variants with fewer erased arguments.
--
-- See also
-- Erased.Stability.[]-cong-axiomatisation≃[]-cong-axiomatisation′.

[]-cong-axiomatisation′→[]-cong-axiomatisation :
  []-cong-axiomatisation′ a →
  []-cong-axiomatisation a
[]-cong-axiomatisation′→[]-cong-axiomatisation {a} ax = record
  { []-cong        = []-cong₀
  ; []-cong-[refl] = []-cong₀-[refl]
  }
  where
  open []-cong-axiomatisation′ ax

  []-cong₀ :
    {@0 A : Type a} {@0 x y : A} →
    Erased (x ≡ y) → [ x ] ≡ [ y ]
  []-cong₀ {A} {x} {y} =
    Erased (x ≡ y)          →⟨ map (cong [_]→) ⟩
    Erased ([ x ] ≡ [ y ])  →⟨ []-cong ⟩
    [ [ x ] ] ≡ [ [ y ] ]   →⟨ cong (map erased) ⟩□
    [ x ] ≡ [ y ]           □

  []-cong₀-[refl] :
    {@0 A : Type a} {@0 x : A} →
    []-cong₀ [ refl x ] ≡ refl [ x ]
  []-cong₀-[refl] {x} =
    cong (map erased) ([]-cong (map (cong [_]→) [ refl x ]))  ≡⟨⟩
    cong (map erased) ([]-cong [ cong [_]→ (refl x) ])        ≡⟨ cong (cong (map erased) ∘ []-cong) $
                                                                 []-cong₀ [ cong-refl _ ] ⟩
    cong (map erased) ([]-cong [ refl [ x ] ])                ≡⟨ cong (cong (map erased)) []-cong-[refl] ⟩
    cong (map erased) (refl [ [ x ] ])                        ≡⟨ cong-refl _ ⟩∎
    refl [ x ]                                                ∎

------------------------------------------------------------------------
-- Some alternatives to []-cong-axiomatisation

-- Stable-≡-Erased-axiomatisation′ a is the property that equality is
-- stable for Erased A, for every type A : Type a, along with a
-- "computation" rule.

Stable-≡-Erased-axiomatisation′ : (a : Level) → Type (lsuc a)
Stable-≡-Erased-axiomatisation′ a =
  ∃ λ (Stable-≡-Erased : {A : Type a} → Stable-≡ (Erased A)) →
    {A : Type a} {x : Erased A} →
    Stable-≡-Erased x x [ refl x ] ≡ refl x

-- Stable-≡-Erased-axiomatisation a is the property that equality is
-- stable for Erased A, for every *erased* type A : Type a, along with
-- a "computation" rule.

Stable-≡-Erased-axiomatisation : (a : Level) → Type (lsuc a)
Stable-≡-Erased-axiomatisation a =
  ∃ λ (Stable-≡-Erased : {@0 A : Type a} → Stable-≡ (Erased A)) →
    {@0 A : Type a} {x : Erased A} →
    Stable-≡-Erased x x [ refl x ] ≡ refl x

-- Some lemmas used to implement Extensionality→[]-cong as well as
-- Erased.Stability.[]-cong-axiomatisation≃Stable-≡-Erased-axiomatisation.

module Stable-≡-Erased-axiomatisation→[]-cong-axiomatisation
  ((Stable-≡-Erased , Stable-≡-Erased-[refl]) :
   Stable-≡-Erased-axiomatisation a)
  where

  -- An implementation of []-cong.

  []-cong :
    {@0 A : Type a} {@0 x y : A} →
    Erased (x ≡ y) → [ x ] ≡ [ y ]
  []-cong {x} {y} =
    Erased (x ≡ y)          ↝⟨ map (cong [_]→) ⟩
    Erased ([ x ] ≡ [ y ])  ↝⟨ Stable-≡-Erased _ _ ⟩□
    [ x ] ≡ [ y ]           □

  -- A "computation rule" for []-cong.

  []-cong-[refl] :
    {@0 A : Type a} {@0 x : A} →
    []-cong [ refl x ] ≡ refl [ x ]
  []-cong-[refl] {x} =
    []-cong [ refl x ]                          ≡⟨⟩
    Stable-≡-Erased _ _ [ cong [_]→ (refl x) ]  ≡⟨ cong (Stable-≡-Erased _ _) ([]-cong [ cong-refl _ ]) ⟩
    Stable-≡-Erased _ _ [ refl [ x ] ]          ≡⟨ Stable-≡-Erased-[refl] ⟩∎
    refl [ x ]                                  ∎

  -- The []-cong axioms can be instantiated.

  instance-of-[]-cong-axiomatisation :
    []-cong-axiomatisation a
  instance-of-[]-cong-axiomatisation = record
    { []-cong        = []-cong
    ; []-cong-[refl] = []-cong-[refl]
    }

-- One can also derive []-cong-axiomatisation a from
-- Stable-≡-Erased-axiomatisation′ a, by going via
-- []-cong-axiomatisation′ a.

module Stable-≡-Erased-axiomatisation′→[]-cong-axiomatisation
  ((Stable-≡-Erased , Stable-≡-Erased-[refl]) :
   Stable-≡-Erased-axiomatisation′ a)
  where

  -- An implementation of []-cong (with a non-erased type argument).

  []-cong :
    {A : Type a} {@0 x y : A} →
    Erased (x ≡ y) → [ x ] ≡ [ y ]
  []-cong {x} {y} =
    Erased (x ≡ y)          ↝⟨ map (cong [_]→) ⟩
    Erased ([ x ] ≡ [ y ])  ↝⟨ Stable-≡-Erased _ _ ⟩□
    [ x ] ≡ [ y ]           □

  -- A "computation rule" for []-cong.

  []-cong-[refl] :
    {A : Type a} {@0 x : A} →
    []-cong [ refl x ] ≡ refl [ x ]
  []-cong-[refl] {x} =
    []-cong [ refl x ]                          ≡⟨⟩
    Stable-≡-Erased _ _ [ cong [_]→ (refl x) ]  ≡⟨ cong (Stable-≡-Erased _ _) ([]-cong [ cong-refl _ ]) ⟩
    Stable-≡-Erased _ _ [ refl [ x ] ]          ≡⟨ Stable-≡-Erased-[refl] ⟩∎
    refl [ x ]                                  ∎

  -- []-cong-axiomatisation′ a is inhabited.

  instance-of-[]-cong-axiomatisation′ :
    []-cong-axiomatisation′ a
  instance-of-[]-cong-axiomatisation′ = record
    { []-cong        = []-cong
    ; []-cong-[refl] = []-cong-[refl]
    }

  -- The []-cong axioms can be instantiated.

  instance-of-[]-cong-axiomatisation :
    []-cong-axiomatisation a
  instance-of-[]-cong-axiomatisation =
    []-cong-axiomatisation′→[]-cong-axiomatisation
      instance-of-[]-cong-axiomatisation′

------------------------------------------------------------------------
-- In the presence of function extensionality the []-cong axioms can
-- be instantiated

-- Some lemmas used to implement
-- Extensionality→[]-cong-axiomatisation.

module Extensionality→[]-cong-axiomatisation
  (ext : Extensionality a a)
  where

  -- Equality is stable for Erased A.
  --
  -- The proof is based on the proof of Lemma 1.25 in "Modalities in
  -- Homotopy Type Theory" by Rijke, Shulman and Spitters, and the
  -- corresponding Coq source code.

  Stable-≡-Erased : {@0 A : Type a} → Stable-≡ (Erased A)
  Stable-≡-Erased x y eq =
    x                               ≡⟨ flip ext⁻¹ eq (

      (λ (_ : Erased (x ≡ y)) → x)     ≡⟨ ∘-[]-injective ext (

        (λ (_ : x ≡ y) → x)               ≡⟨ apply-ext ext (λ (eq : x ≡ y) →

          x                                  ≡⟨ eq ⟩∎
          y                                  ∎) ⟩∎

        (λ (_ : x ≡ y) → y)               ∎) ⟩∎

      (λ (_ : Erased (x ≡ y)) → y)     ∎) ⟩∎

    y                               ∎

  -- A "computation rule" for Stable-≡-Erased.

  Stable-≡-Erased-[refl] :
    {@0 A : Type a} {x : Erased A} →
    Stable-≡-Erased x x [ refl x ] ≡ refl x
  Stable-≡-Erased-[refl] {x = [ x ]} =
    Stable-≡-Erased [ x ] [ x ] [ refl [ x ] ]                    ≡⟨⟩
    ext⁻¹ (∘-[]-injective ext (apply-ext ext id)) [ refl [ x ] ]  ≡⟨ ext⁻¹-∘-[]-injective ⟩
    ext⁻¹ (apply-ext ext id) (refl [ x ])                         ≡⟨ cong (_$ refl _) $ _≃_.left-inverse-of (Eq.extensionality-isomorphism ext) _ ⟩∎
    refl [ x ]                                                    ∎

  open Stable-≡-Erased-axiomatisation→[]-cong-axiomatisation
    (Stable-≡-Erased , Stable-≡-Erased-[refl])
    public

-- If we have extensionality, then []-cong can be implemented.
--
-- The idea for this result comes from "Modalities in Homotopy Type
-- Theory" in which Rijke, Shulman and Spitters state that []-cong can
-- be implemented for every modality, and that it is an equivalence
-- for lex modalities (Theorem 3.1 (ix)).

Extensionality→[]-cong-axiomatisation :
  Extensionality a a →
  []-cong-axiomatisation a
Extensionality→[]-cong-axiomatisation ext =
  instance-of-[]-cong-axiomatisation
  where
  open Extensionality→[]-cong-axiomatisation ext

------------------------------------------------------------------------
-- Erased preserves some kinds of functions

-- The following definitions are parametrised by two implementations
-- of the []-cong axioms.

module Erased-cong
  (ax₁ : []-cong-axiomatisation ℓ₁)
  (ax₂ : []-cong-axiomatisation ℓ₂)
  {@0 A : Type ℓ₁} {@0 B : Type ℓ₂}
  where

  private
    module BC₁ = []-cong-axiomatisation ax₁
    module BC₂ = []-cong-axiomatisation ax₂

  -- Erased preserves split surjections.

  Erased-cong-↠ :
    @0 A ↠ B → Erased A ↠ Erased B
  Erased-cong-↠ A↠B = record
    { logical-equivalence = Erased-cong-⇔
                              (_↠_.logical-equivalence A↠B)
    ; right-inverse-of    = λ { [ x ] →
        BC₂.[]-cong [ _↠_.right-inverse-of A↠B x ] }
    }

  -- Erased preserves bijections.

  Erased-cong-↔ : @0 A ↔ B → Erased A ↔ Erased B
  Erased-cong-↔ A↔B = record
    { surjection      = Erased-cong-↠ (_↔_.surjection A↔B)
    ; left-inverse-of = λ { [ x ] →
        BC₁.[]-cong [ _↔_.left-inverse-of A↔B x ] }
    }

  -- Erased preserves equivalences.

  Erased-cong-≃ : @0 A ≃ B → Erased A ≃ Erased B
  Erased-cong-≃ A≃B =
    from-isomorphism (Erased-cong-↔ (from-isomorphism A≃B))

  -- A variant of Erased-cong (which is defined in Erased.Level-2).

  Erased-cong? :
    @0 A ↝[ c ∣ d ] B →
    Erased A ↝[ c ∣ d ]ᴱ Erased B
  Erased-cong? hyp = generalise-erased-ext?
    (Erased-cong-⇔ (hyp _))
    (λ ext → Erased-cong-↔ (hyp ext))

------------------------------------------------------------------------
-- Some results that follow if the []-cong axioms hold for a single
-- universe level

module []-cong₁ (ax : []-cong-axiomatisation ℓ) where

  open []-cong-axiomatisation ax public
  open Erased-cong ax ax

  ----------------------------------------------------------------------
  -- Some definitions directly related to []-cong

  -- []-cong is an equivalence.

  []-cong-equivalence :
    {@0 A : Type ℓ} {@0 x y : A} →
    Is-equivalence ([]-cong {x = x} {y = y})
  []-cong-equivalence {x} = _≃_.is-equivalence $ Eq.↔→≃
    _
    (λ eq → [ cong erased eq ])
    (elim¹
       (λ { {y = [ _ ]} eq → []-cong [ cong erased eq ] ≡ eq })
       ([]-cong [ cong erased (refl [ x ]) ]  ≡⟨ cong []-cong $ []-cong [ cong-refl _ ] ⟩
        []-cong [ refl x ]                    ≡⟨ []-cong-[refl] ⟩∎
        refl [ x ]                            ∎))
    (λ { [ eq ] →
         [ cong erased ([]-cong [ eq ]) ]    ≡⟨ []-cong
                                                  [ elim¹
                                                      (λ eq → cong erased ([]-cong [ eq ]) ≡ eq)
                                                      (
           cong erased ([]-cong [ refl x ])            ≡⟨ cong (cong erased) []-cong-[refl] ⟩
           cong erased (refl [ x ])                    ≡⟨ cong-refl _ ⟩∎
           refl x                                      ∎)
                                                      _
                                                  ] ⟩∎
         [ eq ]                              ∎ })

  -- There is an equivalence between erased equality proofs and
  -- equalities between erased values.

  Erased-≡≃[]≡[] :
    {@0 A : Type ℓ} {@0 x y : A} →
    Erased (x ≡ y) ≃ ([ x ] ≡ [ y ])
  Erased-≡≃[]≡[] = Eq.⟨ _ , []-cong-equivalence ⟩

  -- A variant of Erased-≡≃[]≡[].

  Erased-≡≃≡ :
    {@0 A : Type ℓ} {x y : Erased A} →
    Erased (erased x ≡ erased y) ≃ (x ≡ y)
  Erased-≡≃≡ {x} {y} =
    Erased (erased x ≡ erased y)  ↝⟨ Erased-≡≃[]≡[] ⟩
    [ erased x ] ≡ [ erased y ]   ↝⟨ [erased]≡[erased]≃≡ ⟩□
    x ≡ y                         □

  -- There is a bijection between erased equality proofs and
  -- equalities between erased values.

  Erased-≡↔[]≡[] :
    {@0 A : Type ℓ} {@0 x y : A} →
    Erased (x ≡ y) ↔ [ x ] ≡ [ y ]
  Erased-≡↔[]≡[] = _≃_.bijection Erased-≡≃[]≡[]

  -- The inverse of []-cong.

  []-cong⁻¹ :
    {@0 A : Type ℓ} {@0 x y : A} →
    [ x ] ≡ [ y ] → Erased (x ≡ y)
  []-cong⁻¹ = _≃_.from Erased-≡≃[]≡[]

  -- Rearrangement lemmas for []-cong and []-cong⁻¹.

  []-cong-[]≡cong-[] :
    {A : Type ℓ} {x y : A} {x≡y : x ≡ y} →
    []-cong [ x≡y ] ≡ cong [_]→ x≡y
  []-cong-[]≡cong-[] {x} {x≡y} = elim¹
    (λ x≡y → []-cong [ x≡y ] ≡ cong [_]→ x≡y)
    ([]-cong [ refl x ]  ≡⟨ []-cong-[refl] ⟩
     refl [ x ]          ≡⟨ sym $ cong-refl _ ⟩∎
     cong [_]→ (refl x)  ∎)
    x≡y

  []-cong⁻¹≡[cong-erased] :
    {@0 A : Type ℓ} {@0 x y : A} {@0 x≡y : [ x ] ≡ [ y ]} →
    []-cong⁻¹ x≡y ≡ [ cong erased x≡y ]
  []-cong⁻¹≡[cong-erased] {x≡y} = []-cong
    [ erased ([]-cong⁻¹ x≡y)      ≡⟨ cong erased (_↔_.from (from≡↔≡to Erased-≡≃[]≡[]) lemma) ⟩
      erased [ cong erased x≡y ]  ≡⟨⟩
      cong erased x≡y             ∎
    ]
    where
    @0 lemma : _
    lemma =
      x≡y                          ≡⟨ sym (_≃_.left-inverse-of []≡[]≃≡ _) ⟩
      cong [_]→ (cong erased x≡y)  ≡⟨ sym []-cong-[]≡cong-[] ⟩∎
      []-cong [ cong erased x≡y ]  ∎

  -- A "computation rule" for []-cong⁻¹.

  []-cong⁻¹-refl :
    {@0 A : Type ℓ} {@0 x : A} →
    []-cong⁻¹ (refl [ x ]) ≡ [ refl x ]
  []-cong⁻¹-refl {x} =
    []-cong⁻¹ (refl [ x ])        ≡⟨ []-cong⁻¹≡[cong-erased] ⟩
    [ cong erased (refl [ x ]) ]  ≡⟨ []-cong [ cong-refl _ ] ⟩∎
    [ refl x ]                    ∎

  -- []-cong and []-cong⁻¹ commute (kind of) with sym.

  []-cong⁻¹-sym :
    {@0 A : Type ℓ} {@0 x y : A} {x≡y : [ x ] ≡ [ y ]} →
    []-cong⁻¹ (sym x≡y) ≡ map sym ([]-cong⁻¹ x≡y)
  []-cong⁻¹-sym {x≡y} = elim¹
    (λ { {y = [ _ ]} x≡y →
         []-cong⁻¹ (sym x≡y) ≡ map sym ([]-cong⁻¹ x≡y) })
    ([]-cong⁻¹ (sym (refl _))      ≡⟨ cong []-cong⁻¹ sym-refl ⟩
     []-cong⁻¹ (refl _)            ≡⟨ []-cong⁻¹-refl ⟩
     [ refl _ ]                    ≡⟨ []-cong [ sym sym-refl ] ⟩
     [ sym (refl _) ]              ≡⟨⟩
     map sym [ refl _ ]            ≡⟨ cong (map sym) $ sym []-cong⁻¹-refl ⟩∎
     map sym ([]-cong⁻¹ (refl _))  ∎)
    x≡y

  []-cong-[sym] :
    {@0 A : Type ℓ} {@0 x y : A} {@0 x≡y : x ≡ y} →
    []-cong [ sym x≡y ] ≡ sym ([]-cong [ x≡y ])
  []-cong-[sym] {x≡y} =
    sym $ _↔_.to (from≡↔≡to $ Eq.↔⇒≃ Erased-≡↔[]≡[]) (
      []-cong⁻¹ (sym ([]-cong [ x≡y ]))      ≡⟨ []-cong⁻¹-sym ⟩
      map sym ([]-cong⁻¹ ([]-cong [ x≡y ]))  ≡⟨ cong (map sym) $ _↔_.left-inverse-of Erased-≡↔[]≡[] _ ⟩∎
      map sym [ x≡y ]                        ∎)

  -- []-cong and []-cong⁻¹ commute (kind of) with trans.

  []-cong⁻¹-trans :
    {@0 A : Type ℓ} {@0 x y z : A}
    {x≡y : [ x ] ≡ [ y ]} {y≡z : [ y ] ≡ [ z ]} →
    []-cong⁻¹ (trans x≡y y≡z) ≡
    [ trans (erased ([]-cong⁻¹ x≡y)) (erased ([]-cong⁻¹ y≡z)) ]
  []-cong⁻¹-trans {x≡y} {y≡z} = elim₁
    (λ { {x = [ _ ]} x≡y →
         []-cong⁻¹ (trans x≡y y≡z) ≡
         [ trans (erased ([]-cong⁻¹ x≡y)) (erased ([]-cong⁻¹ y≡z)) ] })
    ([]-cong⁻¹ (trans (refl _) y≡z)                                    ≡⟨ cong []-cong⁻¹ $ trans-reflˡ _ ⟩
     []-cong⁻¹ y≡z                                                     ≡⟨⟩
     [ erased ([]-cong⁻¹ y≡z) ]                                        ≡⟨ []-cong [ sym $ trans-reflˡ _ ] ⟩
     [ trans (refl _) (erased ([]-cong⁻¹ y≡z)) ]                       ≡⟨⟩
     [ trans (erased [ refl _ ]) (erased ([]-cong⁻¹ y≡z)) ]            ≡⟨ []-cong [ cong (flip trans _) $ cong erased $ sym
                                                                          []-cong⁻¹-refl ] ⟩∎
     [ trans (erased ([]-cong⁻¹ (refl _))) (erased ([]-cong⁻¹ y≡z)) ]  ∎)
    x≡y

  []-cong-[trans] :
    {@0 A : Type ℓ} {@0 x y z : A} {@0 x≡y : x ≡ y} {@0 y≡z : y ≡ z} →
    []-cong [ trans x≡y y≡z ] ≡
    trans ([]-cong [ x≡y ]) ([]-cong [ y≡z ])
  []-cong-[trans] {x≡y} {y≡z} =
    sym $ _↔_.to (from≡↔≡to $ Eq.↔⇒≃ Erased-≡↔[]≡[]) (
      []-cong⁻¹ (trans ([]-cong [ x≡y ]) ([]-cong [ y≡z ]))  ≡⟨ []-cong⁻¹-trans ⟩

      [ trans (erased ([]-cong⁻¹ ([]-cong [ x≡y ])))
              (erased ([]-cong⁻¹ ([]-cong [ y≡z ]))) ]       ≡⟨ []-cong [ cong₂ (λ p q → trans (erased p) (erased q))
                                                                            (_↔_.left-inverse-of Erased-≡↔[]≡[] _)
                                                                            (_↔_.left-inverse-of Erased-≡↔[]≡[] _) ] ⟩∎
      [ trans x≡y y≡z ]                                      ∎)

  -- In an erased context there is an equivalence between equality of
  -- values and equality of "boxed" values.

  @0 ≡≃[]≡[] :
    {A : Type ℓ} {x y : A} →
    (x ≡ y) ≃ ([ x ] ≡ [ y ])
  ≡≃[]≡[] = Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = []-cong ∘ [_]→
        ; from = cong erased
        }
      ; right-inverse-of = λ eq →
          []-cong [ cong erased eq ]  ≡⟨ []-cong-[]≡cong-[] ⟩
          cong [_]→ (cong erased eq)  ≡⟨ _≃_.left-inverse-of []≡[]≃≡ _ ⟩∎
          eq                          ∎
      }
    ; left-inverse-of = λ eq →
        cong erased ([]-cong [ eq ])  ≡⟨ cong (cong erased) []-cong-[]≡cong-[] ⟩
        cong erased (cong [_]→ eq)    ≡⟨ _≃_.right-inverse-of []≡[]≃≡ _ ⟩∎
        eq                            ∎
    })

  -- The left-to-right and right-to-left directions of the equivalence
  -- are definitionally equal to certain functions.

  _ : _≃_.to (≡≃[]≡[] {x = x} {y = y}) ≡ []-cong ∘ [_]→
  _ = refl _

  @0 _ : _≃_.from (≡≃[]≡[] {x = x} {y = y}) ≡ cong erased
  _ = refl _

  ----------------------------------------------------------------------
  -- An isomorphism

  -- The following result is based on a result in Mishra-Linger's PhD
  -- thesis (see Section 5.4.4).

  -- Erased (Erased A) is isomorphic to Erased A.
  --
  -- If the --erased-matches flag is activated, then this lemma can be
  -- proved without the use of []-cong, see
  -- Erased.Erased-matches.Erased-Erased↔Erased.

  Erased-Erased↔Erased :
    {@0 A : Type ℓ} →
    Erased (Erased A) ↔ Erased A
  Erased-Erased↔Erased = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ x → [ erased (erased x) ]
        ; from = [_]→
        }
      ; right-inverse-of = λ { [ _ ] → refl _ }
      }
    ; left-inverse-of = λ { [ _ ] → []-cong [ Erased-η ] }
    }

  ----------------------------------------------------------------------
  -- Variants of subst, cong and the J rule that take erased equality
  -- proofs

  -- A variant of subst that takes an erased equality proof.

  substᴱ :
    {@0 A : Type ℓ} {@0 x y : A}
    (P : @0 A → Type p) → @0 x ≡ y → P x → P y
  substᴱ P eq = subst (λ ([ x ]) → P x) ([]-cong [ eq ])

  -- A variant of elim₁ that takes an erased equality proof.

  elim₁ᴱ :
    {@0 A : Type ℓ} {@0 x y : A}
    (P : {@0 x : A} → @0 x ≡ y → Type p) →
    P (refl y) →
    (@0 x≡y : x ≡ y) → P x≡y
  elim₁ᴱ {x} {y} P p x≡y =
    substᴱ
      (λ p → P (proj₂ p))
      (proj₂ (singleton-contractible y) (x , x≡y))
      p

  -- A variant of elim¹ that takes an erased equality proof.

  elim¹ᴱ :
    {@0 A : Type ℓ} {@0 x y : A}
    (P : {@0 y : A} → @0 x ≡ y → Type p) →
    P (refl x) →
    (@0 x≡y : x ≡ y) → P x≡y
  elim¹ᴱ {x} {y} P p x≡y =
    substᴱ
      (λ p → P (proj₂ p))
      (proj₂ (other-singleton-contractible x) (y , x≡y))
      p

  -- A variant of elim that takes an erased equality proof.

  elimᴱ :
    {@0 A : Type ℓ} {@0 x y : A}
    (P : {@0 x y : A} → @0 x ≡ y → Type p) →
    ((@0 x : A) → P (refl x)) →
    (@0 x≡y : x ≡ y) → P x≡y
  elimᴱ {y} P p = elim₁ᴱ P (p y)

  -- A variant of cong that takes an erased equality proof.

  congᴱ :
    {@0 A : Type ℓ} {@0 x y : A}
    (f : @0 A → B) → @0 x ≡ y → f x ≡ f y
  congᴱ f = elimᴱ (λ {x y} _ → f x ≡ f y) (λ x → refl (f x))

  -- A "computation rule" for substᴱ.

  substᴱ-refl :
    {@0 A : Type ℓ} {@0 x : A} {P : @0 A → Type p} {p : P x} →
    substᴱ P (refl x) p ≡ p
  substᴱ-refl {P} {p} =
    subst (λ ([ x ]) → P x) ([]-cong [ refl _ ]) p  ≡⟨ cong (flip (subst _) _) []-cong-[refl] ⟩
    subst (λ ([ x ]) → P x) (refl [ _ ]) p          ≡⟨ subst-refl _ _ ⟩∎
    p                                               ∎

  -- If all arguments are non-erased, then one can replace substᴱ with
  -- subst (if the first explicit argument is η-expanded).

  substᴱ≡subst :
    {P : @0 A → Type p} {p : P x} →
    substᴱ P eq p ≡ subst (λ x → P x) eq p
  substᴱ≡subst {eq} {P} {p} = elim¹
    (λ eq → substᴱ P eq p ≡ subst (λ x → P x) eq p)
    (substᴱ P (refl _) p           ≡⟨ substᴱ-refl ⟩
     p                             ≡⟨ sym $ subst-refl _ _ ⟩∎
     subst (λ x → P x) (refl _) p  ∎)
    eq

  -- A computation rule for elim₁ᴱ.

  elim₁ᴱ-refl :
    ∀ {@0 A : Type ℓ} {@0 y} →
    (P : {@0 x : A} → @0 x ≡ y → Type p)
    {p : P (refl y)} →
    elim₁ᴱ P p (refl y) ≡ p
  elim₁ᴱ-refl {y} P {p} =
    substᴱ
      (λ p → P (proj₂ p))
      (proj₂ (singleton-contractible y) (y , refl y))
      p                                                ≡⟨ congᴱ (λ q → substᴱ (λ p → P (proj₂ p)) q _)
                                                            (singleton-contractible-refl _) ⟩

    substᴱ (λ p → P (proj₂ p)) (refl (y , refl y)) p   ≡⟨ substᴱ-refl {P = λ p → P (proj₂ p)} ⟩∎

    p                                                  ∎

  -- If all arguments are non-erased, then one can replace elim₁ᴱ with
  -- elim₁ (if the first explicit argument is η-expanded).

  elim₁ᴱ≡elim₁ :
    {P : {@0 x : A} → @0 x ≡ y → Type p} {r : P (refl y)} →
    elim₁ᴱ P r eq ≡ elim₁ (λ x → P x) r eq
  elim₁ᴱ≡elim₁ {eq} {P} {r} = elim₁
    (λ eq → elim₁ᴱ P r eq ≡ elim₁ (λ x → P x) r eq)
    (elim₁ᴱ P r (refl _)           ≡⟨ elim₁ᴱ-refl P ⟩
     r                             ≡⟨ sym $ elim₁-refl _ _ ⟩∎
     elim₁ (λ x → P x) r (refl _)  ∎)
    eq

  -- A computation rule for elim¹ᴱ.

  elim¹ᴱ-refl :
    ∀ {@0 A : Type ℓ} {@0 x} →
    (P : {@0 y : A} → @0 x ≡ y → Type p)
    {p : P (refl x)} →
    elim¹ᴱ P p (refl x) ≡ p
  elim¹ᴱ-refl {x} P {p} =
    substᴱ
      (λ p → P (proj₂ p))
      (proj₂ (other-singleton-contractible x) (x , refl x))
      p                                                      ≡⟨ congᴱ (λ q → substᴱ (λ p → P (proj₂ p)) q _)
                                                                  (other-singleton-contractible-refl _) ⟩

    substᴱ (λ p → P (proj₂ p)) (refl (x , refl x)) p         ≡⟨ substᴱ-refl {P = λ p → P (proj₂ p)} ⟩∎

    p                                                        ∎

  -- If all arguments are non-erased, then one can replace elim¹ᴱ with
  -- elim¹ (if the first explicit argument is η-expanded).

  elim¹ᴱ≡elim¹ :
    {P : {@0 y : A} → @0 x ≡ y → Type p} {r : P (refl x)} →
    elim¹ᴱ P r eq ≡ elim¹ (λ x → P x) r eq
  elim¹ᴱ≡elim¹ {eq} {P} {r} = elim¹
    (λ eq → elim¹ᴱ P r eq ≡ elim¹ (λ x → P x) r eq)
    (elim¹ᴱ P r (refl _)           ≡⟨ elim¹ᴱ-refl P ⟩
     r                             ≡⟨ sym $ elim¹-refl _ _ ⟩∎
     elim¹ (λ x → P x) r (refl _)  ∎)
    eq

  -- A computation rule for elimᴱ.

  elimᴱ-refl :
    {@0 A : Type ℓ} {@0 x : A}
    (P : {@0 x y : A} → @0 x ≡ y → Type p)
    (r : (@0 x : A) → P (refl x)) →
    elimᴱ P r (refl x) ≡ r x
  elimᴱ-refl P _ = elim₁ᴱ-refl P

  -- If all arguments are non-erased, then one can replace elimᴱ with
  -- elim (if the first two explicit arguments are η-expanded).

  elimᴱ≡elim :
    {P : {@0 x y : A} → @0 x ≡ y → Type p}
    {r : ∀ (@0 x) → P (refl x)} →
    elimᴱ P r eq ≡ elim (λ x → P x) (λ x → r x) eq
  elimᴱ≡elim {eq} {P} {r} = elim
    (λ eq → elimᴱ P r eq ≡ elim (λ x → P x) (λ x → r x) eq)
    (λ x →
       elimᴱ P r (refl _)                     ≡⟨ elimᴱ-refl P r ⟩
       r x                                    ≡⟨ sym $ elim-refl _ _ ⟩∎
       elim (λ x → P x) (λ x → r x) (refl _)  ∎)
    eq

  -- A "computation rule" for congᴱ.

  congᴱ-refl :
    {@0 A : Type ℓ} {@0 x : A} {f : @0 A → B} →
    congᴱ f (refl x) ≡ refl (f x)
  congᴱ-refl {x} {f} =
    elimᴱ (λ {x y} _ → f x ≡ f y) (λ x → refl (f x)) (refl x)  ≡⟨ elimᴱ-refl (λ _ → _ ≡ _) (λ x → refl (f x)) ⟩∎
    refl (f x)                                                 ∎

  -- If all arguments are non-erased, then one can replace congᴱ with
  -- cong (if the first explicit argument is η-expanded).

  congᴱ≡cong :
    {f : @0 A → B} →
    congᴱ f eq ≡ cong (λ x → f x) eq
  congᴱ≡cong {eq} {f} = elim¹
    (λ eq → congᴱ f eq ≡ cong (λ x → f x) eq)
    (congᴱ f (refl _)           ≡⟨ congᴱ-refl ⟩
     refl _                     ≡⟨ sym $ cong-refl _ ⟩∎
     cong (λ x → f x) (refl _)  ∎)
    eq

  ----------------------------------------------------------------------
  -- Some equalities

  -- [_] can be "pushed" through subst.

  push-subst-[] :
    {@0 P : A → Type ℓ} {@0 p : P x} {x≡y : x ≡ y} →
    subst (λ x → Erased (P x)) x≡y [ p ] ≡ [ subst P x≡y p ]
  push-subst-[] {P} {p} = elim¹
    (λ x≡y → subst (λ x → Erased (P x)) x≡y [ p ] ≡ [ subst P x≡y p ])
    (subst (λ x → Erased (P x)) (refl _) [ p ]  ≡⟨ subst-refl _ _ ⟩
     [ p ]                                      ≡⟨ []-cong [ sym $ subst-refl _ _ ] ⟩∎
     [ subst P (refl _) p ]                     ∎)
    _

  -- []-cong kind of commutes with sym.

  []-cong-sym :
    {@0 A : Type ℓ} {@0 x y : A} {@0 p : x ≡ y} →
    []-cong [ sym p ] ≡ sym ([]-cong [ p ])
  []-cong-sym =
    elim¹ᴱ
      (λ p → []-cong [ sym p ] ≡ sym ([]-cong [ p ]))
      ([]-cong [ sym (refl _) ]  ≡⟨ cong []-cong $ []-cong [ sym-refl ] ⟩
       []-cong [ refl _ ]        ≡⟨ []-cong-[refl] ⟩
       refl [ _ ]                ≡⟨ sym sym-refl ⟩
       sym (refl [ _ ])          ≡⟨ cong sym $ sym $ []-cong-[refl] ⟩∎
       sym ([]-cong [ refl _ ])  ∎)
      _

  -- []-cong kind of commutes with trans.

  []-cong-trans :
    {@0 A : Type ℓ} {@0 x y z : A} {@0 p : x ≡ y} {@0 q : y ≡ z} →
    []-cong [ trans p q ] ≡ trans ([]-cong [ p ]) ([]-cong [ q ])
  []-cong-trans =
    elim¹ᴱ
      (λ p →
         ∀ (@0 q) →
         []-cong [ trans p q ] ≡ trans ([]-cong [ p ]) ([]-cong [ q ]))
      (λ q →
         []-cong [ trans (refl _) q ]                ≡⟨ cong []-cong $ []-cong [ trans-reflˡ _ ] ⟩
         []-cong [ q ]                               ≡⟨ sym $ trans-reflˡ _ ⟩
         trans (refl [ _ ]) ([]-cong [ q ])          ≡⟨ cong (flip trans _) $ sym []-cong-[refl] ⟩∎
         trans ([]-cong [ refl _ ]) ([]-cong [ q ])  ∎)
      _ _

  ----------------------------------------------------------------------
  -- All h-levels are closed under Erased

  -- Erased commutes with H-level′ n (assuming extensionality).

  Erased-H-level′↔H-level′ :
    {@0 A : Type ℓ} →
    ∀ n → Erased (H-level′ n A) ↝[ ℓ ∣ ℓ ] H-level′ n (Erased A)
  Erased-H-level′↔H-level′ {A} zero ext =
    Erased (H-level′ zero A)                                              ↔⟨⟩
    Erased (∃ λ (x : A) → (y : A) → x ≡ y)                                ↔⟨ Erased-Σ↔Σ ⟩
    (∃ λ (x : Erased A) → Erased ((y : A) → erased x ≡ y))                ↝⟨ (∃-cong λ _ → Erased-Π↔Π-Erased ext) ⟩
    (∃ λ (x : Erased A) → (y : Erased A) → Erased (erased x ≡ erased y))  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → from-isomorphism Erased-≡≃≡) ⟩
    (∃ λ (x : Erased A) → (y : Erased A) → x ≡ y)                         ↔⟨⟩
    H-level′ zero (Erased A)                                              □
  Erased-H-level′↔H-level′ {A} (suc n) ext =
    Erased (H-level′ (suc n) A)                                      ↔⟨⟩
    Erased ((x y : A) → H-level′ n (x ≡ y))                          ↝⟨ Erased-Π↔Π-Erased ext ⟩
    ((x : Erased A) → Erased ((y : A) → H-level′ n (erased x ≡ y)))  ↝⟨ (∀-cong ext λ _ → Erased-Π↔Π-Erased ext) ⟩
    ((x y : Erased A) → Erased (H-level′ n (erased x ≡ erased y)))   ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Erased-H-level′↔H-level′ n ext) ⟩
    ((x y : Erased A) → H-level′ n (Erased (erased x ≡ erased y)))   ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → H-level′-cong ext n Erased-≡≃≡) ⟩
    ((x y : Erased A) → H-level′ n (x ≡ y))                          ↔⟨⟩
    H-level′ (suc n) (Erased A)                                      □

  -- Erased commutes with H-level n (assuming extensionality).

  Erased-H-level↔H-level :
    {@0 A : Type ℓ} →
    ∀ n → Erased (H-level n A) ↝[ ℓ ∣ ℓ ] H-level n (Erased A)
  Erased-H-level↔H-level {A} n ext =
    Erased (H-level n A)   ↝⟨ Erased-cong? H-level↔H-level′ ext ⟩
    Erased (H-level′ n A)  ↝⟨ Erased-H-level′↔H-level′ n ext ⟩
    H-level′ n (Erased A)  ↝⟨ inverse-ext? H-level↔H-level′ ext ⟩□
    H-level n (Erased A)   □

  -- H-level n is closed under Erased.

  H-level-Erased :
    {@0 A : Type ℓ} →
    ∀ n → @0 H-level n A → H-level n (Erased A)
  H-level-Erased n h = Erased-H-level↔H-level n _ [ h ]

  ----------------------------------------------------------------------
  -- Some closure properties related to Is-proposition

  -- If A is a proposition, then Dec-Erased A is a proposition
  -- (assuming extensionality).

  Is-proposition-Dec-Erased :
    {@0 A : Type ℓ} →
    Extensionality ℓ lzero →
    @0 Is-proposition A →
    Is-proposition (Dec-Erased A)
  Is-proposition-Dec-Erased {A} ext p =
                                     $⟨ Dec-closure-propositional ext (H-level-Erased 1 p) ⟩
    Is-proposition (Dec (Erased A))  ↝⟨ H-level-cong _ 1 (inverse $ Dec-Erased↔Dec-Erased {k = equivalence} ext) ⦂ (_ → _) ⟩□
    Is-proposition (Dec-Erased A)    □

  -- If A is a set, then Decidable-erased-equality A is a proposition
  -- (assuming extensionality).

  Is-proposition-Decidable-erased-equality :
    {A : Type ℓ} →
    Extensionality ℓ ℓ →
    @0 Is-set A →
    Is-proposition (Decidable-erased-equality A)
  Is-proposition-Decidable-erased-equality ext s =
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Is-proposition-Dec-Erased (lower-extensionality lzero _ ext) s

  -- Erasedᴾ preserves Is-proposition.

  Is-proposition-Erasedᴾ :
    {@0 A : Type a} {@0 B : Type b} {@0 R : A → B → Type ℓ} →
    @0 (∀ {x y} → Is-proposition (R x y)) →
    ∀ {x y} → Is-proposition (Erasedᴾ R x y)
  Is-proposition-Erasedᴾ prop =
    H-level-Erased 1 prop

  ----------------------------------------------------------------------
  -- Some properties related to "Modalities in Homotopy Type Theory"
  -- by Rijke, Shulman and Spitters

  -- The function λ (A : Type ℓ) → Erased A is left exact.
  --
  -- See Theorem 3.1, case (i) in "Modalities in Homotopy Type Theory"
  -- for the definition of "left exact" used here. That definition is
  -- restricted to modalities. See
  -- Erased.Stability.[]-cong₁.Erased-modality for a proof showing
  -- that the function λ (A : Type ℓ) → Erased A is a modality,
  -- assuming that the []-cong axioms hold for ℓ.

  lex :
    {@0 A : Type ℓ} {@0 x y : A} →
    Contractible (Erased A) → Contractible (Erased (x ≡ y))
  lex {A} {x} {y} =
    Contractible (Erased A)        ↝⟨ _⇔_.from (Erased-H-level↔H-level 0 _) ⟩
    Erased (Contractible A)        ↝⟨ map (⇒≡ 0) ⟩
    Erased (Contractible (x ≡ y))  ↝⟨ Erased-H-level↔H-level 0 _ ⟩□
    Contractible (Erased (x ≡ y))  □

  -- The function λ (A : Type ℓ) → Erased A is left exact.

  lex-modality : Left-exact (λ (A : Type ℓ) → Erased A)
  lex-modality = lex

  ----------------------------------------------------------------------
  -- Erased "commutes" with various things

  -- Erased "commutes" with _⁻¹_.

  Erased-⁻¹ :
    {@0 A : Type a} {@0 B : Type ℓ} {@0 f : A → B} {@0 y : B} →
    Erased (f ⁻¹ y) ↔ map f ⁻¹ [ y ]
  Erased-⁻¹ {f} {y} =
    Erased (∃ λ x → f x ≡ y)             ↝⟨ Erased-Σ↔Σ ⟩
    (∃ λ x → Erased (f (erased x) ≡ y))  ↝⟨ (∃-cong λ _ → Erased-≡↔[]≡[]) ⟩□
    (∃ λ x → map f x ≡ [ y ])            □

  -- Erased "commutes" with Split-surjective.

  Erased-Split-surjective↔Split-surjective :
    {@0 A : Type a} {@0 B : Type ℓ} {@0 f : A → B} →
    Erased (Split-surjective f) ↝[ ℓ ∣ a ⊔ ℓ ]
    Split-surjective (map f)
  Erased-Split-surjective↔Split-surjective {f} ext =
    Erased (∀ y → ∃ λ x → f x ≡ y)                    ↝⟨ Erased-Π↔Π-Erased ext ⟩
    (∀ y → Erased (∃ λ x → f x ≡ erased y))           ↝⟨ (∀-cong ext λ _ → from-isomorphism Erased-Σ↔Σ) ⟩
    (∀ y → ∃ λ x → Erased (f (erased x) ≡ erased y))  ↝⟨ (∀-cong ext λ _ → ∃-cong λ _ → from-isomorphism Erased-≡≃≡) ⟩
    (∀ y → ∃ λ x → [ f (erased x) ] ≡ y)              ↔⟨⟩
    (∀ y → ∃ λ x → map f x ≡ y)                       □

  ----------------------------------------------------------------------
  -- Some lemmas related to whether [_]→ is injective or an embedding

  -- In erased contexts [_]→ is injective.
  --
  -- See also Erased.With-K.Injective-[].

  @0 Injective-[] :
    {A : Type ℓ} →
    Injective {A = A} [_]→
  Injective-[] = erased ∘ []-cong⁻¹

  -- If A is a proposition, then [_]→ {A = A} is an embedding.
  --
  -- See also Erased-Is-embedding-[] and Erased-Split-surjective-[]
  -- above as well as Very-stable→Is-embedding-[] and
  -- Very-stable→Split-surjective-[] in Erased.Stability and
  -- Injective-[] and Is-embedding-[] in Erased.With-K.

  Is-proposition→Is-embedding-[] :
    {A : Type ℓ} →
    Is-proposition A → Is-embedding [ A ∣_]→
  Is-proposition→Is-embedding-[] prop =
    _⇔_.to (Emb.Injective⇔Is-embedding
              set (H-level-Erased 2 set) [_]→)
      (λ _ → prop _ _)
    where
    set = mono₁ 1 prop

  ----------------------------------------------------------------------
  -- Variants of some functions from Equality.Decision-procedures

  -- A variant of Equality.Decision-procedures.Σ.set⇒dec⇒dec⇒dec.

  set⇒dec-erased⇒dec-erased⇒Σ-dec-erased :
    {@0 A : Type ℓ} {@0 P : A → Type p}
    {@0 x₁ x₂ : A} {@0 y₁ : P x₁} {@0 y₂ : P x₂} →
    @0 Is-set A →
    Dec-Erased (x₁ ≡ x₂) →
    (∀ (@0 eq) → Dec-Erased (substᴱ (λ x → P x) eq y₁ ≡ y₂)) →
    Dec-Erased ((x₁ , y₁) ≡ (x₂ , y₂))
  set⇒dec-erased⇒dec-erased⇒Σ-dec-erased _ (no [ x₁≢x₂ ]) _ =
    no [ x₁≢x₂ ∘ cong proj₁ ]
  set⇒dec-erased⇒dec-erased⇒Σ-dec-erased
    {P} {y₁} {y₂} set₁ (yes [ x₁≡x₂ ]) dec₂ =
    ⊎-map
      (map λ cast-y₁≡y₂ →
         Σ-≡,≡→≡ x₁≡x₂
           (subst (λ x → P x) x₁≡x₂ y₁   ≡⟨ sym substᴱ≡subst ⟩
            substᴱ (λ x → P x) x₁≡x₂ y₁  ≡⟨ cast-y₁≡y₂ ⟩∎
            y₂                           ∎))
      (map λ cast-y₁≢y₂ eq →                              $⟨ proj₂ (Σ-≡,≡←≡ eq) ⟩
         subst (λ x → P x) (proj₁ (Σ-≡,≡←≡ eq)) y₁ ≡ y₂   ↝⟨ ≡⇒↝ _ $ cong (_≡ _) $ sym substᴱ≡subst ⟩
         substᴱ (λ x → P x) (proj₁ (Σ-≡,≡←≡ eq)) y₁ ≡ y₂  ↝⟨ subst (λ p → substᴱ _ p _ ≡ _) (set₁ _ _) ⟩
         substᴱ (λ x → P x) x₁≡x₂ y₁ ≡ y₂                 ↝⟨ cast-y₁≢y₂ ⟩□
         ⊥                                                □)
      (dec₂ x₁≡x₂)

  -- A variant of Equality.Decision-procedures.Σ.decidable⇒dec⇒dec.

  decidable-erased⇒dec-erased⇒Σ-dec-erased :
    {@0 A : Type ℓ} {@0 P : A → Type p}
    {x₁ x₂ : A} {@0 y₁ : P x₁} {@0 y₂ : P x₂} →
    Decidable-erased-equality A →
    (∀ (@0 eq) → Dec-Erased (substᴱ (λ x → P x) eq y₁ ≡ y₂)) →
    Dec-Erased ((x₁ , y₁) ≡ (x₂ , y₂))
  decidable-erased⇒dec-erased⇒Σ-dec-erased dec =
    set⇒dec-erased⇒dec-erased⇒Σ-dec-erased
      (decidable⇒set
         (Decidable-erased-equality≃Decidable-equality _ dec))
      (dec _ _)

  -- A variant of Equality.Decision-procedures.Σ.Dec._≟_.

  decidable-erased⇒decidable-erased⇒Σ-decidable-erased :
    {@0 A : Type ℓ} {P : @0 A → Type p} →
    Decidable-erased-equality A →
    ({x : A} → Decidable-erased-equality (P x)) →
    Decidable-erased-equality (Σ A λ x → P x)
  decidable-erased⇒decidable-erased⇒Σ-decidable-erased
    {P} decA decP (_ , x₂) (_ , y₂) =
    decidable-erased⇒dec-erased⇒Σ-dec-erased
      decA
      (λ eq → decP (substᴱ P eq x₂) y₂)

------------------------------------------------------------------------
-- Some results that follow if the []-cong axioms hold for two
-- universe levels

module []-cong₂
  (ax₁ : []-cong-axiomatisation ℓ₁)
  (ax₂ : []-cong-axiomatisation ℓ₂)
  where

  private
    module BC₁ = []-cong₁ ax₁
    module BC₂ = []-cong₁ ax₂

  ----------------------------------------------------------------------
  -- Some equalities

  -- The function map (cong f) can be expressed in terms of
  -- cong (map f) (up to pointwise equality).

  map-cong≡cong-map :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 x y : A}
    {@0 f : A → B} {x≡y : Erased (x ≡ y)} →
    map (cong f) x≡y ≡ BC₂.[]-cong⁻¹ (cong (map f) (BC₁.[]-cong x≡y))
  map-cong≡cong-map {f} {x≡y = [ x≡y ]} =
    [ cong f x≡y ]                                        ≡⟨⟩
    [ cong (erased ∘ map f ∘ [_]→) x≡y ]                  ≡⟨ BC₂.[]-cong [ sym $ cong-∘ _ _ _ ] ⟩
    [ cong (erased ∘ map f) (cong [_]→ x≡y) ]             ≡⟨ BC₂.[]-cong [ cong (cong _) $ sym BC₁.[]-cong-[]≡cong-[] ] ⟩
    [ cong (erased ∘ map f) (BC₁.[]-cong [ x≡y ]) ]       ≡⟨ BC₂.[]-cong [ sym $ cong-∘ _ _ _ ] ⟩
    [ cong erased (cong (map f) (BC₁.[]-cong [ x≡y ])) ]  ≡⟨ sym BC₂.[]-cong⁻¹≡[cong-erased] ⟩∎
    BC₂.[]-cong⁻¹ (cong (map f) (BC₁.[]-cong [ x≡y ]))    ∎

  -- []-cong kind of commutes with cong.

  []-cong-cong :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂}
    {@0 f : A → B} {@0 x y : A} {@0 p : x ≡ y} →
    BC₂.[]-cong [ cong f p ] ≡ cong (map f) (BC₁.[]-cong [ p ])
  []-cong-cong {f} {x} =
    BC₁.elim¹ᴱ
      (λ p → BC₂.[]-cong [ cong f p ] ≡
             cong (map f) (BC₁.[]-cong [ p ]))
      (BC₂.[]-cong [ cong f (refl x) ]        ≡⟨ cong BC₂.[]-cong (BC₂.[]-cong [ cong-refl _ ]) ⟩
       BC₂.[]-cong [ refl (f x) ]             ≡⟨ BC₂.[]-cong-[refl] ⟩
       refl [ f x ]                           ≡⟨ sym $ cong-refl _ ⟩
       cong (map f) (refl [ x ])              ≡⟨ sym $ cong (cong (map f)) BC₁.[]-cong-[refl] ⟩∎
       cong (map f) (BC₁.[]-cong [ refl x ])  ∎)
      _

  ----------------------------------------------------------------------
  -- Erased "commutes" with various things

  -- Erased "commutes" with Has-quasi-inverse (up to _⇔_).

  Erased-Has-quasi-inverse⇔Has-quasi-inverse :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 f : A → B} →
    Erased (Has-quasi-inverse f) ⇔ Has-quasi-inverse (map f)
  Erased-Has-quasi-inverse⇔Has-quasi-inverse {f} = record
    { to = λ ([ f⁻¹ , f-f⁻¹ , f⁻¹-f ]) →
          map f⁻¹
        , (λ { [ _ ] → BC₂.[]-cong [ f-f⁻¹ _ ] })
        , (λ { [ _ ] → BC₁.[]-cong [ f⁻¹-f _ ] })
    ; from = λ (map-f⁻¹ , map-f-map-f⁻¹ , map-f⁻¹-map-f) →
        [ erased ∘ map-f⁻¹ ∘ [_]→
        , (λ x →
             f (erased (map-f⁻¹ [ x ]))                 ≡⟨⟩
             erased (map f [ erased (map-f⁻¹ [ x ]) ])  ≡⟨ cong (erased ∘ map f) (Erased-η {x = map-f⁻¹ _}) ⟩
             erased (map f (map-f⁻¹ [ x ]))             ≡⟨ cong erased (map-f-map-f⁻¹ _) ⟩
             erased [ x ]                               ≡⟨⟩
             x                                          ∎)
        , (λ x →
             erased (map-f⁻¹ [ f x ])        ≡⟨⟩
             erased (map-f⁻¹ (map f [ x ]))  ≡⟨ cong erased (map-f⁻¹-map-f [ _ ]) ⟩
             erased [ x ]                    ≡⟨⟩
             x                               ∎)
        ]
    }

  -- Erased "commutes" with Has-quasi-inverse (assuming function
  -- extensionality).
  --
  -- See also
  -- Erased.Level-2.[]-cong₂-⊔.Erased-Has-quasi-inverse↔Has-quasi-inverse.

  Erased-Has-quasi-inverse≃Has-quasi-inverse :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 f : A → B} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Erased (Has-quasi-inverse f) ≃ Has-quasi-inverse (map f)
  Erased-Has-quasi-inverse≃Has-quasi-inverse {f} ext =
    Erased (∃ λ g → (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x))            ↔⟨ Erased-Σ↔Σ ⟩

    (∃ λ g →
       Erased ((∀ x → f (erased g x) ≡ x) × (∀ x → erased g (f x) ≡ x)))  ↔⟨ (∃-cong λ _ → Erased-Σ↔Σ) ⟩

    (∃ λ g →
       Erased (∀ x → f (erased g x) ≡ x) ×
       Erased (∀ x → erased g (f x) ≡ x))                                 ↝⟨ Σ-cong (Erased-Π↔Π-Erased {k = equivalence} ext₂₁) (λ g →
                                                                             lemma₁ (erased g) ×-cong lemma₂ (erased g)) ⟩□
    (∃ λ g → (∀ x → map f (g x) ≡ x) × (∀ x → g (map f x) ≡ x))           □
    where
    ext₁₁ = lower-extensionality ℓ₂ ℓ₂ ext
    ext₂₁ = lower-extensionality ℓ₁ ℓ₂ ext
    ext₂₂ = lower-extensionality ℓ₁ ℓ₁ ext

    lemma₁ = λ (@0 g) →
      Erased (∀ x → f (g x) ≡ x)                    ↝⟨ Erased-Π↔Π-Erased ext₂₂ ⟩
      (∀ x → Erased (f (g (erased x)) ≡ erased x))  ↝⟨ (∀-cong ext₂₂ λ _ → BC₂.Erased-≡≃≡) ⟩
      (∀ x → [ f (g (erased x)) ] ≡ x)              ↔⟨⟩
      (∀ x → map (f ∘ g) x ≡ x)                     □

    lemma₂ = λ (@0 g) →
      Erased (∀ x → g (f x) ≡ x)                    ↝⟨ Erased-Π↔Π-Erased ext₁₁ ⟩
      (∀ x → Erased (g (f (erased x)) ≡ erased x))  ↝⟨ (∀-cong ext₁₁ λ _ → BC₁.Erased-≡≃≡) ⟩
      (∀ x → [ g (f (erased x)) ] ≡ x)              ↔⟨⟩
      (∀ x → map (g ∘ f) x ≡ x)                     □

  -- Erased "commutes" with HA.Proofs (assuming extensionality).

  Erased-Half-adjoint-proofs≃Half-adjoint-proofs :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 f : A → B} {@0 g : B → A} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    Erased (HA.Proofs f g) ≃ HA.Proofs (map f) (map g)
  Erased-Half-adjoint-proofs≃Half-adjoint-proofs {A} {B} {f} {g} ext =
    Erased (HA.Proofs f g)                                                ↔⟨⟩

    Erased
      (∃ λ (f-g : (x : B) → f (g x) ≡ x) →
       ∃ λ (g-f : (x : A) → g (f x) ≡ x) →
       (x : A) → cong f (g-f x) ≡ f-g (f x))                              ↔⟨ (∃-cong λ _ → Erased-Σ↔Σ) F.∘
                                                                             Erased-Σ↔Σ ⟩
    (∃ λ (f-g : Erased ((x : B) → f (g x) ≡ x)) →
     ∃ λ (g-f : Erased ((x : A) → g (f x) ≡ x)) →
     Erased ((x : A) → cong f (erased g-f x) ≡ erased f-g (f x)))         ↝⟨ (Σ-cong (Erased-Π↔Π-Erased {k = equivalence} ext₂₂) λ _ →
                                                                              Σ-cong (Erased-Π↔Π-Erased {k = equivalence} ext₁₁) λ _ →
                                                                              Erased-Π↔Π-Erased ext₁₂) ⟩
    (∃ λ (f-g : (x : Erased B) → Erased (f (g (erased x)) ≡ erased x)) →
     ∃ λ (g-f : (x : Erased A) → Erased (g (f (erased x)) ≡ erased x)) →
     (x : Erased A) →
     Erased (cong f (erased (g-f x)) ≡ erased (f-g (map f x))))           ↝⟨ (Σ-cong (∀-cong ext₂₂ λ _ → BC₂.Erased-≡≃≡) λ f-g →
                                                                              Σ-cong (∀-cong ext₁₁ λ _ → BC₁.Erased-≡≃≡) λ g-f →
                                                                              ∀-cong ext₁₂ λ { x@([ _ ]) →

      Erased (cong f (erased (g-f x)) ≡ erased (f-g (map f x)))                 ↝⟨ BC₂.Erased-≡≃≡ ⟩

      map (cong f) (g-f x) ≡ f-g (map f x)                                      ↝⟨ inverse $ Eq.≃-≡ BC₂.Erased-≡≃[]≡[] ⟩

      BC₂.[]-cong (map (cong f) (g-f x)) ≡ BC₂.[]-cong (f-g (map f x))          ↔⟨⟩

      BC₂.[]-cong [ cong f (erased (g-f x)) ] ≡
      BC₂.[]-cong (f-g (map f x))                                               ↝⟨ ≡⇒↝ _ $ cong (_≡ _) $
                                                                                   BC₁.elimᴱ
                                                                                     (λ eq →
                                                                                        BC₂.[]-cong [ cong f eq ] ≡
                                                                                        cong (map f) (BC₁.[]-cong [ eq ]))
                                                                                     (λ x →
        BC₂.[]-cong [ cong f (refl x) ]                                                 ≡⟨ cong BC₂.[]-cong $ BC₂.[]-cong [ cong-refl _ ] ⟩
        BC₂.[]-cong [ refl (f x) ]                                                      ≡⟨ BC₂.[]-cong-[refl] ⟩
        refl [ f x ]                                                                    ≡⟨ sym $ cong-refl _ ⟩
        cong (map f) (refl [ x ])                                                       ≡⟨ cong (cong (map f)) $ sym BC₁.[]-cong-[refl] ⟩∎
        cong (map f) (BC₁.[]-cong [ refl x ])                                           ∎)
                                                                                     _ ⟩
      cong (map f) (BC₁.[]-cong [ erased (g-f x) ]) ≡
      BC₂.[]-cong (f-g (map f x))                                               ↝⟨ ≡⇒↝ _ $ cong (_≡ _) $ cong (cong _) $ cong BC₁.[]-cong $ Erased-η ⟩

      cong (map f) (BC₁.[]-cong (g-f x)) ≡ BC₂.[]-cong (f-g (map f x))          □ }) ⟩

    (∃ λ (f-g : (x : Erased B) → map (f ∘ g) x ≡ x) →
     ∃ λ (g-f : (x : Erased A) → map (g ∘ f) x ≡ x) →
     (x : Erased A) → cong (map f) (g-f x) ≡ f-g (map f x))               ↔⟨⟩

    HA.Proofs (map f) (map g)                                             □
    where
    ext₁₁ = lower-extensionality ℓ₂ ℓ₂ ext
    ext₁₂ = lower-extensionality ℓ₂ ℓ₁ ext
    ext₂₂ = lower-extensionality ℓ₁ ℓ₁ ext

------------------------------------------------------------------------
-- Some results that follow if the []-cong axioms hold for the maximum
-- of two universe levels (as well as for the two universe levels)

-- It is possible to instantiate the first two arguments using the
-- third and lower-[]-cong-axiomatisation, but this is not what is
-- done in the module []-cong below.

module []-cong₂-⊔
  (ax₁ : []-cong-axiomatisation ℓ₁)
  (ax₂ : []-cong-axiomatisation ℓ₂)
  (ax  : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
  where

  private
    module EC  = Erased-cong ax ax
    module BC₁ = []-cong₁ ax₁
    module BC₂ = []-cong₁ ax₂
    module BC  = []-cong₁ ax

  ----------------------------------------------------------------------
  -- A property related to "Modalities in Homotopy Type Theory" by
  -- Rijke, Shulman and Spitters

  -- A function f is Erased-connected in the sense of Rijke et al.
  -- exactly when there is an erased proof showing that f is an
  -- equivalence (assuming extensionality).
  --
  -- See also Erased-Is-equivalence↔Is-equivalence below.

  Erased-connected↔Erased-Is-equivalence :
    {@0 A : Type ℓ₁} {B : Type ℓ₂} {@0 f : A → B} →
    (∀ y → Contractible (Erased (f ⁻¹ y))) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ]
    Erased (Is-equivalence f)
  Erased-connected↔Erased-Is-equivalence {f} {k} ext =
    (∀ y → Contractible (Erased (f ⁻¹ y)))  ↝⟨ (∀-cong ext′ λ _ → inverse-ext? (BC.Erased-H-level↔H-level 0) ext) ⟩
    (∀ y → Erased (Contractible (f ⁻¹ y)))  ↝⟨ inverse-ext? Erased-Π↔Π ext′ ⟩
    Erased (∀ y → Contractible (f ⁻¹ y))    ↔⟨⟩
    Erased (CP.Is-equivalence f)            ↝⟨ inverse-ext? (λ ext → EC.Erased-cong? Is-equivalence≃Is-equivalence-CP ext) ext ⟩□
    Erased (Is-equivalence f)               □
    where
    ext′ = lower-extensionality? k ℓ₁ lzero ext

  ----------------------------------------------------------------------
  -- Erased "commutes" with various things

  -- Erased "commutes" with Is-equivalence.

  Erased-Is-equivalence↔Is-equivalence :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 f : A → B} →
    Erased (Is-equivalence f) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ]
    Is-equivalence (map f)
  Erased-Is-equivalence↔Is-equivalence {f} {k} ext =
    Erased (Is-equivalence f)                      ↝⟨ EC.Erased-cong? Is-equivalence≃Is-equivalence-CP ext ⟩
    Erased (∀ x → Contractible (f ⁻¹ x))           ↝⟨ Erased-Π↔Π-Erased ext′ ⟩
    (∀ x → Erased (Contractible (f ⁻¹ erased x)))  ↝⟨ (∀-cong ext′ λ _ → BC.Erased-H-level↔H-level 0 ext) ⟩
    (∀ x → Contractible (Erased (f ⁻¹ erased x)))  ↝⟨ (∀-cong ext′ λ { [ _ ] → H-level-cong ext 0 BC₂.Erased-⁻¹ }) ⟩
    (∀ x → Contractible (map f ⁻¹ x))              ↝⟨ inverse-ext? Is-equivalence≃Is-equivalence-CP ext ⟩□
    Is-equivalence (map f)                         □
    where
    ext′ = lower-extensionality? k ℓ₁ lzero ext

  -- Erased "commutes" with Injective.

  Erased-Injective↔Injective :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 f : A → B} →
    Erased (Injective f) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ] Injective (map f)
  Erased-Injective↔Injective {f} {k} ext =
    Erased (∀ {x y} → f x ≡ f y → x ≡ y)                          ↔⟨ EC.Erased-cong-↔ Bijection.implicit-Π↔Π ⟩

    Erased (∀ x {y} → f x ≡ f y → x ≡ y)                          ↝⟨ EC.Erased-cong?
                                                                       (λ {k} ext →
                                                                          ∀-cong (lower-extensionality? k ℓ₂ lzero ext) λ _ →
                                                                          from-isomorphism Bijection.implicit-Π↔Π)
                                                                       ext ⟩

    Erased (∀ x y → f x ≡ f y → x ≡ y)                            ↝⟨ Erased-Π↔Π-Erased ext₁₁₂ ⟩

    (∀ x → Erased (∀ y → f (erased x) ≡ f y → erased x ≡ y))      ↝⟨ (∀-cong ext₁₁₂ λ _ → Erased-Π↔Π-Erased ext₁₁₂) ⟩

    (∀ x y →
     Erased (f (erased x) ≡ f (erased y) → erased x ≡ erased y))  ↝⟨ (∀-cong ext₁₁₂ λ _ → ∀-cong ext₁₁₂ λ _ → Erased-Π↔Π-Erased ext₂₁) ⟩

    (∀ x y →
     Erased (f (erased x) ≡ f (erased y)) →
     Erased (erased x ≡ erased y))                                ↝⟨ (∀-cong ext₁₁₂ λ { [ _ ] → ∀-cong ext₁₁₂ λ { [ _ ] →
                                                                      generalise-ext?-sym
                                                                        (λ ext →
                                                                           →-cong ext
                                                                             (from-isomorphism BC₂.Erased-≡↔[]≡[])
                                                                             (from-isomorphism BC₁.Erased-≡↔[]≡[]))
                                                                        ext₂₁ }}) ⟩

    (∀ x y → [ f (erased x) ] ≡ [ f (erased y) ] → x ≡ y)         ↝⟨ (∀-cong ext₁₁₂ λ _ → from-isomorphism $ inverse Bijection.implicit-Π↔Π) ⟩

    (∀ x {y} → [ f (erased x) ] ≡ [ f (erased y) ] → x ≡ y)       ↔⟨ inverse Bijection.implicit-Π↔Π ⟩□

    (∀ {x y} → [ f (erased x) ] ≡ [ f (erased y) ] → x ≡ y)       □
    where
    ext₁₁₂ = lower-extensionality? k ℓ₂ lzero ext
    ext₂₁  = lower-extensionality? k ℓ₁ ℓ₂ ext

  -- Erased "commutes" with Is-embedding.

  Erased-Is-embedding↔Is-embedding :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 f : A → B} →
    Erased (Is-embedding f) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ] Is-embedding (map f)
  Erased-Is-embedding↔Is-embedding {f} {k} ext =
    Erased (∀ x y → Is-equivalence (cong f))                         ↝⟨ Erased-Π↔Π-Erased ext′ ⟩

    (∀ x → Erased (∀ y → Is-equivalence (cong f)))                   ↝⟨ (∀-cong ext′ λ _ → Erased-Π↔Π-Erased ext′) ⟩

    (∀ x y → Erased (Is-equivalence (cong f)))                       ↝⟨ (∀-cong ext′ λ _ → ∀-cong ext′ λ _ →
                                                                         Erased-Is-equivalence↔Is-equivalence ext) ⟩

    (∀ x y → Is-equivalence (map (cong f)))                          ↝⟨ (∀-cong ext′ λ x → ∀-cong ext′ λ y →
                                                                         Is-equivalence-cong ext λ _ → []-cong₂.map-cong≡cong-map ax₁ ax₂) ⟩

    (∀ x y →
       Is-equivalence (BC₂.[]-cong⁻¹ ∘ cong (map f) ∘ BC₁.[]-cong))  ↝⟨ (∀-cong ext′ λ { [ _ ] → ∀-cong ext′ λ { [ _ ] →
                                                                         inverse-ext?
                                                                           (Is-equivalence≃Is-equivalence-∘ʳ BC₁.[]-cong-equivalence)
                                                                           ext }}) ⟩

    (∀ x y → Is-equivalence (BC₂.[]-cong⁻¹ ∘ cong (map f)))          ↝⟨ (∀-cong ext′ λ _ → ∀-cong ext′ λ _ →
                                                                         inverse-ext?
                                                                           (Is-equivalence≃Is-equivalence-∘ˡ
                                                                              (_≃_.is-equivalence $ from-isomorphism $ inverse
                                                                               BC₂.Erased-≡↔[]≡[]))
                                                                           ext) ⟩□
    (∀ x y → Is-equivalence (cong (map f)))                          □
    where
    ext′ = lower-extensionality? k ℓ₂ lzero ext

  ----------------------------------------------------------------------
  -- Erased commutes with various type formers

  -- Erased commutes with _⇔_ (assuming function extensionality).

  Erased-⇔↔⇔ :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
    Erased (A ⇔ B) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ] (Erased A ⇔ Erased B)
  Erased-⇔↔⇔ {A} {B} {k} ext =
    Erased (A ⇔ B)                                 ↔⟨ EC.Erased-cong-↔ ⇔↔→×→ ⟩
    Erased ((A → B) × (B → A))                     ↔⟨ Erased-Σ↔Σ ⟩
    Erased (A → B) × Erased (B → A)                ↝⟨ Erased-Π↔Π-Erased ext₁₂ ×-cong Erased-Π↔Π-Erased ext₂₁ ⟩
    (Erased A → Erased B) × (Erased B → Erased A)  ↔⟨ inverse ⇔↔→×→ ⟩□
    (Erased A ⇔ Erased B)                          □
    where
    ext₁₂ = lower-extensionality? k ℓ₂ ℓ₁ ext
    ext₂₁ = lower-extensionality? k ℓ₁ ℓ₂ ext

  -- Erased commutes with _↣_.

  Erased-cong-↣ :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
    @0 A ↣ B → Erased A ↣ Erased B
  Erased-cong-↣ A↣B = record
    { to        = map (_↣_.to A↣B)
    ; injective = Erased-Injective↔Injective _ [ _↣_.injective A↣B ]
    }

------------------------------------------------------------------------
-- Some results that follow if the []-cong axioms hold for all
-- universe levels

module []-cong (ax : ∀ {ℓ} → []-cong-axiomatisation ℓ) where

  private
    open module EC {ℓ₁ ℓ₂} =
      Erased-cong (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂})
      public
    open module BC₁ {ℓ} =
      []-cong₁ (ax {ℓ = ℓ})
      public
    open module BC₂ {ℓ₁ ℓ₂} = []-cong₂ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂})
      public
    open module BC₂-⊔ {ℓ₁ ℓ₂} =
      []-cong₂-⊔ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) (ax {ℓ = ℓ₁ ⊔ ℓ₂})
      public

------------------------------------------------------------------------
-- Some results that were proved assuming extensionality and also that
-- one or more instances of the []-cong axioms can be implemented,
-- reproved without the latter assumptions

module Extensionality where

  -- Erased commutes with H-level′ n (assuming extensionality).

  Erased-H-level′≃H-level′ :
    {@0 A : Type a} →
    Extensionality a a →
    ∀ n → Erased (H-level′ n A) ≃ H-level′ n (Erased A)
  Erased-H-level′≃H-level′ ext n =
    []-cong₁.Erased-H-level′↔H-level′
      (Extensionality→[]-cong-axiomatisation ext)
      n
      ext

  -- Erased commutes with H-level n (assuming extensionality).

  Erased-H-level≃H-level :
    {@0 A : Type a} →
    Extensionality a a →
    ∀ n → Erased (H-level n A) ≃ H-level n (Erased A)
  Erased-H-level≃H-level ext n =
    []-cong₁.Erased-H-level↔H-level
      (Extensionality→[]-cong-axiomatisation ext)
      n
      ext

  -- If A is a set, then Decidable-erased-equality A is a proposition
  -- (assuming extensionality).

  Is-proposition-Decidable-erased-equality′ :
    {A : Type a} →
    Extensionality a a →
    @0 Is-set A →
    Is-proposition (Decidable-erased-equality A)
  Is-proposition-Decidable-erased-equality′ ext =
    []-cong₁.Is-proposition-Decidable-erased-equality
      (Extensionality→[]-cong-axiomatisation ext)
      ext

  -- Erased "commutes" with Split-surjective.

  Erased-Split-surjective≃Split-surjective :
    {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
    Extensionality b (a ⊔ b) →
    Erased (Split-surjective f) ≃ Split-surjective (map f)
  Erased-Split-surjective≃Split-surjective {a} ext =
    []-cong₁.Erased-Split-surjective↔Split-surjective
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality lzero a ext))
      ext

  -- A function f is Erased-connected in the sense of Rijke et al.
  -- exactly when there is an erased proof showing that f is an
  -- equivalence (assuming extensionality).

  Erased-connected≃Erased-Is-equivalence :
    {@0 A : Type a} {B : Type b} {@0 f : A → B} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    (∀ y → Contractible (Erased (f ⁻¹ y))) ≃ Erased (Is-equivalence f)
  Erased-connected≃Erased-Is-equivalence {a} {b} ext =
    []-cong₂-⊔.Erased-connected↔Erased-Is-equivalence
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality b b ext))
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality a a ext))
      (Extensionality→[]-cong-axiomatisation ext)
      ext

  -- Erased "commutes" with Is-equivalence (assuming extensionality).

  Erased-Is-equivalence≃Is-equivalence :
    {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    Erased (Is-equivalence f) ≃ Is-equivalence (map f)
  Erased-Is-equivalence≃Is-equivalence {a} {b} ext =
    []-cong₂-⊔.Erased-Is-equivalence↔Is-equivalence
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality b b ext))
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality a a ext))
      (Extensionality→[]-cong-axiomatisation ext)
      ext

  -- Erased "commutes" with Has-quasi-inverse (assuming
  -- extensionality).

  Erased-Has-quasi-inverse≃Has-quasi-inverse :
    {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    Erased (Has-quasi-inverse f) ≃ Has-quasi-inverse (map f)
  Erased-Has-quasi-inverse≃Has-quasi-inverse {a} {b} ext =
    []-cong₂.Erased-Has-quasi-inverse≃Has-quasi-inverse
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality b b ext))
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality a a ext))
      ext

  -- Erased "commutes" with Injective (assuming extensionality).

  Erased-Injective≃Injective :
    {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    Erased (Injective f) ≃ Injective (map f)
  Erased-Injective≃Injective {a} {b} ext =
    []-cong₂-⊔.Erased-Injective↔Injective
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality b b ext))
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality a a ext))
      (Extensionality→[]-cong-axiomatisation ext)
      ext

  -- Erased "commutes" with Is-embedding (assuming extensionality).

  Erased-Is-embedding≃Is-embedding :
    {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    Erased (Is-embedding f) ≃ Is-embedding (map f)
  Erased-Is-embedding≃Is-embedding {a} {b} ext =
    []-cong₂-⊔.Erased-Is-embedding↔Is-embedding
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality b b ext))
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality a a ext))
      (Extensionality→[]-cong-axiomatisation ext)
      ext

  -- Erased commutes with _⇔_ (assuming function extensionality).

  Erased-⇔≃⇔ :
    {@0 A : Type a} {@0 B : Type b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    Erased (A ⇔ B) ≃ (Erased A ⇔ Erased B)
  Erased-⇔≃⇔ {a} {b} ext =
    []-cong₂-⊔.Erased-⇔↔⇔
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality b b ext))
      (Extensionality→[]-cong-axiomatisation
         (lower-extensionality a a ext))
      (Extensionality→[]-cong-axiomatisation ext)
      ext

------------------------------------------------------------------------
-- Some lemmas related to []-cong-axiomatisation

-- The []-cong axioms can be instantiated in erased contexts.

@0 erased-instance-of-[]-cong-axiomatisation :
  []-cong-axiomatisation a
erased-instance-of-[]-cong-axiomatisation
  .[]-cong-axiomatisation.[]-cong =
  cong [_]→ ∘ erased
erased-instance-of-[]-cong-axiomatisation
  .[]-cong-axiomatisation.[]-cong-[refl] {x} =
  cong [_]→ (erased [ refl x ])  ≡⟨⟩
  cong [_]→ (refl x)             ≡⟨ cong-refl _ ⟩∎
  refl [ x ]                     ∎

-- If the []-cong axioms can be implemented for a certain universe
-- level, then they can also be implemented for all smaller universe
-- levels.

lower-[]-cong-axiomatisation :
  ∀ a′ → []-cong-axiomatisation (a ⊔ a′) → []-cong-axiomatisation a
lower-[]-cong-axiomatisation {a} a′ ax = λ where
    .[]-cong-axiomatisation.[]-cong        → []-cong′
    .[]-cong-axiomatisation.[]-cong-[refl] → []-cong′-[refl]
  where
  open []-cong₁ ax

  lemma :
    {@0 A : Type a} {@0 x y : A} →
    Erased (lift {ℓ = a′} x ≡ lift y) ≃ ([ x ] ≡ [ y ])
  lemma {x} {y} =
    Erased (lift {ℓ = a′} x ≡ lift y)  ↝⟨ Erased-≡≃[]≡[] ⟩
    [ lift x ] ≡ [ lift y ]            ↝⟨ inverse $ Eq.≃-≡ (Eq.↔→≃ (map lower) (map lift) (λ _ → Erased-η) (λ _ → Erased-η)) ⟩□
    [ x ] ≡ [ y ]                      □

  []-cong′ :
    {@0 A : Type a} {@0 x y : A} →
    Erased (x ≡ y) → [ x ] ≡ [ y ]
  []-cong′ {x} {y} =
    Erased (x ≡ y)                     ↝⟨ map (cong lift) ⟩
    Erased (lift {ℓ = a′} x ≡ lift y)  ↔⟨ lemma ⟩□
    [ x ] ≡ [ y ]                      □

  []-cong′-[refl] :
    {@0 A : Type a} {@0 x : A} →
    []-cong′ [ refl x ] ≡ refl [ x ]
  []-cong′-[refl] {x} =
    cong (map lower) ([]-cong [ cong lift (refl x) ])  ≡⟨ cong (cong (map lower) ∘ []-cong) $ []-cong [ cong-refl _ ] ⟩
    cong (map lower) ([]-cong [ refl (lift x) ])       ≡⟨ cong (cong (map lower)) []-cong-[refl] ⟩
    cong (map lower) (refl [ lift x ])                 ≡⟨ cong-refl _ ⟩∎
    refl [ x ]                                         ∎

-- Any two implementations of []-cong are pointwise equal.

[]-cong-unique :
  {@0 A : Type a} {@0 x y : A} {x≡y : Erased (x ≡ y)}
  (ax₁ ax₂ : []-cong-axiomatisation a) →
  []-cong-axiomatisation.[]-cong ax₁ x≡y ≡
  []-cong-axiomatisation.[]-cong ax₂ x≡y
[]-cong-unique {x} {x≡y = [ x≡y ]} ax₁ ax₂ =
  BC₁.elim¹ᴱ
    (λ x≡y → BC₁.[]-cong [ x≡y ] ≡ BC₂.[]-cong [ x≡y ])
    (BC₁.[]-cong [ refl x ]  ≡⟨ BC₁.[]-cong-[refl] ⟩
     refl [ x ]              ≡⟨ sym BC₂.[]-cong-[refl] ⟩∎
     BC₂.[]-cong [ refl x ]  ∎)
    x≡y
  where
  module BC₁ = []-cong₁ ax₁
  module BC₂ = []-cong₁ ax₂

private

  -- A lemma used below.

  ≃Erased²/≡ :
    {@0 A : Type a} {P : {@0 x y : A} → @0 x ≡ y → Type p} →
    ((@0 x y : A) (([ x≡y ]) : Erased (x ≡ y)) → P x≡y) ↝[ a ∣ a ⊔ p ]
    ((([ _ , _ , x≡y ]) : Erased (A ²/≡)) → P x≡y)
  ≃Erased²/≡ {a} = generalise-ext?
    (record
       { to   = λ f ([ _ , _ , x≡y ]) → f _ _ [ x≡y ]
       ; from = λ f (@0 _ _) ([ x≡y ]) → f [ _ , _ , x≡y ]
       })
    (λ ext →
       let ext′ = lower-extensionality lzero a ext in
         (λ _ → apply-ext ext′ λ { [ _ ] → refl _ })
       , (λ _ →
            apply-extᴱ ext λ _ →
            apply-extᴱ ext λ _ →
            apply-ext ext′ λ { [ _ ] →
            refl _ }))

  -- A variant of ≃Erased²/≡.

  ≃Erased²/≡′ :
    {@0 A : Type a} {P : {@0 x y : A} → @0 x ≡ y → Type p} →
    ((@0 x y : A) (@0 x≡y : x ≡ y) → P x≡y) ↝[ a ∣ a ⊔ p ]
    ((([ _ , _ , x≡y ]) : Erased (A ²/≡)) → P x≡y)
  ≃Erased²/≡′ {a} {A} {P} {k} ext =
    ((@0 x y : A) (@0 x≡y : x ≡ y) → P x≡y)              ↝⟨ (∀ᴱ-cong ext λ _ → ∀ᴱ-cong ext λ _ →
                                                             inverse-ext? Π-Erased≃Π0 ext′) ⟩
    ((@0 x y : A) (([ x≡y ]) : Erased (x ≡ y)) → P x≡y)  ↝⟨ ≃Erased²/≡ {P = P} ext ⟩□
    ((([ _ , _ , x≡y ]) : Erased (A ²/≡)) → P x≡y)       □
    where
    ext′ = lower-extensionality? k lzero a ext

-- []-cong-axiomatisation a can be expressed in a different way
-- (assuming function extensionality).

[]-cong-axiomatisation≃ :
  Extensionality (lsuc a) a →
  []-cong-axiomatisation a ≃
  ((([ A ]) : Erased (Type a)) →
   ∃ λ (c : (([ x , y , _ ]) : Erased (A ²/≡)) → [ x ] ≡ [ y ]) →
     (([ x ]) : Erased A) → c [ x , x , refl x ] ≡ refl [ x ])
[]-cong-axiomatisation≃ {a} ext =
  []-cong-axiomatisation a                                         ↔⟨ Eq.↔→≃
                                                                        (λ { (record { []-cong        = c
                                                                                     ; []-cong-[refl] = r
                                                                                     })
                                                                             _ → (λ _ _ → c) , (λ _ → r) })
                                                                        (λ f → record
                                                                           { []-cong        = f _ .proj₁ _ _
                                                                           ; []-cong-[refl] = f _ .proj₂ _
                                                                           })
                                                                        refl
                                                                        refl ⟩
  ((@0 A : Type a) →
   Σ ((@0 x y : A) → Erased (x ≡ y) → [ x ] ≡ [ y ]) λ c →
     (@0 x : A) → c x x [ refl x ] ≡ refl [ x ])                   ↝⟨ (∀-cong ext λ _ →
                                                                       Σ-cong (≃Erased²/≡ {k = equivalence} ext′) λ _ →
                                                                       inverse (Π-Erased≃Π0 ext′)) F.∘
                                                                      inverse (Π-Erased≃Π0 ext) ⟩□
  ((([ A ]) : Erased (Type a)) →
   ∃ λ (c : (([ x , y , _ ]) : Erased (A ²/≡)) → [ x ] ≡ [ y ]) →
     (([ x ]) : Erased A) → c [ x , x , refl x ] ≡ refl [ x ])     □
  where
  ext′ : Extensionality a a
  ext′ = lower-extensionality _ lzero ext

-- The type []-cong-axiomatisation a is propositional (assuming
-- extensionality).
--
-- The proof is based on a proof due to Nicolai Kraus that shows that
-- "J + its computation rule" is contractible, see
-- Equality.Instances-related.Equality-with-J-contractible.

[]-cong-axiomatisation-propositional :
  Extensionality (lsuc a) a →
  Is-proposition ([]-cong-axiomatisation a)
[]-cong-axiomatisation-propositional {a} ext =
  [inhabited⇒contractible]⇒propositional λ ax →
  let module BC = []-cong₁ ax
      module EC = Erased-cong ax ax
  in
  _⇔_.from contractible⇔↔⊤
    ([]-cong-axiomatisation a                                         ↔⟨ []-cong-axiomatisation≃ ext ⟩

     ((([ A ]) : Erased (Type a)) →
      ∃ λ (c : (([ x , y , _ ]) : Erased (A ²/≡)) → [ x ] ≡ [ y ]) →
        (([ x ]) : Erased A) → c [ x , x , refl x ] ≡ refl [ x ])     ↝⟨ (∀-cong ext λ _ →
                                                                          Σ-cong
                                                                            (inverse $
                                                                             Π-cong ext′ (EC.Erased-cong-↔ (inverse U.-²/≡↔-)) λ _ →
                                                                             inverse [erased]≡[erased]≃≡) λ _ →
                                                                          ∀-cong ext′ λ { [ _ ] →
                                                                          F.id }) ⟩
     ((([ A ]) : Erased (Type a)) →
      ∃ λ (c : ((x : Erased A) → x ≡ x)) →
        (x : Erased A) → c x ≡ refl x)                                ↝⟨ (∀-cong ext λ _ → inverse
                                                                          ΠΣ-comm) ⟩
     ((([ A ]) : Erased (Type a)) (x : Erased A) →
      ∃ λ (c : x ≡ x) → c ≡ refl x)                                   ↔⟨⟩

     ((([ A ]) : Erased (Type a)) (x : Erased A) →
      Singleton (refl x))                                             ↝⟨ _⇔_.to contractible⇔↔⊤ $
                                                                           (Π-closure ext  0 λ _ →
                                                                            Π-closure ext′ 0 λ _ →
                                                                            singleton-contractible _) ⟩□
     ⊤                                                                □)
  where
  ext′ : Extensionality a a
  ext′ = lower-extensionality _ lzero ext

-- The type []-cong-axiomatisation a is contractible (assuming
-- extensionality).

[]-cong-axiomatisation-contractible :
  Extensionality (lsuc a) a →
  Contractible ([]-cong-axiomatisation a)
[]-cong-axiomatisation-contractible {a} ext =
  propositional⇒inhabited⇒contractible
    ([]-cong-axiomatisation-propositional ext)
    (Extensionality→[]-cong-axiomatisation
       (lower-extensionality _ lzero ext))

------------------------------------------------------------------------
-- An alternative to []-cong-axiomatisation

-- An axiomatisation of "the inverse of []-cong".

[]-cong⁻¹-axiomatisation : (ℓ : Level) → Type (lsuc ℓ)
[]-cong⁻¹-axiomatisation ℓ =
  {A : Type ℓ} {x y : A} →
  Is-equivalence (λ (eq : [ x ] ≡ [ y ]) → [ cong erased eq ])

-- The type []-cong⁻¹-axiomatisation ℓ is propositional (assuming
-- function extensionality).

[]-cong⁻¹-axiomatisation-propositional :
  Extensionality (lsuc ℓ) ℓ →
  Is-proposition ([]-cong⁻¹-axiomatisation ℓ)
[]-cong⁻¹-axiomatisation-propositional {ℓ} ext =
  implicit-Π-closure ext 1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  Is-equivalence-propositional ext′
  where
  ext′ : Extensionality ℓ ℓ
  ext′ = lower-extensionality _ lzero ext

-- The type []-cong-axiomatisation ℓ is equivalent to
-- []-cong⁻¹-axiomatisation ℓ (assuming extensionality).

[]-cong-axiomatisation≃[]-cong⁻¹-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ ℓ ] []-cong⁻¹-axiomatisation ℓ
[]-cong-axiomatisation≃[]-cong⁻¹-axiomatisation =
  generalise-ext?-prop
    (record
       { to   = to
       ; from = []-cong-axiomatisation′→[]-cong-axiomatisation ∘ from
       })
    []-cong-axiomatisation-propositional
    []-cong⁻¹-axiomatisation-propositional
  where
  to : []-cong-axiomatisation ℓ → []-cong⁻¹-axiomatisation ℓ
  to ax {x} {y} =                                                 $⟨ _≃_.is-equivalence $ inverse Erased-≡≃[]≡[] ⟩
    Is-equivalence ([]-cong⁻¹ {x = x} {y = y})                    →⟨ (Is-equivalence-cong _ λ _ → []-cong⁻¹≡[cong-erased]) ⟩□
    Is-equivalence (λ (eq : [ x ] ≡ [ y ]) → [ cong erased eq ])  □
    where
    open []-cong₁ ax

  module _ (ax : []-cong⁻¹-axiomatisation ℓ) where

    Erased-≡≃[]≡[] :
      {A : Type ℓ} {x y : A} →
      Erased (x ≡ y) ≃ ([ x ] ≡ [ y ])
    Erased-≡≃[]≡[] = inverse Eq.⟨ _ , ax ⟩

    []-cong :
      {A : Type ℓ} {x y : A} →
      Erased (x ≡ y) → [ x ] ≡ [ y ]
    []-cong = _≃_.to Erased-≡≃[]≡[]

    []-cong⁻¹ :
      {A : Type ℓ} {x y : A} →
      [ x ] ≡ [ y ] → Erased (x ≡ y)
    []-cong⁻¹ eq = [ cong erased eq ]

    []-cong₀ :
      {@0 A : Type ℓ} {@0 x y : A} →
      Erased (x ≡ y) → [ x ] ≡ [ y ]
    []-cong₀ {A} {x} {y} =
      Erased (x ≡ y)          →⟨ map (cong [_]→) ⟩
      Erased ([ x ] ≡ [ y ])  →⟨ []-cong ⟩
      [ [ x ] ] ≡ [ [ y ] ]   →⟨ cong (map erased) ⟩□
      [ x ] ≡ [ y ]           □

    from : []-cong-axiomatisation′ ℓ
    from .[]-cong-axiomatisation′.[]-cong =
      []-cong
    from .[]-cong-axiomatisation′.[]-cong-[refl] {x} =
      _≃_.from-to Erased-≡≃[]≡[]
        ([]-cong⁻¹ (refl [ x ])        ≡⟨⟩
         [ cong erased (refl [ x ]) ]  ≡⟨ []-cong₀ [ cong-refl _ ] ⟩∎
         [ refl x ]                    ∎)

------------------------------------------------------------------------
-- Some lemmas related to ≡→Erased[erased≡erased]-axiomatisation

-- The type []-cong⁻¹-axiomatisation ℓ is equivalent to
-- ≡→Erased[erased≡erased]-axiomatisation ℓ (assuming function
-- extensionality).

[]-cong⁻¹-axiomatisation≃≡→Erased[erased≡erased]-axiomatisation :
  []-cong⁻¹-axiomatisation ℓ ↝[ lsuc ℓ ∣ ℓ ]
  ≡→Erased[erased≡erased]-axiomatisation ℓ
[]-cong⁻¹-axiomatisation≃≡→Erased[erased≡erased]-axiomatisation {ℓ} =
  generalise-ext?-prop
    (record { to = to; from = from })
    []-cong⁻¹-axiomatisation-propositional
    ≡→Erased[erased≡erased]-axiomatisation-propositional
  where
  from :
    ≡→Erased[erased≡erased]-axiomatisation ℓ →
    []-cong⁻¹-axiomatisation ℓ
  from ax {x} {y} =                                                 $⟨ ax ⟩

    Is-equivalence
      (≡→Erased[erased≡erased] ⦂ ([ x ] ≡ [ y ] → Erased (x ≡ y)))  →⟨ id ⟩□

    Is-equivalence (λ (eq : [ x ] ≡ [ y ]) → [ cong erased eq ])    □

  to :
    []-cong⁻¹-axiomatisation ℓ →
    ≡→Erased[erased≡erased]-axiomatisation ℓ
  to ax {x = x@([ _ ])} {y = y@([ _ ])} =                     $⟨ _≃_.is-equivalence $ inverse Erased-≡≃[]≡[] ⟩
    Is-equivalence ([]-cong⁻¹ {x = erased x} {y = erased y})  →⟨ (Is-equivalence-cong _ λ _ → []-cong⁻¹≡[cong-erased]) ⟩□
    Is-equivalence (≡→Erased[erased≡erased] {x = x} {y = y})  □
    where
    open []-cong₁
      (_⇔_.from ([]-cong-axiomatisation≃[]-cong⁻¹-axiomatisation _) ax)

-- The type []-cong-axiomatisation ℓ is equivalent to
-- ≡→Erased[erased≡erased]-axiomatisation ℓ (assuming function
-- extensionality).

[]-cong-axiomatisation≃≡→Erased[erased≡erased]-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ ℓ ]
  ≡→Erased[erased≡erased]-axiomatisation ℓ
[]-cong-axiomatisation≃≡→Erased[erased≡erased]-axiomatisation {ℓ} ext =
  []-cong-axiomatisation ℓ                  ↝⟨ []-cong-axiomatisation≃[]-cong⁻¹-axiomatisation ext ⟩
  []-cong⁻¹-axiomatisation ℓ                ↝⟨ []-cong⁻¹-axiomatisation≃≡→Erased[erased≡erased]-axiomatisation ext ⟩□
  ≡→Erased[erased≡erased]-axiomatisation ℓ  □

------------------------------------------------------------------------
-- Another alternative to []-cong-axiomatisation

-- An axiomatisation of substᴱ, restricted to a fixed universe, along
-- with its computation rule.

Substᴱ-axiomatisation : (ℓ : Level) → Type (lsuc ℓ)
Substᴱ-axiomatisation ℓ =
  ∃ λ (substᴱ :
         {@0 A : Type ℓ} {@0 x y : A}
         (P : @0 A → Type ℓ) → @0 x ≡ y → P x → P y) →
    {@0 A : Type ℓ} {@0 x : A} {P : @0 A → Type ℓ} {p : P x} →
    substᴱ P (refl x) p ≡ p

private

  -- The type []-cong-axiomatisation ℓ is logically equivalent to
  -- Substᴱ-axiomatisation ℓ.

  []-cong-axiomatisation⇔Substᴱ-axiomatisation :
    []-cong-axiomatisation ℓ ⇔ Substᴱ-axiomatisation ℓ
  []-cong-axiomatisation⇔Substᴱ-axiomatisation {ℓ} =
    record { to = to; from = from }
    where
    to : []-cong-axiomatisation ℓ → Substᴱ-axiomatisation ℓ
    to ax = []-cong₁.substᴱ ax , []-cong₁.substᴱ-refl ax

    from : Substᴱ-axiomatisation ℓ → []-cong-axiomatisation ℓ
    from (substᴱ , substᴱ-refl) = λ where
        .[]-cong-axiomatisation.[]-cong →
          []-cong
        .[]-cong-axiomatisation.[]-cong-[refl] →
          substᴱ-refl
      where
      []-cong :
        {@0 A : Type ℓ} {@0 x y : A} →
        Erased (x ≡ y) → [ x ] ≡ [ y ]
      []-cong {x} ([ x≡y ]) =
        substᴱ (λ y → [ x ] ≡ [ y ]) x≡y (refl [ x ])

-- The type Substᴱ-axiomatisation ℓ is propositional (assuming
-- extensionality).
--
-- The proof is based on a proof due to Nicolai Kraus that shows that
-- "J + its computation rule" is contractible, see
-- Equality.Instances-related.Equality-with-J-contractible.

Substᴱ-axiomatisation-propositional :
  Extensionality (lsuc ℓ) (lsuc ℓ) →
  Is-proposition (Substᴱ-axiomatisation ℓ)
Substᴱ-axiomatisation-propositional {ℓ} ext =
  [inhabited⇒contractible]⇒propositional λ ax →
  let ax′ = _⇔_.from []-cong-axiomatisation⇔Substᴱ-axiomatisation ax

      module EC = Erased-cong ax′ ax′
  in
  _⇔_.from contractible⇔↔⊤
    (Substᴱ-axiomatisation ℓ                                              ↔⟨ Eq.↔→≃
                                                                               (λ (substᴱ , substᴱ-refl) _ P →
                                                                                    (λ _ _ x≡y → substᴱ P x≡y)
                                                                                  , (λ _ _ → substᴱ-refl))
                                                                               (λ hyp →
                                                                                    (λ _ → hyp _ _ .proj₁ _ _)
                                                                                  , hyp _ _ .proj₂ _ _)
                                                                               refl
                                                                               refl ⟩
     ((@0 A : Type ℓ) (P : @0 A → Type ℓ) →
      Σ ((@0 x y : A) → @0 x ≡ y → P x → P y) λ s →
        (@0 x : A) (p : P x) → s x x (refl x) p ≡ p)                      ↝⟨ (∀-cong ext λ _ →
                                                                              Π-cong ext′ (inverse $ Π-Erased≃Π0 {k = equivalence} ext″) λ _ →
                                                                              Σ-cong (≃Erased²/≡′ {k = equivalence} ext‴) λ _ →
                                                                              inverse (Π-Erased≃Π0 ext‴)) F.∘
                                                                             inverse (Π-Erased≃Π0 ext) ⟩
     ((([ A ]) : Erased (Type ℓ)) (P : Erased A → Type ℓ) →
      ∃ λ (s : (([ x , y , _ ]) : Erased (A ²/≡)) → P [ x ] → P [ y ]) →
        (([ x ]) : Erased A) (p : P [ x ]) → s [ x , x , refl x ] p ≡ p)
                                                                          ↝⟨ (∀-cong ext λ _ → ∀-cong ext′ λ _ →
                                                                              Σ-cong
                                                                                (inverse $
                                                                                 Π-cong ext‴ (EC.Erased-cong-↔ (inverse U.-²/≡↔-)) λ _ →
                                                                                 Bijection.id)
                                                                                (λ _ → Bijection.id)) ⟩
     ((([ A ]) : Erased (Type ℓ)) (P : Erased A → Type ℓ) →
      ∃ λ (s : (([ x ]) : Erased A) → P [ x ] → P [ x ]) →
        (([ x ]) : Erased A) (p : P [ x ]) → s [ x ] p ≡ p)               ↝⟨ (∀-cong ext λ _ → ∀-cong ext′ λ P → inverse $
                                                                              (∃-cong λ _ → ∀-cong ext‴ λ { [ _ ] → F.id }) F.∘
                                                                              ΠΣ-comm F.∘
                                                                              (∀-cong ext‴ λ _ → ΠΣ-comm)) ⟩
     ((([ A ]) : Erased (Type ℓ)) (P : Erased A → Type ℓ)
      (([ x ]) : Erased A) (p : P [ x ]) →
      ∃ λ (p′ : P [ x ]) → p′ ≡ p)                                        ↝⟨ (∀-cong ext λ _ → ∀-cong ext′ λ _ → ∀-cong ext‴ λ { [ _ ] →
                                                                              F.id }) ⟩
     ((([ A ]) : Erased (Type ℓ)) (P : Erased A → Type ℓ)
      (x : Erased A) (p : P x) → ∃ λ (p′ : P x) → p′ ≡ p)                 ↔⟨⟩

     ((([ A ]) : Erased (Type ℓ)) (P : Erased A → Type ℓ)
      (x : Erased A) (p : P x) → Singleton p)                             ↝⟨ (_⇔_.to contractible⇔↔⊤ $
                                                                              Π-closure ext  0 λ _ →
                                                                              Π-closure ext′ 0 λ _ →
                                                                              Π-closure ext‴ 0 λ _ →
                                                                              Π-closure ext‴ 0 λ _ →
                                                                              singleton-contractible _) ⟩□
     ⊤                                                                    □)
  where
  ext′ : Extensionality (lsuc ℓ) ℓ
  ext′ = lower-extensionality lzero _ ext

  ext″ : Extensionality ℓ (lsuc ℓ)
  ext″ = lower-extensionality _ lzero ext

  ext‴ : Extensionality ℓ ℓ
  ext‴ = lower-extensionality _ _ ext

-- The type []-cong-axiomatisation ℓ is equivalent to
-- Substᴱ-axiomatisation ℓ (assuming extensionality).

[]-cong-axiomatisation≃Substᴱ-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ] Substᴱ-axiomatisation ℓ
[]-cong-axiomatisation≃Substᴱ-axiomatisation {ℓ} =
  generalise-ext?-prop
    []-cong-axiomatisation⇔Substᴱ-axiomatisation
    ([]-cong-axiomatisation-propositional ∘
     lower-extensionality lzero _)
    Substᴱ-axiomatisation-propositional

------------------------------------------------------------------------
-- Yet another alternative to []-cong-axiomatisation

-- An axiomatisation of elimᴱ, restricted to a fixed universe, along
-- with its computation rule.

Elimᴱ-axiomatisation : (ℓ : Level) → Type (lsuc ℓ)
Elimᴱ-axiomatisation ℓ =
  ∃ λ (elimᴱ :
         {@0 A : Type ℓ} {@0 x y : A}
         (P : {@0 x y : A} → @0 x ≡ y → Type ℓ) →
         ((@0 x : A) → P (refl x)) →
         (@0 x≡y : x ≡ y) → P x≡y) →
    {@0 A : Type ℓ} {@0 x : A} {P : {@0 x y : A} → @0 x ≡ y → Type ℓ}
    (r : (@0 x : A) → P (refl x)) →
    elimᴱ P r (refl x) ≡ r x

private

  -- The type Substᴱ-axiomatisation ℓ is logically equivalent to
  -- Elimᴱ-axiomatisation ℓ.

  Substᴱ-axiomatisation⇔Elimᴱ-axiomatisation :
    Substᴱ-axiomatisation ℓ ⇔ Elimᴱ-axiomatisation ℓ
  Substᴱ-axiomatisation⇔Elimᴱ-axiomatisation {ℓ} =
    record { to = to; from = from }
    where
    to : Substᴱ-axiomatisation ℓ → Elimᴱ-axiomatisation ℓ
    to ax = elimᴱ , λ {_ _} {P = P} → elimᴱ-refl P
      where
      open
        []-cong₁
          (_⇔_.from []-cong-axiomatisation⇔Substᴱ-axiomatisation ax)

    from : Elimᴱ-axiomatisation ℓ → Substᴱ-axiomatisation ℓ
    from (elimᴱ , elimᴱ-refl) =
        (λ P x≡y p →
           elimᴱ (λ {x = x} {y = y} _ → P x → P y) (λ _ → id) x≡y p)
      , (λ {_ _ _ p} → cong (_$ p) $ elimᴱ-refl _)

-- The type Elimᴱ-axiomatisation ℓ is propositional (assuming
-- extensionality).
--
-- The proof is based on a proof due to Nicolai Kraus that shows that
-- "J + its computation rule" is contractible, see
-- Equality.Instances-related.Equality-with-J-contractible.

Elimᴱ-axiomatisation-propositional :
  Extensionality (lsuc ℓ) (lsuc ℓ) →
  Is-proposition (Elimᴱ-axiomatisation ℓ)
Elimᴱ-axiomatisation-propositional {ℓ} ext =
  [inhabited⇒contractible]⇒propositional λ ax →
  let ax′ = _⇔_.from []-cong-axiomatisation⇔Substᴱ-axiomatisation $
            _⇔_.from Substᴱ-axiomatisation⇔Elimᴱ-axiomatisation ax

      module EC = Erased-cong ax′ ax′
  in
  _⇔_.from contractible⇔↔⊤
    (Elimᴱ-axiomatisation ℓ                                       ↔⟨ Eq.↔→≃
                                                                       (λ (elimᴱ , elimᴱ-refl) _ _ r →
                                                                            (λ _ _ → elimᴱ _ r)
                                                                          , (λ _ → elimᴱ-refl _))
                                                                       (λ hyp →
                                                                            (λ _ r → hyp _ _ r .proj₁ _ _)
                                                                          , (λ _ → hyp _ _ _ .proj₂ _))
                                                                       refl
                                                                       refl ⟩
     ((@0 A : Type ℓ) (P : (@0 x y : A) → @0 x ≡ y → Type ℓ)
      (r : (@0 x : A) → P x x (refl x)) →
      ∃ λ (e : (@0 x y : A) (@0 x≡y : x ≡ y) → P x y x≡y) →
        (@0 x : A) → e x x (refl x) ≡ r x)                        ↝⟨ (∀-cong ext λ _ →
                                                                      Π-cong ext′ (≃Erased²/≡′ {k = equivalence} ext″) λ _ →
                                                                      Π-cong ext‴ (inverse (Π-Erased≃Π0 {k = equivalence} ext‴)) λ _ →
                                                                      Σ-cong (≃Erased²/≡′ {k = equivalence} ext‴) λ _ →
                                                                      inverse (Π-Erased≃Π0 ext‴)) F.∘
                                                                     inverse (Π-Erased≃Π0 ext) ⟩
     ((([ A ]) : Erased (Type ℓ))
      (P : Erased (A ²/≡) → Type ℓ)
      (r : (([ x ]) : Erased A) → P [ x , x , refl x ]) →
      ∃ λ (e : (x : Erased (A ²/≡)) → P x) →
        ((([ x ]) : Erased A) → e [ x , x , refl x ] ≡ r [ x ]))  ↝⟨ (∀-cong ext λ _ →
                                                                      Π-cong {k₁ = bijection} ext′
                                                                        (→-cong₁ ext″ (EC.Erased-cong-↔ U.-²/≡↔-)) λ _ →
                                                                      ∀-cong ext‴ λ _ →
                                                                      Σ-cong
                                                                        (inverse $
                                                                         Π-cong ext‴ (EC.Erased-cong-↔ (inverse U.-²/≡↔-)) λ _ →
                                                                         Bijection.id) λ _ →
                                                                      ∀-cong ext‴ λ { [ _ ] →
                                                                      Bijection.id }) ⟩
     ((([ A ]) : Erased (Type ℓ))
      (P : Erased A → Type ℓ)
      (r : (x : Erased A) → P x) →
      ∃ λ (e : (x : Erased A) → P x) →
        (x : Erased A) → e x ≡ r x)                               ↝⟨ (∀-cong ext λ _ → ∀-cong ext′ λ _ → ∀-cong ext‴ λ _ → inverse
                                                                      ΠΣ-comm) ⟩
     ((([ A ]) : Erased (Type ℓ))
      (P : Erased A → Type ℓ)
      (r : (x : Erased A) → P x)
      (x : Erased A) →
      ∃ λ (p : P x) → p ≡ r x)                                    ↝⟨ (_⇔_.to contractible⇔↔⊤ $
                                                                      Π-closure ext  0 λ _ →
                                                                      Π-closure ext′ 0 λ _ →
                                                                      Π-closure ext‴ 0 λ _ →
                                                                      Π-closure ext‴ 0 λ _ →
                                                                      singleton-contractible _) ⟩□
     ⊤                                                            □)
  where
  ext′ : Extensionality (lsuc ℓ) ℓ
  ext′ = lower-extensionality lzero _ ext

  ext″ : Extensionality ℓ (lsuc ℓ)
  ext″ = lower-extensionality _ lzero ext

  ext‴ : Extensionality ℓ ℓ
  ext‴ = lower-extensionality _ _ ext

-- The type Substᴱ-axiomatisation ℓ is equivalent to
-- Elimᴱ-axiomatisation ℓ (assuming extensionality).

Substᴱ-axiomatisation≃Elimᴱ-axiomatisation :
  Substᴱ-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ] Elimᴱ-axiomatisation ℓ
Substᴱ-axiomatisation≃Elimᴱ-axiomatisation =
  generalise-ext?-prop
    Substᴱ-axiomatisation⇔Elimᴱ-axiomatisation
    Substᴱ-axiomatisation-propositional
    Elimᴱ-axiomatisation-propositional

-- The type []-cong-axiomatisation ℓ is equivalent to
-- Elimᴱ-axiomatisation ℓ (assuming extensionality).

[]-cong-axiomatisation≃Elimᴱ-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ] Elimᴱ-axiomatisation ℓ
[]-cong-axiomatisation≃Elimᴱ-axiomatisation {ℓ} ext =
  []-cong-axiomatisation ℓ  ↝⟨ []-cong-axiomatisation≃Substᴱ-axiomatisation ext ⟩
  Substᴱ-axiomatisation ℓ   ↝⟨ Substᴱ-axiomatisation≃Elimᴱ-axiomatisation ext ⟩□
  Elimᴱ-axiomatisation ℓ    □

------------------------------------------------------------------------
-- One more alternative to []-cong-axiomatisation

-- An axiomatisation of elim¹ᴱ, restricted to a fixed universe, along
-- with its computation rule.

Elim¹ᴱ-axiomatisation : (ℓ : Level) → Type (lsuc ℓ)
Elim¹ᴱ-axiomatisation ℓ =
  ∃ λ (elim¹ᴱ :
         {@0 A : Type ℓ} {@0 x y : A}
         (P : {@0 y : A} → @0 x ≡ y → Type ℓ) →
         P (refl x) →
         (@0 x≡y : x ≡ y) → P x≡y) →
    {@0 A : Type ℓ} {@0 x : A}
    (P : {@0 y : A} → @0 x ≡ y → Type ℓ) {r : P (refl x)} →
    elim¹ᴱ P r (refl x) ≡ r

private

  -- The type Substᴱ-axiomatisation ℓ is logically equivalent to
  -- Elim¹ᴱ-axiomatisation ℓ.

  Substᴱ-axiomatisation⇔Elim¹ᴱ-axiomatisation :
    Substᴱ-axiomatisation ℓ ⇔ Elim¹ᴱ-axiomatisation ℓ
  Substᴱ-axiomatisation⇔Elim¹ᴱ-axiomatisation {ℓ} =
    record { to = to; from = from }
    where
    to : Substᴱ-axiomatisation ℓ → Elim¹ᴱ-axiomatisation ℓ
    to ax = elim¹ᴱ , elim¹ᴱ-refl
      where
      open
        []-cong₁
          (_⇔_.from []-cong-axiomatisation⇔Substᴱ-axiomatisation ax)

    from : Elim¹ᴱ-axiomatisation ℓ → Substᴱ-axiomatisation ℓ
    from (elim¹ᴱ , elim¹ᴱ-refl) =
        (λ {_} {x = x} P x≡y p →
           elim¹ᴱ (λ {y = y} _ → P x → P y) id x≡y p)
      , (λ {_ _ _} {p = p} → cong (_$ p) (elim¹ᴱ-refl _))

-- The type Elim¹ᴱ-axiomatisation ℓ is propositional (assuming
-- extensionality).
--
-- The proof is based on a proof due to Nicolai Kraus that shows that
-- "J + its computation rule" is contractible, see
-- Equality.Instances-related.Equality-with-J-contractible.

Elim¹ᴱ-axiomatisation-propositional :
  Extensionality (lsuc ℓ) (lsuc ℓ) →
  Is-proposition (Elim¹ᴱ-axiomatisation ℓ)
Elim¹ᴱ-axiomatisation-propositional {ℓ} ext =
  [inhabited⇒contractible]⇒propositional λ ax →
  let ax′ = _⇔_.from []-cong-axiomatisation⇔Substᴱ-axiomatisation $
            _⇔_.from Substᴱ-axiomatisation⇔Elim¹ᴱ-axiomatisation ax

      module EC = Erased-cong ax′ ax′
  in
  _⇔_.from contractible⇔↔⊤
    (Elim¹ᴱ-axiomatisation ℓ                                              ↔⟨ Eq.↔→≃
                                                                               (λ (elim¹ᴱ , elim¹ᴱ-refl) _ _ P r →
                                                                                    (λ _ → elim¹ᴱ (P _) _)
                                                                                  , elim¹ᴱ-refl _)
                                                                               (λ hyp →
                                                                                    (λ P r → hyp _ _ (λ _ → P) r .proj₁ _)
                                                                                  , (λ _ → hyp _ _ _ _ .proj₂))
                                                                               refl
                                                                               refl ⟩
     ((@0 A : Type ℓ) (@0 x : A) (P : (@0 y : A) → @0 x ≡ y → Type ℓ)
      (r : P x (refl x)) →
      ∃ λ (e : (@0 y : A) (@0 x≡y : x ≡ y) → P y x≡y) →
        e x (refl x) ≡ r)                                                 ↝⟨ (∀ᴱ-cong ext λ _ → ∀ᴱ-cong ext″ λ _ →
                                                                              ∀-cong ext′ λ _ → ∀-cong ext‴ λ _ →
                                                                              Σ-cong
                                                                                (Eq.↔→≃
                                                                                   (λ e ([ y ]) ([ x≡y ]) → e y x≡y)
                                                                                   (λ e (@0 y x≡y) → e [ y ] [ x≡y ])
                                                                                   (λ _ →
                                                                                      apply-ext ext‴ λ { [ _ ] →
                                                                                      apply-ext ext‴ λ { [ _ ] →
                                                                                      refl _ }})
                                                                                   refl) λ _ →
                                                                              F.id) ⟩
     ((@0 A : Type ℓ) (@0 x : A) (P : (@0 y : A) → @0 x ≡ y → Type ℓ)
      (r : P x (refl x)) →
      ∃ λ (e : (([ y ]) : Erased A) (([ x≡y ]) : Erased (x ≡ y)) →
               P y x≡y) →
        e [ x ] [ refl x ] ≡ r)                                           ↝⟨ (∀ᴱ-cong ext λ _ → ∀ᴱ-cong ext″ λ _ →
                                                                              ∀-cong ext′ λ _ → ∀-cong ext‴ λ _ →
                                                                              Σ-cong
                                                                                ((Π-cong-contra ext‴ Erased-Σ↔Σ λ { ([ _ ]) →
                                                                                  F.id }) F.∘
                                                                                 inverse currying) λ _ →
                                                                              F.id) ⟩
     ((@0 A : Type ℓ) (@0 x : A) (P : (@0 y : A) → @0 x ≡ y → Type ℓ)
      (r : P x (refl x)) →
      ∃ λ (e : (([ y , x≡y ]) : Erased (Other-singleton x)) → P y x≡y) →
        e ([ x , refl x ]) ≡ r)                                           ↝⟨ (∀ᴱ-cong ext λ _ → ∀ᴱ-cong ext″ λ x →
                                                                              ∀-cong ext′ λ _ → ∀-cong ext‴ λ _ →
                                                                              Σ-cong
                                                                                (drop-⊤-left-Π {k = equivalence} ext‴ (
       Erased (Other-singleton x)                                                  ↝⟨ EC.Erased-cong-↔
                                                                                        (inverse Bijection.↑↔ F.∘
                                                                                         _⇔_.to contractible⇔↔⊤ (other-singleton-contractible _)) ⟩
       Erased (↑ _ ⊤)                                                              ↝⟨ Erased-↑↔↑ ⟩
       ↑ _ (Erased ⊤)                                                              ↝⟨ Bijection.↑↔ ⟩
       Erased ⊤                                                                    ↝⟨ Erased-⊤↔⊤ ⟩□
       ⊤                                                                           □)) λ _ →
                                                                              F.id) ⟩
     ((@0 A : Type ℓ) (@0 x : A) (P : (@0 y : A) → @0 x ≡ y → Type ℓ)
      (r : P x (refl x)) → Singleton r)                                   ↝⟨ (_⇔_.to contractible⇔↔⊤ $
                                                                              Πᴱ-closure ext 0 λ _ →
                                                                              Πᴱ-closure ext″ 0 λ _ →
                                                                              Π-closure ext′ 0 λ _ →
                                                                              Π-closure ext‴ 0 λ _ →
                                                                              singleton-contractible _) ⟩□
     ⊤                                                                    □)
  where
  ext′ : Extensionality (lsuc ℓ) ℓ
  ext′ = lower-extensionality lzero _ ext

  ext″ : Extensionality ℓ (lsuc ℓ)
  ext″ = lower-extensionality _ lzero ext

  ext‴ : Extensionality ℓ ℓ
  ext‴ = lower-extensionality _ _ ext

-- The type Substᴱ-axiomatisation ℓ is equivalent to
-- Elim¹ᴱ-axiomatisation ℓ (assuming extensionality).

Substᴱ-axiomatisation≃Elim¹ᴱ-axiomatisation :
  Substᴱ-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ] Elim¹ᴱ-axiomatisation ℓ
Substᴱ-axiomatisation≃Elim¹ᴱ-axiomatisation =
  generalise-ext?-prop
    Substᴱ-axiomatisation⇔Elim¹ᴱ-axiomatisation
    Substᴱ-axiomatisation-propositional
    Elim¹ᴱ-axiomatisation-propositional

-- The type []-cong-axiomatisation ℓ is equivalent to
-- Elim¹ᴱ-axiomatisation ℓ (assuming extensionality).

[]-cong-axiomatisation≃Elim¹ᴱ-axiomatisation :
  []-cong-axiomatisation ℓ ↝[ lsuc ℓ ∣ lsuc ℓ ] Elim¹ᴱ-axiomatisation ℓ
[]-cong-axiomatisation≃Elim¹ᴱ-axiomatisation {ℓ} ext =
  []-cong-axiomatisation ℓ  ↝⟨ []-cong-axiomatisation≃Substᴱ-axiomatisation ext ⟩
  Substᴱ-axiomatisation ℓ   ↝⟨ Substᴱ-axiomatisation≃Elim¹ᴱ-axiomatisation ext ⟩□
  Elim¹ᴱ-axiomatisation ℓ   □
