------------------------------------------------------------------------
-- Pullbacks
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- This module is partly based on code written by Guillame Brunerie in
-- a fork of the Coq HoTT library
-- (https://github.com/guillaumebrunerie/HoTT/), and partly based on
-- the Wikipedia page about pullbacks
-- (https://en.wikipedia.org/wiki/Pullback_(category_theory)).

open import Equality

module Pullback {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Function-universe eq as F hiding (_∘_)
open import H-level.Closure eq

private
  variable
    a a₁ a₂ b b₁ b₂ l m r : Level
    A A₁ A₂ B             : Type a
    C f                   : A
    k                     : Kind

-- Cospans.

record Cospan l r m : Type (lsuc (l ⊔ r ⊔ m)) where
  field
    {Left}   : Type l
    {Right}  : Type r
    {Middle} : Type m
    left     : Left  → Middle
    right    : Right → Middle

-- Cones over cospans. The "corner opposite to" the Middle type is a
-- parameter, not a field, so a more accurate name might be something
-- like Cone-over-cospan-with-given-opposite-corner.

record Cone (A : Type a) (C : Cospan l r m) :
            Type (a ⊔ l ⊔ r ⊔ m) where
  field
    left     : A → Cospan.Left C
    right    : A → Cospan.Right C
    commutes : ∀ x → Cospan.left C (left x) ≡ Cospan.right C (right x)

-- The type of cones can also be written using Σ-types.

Cone↔Σ :
  Cone A C
    ↔
  ∃ λ ((f , g) : (A → Cospan.Left C) × (A → Cospan.Right C)) →
    ∀ x → Cospan.left C (f x) ≡ Cospan.right C (g x)
Cone↔Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → (Cone.left f , Cone.right f) , Cone.commutes f
      ; from = λ ((l , r) , c) →
                 record { left = l; right = r; commutes = c }
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- Equality between cones is isomorphic to certain kinds of triples.

Cone-≡-↔-Σ :
  {C : Cospan l m r} {c d : Cone A C} →
  c ≡ d
    ↔
  (∃ λ (p : Cone.left  c ≡ Cone.left  d) →
   ∃ λ (q : Cone.right c ≡ Cone.right d) →
     subst
       (λ (f , g) →
          ∀ x → Cospan.left C (f x) ≡ Cospan.right C (g x))
       (cong₂ _,_ p q)
       (Cone.commutes c) ≡
     Cone.commutes d)
Cone-≡-↔-Σ {C} {c} {d} =
  c ≡ d                                                      ↔⟨ inverse $ Eq.≃-≡ (Eq.↔⇒≃ Cone↔Σ) ⟩

  ((Cone.left c , Cone.right c) , Cone.commutes c) ≡
  ((Cone.left d , Cone.right d) , Cone.commutes d)           ↝⟨ inverse $ Bijection.Σ-≡,≡↔≡ ⟩

  (∃ λ (p : (Cone.left c , Cone.right c) ≡
            (Cone.left d , Cone.right d)) →
     subst
       (λ (f , g) →
          ∀ x → Cospan.left C (f x) ≡ Cospan.right C (g x))
       p
       (Cone.commutes c) ≡
     Cone.commutes d)                                        ↝⟨ (Σ-cong-contra ≡×≡↔≡ λ _ → F.id) ⟩

  (∃ λ (p : Cone.left  c ≡ Cone.left  d ×
            Cone.right c ≡ Cone.right d) →
     subst
       (λ (f , g) →
          ∀ x → Cospan.left C (f x) ≡ Cospan.right C (g x))
       (uncurry (cong₂ _,_) p)
       (Cone.commutes c) ≡
     Cone.commutes d)                                        ↝⟨ inverse Σ-assoc ⟩□

  (∃ λ (p : Cone.left  c ≡ Cone.left  d) →
   ∃ λ (q : Cone.right c ≡ Cone.right d) →
     subst
       (λ (f , g) →
          ∀ x → Cospan.left C (f x) ≡ Cospan.right C (g x))
       (cong₂ _,_ p q)
       (Cone.commutes c) ≡
     Cone.commutes d)                                        □

-- A composition operation for cones.

composition : Cone B C → (A → B) → Cone A C
composition c f .Cone.left     = c .Cone.left     ∘ f
composition c f .Cone.right    = c .Cone.right    ∘ f
composition c f .Cone.commutes = c .Cone.commutes ∘ f

-- The pullback for a given cospan.

Pullback : Cospan l r m → Type (l ⊔ r ⊔ m)
Pullback C = ∃ λ x → ∃ λ y → Cospan.left C x ≡ Cospan.right C y

-- The cone with the pullback as the "opposite corner".

pullback-cone : Cone (Pullback C) C
pullback-cone .Cone.left     = proj₁
pullback-cone .Cone.right    = proj₁ ∘ proj₂
pullback-cone .Cone.commutes = proj₂ ∘ proj₂

-- The property of being a homotopy pullback.

Is-homotopy-pullback :
  {A : Type a} {C : Cospan l r m} →
  Cone A C → ∀ b → Type (a ⊔ lsuc b ⊔ l ⊔ r ⊔ m)
Is-homotopy-pullback c b =
  (B : Type b) → Is-equivalence (composition {A = B} c)

-- The pullback is a homotopy pullback for pullback-cone.

is-homotopy-pullback : Is-homotopy-pullback (pullback-cone {C = C}) b
is-homotopy-pullback {C} B =
  _≃_.is-equivalence (
    (B → Pullback C)                                                    ↔⟨⟩
    (B → ∃ λ x → ∃ λ y → Cospan.left C x ≡ Cospan.right C y)            ↔⟨ ΠΣ-comm ⟩
    (∃ λ f → ∀ x → ∃ λ y → Cospan.left C (f x) ≡ Cospan.right C y)      ↔⟨ (∃-cong λ _ → ΠΣ-comm) ⟩
    (∃ λ f → ∃ λ g → ∀ x → Cospan.left C (f x) ≡ Cospan.right C (g x))  ↔⟨ Σ-assoc ⟩
    (∃ λ (f , g) → ∀ x → Cospan.left C (f x) ≡ Cospan.right C (g x))    ↔⟨ inverse Cone↔Σ ⟩□
    Cone B C                                                            □)

-- A universal property for pullbacks.

universal-property : (A → Pullback C) ≃ Cone A C
universal-property = Eq.⟨ _ , is-homotopy-pullback _ ⟩

-- A variant of the universal property.

universal-property′ :
  {C : Cospan l r m}
  (c : Cone A C) →
  Contractible
    (∃ λ (f : A → Pullback C) → composition pullback-cone f ≡ c)
universal-property′ {A} {C} c = _⇔_.from contractible⇔↔⊤ (
  (∃ λ (f : A → Pullback C) → composition pullback-cone f ≡ c)  ↝⟨ (Σ-cong universal-property λ _ → F.id) ⟩
  (∃ λ (d : Cone A C) → d ≡ c)                                  ↝⟨ _⇔_.to contractible⇔↔⊤ (singleton-contractible _) ⟩□
  ⊤                                                             □)

-- A preservation lemma for Cone.

Cone-cong :
  {A₁ : Type a₁} {A₂ : Type a₂} {C : Cospan l r m} →
  Extensionality? k (a₁ ⊔ a₂) (l ⊔ r ⊔ m) →
  A₁ ≃ A₂ →
  Cone A₁ C ↝[ k ] Cone A₂ C
Cone-cong {A₁} {A₂} {C} ext A₁≃A₂ =
  Cone A₁ C          ↔⟨ inverse universal-property ⟩
  (A₁ → Pullback C)  ↝⟨ →-cong₁ ext A₁≃A₂ ⟩
  (A₂ → Pullback C)  ↔⟨ universal-property ⟩□
  Cone A₂ C          □

private

  -- A special case of Cone-cong that does not require extensionality.

  Cone-↑⊤↔Cone-↑⊤ : Cone (↑ a₁ ⊤) C ↔ Cone (↑ a₂ ⊤) C
  Cone-↑⊤↔Cone-↑⊤ {C} =
    Cone (↑ _ ⊤) C        ↔⟨ inverse universal-property ⟩
    (↑ _ ⊤ → Pullback C)  ↝⟨ Π-left-identity-↑ ⟩
    Pullback C            ↝⟨ inverse Π-left-identity-↑ ⟩
    (↑ _ ⊤ → Pullback C)  ↔⟨ universal-property ⟩□
    Cone (↑ _ ⊤) C        □

-- The "opposite corners" of homotopy pullbacks for a fixed cospan are
-- equivalent.

homotopy-pullbacks-equivalent :
  (c₁ : Cone A₁ C) (c₂ : Cone A₂ C) →
  Is-homotopy-pullback c₁ b₁ →
  Is-homotopy-pullback c₂ b₂ →
  A₁ ≃ A₂
homotopy-pullbacks-equivalent {A₁} {C} {A₂} _ _ p₁ p₂ =
  A₁              ↔⟨ inverse Π-left-identity-↑ ⟩
  (↑ _ ⊤ → A₁)    ↝⟨ Eq.⟨ _ , p₁ (↑ _ ⊤) ⟩ ⟩
  Cone (↑ _ ⊤) C  ↔⟨ Cone-↑⊤↔Cone-↑⊤ ⟩
  Cone (↑ _ ⊤) C  ↝⟨ inverse Eq.⟨ _ , p₂ (↑ _ ⊤) ⟩ ⟩
  (↑ _ ⊤ → A₂)    ↔⟨ Π-left-identity-↑ ⟩□
  A₂              □

-- The diagonal of a function.
--
-- This definition is taken from "Modalities in Homotopy Type Theory"
-- by Rijke, Shulman and Spitters.
--
-- Note that the symbol used is not Δ (U+0394), but ∆ (U+2206), to go
-- along with ∇ (U+2207).

∆ : (f : A → B) → A → Pullback (record { left = f; right = f })
∆ f x = x , x , refl (f x)

-- If f is an equivalence, then ∆ f is an equivalence.
--
-- This result is mentioned in "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

Is-equivalence-∆ : Is-equivalence f → Is-equivalence (∆ f)
Is-equivalence-∆ {f} f-eq =
  _≃_.is-equivalence $
  Eq.↔→≃
    _
    proj₁
    (λ (x , y , p) →
       (x , x , refl (f x))  ≡⟨ cong (x ,_) $
                                Σ-≡,≡→≡ (lemma₁ x y p) (lemma₂ x y p) ⟩∎
       (x , y , p)           ∎)
    refl
  where
  equiv = Eq.⟨ _ , f-eq ⟩

  lemma₁ = λ (@ω x y p) →
    x                     ≡⟨ sym $ _≃_.left-inverse-of equiv _ ⟩
    _≃_.from equiv (f x)  ≡⟨ cong (_≃_.from equiv) p ⟩
    _≃_.from equiv (f y)  ≡⟨ _≃_.left-inverse-of equiv _ ⟩∎
    y                     ∎

  lemma₂ = λ (@ω x y p) →
    subst (λ y → f x ≡ f y) (lemma₁ x y p) (refl (f x))  ≡⟨ subst-in-terms-of-trans-and-cong ⟩

    trans (sym (cong (const (f x)) (lemma₁ x y p)))
      (trans (refl (f x)) (cong f (lemma₁ x y p)))       ≡⟨ trans (cong (flip trans _) $
                                                                   trans (cong sym $ cong-const _)
                                                                   sym-refl) $
                                                            trans (trans-reflˡ _) $
                                                            trans-reflˡ _ ⟩

    cong f (lemma₁ x y p)                                ≡⟨⟩

    cong f
      (trans (sym $ _≃_.left-inverse-of equiv _)
         (trans (cong (_≃_.from equiv) p)
            (_≃_.left-inverse-of equiv _)))              ≡⟨ trans (cong-trans _ _ _) $
                                                            cong₂ trans
                                                              (trans (cong-sym _ _) $
                                                               cong sym $ _≃_.left-right-lemma equiv _)
                                                              (trans (cong-trans _ _ _) $
                                                               cong₂ trans
                                                                 (cong-∘ _ _ _)
                                                                 (_≃_.left-right-lemma equiv _)) ⟩
    trans (sym $ _≃_.right-inverse-of equiv _)
      (trans (cong (f ∘ _≃_.from equiv) p)
         (_≃_.right-inverse-of equiv _))                 ≡⟨ elim¹
                                                              (λ p →
                                                                 trans (sym $ _≃_.right-inverse-of equiv _)
                                                                   (trans (cong (f ∘ _≃_.from equiv) p)
                                                                      (_≃_.right-inverse-of equiv _)) ≡
                                                                 p)
                                                              (
      trans (sym $ _≃_.right-inverse-of equiv _)
        (trans (cong (f ∘ _≃_.from equiv) (refl _))
           (_≃_.right-inverse-of equiv _))                     ≡⟨ cong (trans _) $
                                                                  trans (cong (flip trans _) $ cong-refl _) $
                                                                  trans-reflˡ _ ⟩
      trans (sym $ _≃_.right-inverse-of equiv _)
        (_≃_.right-inverse-of equiv _)                         ≡⟨ trans-symˡ _ ⟩∎

      refl _                                                   ∎)
                                                              _ ⟩∎
    p                                                    ∎
