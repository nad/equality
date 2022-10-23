------------------------------------------------------------------------
-- Pointed types and loop spaces
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- Partly following the HoTT book.

open import Equality

module Pointed-type
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (_×_)

open import Bijection eq as B using (_↔_)
open import Equivalence eq as E using (_≃_)
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq
open import Surjection eq using (_↠_)
open import Univalence-axiom eq

private
  variable
    a b ℓ : Level
    A B   : Type a
    x y   : A
    p q   : x ≡ y
    k     : Kind

------------------------------------------------------------------------
-- The definition of pointed types

-- Pointed types.

Pointed-type : ∀ ℓ → Type (lsuc ℓ)
Pointed-type a = ∃ λ (A : Type a) → A

------------------------------------------------------------------------
-- Based maps

-- Based maps (generalised to several kinds of underlying
-- "functions").

infix 4 _↝[_]ᴮ_ _→ᴮ_ _≃ᴮ_

_↝[_]ᴮ_ : Pointed-type a → Kind → Pointed-type b → Type (a ⊔ b)
(A , x) ↝[ k ]ᴮ (B , y) =
  ∃ λ (f : A ↝[ k ] B) → to-implication f x ≡ y

-- Based maps.

_→ᴮ_ : Pointed-type a → Pointed-type b → Type (a ⊔ b)
_→ᴮ_ = _↝[ implication ]ᴮ_

-- Based equivalences.

_≃ᴮ_ : Pointed-type a → Pointed-type b → Type (a ⊔ b)
_≃ᴮ_ = _↝[ equivalence ]ᴮ_

private
  variable
    P P₁ P₂ Q Q₁ Q₂ R : Pointed-type a
    P→Q               : P →ᴮ Q
    P≃Q               : P ≃ᴮ Q

-- Based equivalences can be converted to based maps.

≃ᴮ→→ᴮ : P ≃ᴮ Q → P →ᴮ Q
≃ᴮ→→ᴮ = Σ-map _≃_.to id

-- Based equivalences are equivalent to equalities (assuming
-- univalence).

≃ᴮ≃≡ : {P Q : Pointed-type a} → Univalence a → (P ≃ᴮ Q) ≃ (P ≡ Q)
≃ᴮ≃≡ {P = A , x} {Q = B , y} univ =
  (∃ λ (A≃B : A ≃ B) → _≃_.to A≃B x ≡ y)    ↝⟨ (inverse $
                                                Σ-cong (≡≃≃ univ) λ A≃B →
                                                ≡⇒≃ $ cong (_≡ _) $
                                                subst-id-in-terms-of-≡⇒↝ equivalence) ⟩
  (∃ λ (A≡B : A ≡ B) → subst id A≡B x ≡ y)  ↔⟨ B.Σ-≡,≡↔≡ ⟩□
  (A , x) ≡ (B , y)                         □

-- _↝[ k ]ᴮ_ is reflexive.

↝ᴮ-refl : P ↝[ k ]ᴮ P
↝ᴮ-refl {k = k} = F.id , cong (_$ _) (to-implication-id k)

-- _↝[ k ]ᴮ_ is transitive.

↝ᴮ-trans : P ↝[ k ]ᴮ Q → Q ↝[ k ]ᴮ R → P ↝[ k ]ᴮ R
↝ᴮ-trans {P = _ , x} {k = k} {Q = _ , y} {R = _ , z}
  (A↝B , p) (B↝C , q) =
    B↝C F.∘ A↝B
  , (to-implication (B↝C F.∘ A↝B) x             ≡⟨ cong (_$ _) $ to-implication-∘ k ⟩
     to-implication B↝C (to-implication A↝B x)  ≡⟨ cong (to-implication B↝C) p ⟩
     to-implication B↝C y                       ≡⟨ q ⟩∎
     z                                          ∎)

-- _≃ᴮ_ is symmetric.

≃ᴮ-sym : P ≃ᴮ Q → Q ≃ᴮ P
≃ᴮ-sym (A≃B , p) = inverse A≃B , _≃_.to-from A≃B p

-- "Equational" reasoning combinators.

infix  -1 _□ᴮ finallyᴮ
infixr -2 stepᴮ

-- For an explanation of why stepᴮ is defined in this way, see
-- Equality.step-≡.

stepᴮ : (P : Pointed-type a) {Q : Pointed-type b} →
        Q ↝[ k ]ᴮ R → P ↝[ k ]ᴮ Q → P ↝[ k ]ᴮ R
stepᴮ _ = flip ↝ᴮ-trans

syntax stepᴮ P Q↝R P↝Q = P ↝ᴮ⟨ P↝Q ⟩ Q↝R

finallyᴮ :
  (P : Pointed-type a) (Q : Pointed-type b) →
  P ↝[ k ]ᴮ Q → P ↝[ k ]ᴮ Q
finallyᴮ _ _ P↝Q = P↝Q

syntax finallyᴮ P Q P↝Q = P ↝ᴮ⟨ P↝Q ⟩□ Q □

_□ᴮ : (P : Pointed-type a) → P ↝[ k ]ᴮ P
_ □ᴮ = ↝ᴮ-refl

-- There is a split surjection from based maps from
-- (Maybe A , nothing) to functions.

Maybe→ᴮ↠→ : (Maybe A , nothing) →ᴮ (B , x) ↠ (A → B)
Maybe→ᴮ↠→ {A = A} {B = B} {x = x} = record
  { logical-equivalence = record
    { to   = (Maybe A , nothing) →ᴮ (B , x)  ↝⟨ proj₁ ⟩
             (Maybe A → B)                   ↝⟨ _∘ inj₂ ⟩□
             (A → B)                         □
    ; from = λ f → [ (λ _ → x) , f ] , refl x
    }
  ; right-inverse-of = refl
  }

-- Based maps from (Maybe A , nothing) are isomorphic to functions
-- (assuming extensionality).

Maybe→ᴮ↔→ :
  ∀ {A : Type a} {B : Type b} {x} →
  (Maybe A , nothing) →ᴮ (B , x) ↝[ a ∣ b ] (A → B)
Maybe→ᴮ↔→ {A = A} {B} {x} = generalise-ext?
  (_↠_.logical-equivalence Maybe→ᴮ↠→)
  (λ ext →
       refl
     , (λ (f , eq) → Σ-≡,≡→≡
          (apply-ext ext
             [ (λ _ →
                  x          ≡⟨ sym eq ⟩∎
                  f nothing  ∎)
             , (λ _ → refl _)
             ])
          (subst (λ f → f nothing ≡ x)
                 (apply-ext ext [ (λ _ → sym eq) , (λ _ → refl _) ])
                 (refl x)                                             ≡⟨ subst-ext ext ⟩

           subst (_≡ x) (sym eq) (refl x)                             ≡⟨ subst-trans _ ⟩

           trans eq (refl x)                                          ≡⟨ trans-reflʳ _ ⟩∎

           eq                                                         ∎)))

-- A corollary.

Bool→ᴮ↔ :
  ∀ {A : Type a} {x} →
  (Bool , true) →ᴮ (A , x) ↝[ lzero ∣ a ] A
Bool→ᴮ↔ {A = A} {x = x} ext =
  (Bool , true) →ᴮ (A , x)  ↝⟨ Maybe→ᴮ↔→ ext ⟩
  (⊤ → A)                   ↔⟨ Π-left-identity ⟩□
  A                         □

------------------------------------------------------------------------
-- Loop spaces

-- The loop space of a pointed type.

Ω : Pointed-type ℓ → Pointed-type ℓ
Ω (A , x) = (x ≡ x) , refl x

-- Iterated loop spaces.
--
-- The HoTT book uses Ω[ n ] ∘ Ω rather than Ω ∘ Ω[ n ]. I prefer
-- the following definition, because with the other definition the
-- type of Equality.Groupoid.Ω[2+n]-commutative would not be
-- well-formed. (See also Ω∘Ω[]≡Ω[]∘Ω.)

Ω[_] : ℕ → Pointed-type ℓ → Pointed-type ℓ
Ω[ zero  ] = id
Ω[ suc n ] = Ω ∘ Ω[ n ]

-- A rearrangement lemma for Ω and Ω[_].

Ω∘Ω[]≡Ω[]∘Ω : ∀ n → Ω (Ω[ n ] P) ≡ Ω[ n ] (Ω P)
Ω∘Ω[]≡Ω[]∘Ω {P = P} zero =
  Ω P  ∎
Ω∘Ω[]≡Ω[]∘Ω {P = P} (suc n) =
  Ω (Ω[ suc n ] P)  ≡⟨⟩
  Ω (Ω (Ω[ n ] P))  ≡⟨ cong Ω $ Ω∘Ω[]≡Ω[]∘Ω n ⟩
  Ω (Ω[ n ] (Ω P))  ≡⟨⟩
  Ω[ suc n ] (Ω P)  ∎

-- Ω preserves based maps.

Ω-cong-→ᴮ : P →ᴮ Q → Ω P →ᴮ Ω Q
Ω-cong-→ᴮ {P = A , x} {Q = B , y} (to , to≡) =
    (x ≡ x        ↝⟨ cong to ⟩
     to x ≡ to x  ↔⟨ ≡⇒≃ $ cong₂ _≡_ to≡ to≡ ⟩□
     y ≡ y        □)
  , (≡⇒→ (cong₂ _≡_ to≡ to≡) (cong to (refl x))      ≡⟨ cong (≡⇒→ (cong₂ _≡_ to≡ to≡)) $ cong-refl _ ⟩
     ≡⇒→ (cong₂ _≡_ to≡ to≡) (refl (to x))           ≡⟨ elim¹
                                                          (λ to≡ → ≡⇒→ (cong₂ _≡_ to≡ to≡) (refl (to x)) ≡
                                                                   refl _)
                                                          (
         ≡⇒→ (cong₂ _≡_ (refl _) (refl _)) (refl _)        ≡⟨ cong (λ eq → ≡⇒→ eq (refl _)) $ cong₂-refl _≡_ ⟩
         ≡⇒→ (refl _) (refl _)                             ≡⟨ cong (λ eq → _≃_.to eq (refl _)) ≡⇒↝-refl ⟩∎
         refl _                                                       ∎)
                                                          _ ⟩∎
     refl y                                          ∎)

-- Ω preserves based equivalences.

Ω-cong-≃ᴮ : P ≃ᴮ Q → Ω P ≃ᴮ Ω Q
Ω-cong-≃ᴮ {P = A , x} {Q = B , y} (A≃B , to≡) =
    (x ≡ x                        ↝⟨ inverse $ E.≃-≡ A≃B ⟩
     _≃_.to A≃B x ≡ _≃_.to A≃B x  ↝⟨ ≡⇒↝ _ $ cong₂ _≡_ to≡ to≡ ⟩□
     y ≡ y                        □)
  , proj₂ (Ω-cong-→ᴮ (_≃_.to A≃B , to≡))

-- Ω[ n ] preserves based maps.

Ω[_]-cong-→ᴮ : ∀ n → P →ᴮ Q → Ω[ n ] P →ᴮ Ω[ n ] Q
Ω[ zero  ]-cong-→ᴮ A→B = A→B
Ω[ suc n ]-cong-→ᴮ A→B = Ω-cong-→ᴮ (Ω[ n ]-cong-→ᴮ A→B)

-- Ω[ n ] preserves based equivalences.

Ω[_]-cong-≃ᴮ : ∀ n → P ≃ᴮ Q → Ω[ n ] P ≃ᴮ Ω[ n ] Q
Ω[ zero  ]-cong-≃ᴮ A≃B = A≃B
Ω[ suc n ]-cong-≃ᴮ A≃B = Ω-cong-≃ᴮ (Ω[ n ]-cong-≃ᴮ A≃B)

-- ≃ᴮ→→ᴮ commutes with Ω-cong-≃ᴮ/Ω-cong-→ᴮ.

≃ᴮ→→ᴮ-Ω-cong-≃ᴮ :
  (P≃Q : P ≃ᴮ Q) →
  ≃ᴮ→→ᴮ (Ω-cong-≃ᴮ P≃Q) ≡ Ω-cong-→ᴮ (≃ᴮ→→ᴮ P≃Q)
≃ᴮ→→ᴮ-Ω-cong-≃ᴮ _ = refl _

-- ≃ᴮ→→ᴮ commutes with Ω[ n ]-cong-≃ᴮ/Ω[ n ]-cong-→ᴮ.

≃ᴮ→→ᴮ-Ω[_]-cong-≃ᴮ :
  ∀ n →
  ≃ᴮ→→ᴮ (Ω[ n ]-cong-≃ᴮ P≃Q) ≡
  Ω[ n ]-cong-→ᴮ (≃ᴮ→→ᴮ P≃Q)
≃ᴮ→→ᴮ-Ω[_]-cong-≃ᴮ {P≃Q = P≃Q} = λ where
  zero    → refl _
  (suc n) →
    ≃ᴮ→→ᴮ (Ω-cong-≃ᴮ (Ω[ n ]-cong-≃ᴮ P≃Q))  ≡⟨⟩
    Ω-cong-→ᴮ (≃ᴮ→→ᴮ (Ω[ n ]-cong-≃ᴮ P≃Q))  ≡⟨ cong Ω-cong-→ᴮ ≃ᴮ→→ᴮ-Ω[ n ]-cong-≃ᴮ ⟩
    Ω-cong-→ᴮ (Ω[ n ]-cong-→ᴮ (≃ᴮ→→ᴮ P≃Q))  ∎

-- A lemma relating Ω-cong-→ᴮ and ↝ᴮ-refl.

proj₁-Ω-cong-→ᴮ-↝ᴮ-refl :
  proj₁ (Ω-cong-→ᴮ ↝ᴮ-refl) p ≡ p
proj₁-Ω-cong-→ᴮ-↝ᴮ-refl {p = p} =
  ≡⇒→
    (cong₂ _≡_
       (cong (_$ _) (refl _))
       (cong (_$ _) (refl _)))
    (cong id p)                 ≡⟨ cong₂ ≡⇒→
                                     (trans (cong₂ (cong₂ _≡_)
                                               (cong-refl _)
                                               (cong-refl _)) $
                                      cong₂-refl _≡_)
                                     (sym $ cong-id _) ⟩

  ≡⇒→ (refl _) p                ≡⟨ cong (_$ _) ≡⇒→-refl ⟩∎

  p                             ∎

-- A lemma relating Ω-cong-≃ᴮ and ↝ᴮ-refl.

proj₁-Ω-cong-≃ᴮ-↝ᴮ-refl :
  _≃_.to (proj₁ (Ω-cong-≃ᴮ ↝ᴮ-refl)) p ≡ p
proj₁-Ω-cong-≃ᴮ-↝ᴮ-refl = proj₁-Ω-cong-→ᴮ-↝ᴮ-refl

-- A lemma relating Ω-cong-→ᴮ and trans.

Ω-cong-→ᴮ-trans :
  proj₁ (Ω-cong-→ᴮ P→Q) (trans p q) ≡
  trans (proj₁ (Ω-cong-→ᴮ P→Q) p)
        (proj₁ (Ω-cong-→ᴮ P→Q) q)
Ω-cong-→ᴮ-trans {P→Q = to , to≡} {p = p} {q = q} =
  ≡⇒→ (cong₂ _≡_ to≡ to≡) (cong to (trans p q))            ≡⟨ cong (≡⇒→ (cong₂ _≡_ to≡ to≡)) $
                                                              cong-trans _ _ _ ⟩
  ≡⇒→ (cong₂ _≡_ to≡ to≡)
    (trans (cong to p) (cong to q))                        ≡⟨ lemma _ ⟩

  trans
    (trans (sym to≡)
       (trans (cong to p) (cong to q)))
    to≡                                                    ≡⟨ trans (cong (flip trans _) $ sym $ trans-assoc _ _ _) $
                                                              trans-assoc _ _ _ ⟩
  trans
    (trans (sym to≡) (cong to p))
    (trans (cong to q) to≡)                                ≡⟨ cong (trans _) $ sym $
                                                              trans--[trans-sym] _ _ ⟩
  trans (trans (sym to≡) (cong to p))
    (trans to≡ (trans (sym to≡) (trans (cong to q) to≡)))  ≡⟨ trans (cong (trans _) $ cong (trans _) $ sym $ trans-assoc _ _ _) $
                                                              sym $ trans-assoc _ _ _ ⟩
  trans
    (trans (trans (sym to≡) (cong to p)) to≡)
    (trans (trans (sym to≡) (cong to q)) to≡)              ≡⟨ sym $ cong₂ trans (lemma _) (lemma _) ⟩∎

  trans
    (≡⇒→ (cong₂ _≡_ to≡ to≡) (cong to p))
    (≡⇒→ (cong₂ _≡_ to≡ to≡) (cong to q))                  ∎
  where
  lemma = λ p →
    ≡⇒→ (cong₂ _≡_ to≡ to≡) p                          ≡⟨⟩
    ≡⇒→ (trans (cong (_≡ _) to≡) (cong (_ ≡_) to≡)) p  ≡⟨ cong (_$ p) $ ≡⇒↝-trans equivalence ⟩
    ≡⇒→ (cong (_ ≡_) to≡) (≡⇒→ (cong (_≡ _) to≡) p)    ≡⟨ sym $ subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
    subst (_ ≡_) to≡ (≡⇒→ (cong (_≡ _) to≡) p)         ≡⟨ sym trans-subst ⟩
    trans (≡⇒→ (cong (_≡ _) to≡) p) to≡                ≡⟨ cong (flip trans _) $ sym $ subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
    trans (subst (_≡ _) to≡ p) to≡                     ≡⟨ cong (flip trans _) subst-trans-sym ⟩∎
    trans (trans (sym to≡) p) to≡                      ∎

-- A lemma relating Ω-cong-≃ᴮ and trans.

Ω-cong-≃ᴮ-trans :
  (P≃Q : P ≃ᴮ Q) →
  _≃_.to (proj₁ (Ω-cong-≃ᴮ P≃Q)) (trans p q) ≡
  trans (_≃_.to (proj₁ (Ω-cong-≃ᴮ P≃Q)) p)
        (_≃_.to (proj₁ (Ω-cong-≃ᴮ P≃Q)) q)
Ω-cong-≃ᴮ-trans _ = Ω-cong-→ᴮ-trans

-- A lemma relating Ω[_]-cong-→ᴮ and trans.

Ω[1+_]-cong-→ᴮ-trans :
  ∀ n {p q} →
  proj₁ (Ω[ 1 + n ]-cong-→ᴮ P→Q) (trans p q) ≡
  trans (proj₁ (Ω[ 1 + n ]-cong-→ᴮ P→Q) p)
        (proj₁ (Ω[ 1 + n ]-cong-→ᴮ P→Q) q)
Ω[1+ _ ]-cong-→ᴮ-trans = Ω-cong-→ᴮ-trans

-- A lemma relating Ω[_]-cong-≃ᴮ and trans.

Ω[1+_]-cong-≃ᴮ-trans :
  ∀ n {p q} (P≃Q : P ≃ᴮ Q) →
  _≃_.to (proj₁ (Ω[ 1 + n ]-cong-≃ᴮ P≃Q)) (trans p q) ≡
  trans (_≃_.to (proj₁ (Ω[ 1 + n ]-cong-≃ᴮ P≃Q)) p)
        (_≃_.to (proj₁ (Ω[ 1 + n ]-cong-≃ᴮ P≃Q)) q)
Ω[1+ n ]-cong-≃ᴮ-trans P≃Q = Ω-cong-≃ᴮ-trans (Ω[ n ]-cong-≃ᴮ P≃Q)

-- A has h-level 1 + n iff the iterated loop space Ω[ n ] (A , x) is
-- contractible for every x : A.

+⇔∀contractible-Ω[] :
  ∀ n →
  H-level (1 + n) A
    ⇔
  ((x : A) → Contractible (proj₁ $ Ω[ n ] (A , x)))
+⇔∀contractible-Ω[] {A = A} zero =
  Is-proposition A      ↝⟨ record { to   = propositional⇒inhabited⇒contractible
                                  ; from = [inhabited⇒contractible]⇒propositional
                                  } ⟩□
  (A → Contractible A)  □

+⇔∀contractible-Ω[] {A = A} (suc zero) =
  Is-set A                            ↝⟨ 2+⇔∀1+≡ 0 ⟩
  ((x : A) → Is-proposition (x ≡ x))  ↝⟨ (∀-cong _ λ x → record { to   = flip propositional⇒inhabited⇒contractible (refl x)
                                                                ; from = mono₁ 0
                                                                }) ⟩□
  ((x : A) → Contractible (x ≡ x))    □

+⇔∀contractible-Ω[] {A = A} (suc (suc n)) =
  H-level (3 + n) A                                                  ↝⟨ 2+⇔∀1+≡ (1 + n) ⟩

  ((x : A) → H-level (2 + n) (x ≡ x))                                ↝⟨ (∀-cong _ λ _ → +⇔∀contractible-Ω[] (suc n)) ⟩

  ((x : A) (p : x ≡ x) →
   Contractible (proj₁ $ Ω[ 1 + n ] ((x ≡ x) , p)))                  ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → H-level-cong _ _ $ proj₁ $
                                                                         Ω[ 1 + n ]-cong-≃ᴮ $ lemma _) ⟩

  ((x : A) → x ≡ x → Contractible (proj₁ $ Ω[ 1 + n ] (Ω (A , x))))  ↝⟨ (∀-cong _ λ x → _↠_.logical-equivalence $ inhabited→↠ (refl x)) ⟩

  ((x : A) → Contractible (proj₁ $ Ω[ 1 + n ] (Ω (A , x))))          ↝⟨ (∀-cong _ λ _ → ≡⇒↝ _ $ cong (Contractible ∘ proj₁) $ sym $
                                                                         Ω∘Ω[]≡Ω[]∘Ω (1 + n)) ⟩□
  ((x : A) → Contractible (proj₁ $ Ω[ 2 + n ] (A , x)))              □
  where
  lemma : (p : x ≡ x) → ((x ≡ x) , p) ≃ᴮ Ω (A , x)
  lemma p = E.↔⇒≃ (inverse $ flip-trans-isomorphism p)
          , (trans p (sym p)  ≡⟨ trans-symʳ _ ⟩∎
             refl _           ∎)

------------------------------------------------------------------------
-- Products

-- The product of two pointed types.

infixr 2 _×_

_×_ : Pointed-type a → Pointed-type b → Pointed-type (a ⊔ b)
(A , x) × (B , y) = (A P.× B) , (x , y)

-- The first projection.

proj₁ᴾ : (P × Q) →ᴮ P
proj₁ᴾ = proj₁ , refl _

-- The second projection.

proj₂ᴾ : (P × Q) →ᴮ Q
proj₂ᴾ = proj₂ , refl _

-- The operator _×_ preserves based maps and equivalences.

infixr 2 _×-cong-→ᴮ_ _×-cong-≃ᴮ_

_×-cong-→ᴮ_ : P₁ →ᴮ P₂ → Q₁ →ᴮ Q₂ → (P₁ × Q₁) →ᴮ (P₂ × Q₂)
(f₁ , eq₁) ×-cong-→ᴮ (f₂ , eq₂) =
    (f₁ ×-cong f₂)
  , cong₂ _,_ eq₁ eq₂

_×-cong-≃ᴮ_ : P₁ ≃ᴮ P₂ → Q₁ ≃ᴮ Q₂ → (P₁ × Q₁) ≃ᴮ (P₂ × Q₂)
(f₁ , eq₁) ×-cong-≃ᴮ (f₂ , eq₂) =
    (f₁ ×-cong f₂)
  , cong₂ _,_ eq₁ eq₂

-- Ω commutes with _×_.

Ω-× : Ω (P × Q) ≃ᴮ (Ω P × Ω Q)
Ω-× {P = A , x} {Q = B , y} =
    ((x , y) ≡ (x , y)  ↝⟨ E.↔⇒≃ (inverse ≡×≡↔≡) ⟩□
     x ≡ x P.× y ≡ y    □)
  , ((cong proj₁ (refl (x , y)) , cong proj₂ (refl (x , y)))  ≡⟨ cong₂ _,_ (cong-refl _) (cong-refl _) ⟩∎
     (refl x , refl y)                                        ∎)

-- Ω[ n ] commutes with _×_.

Ω[_]-× : ∀ n → Ω[ n ] (P × Q) ≃ᴮ (Ω[ n ] P × Ω[ n ] Q)
Ω[_]-× {P = P} {Q = Q} = λ where
  zero    → P × Q  □ᴮ
  (suc n) →
    Ω (Ω[ n ] (P × Q))           ↝ᴮ⟨ Ω-cong-≃ᴮ Ω[ n ]-× ⟩
    Ω (Ω[ n ] P × Ω[ n ] Q)      ↝ᴮ⟨ Ω-× ⟩□
    Ω (Ω[ n ] P) × Ω (Ω[ n ] Q)  □

-- A lemma relating Ω[ 1 ]-× and Ω-×.

Ω[1]-× : _≃_.to (proj₁ Ω[ 1 ]-×) p ≡ _≃_.to (proj₁ Ω-×) p
Ω[1]-× {p = p} =
  _≃_.to (proj₁ Ω[ 1 ]-×) p                                  ≡⟨⟩
  _≃_.to (proj₁ Ω-×) (_≃_.to (proj₁ (Ω-cong-≃ᴮ ↝ᴮ-refl)) p)  ≡⟨ cong (_≃_.to (proj₁ Ω-×)) proj₁-Ω-cong-≃ᴮ-↝ᴮ-refl ⟩∎
  _≃_.to (proj₁ Ω-×) p                                       ∎

-- A lemma relating Ω-× and trans.

Ω-×-trans :
  _≃_.to (proj₁ Ω-×) (trans p q) ≡
  Σ-zip trans trans
    (_≃_.to (proj₁ Ω-×) p)
    (_≃_.to (proj₁ Ω-×) q)
Ω-×-trans {p = p} {q = q} =
  _≃_.to (proj₁ Ω-×) (trans p q)         ≡⟨⟩

  ( cong proj₁ (trans p q)
  , cong proj₂ (trans p q)
  )                                      ≡⟨ cong₂ _,_
                                              (cong-trans _ _ _)
                                              (cong-trans _ _ _) ⟩
  ( trans (cong proj₁ p) (cong proj₁ q)
  , trans (cong proj₂ p) (cong proj₂ q)
  )                                      ≡⟨⟩

  Σ-zip trans trans
    (_≃_.to (proj₁ Ω-×) p)
    (_≃_.to (proj₁ Ω-×) q)               ∎

-- A lemma relating Ω[_]-× and trans.

Ω[1+_]-×-trans :
  ∀ n {p q : proj₁ (Ω[ suc n ] (P × Q))} →
  _≃_.to (proj₁ Ω[ suc n ]-×) (trans p q) ≡
  Σ-zip trans trans
    (_≃_.to (proj₁ Ω[ suc n ]-×) p)
    (_≃_.to (proj₁ Ω[ suc n ]-×) q)
Ω[1+ n ]-×-trans {p = p} {q = q} =
  _≃_.to (proj₁ Ω-×)
    (_≃_.to (proj₁ (Ω-cong-≃ᴮ Ω[ n ]-×)) (trans p q))  ≡⟨ cong (_≃_.to (proj₁ Ω-×)) $ Ω-cong-≃ᴮ-trans Ω[ n ]-× ⟩

  _≃_.to (proj₁ Ω-×)
    (trans (_≃_.to (proj₁ (Ω-cong-≃ᴮ Ω[ n ]-×)) p)
           (_≃_.to (proj₁ (Ω-cong-≃ᴮ Ω[ n ]-×)) q))    ≡⟨ Ω-×-trans ⟩∎

  Σ-zip trans trans
    (_≃_.to (proj₁ Ω-×)
       (_≃_.to (proj₁ (Ω-cong-≃ᴮ Ω[ n ]-×)) p))
    (_≃_.to (proj₁ Ω-×)
       (_≃_.to (proj₁ (Ω-cong-≃ᴮ Ω[ n ]-×)) q))        ∎
