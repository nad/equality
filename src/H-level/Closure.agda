------------------------------------------------------------------------
-- Closure properties for h-levels
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module H-level.Closure
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection hiding (id; _∘_)
open Derived-definitions-and-properties eq
import Equality.Decidable-UIP eq as DUIP
open import Equality.Decision-procedures eq
import Equivalence.Contractible-preimages eq as CP
open import Equivalence.Half-adjoint eq as HA using (Is-equivalence)
open import Extensionality eq
open import H-level eq
open import Logical-equivalence hiding (id; _∘_)
open import Nat eq as Nat
open import Preimage eq as Preimage
open import Prelude
open import Surjection eq as Surjection hiding (id; _∘_)

------------------------------------------------------------------------
-- The unit type

-- The unit type is contractible.

⊤-contractible : Contractible ⊤
⊤-contractible = (_ , λ _ → refl _)

-- A type is contractible iff it is in bijective correspondence with
-- the unit type.

contractible⇔↔⊤ : ∀ {a} {A : Type a} → Contractible A ⇔ (A ↔ ⊤)
contractible⇔↔⊤ = record
  { to   = flip contractible-isomorphic ⊤-contractible
  ; from = λ A↔⊤ → respects-surjection
                     (_↔_.surjection (Bijection.inverse A↔⊤))
                     0
                     ⊤-contractible
  }

------------------------------------------------------------------------
-- The empty type

opaque

  -- The empty type is not contractible.

  ¬-⊥-contractible : ∀ {ℓ} → ¬ Contractible (⊥ {ℓ = ℓ})
  ¬-⊥-contractible = ⊥-elim ∘ proj₁

  -- The empty type is propositional.

  ⊥-propositional : ∀ {ℓ} → Is-proposition (⊥ {ℓ = ℓ})
  ⊥-propositional x = ⊥-elim x

  -- Thus any uninhabited type is also propositional.

  uninhabited-propositional : ∀ {a} {A : Type a} →
                              ¬ A → Is-proposition A
  uninhabited-propositional ¬A =
    respects-surjection (_↔_.surjection $ ⊥↔uninhabited {ℓ = # 0} ¬A) 1
                        ⊥-propositional

------------------------------------------------------------------------
-- Booleans

opaque

  -- The booleans are not propositional.

  ¬-Bool-propositional : ¬ Is-proposition Bool
  ¬-Bool-propositional propositional =
    Bool.true≢false $
    propositional true false

  -- The booleans form a set.

  Bool-set : Is-set Bool
  Bool-set = DUIP.decidable⇒set Bool._≟_

------------------------------------------------------------------------
-- Natural numbers

opaque

  -- ℕ is not propositional.

  ¬-ℕ-propositional : ¬ Is-proposition ℕ
  ¬-ℕ-propositional ℕ-prop = 0≢+ $ ℕ-prop 0 1

  -- ℕ is a set.

  ℕ-set : Is-set ℕ
  ℕ-set = DUIP.decidable⇒set Nat._≟_

  -- Nat._≤_ is not a family of contractible types.

  ¬-≤-contractible : ¬ (∀ {m n} → Contractible (m Nat.≤ n))
  ¬-≤-contractible ≤-contr with proj₁ (≤-contr {m = 1} {n = 0})
  ... | ≤-refl′ 1≡0   = 0≢+ (sym 1≡0)
  ... | ≤-step′ _ +≡0 = 0≢+ (sym +≡0)

  -- Nat._≤_ is a family of propositions.

  ≤-propositional : ∀ {m n} → Is-proposition (m Nat.≤ n)
  ≤-propositional = irr
    where
    lemma : ∀ {m n k} → m ≡ n → m ≤ k → suc k ≡ n → ⊥₀
    lemma {m} {n} {k} m≡n m≤k 1+k≡n = <-irreflexive (
      suc n  ≡⟨ cong suc $ sym m≡n ⟩≤
      suc m  ≤⟨ suc≤suc m≤k ⟩
      suc k  ≡⟨ 1+k≡n ⟩≤
      n      ∎≤)

    cong-≤-step′ :
      ∀ {m n k₁ k₂}
        {p₁ : m ≤ k₁} {q₁ : suc k₁ ≡ n}
        {p₂ : m ≤ k₂} {q₂ : suc k₂ ≡ n} →
      (k₁≡k₂ : k₁ ≡ k₂) →
      subst (m ≤_) k₁≡k₂ p₁ ≡ p₂ →
      subst (λ k → suc k ≡ n) k₁≡k₂ q₁ ≡ q₂ →
      ≤-step′ p₁ q₁ ≡ ≤-step′ p₂ q₂
    cong-≤-step′ {p₁} {q₁} {p₂} {q₂} k₁≡k₂ p-eq q-eq =
      cong (λ { (k , p , q) → ≤-step′ {k = k} p q })
        (Σ-≡,≡→≡
           k₁≡k₂
           (subst (λ k → _ ≤ k × suc k ≡ _) k₁≡k₂ (p₁ , q₁)             ≡⟨ push-subst-, _ _ ⟩
            (subst (_ ≤_) k₁≡k₂ p₁ , subst (λ k → suc k ≡ _) k₁≡k₂ q₁)  ≡⟨ cong₂ _,_ p-eq q-eq ⟩∎
            (p₂ , q₂)                                                   ∎))

    irr : ∀ {m n} → Is-proposition (m Nat.≤ n)
    irr (≤-refl′ q₁)    (≤-refl′ q₂)    = cong ≤-refl′ $ ℕ-set q₁ q₂
    irr (≤-refl′ q₁)    (≤-step′ p₂ q₂) = ⊥-elim (lemma q₁ p₂ q₂)
    irr (≤-step′ p₁ q₁) (≤-refl′ q₂)    = ⊥-elim (lemma q₂ p₁ q₁)

    irr {n} (≤-step′ {k = k₁} p₁ q₁)
            (≤-step′ {k = k₂} p₂ q₂) =
      cong-≤-step′ (cancel-suc (suc k₁  ≡⟨ q₁ ⟩
                                n       ≡⟨ sym q₂ ⟩∎
                                suc k₂  ∎))
                   (irr _ p₂)
                   (ℕ-set _ _)

  -- Nat.Distinct is not a family of contractible types.

  ¬-Distinct-contractible :
    ¬ (∀ m n → Contractible (Nat.Distinct m n))
  ¬-Distinct-contractible Distinct-contr =
    proj₁ (Distinct-contr 0 0)

  -- Distinct is a family of propositions.

  Distinct-propositional : ∀ m n → Is-proposition (Distinct m n)
  Distinct-propositional zero    zero    = ⊥-propositional
  Distinct-propositional zero    (suc n) = mono₁ 0 ⊤-contractible
  Distinct-propositional (suc m) zero    = mono₁ 0 ⊤-contractible
  Distinct-propositional (suc m) (suc n) = Distinct-propositional m n

------------------------------------------------------------------------
-- Π-types

opaque

  -- Given extensionality there is a (split) surjection from
  -- ∀ x → f x ≡ g x to f ≡ g.

  ext-surj :
    ∀ {a p} →
    Extensionality a p →
    {A : Type a} {P : A → Type p} {f g : (x : A) → P x} →
    (∀ x → f x ≡ g x) ↠ (f ≡ g)
  ext-surj ext =
    _↔_.surjection $
    HA.Is-equivalence→↔ $
    HA.inverse-equivalence $
    Extensionality.extensionality ext

-- H-level′ is closed under Π A (assuming extensionality).

Π-closure′ :
  ∀ {a b} {A : Type a} {B : A → Type b} →
  Extensionality a b →
  ∀ n → (∀ x → H-level′ n (B x)) → H-level′ n ((x : A) → B x)
Π-closure′ ext zero =
  _⇔_.from [Π-Contractible→Contractible-Π]⇔Function-extensionality′
    (apply-ext ext)
Π-closure′ ext (suc n) = λ h f g →
  respects-surjection′ (ext-surj ext) n $
  Π-closure′ ext n (λ x → h x (f x) (g x))

-- H-level is closed under Π A (assuming extensionality).

Π-closure : ∀ {a b} {A : Type a} {B : A → Type b} →
            Extensionality a b →
            ∀ n → (∀ x → H-level n (B x)) → H-level n ((x : A) → B x)
Π-closure ext n h =
  _⇔_.from H-level⇔H-level′ $
  Π-closure′ ext n (λ x → _⇔_.to H-level⇔H-level′ (h x))

-- This also applies to the implicit function space.

implicit-Π-closure :
  ∀ {a b} {A : Type a} {B : A → Type b} →
  Extensionality a b →
  ∀ n → (∀ x → H-level n (B x)) → H-level n ({x : A} → B x)
implicit-Π-closure ext n =
  respects-surjection
    (_↔_.surjection $ Bijection.inverse implicit-Π↔Π) n ∘
  Π-closure ext n

opaque

  -- Negated types are propositional, assuming extensionality.

  ¬-propositional :
    ∀ {a} {A : Type a} →
    Extensionality a lzero →
    Is-proposition (¬ A)
  ¬-propositional ext = Π-closure ext 1 (λ _ → ⊥-propositional)

-- The type ∀ y → x ≡ y is a proposition (assuming extensionality).
--
-- This is Lemma 4.1 from van Doorn's "Constructing the Propositional
-- Truncation using Non-recursive HITs" (perhaps the proof is not
-- quite identical to van Doorn's).

Π≡-proposition :
  ∀ {a} {A : Type a} →
  Extensionality a a →
  (x : A) → Is-proposition (∀ y → x ≡ y)
Π≡-proposition {A} ext x =
  [inhabited⇒+]⇒+ 0 λ f →
  let prop : Is-proposition A
      prop u v =
        u  ≡⟨ sym (f u) ⟩
        x  ≡⟨ f v ⟩∎
        v  ∎
  in
  Π-closure ext 1 λ _ →
  mono₁ 1 prop

------------------------------------------------------------------------
-- Σ-types

-- H-level′ is closed under Σ.

Σ-closure′ :
  ∀ {a b} {A : Type a} {B : A → Type b} n →
  H-level′ n A → (∀ x → H-level′ n (B x)) → H-level′ n (Σ A B)
Σ-closure′ {A} {B} zero (x , irrA) hB =
  ((x , proj₁ (hB x)) , λ p →
     (x       , proj₁ (hB x))          ≡⟨ elim (λ {x y} _ → _≡_ {A = Σ A B} (x , proj₁ (hB x))
                                                                            (y , proj₁ (hB y)))
                                               (λ _ → refl _)
                                               (irrA (proj₁ p)) ⟩
     (proj₁ p , proj₁ (hB (proj₁ p)))  ≡⟨ cong (_,_ (proj₁ p)) (proj₂ (hB (proj₁ p)) (proj₂ p)) ⟩∎
     p                                 ∎)
Σ-closure′ {B} (suc n) hA hB = λ p₁ p₂ →
  respects-surjection′ (_↔_.surjection Σ-≡,≡↔≡) n $
    Σ-closure′ n (hA (proj₁ p₁) (proj₁ p₂))
      (λ pr₁p₁≡pr₁p₂ →
         hB (proj₁ p₂) (subst B pr₁p₁≡pr₁p₂ (proj₂ p₁)) (proj₂ p₂))

-- H-level is closed under Σ.

Σ-closure : ∀ {a b} {A : Type a} {B : A → Type b} n →
            H-level n A → (∀ x → H-level n (B x)) → H-level n (Σ A B)
Σ-closure n hA hB =
  _⇔_.from H-level⇔H-level′
    (Σ-closure′ n (_⇔_.to H-level⇔H-level′ hA)
                  (_⇔_.to H-level⇔H-level′ ∘ hB))

opaque

  -- In the case of contractibility the codomain only needs to have
  -- the right h-level (0) for a single index.

  Σ-closure-contractible :
    ∀ {a b} {A : Type a} {B : A → Type b} →
    (c : Contractible A) → Contractible (B (proj₁ c)) →
    Contractible (Σ A B)
  Σ-closure-contractible {B} cA (b , irrB) = Σ-closure 0 cA cB
    where
    cB : ∀ a → Contractible (B a)
    cB a =
      subst B (proj₂ cA a) b , λ b′ →

      subst B (proj₂ cA a) b                                ≡⟨ cong (subst B (proj₂ cA a)) $
                                                                irrB (subst B (sym $ proj₂ cA a) b′) ⟩
      subst B (proj₂ cA a) (subst B (sym $ proj₂ cA a) b′)  ≡⟨ subst-subst-sym _ _ _ ⟩∎

      b′                                                    ∎

  -- H-level is closed under _×_.

  ×-closure : ∀ {a b} {A : Type a} {B : Type b} n →
              H-level n A → H-level n B → H-level n (A × B)
  ×-closure n hA hB = Σ-closure n hA (const hB)

  -- If B a is inhabited for all a, and Σ A B has h-level n, then A
  -- also has h-level n.
  --
  -- One cannot, in general, replace ∀ a → B a with ∀ a → ∥ B a ∥ (see
  -- Circle.¬-generalised-proj₁-closure). However, this is possible if
  -- B is constant (see H-level.Truncation.Propositional.H-level-×₁).

  proj₁-closure :
    ∀ {a b} {A : Type a} {B : A → Type b} →
    (∀ a → B a) →
    ∀ n → H-level n (Σ A B) → H-level n A
  proj₁-closure {A} {B} inhabited = respects-surjection surj
    where
    surj : Σ A B ↠ A
    surj = record
      { logical-equivalence = record
        { to   = proj₁
        ; from = λ x → x , inhabited x
        }
      ; right-inverse-of = refl
      }

  -- If A is inhabited and A × B has h-level n, then B also has
  -- h-level n.

  proj₂-closure :
    ∀ {a b} {A : Type a} {B : Type b} →
    A →
    ∀ n → H-level n (A × B) → H-level n B
  proj₂-closure {A} {B} inhabited = respects-surjection surj
    where
    surj : A × B ↠ B
    surj = record
      { logical-equivalence = record
        { to   = proj₂
        ; from = λ x → inhabited , x
        }
      ; right-inverse-of = refl
      }

------------------------------------------------------------------------
-- Logical equivalences, split surjections and bijections

-- H-level n is closed under the type formers _⇔_, _↠_ and _↔_
-- (assuming extensionality).

⇔-closure :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  ∀ n → H-level n A → H-level n B → H-level n (A ⇔ B)
⇔-closure {a} {b} ext n hA hB =
  respects-surjection
    (record
       { logical-equivalence = record
         { to   = _
         ; from = λ A⇔B → _⇔_.to A⇔B , _⇔_.from A⇔B
         }
       ; right-inverse-of = λ _ → refl _
       })
    n
    (×-closure n
       (Π-closure (lower-extensionality b a ext) n (λ _ → hB))
       (Π-closure (lower-extensionality a b ext) n (λ _ → hA)))

↠-closure :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  ∀ n → H-level n A → H-level n B → H-level n (A ↠ B)
↠-closure {a} {b} ext n hA hB =
  respects-surjection
    (record
       { logical-equivalence = record
         { to   = _
         ; from = λ A↠B → _↠_.logical-equivalence A↠B ,
                          _↠_.right-inverse-of A↠B
         }
       ; right-inverse-of = λ _ → refl _
       })
    n
    (Σ-closure n (⇔-closure ext n hA hB) λ _ →
     Π-closure (lower-extensionality a a ext) n λ _ →
     ⇒≡ _ hB)

↔-closure :
  ∀ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  ∀ n → H-level n A → H-level n B → H-level n (A ↔ B)
↔-closure {a} {b} ext n hA hB =
  respects-surjection
    (record
       { logical-equivalence = record
         { to   = _
         ; from = λ A↔B → _↔_.surjection A↔B ,
                          _↔_.left-inverse-of A↔B
         }
       ; right-inverse-of = λ _ → refl _
       })
    n
    (Σ-closure n (↠-closure ext n hA hB) λ _ →
     Π-closure (lower-extensionality b b ext) n λ _ →
     ⇒≡ _ hA)

------------------------------------------------------------------------
-- Lifted types

-- All H-levels are closed under lifting.

↑-closure : ∀ {a b} {A : Type a} n → H-level n A → H-level n (↑ b A)
↑-closure =
  respects-surjection (_↔_.surjection (Bijection.inverse ↑↔))

-- All H-levels are also closed under removal of lifting.

↑⁻¹-closure : ∀ {a b} {A : Type a} n → H-level n (↑ b A) → H-level n A
↑⁻¹-closure = respects-surjection (_↔_.surjection ↑↔)

------------------------------------------------------------------------
-- W-types

-- W-types are isomorphic to Σ-types containing W-types.

W-unfolding : ∀ {a b} {A : Type a} {B : A → Type b} →
              W A B ↔ ∃ λ (x : A) → B x → W A B
W-unfolding = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ w → headᵂ w , tailᵂ w
      ; from = uncurry sup
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = left-inverse-of
  }
  where
  left-inverse-of : (w : W _ _) → sup (headᵂ w) (tailᵂ w) ≡ w
  left-inverse-of (sup x f) = refl (sup x f)

opaque

  -- Equality between elements of a W-type can be proved using a pair
  -- of equalities (assuming extensionality).

  W-≡,≡↠≡ : ∀ {a b} {A : Type a} {B : A → Type b} →
            Extensionality b (a ⊔ b) →
            ∀ {x y} {f : B x → W A B} {g : B y → W A B} →
            (∃ λ (p : x ≡ y) → ∀ i → f i ≡ g (subst B p i)) ↠
            (sup x f ≡ sup y g)
  W-≡,≡↠≡ {a} {A} {B} ext {x} {y} {f} {g} =
    (∃ λ (p : x ≡ y) → ∀ i → f i ≡ g (subst B p i))        ↠⟨ Surjection.∃-cong lemma ⟩
    (∃ λ (p : x ≡ y) → subst (λ x → B x → W A B) p f ≡ g)  ↠⟨ _↔_.surjection Σ-≡,≡↔≡ ⟩
    (_≡_ {A = ∃ λ (x : A) → B x → W A B} (x , f) (y , g))  ↠⟨ ↠-≡ (_↔_.surjection (Bijection.inverse (W-unfolding {A = A} {B = B}))) ⟩□
    (sup x f ≡ sup y g)                                    □
    where
    lemma : (p : x ≡ y) →
            (∀ i → f i ≡ g (subst B p i)) ↠
            (subst (λ x → B x → W A B) p f ≡ g)
    lemma p = elim
      (λ {x y} p → (f : B x → W A B) (g : B y → W A B) →
                   (∀ i → f i ≡ g (subst B p i)) ↠
                   (subst (λ x → B x → W A B) p f ≡ g))
      (λ x f g →
         (∀ i → f i ≡ g (subst B (refl x) i))        ↠⟨ subst (λ h → (∀ i → f i ≡ g (h i)) ↠ (∀ i → f i ≡ g i))
                                                              (sym (apply-ext (lower-extensionality lzero a ext) (subst-refl B)))
                                                              Surjection.id ⟩
         (∀ i → f i ≡ g i)                           ↠⟨ ext-surj ext ⟩
         (f ≡ g)                                     ↠⟨ subst (λ h → (f ≡ g) ↠ (h ≡ g))
                                                              (sym $ subst-refl (λ x' → B x' → W A B) f)
                                                              Surjection.id ⟩□
         (subst (λ x → B x → W A B) (refl x) f ≡ g)  □)
      p f g

  -- H-level is not closed under W.

  ¬-W-closure-contractible : ∀ {a b} →
    ¬ (∀ {A : Type a} {B : A → Type b} →
       Contractible A → (∀ x → Contractible (B x)) →
       Contractible (W A B))
  ¬-W-closure-contractible closure =
    inhabited⇒W-empty (const (lift tt)) $
    proj₁ $
    closure (↑-closure 0 ⊤-contractible)
            (const (↑-closure 0 ⊤-contractible))

  ¬-W-closure : ∀ {a b} →
    ¬ (∀ {A : Type a} {B : A → Type b} n →
       H-level n A → (∀ x → H-level n (B x)) → H-level n (W A B))
  ¬-W-closure closure = ¬-W-closure-contractible (closure 0)

  -- However, all positive h-levels are closed under W (assuming
  -- extensionality).

  W-closure′ :
    ∀ {a b} {A : Type a} {B : A → Type b} →
    Extensionality b (a ⊔ b) →
    ∀ n → H-level′ (1 + n) A → H-level′ (1 + n) (W A B)
  W-closure′ {A} {B} ext n h = closure
    where
    closure : (x y : W A B) → H-level′ n (x ≡ y)
    closure (sup x f) (sup y g) =
      respects-surjection′ (W-≡,≡↠≡ ext) n $
        Σ-closure′ n (h x y) (λ _ →
          Π-closure′ ext n (λ i → closure (f _) (g _)))

  W-closure :
    ∀ {a b} {A : Type a} {B : A → Type b} →
    Extensionality b (a ⊔ b) →
    ∀ n → H-level (1 + n) A → H-level (1 + n) (W A B)
  W-closure ext n h =
    _⇔_.from H-level⇔H-level′
      (W-closure′ ext n (_⇔_.to H-level⇔H-level′ h))

------------------------------------------------------------------------
-- H-levels

opaque

  -- Contractible is /not/ a comonad in the category of types and
  -- functions, because map cannot be defined, but we can at least
  -- define the following functions.

  counit : ∀ {a} {A : Type a} → Contractible A → A
  counit = proj₁

  cojoin : ∀ {a} {A : Type a} →
           Extensionality a a →
           Contractible A → Contractible (Contractible A)
  cojoin {A} ext contr = contr₃
    where
    x : A
    x = proj₁ contr

    contr₁ : Contractible (∀ y → x ≡ y)
    contr₁ = Π-closure′ ext 0 (mono₁′ 0 contr x)

    contr₂ : (x : A) → Contractible (∀ y → x ≡ y)
    contr₂ x =
      subst (λ x → Contractible (∀ y → x ≡ y)) (proj₂ contr x) contr₁

    contr₃ : Contractible (∃ λ (x : A) → ∀ y → x ≡ y)
    contr₃ = Σ-closure 0 contr contr₂

  -- Contractible is not necessarily contractible.

  ¬-Contractible-contractible :
    ¬ ({A : Type} → Contractible (Contractible A))
  ¬-Contractible-contractible contr = proj₁ $ proj₁ $ contr {A = ⊥}

  -- Contractible is propositional (assuming extensionality).

  Contractible-propositional :
    ∀ {a} {A : Type a} →
    Extensionality a a →
    Is-proposition (Contractible A)
  Contractible-propositional ext =
    [inhabited⇒contractible]⇒propositional (cojoin ext)

  -- H-level′ is closed under λ P → For-iterated-equality n P A.

  H-level′-For-iterated-equality :
    ∀ {p A} {P : Type p → Type p} →
    Extensionality p p →
    ∀ m n →
    (∀ {A} → H-level′ m (P A)) →
    H-level′ m (For-iterated-equality n P A)
  H-level′-For-iterated-equality ext m zero    hyp = hyp
  H-level′-For-iterated-equality ext m (suc n) hyp =
    Π-closure′ ext m λ _ →
    Π-closure′ ext m λ _ →
    H-level′-For-iterated-equality ext m n hyp

  -- A variant of the previous result.

  H-level′-For-iterated-equality′ :
    ∀ {p A} {P : Type p → Type p} →
    Extensionality p p →
    ∀ m n {o} →
    H-level′ (n + o) A →
    (∀ {A} → H-level′ o A → H-level′ m (P A)) →
    H-level′ m (For-iterated-equality n P A)
  H-level′-For-iterated-equality′ ext m zero    hyp₁ hyp₂ = hyp₂ hyp₁
  H-level′-For-iterated-equality′ ext m (suc n) hyp₁ hyp₂ =
    Π-closure′ ext m λ _ →
    Π-closure′ ext m λ _ →
    H-level′-For-iterated-equality′ ext m n (hyp₁ _ _) hyp₂

  -- H-level is closed under λ P → For-iterated-equality n P A.

  H-level-For-iterated-equality :
    ∀ {p A} {P : Type p → Type p} →
    Extensionality p p →
    ∀ m n →
    (∀ {A} → H-level m (P A)) →
    H-level m (For-iterated-equality n P A)
  H-level-For-iterated-equality ext m n hyp =
    _⇔_.from H-level⇔H-level′ $
    H-level′-For-iterated-equality ext m n $
    _⇔_.to H-level⇔H-level′ hyp

  -- A variant of the previous result.

  H-level-For-iterated-equality′ :
    ∀ {p A} {P : Type p → Type p} →
    Extensionality p p →
    ∀ m n {o} →
    H-level (n + o) A →
    (∀ {A} → H-level o A → H-level m (P A)) →
    H-level m (For-iterated-equality n P A)
  H-level-For-iterated-equality′ ext m n hyp₁ hyp₂ =
    _⇔_.from (H-level⇔H-level′ {n = m}) $
    H-level′-For-iterated-equality′ ext m n
      (_⇔_.to H-level⇔H-level′ hyp₁)
      (_⇔_.to H-level⇔H-level′ ∘ hyp₂ ∘ _⇔_.from H-level⇔H-level′)

  -- H-level′ is pointwise propositional (assuming extensionality).

  H-level′-propositional :
    ∀ {a} → Extensionality a a →
    ∀ {A : Type a} n → Is-proposition (H-level′ n A)
  H-level′-propositional ext n =
    _⇔_.from (H-level⇔H-level′ {n = 1}) $
    H-level′-For-iterated-equality ext 1 n $
    _⇔_.to (H-level⇔H-level′ {n = 1}) $
    Contractible-propositional ext

  -- The property Is-proposition A is a proposition (assuming
  -- extensionality).
  --
  -- This result is proved in the HoTT book (first edition,
  -- Lemma 3.3.5).

  Is-proposition-propositional :
    ∀ {a} {A : Type a} → Extensionality a a →
    Is-proposition (Is-proposition A)
  Is-proposition-propositional ext = [inhabited⇒+]⇒+ 0 λ p →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    ⇒≡ 1 p

  -- All h-levels are propositional (assuming extensionality).

  H-level-propositional :
    ∀ {a} → Extensionality a a →
    ∀ {A : Type a} n → Is-proposition (H-level n A)
  H-level-propositional ext zero =
    Contractible-propositional ext
  H-level-propositional ext (suc zero) =
    Is-proposition-propositional ext
  H-level-propositional ext (suc (suc n)) =
    implicit-Π-closure ext 1 λ x →
    implicit-Π-closure ext 1 λ y →
    H-level-propositional ext {A = x ≡ y} (suc n)

  -- Uniqueness-of-identity-proofs is pointwise propositional
  -- (assuming extensionality).

  UIP-propositional :
    ∀ {ℓ} → Extensionality (lsuc ℓ) ℓ →
    Is-proposition (Uniqueness-of-identity-proofs ℓ)
  UIP-propositional ext =
    implicit-Π-closure ext 1 λ A →
    H-level-propositional (lower-extensionality _ lzero ext) 2

------------------------------------------------------------------------
-- Is-equivalence

-- Π A preserves surjections (assuming extensionality).

∀-cong-↠ :
  ∀ {a p₁ p₂} {A : Type a} {P₁ : A → Type p₁} {P₂ : A → Type p₂} →
  Extensionality a (p₁ ⊔ p₂) →
  (∀ x → P₁ x ↠ P₂ x) →
  ((x : A) → P₁ x) ↠ ((x : A) → P₂ x)
∀-cong-↠ {p₁} ext P₁↠P₂ = record
  { logical-equivalence = equiv
  ; right-inverse-of    = right-inverse-of′
  }
  where
  equiv = record
    { to   = _↠_.to   (P₁↠P₂ _) ∘_
    ; from = _↠_.from (P₁↠P₂ _) ∘_
    }

  opaque

    right-inverse-of′ : ∀ f → _⇔_.to equiv (_⇔_.from equiv f) ≡ f
    right-inverse-of′ f =
      apply-ext (lower-extensionality lzero p₁ ext) λ x →
        _↠_.to (P₁↠P₂ x) (_↠_.from (P₁↠P₂ x) (f x))  ≡⟨ _↠_.right-inverse-of (P₁↠P₂ x) (f x) ⟩∎
        f x                                          ∎

opaque

  -- Is-equivalence f is a proposition (assuming extensionality).

  Is-equivalence-propositional :
    ∀ {a b} {A : Type a} {B : Type b} {f : A → B} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    Is-proposition (Is-equivalence f)
  Is-equivalence-propositional {a} {b} {A} {B} {f} ext =
    [inhabited⇒+]⇒+ 0 λ eq →
    mono₁ 0 $
    respects-surjection
      ((∃ λ ((f⁻¹ , f-f⁻¹) : ∃ λ f⁻¹ → ∀ x → f (f⁻¹ x) ≡ x) →
        ∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
            ∀ x → cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x))              ↠⟨ _↔_.surjection $ Bijection.inverse Bijection.Σ-assoc ⟩□

       Is-equivalence f                                        □)
      0 $
    Σ-closure 0 (lemma₁ eq) (uncurry $ lemma₂ eq)
    where
    ext₁ : Extensionality b b
    ext₁ = lower-extensionality a a ext

    ext₁′ : Extensionality b a
    ext₁′ = lower-extensionality a b ext

    ext-↠ :
      {A B : Type b} {f g : A → B} →
      f ≡ g ↠ (∀ x → f x ≡ g x)
    ext-↠ =
      _↔_.surjection $
      HA.Is-equivalence→↔ $
      Extensionality.extensionality ext₁

    lemma₁ :
      Is-equivalence f →
      Contractible (∃ λ (f⁻¹ : B → A) → ∀ x → f (f⁻¹ x) ≡ x)
    lemma₁ (f⁻¹ , f-f⁻¹ , f⁻¹-f , f-f⁻¹-f) =
      respects-surjection
        ((∃ λ f⁻¹ → f ∘ f⁻¹ ≡ id)         ↠⟨ (Surjection.∃-cong λ _ → ext-↠) ⟩□
         (∃ λ f⁻¹ → ∀ x → f (f⁻¹ x) ≡ x)  □)
        0 $
      Preimage.bijection⁻¹-contractible
        (record
           { surjection = record
             { logical-equivalence = record
               { to   = f   ∘_
               ; from = f⁻¹ ∘_
               }
             ; right-inverse-of = λ g → apply-ext ext₁ λ x →
                 f (f⁻¹ (g x))  ≡⟨ f-f⁻¹ (g x) ⟩∎
                 g x            ∎
             }
           ; left-inverse-of = λ g → apply-ext ext₁′ λ x →
               f⁻¹ (f (g x))  ≡⟨ f⁻¹-f (g x) ⟩∎
               g x            ∎
           })
        id

    ext₂ : Extensionality a (a ⊔ b)
    ext₂ = lower-extensionality b lzero ext

    lemma₂ :
      Is-equivalence f →
      (f⁻¹ : B → A) (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
      Contractible
        (∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
           ∀ x → cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x))
    lemma₂ eq f⁻¹ f-f⁻¹ =
      respects-surjection
        ((∀ x → (f⁻¹ (f x) , f-f⁻¹ (f x)) ≡ (x , refl (f x)))             ↠⟨ (∀-cong-↠ ext₂ λ _ → _↔_.surjection $
                                                                              Bijection.inverse Bijection.Σ-≡,≡↔≡) ⟩
         (∀ x → ∃ λ f⁻¹-f →
                  subst (λ y → f y ≡ f x) f⁻¹-f (f-f⁻¹ (f x)) ≡
                  refl (f x))                                             ↠⟨ (∀-cong-↠ ext₂ λ x → Surjection.∃-cong λ f⁻¹-f →
                                                                              elim (λ {A B} _ → A ↠ B) (λ _ → Surjection.id) (

             subst (λ y → f y ≡ f x) f⁻¹-f (f-f⁻¹ (f x)) ≡ refl (f x)           ≡⟨ cong (_≡ _) $ subst-∘ _ _ _ ⟩
             subst (_≡ f x) (cong f f⁻¹-f) (f-f⁻¹ (f x)) ≡ refl (f x)           ≡⟨ cong (_≡ _) subst-trans-sym ⟩
             trans (sym (cong f f⁻¹-f)) (f-f⁻¹ (f x)) ≡ refl (f x)              ≡⟨ [trans≡]≡[≡trans-symˡ] _ _ _ ⟩
             f-f⁻¹ (f x) ≡ trans (sym (sym (cong f f⁻¹-f))) (refl (f x))        ≡⟨ cong (_ ≡_) $ trans-reflʳ _ ⟩
             f-f⁻¹ (f x) ≡ sym (sym (cong f f⁻¹-f))                             ≡⟨ cong (_ ≡_) $ sym-sym _ ⟩∎
             f-f⁻¹ (f x) ≡ cong f f⁻¹-f                                         ∎)) ⟩

         (∀ x → ∃ λ f⁻¹-f → f-f⁻¹ (f x) ≡ cong f f⁻¹-f)                   ↠⟨ (∀-cong-↠ ext₂ λ _ → Surjection.∃-cong λ _ →
                                                                              _↔_.surjection Bijection.≡-comm) ⟩

         (∀ x → ∃ λ f⁻¹-f → cong f f⁻¹-f ≡ f-f⁻¹ (f x))                   ↠⟨ _↔_.surjection Bijection.ΠΣ-comm ⟩□

         (∃ λ f⁻¹-f → ∀ x → cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x))               □)
        0 $
      Π-closure ext₂ 0 λ x →
      ⇒≡ 0 $
      _⇔_.to HA.Is-equivalence⇔Is-equivalence-CP eq (f x)

-- If the domain of f is contractible and the codomain is
-- propositional, then Is-equivalence f is contractible (assuming
-- extensionality).

Is-equivalence-sometimes-contractible :
  ∀ {a b} {A : Type a} {B : Type b} {f : A → B} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Contractible A → Is-proposition B →
  Contractible (Is-equivalence f)
Is-equivalence-sometimes-contractible
  {a} {b} ext A-contr B-prop =
  Σ-closure 0 (Π-closure ext-b-a 0 λ _ → A-contr)              λ _ →
  Σ-closure 0 (Π-closure ext-b-b 0 λ _ → +⇒≡ B-prop)   λ _ →
  Σ-closure 0 (Π-closure ext-a-a 0 λ _ → ⇒≡ 0 A-contr) λ _ →
  Π-closure ext-a-b 0 λ _ → ⇒≡ 0 $ +⇒≡ B-prop
  where
  ext-a-a : Extensionality a a
  ext-a-a = lower-extensionality b b ext

  ext-a-b : Extensionality a b
  ext-a-b = lower-extensionality b a ext

  ext-b-a : Extensionality b a
  ext-b-a = lower-extensionality a b ext

  ext-b-b : Extensionality b b
  ext-b-b = lower-extensionality a a ext

------------------------------------------------------------------------
-- Function extensionality

-- Extensionality is propositional (assuming extensionality).

Extensionality-propositional :
  ∀ {a p} →
  Extensionality (lsuc (a ⊔ p)) (a ⊔ lsuc p) →
  Is-proposition (Extensionality a p)
Extensionality-propositional {a} {p} ext =
  respects-surjection surj 1 $
  implicit-Π-closure ext₁ 1 λ _ →
  implicit-Π-closure ext₂ 1 λ _ →
  implicit-Π-closure ext₃ 1 λ _ →
  implicit-Π-closure ext₃ 1 λ _ →
  Is-equivalence-propositional ext₃
  where
  ext₁ : Extensionality (lsuc a) (a ⊔ lsuc p)
  ext₁ = lower-extensionality (lsuc p) lzero ext

  ext₂ : Extensionality (a ⊔ lsuc p) (a ⊔ p)
  ext₂ = lower-extensionality (lsuc a) (lsuc p) ext

  ext₃ : Extensionality (a ⊔ p) (a ⊔ p)
  ext₃ = lower-extensionality _ (lsuc p) ext

  surj :
    ({A : Type a} {P : A → Type p} → Extensionality′ A P) ↠
    Extensionality a p
  surj = record
    { logical-equivalence = record
      { to   = λ ext → record { extensionality = ext }
      ; from = Extensionality.extensionality
      }
    ; right-inverse-of = λ where
        record { extensionality = ext } → refl _
    }

------------------------------------------------------------------------
-- CP.Is-equivalence

opaque

  -- CP.Is-equivalence f is a proposition, assuming extensional
  -- equality.

  Is-equivalence-CP-propositional :
    ∀ {a b} {A : Type a} {B : Type b} {f : A → B} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    Is-proposition (CP.Is-equivalence f)
  Is-equivalence-CP-propositional {a} ext =
    Π-closure (lower-extensionality a lzero ext) 1 λ _ →
    Contractible-propositional ext

  -- If the domain is contractible and the codomain is propositional,
  -- then CP.Is-equivalence f is contractible.

  Is-equivalence-CP-sometimes-contractible :
    ∀ {a b} {A : Type a} {B : Type b} {f : A → B} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    Contractible A → Is-proposition B →
    Contractible (CP.Is-equivalence f)
  Is-equivalence-CP-sometimes-contractible {a} ext A-contr B-prop =
    Π-closure (lower-extensionality a lzero ext) 0 λ _ →
    cojoin ext (Σ-closure 0 A-contr (λ _ → +⇒≡ B-prop))

  -- CP.Is-equivalence f is not always contractible.

  Is-equivalence-CP-not-always-contractible₁ :
    ∀ {a b} →
    ∃ λ (A : Type a) → ∃ λ (B : Type b) → ∃ λ (f : A → B) →
      Is-proposition A × Contractible B ×
      ¬ Contractible (CP.Is-equivalence f)
  Is-equivalence-CP-not-always-contractible₁ =
    ⊥ ,
    ↑ _ ⊤ ,
    const (lift tt) ,
    ⊥-propositional ,
    ↑-closure 0 ⊤-contractible ,
    λ c → ⊥-elim (proj₁ (proj₁ (proj₁ c (lift tt))))

  Is-equivalence-CP-not-always-contractible₂ :
    ∀ {a b} →
    ∃ λ (A : Type a) → ∃ λ (B : Type b) → ∃ λ (f : A → B) →
      Contractible A × Is-set B ×
      ¬ Contractible (CP.Is-equivalence f)
  Is-equivalence-CP-not-always-contractible₂ =
    ↑ _ ⊤ ,
    ↑ _ Bool ,
    const (lift true) ,
    ↑-closure 0 ⊤-contractible ,
    ↑-closure 2 Bool-set ,
    λ c → Bool.true≢false (cong lower
            (proj₂ (proj₁ (proj₁ c (lift false)))))

------------------------------------------------------------------------
-- Binary sums

opaque

  -- Binary sums can be expressed using Σ and Bool (with large
  -- elimination).

  sum-as-pair : ∀ {a b} {A : Type a} {B : Type b} →
                (A ⊎ B) ↔ (∃ λ (x : Bool) → if x then ↑ b A else ↑ a B)
  sum-as-pair {a} {b} {A} {B} = record
    { surjection = record
      { logical-equivalence = record
        { to   = to
        ; from = from
        }
      ; right-inverse-of = to∘from
      }
    ; left-inverse-of = [ refl ∘ inj₁ {B = B} , refl ∘ inj₂ {A = A} ]
    }
    where
    to : A ⊎ B → (∃ λ (x : Bool) → if x then ↑ b A else ↑ a B)
    to = [ _,_ true ∘ lift , _,_ false ∘ lift ]

    from : (∃ λ (x : Bool) → if x then ↑ b A else ↑ a B) → A ⊎ B
    from (true  , x) = inj₁ $ lower x
    from (false , y) = inj₂ $ lower y

    to∘from : (y : ∃ λ x → if x then ↑ b A else ↑ a B) →
              to (from y) ≡ y
    to∘from (true  , x) = refl _
    to∘from (false , y) = refl _

  -- H-level is not closed under _⊎_.

  ¬-⊎-propositional : ∀ {a b} {A : Type a} {B : Type b} →
                      A → B → ¬ Is-proposition (A ⊎ B)
  ¬-⊎-propositional x y hA⊎B = ⊎.inj₁≢inj₂ $ hA⊎B (inj₁ x) (inj₂ y)

  ¬-⊎-closure : ∀ {a b} →
    ¬ (∀ {A : Type a} {B : Type b} n →
       H-level n A → H-level n B → H-level n (A ⊎ B))
  ¬-⊎-closure ⊎-closure =
    ¬-⊎-propositional (lift tt) (lift tt) $
    mono₁ 0 $
    ⊎-closure 0 (↑-closure 0 ⊤-contractible)
                (↑-closure 0 ⊤-contractible)

  -- However, all levels greater than or equal to 2 are closed under
  -- _⊎_.

  ⊎-closure :
    ∀ {a b} {A : Type a} {B : Type b} n →
    H-level (2 + n) A → H-level (2 + n) B → H-level (2 + n) (A ⊎ B)
  ⊎-closure {a} {b} {A} {B} n hA hB =
    respects-surjection
      (_↔_.surjection $ Bijection.inverse sum-as-pair)
      (2 + n)
      (Σ-closure (2 + n) Bool-2+n if-2+n)
    where
    Bool-2+n : H-level (2 + n) Bool
    Bool-2+n = mono (m≤m+n 2 n) Bool-set

    if-2+n : (x : Bool) → H-level (2 + n) (if x then ↑ b A else ↑ a B)
    if-2+n true  = respects-surjection
                     (_↔_.surjection $ Bijection.inverse ↑↔)
                     (2 + n) hA
    if-2+n false = respects-surjection
                     (_↔_.surjection $ Bijection.inverse ↑↔)
                     (2 + n) hB

  -- Furthermore, if A and B are propositions and mutually exclusive,
  -- then A ⊎ B is a proposition.

  ⊎-closure-propositional :
    ∀ {a b} {A : Type a} {B : Type b} →
    (A → B → ⊥₀) →
    Is-proposition A → Is-proposition B → Is-proposition (A ⊎ B)
  ⊎-closure-propositional A→B→⊥ A-prop B-prop = λ where
    (inj₁ a₁) (inj₁ a₂) → cong inj₁ (A-prop a₁ a₂)
    (inj₁ a₁) (inj₂ b₂) → ⊥-elim (A→B→⊥ a₁ b₂)
    (inj₂ b₁) (inj₁ a₂) → ⊥-elim (A→B→⊥ a₂ b₁)
    (inj₂ b₁) (inj₂ b₂) → cong inj₂ (B-prop b₁ b₂)

  -- All levels greater than or equal to 2 are also closed under
  -- Maybe.

  Maybe-closure :
    ∀ {a} {A : Type a} n →
    H-level (2 + n) A → H-level (2 + n) (Maybe A)
  Maybe-closure n h =
    ⊎-closure n (mono (zero≤ (2 + n)) ⊤-contractible) h

  -- Equality with nothing is a proposition.

  Equality-⊎-nothing-propositional :
    ∀ {a} {A : Type a} {x : Maybe A} →
    Is-proposition (Equality-⊎ x nothing)
  Equality-⊎-nothing-propositional {x = just _}  = ⊥-propositional
  Equality-⊎-nothing-propositional {x = nothing} =
    ↑-closure 1 $ mono₁ 0 $ ⇒≡ 0 ⊤-contractible

  -- Equality with nothing is a proposition.

  ≡-nothing-propositional :
    ∀ {a} {A : Type a} {x : Maybe A} →
    Is-proposition (x ≡ nothing)
  ≡-nothing-propositional =
    respects-surjection (_↔_.surjection $ Bijection.inverse ≡↔⊎)
      1 Equality-⊎-nothing-propositional

  -- T is pointwise propositional.

  T-propositional :
    ∀ {a b} {A : Type a} {B : Type b} →
    (x : A ⊎ B) → Is-proposition (T x)
  T-propositional (inj₁ _) = mono₁ 0 ⊤-contractible
  T-propositional (inj₂ _) = ⊥-propositional

  -- Is-proposition is closed under Dec (assuming extensionality).

  Dec-closure-propositional :
    ∀ {a} {A : Type a} →
    Extensionality a lzero →
    Is-proposition A → Is-proposition (Dec A)
  Dec-closure-propositional {A} ext p = λ where
    (yes  a) (yes  a′) → cong yes $ p a a′
    (yes  a) (no  ¬a)  → ⊥-elim (¬a a)
    (no  ¬a) (yes  a)  → ⊥-elim (¬a a)
    (no  ¬a) (no  ¬a′) → cong no $ ¬-propositional ext ¬a ¬a′

  -- Is-proposition is also closed under _Xor_ (assuming
  -- extensionality).

  Xor-closure-propositional :
    ∀ {a b} {A : Type a} {B : Type b} →
    Extensionality (a ⊔ b) (# 0) →
    Is-proposition A → Is-proposition B →
    Is-proposition (A Xor B)
  Xor-closure-propositional {a = ℓa} {b = ℓb} {A} {B}
                            ext pA pB = λ where
    (inj₁ (a , ¬b)) (inj₂ (¬a  , b))   → ⊥-elim (¬a a)
    (inj₂ (¬a , b)) (inj₁ (a   , ¬b))  → ⊥-elim (¬b b)
    (inj₁ (a , ¬b)) (inj₁ (a′  , ¬b′)) →
      cong₂ (λ x y → inj₁ (x , y))
        (pA a a′)
        (apply-ext (lower-extensionality ℓa _ ext) λ b → ⊥-elim (¬b b))
    (inj₂ (¬a , b)) (inj₂ (¬a′ , b′)) →
      cong₂ (λ x y → inj₂ (x , y))
        (apply-ext (lower-extensionality ℓb _ ext) λ a → ⊥-elim (¬a a))
        (pB b b′)

  -- However, H-level is not closed under _Xor_.

  ¬-Xor-closure-contractible : ∀ {a b} →
    ¬ ({A : Type a} {B : Type b} →
       Contractible A → Contractible B → Contractible (A Xor B))
  ¬-Xor-closure-contractible closure
    with proj₁ $ closure (↑-closure 0 ⊤-contractible)
                         (↑-closure 0 ⊤-contractible)
  ... | inj₁ (_ , ¬⊤) = ¬⊤ _
  ... | inj₂ (¬⊤ , _) = ¬⊤ _

-- Alternative definition of ⊎-closure (for Type₀).

module Alternative-proof where

  opaque

    -- Is-set is closed under _⊎_, by an argument similar to the one
    -- Hedberg used to prove that decidable equality implies
    -- uniqueness of identity proofs.

    ⊎-closure-set : {A B : Type} →
                    Is-set A → Is-set B → Is-set (A ⊎ B)
    ⊎-closure-set {A} {B} A-set B-set = DUIP.constant⇒set c
      where
      c : (x y : A ⊎ B) → ∃ λ (f : x ≡ y → x ≡ y) → DUIP.Constant f
      c (inj₁ x) (inj₁ y) = (cong inj₁ ∘ ⊎.cancel-inj₁ , λ p q → cong (cong inj₁) $ A-set (⊎.cancel-inj₁ p) (⊎.cancel-inj₁ q))
      c (inj₂ x) (inj₂ y) = (cong inj₂ ∘ ⊎.cancel-inj₂ , λ p q → cong (cong inj₂) $ B-set (⊎.cancel-inj₂ p) (⊎.cancel-inj₂ q))
      c (inj₁ x) (inj₂ y) = (⊥-elim ∘ ⊎.inj₁≢inj₂       , λ _ → ⊥-elim ∘ ⊎.inj₁≢inj₂)
      c (inj₂ x) (inj₁ y) = (⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym , λ _ → ⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym)

    -- H-level is closed under _⊎_ for other levels greater than or equal
    -- to 2 too.

    ⊎-closure′ :
      ∀ {A B : Type} n →
      H-level (2 + n) A → H-level (2 + n) B → H-level (2 + n) (A ⊎ B)
    ⊎-closure′         zero    = ⊎-closure-set
    ⊎-closure′ {A} {B} (suc n) = clos
      where
      clos : H-level (3 + n) A → H-level (3 + n) B → H-level (3 + n) (A ⊎ B)
      clos hA hB {x = inj₁ x} {y = inj₁ y}         = respects-surjection (_↔_.surjection ≡↔inj₁≡inj₁) (2 + n) hA
      clos hA hB {x = inj₂ x} {y = inj₂ y}         = respects-surjection (_↔_.surjection ≡↔inj₂≡inj₂) (2 + n) hB
      clos hA hB {x = inj₁ x} {y = inj₂ y} {x = p} = ⊥-elim (⊎.inj₁≢inj₂ p)
      clos hA hB {x = inj₂ x} {y = inj₁ y} {x = p} = ⊥-elim (⊎.inj₁≢inj₂ (sym p))
