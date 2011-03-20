------------------------------------------------------------------------
-- Closure properties for h-levels
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module H-level.Closure
  {reflexive} (eq : Equality-with-J reflexive) where

private
  module Bijection where
    import Bijection; open Bijection eq public
open Bijection hiding (id; _∘_)
open Derived-definitions-and-properties eq
private
  module DUIP where
    import Equality.Decidable-UIP as DUIP; open DUIP eq public
import Equality.Decision-procedures as ED; open ED eq
import Equality.Groupoid as EG
private module G {A : Set} = EG.Groupoid eq (EG.groupoid eq A)
import Equality.Tactic as Tactic; open Tactic eq
open import Equivalence hiding (id; _∘_)
import H-level; open H-level eq
open import Prelude
private
  module Surjection where
    import Surjection; open Surjection eq public
open Surjection hiding (id; _∘_)

------------------------------------------------------------------------
-- The unit type

-- The unit type is contractible.

⊤-contractible : Contractible ⊤
⊤-contractible = (_ , λ _ → refl _)

------------------------------------------------------------------------
-- The empty type

abstract

  -- The empty type is not contractible.

  ¬-⊥-contractible : ¬ Contractible ⊥
  ¬-⊥-contractible = ⊥-elim ∘ proj₁

  -- The empty type is propositional.

  ⊥-propositional : Propositional ⊥
  ⊥-propositional =
    _⇔_.from propositional⇔irrelevant (λ x → ⊥-elim x)

  -- Thus any uninhabited type is also propositional.

  ⊥↠uninhabited : ∀ {A} → ¬ A → ⊥ ↠ A
  ⊥↠uninhabited ¬A = record
    { equivalence = record
      { to   = ⊥-elim
      ; from = ¬A
      }
    ; right-inverse-of = ⊥-elim ∘ ¬A
    }

  uninhabited-propositional : ∀ {A} → ¬ A → Propositional A
  uninhabited-propositional ¬A =
    respects-surjection (⊥↠uninhabited ¬A) 1 ⊥-propositional

------------------------------------------------------------------------
-- Booleans

abstract

  -- The booleans are not propositional.

  ¬-Bool-propositional : ¬ Propositional Bool
  ¬-Bool-propositional propositional =
    Bool.true≢false $
    (_⇔_.to propositional⇔irrelevant propositional) true false

  -- The booleans form a set.

  Bool-set : Is-set Bool
  Bool-set = decidable⇒set Bool._≟_

------------------------------------------------------------------------
-- Π-types

-- Closure of contractibility under Π A is equivalent to having
-- extensional equality for functions from A.

Π-closure-contractible⇔extensionality :
  ∀ {A} →
  ({B : A → Set} →
   (∀ x → Contractible (B x)) → Contractible ((x : A) → B x)) ⇔
  (∀ {B} → Extensionality A B)
Π-closure-contractible⇔extensionality {A} = record
  { to   = ⇒
  ; from = λ ext cB →
      ((λ x → proj₁ (cB x)) , λ f → ext λ x → proj₂ (cB x) (f x))
  }
  where
  ⇒ : ({B : A → Set} →
       (∀ x → Contractible (B x)) → Contractible ((x : A) → B x)) →
      (∀ {B} → Extensionality A B)
  ⇒ closure {B} {f} {g} f≡g =
    f                                     ≡⟨ sym $ cong (λ c → λ x → proj₁ (c x)) $
                                               proj₂ contractible (λ x → (f x , f≡g x)) ⟩
    (λ x → proj₁ (proj₁ contractible x))  ≡⟨ cong (λ c → λ x → proj₁ (c x)) $
                                               proj₂ contractible (λ x → (g x , refl (g x))) ⟩∎
    g                                     ∎
    where
    contractible : Contractible ((x : A) → Singleton (g x))
    contractible = closure (singleton-contractible ∘ g)

abstract

  -- Given (generalised) extensionality one can define an
  -- extensionality proof which is well-behaved.

  extensionality⇒well-behaved-extensionality :
    ∀ {A} → (∀ {B} → Extensionality A B) →
    ∀ {B} → Well-behaved-extensionality A B
  extensionality⇒well-behaved-extensionality {A} ext {B} =
    (λ {_} → ext′) , λ f →
      ext′ (refl ∘ f)  ≡⟨ G.right-inverse _ ⟩∎
      refl f           ∎
    where
    ext′ : Extensionality A B
    ext′ = to (from ext)
      where open _⇔_ Π-closure-contractible⇔extensionality

  -- Given extensionality there is a surjection from ∀ x → f x ≡ g x
  -- to f ≡ g.

  ext-surj : ∀ {A} → (∀ {B} → Extensionality A B) →
             ∀ {B : A → Set} {f g : (x : A) → B x} →
             (∀ x → f x ≡ g x) ↠ (f ≡ g)
  ext-surj {A} ext {f} {g} = record
    { equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of =
        elim (λ {f g} f≡g → to (from f≡g) ≡ f≡g) λ h →
          proj₁ ext′ (from (refl h))  ≡⟨ cong (proj₁ ext′) (proj₁ ext′ λ x →
                                           prove (Cong (λ h → h x) (Refl {x = h})) Refl (refl _)) ⟩
          proj₁ ext′ (refl ∘ h)       ≡⟨ proj₂ ext′ h ⟩∎
          refl h                      ∎
    }
    where
    ext′ : ∀ {B} → Well-behaved-extensionality A B
    ext′ = extensionality⇒well-behaved-extensionality ext

    to : ∀ {f g} → (∀ x → f x ≡ g x) → f ≡ g
    to = proj₁ ext′

    from : ∀ {f g} → f ≡ g → (∀ x → f x ≡ g x)
    from f≡g x = cong (λ h → h x) f≡g

  -- H-level is closed under Π A, assuming extensionality for
  -- functions from A.

  Π-closure : ∀ {A} →
              (∀ {B} → Extensionality A B) →
              ∀ {B : A → Set} n →
              (∀ x → H-level n (B x)) → H-level n ((x : A) → B x)
  Π-closure ext zero =
    _⇔_.from Π-closure-contractible⇔extensionality ext
  Π-closure ext (suc n) = λ h f g →
    respects-surjection (ext-surj ext) n $
      Π-closure ext n (λ x → h x (f x) (g x))

  -- This also applies to the implicit function space.

  implicit-Π-closure :
    ∀ {A} →
    (∀ {B} → Extensionality A B) →
    ∀ {B : A → Set} n →
    (∀ x → H-level n (B x)) → H-level n ({x : A} → B x)
  implicit-Π-closure {A} ext {B} n =
    respects-surjection surj n ∘ Π-closure ext n
    where
    surj : ((x : A) → B x) ↠ ({x : A} → B x)
    surj = record
      { equivalence = record
        { to   = λ f {x} → f x
        ; from = λ f x → f {x}
        }
      ; right-inverse-of = refl
      }

  -- Negated types are propositional, assuming extensionality.

  ¬-propositional :
    ∀ {A} → (∀ {B} → Extensionality A B) → Propositional (¬ A)
  ¬-propositional ext = Π-closure ext 1 (λ _ → ⊥-propositional)

------------------------------------------------------------------------
-- Σ-types

-- Equality between pairs can be expressed as a pair of equalities.

Σ-≡,≡↔≡ : ∀ {A B} {p₁ p₂ : Σ A B} →
          (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
             subst B p (proj₂ p₁) ≡ proj₂ p₂) ↔
          (p₁ ≡ p₂)
Σ-≡,≡↔≡ {A} {B} = record
  { surjection = record
    { equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = elim (λ p≡q → to (from p≡q) ≡ p≡q) λ x →
        let lem = subst-refl B (proj₂ x) in
        to (from (refl x))                          ≡⟨ cong to (elim-refl from-P _) ⟩
        to (refl (proj₁ x) , lem)                   ≡⟨ cong (λ f → f lem) (elim-refl to-P _) ⟩
        cong (_,_ (proj₁ x)) (trans (sym lem) lem)  ≡⟨ cong (cong (_,_ (proj₁ x))) $ G.right-inverse lem ⟩
        cong (_,_ (proj₁ x)) (refl (proj₂ x))       ≡⟨ cong-refl (_,_ (proj₁ x)) ⟩∎
        refl x                                      ∎
    }
  ; left-inverse-of = λ p → elim
      (λ {x₁ x₂} x₁≡x₂ →
         ∀ {y₁ y₂} (y₁′≡y₂ : subst B x₁≡x₂ y₁ ≡ y₂) →
         from (to (x₁≡x₂ , y₁′≡y₂)) ≡ (x₁≡x₂ , y₁′≡y₂))
      (λ x {y₁} y₁′≡y₂ → elim
         (λ {y₁ y₂} (y₁≡y₂ : y₁ ≡ y₂) →
            (y₁′≡y₂ : subst B (refl x) y₁ ≡ y₂) →
            y₁≡y₂ ≡ trans (sym $ subst-refl B y₁) y₁′≡y₂ →
            from (to (refl x , y₁′≡y₂)) ≡ (refl x , y₁′≡y₂))
         (λ y y′≡y eq →
          let lem = subst-refl B y in
          from (to (refl x , y′≡y))                   ≡⟨ cong (λ f → from (f y′≡y)) $ elim-refl to-P _ ⟩
          from (cong (_,_ x) (trans (sym lem) y′≡y))  ≡⟨ cong (from ∘ cong (_,_ x)) $ sym eq ⟩
          from (cong (_,_ x) (refl y))                ≡⟨ cong from $ cong-refl (_,_ x) ⟩
          from (refl (x , y))                         ≡⟨ elim-refl from-P _ ⟩
          (refl x , lem)                              ≡⟨ cong (_,_ (refl x)) (
             lem                                           ≡⟨ prove (Lift lem) (Trans (Lift lem) Refl) (refl _) ⟩
             trans lem (refl _)                            ≡⟨ cong (trans lem) eq ⟩
             trans lem (trans (sym lem) y′≡y)              ≡⟨ prove (Trans (Lift lem) (Trans (Sym (Lift lem)) (Lift y′≡y)))
                                                                    (Trans (Trans (Lift lem) (Sym (Lift lem))) (Lift y′≡y))
                                                                    (refl _) ⟩
             trans (trans lem (sym lem)) y′≡y              ≡⟨ cong (λ p → trans p y′≡y) $ G.left-inverse lem ⟩
             trans (refl _) y′≡y                           ≡⟨ prove (Trans Refl (Lift y′≡y)) (Lift y′≡y) (refl _) ⟩∎
             y′≡y                                          ∎) ⟩∎
          (refl x , y′≡y)                             ∎)
         (trans (sym $ subst-refl B y₁) y₁′≡y₂)
         y₁′≡y₂
         (refl _))
      (proj₁ p) (proj₂ p)
  }
  where
  from-P = λ {p₁ p₂ : Σ A B} (_ : p₁ ≡ p₂) →
             ∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
               subst B p (proj₂ p₁) ≡ proj₂ p₂

  from : {p₁ p₂ : Σ A B} →
         p₁ ≡ p₂ →
         ∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
           subst B p (proj₂ p₁) ≡ proj₂ p₂
  from = elim from-P (λ p → refl _ , subst-refl B _)

  to-P = λ {x₁ y₁ : A} (p : x₁ ≡ y₁) → {x₂ : B x₁} {y₂ : B y₁} →
           subst B p x₂ ≡ y₂ →
           _≡_ {A = Σ A B} (x₁ , x₂) (y₁ , y₂)

  to : {p₁ p₂ : Σ A B} →
       (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
          subst B p (proj₂ p₁) ≡ proj₂ p₂) →
       p₁ ≡ p₂
  to (p , q) = elim
    to-P
    (λ z₁ {x₂} {y₂} x₂≡y₂ → cong (_,_ z₁) (
       x₂                    ≡⟨ sym $ subst-refl B x₂ ⟩
       subst B (refl z₁) x₂  ≡⟨ x₂≡y₂ ⟩∎
       y₂                    ∎))
    p q

abstract

  -- H-level is closed under Σ.

  Σ-closure : ∀ {A} {B : A → Set} n →
              H-level n A → (∀ x → H-level n (B x)) → H-level n (Σ A B)
  Σ-closure {A} {B} zero (x , irrA) hB =
    ((x , proj₁ (hB x)) , λ p →
       (x       , proj₁ (hB x))          ≡⟨ elim (λ {x y} _ → _≡_ {A = Σ A B} (x , proj₁ (hB x))
                                                                              (y , proj₁ (hB y)))
                                                 (λ _ → refl _)
                                                 (irrA (proj₁ p)) ⟩
       (proj₁ p , proj₁ (hB (proj₁ p)))  ≡⟨ cong (_,_ (proj₁ p)) (proj₂ (hB (proj₁ p)) (proj₂ p)) ⟩∎
       p                                 ∎)
  Σ-closure {A} {B} (suc n) hA hB = λ p₁ p₂ →
    respects-surjection (_↔_.surjection Σ-≡,≡↔≡) n $
      Σ-closure n (hA (proj₁ p₁) (proj₁ p₂))
        (λ pr₁p₁≡pr₁p₂ →
           hB (proj₁ p₂) (subst B pr₁p₁≡pr₁p₂ (proj₂ p₁)) (proj₂ p₂))

  -- H-level is closed under _×_.

  ×-closure : ∀ {A B} n → H-level n A → H-level n B → H-level n (A × B)
  ×-closure n hA hB = Σ-closure n hA (const hB)

------------------------------------------------------------------------
-- W-types

-- W-types are isomorphic to Σ-types containing W-types.

W-unfolding : ∀ {A B} → W A B ↔ ∃ λ (x : A) → B x → W A B
W-unfolding = record
  { surjection = record
    { equivalence = record
      { to   = λ w → head w , tail w
      ; from = uncurry sup
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = left-inverse-of
  }
  where
  left-inverse-of : (w : W _ _) → sup (head w) (tail w) ≡ w
  left-inverse-of (sup x f) = refl (sup x f)

abstract

  -- Equality between elements of a W-type can be proved using a pair
  -- of equalities (assuming extensionality).

  W-≡,≡↠≡ : ∀ {A} {B : A → Set} →
            (∀ {x C} → Extensionality (B x) C) →
            ∀ {x y} {f : B x → W A B} {g : B y → W A B} →
            (∃ λ (p : x ≡ y) → ∀ i → f i ≡ g (subst B p i)) ↠
            (sup x f ≡ sup y g)
  W-≡,≡↠≡ {A} {B} ext {x} {y} {f} {g} =
    (∃ λ (p : x ≡ y) → ∀ i → f i ≡ g (subst B p i))        ↠⟨ Surjection.∃-cong lemma ⟩
    (∃ λ (p : x ≡ y) → subst (λ x → B x → W A B) p f ≡ g)  ↠⟨ _↔_.surjection Σ-≡,≡↔≡ ⟩
    (_≡_ {A = ∃ λ (x : A) → B x → W A B} (x , f) (y , g))  ↠⟨ ↠-≡ $ _↔_.surjection $ Bijection.inverse W-unfolding ⟩∎
    (sup x f ≡ sup y g)                                    ∎
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
                                                              (sym $ ext $ subst-refl B)
                                                              Surjection.id ⟩
         (∀ i → f i ≡ g i)                           ↠⟨ ext-surj ext ⟩
         (f ≡ g)                                     ↠⟨ subst (λ h → (f ≡ g) ↠ (h ≡ g))
                                                              (sym $ subst-refl (λ x' → B x' → W A B) f)
                                                              Surjection.id ⟩∎
         (subst (λ x → B x → W A B) (refl x) f ≡ g)  ∎)
      p f g

  -- H-level is not closed under W.

  ¬-W-closure-contractible :
    ¬ (∀ {A B} →
       Contractible A → (∀ x → Contractible (B x)) →
       Contractible (W A B))
  ¬-W-closure-contractible closure =
    inhabited⇒W-empty (const tt) $
    proj₁ $
    closure ⊤-contractible (const ⊤-contractible)

  ¬-W-closure :
    ¬ (∀ {A B} n →
       H-level n A → (∀ x → H-level n (B x)) → H-level n (W A B))
  ¬-W-closure closure = ¬-W-closure-contractible (closure 0)

  -- However, all positive h-levels are closed under W, assuming that
  -- equality is sufficiently extensional.

  W-closure :
    ∀ {A} {B : A → Set} →
    (∀ {x C} → Extensionality (B x) C) →
    ∀ n → H-level (1 + n) A → H-level (1 + n) (W A B)
  W-closure {A} {B} ext n h = closure
    where
    closure : (x y : W A B) → H-level n (x ≡ y)
    closure (sup x f) (sup y g) =
      respects-surjection (W-≡,≡↠≡ ext) n $
        Σ-closure n (h x y) (λ _ →
          Π-closure ext n (λ i → closure (f _) (g _)))

------------------------------------------------------------------------
-- M-types

-- Bisimilarity for M-types.

infix 4 _≡M_

data _≡M_ {A B} : M A B → M A B → Set where
  dns : ∀ {x x′ f f′}
        (x≡x′ : x ≡ x′)
        (f≡f′ : ∀ b → ∞ (♭ (f b) ≡M ♭ (f′ (subst B x≡x′ b)))) →
        dns x f ≡M dns x′ f′

-- Equality implies bisimilarity.

≡⇒≡M : ∀ {A B} {x y : M A B} → x ≡ y → x ≡M y
≡⇒≡M {B = B} {dns x f} {dns y g} p =
  dns (proj₁ q) (λ b → ♯ ≡⇒≡M (proj₂ q b))
  where
  q = elim (λ {m m′} m≡m′ →
              ∃ λ (x≡y : pɐǝɥ m ≡ pɐǝɥ m′) →
                  ∀ b → lıɐʇ m b ≡ lıɐʇ m′ (subst B x≡y b))
           (λ m → refl (pɐǝɥ m) , λ b →
              lıɐʇ m b                            ≡⟨ cong (lıɐʇ m) (sym $ subst-refl B _) ⟩∎
              lıɐʇ m (subst B (refl (pɐǝɥ m)) b)  ∎)
           p

abstract

  -- If we assume a notion of extensionality (bisimilarity implies
  -- equality) then Contractible is closed under M.

  M-closure-contractible :
    ∀ {A B} → ({m m′ : M A B} → m ≡M m′ → m ≡ m′) →
    Contractible A → Contractible (M A B)
  M-closure-contractible {A} {B} ext (x , irrA) = (m , ext ∘ irr)
    where
    m : M A B
    m = dns x (λ _ → ♯ m)

    irr : ∀ m′ → m ≡M m′
    irr (dns x′ f) = dns (irrA x′) (λ _ → ♯ irr _)

  -- The same applies to Propositional.

  M-closure-propositional :
    ∀ {A B} →
    ({m m′ : M A B} → m ≡M m′ → m ≡ m′) →
    Propositional A → Propositional (M A B)
  M-closure-propositional {A} {B} ext p =
    _⇔_.from propositional⇔irrelevant (λ x y → ext $ irrelevant x y)
    where
    irrelevant : (x y : M A B) → x ≡M y
    irrelevant (dns x f) (dns y g) =
      dns (proj₁ $ p x y) (λ _ → ♯ irrelevant _ _)

------------------------------------------------------------------------
-- H-levels

abstract

  -- Contractible is /not/ a comonad in the category of types and
  -- functions, because map cannot be defined, but we can at least
  -- define the following functions.

  counit : ∀ {A} → Contractible A → A
  counit = proj₁

  cojoin : ∀ {A} → (∀ {B} → Extensionality A B) →
           Contractible A → Contractible (Contractible A)
  cojoin ext contr = contr₃
    where
    x = proj₁ contr

    contr₁ : Contractible (∀ y → x ≡ y)
    contr₁ = Π-closure ext 0 (mono₁ 0 contr x)

    contr₂ : ∀ x → Contractible (∀ y → x ≡ y)
    contr₂ x =
      subst (λ x → Contractible (∀ y → x ≡ y)) (proj₂ contr x) contr₁

    contr₃ : Contractible (∃ λ x → ∀ y → x ≡ y)
    contr₃ = Σ-closure 0 contr contr₂

  -- Contractible is not necessarily contractible.

  ¬-Contractible-contractible :
    ¬ (∀ {A} → Contractible (Contractible A))
  ¬-Contractible-contractible contr = proj₁ $ proj₁ $ contr {A = ⊥}

  -- Contractible is propositional (assuming extensionality).

  Contractible-propositional :
    ∀ {A} → (∀ {B} → Extensionality A B) →
    Propositional (Contractible A)
  Contractible-propositional ext =
    [inhabited⇒contractible]⇒propositional (cojoin ext)

  -- All h-levels are propositional (assuming extensionality).

  H-level-propositional :
    ∀ {A} → (∀ {A B} → Extensionality A B) →
    ∀ n → Propositional (H-level n A)
  H-level-propositional     ext zero    = Contractible-propositional ext
  H-level-propositional {A} ext (suc n) =
    Π-closure ext 1 λ x →
    Π-closure ext 1 λ y →
    H-level-propositional {x ≡ y} ext n

------------------------------------------------------------------------
-- Binary sums

abstract

  -- Binary sums can be expressed using Σ and Bool (with large
  -- elimination).

  sum-as-pair : ∀ {A B} → (A ⊎ B) ↔ (∃ λ b → if b then A else B)
  sum-as-pair {A} {B} = record
    { surjection = record
      { equivalence = record
        { to   = to
        ; from = from
        }
      ; right-inverse-of = to∘from
      }
    ; left-inverse-of  = [ refl ∘ inj₁ , refl ∘ inj₂ ]
    }
    where
    to = [ _,_ true , _,_ false ]

    from : (∃ λ b → if b then A else B) → A ⊎ B
    from (true  , x) = inj₁ x
    from (false , y) = inj₂ y

    to∘from : ∀ x → to (from x) ≡ x
    to∘from (true  , x) = refl _
    to∘from (false , y) = refl _

  -- H-level is not closed under _⊎_.

  ¬-⊎-propositional : ∀ {A B} → A → B → ¬ Propositional (A ⊎ B)
  ¬-⊎-propositional x y hA⊎B =
    ⊎.inj₁≢inj₂ $ proj₁ $ hA⊎B (inj₁ x) (inj₂ y)

  ¬-⊎-closure :
    ¬ (∀ {A B} n → H-level n A → H-level n B → H-level n (A ⊎ B))
  ¬-⊎-closure ⊎-closure =
    ¬-⊎-propositional tt tt $
    mono₁ 0 $
    ⊎-closure 0 ⊤-contractible ⊤-contractible

  -- However, all levels greater than or equal to 2 are closed under
  -- _⊎_.

  ⊎-closure :
    ∀ {A B} n →
    H-level (2 + n) A → H-level (2 + n) B → H-level (2 + n) (A ⊎ B)
  ⊎-closure {A} {B} n hA hB =
    respects-surjection
      (_↔_.surjection $ Bijection.inverse sum-as-pair)
      (2 + n)
      (Σ-closure (2 + n) Bool-2+n if-2+n)
    where
    Bool-2+n : H-level (2 + n) Bool
    Bool-2+n = mono (m≤m+n 2 n) Bool-set

    if-2+n : ∀ b → H-level (2 + n) (if b then A else B)
    if-2+n true  = hA
    if-2+n false = hB

  -- Furthermore Propositional is closed under Dec (assuming
  -- extensionality).

  Dec-closure-propositional :
    ∀ {A} → (∀ {B} → Extensionality A B) →
    Propositional A → Propositional (Dec A)
  Dec-closure-propositional {A} ext p =
    _⇔_.from propositional⇔irrelevant irrelevant
    where
    irrelevant : Proof-irrelevant (Dec A)
    irrelevant (inj₁  a) (inj₁  a′) = cong inj₁ $ proj₁ $ p a a′
    irrelevant (inj₁  a) (inj₂ ¬a)  = ⊥-elim (¬a a)
    irrelevant (inj₂ ¬a) (inj₁  a)  = ⊥-elim (¬a a)
    irrelevant (inj₂ ¬a) (inj₂ ¬a′) =
      cong inj₂ $ proj₁ $ ¬-propositional ext ¬a ¬a′

  -- Alternative definition of ⊎-closure.

  module Alternative-proof where

    -- Is-set is closed under _⊎_, by an argument similar to the one
    -- Hedberg used to prove that decidable equality implies
    -- uniqueness of identity proofs.

    ⊎-closure-set : ∀ {A B} → Is-set A → Is-set B → Is-set (A ⊎ B)
    ⊎-closure-set {A} {B} A-set B-set =
      _⇔_.from set⇔UIP (DUIP.constant⇒UIP c)
      where
      c : (x y : A ⊎ B) → ∃ λ (f : x ≡ y → x ≡ y) → DUIP.Constant f
      c (inj₁ x) (inj₁ y) = (cong inj₁ ∘ ⊎.cancel-inj₁ , λ p q → cong (cong inj₁) $ proj₁ $ A-set x y (⊎.cancel-inj₁ p) (⊎.cancel-inj₁ q))
      c (inj₂ x) (inj₂ y) = (cong inj₂ ∘ ⊎.cancel-inj₂ , λ p q → cong (cong inj₂) $ proj₁ $ B-set x y (⊎.cancel-inj₂ p) (⊎.cancel-inj₂ q))
      c (inj₁ x) (inj₂ y) = (⊥-elim ∘ ⊎.inj₁≢inj₂       , λ _ → ⊥-elim ∘ ⊎.inj₁≢inj₂)
      c (inj₂ x) (inj₁ y) = (⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym , λ _ → ⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym)

    -- H-level is closed under _⊎_ for other levels greater than or equal
    -- to 2 too.

    ⊎-closure′ :
      ∀ {A B} n →
      H-level (2 + n) A → H-level (2 + n) B → H-level (2 + n) (A ⊎ B)
    ⊎-closure′         zero    = ⊎-closure-set
    ⊎-closure′ {A} {B} (suc n) = clos
      where
      mutual
        clos : H-level (3 + n) A → H-level (3 + n) B → H-level (3 + n) (A ⊎ B)
        clos hA hB (inj₁ x) (inj₁ y) = respects-surjection surj₁ (2 + n) (hA x y)
        clos hA hB (inj₂ x) (inj₂ y) = respects-surjection surj₂ (2 + n) (hB x y)
        clos hA hB (inj₁ x) (inj₂ y) = ⊥-elim ∘ ⊎.inj₁≢inj₂
        clos hA hB (inj₂ x) (inj₁ y) = ⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym

        surj₁ : ∀ {x y} → (x ≡ y) ↠ _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y)
        surj₁ {x} {y} = record
          { equivalence = record
            { to   = cong inj₁
            ; from = ⊎.cancel-inj₁
            }
          ; right-inverse-of = λ ix≡iy →
              cong inj₁ (⊎.cancel-inj₁ ix≡iy)              ≡⟨ prove (Cong inj₁ (Cong [ id , const x ] (Lift ix≡iy)))
                                                                    (Cong f (Lift ix≡iy))
                                                                    (refl _) ⟩
              cong f ix≡iy                                 ≡⟨ cong-lemma f p ix≡iy _ _ f≡id ⟩
              trans (refl _) (trans ix≡iy $ sym (refl _))  ≡⟨ prove (Trans Refl (Trans (Lift ix≡iy) (Sym Refl)))
                                                                    (Lift ix≡iy)
                                                                    (refl _) ⟩∎
              ix≡iy                                        ∎
          }
          where
          f : A ⊎ B → A ⊎ B
          f = inj₁ ∘ [ id , const x ]

          p : A ⊎ B → Bool
          p = [ const true , const false ]

          f≡id : ∀ z → T (p z) → f z ≡ z
          f≡id (inj₁ x) = const (refl (inj₁ x))
          f≡id (inj₂ y) = ⊥-elim

        surj₂ : ∀ {x y} → (x ≡ y) ↠ _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y)
        surj₂ {x} {y} = record
          { equivalence = record
            { to   = cong inj₂
            ; from = ⊎.cancel-inj₂
            }
          ; right-inverse-of = λ ix≡iy →
              cong inj₂ (⊎.cancel-inj₂ ix≡iy)              ≡⟨ prove (Cong inj₂ (Cong [ const x , id ] (Lift ix≡iy)))
                                                                    (Cong f (Lift ix≡iy))
                                                                    (refl _) ⟩
              cong f ix≡iy                                 ≡⟨ cong-lemma f p ix≡iy _ _ f≡id ⟩
              trans (refl _) (trans ix≡iy $ sym (refl _))  ≡⟨ prove (Trans Refl (Trans (Lift ix≡iy) (Sym Refl)))
                                                                    (Lift ix≡iy)
                                                                    (refl _) ⟩∎
              ix≡iy                                        ∎
          }
          where
          f : A ⊎ B → A ⊎ B
          f = inj₂ ∘ [ const x , id ]

          p : A ⊎ B → Bool
          p = [ const false , const true ]

          f≡id : ∀ z → T (p z) → f z ≡ z
          f≡id (inj₁ x) = ⊥-elim
          f≡id (inj₂ y) = const (refl (inj₂ y))

        -- If f z evaluates to z for a decidable set of values which
        -- includes x and y, do we have
        --
        --   cong f x≡y ≡ x≡y
        --
        -- for any x≡y : x ≡ y? The answer is yes, but cong-lemma only
        -- captures this statement indirectly. (Note that the equation
        -- above is not well-typed if f is a variable.) If cong-lemma
        -- is instantiated properly with the various components above,
        -- then we get
        --
        --   cong f x≡y ≡ trans … (trans x≡y (sym …)),
        --
        -- where the two occurrences of … evaluate to reflexivity
        -- proofs.

        cong-lemma : ∀ {A} (f : A → A) (p : A → Bool) {x y : A}
                     (x≡y : x ≡ y) (px : T (p x)) (py : T (p y))
                     (f≡id : ∀ z → T (p z) → f z ≡ z) →
                     cong f x≡y ≡
                     trans (f≡id x px) (trans x≡y $ sym (f≡id y py))
        cong-lemma {A} f p =
          elim (λ {x y} x≡y →
                  (px : T (p x)) (py : T (p y))
                  (f≡id : ∀ z → T (p z) → f z ≡ z) →
                  cong f x≡y ≡
                  trans (f≡id x px) (trans x≡y $ sym (f≡id y py)))
               (λ x px px′ f≡id → helper x (p x) px px′ (f≡id x))
          where
          helper :
            (x : A) (b : Bool) (px px′ : T b)
            (f≡id : T b → f x ≡ x) →
            cong f (refl x) ≡
            trans (f≡id px) (trans (refl x) $ sym (f≡id px′))
          helper x false px _ f≡id = ⊥-elim px
          helper x true  _  _ f≡id =
            cong f (refl x)                                 ≡⟨ prove (Cong f Refl) Refl (refl _) ⟩
            refl (f x)                                      ≡⟨ sym $ G.left-inverse _ ⟩
            trans (f≡id _) (sym (f≡id _))                   ≡⟨ prove (Trans fx≡x (Sym fx≡x))
                                                                     (Trans fx≡x (Trans Refl (Sym fx≡x)))
                                                                     (refl _) ⟩∎
            trans (f≡id _) (trans (refl x) $ sym (f≡id _))  ∎
            where fx≡x = Lift (f≡id _)
