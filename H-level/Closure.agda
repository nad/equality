------------------------------------------------------------------------
-- Closure properties for h-levels
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module H-level.Closure
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection hiding (id; _∘_)
open Derived-definitions-and-properties eq
import Equality.Decidable-UIP eq as DUIP
open import Equality.Decision-procedures eq
open import H-level eq
open import Logical-equivalence hiding (id; _∘_)
open import Prelude
open import Surjection eq as Surjection hiding (id; _∘_)

------------------------------------------------------------------------
-- The unit type

-- The unit type is contractible.

⊤-contractible : Contractible ⊤
⊤-contractible = (_ , λ _ → refl _)

abstract

  -- A type is contractible iff it is in bijective correspondence with
  -- the unit type.

  contractible⇔⊤↔ : ∀ {a} {A : Set a} → Contractible A ⇔ (⊤ ↔ A)
  contractible⇔⊤↔ = λ {a} {A} → record
    { to   = contractible-isomorphic ⊤-contractible
    ; from = λ ⊤↔A → respects-surjection (_↔_.surjection ⊤↔A) 0
                                         ⊤-contractible
    }

------------------------------------------------------------------------
-- The empty type

abstract

  -- The empty type is not contractible.

  ¬-⊥-contractible : ∀ {ℓ} → ¬ Contractible (⊥ {ℓ = ℓ})
  ¬-⊥-contractible = ⊥-elim ∘ proj₁

  -- The empty type is propositional.

  ⊥-propositional : ∀ {ℓ} → Is-proposition (⊥ {ℓ = ℓ})
  ⊥-propositional =
    _⇔_.from propositional⇔irrelevant (λ x → ⊥-elim x)

  -- Thus any uninhabited type is also propositional.

  ⊥↔uninhabited : ∀ {a ℓ} {A : Set a} → ¬ A → ⊥ {ℓ = ℓ} ↔ A
  ⊥↔uninhabited ¬A = record
    { surjection = record
      { logical-equivalence = record
        { to   = ⊥-elim
        ; from = ⊥-elim ∘ ¬A
        }
      ; right-inverse-of = ⊥-elim ∘ ¬A
      }
    ; left-inverse-of = λ ()
    }

  uninhabited-propositional : ∀ {a} {A : Set a} →
                              ¬ A → Is-proposition A
  uninhabited-propositional ¬A =
    respects-surjection (_↔_.surjection $ ⊥↔uninhabited {ℓ = # 0} ¬A) 1
                        ⊥-propositional

------------------------------------------------------------------------
-- Booleans

abstract

  -- The booleans are not propositional.

  ¬-Bool-propositional : ¬ Is-proposition Bool
  ¬-Bool-propositional propositional =
    Bool.true≢false $
    (_⇔_.to propositional⇔irrelevant propositional) true false

  -- The booleans form a set.

  Bool-set : Is-set Bool
  Bool-set = DUIP.decidable⇒set Bool._≟_

------------------------------------------------------------------------
-- Natural numbers

abstract

  -- ℕ is not propositional.

  ¬-ℕ-propositional : ¬ Is-proposition ℕ
  ¬-ℕ-propositional ℕ-prop =
    ℕ.0≢+ $ _⇔_.to propositional⇔irrelevant ℕ-prop 0 1

  -- ℕ is a set.

  ℕ-set : Is-set ℕ
  ℕ-set = DUIP.decidable⇒set ℕ._≟_

------------------------------------------------------------------------
-- Π-types

-- Closure of contractibility under Π A is logically equivalent to
-- having extensional equality for functions from A.

Π-closure-contractible⇔extensionality :
  ∀ {a b} {A : Set a} →
  ({B : A → Set b} →
   (∀ x → Contractible (B x)) → Contractible ((x : A) → B x)) ⇔
  ({B : A → Set b} → Extensionality′ A B)
Π-closure-contractible⇔extensionality {b = b} {A} = record
  { to   = ⇒
  ; from = λ ext cB →
      ((λ x → proj₁ (cB x)) , λ f → ext λ x → proj₂ (cB x) (f x))
  }
  where
  ⇒ : ({B : A → Set b} →
       (∀ x → Contractible (B x)) → Contractible ((x : A) → B x)) →
      (∀ {B} → Extensionality′ A B)
  ⇒ closure {B} {f} {g} f≡g =
    f                                     ≡⟨ sym (cong (λ c → λ x → proj₁ (c x)) $
                                               proj₂ contractible (λ x → (f x , f≡g x))) ⟩
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
    ∀ {a b} {A : Set a} →
    ({B : A → Set b} → Extensionality′ A B) →
    {B : A → Set b} → Well-behaved-extensionality A B
  extensionality⇒well-behaved-extensionality {A = A} ext {B} =
    (λ {_} → ext′) , λ f →
      ext′ (refl ∘ f)  ≡⟨ trans-symˡ _ ⟩∎
      refl f           ∎
    where
    ext′ : Extensionality′ A B
    ext′ = to (from ext)
      where open _⇔_ Π-closure-contractible⇔extensionality

-- A potential inverse of extensionality. (See Equivalence for a proof
-- which shows that this function has an inverse, assuming
-- extensionality.)

ext⁻¹ : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
        f ≡ g → (∀ x → f x ≡ g x)
ext⁻¹ f≡g = λ x → cong (λ h → h x) f≡g

abstract

  -- "Evaluation rule" for ext⁻¹.

  ext⁻¹-refl : ∀ {a b} {A : Set a} {B : A → Set b}
               (f : (x : A) → B x) {x} →
               ext⁻¹ (refl f) x ≡ refl (f x)
  ext⁻¹-refl f {x} = cong-refl (λ h → h x) {x = f}

  -- Given extensionality there is a (split) surjection from
  -- ∀ x → f x ≡ g x to f ≡ g.

  ext-surj : ∀ {a b} {A : Set a} →
             ({B : A → Set b} → Extensionality′ A B) →
             {B : A → Set b} {f g : (x : A) → B x} →
             (∀ x → f x ≡ g x) ↠ (f ≡ g)
  ext-surj {b = b} {A} ext {B} = record
    { logical-equivalence = record
      { to   = to
      ; from = ext⁻¹
      }
    ; right-inverse-of =
        elim (λ {f g} f≡g → to (ext⁻¹ f≡g) ≡ f≡g) λ h →
          proj₁ ext′ (ext⁻¹ (refl h))  ≡⟨ cong (proj₁ ext′) (proj₁ ext′ λ _ →
                                            ext⁻¹-refl h) ⟩
          proj₁ ext′ (refl ∘ h)        ≡⟨ proj₂ ext′ h ⟩∎
          refl h                       ∎
    }
    where
    ext′ : {B : A → Set b} → Well-behaved-extensionality A B
    ext′ = extensionality⇒well-behaved-extensionality ext

    to : {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
    to = proj₁ ext′

  -- H-level is closed under Π A, assuming extensionality for
  -- functions from A.

  Π-closure : ∀ {a b} {A : Set a} →
              ({B : A → Set b} → Extensionality′ A B) →
              ∀ {B : A → Set b} n →
              (∀ x → H-level n (B x)) → H-level n ((x : A) → B x)
  Π-closure ext zero =
    _⇔_.from Π-closure-contractible⇔extensionality ext
  Π-closure ext (suc n) = λ h f g →
    respects-surjection (ext-surj ext) n $
      Π-closure ext n (λ x → h x (f x) (g x))

  -- This also applies to the implicit function space.

  implicit-Π-closure :
    ∀ {a b} {A : Set a} →
    ({B : A → Set b} → Extensionality′ A B) →
    ∀ {B : A → Set b} n →
    (∀ x → H-level n (B x)) → H-level n ({x : A} → B x)
  implicit-Π-closure {A = A} ext {B} n =
    respects-surjection
      (_↔_.surjection $ Bijection.inverse implicit-Π↔Π) n ∘
    Π-closure ext n

  -- Negated types are propositional, assuming extensionality.

  ¬-propositional :
    ∀ {a} {A : Set a} →
    ({B : A → Set} → Extensionality′ A B) →
    Is-proposition (¬ A)
  ¬-propositional ext = Π-closure ext 1 (λ _ → ⊥-propositional)

------------------------------------------------------------------------
-- Σ-types

abstract

  -- H-level is closed under Σ.

  Σ-closure : ∀ {a b} {A : Set a} {B : A → Set b} n →
              H-level n A → (∀ x → H-level n (B x)) → H-level n (Σ A B)
  Σ-closure {A = A} {B} zero (x , irrA) hB =
    ((x , proj₁ (hB x)) , λ p →
       (x       , proj₁ (hB x))          ≡⟨ elim (λ {x y} _ → _≡_ {A = Σ A B} (x , proj₁ (hB x))
                                                                              (y , proj₁ (hB y)))
                                                 (λ _ → refl _)
                                                 (irrA (proj₁ p)) ⟩
       (proj₁ p , proj₁ (hB (proj₁ p)))  ≡⟨ cong (_,_ (proj₁ p)) (proj₂ (hB (proj₁ p)) (proj₂ p)) ⟩∎
       p                                 ∎)
  Σ-closure {B = B} (suc n) hA hB = λ p₁ p₂ →
    respects-surjection (_↔_.surjection Σ-≡,≡↔≡) n $
      Σ-closure n (hA (proj₁ p₁) (proj₁ p₂))
        (λ pr₁p₁≡pr₁p₂ →
           hB (proj₁ p₂) (subst B pr₁p₁≡pr₁p₂ (proj₂ p₁)) (proj₂ p₂))

  -- H-level is closed under _×_.

  ×-closure : ∀ {a b} {A : Set a} {B : Set b} n →
              H-level n A → H-level n B → H-level n (A × B)
  ×-closure n hA hB = Σ-closure n hA (const hB)

------------------------------------------------------------------------
-- Lifted types

abstract

  -- All H-levels are closed under lifting.

  ↑-closure : ∀ {a b} {A : Set a} n → H-level n A → H-level n (↑ b A)
  ↑-closure =
    respects-surjection (_↔_.surjection (Bijection.inverse ↑↔))

------------------------------------------------------------------------
-- W-types

-- W-types are isomorphic to Σ-types containing W-types.

W-unfolding : ∀ {a b} {A : Set a} {B : A → Set b} →
              W A B ↔ ∃ λ (x : A) → B x → W A B
W-unfolding = record
  { surjection = record
    { logical-equivalence = record
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

  W-≡,≡↠≡ : ∀ {a b} {A : Set a} {B : A → Set b} →
            (∀ {x} {C : B x → Set (a ⊔ b)} → Extensionality′ (B x) C) →
            ∀ {x y} {f : B x → W A B} {g : B y → W A B} →
            (∃ λ (p : x ≡ y) → ∀ i → f i ≡ g (subst B p i)) ↠
            (sup x f ≡ sup y g)
  W-≡,≡↠≡ {a} {A = A} {B} ext {x} {y} {f} {g} =
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
                                                              (sym (lower-extensionality₂ a ext (subst-refl B)))
                                                              Surjection.id ⟩
         (∀ i → f i ≡ g i)                           ↠⟨ ext-surj ext ⟩
         (f ≡ g)                                     ↠⟨ subst (λ h → (f ≡ g) ↠ (h ≡ g))
                                                              (sym $ subst-refl (λ x' → B x' → W A B) f)
                                                              Surjection.id ⟩□
         (subst (λ x → B x → W A B) (refl x) f ≡ g)  □)
      p f g

  -- H-level is not closed under W.

  ¬-W-closure-contractible : ∀ {a b} →
    ¬ (∀ {A : Set a} {B : A → Set b} →
       Contractible A → (∀ x → Contractible (B x)) →
       Contractible (W A B))
  ¬-W-closure-contractible closure =
    inhabited⇒W-empty (const (lift tt)) $
    proj₁ $
    closure (↑-closure 0 ⊤-contractible)
            (const (↑-closure 0 ⊤-contractible))

  ¬-W-closure : ∀ {a b} →
    ¬ (∀ {A : Set a} {B : A → Set b} n →
       H-level n A → (∀ x → H-level n (B x)) → H-level n (W A B))
  ¬-W-closure closure = ¬-W-closure-contractible (closure 0)

  -- However, all positive h-levels are closed under W, assuming that
  -- equality is sufficiently extensional.

  W-closure :
    ∀ {a b} {A : Set a} {B : A → Set b} →
    (∀ {x} {C : B x → Set (a ⊔ b)} → Extensionality′ (B x) C) →
    ∀ n → H-level (1 + n) A → H-level (1 + n) (W A B)
  W-closure {A = A} {B} ext n h = closure
    where
    closure : (x y : W A B) → H-level n (x ≡ y)
    closure (sup x f) (sup y g) =
      respects-surjection (W-≡,≡↠≡ ext) n $
        Σ-closure n (h x y) (λ _ →
          Π-closure ext n (λ i → closure (f _) (g _)))

------------------------------------------------------------------------
-- H-levels

abstract

  -- Contractible is /not/ a comonad in the category of types and
  -- functions, because map cannot be defined, but we can at least
  -- define the following functions.

  counit : ∀ {a} {A : Set a} → Contractible A → A
  counit = proj₁

  cojoin : ∀ {a} {A : Set a} →
           ({B : A → Set a} → Extensionality′ A B) →
           Contractible A → Contractible (Contractible A)
  cojoin {A = A} ext contr = contr₃
    where
    x : A
    x = proj₁ contr

    contr₁ : Contractible (∀ y → x ≡ y)
    contr₁ = Π-closure ext 0 (mono₁ 0 contr x)

    contr₂ : (x : A) → Contractible (∀ y → x ≡ y)
    contr₂ x =
      subst (λ x → Contractible (∀ y → x ≡ y)) (proj₂ contr x) contr₁

    contr₃ : Contractible (∃ λ (x : A) → ∀ y → x ≡ y)
    contr₃ = Σ-closure 0 contr contr₂

  -- Contractible is not necessarily contractible.

  ¬-Contractible-contractible :
    ¬ ({A : Set} → Contractible (Contractible A))
  ¬-Contractible-contractible contr = proj₁ $ proj₁ $ contr {A = ⊥}

  -- Contractible is propositional (assuming extensionality).

  Contractible-propositional :
    ∀ {a} {A : Set a} →
    ({B : A → Set a} → Extensionality′ A B) →
    Is-proposition (Contractible A)
  Contractible-propositional ext =
    [inhabited⇒contractible]⇒propositional (cojoin ext)

  -- All h-levels are propositional (assuming extensionality).

  H-level-propositional :
    ∀ {a} → Extensionality a a →
    ∀ {A : Set a} n → Is-proposition (H-level n A)
  H-level-propositional     ext zero    = Contractible-propositional ext
  H-level-propositional {A} ext (suc n) =
    Π-closure ext 1 λ x →
    Π-closure ext 1 λ y →
    H-level-propositional ext {A = x ≡ y} n

------------------------------------------------------------------------
-- Binary sums

abstract

  -- Binary sums can be expressed using Σ and Bool (with large
  -- elimination).

  sum-as-pair : ∀ {a b} {A : Set a} {B : Set b} →
                (A ⊎ B) ↔ (∃ λ x → if x then ↑ b A else ↑ a B)
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
    to : A ⊎ B → (∃ λ x → if x then ↑ b A else ↑ a B)
    to = [ _,_ true ∘ lift , _,_ false ∘ lift ]

    from : (∃ λ x → if x then ↑ b A else ↑ a B) → A ⊎ B
    from (true  , x) = inj₁ $ lower x
    from (false , y) = inj₂ $ lower y

    to∘from : (y : ∃ λ x → if x then ↑ b A else ↑ a B) →
              to (from y) ≡ y
    to∘from (true  , x) = refl _
    to∘from (false , y) = refl _

  -- H-level is not closed under _⊎_.

  ¬-⊎-propositional : ∀ {a b} {A : Set a} {B : Set b} →
                      A → B → ¬ Is-proposition (A ⊎ B)
  ¬-⊎-propositional {A = A} {B} x y hA⊎B =
    ⊎.inj₁≢inj₂ {A = A} {B = B} $ proj₁ $ hA⊎B (inj₁ x) (inj₂ y)

  ¬-⊎-closure : ∀ {a b} →
    ¬ (∀ {A : Set a} {B : Set b} n →
       H-level n A → H-level n B → H-level n (A ⊎ B))
  ¬-⊎-closure ⊎-closure =
    ¬-⊎-propositional (lift tt) (lift tt) $
    mono₁ 0 $
    ⊎-closure 0 (↑-closure 0 ⊤-contractible)
                (↑-closure 0 ⊤-contractible)

  -- However, all levels greater than or equal to 2 are closed under
  -- _⊎_.

  ⊎-closure :
    ∀ {a b} {A : Set a} {B : Set b} n →
    H-level (2 + n) A → H-level (2 + n) B → H-level (2 + n) (A ⊎ B)
  ⊎-closure {a} {b} {A} {B} n hA hB =
    respects-surjection
      (_↔_.surjection $ Bijection.inverse sum-as-pair)
      (2 + n)
      (Σ-closure (2 + n) Bool-2+n if-2+n)
    where
    Bool-2+n : H-level (2 + n) Bool
    Bool-2+n = mono (m≤m+n 2 n) Bool-set

    if-2+n : ∀ x → H-level (2 + n) (if x then ↑ b A else ↑ a B)
    if-2+n true  = respects-surjection
                     (_↔_.surjection $ Bijection.inverse ↑↔)
                     (2 + n) hA
    if-2+n false = respects-surjection
                     (_↔_.surjection $ Bijection.inverse ↑↔)
                     (2 + n) hB

  -- Furthermore Is-proposition is closed under Dec (assuming
  -- extensionality).

  Dec-closure-propositional :
    ∀ {a} {A : Set a} →
    ({B : A → Set} → Extensionality′ A B) →
    Is-proposition A → Is-proposition (Dec A)
  Dec-closure-propositional {A = A} ext p =
    _⇔_.from propositional⇔irrelevant irrelevant
    where
    irrelevant : Proof-irrelevant (Dec A)
    irrelevant (inj₁  a) (inj₁  a′) = cong (inj₁ {B = ¬ A}) $ proj₁ $ p a a′
    irrelevant (inj₁  a) (inj₂ ¬a)  = ⊥-elim (¬a a)
    irrelevant (inj₂ ¬a) (inj₁  a)  = ⊥-elim (¬a a)
    irrelevant (inj₂ ¬a) (inj₂ ¬a′) =
      cong (inj₂ {A = A}) $ proj₁ $ ¬-propositional ext ¬a ¬a′

  -- Is-proposition is also closed under _Xor_ (assuming
  -- extensionality).

  Xor-closure-propositional :
    ∀ {a b} {A : Set a} {B : Set b} →
    Extensionality (a ⊔ b) (# 0) →
    Is-proposition A → Is-proposition B →
    Is-proposition (A Xor B)
  Xor-closure-propositional {ℓa} {ℓb} {A} {B} ext pA pB =
    _⇔_.from propositional⇔irrelevant irr
    where
    irr : (x y : A Xor B) → x ≡ y
    irr (inj₁ (a , ¬b)) (inj₂ (¬a  , b))   = ⊥-elim (¬a a)
    irr (inj₂ (¬a , b)) (inj₁ (a   , ¬b))  = ⊥-elim (¬b b)
    irr (inj₁ (a , ¬b)) (inj₁ (a′  , ¬b′)) =
      cong₂ (λ x y → inj₁ (x , y))
        (_⇔_.to propositional⇔irrelevant pA a a′)
        (lower-extensionality ℓa _ ext λ b → ⊥-elim (¬b b))
    irr (inj₂ (¬a , b)) (inj₂ (¬a′ , b′)) =
      cong₂ (λ x y → inj₂ (x , y))
        (lower-extensionality ℓb _ ext λ a → ⊥-elim (¬a a))
        (_⇔_.to propositional⇔irrelevant pB b b′)

  -- However, H-level is not closed under _Xor_.

  ¬-Xor-closure-contractible : ∀ {a b} →
    ¬ ({A : Set a} {B : Set b} →
       Contractible A → Contractible B → Contractible (A Xor B))
  ¬-Xor-closure-contractible closure
    with proj₁ $ closure (↑-closure 0 ⊤-contractible)
                         (↑-closure 0 ⊤-contractible)
  ... | inj₁ (_ , ¬⊤) = ¬⊤ _
  ... | inj₂ (¬⊤ , _) = ¬⊤ _

  -- Alternative definition of ⊎-closure (for Set₀).

  module Alternative-proof where

    -- Is-set is closed under _⊎_, by an argument similar to the one
    -- Hedberg used to prove that decidable equality implies
    -- uniqueness of identity proofs.

    ⊎-closure-set : {A B : Set} →
                    Is-set A → Is-set B → Is-set (A ⊎ B)
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
      ∀ {A B : Set} n →
      H-level (2 + n) A → H-level (2 + n) B → H-level (2 + n) (A ⊎ B)
    ⊎-closure′         zero    = ⊎-closure-set
    ⊎-closure′ {A} {B} (suc n) = clos
      where
      clos : H-level (3 + n) A → H-level (3 + n) B → H-level (3 + n) (A ⊎ B)
      clos hA hB (inj₁ x) (inj₁ y) = respects-surjection (_↔_.surjection ≡↔inj₁≡inj₁) (2 + n) (hA x y)
      clos hA hB (inj₂ x) (inj₂ y) = respects-surjection (_↔_.surjection ≡↔inj₂≡inj₂) (2 + n) (hB x y)
      clos hA hB (inj₁ x) (inj₂ y) = ⊥-elim ∘ ⊎.inj₁≢inj₂
      clos hA hB (inj₂ x) (inj₁ y) = ⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym
