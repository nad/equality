------------------------------------------------------------------------
-- Closure properties for h-levels
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

module H-level.Closure where

open import Bijection hiding (id; _∘_)
open import Equality
import Equality.Decidable-UIP as DUIP
import Equality.Groupoid as EG
private module G {A : Set} = EG.Groupoid (EG.groupoid {A = A})
import Equality.Tactic as Tactic; open Tactic.Eq
open import Equivalence hiding (id; _∘_)
open import H-level
open import Prelude
open import Surjection hiding (id; _∘_)

------------------------------------------------------------------------
-- The unit type

-- The unit type is contractible.

⊤-contractible : Contractible ⊤
⊤-contractible = (_ , λ _ → refl _)

------------------------------------------------------------------------
-- The empty type

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

-- The values true and false are distinct.

true≢false : ¬ true ≡ false
true≢false true≡false = subst T true≡false _

-- The booleans are not propositional.

¬-Bool-propositional : ¬ Propositional Bool
¬-Bool-propositional propositional =
  true≢false $
  (_⇔_.to propositional⇔irrelevant propositional) true false

-- The booleans form a set.

Bool-set : Is-set Bool
Bool-set = decidable⇒set dec
  where
  dec : (x y : Bool) → Dec (x ≡ y)
  dec true  true  = yes (refl true)
  dec true  false = no  true≢false
  dec false true  = no  (true≢false ∘ sym)
  dec false false = yes (refl false)

------------------------------------------------------------------------
-- Π-types

-- Closure of contractibility under Π A is equivalent to having
-- extensional equality for functions from A.

Π-closure-contractible⇔extensionality :
  ∀ {A} →
  ({B : A → Set} →
   (∀ x → Contractible (B x)) → Contractible ((x : A) → B x)) ⇔
  (∀ {B} → Extensionality A B)
Π-closure-contractible⇔extensionality {A} =
  equivalent
    ⇒
    (λ ext cB →
       ((λ x → proj₁ (cB x)) , λ f → ext λ x → proj₂ (cB x) (f x)))
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

-- Given (generalised) extensionality one can define an extensionality
-- proof which is well-behaved.

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

-- Given extensionality there is a surjection from ∀ x → f x ≡ g x to
-- f ≡ g.

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
                                         Tactic.prove (Cong (λ h → h x) (Refl {x = h})) Refl (refl _)) ⟩
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

-- H-level is closed under Π A, assuming extensionality for functions
-- from A.

Π-closure : ∀ {A} →
            (∀ {B} → Extensionality A B) →
            ∀ {B : A → Set} n →
            (∀ x → H-level n (B x)) → H-level n ((x : A) → B x)
Π-closure ext zero =
  _⇔_.from Π-closure-contractible⇔extensionality ext
Π-closure ext (suc n) = λ h f g →
  respects-surjection (ext-surj ext) n $
    Π-closure ext n (λ x → h x (f x) (g x))

-- Negated types are propositional, assuming extensionality.

¬-propositional :
  ∀ {A} → (∀ {B} → Extensionality A B) → Propositional (¬ A)
¬-propositional ext = Π-closure ext 1 (λ _ → ⊥-propositional)

------------------------------------------------------------------------
-- Σ-types

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
  respects-surjection surj n $
    Σ-closure n (hA (proj₁ p₁) (proj₁ p₂))
      (λ pr₁p₁≡pr₁p₂ →
         hB (proj₁ p₂) (subst B pr₁p₁≡pr₁p₂ (proj₂ p₁)) (proj₂ p₂))
  where
  surj : {p₁ p₂ : Σ A B} →
         (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
            subst B p (proj₂ p₁) ≡ proj₂ p₂) ↠
         (p₁ ≡ p₂)
  surj = record
    { equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = elim (λ p≡q → to (from p≡q) ≡ p≡q) (λ x →
        let lem = subst-refl B _ in
        to (from (refl x))                      ≡⟨ cong to (elim-refl from-P _) ⟩
        to (refl (proj₁ x) , subst-refl B _)    ≡⟨ cong (λ f → f (subst-refl B _)) (elim-refl to-P _) ⟩
        trans (cong (_,_ (proj₁ x)) $ sym lem)
              (cong (_,_ (proj₁ x)) lem)        ≡⟨ Tactic.prove (Trans (Cong (_,_ (proj₁ x)) (Sym (Lift lem)))
                                                                       (Cong (_,_ (proj₁ x)) (Lift lem)))
                                                                (Trans (Sym (Cong (_,_ (proj₁ x)) (Lift lem)))
                                                                       (Cong (_,_ (proj₁ x)) (Lift lem)))
                                                                (refl _) ⟩
        trans (sym _) _                         ≡⟨ G.right-inverse _ ⟩∎
        refl x                                  ∎)
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
      (λ z₁ {x₂} {y₂} x₂≡y₂ →
         (z₁ , x₂)                    ≡⟨ cong (_,_ z₁) $ sym $ subst-refl B x₂ ⟩
         (z₁ , subst B (refl z₁) x₂)  ≡⟨ cong (_,_ z₁) x₂≡y₂ ⟩∎
         (z₁ , y₂)                    ∎)
      p q

-- H-level is closed under _×_.

×-closure : ∀ {A B} n → H-level n A → H-level n B → H-level n (A × B)
×-closure n hA hB = Σ-closure n hA (const hB)

------------------------------------------------------------------------
-- W-types

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

-- However, Propositional is closed under W, assuming that equality is
-- sufficiently extensional.

W-closure-propositional :
  ∀ {A B} → (∀ {x} → Extensionality (B x) (λ _ → W A B)) →
  Propositional A → Propositional (W A B)
W-closure-propositional {A} {B} ext pA =
  _⇔_.from propositional⇔irrelevant irrelevant
  where
  irrelevant : Proof-irrelevant (W A B)
  irrelevant (sup x f) (sup y g) =
    sup x f                               ≡⟨ elim (λ {y x} y≡x → (f : B x → W A B) →
                                                     sup x f ≡ sup y (f ∘ subst B y≡x))
                                                  (λ z h → cong (sup z) (ext λ i →
                                                             cong h (sym $ subst-refl B i)))
                                                  (proj₁ $ pA y x) f ⟩
    sup y (f ∘ subst B (proj₁ $ pA y x))  ≡⟨ cong (sup y) (ext λ i → irrelevant (f _) (g i)) ⟩∎
    sup y g                               ∎

-- H-level is closed under W for other levels greater than or equal to
-- 1 as well (assuming extensionality).

W-closure :
  ∀ {A} {B : A → Set} →
  (∀ {x C} → Extensionality (B x) C) →
  ∀ n → H-level (1 + n) A → H-level (1 + n) (W A B)
W-closure         ext zero    h = W-closure-propositional ext h
W-closure {A} {B} ext (suc n) h = closure
  where
  closure : (x y : W A B) → H-level (1 + n) (x ≡ y)
  closure (sup x f) (sup y g) =
    respects-surjection surj (1 + n) $
      Σ-closure (1 + n) (h x y) (λ _ →
        Π-closure ext (1 + n) (λ i → closure (f _) (g _)))
    where
    ext′ : ∀ {x C} → Well-behaved-extensionality (B x) C
    ext′ = extensionality⇒well-behaved-extensionality ext

    surj : (∃ λ (p : x ≡ y) → ∀ i → f i ≡ g (subst B p i)) ↠
           (sup x f ≡ sup y g)
    surj = record
      { equivalence = record
        { to   = to (sup x f) (sup y g)
        ; from = from
        }
      ; right-inverse-of = elim (λ p → to _ _ (from p) ≡ p) to∘from
      }
      where
      to-P = λ {x y : A} (p : x ≡ y) →
               (f : B x → W A B) (g : B y → W A B) →
               (∀ i → f i ≡ g (subst B p i)) →
               sup x f ≡ sup y g

      to : (w w′ : W A B) →
           (∃ λ (p : head w ≡ head w′) →
              ∀ i → tail w i ≡ tail w′ (subst B p i)) →
           w ≡ w′
      to (sup x f) (sup y g) (x≡y , f≡g) = elim to-P
        (λ x f g f≡g →
           sup x f ≡⟨ cong (sup x) (proj₁ ext′ λ i →
                        f i                     ≡⟨ f≡g i ⟩
                        g (subst B (refl x) i)  ≡⟨ cong g (subst-refl B i) ⟩∎
                        g i                     ∎) ⟩∎
           sup x g ∎)
        x≡y _ _ f≡g

      from-P = λ {w w′ : W A B} (_ : w ≡ w′) →
                 ∃ λ (p : head w ≡ head w′) →
                   ∀ i → tail w i ≡ tail w′ (subst B p i)

      from : {w w′ : W A B} →
             w ≡ w′ →
             ∃ λ (p : head w ≡ head w′) →
               ∀ i → tail w i ≡ tail w′ (subst B p i)
      from = elim from-P
        (λ w → refl (head w) , λ i →
           tail w i                               ≡⟨ cong (tail w) $ sym $ subst-refl B i ⟩∎
           tail w (subst B (refl (head w)) i)  ∎)

      to∘from : (w : W A B) → to w w (from (refl w)) ≡ refl w
      to∘from (sup x f) =
        to (sup x f) (sup x f) (from (refl (sup x f)))        ≡⟨ cong (to _ _) (elim-refl from-P _ {x = sup x f}) ⟩
        to (sup x f) (sup x f) (refl x , cong f ∘ sym ∘ lem)  ≡⟨ cong (λ h → h _ _ (cong f ∘ sym ∘ lem)) $
                                                                   elim-refl to-P _ ⟩
        cong (sup x) (proj₁ ext′ λ i →
          trans (cong f (sym $ lem i)) (cong f (lem i)))      ≡⟨ cong (cong (sup x) ∘ proj₁ ext′) (proj₁ ext′ λ i →
                                                                   Tactic.prove
                                                                     (Trans (Cong f (Sym (Lift $ lem i))) (Cong f (Lift $ lem i)))
                                                                     (Trans (Sym (Cong f (Lift $ lem i))) (Cong f (Lift $ lem i)))
                                                                     (refl _)) ⟩
        cong (sup x) (proj₁ ext′ λ i →
          trans (sym $ cong f $ lem i) (cong f $ lem i))      ≡⟨ cong (cong (sup x) ∘ proj₁ ext′) (proj₁ ext′ λ i →
                                                                   G.right-inverse _) ⟩
        cong (sup x) (proj₁ ext′ (refl ∘ f))                  ≡⟨ cong (cong (sup x)) $ proj₂ ext′ f ⟩
        cong (sup x) (refl f)                                 ≡⟨ Tactic.prove (Cong (sup x) Refl) Refl (refl _) ⟩∎
        refl (sup x f)                                        ∎
        where lem = subst-refl B

------------------------------------------------------------------------
-- H-levels

-- Contractible is a comonad (assuming extensionality).

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

private

  inj₁≢inj₂ : ∀ {A B} {x : A} {y : B} → ¬ inj₁ x ≡ inj₂ y
  inj₁≢inj₂ = true≢false ∘ cong [ const true , const false ]

¬-⊎-propositional : ∀ {A B} → A → B → ¬ Propositional (A ⊎ B)
¬-⊎-propositional x y hA⊎B = inj₁≢inj₂ $ proj₁ $ hA⊎B (inj₁ x) (inj₂ y)

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
  irrelevant (yes a) (yes a′) = cong yes $ proj₁ $ p a a′
  irrelevant (yes a) (no ¬a)  = ⊥-elim (¬a a)
  irrelevant (no ¬a) (yes a)  = ⊥-elim (¬a a)
  irrelevant (no ¬a) (no ¬a′) =
    cong no $ proj₁ $ ¬-propositional ext ¬a ¬a′

-- Alternative definition of ⊎-closure.

module Alternative-proof where

  -- Is-set is closed under _⊎_, by an argument similar to the one
  -- Hedberg used to prove that decidable equality implies uniqueness
  -- of identity proofs.

  private

    drop-inj₁ : ∀ {A B x y} → _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
    drop-inj₁ {x = x} = cong [ id , const x ]

    drop-inj₂ : ∀ {A B x y} → _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y) → x ≡ y
    drop-inj₂ {x = x} = cong [ const x , id ]

  ⊎-closure-set : ∀ {A B} → Is-set A → Is-set B → Is-set (A ⊎ B)
  ⊎-closure-set {A} {B} A-set B-set =
    _⇔_.from set⇔UIP (DUIP.constant⇒UIP c)
    where
    c : (x y : A ⊎ B) → ∃ λ (f : x ≡ y → x ≡ y) → DUIP.Constant f
    c (inj₁ x) (inj₁ y) = (cong inj₁ ∘ drop-inj₁ , λ p q → cong (cong inj₁) $ proj₁ $ A-set x y (drop-inj₁ p) (drop-inj₁ q))
    c (inj₂ x) (inj₂ y) = (cong inj₂ ∘ drop-inj₂ , λ p q → cong (cong inj₂) $ proj₁ $ B-set x y (drop-inj₂ p) (drop-inj₂ q))
    c (inj₁ x) (inj₂ y) = (⊥-elim ∘ inj₁≢inj₂       , λ _ → ⊥-elim ∘ inj₁≢inj₂)
    c (inj₂ x) (inj₁ y) = (⊥-elim ∘ inj₁≢inj₂ ∘ sym , λ _ → ⊥-elim ∘ inj₁≢inj₂ ∘ sym)

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
      clos hA hB (inj₁ x) (inj₂ y) = ⊥-elim ∘ inj₁≢inj₂
      clos hA hB (inj₂ x) (inj₁ y) = ⊥-elim ∘ inj₁≢inj₂ ∘ sym

      surj₁ : ∀ {x y} → (x ≡ y) ↠ _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y)
      surj₁ {x} {y} = record
        { equivalence = record
          { to   = cong inj₁
          ; from = drop-inj₁
          }
        ; right-inverse-of = λ ix≡iy →
            cong inj₁ (drop-inj₁ ix≡iy)                  ≡⟨ Tactic.prove (Cong inj₁ (Cong [ id , const x ] (Lift ix≡iy)))
                                                                         (Cong f (Lift ix≡iy))
                                                                         (refl _) ⟩
            cong f ix≡iy                                 ≡⟨ cong-lemma f p ix≡iy _ _ f≡id ⟩
            trans (refl _) (trans ix≡iy $ sym (refl _))  ≡⟨ Tactic.prove (Trans Refl (Trans (Lift ix≡iy) (Sym Refl)))
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
          ; from = drop-inj₂
          }
        ; right-inverse-of = λ ix≡iy →
            cong inj₂ (drop-inj₂ ix≡iy)                  ≡⟨ Tactic.prove (Cong inj₂ (Cong [ const x , id ] (Lift ix≡iy)))
                                                                         (Cong f (Lift ix≡iy))
                                                                         (refl _) ⟩
            cong f ix≡iy                                 ≡⟨ cong-lemma f p ix≡iy _ _ f≡id ⟩
            trans (refl _) (trans ix≡iy $ sym (refl _))  ≡⟨ Tactic.prove (Trans Refl (Trans (Lift ix≡iy) (Sym Refl)))
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
      -- captures this statement indirectly. (Note that the equation above
      -- is not well-typed if f is a variable.) If cong-lemma is
      -- instantiated properly with the various components above, then we
      -- get
      --
      --   cong f x≡y ≡ trans … (trans x≡y (sym …)),
      --
      -- where the two occurrences of … evaluate to reflexivity proofs.

      cong-lemma : ∀ {A} (f : A → A) (p : A → Bool)
                   {x y : A} (x≡y : x ≡ y) (px : T (p x)) (py : T (p y))
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
          cong f (refl x)                                 ≡⟨ Tactic.prove (Cong f Refl) Refl (refl _) ⟩
          refl (f x)                                      ≡⟨ sym $ G.left-inverse _ ⟩
          trans (f≡id _) (sym (f≡id _))                   ≡⟨ Tactic.prove (Trans fx≡x (Sym fx≡x))
                                                                          (Trans fx≡x (Trans Refl (Sym fx≡x)))
                                                                          (refl _) ⟩∎
          trans (f≡id _) (trans (refl x) $ sym (f≡id _))  ∎
          where fx≡x = Lift (f≡id _)
