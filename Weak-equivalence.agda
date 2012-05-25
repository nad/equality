------------------------------------------------------------------------
-- Weak equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module Weak-equivalence
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

private
  module Bijection where
    import Bijection; open Bijection eq public
open Bijection hiding (id; _∘_; inverse)
open Derived-definitions-and-properties eq
import Groupoid; open Groupoid eq
open import Equivalence hiding (id; _∘_; inverse)
private
  module H-level where
    import H-level; open H-level eq public
open H-level
import H-level.Closure; open H-level.Closure eq
private
  module Injection where
    import Injection; open Injection eq public
open Injection using (_↣_; module _↣_; Injective)
private
  module Preimage where
    import Preimage; open Preimage eq public
open Preimage using (_⁻¹_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
private
  module Surjection where
    import Surjection; open Surjection eq public
open Surjection using (_↠_; module _↠_)

------------------------------------------------------------------------
-- Is-weak-equivalence

-- A function f is a weak equivalence if all preimages under f are
-- contractible.

Is-weak-equivalence : ∀ {a b} {A : Set a} {B : Set b} →
                      (A → B) → Set (a ⊔ b)
Is-weak-equivalence f = ∀ y → Contractible (f ⁻¹ y)

abstract

  -- Is-weak-equivalence f is a proposition, assuming extensional
  -- equality.

  propositional :
    ∀ {a b} →
    ({A : Set (a ⊔ b)} {B : A → Set (a ⊔ b)} → Extensionality A B) →
    {A : Set a} {B : Set b} (f : A → B) →
    Propositional (Is-weak-equivalence f)
  propositional {a} ext f =
    Π-closure (lower-extensionality a lzero ext) 1 λ _ →
      Contractible-propositional ext

-- Is-weak-equivalence respects extensional equality.

respects-extensional-equality :
  ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} →
  (∀ x → f x ≡ g x) →
  Is-weak-equivalence f → Is-weak-equivalence g
respects-extensional-equality f≡g f-weq = λ b →
  H-level.respects-surjection
    (_↔_.surjection (Preimage.respects-extensional-equality f≡g))
    0
    (f-weq b)

abstract

  -- The function subst is a weak equivalence family.
  --
  -- Note that this proof would be easier if subst P (refl x) p
  -- reduced to p.

  subst-is-weak-equivalence :
    ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} (x≡y : x ≡ y) →
    Is-weak-equivalence (subst P x≡y)
  subst-is-weak-equivalence P = elim
    (λ {x y} x≡y → Is-weak-equivalence (subst P x≡y))
    (λ x p → _ , λ q →
       (p , subst-refl P p)                                     ≡⟨ elim
                                                                     (λ {u v : P x} u≡v →
                                                                        _≡_ {A = ∃ λ (w : P x) → subst P (refl x) w ≡ v}
                                                                            (v , subst-refl P v)
                                                                            (u , trans (subst-refl P u) u≡v))
                                                                     (λ p → cong (_,_ p) (sym $ trans-reflʳ _))
                                                                     (proj₁ q                     ≡⟨ sym $ subst-refl P (proj₁ q) ⟩
                                                                      subst P (refl x) (proj₁ q)  ≡⟨ proj₂ q ⟩∎
                                                                      p                           ∎) ⟩
       (proj₁ q , (trans      (subst-refl P (proj₁ q))  $
                   trans (sym (subst-refl P (proj₁ q))) $
                         proj₂ q))                              ≡⟨ cong (_,_ (proj₁ q)) $ sym $ trans-assoc _ _ _ ⟩
       (proj₁ q , trans (trans      (subst-refl P (proj₁ q))
                               (sym (subst-refl P (proj₁ q))))
                        (proj₂ q))                              ≡⟨ cong (λ eq → proj₁ q , trans eq (proj₂ q)) $ trans-symʳ _ ⟩
       (proj₁ q , trans (refl _) (proj₂ q))                     ≡⟨ cong (_,_ (proj₁ q)) $ trans-reflˡ _ ⟩∎
       q                                                        ∎)

  -- If Σ-map id f is a weak equivalence, then f is also a weak
  -- equivalence.

  drop-Σ-map-id :
    ∀ {a b} {A : Set a} {B C : A → Set b} (f : ∀ {x} → B x → C x) →
    Is-weak-equivalence {A = Σ A B} {B = Σ A C} (Σ-map P.id f) →
    ∀ x → Is-weak-equivalence (f {x = x})
  drop-Σ-map-id {b = b} {A} {B} {C} f weq x z =
    H-level.respects-surjection surj 0 (weq (x , z))
    where
    map-f : Σ A B → Σ A C
    map-f = Σ-map P.id f

    to-P : ∀ {x y} {p : ∃ C} → (x , f y) ≡ p → Set b
    to-P {y = y} {p} _ = ∃ λ y′ → f y′ ≡ proj₂ p

    to : map-f ⁻¹ (x , z) → f ⁻¹ z
    to ((x′ , y) , eq) = elim¹ to-P (y , refl (f y)) eq

    from : f ⁻¹ z → map-f ⁻¹ (x , z)
    from (y , eq) = (x , y) , cong (_,_ x) eq

    to∘from : ∀ p → to (from p) ≡ p
    to∘from (y , eq) = elim¹
      (λ {z′} (eq : f y ≡ z′) →
         _≡_ {A = ∃ λ (y : B x) → f y ≡ z′}
             (elim¹ to-P (y , refl (f y)) (cong (_,_ x) eq))
             (y , eq))
      (elim¹ to-P (y , refl (f y)) (cong (_,_ x) (refl (f y)))  ≡⟨ cong (elim¹ to-P (y , refl (f y))) $
                                                                        cong-refl (_,_ x) {x = f y} ⟩
       elim¹ to-P (y , refl (f y)) (refl (x , f y))             ≡⟨ elim¹-refl to-P _ ⟩∎
       (y , refl (f y))                                         ∎)
      eq

    surj : map-f ⁻¹ (x , z) ↠ f ⁻¹ z
    surj = record
      { equivalence      = record { to = to; from = from }
      ; right-inverse-of = to∘from
      }

------------------------------------------------------------------------
-- _≈_

-- Weak equivalences.

infix 4 _≈_

record _≈_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor weq
  field
    to                  : A → B
    is-weak-equivalence : Is-weak-equivalence to

  -- Weakly equivalent sets are isomorphic.

  from : B → A
  from = proj₁ ⊚ proj₁ ⊚ is-weak-equivalence

  abstract
    right-inverse-of : ∀ x → to (from x) ≡ x
    right-inverse-of = proj₂ ⊚ proj₁ ⊚ is-weak-equivalence

    left-inverse-of : ∀ x → from (to x) ≡ x
    left-inverse-of  = λ x →
      cong (proj₁ {B = λ x′ → to x′ ≡ to x}) $
        proj₂ (is-weak-equivalence (to x)) (x , refl (to x))

  bijection : A ↔ B
  bijection = record
    { surjection = record
      { equivalence = record
        { to   = to
        ; from = from
        }
      ; right-inverse-of = right-inverse-of
      }
    ; left-inverse-of = left-inverse-of
    }

  open _↔_ bijection public
    hiding (from; to; right-inverse-of; left-inverse-of)

  abstract

    -- All preimages of an element under the weak equivalence are
    -- equal.

    irrelevance : ∀ y (p : to ⁻¹ y) → (from y , right-inverse-of y) ≡ p
    irrelevance = proj₂ ⊚ is-weak-equivalence

    -- The two proofs left-inverse-of and right-inverse-of are
    -- related.

    left-right-lemma :
      ∀ x → cong to (left-inverse-of x) ≡ right-inverse-of (to x)
    left-right-lemma x =
      lemma₁ to _ _ (lemma₂ (irrelevance (to x) (x , refl (to x))))
      where
      lemma₁ : {x y : A} (f : A → B) (p : x ≡ y) (q : f x ≡ f y) →
               refl (f y) ≡ trans (cong f (sym p)) q →
               cong f p ≡ q
      lemma₁ f = elim
        (λ {x y} p → ∀ q → refl (f y) ≡ trans (cong f (sym p)) q →
                           cong f p ≡ q)
        (λ x q hyp →
           cong f (refl x)                  ≡⟨ cong-refl f ⟩
           refl (f x)                       ≡⟨ hyp ⟩
           trans (cong f (sym (refl x))) q  ≡⟨ cong (λ p → trans (cong f p) q) sym-refl ⟩
           trans (cong f (refl x)) q        ≡⟨ cong (λ p → trans p q) (cong-refl f) ⟩
           trans (refl (f x)) q             ≡⟨ trans-reflˡ _ ⟩∎
           q                                ∎)

      lemma₂ : ∀ {f : A → B} {y} {f⁻¹y₁ f⁻¹y₂ : f ⁻¹ y}
               (p : f⁻¹y₁ ≡ f⁻¹y₂) →
               proj₂ f⁻¹y₂ ≡
               trans (cong f (sym (cong (proj₁ {B = λ x → f x ≡ y}) p)))
                     (proj₂ f⁻¹y₁)
      lemma₂ {f} {y} =
        let pr = proj₁ {B = λ x → f x ≡ y} in
        elim {A = f ⁻¹ y}
          (λ {f⁻¹y₁ f⁻¹y₂} p →
             proj₂ f⁻¹y₂ ≡
               trans (cong f (sym (cong pr p))) (proj₂ f⁻¹y₁))
          (λ f⁻¹y →
             proj₂ f⁻¹y                                               ≡⟨ sym $ trans-reflˡ _ ⟩
             trans (refl (f (proj₁ f⁻¹y))) (proj₂ f⁻¹y)               ≡⟨ cong (λ p → trans p (proj₂ f⁻¹y)) (sym (cong-refl f)) ⟩
             trans (cong f (refl (proj₁ f⁻¹y))) (proj₂ f⁻¹y)          ≡⟨ cong (λ p → trans (cong f p) (proj₂ f⁻¹y)) (sym sym-refl) ⟩
             trans (cong f (sym (refl (proj₁ f⁻¹y)))) (proj₂ f⁻¹y)    ≡⟨ cong (λ p → trans (cong f (sym p)) (proj₂ f⁻¹y))
                                                                              (sym (cong-refl pr)) ⟩∎
             trans (cong f (sym (cong pr (refl f⁻¹y)))) (proj₂ f⁻¹y)  ∎)

-- Bijections are weak equivalences.

bijection⇒weak-equivalence : ∀ {a b} {A : Set a} {B : Set b} →
                             A ↔ B → A ≈ B
bijection⇒weak-equivalence A↔B = record
  { to                  = to
  ; is-weak-equivalence = λ y →
      (from y , right-inverse-of y) , irrelevance y
  }
  where
  open _↔_ A↔B using (to; from)

  abstract
    is-weak-equivalence : Is-weak-equivalence to
    is-weak-equivalence = Preimage.bijection⁻¹-contractible A↔B

    right-inverse-of : ∀ x → to (from x) ≡ x
    right-inverse-of = proj₂ ⊚ proj₁ ⊚ is-weak-equivalence

    irrelevance : ∀ y (p : to ⁻¹ y) → (from y , right-inverse-of y) ≡ p
    irrelevance = proj₂ ⊚ is-weak-equivalence

------------------------------------------------------------------------
-- Equivalence

-- Weak equivalences are equivalence relations.

id : ∀ {a} {A : Set a} → A ≈ A
id {A = A} = record
  { to                  = to
  ; is-weak-equivalence = λ y →
      (from y , right-inverse-of y) , irrelevance y
  }
  where
  A≈A  = bijection⇒weak-equivalence (Bijection.id {A = A})
  to   = _≈_.to   A≈A
  from = _≈_.from A≈A

  abstract
    right-inverse-of : ∀ x → to (from x) ≡ x
    right-inverse-of = _≈_.right-inverse-of A≈A

    irrelevance : ∀ y (p : to ⁻¹ y) → (from y , right-inverse-of y) ≡ p
    irrelevance = _≈_.irrelevance A≈A

inverse : ∀ {a b} {A : Set a} {B : Set b} → A ≈ B → B ≈ A
inverse A≈B = record
  { to                  = to
  ; is-weak-equivalence = λ y →
      (from y , right-inverse-of y) , irrelevance y
  }
  where
  B≈A  = bijection⇒weak-equivalence $
         Bijection.inverse $
         _≈_.bijection A≈B
  to   = _≈_.to   B≈A
  from = _≈_.from B≈A

  abstract
    right-inverse-of : ∀ x → to (from x) ≡ x
    right-inverse-of = _≈_.right-inverse-of B≈A

    irrelevance : ∀ y (p : to ⁻¹ y) → (from y , right-inverse-of y) ≡ p
    irrelevance = _≈_.irrelevance B≈A

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ≈ C → A ≈ B → A ≈ C
f ∘ g = record
  { to                  = to
  ; is-weak-equivalence = λ y →
      (from y , right-inverse-of y) , irrelevance y
  }
  where
  f∘g  = bijection⇒weak-equivalence $
         Bijection._∘_ (_≈_.bijection f) (_≈_.bijection g)
  to   = _≈_.to   f∘g
  from = _≈_.from f∘g

  abstract
    right-inverse-of : ∀ x → to (from x) ≡ x
    right-inverse-of = _≈_.right-inverse-of f∘g

    irrelevance : ∀ y (p : to ⁻¹ y) → (from y , right-inverse-of y) ≡ p
    irrelevance = _≈_.irrelevance f∘g

-- Equational reasoning combinators.

infixr 0 _≈⟨_⟩_
infix  0 finally-≈

_≈⟨_⟩_ : ∀ {a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ≈ B → B ≈ C → A ≈ C
_ ≈⟨ A≈B ⟩ B≈C = B≈C ∘ A≈B

finally-≈ : ∀ {a b} (A : Set a) (B : Set b) → A ≈ B → A ≈ B
finally-≈ _ _ A≈B = A≈B

syntax finally-≈ A B A≈B = A ≈⟨ A≈B ⟩□ B □

------------------------------------------------------------------------
-- The two-out-of-three property

-- If two out of three of f, g and g ∘ f are weak equivalences, then
-- the third one is also a weak equivalence.

record Two-out-of-three
         {a b c} {A : Set a} {B : Set b} {C : Set c}
         (f : A → B) (g : B → C) : Set (a ⊔ b ⊔ c) where
  field
    f-g   : Is-weak-equivalence f → Is-weak-equivalence g →
            Is-weak-equivalence (g ⊚ f)
    g-g∘f : Is-weak-equivalence g → Is-weak-equivalence (g ⊚ f) →
            Is-weak-equivalence f
    g∘f-f : Is-weak-equivalence (g ⊚ f) → Is-weak-equivalence f →
            Is-weak-equivalence g

two-out-of-three :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) → Two-out-of-three f g
two-out-of-three f g = record
  { f-g   = λ f-weq g-weq →
              _≈_.is-weak-equivalence (weq g g-weq ∘ weq f f-weq)
  ; g-g∘f = λ g-weq g∘f-weq →
              respects-extensional-equality
                (λ x → let g⁻¹ = _≈_.from (weq g g-weq) in
                   g⁻¹ (g (f x))  ≡⟨ _≈_.left-inverse-of (weq g g-weq) (f x) ⟩∎
                   f x            ∎)
                (_≈_.is-weak-equivalence
                   (inverse (weq g g-weq) ∘ weq _ g∘f-weq))
  ; g∘f-f = λ g∘f-weq f-weq →
              respects-extensional-equality
                (λ x → let f⁻¹ = _≈_.from (weq f f-weq) in
                   g (f (f⁻¹ x))  ≡⟨ cong g (_≈_.right-inverse-of (weq f f-weq) x) ⟩∎
                   g x            ∎)
                (_≈_.is-weak-equivalence
                   (weq _ g∘f-weq ∘ inverse (weq f f-weq)))
  }

------------------------------------------------------------------------
-- f ≡ g and ∀ x → f x ≡ g x are isomorphic (assuming extensionality)

abstract

  -- Functions between contractible types are weak equivalences.

  function-between-contractible-types-is-weak-equivalence :
    ∀ {a b} {A : Set a} {B : Set b} (f : A → B) →
    Contractible A → Contractible B → Is-weak-equivalence f
  function-between-contractible-types-is-weak-equivalence f cA cB =
    Two-out-of-three.g-g∘f
      (two-out-of-three f (const tt))
      (lemma cB)
      (lemma cA)
    where
    -- Functions from a contractible type to the unit type are
    -- contractible.

    lemma : ∀ {b} {C : Set b} → Contractible C →
            Is-weak-equivalence (λ (_ : C) → tt)
    lemma (x , irr) _ = (x , refl tt) , λ p →
      (x , refl tt)  ≡⟨ _↔_.to Σ-≡,≡↔≡ (irr (proj₁ p) ,
                          (subst (λ _ → tt ≡ tt)
                             (irr (proj₁ p)) (refl tt)  ≡⟨ elim (λ eq → subst (λ _ → tt ≡ tt) eq (refl tt) ≡ refl tt)
                                                                (λ _ → subst-refl (λ _ → tt ≡ tt) (refl tt))
                                                                (irr (proj₁ p)) ⟩
                           refl tt                      ≡⟨ elim (λ eq → refl tt ≡ eq) (refl ⊚ refl) (proj₂ p) ⟩∎
                           proj₂ p                      ∎)) ⟩∎
      p              ∎

  -- ext⁻¹ is a weak equivalence (assuming extensionality).

  ext⁻¹-is-weak-equivalence :
    ∀ {a b} {A : Set a} →
    ({B : A → Set b} → Extensionality A B) →
    {B : A → Set b} {f g : (x : A) → B x} →
    Is-weak-equivalence (ext⁻¹ {f = f} {g = g})
  ext⁻¹-is-weak-equivalence ext {f = f} {g} =
    let surj : (∀ x → Singleton (g x)) ↠ (∃ λ f → ∀ x → f x ≡ g x)
        surj = record
          { equivalence = record
            { to   = λ f → proj₁ ⊚ f , proj₂ ⊚ f
            ; from = λ p x → proj₁ p x , proj₂ p x
            }
          ; right-inverse-of = refl
          }

        lemma₁ : Contractible (∃ λ f → ∀ x → f x ≡ g x)
        lemma₁ =
          H-level.respects-surjection surj 0 $
            _⇔_.from Π-closure-contractible⇔extensionality
              ext (singleton-contractible ⊚ g)

        lemma₂ : Is-weak-equivalence (Σ-map P.id ext⁻¹)
        lemma₂ = function-between-contractible-types-is-weak-equivalence
                   _ (singleton-contractible g) lemma₁

    in drop-Σ-map-id ext⁻¹ lemma₂ f

-- f ≡ g and ∀ x → f x ≡ g x are isomorphic (assuming extensionality).

extensionality-isomorphism :
  ∀ {a b} {A : Set a} →
  ({B : A → Set b} → Extensionality A B) →
  {B : A → Set b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) ≈ (f ≡ g)
extensionality-isomorphism ext =
  inverse (weq _ (ext⁻¹-is-weak-equivalence ext))

------------------------------------------------------------------------
-- Groupoid

abstract

  -- Two proofs of weak equivalence are equal if the function
  -- components are equal (assuming extensionality).

  lift-equality :
    ∀ {a b} →
    ({A : Set (a ⊔ b)} {B : A → Set (a ⊔ b)} → Extensionality A B) →
    {A : Set a} {B : Set b} {p q : A ≈ B} →
    (∀ x → _≈_.to p x ≡ _≈_.to q x) → p ≡ q
  lift-equality {a} {b} ext {p = weq f f-weq} {q = weq g g-weq} f≡g =
    elim (λ {f g} f≡g → ∀ f-weq g-weq → weq f f-weq ≡ weq g g-weq)
         (λ f f-weq g-weq →
            cong (weq f)
              (_⇔_.to {To = Proof-irrelevant _}
                      propositional⇔irrelevant
                      (propositional ext f) f-weq g-weq))
         (lower-extensionality b a ext f≡g)
         f-weq g-weq

-- _≈_ comes with a groupoid structure (assuming extensionality).

groupoid : ∀ {ℓ} →
           ({A : Set ℓ} {B : A → Set ℓ} → Extensionality A B) →
           Groupoid (lsuc ℓ) ℓ
groupoid {ℓ} ext = record
  { Object         = Set ℓ
  ; _∼_            = _≈_
  ; id             = id
  ; _∘_            = _∘_
  ; _⁻¹            = inverse
  ; left-identity  = left-identity
  ; right-identity = right-identity
  ; assoc          = assoc
  ; left-inverse   = left-inverse
  ; right-inverse  = right-inverse
  }
  where
  abstract
    left-identity : {X Y : Set ℓ} (p : X ≈ Y) → id ∘ p ≡ p
    left-identity _ = lift-equality ext (λ _ → refl _)

    right-identity : {X Y : Set ℓ} (p : X ≈ Y) → p ∘ id ≡ p
    right-identity _ = lift-equality ext (λ _ → refl _)

    assoc : {W X Y Z : Set ℓ} (p : Y ≈ Z) (q : X ≈ Y) (r : W ≈ X) →
            p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
    assoc _ _ _ = lift-equality ext (λ _ → refl _)

    left-inverse : {X Y : Set ℓ} (p : X ≈ Y) → inverse p ∘ p ≡ id
    left-inverse p = lift-equality ext (_≈_.left-inverse-of p)

    right-inverse : {X Y : Set ℓ} (p : X ≈ Y) → p ∘ inverse p ≡ id
    right-inverse p = lift-equality ext (_≈_.right-inverse-of p)

------------------------------------------------------------------------
-- A surjection from A ↔ B to A ≈ B

abstract

  -- bijection⇒weak-equivalence is a left inverse of _≈_.bijection
  -- (assuming extensionality).

  bijection⇒weak-equivalence-left-inverse :
    ∀ {a b} {A : Set a} {B : Set b} →
    ({A : Set (a ⊔ b)} {B : A → Set (a ⊔ b)} → Extensionality A B) →
    (A≈B : A ≈ B) →
    bijection⇒weak-equivalence (_≈_.bijection A≈B) ≡ A≈B
  bijection⇒weak-equivalence-left-inverse ext _ =
    lift-equality ext (λ _ → refl _)

-- There is a surjection from A ↔ B to A ≈ B (assuming
-- extensionality).

↔-↠-≈ :
  ∀ {a b} {A : Set a} {B : Set b} →
  ({A : Set (a ⊔ b)} {B : A → Set (a ⊔ b)} → Extensionality A B) →
  (A ↔ B) ↠ (A ≈ B)
↔-↠-≈ ext = record
  { equivalence = record
    { to   = bijection⇒weak-equivalence
    ; from = _≈_.bijection
    }
  ; right-inverse-of = bijection⇒weak-equivalence-left-inverse ext
  }

------------------------------------------------------------------------
-- Closure, preservation

abstract

  -- Positive h-levels are closed under the weak equivalence operator
  -- (assuming extensionality).

  right-closure :
    ∀ {a b} →
    ({A : Set (a ⊔ b)} {B : A → Set (a ⊔ b)} → Extensionality A B) →
    ∀ {A : Set a} {B : Set b} n →
    H-level (1 + n) B → H-level (1 + n) (A ≈ B)
  right-closure {a} {b} ext {A = A} {B} n h =
    H-level.respects-surjection surj (1 + n) lemma
    where
    lemma : H-level (1 + n) (∃ λ (to : A → B) → Is-weak-equivalence to)
    lemma = Σ-closure (1 + n)
              (Π-closure (lower-extensionality b a ext)
                         (1 + n) (const h))
              (mono (m≤m+n 1 n) ⊚ propositional ext)

    surj : (∃ λ (to : A → B) → Is-weak-equivalence to) ↠ (A ≈ B)
    surj = record
      { equivalence = record
          { to   = λ A≈B → weq (proj₁ A≈B) (proj₂ A≈B)
          ; from = λ A≈B → (_≈_.to A≈B , _≈_.is-weak-equivalence A≈B)
          }
      ; right-inverse-of = λ _ → refl _
      }

  left-closure :
    ∀ {a b} →
    ({A : Set (a ⊔ b)} {B : A → Set (a ⊔ b)} → Extensionality A B) →
    ∀ {A : Set a} {B : Set b} n →
    H-level (1 + n) A → H-level (1 + n) (A ≈ B)
  left-closure ext {A = A} {B} n h =
    H-level.[inhabited⇒+]⇒+ n λ (A≈B : A ≈ B) →
      right-closure ext n $
        H-level.respects-surjection (_≈_.surjection A≈B) (1 + n) h

-- Equalities are closed, in a strong sense, under applications of
-- weak equivalences.

≈-≡ : ∀ {a b} {A : Set a} {B : Set b} (A≈B : A ≈ B) {x y : A} →
      let open _≈_ A≈B in
      (to x ≡ to y) ≈ (x ≡ y)
≈-≡ A≈B {x} {y} =
  bijection⇒weak-equivalence record
    { surjection      = surjection′
    ; left-inverse-of = left-inverse-of′
    }
  where
  open _≈_ A≈B

  surjection′ : (to x ≡ to y) ↠ (x ≡ y)
  surjection′ =
    Surjection.↠-≡ $
    _↔_.surjection $
    Bijection.inverse $
    _≈_.bijection A≈B

  abstract
    left-inverse-of′ :
      ∀ p → _↠_.from surjection′ (_↠_.to surjection′ p) ≡ p
    left-inverse-of′ = λ to-x≡to-y →
      cong to (
        trans (sym (left-inverse-of x)) $
        trans (cong from to-x≡to-y) $
        left-inverse-of y)                         ≡⟨ cong-trans to _ _ ⟩
      trans (cong to (sym (left-inverse-of x))) (
        cong to (trans (cong from to-x≡to-y) (
                 left-inverse-of y)))              ≡⟨ cong₂ trans (cong-sym to _) (cong-trans to _ _) ⟩
      trans (sym (cong to (left-inverse-of x))) (
        trans (cong to (cong from to-x≡to-y)) (
        cong to (left-inverse-of y)))              ≡⟨ cong₂ (λ eq₁ eq₂ → trans (sym eq₁) $
                                                                         trans (cong to (cong from to-x≡to-y)) $
                                                                         eq₂)
                                                           (left-right-lemma x)
                                                           (left-right-lemma y) ⟩
      trans (sym (right-inverse-of (to x))) (
        trans (cong to (cong from to-x≡to-y)) (
        right-inverse-of (to y)))                  ≡⟨ _↠_.right-inverse-of (Surjection.↠-≡ $ _≈_.surjection A≈B) to-x≡to-y ⟩∎
      to-x≡to-y                                    ∎

abstract
  private

    -- We can push subst through certain function applications.

    push-subst :
      ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
        (B₁ : A₁ → Set b₁) {B₂ : A₂ → Set b₂}
        {f : A₂ → A₁} {x₁ x₂ : A₂} {y : B₁ (f x₁)}
      (g : ∀ x → B₁ (f x) → B₂ x) (eq : x₁ ≡ x₂) →
      subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ (cong f eq) y)
    push-subst B₁ {B₂} {f} g eq = elim
      (λ {x₁ x₂} eq → ∀ y → subst B₂ eq (g x₁ y) ≡
                            g x₂ (subst B₁ (cong f eq) y))
      (λ x y → subst B₂ (refl x) (g x y)           ≡⟨ subst-refl B₂ _ ⟩
               g x y                               ≡⟨ sym $ cong (g x) $ subst-refl B₁ _ ⟩
               g x (subst B₁ (refl (f x)) y)       ≡⟨ cong (λ eq → g x (subst B₁ eq y)) (sym $ cong-refl f) ⟩∎
               g x (subst B₁ (cong f (refl x)) y)  ∎)
      eq _

    push-subst′ :
      ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
      (A₁≈A₂ : A₁ ≈ A₂) (B₁ : A₁ → Set b₁) (B₂ : A₂ → Set b₂) →
      let open _≈_ A₁≈A₂ in {x₁ x₂ : A₁} {y : B₁ (from (to x₁))}
      (g : ∀ x → B₁ (from (to x)) → B₂ (to x)) (eq : to x₁ ≡ to x₂) →
      subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ (cong from eq) y)
    push-subst′ A₁≈A₂ B₁ B₂ {x₁} {x₂} {y} g eq =
      subst B₂ eq (g x₁ y)                    ≡⟨ cong (subst B₂ eq) $ sym $ g′-lemma _ _ ⟩
      subst B₂ eq (g′ (to x₁) y)              ≡⟨ push-subst B₁ g′ eq ⟩
      g′ (to x₂) (subst B₁ (cong from eq) y)  ≡⟨ g′-lemma _ _ ⟩∎
      g x₂ (subst B₁ (cong from eq) y)        ∎
      where
      open _≈_ A₁≈A₂

      g′ : ∀ x′ → B₁ (from x′) → B₂ x′
      g′ x′ y = subst B₂ (right-inverse-of x′) $
                g (from x′) $
                subst B₁ (sym $ cong from $ right-inverse-of x′) y

      g′-lemma : ∀ x y → g′ (to x) y ≡ g x y
      g′-lemma x y =
        let lemma = λ y →
              let gy = g (from (to x)) $
                         subst B₁
                           (sym $ cong from $ cong to (refl _)) y in
              subst B₂ (cong to (refl _)) gy             ≡⟨ cong (λ p → subst B₂ p gy) $ cong-refl to ⟩
              subst B₂ (refl _) gy                       ≡⟨ subst-refl B₂ gy ⟩
              gy                                         ≡⟨ cong (λ p → g (from (to x)) $ subst B₁ (sym $ cong from p) y) $ cong-refl to ⟩
              g (from (to x))
                (subst B₁ (sym $ cong from (refl _)) y)  ≡⟨ cong (λ p → g (from (to x)) $ subst B₁ (sym p) y) $ cong-refl from ⟩
              g (from (to x))
                (subst B₁ (sym (refl _)) y)              ≡⟨ cong (λ p → g (from (to x)) $ subst B₁ p y) sym-refl ⟩
              g (from (to x)) (subst B₁ (refl _) y)      ≡⟨ cong (g (from (to x))) $ subst-refl B₁ y ⟩∎
              g (from (to x)) y                          ∎
        in
        subst B₂ (right-inverse-of (to x))
          (g (from (to x)) $
           subst B₁ (sym $ cong from $
                       right-inverse-of (to x)) y)  ≡⟨ cong (λ p → subst B₂ p (g (from (to x)) $ subst B₁ (sym $ cong from p) y)) $
                                                         sym $ left-right-lemma x ⟩
        subst B₂ (cong to $ left-inverse-of x)
          (g (from (to x)) $
           subst B₁ (sym $ cong from $ cong to $
                       left-inverse-of x) y)        ≡⟨ elim¹
                                                         (λ {x′} eq →
                                                            (y : B₁ (from (to x′))) →
                                                            subst B₂ (cong to eq)
                                                              (g (from (to x)) $ subst B₁ (sym $ cong from $ cong to eq) y) ≡
                                                            g x′ y)
                                                         lemma
                                                         (left-inverse-of x) y ⟩∎
        g x y                                       ∎

-- If the first component is instantiated to id, then the following
-- lemmas state that ∃ preserves functions, equivalences, injections,
-- surjections and bijections.

∃-preserves-functions :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
    {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x → B₂ (_≈_.to A₁≈A₂ x)) →
  Σ A₁ B₁ → Σ A₂ B₂
∃-preserves-functions A₁≈A₂ B₁→B₂ = Σ-map (_≈_.to A₁≈A₂) (B₁→B₂ _)

∃-preserves-equivalences :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
    {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ⇔ B₂ (_≈_.to A₁≈A₂ x)) →
  Σ A₁ B₁ ⇔ Σ A₂ B₂
∃-preserves-equivalences {B₂ = B₂} A₁≈A₂ B₁⇔B₂ = record
  { to   = ∃-preserves-functions A₁≈A₂ (_⇔_.to ⊚ B₁⇔B₂)
  ; from =
     ∃-preserves-functions
       (inverse A₁≈A₂)
       (λ x y → _⇔_.from
                  (B₁⇔B₂ (_≈_.from A₁≈A₂ x))
                  (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂ x)) y))
  }

∃-preserves-injections :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
    {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ↣ B₂ (_≈_.to A₁≈A₂ x)) →
  Σ A₁ B₁ ↣ Σ A₂ B₂
∃-preserves-injections {A₁ = A₁} {A₂} {B₁} {B₂} A₁≈A₂ B₁↣B₂ = record
  { to        = to′
  ; injective = injective′
  }
  where
  open _↣_

  to′ : Σ A₁ B₁ → Σ A₂ B₂
  to′ = ∃-preserves-functions A₁≈A₂ (_↣_.to ⊚ B₁↣B₂)

  abstract
    injective′ : Injective to′
    injective′ {x = (x₁ , x₂)} {y = (y₁ , y₂)} =
      _↔_.to Σ-≡,≡↔≡ ⊚
      Σ-map (_≈_.injective A₁≈A₂) (λ {eq₁} eq₂ →
        let lemma =
              to (B₁↣B₂ y₁) (subst B₁ (_≈_.injective A₁≈A₂ eq₁) x₂)      ≡⟨ refl _ ⟩
              to (B₁↣B₂ y₁)
                (subst B₁ (trans (sym (_≈_.left-inverse-of A₁≈A₂ x₁)) $
                           trans (cong (_≈_.from A₁≈A₂) eq₁)
                                 (_≈_.left-inverse-of A₁≈A₂ y₁))
                          x₂)                                            ≡⟨ cong (to (B₁↣B₂ y₁)) $ sym $ subst-subst B₁ _ _ _ ⟩
              to (B₁↣B₂ y₁)
                 (subst B₁ (trans (cong (_≈_.from A₁≈A₂) eq₁)
                                  (_≈_.left-inverse-of A₁≈A₂ y₁)) $
                  subst B₁ (sym (_≈_.left-inverse-of A₁≈A₂ x₁))
                           x₂)                                           ≡⟨ cong (to (B₁↣B₂ y₁)) $ sym $ subst-subst B₁ _ _ _ ⟩
              to (B₁↣B₂ y₁)
                 (subst B₁ (_≈_.left-inverse-of A₁≈A₂ y₁) $
                  subst B₁ (cong (_≈_.from A₁≈A₂) eq₁) $
                  subst B₁ (sym (_≈_.left-inverse-of A₁≈A₂ x₁)) x₂)      ≡⟨ sym $ push-subst′ A₁≈A₂ B₁ B₂
                                                                              (λ x y → to (B₁↣B₂ x)
                                                                                          (subst B₁ (_≈_.left-inverse-of A₁≈A₂ x) y))
                                                                              eq₁ ⟩
              subst B₂ eq₁
                (to (B₁↣B₂ x₁) $
                 subst B₁ (_≈_.left-inverse-of A₁≈A₂ x₁) $
                 subst B₁ (sym (_≈_.left-inverse-of A₁≈A₂ x₁)) x₂)       ≡⟨ cong (subst B₂ eq₁ ⊚ to (B₁↣B₂ x₁)) $ subst-subst B₁ _ _ _ ⟩
              subst B₂ eq₁
                (to (B₁↣B₂ x₁) $
                 subst B₁ (trans (sym (_≈_.left-inverse-of A₁≈A₂ x₁))
                                 (_≈_.left-inverse-of A₁≈A₂ x₁))
                          x₂)                                            ≡⟨ cong (λ p → subst B₂ eq₁ (to (B₁↣B₂ x₁) (subst B₁ p x₂))) $
                                                                                 trans-symˡ _ ⟩
              subst B₂ eq₁ (to (B₁↣B₂ x₁) $ subst B₁ (refl _) x₂)        ≡⟨ cong (subst B₂ eq₁ ⊚ to (B₁↣B₂ x₁)) $
                                                                                 subst-refl B₁ x₂ ⟩
              subst B₂ eq₁ (to (B₁↣B₂ x₁) x₂)                            ≡⟨ eq₂ ⟩∎
              to (B₁↣B₂ y₁) y₂                                           ∎
        in
        subst B₁ (_≈_.injective A₁≈A₂ eq₁) x₂  ≡⟨ _↣_.injective (B₁↣B₂ y₁) lemma ⟩∎
        y₂                                     ∎) ⊚
      _↔_.from Σ-≡,≡↔≡

∃-preserves-surjections :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
    {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ↠ B₂ (_≈_.to A₁≈A₂ x)) →
  Σ A₁ B₁ ↠ Σ A₂ B₂
∃-preserves-surjections {A₁ = A₁} {A₂} {B₁} {B₂} A₁≈A₂ B₁↠B₂ = record
  { equivalence      = equivalence′
  ; right-inverse-of = right-inverse-of′
  }
  where
  open _↠_

  equivalence′ : Σ A₁ B₁ ⇔ Σ A₂ B₂
  equivalence′ = ∃-preserves-equivalences A₁≈A₂ (equivalence ⊚ B₁↠B₂)

  abstract
    right-inverse-of′ :
      ∀ p → _⇔_.to equivalence′ (_⇔_.from equivalence′ p) ≡ p
    right-inverse-of′ = λ p → _↔_.to Σ-≡,≡↔≡
      ( _≈_.right-inverse-of A₁≈A₂ (proj₁ p)
      , (subst B₂ (_≈_.right-inverse-of A₁≈A₂ (proj₁ p))
           (to (B₁↠B₂ _) (from (B₁↠B₂ _)
              (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂ (proj₁ p)))
                 (proj₂ p))))                                         ≡⟨ cong (subst B₂ _) $ right-inverse-of (B₁↠B₂ _) _ ⟩
         subst B₂ (_≈_.right-inverse-of A₁≈A₂ (proj₁ p))
           (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂ (proj₁ p)))
              (proj₂ p))                                              ≡⟨ subst-subst-sym B₂ _ _ ⟩∎
         proj₂ p ∎)
      )

∃-preserves-bijections :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
    {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ↔ B₂ (_≈_.to A₁≈A₂ x)) →
  Σ A₁ B₁ ↔ Σ A₂ B₂
∃-preserves-bijections {A₁ = A₁} {A₂} {B₁} {B₂} A₁≈A₂ B₁↔B₂ = record
  { surjection      = surjection′
  ; left-inverse-of = left-inverse-of′
  }
  where
  open _↔_

  surjection′ : Σ A₁ B₁ ↠ Σ A₂ B₂
  surjection′ = ∃-preserves-surjections A₁≈A₂ (surjection ⊚ B₁↔B₂)

  abstract
    left-inverse-of′ :
      ∀ p → _↠_.from surjection′ (_↠_.to surjection′ p) ≡ p
    left-inverse-of′ = λ p → _↔_.to Σ-≡,≡↔≡
      ( _≈_.left-inverse-of A₁≈A₂ (proj₁ p)
      , (subst B₁ (_≈_.left-inverse-of A₁≈A₂ (proj₁ p))
           (from (B₁↔B₂ _)
              (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂
                                (_≈_.to A₁≈A₂ (proj₁ p))))
                 (to (B₁↔B₂ _) (proj₂ p))))                        ≡⟨ push-subst B₂ (λ x → from (B₁↔B₂ x))
                                                                        (_≈_.left-inverse-of A₁≈A₂ (proj₁ p)) ⟩
         from (B₁↔B₂ _)
           (subst B₂ (cong (_≈_.to A₁≈A₂)
                           (_≈_.left-inverse-of A₁≈A₂ (proj₁ p)))
              (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂
                                (_≈_.to A₁≈A₂ (proj₁ p))))
                 (to (B₁↔B₂ _) (proj₂ p))))                        ≡⟨ cong (λ eq → from (B₁↔B₂ _)
                                                                                     (subst B₂ eq
                                                                                        (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂ _))
                                                                                           (to (B₁↔B₂ _) (proj₂ p))))) $
                                                                           _≈_.left-right-lemma A₁≈A₂ _ ⟩
         from (B₁↔B₂ _)
           (subst B₂ (_≈_.right-inverse-of A₁≈A₂
                        (_≈_.to A₁≈A₂ (proj₁ p)))
              (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂
                                (_≈_.to A₁≈A₂ (proj₁ p))))
                 (to (B₁↔B₂ _) (proj₂ p))))                        ≡⟨ cong (from (B₁↔B₂ _)) $ subst-subst-sym B₂ _ _ ⟩
         from (B₁↔B₂ _) (to (B₁↔B₂ _) (proj₂ p))                   ≡⟨ left-inverse-of (B₁↔B₂ _) _ ⟩∎
         proj₂ p                                                   ∎)
      )

-- Σ preserves weak equivalence.

Σ-preserves : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
              (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ≈ B₂ (_≈_.to A₁≈A₂ x)) →
              Σ A₁ B₁ ≈ Σ A₂ B₂
Σ-preserves A₁≈A₂ B₁≈B₂ = bijection⇒weak-equivalence $
  ∃-preserves-bijections A₁≈A₂ (_≈_.bijection ⊚ B₁≈B₂)

-- Π preserves weak equivalence (assuming extensionality).

Π-preserves :
  ∀ {a₁ a₂ b₁ b₂} →
  ({A : Set (a₁ ⊔ a₂)} {B : A → Set (b₁ ⊔ b₂)} → Extensionality A B) →
  {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂} →
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ≈ B₂ (_≈_.to A₁≈A₂ x)) →
  ((x : A₁) → B₁ x) ≈ ((x : A₂) → B₂ x)
Π-preserves {a₁} {a₂} {b₁} {b₂} ext
            {A₁ = A₁} {A₂} {B₁} {B₂} A₁≈A₂ B₁≈B₂ =
  bijection⇒weak-equivalence record
    { surjection = record
      { equivalence = record
        { to   = to′
        ; from = from′
        }
      ; right-inverse-of = right-inverse-of′
      }
    ; left-inverse-of = left-inverse-of′
    }
  where
  open _≈_

  to′ : ((x : A₁) → B₁ x) → (x : A₂) → B₂ x
  to′ f x = subst B₂ (right-inverse-of A₁≈A₂ x)
                  (to (B₁≈B₂ (from A₁≈A₂ x))
                      (f (from A₁≈A₂ x)))

  from′ : ((x : A₂) → B₂ x) → (x : A₁) → B₁ x
  from′ f x = from (B₁≈B₂ x) (f (to A₁≈A₂ x))

  abstract
    right-inverse-of′ : ∀ f → to′ (from′ f) ≡ f
    right-inverse-of′ = λ f → lower-extensionality a₁ b₁ ext λ x →
      subst B₂ (right-inverse-of A₁≈A₂ x)
            (to (B₁≈B₂ (from A₁≈A₂ x))
                (from (B₁≈B₂ (from A₁≈A₂ x))
                      (f (to A₁≈A₂ (from A₁≈A₂ x)))))  ≡⟨ cong (subst B₂ (right-inverse-of A₁≈A₂ x)) $
                                                               right-inverse-of (B₁≈B₂ _) _ ⟩
      subst B₂ (right-inverse-of A₁≈A₂ x)
            (f (to A₁≈A₂ (from A₁≈A₂ x)))              ≡⟨ elim (λ {x y} x≡y → subst B₂ x≡y (f x) ≡ f y)
                                                               (λ x → subst-refl B₂ (f x))
                                                               (right-inverse-of A₁≈A₂ x) ⟩∎
      f x                                              ∎

    left-inverse-of′ : ∀ f → from′ (to′ f) ≡ f
    left-inverse-of′ = λ f → lower-extensionality a₂ b₂ ext λ x →
      from (B₁≈B₂ x)
           (subst B₂ (right-inverse-of A₁≈A₂ (to A₁≈A₂ x))
                  (to (B₁≈B₂ (from A₁≈A₂ (to A₁≈A₂ x)))
                      (f (from A₁≈A₂ (to A₁≈A₂ x)))))             ≡⟨ cong (λ eq → from (B₁≈B₂ x)
                                                                                    (subst B₂ eq
                                                                                       (to (B₁≈B₂ (from A₁≈A₂ (to A₁≈A₂ x)))
                                                                                          (f (from A₁≈A₂ (to A₁≈A₂ x))))))
                                                                          (sym $ left-right-lemma A₁≈A₂ x) ⟩
      from (B₁≈B₂ x)
           (subst B₂ (cong (to A₁≈A₂) (left-inverse-of A₁≈A₂ x))
                  (to (B₁≈B₂ (from A₁≈A₂ (to A₁≈A₂ x)))
                      (f (from A₁≈A₂ (to A₁≈A₂ x)))))             ≡⟨ sym $ push-subst B₂ (λ x y → from (B₁≈B₂ x) y)
                                                                                      (left-inverse-of A₁≈A₂ x) ⟩
      subst B₁ (left-inverse-of A₁≈A₂ x)
            (from (B₁≈B₂ (from A₁≈A₂ (to A₁≈A₂ x)))
                  (to (B₁≈B₂ (from A₁≈A₂ (to A₁≈A₂ x)))
                      (f (from A₁≈A₂ (to A₁≈A₂ x)))))             ≡⟨ cong (subst B₁ (left-inverse-of A₁≈A₂ x)) $
                                                                       left-inverse-of (B₁≈B₂ _) _ ⟩
      subst B₁ (left-inverse-of A₁≈A₂ x)
            (f (from A₁≈A₂ (to A₁≈A₂ x)))                         ≡⟨ elim (λ {x y} x≡y → subst B₁ x≡y (f x) ≡ f y)
                                                                          (λ x → subst-refl B₁ (f x))
                                                                          (left-inverse-of A₁≈A₂ x) ⟩∎
      f x                                                         ∎

-- Weak equivalence preserves weak equivalences (assuming
-- extensionality).

≈-preserves :
  ∀ {a₁ a₂ b₁ b₂} →
  ({A : Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂)} {B : A → Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂)} →
   Extensionality A B) →
  {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : Set b₁} {B₂ : Set b₂} →
  A₁ ≈ A₂ → B₁ ≈ B₂ → (A₁ ≈ B₁) ≈ (A₂ ≈ B₂)
≈-preserves {a₁} {a₂} {b₁} {b₂} ext {A₁} {A₂} {B₁} {B₂} A₁≈A₂ B₁≈B₂ =
  bijection⇒weak-equivalence (record
    { surjection = record
      { equivalence = record
        { to   = λ A₁≈B₁ → B₁≈B₂ ∘ A₁≈B₁ ∘ inverse A₁≈A₂
        ; from = λ A₂≈B₂ → inverse B₁≈B₂ ∘ A₂≈B₂ ∘ A₁≈A₂
        }
      ; right-inverse-of = to∘from
      }
    ; left-inverse-of = from∘to
    })
  where
  open _≈_

  abstract
    to∘from :
      (A₂≈B₂ : A₂ ≈ B₂) →
      B₁≈B₂ ∘ (inverse B₁≈B₂ ∘ A₂≈B₂ ∘ A₁≈A₂) ∘ inverse A₁≈A₂ ≡ A₂≈B₂
    to∘from A₂≈B₂ =
      lift-equality (lower-extensionality (a₁ ⊔ b₁) (a₁ ⊔ b₁) ext) λ x →
          to B₁≈B₂ (from B₁≈B₂ (to A₂≈B₂ (to A₁≈A₂ (from A₁≈A₂ x))))  ≡⟨ right-inverse-of B₁≈B₂ _ ⟩
          to A₂≈B₂ (to A₁≈A₂ (from A₁≈A₂ x))                          ≡⟨ cong (to A₂≈B₂) $ right-inverse-of A₁≈A₂ _ ⟩∎
          to A₂≈B₂ x                                                  ∎

    from∘to :
      (A₁≈B₁ : A₁ ≈ B₁) →
      inverse B₁≈B₂ ∘ (B₁≈B₂ ∘ A₁≈B₁ ∘ inverse A₁≈A₂) ∘ A₁≈A₂ ≡ A₁≈B₁
    from∘to A₁≈B₁ =
      lift-equality (lower-extensionality (a₂ ⊔ b₂) (a₂ ⊔ b₂) ext) λ x →
          from B₁≈B₂ (to B₁≈B₂ (to A₁≈B₁ (from A₁≈A₂ (to A₁≈A₂ x))))  ≡⟨ left-inverse-of B₁≈B₂ _ ⟩
          to A₁≈B₁ (from A₁≈A₂ (to A₁≈A₂ x))                          ≡⟨ cong (to A₁≈B₁) $ left-inverse-of A₁≈A₂ _ ⟩∎
          to A₁≈B₁ x                                                  ∎

-- Weak equivalence preserves bijections (assuming extensionality).

≈-preserves-bijections :
  ∀ {a₁ a₂ b₁ b₂} →
  ({A : Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂)} {B : A → Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂)} →
   Extensionality A B) →
  {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : Set b₁} {B₂ : Set b₂} →
  A₁ ↔ A₂ → B₁ ↔ B₂ → (A₁ ≈ B₁) ↔ (A₂ ≈ B₂)
≈-preserves-bijections ext A₁↔A₂ B₁↔B₂ =
  _≈_.bijection $
    ≈-preserves ext (bijection⇒weak-equivalence A₁↔A₂)
                    (bijection⇒weak-equivalence B₁↔B₂)
