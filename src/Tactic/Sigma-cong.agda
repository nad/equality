------------------------------------------------------------------------
-- Tactics for proving instances of Σ-cong (and Surjection.Σ-cong)
-- with "better" computational behaviour
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Tactic.Sigma-cong
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence as L using (_⇔_)
open import Prelude

open import Bijection eq as B using (_↔_)
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq as F hiding (id; _∘_)
open import Monad eq
open import Surjection eq as S using (_↠_)
open import TC-monad eq hiding (Type)

private

  variable
    a b                 : Level
    A B                 : Type a
    f g k k₁ k₂ p q x y : A
    P Q                 : A → Type p

------------------------------------------------------------------------
-- Σ-cong-refl

-- Building blocks used to construct the proofs in Σ-cong-refl.

record Σ-cong-refl-proofs
         (k : Kind)
         (A : Type a) (B : Type b) (P : A → Type p) (Q : B → Type q) :
         Type (lsuc (a ⊔ b ⊔ p ⊔ q)) where
  field
    refl₁ : (x : Σ B Q) → x ≡ x
    refl₂ : (x : Σ A P) → x ≡ x

    cong-refl₃ :
      (f : Σ A P → Σ B Q)
      (p : Σ A P) →
      cong f (refl p) ≡ refl (f p)

    →↝ :
      (A⇔B : A ⇔ B)
      (P→Q : ∀ x → P x → Q (_⇔_.to A⇔B x))
      (Q→P : ∀ x → Q x → P (_⇔_.from A⇔B x)) →
      (eq₁ : (p : Σ B Q) →
             Σ-map (_⇔_.to A⇔B) (P→Q _)
               (Σ-map (_⇔_.from A⇔B) (Q→P _) p) ≡
             p) →
      (eq₂ : (p : Σ A P) →
             Σ-map (_⇔_.from A⇔B) (Q→P _)
               (Σ-map (_⇔_.to A⇔B) (P→Q _) p) ≡
             p) →
      ((p : Σ A P) →
       cong (Σ-map (_⇔_.to A⇔B) (P→Q _)) (eq₂ p) ≡
       eq₁ (Σ-map (_⇔_.to A⇔B) (P→Q _) p)) →
      Σ A P ↝[ k ] Σ B Q

instance

  -- The building blocks can be proved.

  instance-of-Σ-cong-refl-proofs :
    Σ-cong-refl-proofs k A B P Q
  instance-of-Σ-cong-refl-proofs = λ where
      .refl₁ _              → refl _
      .refl₂ _              → refl _
      .cong-refl₃ _ _       → cong-refl _
      .→↝ A⇔B P→Q Q→P p q r →
        from-equivalence $
        Eq.⟨   Σ-map (_⇔_.to   A⇔B) (P→Q _)
           , ( Σ-map (_⇔_.from A⇔B) (Q→P _)
             , p
             , q
             , r
             )
           ⟩
    where
    open Σ-cong-refl-proofs

private

  -- Used to implement Σ-cong-refl.
  --
  -- The constructed term is returned.

  Σ-cong-refl-tactic :
    Σ-cong-refl-proofs k A B P Q →
    (A⇔B : A ⇔ B) → (∀ x → P x ⇔ Q (_⇔_.to A⇔B x)) →
    Term → TC Term
  Σ-cong-refl-tactic proofs A⇔B P⇔Q goal = do
    refl₁      ← quoteTC (Σ-cong-refl-proofs.refl₁      proofs)
    refl₂      ← quoteTC (Σ-cong-refl-proofs.refl₂      proofs)
    cong-refl₃ ← quoteTC (Σ-cong-refl-proofs.cong-refl₃ proofs
                            (Σ-map (_⇔_.to A⇔B) (_⇔_.to (P⇔Q _))))
    proofs     ← quoteTC proofs
    P→Q        ← quoteTC (_⇔_.to   ∘ P⇔Q)
    Q→P        ← quoteTC (_⇔_.from ∘ P⇔Q ∘ _⇔_.from A⇔B)
    A⇔B        ← quoteTC A⇔B
    let t = def (quote Σ-cong-refl-proofs.→↝)
                (varg proofs ∷
                 varg A⇔B ∷
                 varg P→Q ∷
                 varg Q→P ∷
                 varg refl₁ ∷
                 varg refl₂ ∷
                 varg cong-refl₃ ∷
                 [])
    unify goal t
    return t

macro

  -- A macro that tries to prove Σ A P ↝[ k₃ ] Σ B Q.
  --
  -- If k₃ is symmetric, then the two directions of the proof are
  -- constructed in the following way:
  --
  -- * The forward direction is a function from Σ A P to Σ B Q,
  --   constructed in the "obvious" way using the forward directions
  --   of the two supplied proofs.
  --
  -- * The other direction is a function from Σ B (Q ∘ f ∘ g) to
  --   Σ A P, where f and g are the two directions of the first proof.
  --   This function is also constructed in the "obvious" way, using
  --   the right-to-left directions of the two supplied proofs. It is
  --   assumed that Q ∘ f ∘ g is definitionally equal to Q.
  --
  -- The two functions are assumed to be definitionally equal, so that
  -- they can be proved to be inverses of each other (pointwise) using
  -- reflexivity.

  Σ-cong-refl :
    {k₁ k₂ : Symmetric-kind} {k₃ : Kind}
    ⦃ proofs : Σ-cong-refl-proofs k₃ A B P Q ⦄ →
    (A↝B : A ↝[ ⌊ k₁ ⌋-sym ] B) →
    (∀ x → P x ↝[ ⌊ k₂ ⌋-sym ] Q (_⇔_.to (sym→⇔ A↝B) x)) →
    Term → TC ⊤
  Σ-cong-refl ⦃ proofs = proofs ⦄ A↝B P↝Q goal = do
    Σ-cong-refl-tactic proofs (sym→⇔ A↝B) (sym→⇔ ∘ P↝Q) goal
    return _

private

  -- Some unit tests.

  t₁ : (A × A) ≃ (A × A)
  t₁ = Σ-cong-refl L.id λ _ → B.id

  _ : _≃_.to t₁ p ≡ p
  _ = refl _

  _ : _≃_.from t₁ p ≡ p
  _ = refl _

  _ :
    {p : A × A} →
    _≃_.right-inverse-of t₁ p ≡ refl _
  _ = refl _

  _ :
    {p : A × A} →
    _≃_.left-inverse-of t₁ p ≡ refl _
  _ = refl _

  t₂ : (A × A) ↔ (A × A)
  t₂ = Σ-cong-refl Eq.id λ _ → L.id

  _ : _↔_.to t₂ p ≡ p
  _ = refl _

  _ : _↔_.from t₂ p ≡ p
  _ = refl _

  _ :
    {p : A × A} →
    _↔_.right-inverse-of t₂ p ≡ refl _
  _ = refl _

  _ :
    {p : A × A} →
    _↔_.left-inverse-of t₂ p ≡ refl _
  _ = refl _

  t₃ :
    {P : A → B → Type p} {Q : A → B → (∀ x y → P x y) → Type q} →
    (∃ λ (f : ∀ x y → P x y) → ∀ x y → Q x y f) ≃
    (∃ λ (f : ∀ y x → P x y) → ∀ y x → Q x y (flip f))
  t₃ = Σ-cong-refl Π-comm λ _ → Π-comm

  _ : _≃_.to t₃ p ≡ Σ-map flip flip p
  _ = refl _

  _ : _≃_.from t₃ p ≡ Σ-map flip flip p
  _ = refl _

  _ :
    {P : A → B → Type p} {Q : A → B → (∀ x y → P x y) → Type q}
    {p : ∃ λ (f : ∀ y x → P x y) → ∀ y x → Q x y (flip f)} →
    _≃_.right-inverse-of (t₃ {Q = Q}) p ≡ refl _
  _ = refl _

  _ :
    {P : A → B → Type p} {Q : A → B → (∀ x y → P x y) → Type q}
    {p : ∃ λ (f : ∀ x y → P x y) → ∀ x y → Q x y f} →
    _≃_.left-inverse-of (t₃ {Q = Q}) p ≡ refl _
  _ = refl _

  -- The following proof—implemented using Σ-cong—is, at the time of
  -- writing, "worse".

  t₃′ :
    {P : A → B → Type p} {Q : A → B → (∀ x y → P x y) → Type q} →
    (∃ λ (f : ∀ x y → P x y) → ∀ x y → Q x y f) ≃
    (∃ λ (f : ∀ y x → P x y) → ∀ y x → Q x y (flip f))
  t₃′ = Eq.↔⇒≃ $ Σ-cong Π-comm λ _ → Π-comm

  _ : _≃_.to t₃′ p ≡ Σ-map flip flip p
  _ = refl _

  _ :
    ∀ {P : A → B → Type p} {Q : A → B → (∀ x y → P x y) → Type q} {p} →
    _≃_.from (t₃′ {Q = Q}) p ≡
    Σ-map flip
      (flip ∘ subst (λ f → ∀ y x → Q x y (flip f)) (sym (refl _)))
      p
  _ = refl _

------------------------------------------------------------------------
-- Σ-cong-id

-- Building blocks used to construct the proofs in Σ-cong-id.

record Σ-cong-id-proofs
         (k : Kind) (A : Type a) (B : Type b) (P : B → Type p) :
         Type (lsuc (a ⊔ b ⊔ p)) where
  field
    refl₁ : (x : Σ B P) → x ≡ x

    subst-refl₂ :
      (A≃B : A ≃ B)
      ((x , y) : Σ A (P ∘ _≃_.to A≃B)) →
      subst P (refl (_≃_.to A≃B x)) y ≡ y

    →↝ :
      (A≃B : A ≃ B)
      (g : ∀ x → P x → P (_≃_.to A≃B (_≃_.from A≃B x))) →
      ((p : Σ B P) →
       Σ-map (_≃_.to A≃B) id (Σ-map (_≃_.from A≃B) (g _) p) ≡ p) →
      (((x , y) : Σ A (P ∘ _≃_.to A≃B)) →
       subst P (_≃_.right-inverse-of A≃B (_≃_.to A≃B x)) (g _ y) ≡ y) →
      Σ A (P ∘ _≃_.to A≃B) ↝[ k ] Σ B P

instance

  -- The building blocks can be proved.

  instance-of-Σ-cong-id-proofs : Σ-cong-id-proofs k A B P
  instance-of-Σ-cong-id-proofs {P} = λ where
      .refl₁           → refl
      .subst-refl₂ _ _ → subst-refl _ _
      .→↝ A≃B g p q    →
        let open _≃_ A≃B in
        from-equivalence $
        Eq.↔→≃
          (Σ-map to id)
          (Σ-map from (g _))
          p
          (λ (x , y) →
             Σ-≡,≡→≡ (left-inverse-of _)
               (subst (P ∘ to) (left-inverse-of x) (g _ y)     ≡⟨ subst-∘ _ _ _ ⟩
                subst P (cong to (left-inverse-of x)) (g _ y)  ≡⟨ cong (λ eq → subst P eq _) (left-right-lemma x) ⟩
                subst P (right-inverse-of (to x)) (g _ y)      ≡⟨ q _ ⟩∎
                y                                              ∎))
    where
    open Σ-cong-id-proofs

private

  -- Used to implement Σ-cong-id.
  --
  -- The constructed term is returned.

  Σ-cong-id-tactic :
    Σ-cong-id-proofs k A B P →
    A ≃ B → Term → TC Term
  Σ-cong-id-tactic proofs A≃B goal = do
    refl₁       ← quoteTC (Σ-cong-id-proofs.refl₁       proofs)
    subst-refl₂ ← quoteTC (Σ-cong-id-proofs.subst-refl₂ proofs A≃B)
    proofs      ← quoteTC proofs
    A≃B         ← quoteTC A≃B
    let t = def (quote Σ-cong-id-proofs.→↝)
                (varg proofs ∷
                 varg A≃B ∷
                 varg (lam visible $ abs "_" $
                       lam visible $ abs "x" $
                       var 0 []) ∷
                 varg refl₁ ∷
                 varg subst-refl₂ ∷
                 [])
    unify goal t
    return t

macro

  -- A macro that tries to prove
  -- Σ A (P ∘ from-isomorphism eq) ↝[ k₂ ] Σ B P, given that there is
  -- a proof eq : A ↔[ k₁ ] B for which the "right inverse of" proof
  -- is definitionally equal to reflexivity. If k₂ is surjection,
  -- bijection or equivalence, then the "right inverse of" component
  -- of the resulting proof is reflexivity.

  Σ-cong-id :
    ⦃ proofs : Σ-cong-id-proofs k₂ A B P ⦄ →
    A ↔[ k₁ ] B → Term → TC ⊤
  Σ-cong-id ⦃ proofs = proofs ⦄ A↝B goal = do
    Σ-cong-id-tactic proofs (from-isomorphism A↝B) goal
    return _

private

  -- Some unit tests.

  t₄ : (A × A) ↔ (A × A)
  t₄ = Σ-cong-id B.id

  _ : _↔_.to t₄ p ≡ p
  _ = refl _

  _ : _↔_.from t₄ p ≡ p
  _ = refl _

  _ :
    {p : A × A} →
    _↔_.right-inverse-of t₄ p ≡ refl _
  _ = refl _

  t₅ : (∃ λ (x : ⊥₀ ⊎ A) → _↔_.to ⊎-left-identity x ≡ y) ≃
       (∃ λ (x : A) → x ≡ y)
  t₅ = Σ-cong-id ⊎-left-identity

  _ : _≃_.to t₅ (inj₂ x , p) ≡ (x , p)
  _ = refl _

  _ : _≃_.from t₅ p ≡ Σ-map inj₂ id p
  _ = refl _

  _ :
    {p : ∃ λ (x : A) → x ≡ y} →
    _≃_.right-inverse-of t₅ p ≡ refl _
  _ = refl _

  -- The following proof—implemented using Σ-cong—is, at the time of
  -- writing, "worse".

  t₅′ : (∃ λ (x : ⊥₀ ⊎ A) → _↔_.to ⊎-left-identity x ≡ y) ≃
        (∃ λ (x : A) → x ≡ y)
  t₅′ = Eq.↔⇒≃ $ Σ-cong ⊎-left-identity λ _ → F.id

  _ : _≃_.to t₅′ (inj₂ x , p) ≡ (x , p)
  _ = refl _

  _ : _≃_.from t₅′ p ≡
      Σ-map inj₂ (subst (_≡ y) (sym (refl _))) p
  _ = refl _

------------------------------------------------------------------------
-- Σ-cong-id-↠

-- Building blocks used to construct the proofs in Σ-cong-id-↠.

record Σ-cong-id-↠-proofs
         (A : Type a) (B : Type b) (P : B → Type p) :
         Type (lsuc (a ⊔ b ⊔ p)) where
  field
    refl₁ : (x : Σ B P) → x ≡ x

    →↠ :
      (A↠B : A ↠ B)
      (g : ∀ x → P x → P (_↠_.to A↠B (_↠_.from A↠B x))) →
      ((p : Σ B P) →
       Σ-map (_↠_.to A↠B) id (Σ-map (_↠_.from A↠B) (g _) p) ≡ p) →
      Σ A (P ∘ _↠_.to A↠B) ↠ Σ B P

instance

  -- The building blocks can be proved.

  instance-of-Σ-cong-id-↠-proofs : Σ-cong-id-↠-proofs A B P
  instance-of-Σ-cong-id-↠-proofs {P} = λ where
      .refl₁      → refl
      .→↠ A↠B g p → record
        { logical-equivalence = record
          { to   = Σ-map (_↠_.to   A↠B) id
          ; from = Σ-map (_↠_.from A↠B) (g _)
          }
        ; right-inverse-of = p
        }
    where
    open Σ-cong-id-↠-proofs

private

  -- Used to implement Σ-cong-id-↠.
  --
  -- The constructed term is returned.

  Σ-cong-id-↠-tactic :
    Σ-cong-id-↠-proofs A B P →
    A ↠ B → Term → TC Term
  Σ-cong-id-↠-tactic proofs A↠B goal = do
    refl₁  ← quoteTC (Σ-cong-id-↠-proofs.refl₁ proofs)
    proofs ← quoteTC proofs
    A↠B    ← quoteTC A↠B
    let t = def (quote Σ-cong-id-↠-proofs.→↠)
                (varg proofs ∷
                 varg A↠B ∷
                 varg (lam visible $ abs "_" $
                       lam visible $ abs "x" $
                       var 0 []) ∷
                 varg refl₁ ∷
                 [])
    unify goal t
    return t

macro

  -- A macro that tries to prove Σ A (P ∘ _↠_.to eq) ↠ Σ B P, given a
  -- proof eq for which _↠_.to eq ∘ _↠_.from eq is definitionally
  -- equal to the identity function. The right-inverse-of component of
  -- the resulting proof is reflexivity.

  Σ-cong-id-↠ :
    ⦃ proofs : Σ-cong-id-↠-proofs A B P ⦄ →
    A ↠ B → Term → TC ⊤
  Σ-cong-id-↠ ⦃ proofs = proofs ⦄ A↠B goal = do
    Σ-cong-id-↠-tactic proofs A↠B goal
    return _

private

  -- Some unit tests.

  t₆ : (A × A) ↠ (A × A)
  t₆ = Σ-cong-id-↠ S.id

  _ : _↠_.to t₆ p ≡ p
  _ = refl _

  _ : _↠_.from t₆ p ≡ p
  _ = refl _

  _ :
    {p : A × A} →
    _↠_.right-inverse-of t₆ p ≡ refl _
  _ = refl _

  t₇ :
    (∃ λ (f : (x : A ⊎ B) → P x) → (f ∘ inj₁ , f ∘ inj₂) ≡ q) ↠
    (∃ λ (p : ((x : A) → P (inj₁ x)) ×
              ((y : B) → P (inj₂ y))) →
       p ≡ q)
  t₇ = Σ-cong-id-↠ Π⊎↠Π×Π

  _ : _↠_.to t₇ (f , p) ≡ ((f ∘ inj₁ , f ∘ inj₂) , p)
  _ = refl _

  _ : _↠_.from t₇ ((f , g) , p) ≡ ([ f , g ] , p)
  _ = refl _

  _ :
    ∀ {P : A ⊎ B → Type p} {q}
      {p : ∃ λ (p : ((x : A) → P (inj₁ x)) ×
                    ((y : B) → P (inj₂ y))) →
             p ≡ q} →
    _↠_.right-inverse-of (t₇ {P = P}) p ≡ refl p
  _ = refl _

  -- The following proof—implemented using S.Σ-cong—is, at the time of
  -- writing, "worse".

  t₇′ :
    (∃ λ (f : (x : A ⊎ B) → P x) → (f ∘ inj₁ , f ∘ inj₂) ≡ q) ↠
    (∃ λ (p : ((x : A) → P (inj₁ x)) ×
              ((y : B) → P (inj₂ y))) →
       p ≡ q)
  t₇′ = S.Σ-cong Π⊎↠Π×Π λ _ → F.id

  _ : _↠_.to t₇′ (f , p) ≡ ((f ∘ inj₁ , f ∘ inj₂) , p)
  _ = refl _

  _ : _↠_.from t₇′ ((f , g) , p) ≡
      ([ f , g ] , subst (_≡ q) (sym (refl _)) p)
  _ = refl _
