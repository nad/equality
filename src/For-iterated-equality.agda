------------------------------------------------------------------------
-- Some results related to the For-iterated-equality predicate
-- transformer
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module For-iterated-equality
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_)
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq
open import List eq
open import Nat eq
open import Surjection eq as Surj using (_↠_)

private
  variable
    a b ℓ p q : Level
    A B       : Type a
    P Q R     : Type p → Type p
    x y       : A
    k         : Kind
    n         : ℕ

------------------------------------------------------------------------
-- Some lemmas related to nested occurrences of For-iterated-equality

-- Nested uses of For-iterated-equality can be merged.

For-iterated-equality-For-iterated-equality′ :
  {A : Type a} →
  ∀ m n →
  For-iterated-equality m (For-iterated-equality n P) A ↝[ a ∣ a ]
  For-iterated-equality (m + n) P A
For-iterated-equality-For-iterated-equality′ zero _ _ = F.id

For-iterated-equality-For-iterated-equality′ {P = P} {A = A}
                                             (suc m) n ext =
  ((x y : A) →
   For-iterated-equality m (For-iterated-equality n P) (x ≡ y))  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                     For-iterated-equality-For-iterated-equality′ m n ext) ⟩□
  ((x y : A) → For-iterated-equality (m + n) P (x ≡ y))          □

-- A variant of the previous result.

For-iterated-equality-For-iterated-equality :
  {A : Type a} →
  ∀ m n →
  For-iterated-equality m (For-iterated-equality n P) A ↝[ a ∣ a ]
  For-iterated-equality (n + m) P A
For-iterated-equality-For-iterated-equality {P = P} {A = A}
                                            m n ext =
  For-iterated-equality m (For-iterated-equality n P) A  ↝⟨ For-iterated-equality-For-iterated-equality′ m n ext ⟩
  For-iterated-equality (m + n) P A                      ↝⟨ ≡⇒↝ _ $ cong (λ n → For-iterated-equality n P A) (+-comm m) ⟩□
  For-iterated-equality (n + m) P A                      □

------------------------------------------------------------------------
-- Preservation lemmas for For-iterated-equality

-- A preservation lemma for the predicate.

For-iterated-equality-cong₁ :
  {P Q : Type ℓ → Type ℓ} →
  Extensionality? k ℓ ℓ →
  ∀ n →
  (∀ {A} → P A ↝[ k ] Q A) →
  For-iterated-equality n P A ↝[ k ] For-iterated-equality n Q A
For-iterated-equality-cong₁ _ zero P↝Q = P↝Q

For-iterated-equality-cong₁ {A = A} {P = P} {Q = Q} ext (suc n) P↝Q =
  ((x y : A) → For-iterated-equality n P (x ≡ y))  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                       For-iterated-equality-cong₁ ext n P↝Q) ⟩□
  ((x y : A) → For-iterated-equality n Q (x ≡ y))  □

-- Preservation lemmas for both the predicate and the type.

For-iterated-equality-cong-→ :
  ∀ n →
  (∀ {A B} → A ↠ B → P A → Q B) →
  A ↠ B →
  For-iterated-equality n P A → For-iterated-equality n Q B
For-iterated-equality-cong-→ zero P↝Q A↠B = P↝Q A↠B

For-iterated-equality-cong-→ {P = P} {Q = Q} {A = A} {B = B}
                             (suc n) P↝Q A↠B =
  ((x y : A) → For-iterated-equality n P (x ≡ y))  ↝⟨ (Π-cong-contra-→ (_↠_.from A↠B) λ _ → Π-cong-contra-→ (_↠_.from A↠B) λ _ →
                                                       For-iterated-equality-cong-→ n P↝Q $ Surj.↠-≡ A↠B) ⟩□
  ((x y : B) → For-iterated-equality n Q (x ≡ y))  □

For-iterated-equality-cong :
  {P : Type p → Type p} {Q : Type q → Type q} →
  Extensionality? k (p ⊔ q) (p ⊔ q) →
  ∀ n →
  (∀ {A B} → A ↔ B → P A ↝[ k ] Q B) →
  A ↔ B →
  For-iterated-equality n P A ↝[ k ] For-iterated-equality n Q B
For-iterated-equality-cong _ zero P↝Q A↔B = P↝Q A↔B

For-iterated-equality-cong {A = A} {B = B} {P = P} {Q = Q}
                           ext (suc n) P↝Q A↔B =
  ((x y : A) → For-iterated-equality n P (x ≡ y))  ↝⟨ (Π-cong ext A↔B λ _ → Π-cong ext A↔B λ _ →
                                                       For-iterated-equality-cong ext n P↝Q $ inverse $ _≃_.bijection $
                                                       Eq.≃-≡ $ from-isomorphism A↔B) ⟩□
  ((x y : B) → For-iterated-equality n Q (x ≡ y))  □

------------------------------------------------------------------------
-- Some "closure properties" for the type

private

  -- A lemma.

  lift≡lift↔ : lift {ℓ = ℓ} x ≡ lift y ↔ x ≡ y
  lift≡lift↔ = inverse $ _≃_.bijection $ Eq.≃-≡ $ Eq.↔⇒≃ Bijection.↑↔

-- Closure properties for ⊤.

For-iterated-equality-↑-⊤ :
  Extensionality? k ℓ ℓ →
  ∀ n →
  (∀ {A B} → A ↔ B → P A ↝[ k ] P B) →
  P (↑ ℓ ⊤) ↝[ k ] For-iterated-equality n P (↑ ℓ ⊤)
For-iterated-equality-↑-⊤ _ zero _ = F.id

For-iterated-equality-↑-⊤ {P = P} ext (suc n) resp =
  P (↑ _ ⊤)                                                ↝⟨ For-iterated-equality-↑-⊤ ext n resp ⟩
  For-iterated-equality n P (↑ _ ⊤)                        ↝⟨ For-iterated-equality-cong ext n resp $
                                                              inverse lift≡lift↔ F.∘ inverse tt≡tt↔⊤ F.∘ Bijection.↑↔ ⟩
  For-iterated-equality n P (lift tt ≡ lift tt)            ↝⟨ inverse-ext? (λ ext → drop-⊤-left-Π ext Bijection.↑↔) ext ⟩
  ((y : ↑ _ ⊤) → For-iterated-equality n P (lift tt ≡ y))  ↝⟨ inverse-ext? (λ ext → drop-⊤-left-Π ext Bijection.↑↔) ext ⟩□
  ((x y : ↑ _ ⊤) → For-iterated-equality n P (x ≡ y))      □

For-iterated-equality-⊤ :
  Extensionality? k lzero lzero →
  ∀ n →
  (∀ {A B} → A ↔ B → P A ↝[ k ] P B) →
  P ⊤ ↝[ k ] For-iterated-equality n P ⊤
For-iterated-equality-⊤ {P = P} ext n resp =
  P ⊤                                ↝⟨ resp (inverse Bijection.↑↔) ⟩
  P (↑ _ ⊤)                          ↝⟨ For-iterated-equality-↑-⊤ ext n resp ⟩
  For-iterated-equality n P (↑ _ ⊤)  ↝⟨ For-iterated-equality-cong ext n resp Bijection.↑↔ ⟩□
  For-iterated-equality n P ⊤        □

-- Closure properties for ⊥.

For-iterated-equality-suc-⊥ :
  {P : Type p → Type p} →
  ∀ n → ⊤ ↝[ p ∣ p ] For-iterated-equality (suc n) P ⊥
For-iterated-equality-suc-⊥ {P = P} n ext =
  ⊤                                                ↝⟨ inverse-ext? Π⊥↔⊤ ext ⟩□
  ((x y : ⊥) → For-iterated-equality n P (x ≡ y))  □

For-iterated-equality-⊥ :
  {P : Type p → Type p} →
  Extensionality? k p p →
  ∀ n →
  ⊤ ↝[ k ] P ⊥ →
  ⊤ ↝[ k ] For-iterated-equality n P ⊥
For-iterated-equality-⊥ _   zero      = id
For-iterated-equality-⊥ ext (suc n) _ =
  For-iterated-equality-suc-⊥ n ext

-- A closure property for Π.

For-iterated-equality-Π :
  {A : Type a} {B : A → Type b} →
  Extensionality a b →
  ∀ n →
  (∀ {A B} → A ↔ B → Q A → Q B) →
  ({A : Type a} {B : A → Type b} →
   (∀ x → P (B x)) → Q (∀ x → B x)) →
  (∀ x → For-iterated-equality n P (B x)) →
  For-iterated-equality n Q (∀ x → B x)
For-iterated-equality-Π _ zero _ hyp = hyp

For-iterated-equality-Π {Q = Q} {P = P} {B = B} ext (suc n) resp hyp =
  (∀ x (y z : B x) → For-iterated-equality n P (y ≡ z))              ↝⟨ (λ hyp _ _ _ → hyp _ _ _) ⟩
  (∀ (f g : ∀ x → B x) x → For-iterated-equality n P (f x ≡ g x))    ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → For-iterated-equality-Π ext n resp hyp) ⟩
  ((f g : ∀ x → B x) → For-iterated-equality n Q (∀ x → f x ≡ g x))  ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → For-iterated-equality-cong _ n resp $
                                                                         from-isomorphism $ Eq.extensionality-isomorphism ext) ⟩□
  ((f g : ∀ x → B x) → For-iterated-equality n Q (f ≡ g))            □

-- A closure property for Σ.

For-iterated-equality-Σ :
  {A : Type a} {B : A → Type b} →
  ∀ n →
  (∀ {A B} → A ↔ B → R A → R B) →
  ({A : Type a} {B : A → Type b} →
   P A → (∀ x → Q (B x)) → R (Σ A B)) →
  For-iterated-equality n P A →
  (∀ x → For-iterated-equality n Q (B x)) →
  For-iterated-equality n R (Σ A B)
For-iterated-equality-Σ zero _ hyp = hyp

For-iterated-equality-Σ {R = R} {P = P} {Q = Q} {A = A} {B = B}
  (suc n) resp hyp = curry (

  ((x y : A) → For-iterated-equality n P (x ≡ y)) ×
  ((x : A) (y z : B x) → For-iterated-equality n Q (y ≡ z))            ↝⟨ (λ (hyp₁ , hyp₂) _ _ → hyp₁ _ _ , λ _ → hyp₂ _ _ _) ⟩

  (((x₁ , x₂) (y₁ , y₂) : Σ A B) →
   For-iterated-equality n P (x₁ ≡ y₁) ×
   (∀ p → For-iterated-equality n Q (subst B p x₂ ≡ y₂)))              ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → uncurry $
                                                                           For-iterated-equality-Σ n resp hyp) ⟩
  (((x₁ , x₂) (y₁ , y₂) : Σ A B) →
   For-iterated-equality n R (∃ λ (p : x₁ ≡ y₁) → subst B p x₂ ≡ y₂))  ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                                           For-iterated-equality-cong _ n resp Bijection.Σ-≡,≡↔≡) ⟩□
  ((x y : Σ A B) → For-iterated-equality n R (x ≡ y))                  □)

-- A closure property for _×_.

For-iterated-equality-× :
  {A : Type a} {B : Type b} →
  ∀ n →
  (∀ {A B} → A ↔ B → R A → R B) →
  ({A : Type a} {B : Type b} → P A → Q B → R (A × B)) →
  For-iterated-equality n P A →
  For-iterated-equality n Q B →
  For-iterated-equality n R (A × B)
For-iterated-equality-× zero _ hyp = hyp

For-iterated-equality-× {R = R} {P = P} {Q = Q} {A = A} {B = B}
  (suc n) resp hyp = curry (

  ((x y : A) → For-iterated-equality n P (x ≡ y)) ×
  ((x y : B) → For-iterated-equality n Q (x ≡ y))      ↝⟨ (λ (hyp₁ , hyp₂) _ _ → hyp₁ _ _ , hyp₂ _ _) ⟩

  (((x₁ , x₂) (y₁ , y₂) : A × B) →
   For-iterated-equality n P (x₁ ≡ y₁) ×
   For-iterated-equality n Q (x₂ ≡ y₂))                ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → uncurry $
                                                           For-iterated-equality-× n resp hyp) ⟩
  (((x₁ , x₂) (y₁ , y₂) : A × B) →
   For-iterated-equality n R (x₁ ≡ y₁ × x₂ ≡ y₂))      ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                           For-iterated-equality-cong _ n resp ≡×≡↔≡) ⟩□
  ((x y : A × B) → For-iterated-equality n R (x ≡ y))  □)

-- A closure property for ↑.

For-iterated-equality-↑ :
  {A : Type a} {Q : Type (a ⊔ ℓ) → Type (a ⊔ ℓ)} →
  Extensionality? k (a ⊔ ℓ) (a ⊔ ℓ) →
  ∀ n →
  (∀ {A B} → A ↔ B → P A ↝[ k ] Q B) →
  For-iterated-equality n P A ↝[ k ]
  For-iterated-equality n Q (↑ ℓ A)
For-iterated-equality-↑ ext n resp =
  For-iterated-equality-cong ext n resp (inverse Bijection.↑↔)

-- Closure properties for W.

For-iterated-equality-W-suc :
  {A : Type a} {B : A → Type b} →
  Extensionality b (a ⊔ b) →
  ∀ n →
  (∀ {A B} → A ↔ B → Q A → Q B) →
  ({A : Type b} {B : A → Type (a ⊔ b)} →
   (∀ x → Q (B x)) → Q (∀ x → B x)) →
  ({A : Type a} {B : A → Type (a ⊔ b)} →
   P A → (∀ x → Q (B x)) → Q (Σ A B)) →
  For-iterated-equality (suc n) P A →
  For-iterated-equality (suc n) Q (W A B)
For-iterated-equality-W-suc {Q = Q} {P = P} {B = B}
  ext n resp hyp-Π hyp-Σ fie = lemma
  where
  lemma : ∀ x y → For-iterated-equality n Q (x ≡ y)
  lemma (sup x f) (sup y g) =                                        $⟨ (λ p i → lemma (f i) _) ⟩

    (∀ p i → For-iterated-equality n Q (f i ≡ g (subst B p i)))      ↝⟨ (∀-cong _ λ _ → For-iterated-equality-Π ext n resp hyp-Π) ⟩

    (∀ p → For-iterated-equality n Q (∀ i → f i ≡ g (subst B p i)))  ↝⟨ fie _ _ ,_ ⟩

    For-iterated-equality n P (x ≡ y) ×
    (∀ p → For-iterated-equality n Q (∀ i → f i ≡ g (subst B p i)))  ↝⟨ uncurry $ For-iterated-equality-Σ n resp hyp-Σ ⟩

    For-iterated-equality n Q
      (∃ λ (p : x ≡ y) → ∀ i → f i ≡ g (subst B p i))                ↝⟨ For-iterated-equality-cong _ n resp $ _≃_.bijection $ Eq.W-≡,≡≃≡ ext ⟩□

    For-iterated-equality n Q (sup x f ≡ sup y g)                    □

For-iterated-equality-W :
  {A : Type a} {B : A → Type b} →
  Extensionality b (a ⊔ b) →
  ∀ n →
  (∀ {A B} → A ↔ B → Q A → Q B) →
  ({A : Type b} {B : A → Type (a ⊔ b)} →
   (∀ x → Q (B x)) → Q (∀ x → B x)) →
  ({A : Type a} {B : A → Type (a ⊔ b)} →
   P A → (∀ x → Q (B x)) → Q (Σ A B)) →
  (P A → Q (W A B)) →
  For-iterated-equality n P A →
  For-iterated-equality n Q (W A B)
For-iterated-equality-W _   zero    _    _     _     hyp-W = hyp-W
For-iterated-equality-W ext (suc n) resp hyp-Π hyp-Σ _     =
  For-iterated-equality-W-suc ext n resp hyp-Π hyp-Σ

-- Closure properties for _⊎_.

For-iterated-equality-⊎-suc :
  {A : Type a} {B : Type b} →
  ∀ n →
  (∀ {A B} → A ↔ B → P A → P B) →
  P ⊥ →
  For-iterated-equality (suc n) P (↑ b A) →
  For-iterated-equality (suc n) P (↑ a B) →
  For-iterated-equality (suc n) P (A ⊎ B)
For-iterated-equality-⊎-suc {P = P} n resp hyp-⊥ fie-A fie-B = λ where
  (inj₁ x) (inj₁ y) →                            $⟨ fie-A (lift x) (lift y) ⟩
    For-iterated-equality n P (lift x ≡ lift y)  ↝⟨ For-iterated-equality-cong _ n resp (Bijection.≡↔inj₁≡inj₁ F.∘ lift≡lift↔) ⟩□
    For-iterated-equality n P (inj₁ x ≡ inj₁ y)  □

  (inj₂ x) (inj₂ y) →                            $⟨ fie-B (lift x) (lift y) ⟩
    For-iterated-equality n P (lift x ≡ lift y)  ↝⟨ For-iterated-equality-cong _ n resp (Bijection.≡↔inj₂≡inj₂ F.∘ lift≡lift↔) ⟩□
    For-iterated-equality n P (inj₂ x ≡ inj₂ y)  □

  (inj₁ x) (inj₂ y) →                            $⟨ hyp-⊥ ⟩
    P ⊥                                          ↝⟨ (λ hyp → For-iterated-equality-⊥ _ n (λ _ → hyp) _) ⟩
    For-iterated-equality n P ⊥                  ↝⟨ For-iterated-equality-cong _ n resp (inverse Bijection.≡↔⊎) ⟩□
    For-iterated-equality n P (inj₁ x ≡ inj₂ y)  □

  (inj₂ x) (inj₁ y) →                            $⟨ hyp-⊥ ⟩
    P ⊥                                          ↝⟨ (λ hyp → For-iterated-equality-⊥ _ n (λ _ → hyp) _) ⟩
    For-iterated-equality n P ⊥                  ↝⟨ For-iterated-equality-cong _ n resp (inverse Bijection.≡↔⊎) ⟩□
    For-iterated-equality n P (inj₂ x ≡ inj₁ y)  □

For-iterated-equality-⊎ :
  {A : Type a} {B : Type b} →
  ∀ n →
  (∀ {A B} → A ↔ B → P A → P B) →
  P ⊥ →
  (P (↑ b A) → P (↑ a B) → P (A ⊎ B)) →
  For-iterated-equality n P (↑ b A) →
  For-iterated-equality n P (↑ a B) →
  For-iterated-equality n P (A ⊎ B)
For-iterated-equality-⊎ zero    _    _     hyp-⊎ = hyp-⊎
For-iterated-equality-⊎ (suc n) resp hyp-⊥ _     =
  For-iterated-equality-⊎-suc n resp hyp-⊥

-- Closure properties for List.

For-iterated-equality-List-suc :
  {A : Type a} →
  ∀ n →
  (∀ {A B} → A ↔ B → P A → P B) →
  P (↑ a ⊤) →
  P ⊥ →
  (∀ {A B} → P A → P B → P (A × B)) →
  For-iterated-equality (suc n) P A →
  For-iterated-equality (suc n) P (List A)
For-iterated-equality-List-suc {P = P} n resp hyp-⊤ hyp-⊥ hyp-× fie = λ where
  [] [] →                                $⟨ hyp-⊤ ⟩
    P (↑ _ ⊤)                            ↝⟨ For-iterated-equality-↑-⊤ _ n resp ⟩
    For-iterated-equality n P (↑ _ ⊤)    ↝⟨ For-iterated-equality-cong _ n resp (inverse []≡[]↔⊤ F.∘ Bijection.↑↔) ⟩□
    For-iterated-equality n P ([] ≡ [])  □

  (x ∷ xs) (y ∷ ys) →                            $⟨ For-iterated-equality-List-suc n resp hyp-⊤ hyp-⊥ hyp-× fie xs ys ⟩
    For-iterated-equality n P (xs ≡ ys)          ↝⟨ fie _ _ ,_ ⟩

    For-iterated-equality n P (x ≡ y) ×
    For-iterated-equality n P (xs ≡ ys)          ↝⟨ uncurry $ For-iterated-equality-× n resp hyp-× ⟩

    For-iterated-equality n P (x ≡ y × xs ≡ ys)  ↝⟨ For-iterated-equality-cong _ n resp (inverse ∷≡∷↔≡×≡) ⟩□

    For-iterated-equality n P (x ∷ xs ≡ y ∷ ys)  □

  [] (y ∷ ys) →                              $⟨ hyp-⊥ ⟩
    P ⊥                                      ↝⟨ (λ hyp → For-iterated-equality-⊥ _ n (λ _ → hyp) _) ⟩
    For-iterated-equality n P ⊥              ↝⟨ For-iterated-equality-cong _ n resp (inverse []≡∷↔⊥) ⟩□
    For-iterated-equality n P ([] ≡ y ∷ ys)  □

  (x ∷ xs) [] →                              $⟨ hyp-⊥ ⟩
    P ⊥                                      ↝⟨ (λ hyp → For-iterated-equality-⊥ _ n (λ _ → hyp) _) ⟩
    For-iterated-equality n P ⊥              ↝⟨ For-iterated-equality-cong _ n resp (inverse ∷≡[]↔⊥) ⟩□
    For-iterated-equality n P (x ∷ xs ≡ [])  □

For-iterated-equality-List :
  {A : Type a} →
  ∀ n →
  (∀ {A B} → A ↔ B → P A → P B) →
  P (↑ a ⊤) →
  P ⊥ →
  (∀ {A B} → P A → P B → P (A × B)) →
  (P A → P (List A)) →
  For-iterated-equality n P A →
  For-iterated-equality n P (List A)
For-iterated-equality-List zero _ _ _ _ hyp-List = hyp-List

For-iterated-equality-List (suc n) resp hyp-⊤ hyp-⊥ hyp-× _ =
  For-iterated-equality-List-suc n resp hyp-⊤ hyp-⊥ hyp-×

------------------------------------------------------------------------
-- Some "closure properties" for the predicate

-- For-iterated-equality commutes with certain type constructors
-- (assuming extensionality).

For-iterated-equality-commutes :
  Extensionality? k ℓ ℓ →
  (F : Type ℓ → Type ℓ) →
  ∀ n →
  ({A : Type ℓ} {P : A → Type ℓ} →
   F (∀ x → P x) ↝[ k ] ∀ x → F (P x)) →
  F (For-iterated-equality n P A) ↝[ k ]
  For-iterated-equality n (F ∘ P) A
For-iterated-equality-commutes _ _ zero _ = F.id

For-iterated-equality-commutes {P = P} {A = A} ext F (suc n) hyp =
  F ((x y : A) → For-iterated-equality n P (x ≡ y))            ↝⟨ hyp ⟩
  ((x : A) → F ((y : A) → For-iterated-equality n P (x ≡ y)))  ↝⟨ (∀-cong ext λ _ → hyp) ⟩
  ((x y : A) → F (For-iterated-equality n P (x ≡ y)))          ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → For-iterated-equality-commutes ext F n hyp) ⟩□
  ((x y : A) → For-iterated-equality n (F ∘ P) (x ≡ y))        □

-- A variant of the previous lemma.

For-iterated-equality-commutes-← :
  Extensionality? k ℓ ℓ →
  (F : Type ℓ → Type ℓ) →
  ∀ n →
  ({A : Type ℓ} {P : A → Type ℓ} →
   (∀ x → F (P x)) ↝[ k ] F (∀ x → P x)) →
  For-iterated-equality n (F ∘ P) A ↝[ k ]
  F (For-iterated-equality n P A)
For-iterated-equality-commutes-← _ _ zero _ = F.id

For-iterated-equality-commutes-← {P = P} {A = A} ext F (suc n) hyp =
  ((x y : A) → For-iterated-equality n (F ∘ P) (x ≡ y))        ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → For-iterated-equality-commutes-← ext F n hyp) ⟩
  ((x y : A) → F (For-iterated-equality n P (x ≡ y)))          ↝⟨ (∀-cong ext λ _ → hyp) ⟩
  ((x : A) → F ((y : A) → For-iterated-equality n P (x ≡ y)))  ↝⟨ hyp ⟩□
  F ((x y : A) → For-iterated-equality n P (x ≡ y))            □

-- For-iterated-equality commutes with certain binary type
-- constructors (assuming extensionality).

For-iterated-equality-commutes₂ :
  Extensionality? k ℓ ℓ →
  (F : Type ℓ → Type ℓ → Type ℓ) →
  ∀ n →
  ({A : Type ℓ} {P Q : A → Type ℓ} →
   F (∀ x → P x) (∀ x → Q x) ↝[ k ] ∀ x → F (P x) (Q x)) →
  F (For-iterated-equality n P A) (For-iterated-equality n Q A) ↝[ k ]
  For-iterated-equality n (λ A → F (P A) (Q A)) A
For-iterated-equality-commutes₂ _ _ zero _ = F.id

For-iterated-equality-commutes₂ {P = P} {A = A} {Q = Q}
                                ext F (suc n) hyp =
  F ((x y : A) → For-iterated-equality n P (x ≡ y))
    ((x y : A) → For-iterated-equality n Q (x ≡ y))                    ↝⟨ hyp ⟩

  ((x : A) → F ((y : A) → For-iterated-equality n P (x ≡ y))
               ((y : A) → For-iterated-equality n Q (x ≡ y)))          ↝⟨ (∀-cong ext λ _ → hyp) ⟩

  ((x y : A) → F (For-iterated-equality n P (x ≡ y))
                 (For-iterated-equality n Q (x ≡ y)))                  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                           For-iterated-equality-commutes₂ ext F n hyp) ⟩□
  ((x y : A) → For-iterated-equality n (λ A → F (P A) (Q A)) (x ≡ y))  □

-- A variant of the previous lemma.

For-iterated-equality-commutes₂-← :
  Extensionality? k ℓ ℓ →
  (F : Type ℓ → Type ℓ → Type ℓ) →
  ∀ n →
  ({A : Type ℓ} {P Q : A → Type ℓ} →
   (∀ x → F (P x) (Q x)) ↝[ k ] F (∀ x → P x) (∀ x → Q x)) →
  For-iterated-equality n (λ A → F (P A) (Q A)) A ↝[ k ]
  F (For-iterated-equality n P A) (For-iterated-equality n Q A)
For-iterated-equality-commutes₂-← _ _ zero _ = F.id

For-iterated-equality-commutes₂-← {P = P} {Q = Q} {A = A}
                                  ext F (suc n) hyp =
  ((x y : A) → For-iterated-equality n (λ A → F (P A) (Q A)) (x ≡ y))  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                           For-iterated-equality-commutes₂-← ext F n hyp) ⟩
  ((x y : A) → F (For-iterated-equality n P (x ≡ y))
                 (For-iterated-equality n Q (x ≡ y)))                  ↝⟨ (∀-cong ext λ _ → hyp) ⟩

  ((x : A) → F ((y : A) → For-iterated-equality n P (x ≡ y))
               ((y : A) → For-iterated-equality n Q (x ≡ y)))          ↝⟨ hyp ⟩□

  F ((x y : A) → For-iterated-equality n P (x ≡ y))
    ((x y : A) → For-iterated-equality n Q (x ≡ y))                    □

-- Some corollaries of For-iterated-equality-commutes₂.

For-iterated-equality-commutes-× :
  {A : Type a} →
  ∀ n →
  For-iterated-equality n P A × For-iterated-equality n Q A ↝[ a ∣ a ]
  For-iterated-equality n (λ A → P A × Q A) A
For-iterated-equality-commutes-× n ext =
  For-iterated-equality-commutes₂ ext _×_ n
    (from-isomorphism $ inverse ΠΣ-comm)

For-iterated-equality-commutes-⊎ :
  ∀ n →
  For-iterated-equality n P A ⊎ For-iterated-equality n Q A →
  For-iterated-equality n (λ A → P A ⊎ Q A) A
For-iterated-equality-commutes-⊎ n =
  For-iterated-equality-commutes₂ _ _⊎_ n [ inj₁ ∘_ , inj₂ ∘_ ]
