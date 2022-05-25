------------------------------------------------------------------------
-- The All predicate, defined using _∈_
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module List.All {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bag-equivalence eq hiding (cons)
open import Bijection eq as Bijection using (_↔_)
import Equality.Groupoid eq as EG
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import Groupoid eq
open import H-level eq
open import H-level.Closure eq
open import List eq as L using (_++_)
open import Monad eq hiding (map)
open import Vec.Function eq as Vec using (Vec)

private
  variable
    a b ℓ p q : Level
    A B       : Type a
    P         : A → Type p
    Q         : A → Type q
    k x y     : A
    n         : ℕ
    xs ys     : List A

-- All P xs means that P holds for every element of xs.

All : {A : Type a} → (A → Type p) → List A → Type (a ⊔ p)
All P xs = ∀ x → x ∈ xs → P x

-- The type xs ⊆ ys means that every element of xs is also an element
-- of ys.

infix 4 _⊆_

_⊆_ : {A : Type a} → List A → List A → Type a
xs ⊆ ys = All (_∈ ys) xs

-- The _⊆_ relation matches _∼[ implication ]_.

⊆↔∼[implication] : xs ⊆ ys ↔ xs ∼[ implication ] ys
⊆↔∼[implication] {xs = xs} {ys = ys} =
  xs ⊆ ys                  ↔⟨⟩
  All (_∈ ys) xs           ↔⟨⟩
  (∀ x → x ∈ xs → x ∈ ys)  ↔⟨⟩
  xs ∼[ implication ] ys   □

-- Some rearrangement lemmas.

All-[] :
  ∀ {k} {A : Type a} (P : A → Type p) →
  Extensionality? k a (a ⊔ p) →
  All P [] ↝[ k ] ⊤
All-[] {a = a} {k = k} {A} P ext =
  All P []              ↔⟨⟩
  (∀ y → y ∈ [] → P y)  ↔⟨⟩
  (∀ y → ⊥ → P y)       ↝⟨ (∀-cong ext λ _ → Π⊥↔⊤ (lower-extensionality? k a a ext)) ⟩
  (A → ⊤)               ↔⟨ →-right-zero ⟩□
  ⊤                     □

module _ {k} {A : Type a} {P : A → Type p}
         (ext : Extensionality? k a (a ⊔ p)) where

  private
    ext′ : Extensionality? k a p
    ext′ = lower-extensionality? k a a ext

  All-∷ : All P (x ∷ xs) ↝[ k ] P x × All P xs
  All-∷ {x = x} {xs = xs} =
    All P (x ∷ xs)                              ↔⟨⟩
    (∀ y → y ∈ x ∷ xs → P y)                    ↔⟨⟩
    (∀ y → y ≡ x ⊎ y ∈ xs → P y)                ↝⟨ ∀-cong ext (λ _ → Π⊎↔Π×Π ext′) ⟩
    (∀ y → (y ≡ x → P y) × (y ∈ xs → P y))      ↔⟨ ΠΣ-comm ⟩
    (∀ y → y ≡ x → P y) × (∀ y → y ∈ xs → P y)  ↝⟨ (×-cong₁ λ _ → ∀-cong ext λ _ → →-cong₁ ext′ ≡-comm) ⟩
    (∀ y → x ≡ y → P y) × (∀ y → y ∈ xs → P y)  ↝⟨ inverse-ext? (λ ext → ∀-intro _ ext) ext ×-cong F.id ⟩□
    P x × All P xs                              □

  All-++ : All P (xs ++ ys) ↝[ k ] All P xs × All P ys
  All-++ {xs = xs} {ys = ys} =
    All P (xs ++ ys)                             ↔⟨⟩
    (∀ x → x ∈ xs ++ ys → P x)                   ↝⟨ (∀-cong ext λ _ → →-cong₁ ext′ (Any-++ _ _ _)) ⟩
    (∀ x → x ∈ xs ⊎ x ∈ ys → P x)                ↝⟨ (∀-cong ext λ _ → Π⊎↔Π×Π ext′) ⟩
    (∀ x → (x ∈ xs → P x) × (x ∈ ys → P x))      ↔⟨ ΠΣ-comm ⟩
    (∀ x → x ∈ xs → P x) × (∀ x → x ∈ ys → P x)  ↔⟨⟩
    All P xs × All P ys                          □

  All-concat : All P (L.concat xs) ↝[ k ] All (All P) xs
  All-concat {xs = xss} =
    (∀ x → x ∈ L.concat xss → P x)              ↝⟨ ∀-cong ext (λ _ → →-cong₁ ext′ (Any-concat _ _)) ⟩
    (∀ x → Any (x ∈_) xss → P x)                ↝⟨ ∀-cong ext (λ _ → →-cong₁ ext′ (Any-∈ _ _)) ⟩
    (∀ x → (∃ λ xs → x ∈ xs × xs ∈ xss) → P x)  ↝⟨ ∀-cong ext (λ _ → from-bijection currying) ⟩
    (∀ x → ∀ xs → x ∈ xs × xs ∈ xss → P x)      ↔⟨ Π-comm ⟩
    (∀ xs → ∀ x → x ∈ xs × xs ∈ xss → P x)      ↝⟨ ∀-cong ext (λ _ → ∀-cong ext λ _ → from-bijection currying) ⟩
    (∀ xs → ∀ x → x ∈ xs → xs ∈ xss → P x)      ↝⟨ ∀-cong ext (λ _ → ∀-cong ext λ _ → from-bijection Π-comm) ⟩
    (∀ xs → ∀ x → xs ∈ xss → x ∈ xs → P x)      ↝⟨ ∀-cong ext (λ _ → from-bijection Π-comm) ⟩□
    (∀ xs → xs ∈ xss → ∀ x → x ∈ xs → P x)      □

All-map :
  ∀ {k} {A : Type a} {B : Type b} {P : B → Type p}
    {f : A → B} {xs : List A} →
  (ext : Extensionality? k (a ⊔ b) (a ⊔ b ⊔ p)) →
  All P (L.map f xs) ↝[ k ] All (P ∘ f) xs
All-map {a = a} {b = b} {p = p} {k = k} {P = P} {f} {xs} ext =
  (∀ x → x ∈ L.map f xs → P x)              ↝⟨ (∀-cong ext₁ λ _ → →-cong₁ ext₂ (Any-map _ _ _)) ⟩
  (∀ x → Any (λ y → x ≡ f y) xs → P x)      ↝⟨ (∀-cong ext₃ λ _ → →-cong₁ ext₄ (Any-∈ _ _)) ⟩
  (∀ x → (∃ λ y → x ≡ f y × y ∈ xs) → P x)  ↝⟨ (∀-cong ext₃ λ _ → from-bijection currying) ⟩
  (∀ x → ∀ y → x ≡ f y × y ∈ xs → P x)      ↝⟨ (∀-cong ext₃ λ _ → ∀-cong ext₅ λ _ → from-bijection currying) ⟩
  (∀ x → ∀ y → x ≡ f y → y ∈ xs → P x)      ↔⟨ Π-comm ⟩
  (∀ x → ∀ y → y ≡ f x → x ∈ xs → P y)      ↝⟨ (∀-cong ext₅ λ _ → ∀-cong ext₃ λ _ → →-cong₁ ext₆ ≡-comm) ⟩
  (∀ x → ∀ y → f x ≡ y → x ∈ xs → P y)      ↝⟨ (∀-cong ext₅ λ _ → inverse-ext? (λ ext → ∀-intro _ ext) ext₃) ⟩□
  (∀ x → x ∈ xs → P (f x))                  □
  where
  ext₁ = lower-extensionality? k a     a       ext
  ext₂ = lower-extensionality? k a     (a ⊔ b) ext
  ext₃ = lower-extensionality? k a     lzero   ext
  ext₄ = lower-extensionality? k lzero (a ⊔ b) ext
  ext₅ = lower-extensionality? k b     lzero   ext
  ext₆ = lower-extensionality? k a     b       ext

All->>= :
  ∀ {k} {A B : Type ℓ} {P : B → Type p} {f : A → List B} {xs : List A} →
  (ext : Extensionality? k ℓ (ℓ ⊔ p)) →
  All P (xs >>= f) ↝[ k ] All (All P ∘ f) xs
All->>= {P = P} {f = f} {xs = xs} ext =
  All P (L.concat (L.map f xs))  ↝⟨ All-concat ext ⟩
  All (All P) (L.map f xs)       ↝⟨ All-map ext ⟩□
  All (All P ∘ f) xs             □

All-const :
  {A : Type a} {B : Type b} {xs : List B} →
  Extensionality? k b a →
  All (const A) xs ↝[ k ] Vec A (L.length xs)
All-const {A = A} {xs = xs} ext =
  (∀ x → x ∈ xs → A)       ↔⟨ inverse currying ⟩
  (∃ (_∈ xs) → A)          ↝⟨ →-cong₁ ext (Fin-length _) ⟩□
  (Fin (L.length xs) → A)  □

private

  -- The following lemma that relates All-const and Fin-length holds
  -- by definition.

  All-const-Fin-length :
    ∀ {xs : List A} {bs : All (const B) xs} {i} →
    All-const _ bs i ≡
    uncurry bs (_↔_.from (Fin-length xs) i)
  All-const-Fin-length = refl _

All-const-replicate :
  {A : Type a} →
  Extensionality? k lzero a →
  All (const A) (L.replicate n tt) ↝[ k ] Vec A n
All-const-replicate {n = n} {A = A} ext =
  All (const A) (L.replicate n tt)     ↝⟨ All-const ext ⟩
  Vec A (L.length (L.replicate n tt))  ↝⟨ →-cong₁ ext $ ≡⇒↝ bijection $ cong Fin (L.length-replicate _) ⟩□
  Vec A n                              □

All-Σ :
  {A : Type a} {P : A → Type p} {Q : ∀ x → P x → Type q} {xs : List A} →
  Extensionality? k a (a ⊔ p ⊔ q) →
  All (λ x → Σ (P x) (Q x)) xs ↝[ k ]
  ∃ λ (ps : All P xs) → ∀ x (x∈xs : x ∈ xs) → Q x (ps x x∈xs)
All-Σ {P = P} {Q = Q} {xs = xs} ext =
  All (λ x → Σ (P x) (Q x)) xs                                   ↔⟨⟩

  (∀ x → x ∈ xs → Σ (P x) (Q x))                                 ↝⟨ (∀-cong ext λ _ → from-isomorphism ΠΣ-comm) ⟩

  (∀ x → ∃ λ (ps : x ∈ xs → P x) →
     (x∈xs : x ∈ xs) → Q x (ps x∈xs))                            ↔⟨ ΠΣ-comm ⟩

  (∃ λ (ps : ∀ x → x ∈ xs → P x) →
     ∀ x (x∈xs : x ∈ xs) → Q x (ps x x∈xs))                      ↔⟨⟩

  (∃ λ (ps : All P xs) → ∀ x (x∈xs : x ∈ xs) → Q x (ps x x∈xs))  □

-- Some abbreviations.

nil : All P []
nil {P = P} = _⇔_.from (All-[] P _) _

cons : P x → All P xs → All P (x ∷ xs)
cons = curry (_⇔_.from (All-∷ _))

head : All P (x ∷ xs) → P x
head = proj₁ ∘ _⇔_.to (All-∷ _)

tail : All P (x ∷ xs) → All P xs
tail = proj₂ ∘ _⇔_.to (All-∷ _)

append : All P xs → All P ys → All P (xs ++ ys)
append = curry (_⇔_.from (All-++ _))

-- All preserves h-levels (assuming extensionality).

H-level-All :
  {A : Type a} {P : A → Type p} →
  Extensionality a (a ⊔ p) →
  ∀ n →
  (∀ x → H-level n (P x)) →
  (∀ xs → H-level n (All P xs))
H-level-All {a = a} ext n h xs =
  Π-closure ext n λ _ →
  Π-closure (lower-extensionality a a ext) n λ _ →
  h _

-- Some lemmas related to append.

append-Any-++-inj₁ :
  ∀ {xs ys} {ps : All P xs} {qs : All P ys}
  (x∈xs : x ∈ xs) →
  append ps qs _ (_↔_.from (Any-++ _ _ _) (inj₁ x∈xs)) ≡
  ps _ x∈xs
append-Any-++-inj₁ {P = P} {x = x} {ps = ps} {qs} x∈xs =
  append ps qs _ (_↔_.from (Any-++ _ _ _) (inj₁ x∈xs))       ≡⟨⟩

  [ ps _ , qs _ ] (_↔_.to (Any-++ _ _ _)
                     (_↔_.from (Any-++ _ _ _) (inj₁ x∈xs)))  ≡⟨ cong [ ps _ , qs _ ] (_↔_.right-inverse-of (Any-++ _ _ _) _) ⟩

  [_,_] {C = λ _ → P x} (ps _) (qs _) (inj₁ x∈xs)            ≡⟨⟩

  ps _ x∈xs                                                  ∎

append-Any-++-inj₂ :
  ∀ xs {ys} {ps : All P xs} {qs : All P ys} {y∈ys : y ∈ ys} →
  append ps qs _ (_↔_.from (Any-++ _ xs _) (inj₂ y∈ys)) ≡
  qs _ y∈ys
append-Any-++-inj₂ {P = P} {y = y} xs {ps = ps} {qs} {y∈ys} =
  append ps qs _ (_↔_.from (Any-++ _ xs _) (inj₂ y∈ys))       ≡⟨⟩

  [ ps _ , qs _ ] (_↔_.to (Any-++ _ _ _)
                     (_↔_.from (Any-++ _ xs _) (inj₂ y∈ys)))  ≡⟨ cong [ ps _ , qs _ ] (_↔_.right-inverse-of (Any-++ _ _ _) _) ⟩

  [_,_] {C = λ _ → P y} (ps _) (qs _) (inj₂ y∈ys)             ≡⟨⟩

  qs _ y∈ys                                                   ∎

-- Some congruence lemmas.

All-cong :
  ∀ {k} {A : Type a} {P : A → Type p} {Q : A → Type q} {xs ys} →
  Extensionality? ⌊ k ⌋-sym a (a ⊔ p ⊔ q) →
  (∀ x → P x ↝[ ⌊ k ⌋-sym ] Q x) →
  xs ∼[ ⌊ k ⌋-sym ] ys →
  All P xs ↝[ ⌊ k ⌋-sym ] All Q ys
All-cong {a = a} {k = k} {P = P} {Q} {xs} {ys} ext P↝Q xs∼ys =
  All P xs              ↔⟨⟩
  (∀ x → x ∈ xs → P x)  ↝⟨ ∀-cong ext (λ _ → →-cong (lower-extensionality? ⌊ k ⌋-sym a a ext) (xs∼ys _) (P↝Q _)) ⟩
  (∀ x → x ∈ ys → Q x)  ↔⟨⟩
  All Q ys              □

All-cong-→ :
  (∀ x → P x → Q x) →
  ys ∼[ implication ] xs →
  All P xs → All Q ys
All-cong-→ {P = P} {Q = Q} {ys = ys} {xs = xs} P→Q ys∼xs =
  All P xs              ↔⟨⟩
  (∀ x → x ∈ xs → P x)  ↝⟨ ∀-cong _ (λ _ → →-cong-→ (ys∼xs _) (P→Q _)) ⟩
  (∀ x → x ∈ ys → Q x)  ↔⟨⟩
  All Q ys              □

map : (∀ x → P x → Q x) → ys ⊆ xs → All P xs → All Q ys
map P→Q ys∼xs = All-cong-→ P→Q ys∼xs

map₁ : (∀ x → P x → Q x) → All P xs → All Q xs
map₁ P→Q = map P→Q (λ _ → id)

map₂ : ys ⊆ xs → All P xs → All P ys
map₂ ys⊆xs = map (λ _ → id) ys⊆xs

private

  map₁-∘ :
    ∀ {P : A → Type p} {xs} {f : ∀ x → P x → Q x} {ps : All P xs} →
    map₁ f ps ≡ λ _ → f _ ∘ ps _
  map₁-∘ = refl _

  map₂-∘ :
    ∀ {xs ys} {ys⊆xs : ys ⊆ xs} {ps : All P xs} →
    map₂ ys⊆xs ps ≡ λ _ → ps _ ∘ ys⊆xs _
  map₂-∘ = refl _

-- Some properties that hold by definition.

map₂∘map₂ :
  ∀ {xs ys zs} {xs⊆ys : xs ⊆ ys} {ys⊆zs : ys ⊆ zs} {ps : All P zs} →
  map₂ xs⊆ys (map₂ ys⊆zs ps) ≡ map₂ (map₁ ys⊆zs xs⊆ys) ps
map₂∘map₂ = refl _

map₂-inj₂-∘ :
  ∀ {xs ys} {f : ys ⊆ xs} {p : P x} {ps : All P xs} →
  map₂ (λ _ → inj₂ ∘ f _) (cons p ps) ≡ map₂ f ps
map₂-inj₂-∘ = refl _

map₂-id :
  ∀ {xs} {ps : All P xs} →
  map₂ (λ _ → id) ps ≡ ps
map₂-id = refl _

map₂-inj₂ :
  ∀ {xs} {p : P x} {ps : All P xs} →
  map₂ (λ _ → inj₂) (cons p ps) ≡ ps
map₂-inj₂ = refl _

-- Some rearrangement lemmas for map₂.

map₂-⊎-map-id :
  {A : Type a} {P : A → Type p} →
  Extensionality a (a ⊔ p) →
  ∀ {x xs ys} {f : ys ⊆ xs} {p : P x} {ps : All P xs} →
  map₂ (λ _ → ⊎-map id (f _)) (cons p ps) ≡ cons p (map₂ f ps)
map₂-⊎-map-id {a = a} ext {f = f} {p} {ps} =
  apply-ext ext λ _ →
  apply-ext (lower-extensionality lzero a ext)
    [ (λ _ → refl _) , (λ _ → refl _) ]

map₂-⊎-map-id-inj₂ :
  {A : Type a} {P : A → Type p} →
  Extensionality a (a ⊔ p) →
  ∀ {x y xs} {p : P x} {q : P y} {ps : All P xs} →
  map₂ (λ _ → ⊎-map id inj₂) (cons p (cons q ps)) ≡ cons p ps
map₂-⊎-map-id-inj₂ ext {p = p} {q} {ps} =
  map₂ (λ _ → ⊎-map id inj₂) (cons p (cons q ps))  ≡⟨ map₂-⊎-map-id ext ⟩
  cons p (map₂ (λ _ → inj₂) (cons q ps))           ≡⟨⟩
  cons p ps                                        ∎

map₂-++-cong :
  {A : Type a} {P : A → Type p} →
  Extensionality a (a ⊔ p) →
  ∀ xs₁ {ys₁ xs₂ ys₂} {ps : All P xs₂} {qs : All P ys₂}
  {f : xs₁ ⊆ xs₂} {g : ys₁ ⊆ ys₂} →
  map₂ (++-cong f g) (append ps qs) ≡
  append (map₂ f ps) (map₂ g qs)
map₂-++-cong {a = a} ext _ {ps = ps} {qs} {f} {g} =
  apply-ext ext λ _ →
  apply-ext (lower-extensionality lzero a ext) λ x∈ →

    let lemma : ∀ x → [ ps _ , qs _ ] (⊎-map (f _) (g _) x) ≡
                      [ ps _ ∘ f _ , qs _ ∘ g _ ] x
        lemma = [ (λ _ → refl _) , (λ _ → refl _) ]
    in

    [ ps _ , qs _ ] (_↔_.to (Any-++ _ _ _) (_↔_.from (Any-++ _ _ _)
                       (⊎-map (f _) (g _) (_↔_.to (Any-++ _ _ _) x∈))))  ≡⟨ cong [ ps _ , qs _ ] (_↔_.right-inverse-of (Any-++ _ _ _) _) ⟩

    [ ps _ , qs _ ] (⊎-map (f _) (g _) (_↔_.to (Any-++ _ _ _) x∈))       ≡⟨ lemma (_↔_.to (Any-++ _ _ _) x∈) ⟩∎

    [ ps _ ∘ f _ , qs _ ∘ g _ ] (_↔_.to (Any-++ _ _ _) x∈)               ∎
