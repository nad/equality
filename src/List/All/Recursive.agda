------------------------------------------------------------------------
-- The All predicate, defined recursively
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module List.All.Recursive
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bag-equivalence eq hiding (module Dec)
open import Bijection eq as Bijection using (_↔_)
open import Equality.Decision-procedures eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import List eq as L using (_++_)
import List.All eq as A
open import Monad eq hiding (map)
import Nat eq as Nat
open import Surjection eq using (_↠_)
open import Tactic.By.Parametrised eq
open import Vec eq as Vec using (Vec)

private
  variable
    a ℓ p q : Level
    A B     : Type a
    f       : A → B
    P       : A → Type p
    Q       : A → Type q
    x y     : A
    xs ys   : List A
    n       : ℕ

-- All P xs means that P holds for every element of xs.

All : (A → Type p) → List A → Type p
All P []       = ↑ _ ⊤
All P (x ∷ xs) = P x × All P xs

-- The type xs ⊆ ys means that every element of xs is also an element
-- of ys.

infix 4 _⊆_

_⊆_ : {A : Type a} → List A → List A → Type a
xs ⊆ ys = All (_∈ ys) xs

-- If All P xs holds and x is an element of xs, then P x holds.

index : All P xs → x ∈ xs → P x
index {P = P} {xs = _ ∷ _} (p , _)  (inj₁ eq) = subst P (sym eq) p
index         {xs = _ ∷ _} (_ , ps) (inj₂ q)  = index ps q

-- If P holds for every element of xs, then All P xs holds.

tabulate : (∀ {x} → x ∈ xs → P x) → All P xs
tabulate {xs = []}    _ = _
tabulate {xs = _ ∷ _} f = f (inj₁ (refl _)) , tabulate (f ∘ inj₂)

-- Some synonyms.

cons : P x → All P xs → All P (x ∷ xs)
cons = _,_

head : All P (x ∷ xs) → P x
head = proj₁

tail : All P (x ∷ xs) → All P xs
tail = proj₂

-- All can be expressed using List and ∃.

∃-All↔List-∃ : (∃ λ xs → All P xs) ↔ List (∃ P)
∃-All↔List-∃ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : (∃ λ xs → All P xs) → List (∃ P)
  to ([]     , _)      = []
  to (x ∷ xs , p , ps) = (x , p) ∷ to (xs , ps)

  from : List (∃ P) → (∃ λ xs → All P xs)
  from []              = [] , _
  from ((x , p) ∷ xps) = Σ-map (x ∷_) (p ,_) (from xps)

  to∘from : ∀ xps → to (from xps) ≡ xps
  to∘from []         = refl _
  to∘from (xp ∷ xps) = cong (xp ∷_) (to∘from xps)

  from∘to : ∀ xsps → from (to xsps) ≡ xsps
  from∘to ([]     , _)      = refl _
  from∘to (x ∷ xs , p , ps) =
    cong (Σ-map (x ∷_) (p ,_)) (from∘to (xs , ps))

-- Some rearrangement lemmas.

All-[] : (P : A → Type p) → All P [] ↔ ⊤
All-[] P =
  All P []  ↔⟨⟩
  ↑ _ ⊤     ↝⟨ Bijection.↑↔ ⟩□
  ⊤         □

All-∷ : All P (x ∷ xs) ↔ P x × All P xs
All-∷ = F.id

All-++ : All P (xs ++ ys) ↔ All P xs × All P ys
All-++ {P = P} {xs = []} {ys = ys} =
  All P ys             ↝⟨ inverse $ drop-⊤-left-× (λ _ → All-[] P) ⟩□
  All P [] × All P ys  □
All-++ {P = P} {xs = x ∷ xs} {ys = ys} =
  P x × All P (xs ++ ys)       ↝⟨ F.id ×-cong All-++ ⟩
  P x × All P xs × All P ys    ↝⟨ ×-assoc ⟩□
  (P x × All P xs) × All P ys  □

All-map : All P (L.map f xs) ↔ All (P ∘ f) xs
All-map                 {xs = []}     = F.id
All-map {P = P} {f = f} {xs = x ∷ xs} =
  P (f x) × All P (L.map f xs)  ↝⟨ (∃-cong λ _ → All-map) ⟩□
  P (f x) × All (P ∘ f) xs      □

All-concat : All P (L.concat xs) ↔ All (All P) xs
All-concat         {xs = []}       = F.id
All-concat {P = P} {xs = xs ∷ xss} =
  All P (xs ++ L.concat xss)       ↝⟨ All-++ ⟩
  All P xs × All P (L.concat xss)  ↝⟨ (∃-cong λ _ → All-concat) ⟩□
  All P xs × All (All P) xss       □

All->>= :
  {A : Type ℓ} {f : A → List B} {xs : List A} →
  All P (xs >>= f) ↔ All (All P ∘ f) xs
All->>= {P = P} {f = f} {xs = xs} =
  All P (L.concat (L.map f xs))  ↝⟨ All-concat ⟩
  All (All P) (L.map f xs)       ↝⟨ All-map ⟩□
  All (All P ∘ f) xs             □

All-const : All (const A) xs ↔ Vec A (L.length xs)
All-const         {xs = []}     = F.id
All-const {A = A} {xs = x ∷ xs} =
  A × All (const A) xs     ↝⟨ (∃-cong λ _ → All-const) ⟩□
  A × Vec A (L.length xs)  □

All-const-replicate : All (const A) (L.replicate n tt) ↔ Vec A n
All-const-replicate         {n = zero}  = F.id
All-const-replicate {A = A} {n = suc n} =
  A × All (const A) (L.replicate n tt)  ↝⟨ (∃-cong λ _ → All-const-replicate) ⟩□
  A × Vec A n                           □

All-Σ :
  {A : Type a} {P : A → Type p} {Q : ∃ P → Type q} {xs : List A} →
  All (λ x → Σ (P x) (curry Q x)) xs ↔
  ∃ λ (ps : All P xs) → All Q (_↔_.to ∃-All↔List-∃ (xs , ps))
All-Σ {P = P} {Q = Q} {xs = []} =
  All (λ x → Σ (P x) (curry Q x)) []                             ↔⟨⟩
  ↑ _ ⊤                                                          ↝⟨ Bijection.↑↔ ⟩
  ⊤                                                              ↝⟨ inverse Bijection.↑↔ ⟩
  ↑ _ ⊤                                                          ↝⟨ inverse (drop-⊤-right λ _ → Bijection.↑↔) ⟩
  ↑ _ ⊤ × ↑ _ ⊤                                                  ↔⟨⟩
  (∃ λ (ps : All P []) → All Q (_↔_.to ∃-All↔List-∃ ([] , ps)))  □
All-Σ {P = P} {Q = Q} {xs = x ∷ xs} =
  All (λ x → Σ (P x) (curry Q x)) (x ∷ xs)                            ↔⟨⟩

  Σ (P x) (curry Q x) × All (λ x → Σ (P x) (curry Q x)) xs            ↝⟨ ∃-cong (λ _ → All-Σ) ⟩

  Σ (P x) (curry Q x) ×
  (∃ λ (ps : All P xs) → All Q (_↔_.to ∃-All↔List-∃ (_ , ps)))        ↝⟨ inverse Σ-assoc ⟩

  (∃ λ p → Q (x , p) ×
   ∃ λ (ps : All P xs) → All Q (_↔_.to ∃-All↔List-∃ (_ , ps)))        ↝⟨ ∃-cong (λ _ → ∃-comm) ⟩

  (∃ λ p → ∃ λ (ps : All P xs) →
   Q (x , p) × All Q (_↔_.to ∃-All↔List-∃ (_ , ps)))                  ↝⟨ Σ-assoc ⟩

  (∃ λ (p , ps) → Q (x , p) × All Q (_↔_.to ∃-All↔List-∃ (xs , ps)))  ↔⟨⟩

  (∃ λ (ps : All P (x ∷ xs)) →
     All Q (_↔_.to ∃-All↔List-∃ (x ∷ xs , ps)))                       □

Vec-Σ :
  {A : Type a} {P : A → Type p} →
  Vec (Σ A P) n ↔
  ∃ λ (xs : Vec A n) → All P (Vec.to-list xs)
Vec-Σ {n = zero} {A = A} {P = P} =
  Vec (Σ A P) zero                                  ↔⟨⟩
  ↑ _ ⊤                                             ↝⟨ Bijection.↑↔ ⟩
  ⊤                                                 ↝⟨ inverse Bijection.↑↔ ⟩
  ↑ _ ⊤                                             ↝⟨ inverse (drop-⊤-right λ _ → Bijection.↑↔) ⟩
  ↑ _ ⊤ × ↑ _ ⊤                                     ↔⟨⟩
  (∃ λ (xs : Vec A zero) → All P (Vec.to-list xs))  □
Vec-Σ {n = suc n} {A = A} {P = P} =
  Vec (Σ A P) (suc n)                                                ↔⟨⟩

  Σ A P × Vec (Σ A P) n                                              ↝⟨ ∃-cong (λ _ → Vec-Σ) ⟩

  (Σ A P × ∃ λ (xs : Vec A n) → All P (Vec.to-list xs))              ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (x : A) → P x × ∃ λ (xs : Vec A n) → All P (Vec.to-list xs))  ↝⟨ ∃-cong (λ _ → ∃-comm) ⟩

  (∃ λ (x : A) → ∃ λ (xs : Vec A n) → P x × All P (Vec.to-list xs))  ↝⟨ Σ-assoc ⟩

  (∃ λ ((x , xs) : A × Vec A n) → P x × All P (Vec.to-list xs))      ↔⟨⟩

  (∃ λ ((x , xs) : Vec A (suc n)) → P x × All P (Vec.to-list xs))    □

private

  -- The following alternative proof, which makes use of All-Σ, might
  -- compute less well if the J rule does not compute.

  Vec-Σ′ :
    {A : Type a} {P : A → Type p} →
    Vec (Σ A P) n ↔
    ∃ λ (xs : Vec A n) → All P (Vec.to-list xs)
  Vec-Σ′ {n = n} {A = A} {P = P} =
    Vec (Σ A P) n                                           ↝⟨ inverse All-const-replicate ⟩

    All (const (Σ A P)) (L.replicate n tt)                  ↝⟨ All-Σ ⟩

    (∃ λ (xs : All (const A) (L.replicate n tt)) →
       All (P ∘ proj₂) (_↔_.to ∃-All↔List-∃ (_ , xs)))      ↝⟨ (∃-cong λ _ → inverse All-map) ⟩

    (∃ λ (xs : All (const A) (L.replicate n tt)) →
       All P (L.map proj₂ (_↔_.to ∃-All↔List-∃ (_ , xs))))  ↝⟨ inverse (Σ-cong (inverse All-const-replicate) λ _ →
                                                               ≡⇒↝ _ (cong (All P) lemma)) ⟩□
    (∃ λ (xs : Vec A n) → All P (Vec.to-list xs))           □
    where
    lemma :
      ∀ {n} {xs : Vec A n} →
      Vec.to-list xs ≡
      L.map proj₂
        (_↔_.to ∃-All↔List-∃ (_ , _↔_.from All-const-replicate xs))
    lemma {n = zero}  = refl _
    lemma {n = suc n} = cong (_ ∷_) lemma

-- Concatenation.

append : All P xs → All P ys → All P (xs ++ ys)
append = curry (_↔_.from All-++)

private

  -- A lemma used below.

  subst-sym-refl : {p : P x} → subst P (sym (refl x)) p ≡ p
  subst-sym-refl {P = P} {x = x} {p = p} =
    subst P ⟨ sym (refl x) ⟩ p  ≡⟨ ⟨by⟩ sym-refl ⟩
    ⟨ subst P (refl x) p ⟩      ≡⟨ ⟨by⟩ subst-refl ⟩∎
    p                           ∎

-- The functions index and tabulate are inverses (roughly).

tabulate∘index :
  ∀ {xs} (ps : All P xs) →
  tabulate (index ps) ≡ ps
tabulate∘index         {xs = []}    _        = refl _
tabulate∘index {P = P} {xs = _ ∷ _} (p , ps) = cong₂ _,_
  (subst P (sym (refl _)) p  ≡⟨ subst-sym-refl ⟩∎
   p                         ∎)
  (tabulate (index ps)  ≡⟨ tabulate∘index ps ⟩∎
   ps                   ∎)

index∘tabulate :
  ∀ {xs} (f : ∀ {x} → x ∈ xs → P x) (×∈xs : x ∈ xs) →
  index (tabulate f) ×∈xs ≡ f ×∈xs
index∘tabulate         {xs = _ ∷ _} f (inj₂ p)  = index∘tabulate _ p
index∘tabulate {P = P} {xs = _ ∷ _} f (inj₁ eq) = elim₁
  (λ eq → subst P (sym eq) (f (inj₁ (refl _))) ≡ f (inj₁ eq))
  subst-sym-refl
  eq

-- The tabulate function preserves pointwise equality.

tabulate-cong :
  ∀ {xs} {f g : ∀ {x} → x ∈ xs → P x} →
  (∀ {x} (x∈xs : x ∈ xs) → f x∈xs ≡ g x∈xs) →
  tabulate f ≡ tabulate g
tabulate-cong {xs = []}    _   = refl _
tabulate-cong {xs = _ ∷ _} f≡g =
  cong₂ _,_ (f≡g _) (tabulate-cong (f≡g ∘ inj₂))

-- An extensionality principle for All.

extensionality :
  ∀ {xs} {ps qs : All P xs} →
  (∀ {x} (x∈xs : x ∈ xs) → index ps x∈xs ≡ index qs x∈xs) →
  ps ≡ qs
extensionality {ps = ps} {qs} ps≡qs =
  ps                   ≡⟨ sym $ tabulate∘index _ ⟩
  tabulate (index ps)  ≡⟨ tabulate-cong ps≡qs ⟩
  tabulate (index qs)  ≡⟨ tabulate∘index _ ⟩∎
  qs                   ∎

-- All and A.All are pointwise logically equivalent.

All⇔All : All P xs ⇔ A.All P xs
All⇔All = record { to = λ p _ → index p; from = λ f → tabulate (f _) }

-- There is a split surjection from A.All P xs to All P xs.

All↠All : A.All P xs ↠ All P xs
All↠All = record
  { logical-equivalence = inverse All⇔All
  ; right-inverse-of    = tabulate∘index
  }

-- All and A.All are pointwise equivalent (assuming extensionality).

All↔All :
  ∀ {k} {A : Type a} {P : A → Type p} {xs : List A} →
  Extensionality? k a (a ⊔ p) →
  All P xs ↝[ k ] A.All P xs
All↔All {a = a} =
  generalise-ext?
    All⇔All
    (λ ext →
         (λ _ →
            apply-ext ext λ _ →
            apply-ext (lower-extensionality a a ext) $
            index∘tabulate _)
       , tabulate∘index)

-- All preserves decidability of equality.

module Dec (dec : ∀ {x} → Decidable-equality (P x)) where

  infix 4 _≟_

  _≟_ : Decidable-equality (All P xs)
  _≟_ {xs = []}    = ↑.Dec._≟_ ⊤._≟_
  _≟_ {xs = _ ∷ _} = ×.Dec._≟_ dec _≟_

-- If xs and ys have type List A, where A is a set, then equality is
-- decidable for xs ⊆ ys.

module Dec-⊆ (A-set : Is-set A) where

  infix 4 _≟_

  _≟_ : {xs ys : List A} → Decidable-equality (xs ⊆ ys)
  _≟_ = Dec._≟_ (Dec-∈._≟_ A-set)

-- All preserves h-levels.

H-level-All :
  ∀ n →
  (∀ x → H-level n (P x)) →
  (∀ xs → H-level n (All P xs))
H-level-All n h []       = mono (Nat.zero≤ n) $
                           ↑-closure 0 ⊤-contractible
H-level-All n h (x ∷ xs) =
  ×-closure n (h _) (H-level-All n h xs)

-- The _⊆_ relation matches _∼[ implication ]_.

⊆↔∼[implication] :
  ∀ {k} {A : Type a} {xs ys : List A} →
  Extensionality? k a a →
  xs ⊆ ys ↝[ k ] xs ∼[ implication ] ys
⊆↔∼[implication] {xs = xs} {ys} ext =
  xs ⊆ ys                 ↝⟨ All↔All ext ⟩
  xs A.⊆ ys               ↔⟨ A.⊆↔∼[implication] ⟩
  xs ∼[ implication ] ys  □

-- A variant of _⊆_, based on A._⊆_.

infix 4 _⊆′_

_⊆′_ : {A : Type a} → List A → List A → Type a
xs ⊆′ ys = ∀ {z} → z ∈ xs → z ∈ ys

-- Some congruence lemmas.

All-cong₁ :
  ∀ {k} →
  (∀ x → P x ↝[ k ] Q x) →
  All P xs ↝[ k ] All Q xs
All-cong₁ {xs = []} P↝Q =
  ↑ _ ⊤  ↔⟨ Bijection.↑↔ ⟩
  ⊤      ↔⟨ inverse Bijection.↑↔ ⟩□
  ↑ _ ⊤  □
All-cong₁ {P = P} {Q = Q} {xs = x ∷ xs} P↝Q =
  P x × All P xs  ↝⟨ P↝Q _ ×-cong All-cong₁ P↝Q ⟩□
  Q x × All Q xs  □

map₁ : (∀ {x} → P x → Q x) → All P xs → All Q xs
map₁ f = All-cong₁ (λ _ → f)

map₂ : ys ⊆ xs → All P xs → All P ys
map₂ {ys = []}    _           ps = _
map₂ {ys = _ ∷ _} (y∈xs , qs) ps = index ps y∈xs , map₂ qs ps

map₂′ : ys ⊆′ xs → All P xs → All P ys
map₂′ = map₂ ∘ tabulate

map : (∀ {x} → P x → Q x) → ys ⊆ xs → All P xs → All Q ys
map P→Q ys∼xs = map₁ P→Q ∘ map₂ ys∼xs

All-cong-→ :
  (∀ x → P x → Q x) →
  ys ∼[ implication ] xs →
  All P xs → All Q ys
All-cong-→ {P = P} {Q = Q} {ys = ys} {xs = xs} P→Q ys∼xs =
  All P xs    ↝⟨ _↠_.from All↠All ⟩
  A.All P xs  ↝⟨ A.All-cong-→ P→Q ys∼xs ⟩
  A.All Q ys  ↝⟨ _↠_.to All↠All ⟩□
  All Q ys    □

All-cong :
  ∀ {k} {A : Type a} {P : A → Type p} {Q : A → Type q} {xs ys} →
  Extensionality? ⌊ k ⌋-sym a (a ⊔ p ⊔ q) →
  (∀ x → P x ↝[ ⌊ k ⌋-sym ] Q x) →
  xs ∼[ ⌊ k ⌋-sym ] ys →
  All P xs ↝[ ⌊ k ⌋-sym ] All Q ys
All-cong {a = a} {p = p} {q = q} {k} {P = P} {Q} {xs} {ys}
         ext P↝Q xs∼ys =
  All P xs    ↝⟨ All↔All (lower-extensionality? ⌊ k ⌋-sym a q ext) ⟩
  A.All P xs  ↝⟨ A.All-cong ext P↝Q xs∼ys ⟩
  A.All Q ys  ↝⟨ inverse-ext? All↔All (lower-extensionality? ⌊ k ⌋-sym a p ext) ⟩□
  All Q ys    □

-- A fusion lemma for index.

index∘index :
  ∀ {xs ys} {ps : All P ys} {x∈xs : x ∈ xs} (xs⊆ys : xs ⊆ ys) →
  index ps (index xs⊆ys x∈xs) ≡ index (map₂ xs⊆ys ps) x∈xs
index∘index {xs = _ ∷ _} {x∈xs = inj₂ _}  (_ , ⊆ys) =
  index∘index ⊆ys

index∘index {P = P} {xs = _ ∷ _} {ys} {ps} {inj₁ eq} (∈ys , _) = elim₁
  (λ eq → index ps (subst (_∈ ys) (sym eq) ∈ys) ≡
          subst P (sym eq) (index ps ∈ys))
  (index ps ⟨ subst (_∈ ys) (sym (refl _)) ∈ys ⟩  ≡⟨ ⟨by⟩ subst-sym-refl ⟩
   index ps ∈ys                                   ≡⟨ sym subst-sym-refl ⟩∎
   subst P (sym (refl _)) (index ps ∈ys)          ∎)
  eq

-- Some rearrangement lemmas for index.

index-map₁ :
  ∀ {P : A → Type p}
    xs {f : ∀ {x} → P x → Q x} {ps : All P xs} {q : x ∈ xs} →
  index (map₁ f ps) q ≡ f (index ps q)
index-map₁ (_ ∷ xs) {q = inj₂ q}  = index-map₁ xs

index-map₁ {Q = Q} {P = P} (_ ∷ _) {f} {p , _} {q = inj₁ eq} = elim₁
  (λ eq → subst Q (sym eq) (f p) ≡
          f (subst P (sym eq) p))
  (subst Q (sym (refl _)) (f p)  ≡⟨ subst-sym-refl ⟩
   f ⟨ p ⟩                       ≡⟨ ⟨by⟩ subst-sym-refl ⟩∎
   f (subst P (sym (refl _)) p)  ∎)
  eq

index-append-Any-++-inj₁ :
  ∀ {xs ys} {ps : All P xs} {qs : All P ys} (x∈xs : x ∈ xs) →
  index (append ps qs) (_↔_.from (Any-++ _ _ _) (inj₁ x∈xs)) ≡
  index ps x∈xs
index-append-Any-++-inj₁ {xs = _ ∷ _} (inj₁ _) = refl _
index-append-Any-++-inj₁ {xs = _ ∷ _} (inj₂ p) =
  index-append-Any-++-inj₁ p

index-append-Any-++-inj₂ :
  ∀ xs {ys} {ps : All P xs} {qs : All P ys} {y∈ys : y ∈ ys} →
  index (append ps qs) (_↔_.from (Any-++ _ xs _) (inj₂ y∈ys)) ≡
  index qs y∈ys
index-append-Any-++-inj₂ []       = refl _
index-append-Any-++-inj₂ (_ ∷ xs) = index-append-Any-++-inj₂ xs

index-All-const :
  ∀ (xs : List A) {bs : All (const B) xs} {i} →
  Vec.index (_↔_.to All-const bs) i ≡
  index bs (proj₂ (_↔_.from (Fin-length xs) i))
index-All-const (_ ∷ xs)    {i = fsuc i} = index-All-const xs
index-All-const (_ ∷ _) {b , _} {fzero}  =
  b                                 ≡⟨ sym subst-sym-refl ⟩∎
  subst (const _) (sym (refl _)) b  ∎

-- A rearrangement lemma for Vec-Σ.

proj₁-Vec-Σ :
  {A : Type a} {P : A → Type p} {xs : Vec (Σ A P) n} →
  proj₁ (_↔_.to Vec-Σ xs) ≡ Vec.map proj₁ xs
proj₁-Vec-Σ {n = zero}  = refl _
proj₁-Vec-Σ {n = suc n} = cong (_ ,_) proj₁-Vec-Σ

-- A fusion lemma for map₂.

map₂∘map₂′ :
  ∀ {xs ys zs} {xs⊆ys : xs ⊆ ys} {ys⊆zs : ys ⊆′ zs} {ps : All P zs} →
  map₂ xs⊆ys (map₂′ ys⊆zs ps) ≡ map₂ (map₁ ys⊆zs xs⊆ys) ps
map₂∘map₂′ {xs = []}                             = refl _
map₂∘map₂′ {xs = _ ∷ _} {xs⊆ys = q , _} {f} {ps} =
  cong₂ _,_ lemma map₂∘map₂′
  where
  lemma =
    index (map₂ (tabulate f) ps) q     ≡⟨ sym $ index∘index (tabulate f) ⟩
    index ps ⟨ index (tabulate f) q ⟩  ≡⟨ ⟨by⟩ (index∘tabulate f q) ⟩∎
    index ps (f q)                     ∎

-- Some rearrangement lemmas for map₂′.

map₂′-inj₂-∘ :
  ∀ {xs ys} {f : ys ⊆′ xs} {p : P x} {ps : All P xs} →
  map₂′ (inj₂ ∘ f) (p , ps) ≡ map₂′ f ps
map₂′-inj₂-∘ {ys = []}    = refl _
map₂′-inj₂-∘ {ys = _ ∷ _} = cong (_ ,_) map₂′-inj₂-∘

mutual

  map₂′-id :
    ∀ {xs} {ps : All P xs} →
    map₂′ id ps ≡ ps
  map₂′-id {xs = []}    = refl _
  map₂′-id {xs = _ ∷ _} = cong₂ _,_ subst-sym-refl map₂′-inj₂

  map₂′-inj₂ :
    ∀ {xs} {p : P x} {ps : All P xs} →
    map₂′ inj₂ (p , ps) ≡ ps
  map₂′-inj₂ {p = p} {ps} =
    map₂′ inj₂ (p , ps)  ≡⟨ map₂′-inj₂-∘ ⟩
    map₂′ id ps          ≡⟨ map₂′-id ⟩∎
    ps                   ∎

map₂′-⊎-map-id :
  ∀ {xs ys} {f : ys ⊆′ xs} {p : P x} {ps : All P xs} →
  map₂′ (⊎-map id f) (p , ps) ≡ (p , map₂′ f ps)
map₂′-⊎-map-id {f = f} {p} {ps} = cong₂ _,_ subst-sym-refl
  (map₂′ (inj₂ ∘ f) (p , ps)  ≡⟨ map₂′-inj₂-∘ ⟩∎
   map₂′ f ps                 ∎)

map₂′-⊎-map-id-inj₂ :
  ∀ {xs} {p : P x} {q : P y} {ps : All P xs} →
  map₂′ (⊎-map id inj₂) (p , q , ps) ≡ (p , ps)
map₂′-⊎-map-id-inj₂ {p = p} {q} {ps} =
  map₂′ (⊎-map id inj₂) (p , q , ps)  ≡⟨ map₂′-⊎-map-id ⟩
  (p , map₂′ inj₂ (q , ps))           ≡⟨ cong (_ ,_) map₂′-inj₂ ⟩
  (p , ps)                            ∎

map₂′-++-cong :
  ∀ xs₁ {xs₂ ys₁ ys₂} {ps : All P xs₂} {qs : All P ys₂}
  (f : xs₁ ⊆′ xs₂) {g : ys₁ ⊆′ ys₂} →
  map₂′ (++-cong (λ _ → f) (λ _ → g) _) (append ps qs) ≡
  append (map₂′ f ps) (map₂′ g qs)
map₂′-++-cong [] {ys₁ = []} _ = refl _

map₂′-++-cong [] {xs₂} {_ ∷ _} {ps = ps} {qs} f {g} = cong₂ _,_

  (index (append ps qs) (++-cong (λ _ → f) (λ _ → g) _ (inj₁ (refl _)))  ≡⟨⟩

   index (append ps qs)
     (_↔_.from (Any-++ _ xs₂ _) (inj₂ (g (inj₁ (refl _)))))              ≡⟨ index-append-Any-++-inj₂ xs₂ ⟩∎

   index qs (g (inj₁ (refl _)))                                          ∎)

  (map₂′ (++-cong (λ _ → f) (λ _ → g ∘ inj₂) _) (append ps qs)  ≡⟨ map₂′-++-cong _ f ⟩∎
   append (map₂′ f ps) (map₂′ (g ∘ inj₂) qs)                    ∎)

map₂′-++-cong (_ ∷ _) {ps = ps} {qs} f {g} = cong₂ _,_

  (index (append ps qs) (++-cong (λ _ → f) (λ _ → g) _ (inj₁ (refl _)))  ≡⟨⟩

   index (append ps qs)
         (_↔_.from (Any-++ _ _ _) (inj₁ (f (inj₁ (refl _)))))            ≡⟨ index-append-Any-++-inj₁ (f (inj₁ (refl _))) ⟩∎

   index ps (f (inj₁ (refl _)))                                          ∎)

  (map₂′ (++-cong (λ _ → f) (λ _ → g) _ ∘ inj₂) (append ps qs)  ≡⟨ cong (λ f → map₂ f _) (tabulate-cong (++-cong-inj₂ f g)) ⟩
   map₂′ (++-cong (λ _ → f ∘ inj₂) (λ _ → g) _) (append ps qs)  ≡⟨ map₂′-++-cong _ (f ∘ inj₂) ⟩
   append (map₂′ (f ∘ inj₂) ps) (map₂′ g qs)                    ≡⟨⟩
   append (proj₂ (map₂′ f ps)) (map₂′ g qs)                     ∎)

  where

  ++-cong-inj₂ :
    ∀ {xs₁ xs₂ ys₁ ys₂}
    (f : x ∷ xs₁ ⊆′ xs₂) (g : ys₁ ⊆′ ys₂) {z} (p : z ∈ xs₁ ++ ys₁) →
    ++-cong (λ _ → f) (λ _ → g) _ (inj₂ p) ≡
    ++-cong (λ _ → f ∘ inj₂) (λ _ → g) _ p
  ++-cong-inj₂ f g p =
    ++-cong (λ _ → f) (λ _ → g) _ (inj₂ p)                                  ≡⟨⟩

    _↔_.from (Any-++ _ _ _)
      ⟨ ⊎-map f g (_↔_.to ⊎-assoc (inj₂ (_↔_.to (Any-++ _ _ _) p))) ⟩       ≡⟨ ⟨by⟩ (lemma (_↔_.to (Any-++ _ _ _) p)) ⟩

    _↔_.from (Any-++ _ _ _) (⊎-map (f ∘ inj₂) g (_↔_.to (Any-++ _ _ _) p))  ≡⟨⟩

    ++-cong (λ _ → f ∘ inj₂) (λ _ → g) _ p                                  ∎
    where
    lemma : ∀ x → ⊎-map f g (_↔_.to ⊎-assoc (inj₂ x)) ≡
                  ⊎-map (f ∘ inj₂) g x
    lemma = [ (λ _ → refl _) , (λ _ → refl _) ]
