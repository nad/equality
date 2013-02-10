------------------------------------------------------------------------
-- The list container
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container.List where

open import Bag-equivalence
  using () renaming (_≈-bag_ to _≈-bagL_; _∈_ to _∈L_; Any to AnyL)
open import Container
open import Equality.Propositional
open import Fin
open import Logical-equivalence using (_⇔_; module _⇔_)
open import Prelude as P hiding (List; []; _∷_; foldr; _++_; id; _∘_)

open import Bijection equality-with-J using (_↔_; module _↔_; Σ-≡,≡↔≡)
open import Function-universe equality-with-J
open import H-level.Closure equality-with-J

------------------------------------------------------------------------
-- The type

-- Lists.

List : Container lzero
List = ℕ ▷ Fin

------------------------------------------------------------------------
-- The definitions of lists and bag equivalence for lists given in
-- Container/Container.List and in Prelude/Bag-equivalence are closely
-- related

-- The two definitions of lists are logically equivalent.

List⇔List : {A : Set} → ⟦ List ⟧ A ⇔ P.List A
List⇔List {A} = record
  { to   = to
  ; from = λ xs → (length xs , P.lookup xs)
  }
  where
  to : ⟦ List ⟧ A → P.List A
  to (zero  , f) = P.[]
  to (suc n , f) = P._∷_ (f (inj₁ tt)) (to (n , f ∘ inj₂))

-- If we assume that equality of functions is extensional, then we can
-- also prove that the two definitions are isomorphic.

List↔List : {A : Set} →
            ({B : Set} → Extensionality′ B (λ _ → A)) →
            ⟦ List ⟧ A ↔ P.List A
List↔List {A} ext = record
  { surjection = record
    { equivalence      = List⇔List
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  open _⇔_ List⇔List

  to∘from : ∀ xs → to (from xs) ≡ xs
  to∘from P.[]         = refl
  to∘from (P._∷_ x xs) = cong (P._∷_ x) (to∘from xs)

  from∘to : ∀ xs → from (to xs) ≡ xs
  from∘to (zero  , f) = cong (_,_ _) (ext λ ())
  from∘to (suc n , f) =
    (suc (length (to xs)) , P.lookup (P._∷_ x (to xs)))  ≡⟨ lemma₃ (from∘to (n , f ∘ inj₂)) ⟩
    (suc n                , [ (λ _ → x) , f ∘ inj₂ ])    ≡⟨ lemma₁ ⟩∎
    (suc n                , f)                           ∎
    where
    x  = f (inj₁ tt)
    xs = (n , f ∘ inj₂)

    lemma₁ : ∀ {n f} →
             _≡_ {A = ⟦ List ⟧ A}
                 (suc n , [ (λ _ → f (inj₁ tt)) , f ∘ inj₂ ])
                 (suc n , f)
    lemma₁ = cong (_,_ _) (ext [ (λ { tt → refl }) , (λ _ → refl) ])

    lemma₂ : {n : ℕ} {lkup : Fin n → A} →
             (≡n : length (to xs) ≡ n) →
             subst (λ n → Fin n → A) ≡n (P.lookup (to xs)) ≡ lkup →
             _≡_ {A = ⟦ List ⟧ A}
                 (suc (length (to xs)) , P.lookup (P._∷_ x (to xs)))
                 (suc n , [ (λ _ → x) , lkup ])
    lemma₂ refl refl = sym lemma₁

    lemma₃ : {ys : ⟦ List ⟧ A} →
             (length (to xs) , P.lookup (to xs)) ≡ ys →
             _≡_ {A = ⟦ List ⟧ A}
                 (suc (length (to xs)) , P.lookup (P._∷_ x (to xs)))
                 (suc (proj₁ ys) , [ (λ _ → x) , proj₂ ys ])
    lemma₃ ≡ys = lemma₂ (proj₁ ≡,≡) (proj₂ ≡,≡)
      where ≡,≡ = Σ-≡,≡←≡ ≡ys

-- The two definitions of Any are isomorphic (both via "to" and
-- "from").

Any↔Any-to : {A : Set} (xs : ⟦ List ⟧ A) (P : A → Set) →
             Any P xs ↔ AnyL P (_⇔_.to List⇔List xs)
Any↔Any-to (zero , lkup) P =
  (∃ λ (p : Fin zero) → P (lkup p))  ↔⟨ ∃-Fin-zero _ ⟩
  ⊥                                  □
Any↔Any-to (suc n , lkup) P =
  (∃ λ (p : Fin (suc n)) → P (lkup p))                              ↔⟨ ∃-Fin-suc _ ⟩
  P (lkup (inj₁ tt)) ⊎ Any {C = List} P (n , lkup ∘ inj₂)           ↔⟨ id ⊎-cong Any↔Any-to (n , lkup ∘ inj₂) P ⟩
  P (lkup (inj₁ tt)) ⊎ AnyL P (_⇔_.to List⇔List (n , lkup ∘ inj₂))  □

Any-from↔Any : {A : Set} (xs : P.List A) (P : A → Set) →
               Any P (_⇔_.from List⇔List xs) ↔ AnyL P xs
Any-from↔Any P.[] P =
  (∃ λ (p : Fin zero) → P (P.lookup P.[] p))  ↔⟨ ∃-Fin-zero _ ⟩
  ⊥                                           □
Any-from↔Any (P._∷_ x xs) P =
  (∃ λ (p : Fin (suc (P.length xs))) → P (P.lookup (P._∷_ x xs) p))  ↔⟨ ∃-Fin-suc _ ⟩
  P x ⊎ Any {C = List} P (_⇔_.from List⇔List xs)                     ↔⟨ id ⊎-cong Any-from↔Any xs P ⟩
  P x ⊎ AnyL P xs                                                    □

-- The definition of bag equivalence in Bag-equivalence and the one in
-- Container, instantiated with the List container, are logically
-- equivalent (both via "to" and "from").

≈-⇔-to-≈-to :
  {A : Set} {xs ys : ⟦ List ⟧ A} →
  xs ≈-bag ys ⇔ _⇔_.to List⇔List xs ≈-bagL _⇔_.to List⇔List ys
≈-⇔-to-≈-to {xs = xs} {ys} = record
  { to   = λ xs≈ys z →
             z ∈L (_⇔_.to List⇔List xs)  ↔⟨ inverse $ Any↔Any-to xs _ ⟩
             z ∈ xs                      ↔⟨ xs≈ys z ⟩
             z ∈ ys                      ↔⟨ Any↔Any-to ys _ ⟩
             z ∈L (_⇔_.to List⇔List ys)  □
  ; from = λ xs≈ys z →
             z ∈ xs                      ↔⟨ Any↔Any-to xs _ ⟩
             z ∈L (_⇔_.to List⇔List xs)  ↔⟨ xs≈ys z ⟩
             z ∈L (_⇔_.to List⇔List ys)  ↔⟨ inverse $ Any↔Any-to ys _ ⟩
             z ∈ ys                      □
  }

≈-⇔-from-≈-from :
  {A : Set} {xs ys : P.List A} →
  xs ≈-bagL ys ⇔ _⇔_.from List⇔List xs ≈-bag _⇔_.from List⇔List ys
≈-⇔-from-≈-from {xs = xs} {ys} = record
  { to   = λ xs≈ys z →
             z ∈ (_⇔_.from List⇔List xs)  ↔⟨ Any-from↔Any xs _ ⟩
             z ∈L xs                      ↔⟨ xs≈ys z ⟩
             z ∈L ys                      ↔⟨ inverse $ Any-from↔Any ys _ ⟩
             z ∈ (_⇔_.from List⇔List ys)  □
  ; from = λ xs≈ys z →
             z ∈L xs                      ↔⟨ inverse $ Any-from↔Any xs _ ⟩
             z ∈ (_⇔_.from List⇔List xs)  ↔⟨ xs≈ys z ⟩
             z ∈ (_⇔_.from List⇔List ys)  ↔⟨ Any-from↔Any ys _ ⟩
             z ∈L ys                      □
  }

------------------------------------------------------------------------
-- Constructors

[] : {A : Set} → ⟦ List ⟧ A
[] = (zero , λ ())

infixr 5 _∷_

_∷_ : {A : Set} → A → ⟦ List ⟧ A → ⟦ List ⟧ A
x ∷ (n , lkup) = (suc n , [ (λ _ → x) , lkup ])

-- Even if we don't assume extensionality we can prove that
-- intensionally distinct implementations of the constructors are bag
-- equivalent.

[]≈ : {A : Set} {lkup : _ → A} →
      _≈-bag_ {C₂ = List} [] (zero , lkup)
[]≈ _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (() , _) }
      ; from = λ { (() , _) }
      }
    ; right-inverse-of = λ { (() , _) }
    }
  ; left-inverse-of = λ { (() , _) }
  }

∷≈ : ∀ {A : Set} {n} {lkup : _ → A} →
     _≈-bag_ {C₂ = List}
             (lkup (inj₁ tt) ∷ (n , lkup ∘ inj₂))
             (suc n , lkup)
∷≈ _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (inj₁ tt , eq) → (inj₁ tt , eq)
                 ; (inj₂ s  , eq) → (inj₂ s  , eq)
                 }
      ; from = λ { (inj₁ tt , eq) → (inj₁ tt , eq)
                 ; (inj₂ s  , eq) → (inj₂ s  , eq)
                 }
      }
    ; right-inverse-of = λ { (inj₁ tt , eq) → refl
                           ; (inj₂ s  , eq) → refl
                           }
    }
  ; left-inverse-of = λ { (inj₁ tt , eq) → refl
                        ; (inj₂ s  , eq) → refl
                        }
  }

-- Any lemmas for the constructors.

Any-[] : {A : Set} (P : A → Set) →
         Any P [] ↔ ⊥₀
Any-[] _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (() , _) }
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ { (() , _) }
  }

Any-∷ : ∀ {A : Set} (P : A → Set) {x xs} →
        Any P (x ∷ xs) ↔ P x ⊎ Any P xs
Any-∷ _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (inj₁ tt , eq) → inj₁ eq
                 ; (inj₂ s  , eq) → inj₂ (s , eq)
                 }
      ; from = λ { (inj₁ eq)       → (inj₁ tt , eq)
                 ; (inj₂ (s , eq)) → (inj₂ s  , eq)
                 }
      }
    ; right-inverse-of = λ { (inj₁ eq)       → refl
                           ; (inj₂ (s , eq)) → refl
                           }
    }
  ; left-inverse-of = λ { (inj₁ tt , eq) → refl
                        ; (inj₂ s  , eq) → refl
                        }
  }

------------------------------------------------------------------------
-- More functions

-- A fold for lists. (Well, this is not a catamorphism, it is a
-- paramorphism.)

fold : {A B : Set} → B → (A → ⟦ List ⟧ A → B → B) → ⟦ List ⟧ A → B
fold nl cns (zero  , lkup) = nl
fold nl cns (suc n , lkup) =
  cns (lkup (inj₁ tt)) (n , lkup ∘ inj₂)
      (fold nl cns (n , lkup ∘ inj₂))

-- A lemma which can be used to prove properties about fold.
--
-- The "respects bag equivalence" argument could be omitted if
-- equality of functions were extensional.

fold-lemma : ∀ {A B : Set} {nl : B} {cns : A → ⟦ List ⟧ A → B → B}
             (P : ⟦ List ⟧ A → B → Set) →
             (∀ xs ys → xs ≈-bag ys → ∀ b → P xs b → P ys b) →
             P [] nl →
             (∀ x xs b → P xs b → P (x ∷ xs) (cns x xs b)) →
             ∀ xs → P xs (fold nl cns xs)
fold-lemma Q resp nl cns (zero  , lkup) = resp _ _ []≈ _ nl
fold-lemma Q resp nl cns (suc n , lkup) = resp _ _ ∷≈ _ $
  cns _ _ _ $ fold-lemma Q resp nl cns (n , lkup ∘ inj₂)

-- Why have I included both fold and fold-lemma rather than simply a
-- dependent eliminator? I tried this, and could easily define the
-- functions I wanted to define. However, the functions were defined
-- together with (partial) correctness proofs, and were unnecessarily
-- hard to read. I wanted to be able to define functions which were
-- easy to read, like the _++_ function below, and then have the
-- option to prove properties about them, like Any-++.
--
-- Unfortunately this turned out to be harder than expected. When
-- proving the Any-++ lemma it seemed as if I had to prove that _++_
-- preserves bag equivalence in its first argument in order to
-- instantiate the "respects bag equivalence" argument. However, my
-- preferred proof of this property uses Any-++…
--
-- An alternative could be to assume that equality of functions is
-- extensional, in which case the "respects bag equivalence" argument
-- could be removed. Another option would be to listen to Conor
-- McBride and avoid higher-order representations of first-order data.

-- Append.

infixr 5 _++_

_++_ : {A : Set} → ⟦ List ⟧ A → ⟦ List ⟧ A → ⟦ List ⟧ A
xs ++ ys = fold ys (λ z _ zs → z ∷ zs) xs

-- An Any lemma for append.

Any-++ : ∀ {A : Set} (P : A → Set) xs ys →
         Any P (xs ++ ys) ↔ Any P xs ⊎ Any P ys
Any-++ P xs ys = fold-lemma
  (λ xs xs++ys → Any P xs++ys ↔ Any P xs ⊎ Any P ys)

  (λ us vs us≈vs us++ys hyp →
    Any P us++ys         ↔⟨ hyp ⟩
    Any P us ⊎ Any P ys  ↔⟨ _⇔_.to (∼⇔∼″ us vs) us≈vs P ⊎-cong id ⟩
    Any P vs ⊎ Any P ys  □)

  (Any P ys             ↔⟨ inverse ⊎-left-identity ⟩
   ⊥ ⊎ Any P ys         ↔⟨ inverse (Any-[] P) ⊎-cong id ⟩
   Any P [] ⊎ Any P ys  □)

  (λ x xs xs++ys ih →
     Any P (x ∷ xs++ys)           ↔⟨ Any-∷ P ⟩
     P x ⊎ Any P xs++ys           ↔⟨ id ⊎-cong ih ⟩
     P x ⊎ Any P xs ⊎ Any P ys    ↔⟨ ⊎-assoc ⟩
     (P x ⊎ Any P xs) ⊎ Any P ys  ↔⟨ inverse (Any-∷ P) ⊎-cong id ⟩
     Any P (x ∷ xs) ⊎ Any P ys    □)

  xs
