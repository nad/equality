------------------------------------------------------------------------
-- Bag equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Note that this module is not parametrised by a definition of
-- equality; it uses ordinary propositional equality.

module Bag-equality where

open import Equality.Propositional hiding (trans)
open import Equivalence hiding (id; _∘_)
open import Fin
open import Prelude

private
  module Bijection where
    import Bijection
    open Bijection equality-with-J public
  open Bijection hiding (id; _∘_)

  import Equality.Decision-procedures
  open Equality.Decision-procedures.Fin equality-with-J
    using (_≟_; 0≢+)

  module Weak where
    import Weak-equivalence
    open Weak-equivalence equality-with-J public
  open Weak hiding (id; _∘_)

------------------------------------------------------------------------
-- Any

-- Any.

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x xs} → P x      → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

-- Alternative definition of Any.

Any′ : {A : Set} (P : A → Set) → List A → Set
Any′ P []       = ⊥
Any′ P (x ∷ xs) = P x ⊎ Any′ P xs

-- The two definitions of Any are isomorphic.

Any-[] : ∀ {A : Set} {P : A → Set} → Any P [] ↔ ⊥
Any-[] {P = P} = record
  { surjection = record
    { equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = λ p → ⊥-elim p
    }
  ; left-inverse-of = from∘to
  }
  where
  to : Any P [] → ⊥
  to ()

  from = ⊥-elim

  from∘to : ∀ p → from (to p) ≡ p
  from∘to ()

Any-∷ : ∀ {A : Set} {P : A → Set} {x xs} →
        Any P (x ∷ xs) ↔ P x ⊎ Any P xs
Any-∷ {P = P} {x} {xs} = record
  { surjection = record
    { equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = [ (λ _ → refl) , (λ _ → refl) ]
    }
  ; left-inverse-of = from∘to
  }
  where
  to : Any P (x ∷ xs) → P x ⊎ Any P xs
  to (here  p) = inj₁ p
  to (there p) = inj₂ p

  from = [ here , there ]

  from∘to : ∀ p → from (to p) ≡ p
  from∘to (here  p) = refl
  from∘to (there p) = refl

Any↔Any′ : ∀ {A} {P : A → Set} {xs} → Any P xs ↔ Any′ P xs
Any↔Any′ {P = P} {[]}     = Any-[]
Any↔Any′ {P = P} {x ∷ xs} =
  Any P (x ∷ xs)   ↔⟨ Any-∷ ⟩
  P x ⊎ Any P xs   ↔⟨ Bijection.id ⊎-cong Any↔Any′ ⟩∎
  P x ⊎ Any′ P xs  ∎

------------------------------------------------------------------------
-- Bag equality

-- List membership.

infix 4 _∈_

_∈_ : {A : Set} → A → List A → Set
x ∈ xs = Any (λ y → x ≡ y) xs

-- Bag equality.

infix 4 _≈-bag_

_≈-bag_ : {A : Set} → List A → List A → Set
xs ≈-bag ys = ∀ z → z ∈ xs ↔ z ∈ ys

-- Alternative definition of bag equality.

infix 4 _≈-bag′_

_≈-bag′_ : {A : Set} → List A → List A → Set
xs ≈-bag′ ys =
  ∃ λ (f : Fin (length xs) ↔ Fin (length ys)) →
      xs And ys Are-related-by f

-- Yet another definition of bag equality. This definition is taken
-- from Coq's standard library.

infixr 5 _∷_
infix  4 _≈-bag″_

data _≈-bag″_ {A : Set} : List A → List A → Set where
  []    : [] ≈-bag″ []
  _∷_   : ∀ x {xs ys} (xs≈ys : xs ≈-bag″ ys) → x ∷ xs ≈-bag″ x ∷ ys
  swap  : ∀ {x y xs} → x ∷ y ∷ xs ≈-bag″ y ∷ x ∷ xs
  trans : ∀ {xs ys zs}
          (xs≈ys : xs ≈-bag″ ys) (ys≈zs : ys ≈-bag″ zs) → xs ≈-bag″ zs

------------------------------------------------------------------------
-- The first two definitions of bag equality above are equivalent

-- One direction follows from the following lemma, which states that
-- list membership can be expressed as "there is an index which points
-- to the element".

private
 module ∈-lookup {A : Set} {z : A} where

  to : ∀ {xs} → z ∈ xs → ∃ λ i → z ≡ lookup xs i
  to (here z≡x)   = (zero , z≡x)
  to (there z∈xs) = Σ-map suc id (to z∈xs)

  mutual

    from : ∀ xs → (∃ λ i → z ≡ lookup xs i) → z ∈ xs
    from xs (i , eq) = from′ xs i refl eq

    from′ : ∀ {n} xs (i : Fin n) (eq : length xs ≡ n) →
            z ≡ lookup′ xs i eq → z ∈ xs
    from′ []       ()      refl _
    from′ (x ∷ xs) zero    _    z≡x     = here z≡x
    from′ (x ∷ xs) (suc i) refl z≡xs[i] = there (from xs (i , z≡xs[i]))

  abstract

    from∘to : ∀ {xs} (z∈xs : z ∈ xs) → from xs (to z∈xs) ≡ z∈xs
    from∘to (here z≡x)   = refl
    from∘to (there z∈xs) = cong there (from∘to z∈xs)

    lemma : ∀ {n z} (xs : List A) (i : Fin n) (eq : length xs ≡ n) →
            z ≡ lookup′ xs i eq →
            z ≡ lookup′ xs (subst Fin (sym eq) i) refl
    lemma xs i refl eq = eq

    mutual

      to∘from : ∀ xs (p : ∃ λ i → z ≡ lookup xs i) → to (from xs p) ≡ p
      to∘from xs (i , eq) = to∘from′ xs i refl eq

      to∘from′ : ∀ {n} xs (i : Fin n) eq′ (eq : z ≡ lookup′ xs i eq′) →
                 to (from′ xs i eq′ eq) ≡
                 (subst Fin (sym eq′) i , lemma xs i eq′ eq)
      to∘from′ []       ()      refl _
      to∘from′ (x ∷ xs) zero    refl z≡x     = refl
      to∘from′ (x ∷ xs) (suc i) refl z≡xs[i] =
        cong (Σ-map suc id) (to∘from xs (i , z≡xs[i]))

∈-lookup : ∀ {A z} {xs : List A} → z ∈ xs ↔ ∃ λ i → z ≡ lookup xs i
∈-lookup {A} {z} {xs} = record
  { surjection = record
    { equivalence = record
      { to   = to
      ; from = from xs
      }
    ; right-inverse-of = to∘from xs
    }
  ; left-inverse-of = from∘to
  }
  where open ∈-lookup

-- The index.

index : ∀ {A z} {xs : List A} → z ∈ xs → Fin (length xs)
index = proj₁ ∘ _↔_.to ∈-lookup

abstract

  -- The index points to the element.

  index-lookup : ∀ {A z} {xs : List A} (z∈xs : z ∈ xs) →
                 lookup xs (index z∈xs) ≡ z
  index-lookup = sym ∘ proj₂ ∘ _↔_.to ∈-lookup

-- For the other direction a sequence of lemmas is used.

-- The first lemma states that ∃ λ z → z ∈ xs is isomorphic to Fin n,
-- where n is the length of xs. Thierry Coquand pointed out that this
-- is a generalisation of singleton-contractible.

Fin-length : ∀ {A} (xs : List A) → Fin (length xs) ↔ ∃ λ z → z ∈ xs
Fin-length {A} = λ xs → record
  { surjection = record
    { equivalence = record
      { to   = to xs
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to xs
  }
  where

  -- An enhanced lookup function.

  mutual

    to : (xs : List A) → Fin (length xs) → ∃ λ z → z ∈ xs
    to xs i = to′ xs i refl

    to′ : ∀ {n} (xs : List A) → Fin n → length xs ≡ n → ∃ λ z → z ∈ xs
    to′ []       ()      refl
    to′ (x ∷ xs) zero    _    = (x , here refl)
    to′ (x ∷ xs) (suc i) refl = Σ-map id there (to xs i)

  from : ∀ {xs : List A} → (∃ λ z → z ∈ xs) → Fin (length xs)
  from = index ∘ proj₂

  abstract

    mutual

      from∘to : ∀ xs i → from (to xs i) ≡ i
      from∘to xs i = from∘to′ xs i refl

      from∘to′ : ∀ {n} xs (i : Fin n) eq →
                 from (to′ xs i eq) ≡ subst Fin (sym eq) i
      from∘to′ []       ()      refl
      from∘to′ (x ∷ xs) zero    refl = refl
      from∘to′ (x ∷ xs) (suc i) refl = cong suc (from∘to xs i)

    to∘from : ∀ {xs} p → to xs (from p) ≡ p
    to∘from (z , here refl)  = refl
    to∘from (z , there z∈xs) =
      cong (Σ-map id there) (to∘from (z , z∈xs))

-- From this lemma we get that lists which are bag equal have related
-- lengths.

Fin-length-cong : ∀ {A} {xs ys : List A} →
                  xs ≈-bag ys → Fin (length xs) ↔ Fin (length ys)
Fin-length-cong {xs = xs} {ys} xs≈ys =
  Fin (length xs)   ↔⟨ Fin-length xs ⟩
  ∃ (λ z → z ∈ xs)  ↔≈⟨ Weak.Σ-preserves Weak.id (bijection⇒weak-equivalence ∘ xs≈ys) ⟩
  ∃ (λ z → z ∈ ys)  ↔⟨ Bijection.inverse (Fin-length ys) ⟩∎
  Fin (length ys)   ∎

abstract

  -- In fact, they have equal lengths.

  length-cong : ∀ {A} {xs ys : List A} →
                xs ≈-bag ys → length xs ≡ length ys
  length-cong = _⇔_.to Fin.isomorphic-same-size ∘ Fin-length-cong

  -- All that remains (except for some bookkeeping) is to show that
  -- the isomorphism which Fin-length-cong returns relates the two
  -- lists.

  Fin-length-cong-relates :
    ∀ {A} {xs ys : List A} (xs≈ys : xs ≈-bag ys) →
    xs And ys Are-related-by Fin-length-cong xs≈ys
  Fin-length-cong-relates {xs = xs} {ys} xs≈ys i =
    lookup xs i                               ≡⟨ cong (lookup xs) $ sym $ left-inverse-of (Fin-length xs) i ⟩
    lookup xs (from (Fin-length xs) $
               to (Fin-length xs) i)          ≡⟨ refl ⟩
    lookup xs (index $ proj₂ $
               to (Fin-length xs) i)          ≡⟨ index-lookup $ proj₂ $ to (Fin-length xs) i ⟩
    proj₁ (to (Fin-length xs) i)              ≡⟨ sym $ index-lookup $ to (xs≈ys _) (proj₂ (to (Fin-length xs) i)) ⟩
    lookup ys (index $ proj₂ $
               Σ-map id (to (xs≈ys _)) $
               to (Fin-length xs) i)          ≡⟨ refl ⟩∎
    lookup ys (to (Fin-length-cong xs≈ys) i)  ∎
    where open _↔_

-- We get that the two definitions of bag equality are equivalent.

≈⇔≈′ : ∀ {A : Set} {xs ys : List A} → xs ≈-bag ys ⇔ xs ≈-bag′ ys
≈⇔≈′ = record
  { to   = λ xs≈ys → ( Fin-length-cong xs≈ys
                     , Fin-length-cong-relates xs≈ys
                     )
  ; from = from
  }
  where
  equality-lemma : ∀ {A} {x y z : A} → y ≡ z → (x ≡ y) ≈ (x ≡ z)
  equality-lemma refl = Weak.id

  from : ∀ {xs ys} → xs ≈-bag′ ys → xs ≈-bag ys
  from {xs} {ys} (f , related) z =
    z ∈ xs                     ↔⟨ ∈-lookup ⟩
    ∃ (λ i → z ≡ lookup xs i)  ↔≈⟨ Weak.Σ-preserves (bijection⇒weak-equivalence f)
                                                    (λ i → equality-lemma (related i)) ⟩
    ∃ (λ i → z ≡ lookup ys i)  ↔⟨ Bijection.inverse ∈-lookup ⟩∎
    z ∈ ys                     ∎

------------------------------------------------------------------------
-- If x ∷ xs is bag equal to x ∷ ys, then xs and ys are bag equal

-- We have basically already showed this for the (first) alternative
-- definition of bag equality.

drop-cons′ : ∀ {A : Set} {x : A} xs ys →
             x ∷ xs ≈-bag′ x ∷ ys → xs ≈-bag′ ys
drop-cons′ {x = x} xs ys (f , related) =
  ( Fin.cancel-suc f
  , Fin.cancel-suc-preserves-relatedness x xs ys f related
  )

-- By the equivalence above we get the result also for the first
-- definition of bag equality, but we can show this directly, with the
-- help of some lemmas.

abstract

  -- The index function commutes with applications of certain
  -- inverses.

  index-commutes : ∀ {A : Set} {z : A} {xs ys} →
                   (xs≈ys : xs ≈-bag ys) (p : z ∈ xs) →
                   index (_↔_.to (xs≈ys z) p) ≡
                   _↔_.to (Fin-length-cong xs≈ys) (index p)
  index-commutes {z = z} {xs} {ys} xs≈ys p =
    (index $ to (xs≈ys z) p)                             ≡⟨ lemma ⟩
    (index $ to (xs≈ys _) $ proj₂ $
     to (Fin-length xs) $ from (Fin-length xs) (z , p))  ≡⟨ refl ⟩
    (index $ proj₂ $ Σ-map id (to (xs≈ys _)) $
     to (Fin-length xs) $ from (Fin-length xs) (z , p))  ≡⟨ refl ⟩
    (from (Fin-length ys) $ Σ-map id (to (xs≈ys _)) $
     to (Fin-length xs) $ index p)                       ≡⟨ refl ⟩∎
    (to (Fin-length-cong xs≈ys) $ index p)               ∎
    where
    open _↔_

    lemma : (index $ to (xs≈ys z) p) ≡
            (index $ to (xs≈ys _) $
             proj₂ $ to (Fin-length xs) $
             from (Fin-length xs) (z , p))
    lemma with to (Fin-length xs) (from (Fin-length xs) (z , p))
             | right-inverse-of (Fin-length xs) (z , p)
    ... | .(z , p) | refl = refl

  -- Bag equality isomorphisms preserve index equality. Note that this
  -- means that, even if the underlying equality is proof relevant, a
  -- bag equality isomorphism cannot map two distinct proofs of z ∈ xs
  -- (say) to different positions.

  index-equality-preserved :
    ∀ {A : Set} {z : A} {xs ys} {p q : z ∈ xs}
    (xs≈ys : xs ≈-bag ys) →
    index p ≡ index q →
    index (_↔_.to (xs≈ys z) p) ≡ index (_↔_.to (xs≈ys z) q)
  index-equality-preserved {z = z} {p = p} {q} xs≈ys eq =
    index (_↔_.to (xs≈ys z) p)                ≡⟨ index-commutes xs≈ys p ⟩
    _↔_.to (Fin-length-cong xs≈ys) (index p)  ≡⟨ cong (_↔_.to (Fin-length-cong xs≈ys)) eq ⟩
    _↔_.to (Fin-length-cong xs≈ys) (index q)  ≡⟨ sym $ index-commutes xs≈ys q ⟩∎
    index (_↔_.to (xs≈ys z) q)                ∎

-- If x ∷ xs is bag equal to x ∷ ys, then xs and ys are bag equal.

drop-cons : ∀ {A : Set} {x : A} {xs ys} →
            x ∷ xs ≈-bag x ∷ ys → xs ≈-bag ys
drop-cons {A = A} {x} {xs} {ys} x∷xs≈x∷ys z = record
  { surjection = record
    { equivalence = record
      { to   = f                       x∷xs≈x∷ys
      ; from = f $ Bijection.inverse ∘ x∷xs≈x∷ys
      }
    ; right-inverse-of = f∘f $ Bijection.inverse ∘ x∷xs≈x∷ys
    }
  ; left-inverse-of    = f∘f                       x∷xs≈x∷ys
  }
  where
  open _↔_

  abstract

    -- If the equality type is proof irrelevant (so that p and q are
    -- equal), then this lemma can be proved without the help of
    -- index-equality-preserved.

    lemma : ∀ {xs ys} (inv : x ∷ xs ≈-bag x ∷ ys) {p q z∈xs} →
            here p ≡ from (inv z) (here q) →
            there z∈xs ≡ from (inv z) (here p) →
            ⊥
    lemma {xs} inv {p} {q} {z∈xs} hyp₁ hyp₂ = 0≢+ (
      zero                           ≡⟨ refl ⟩
      index (here {xs = xs} p)       ≡⟨ cong index hyp₁ ⟩
      index (from (inv z) (here q))  ≡⟨ index-equality-preserved (Bijection.inverse ∘ inv) refl ⟩
      index (from (inv z) (here p))  ≡⟨ cong index (sym hyp₂) ⟩
      index (there {x = x} z∈xs)     ≡⟨ refl ⟩∎
      suc (index z∈xs)               ∎)

  f : ∀ {xs ys} → x ∷ xs ≈-bag x ∷ ys → z ∈ xs → z ∈ ys
  f inv z∈xs with to (inv z) (there z∈xs) | sym (left-inverse-of (inv z) (there z∈xs))
  f inv z∈xs | there z∈ys | left⁺ = z∈ys
  f inv z∈xs | here  z≡x  | left⁺ with to (inv z) (here z≡x) | sym (left-inverse-of (inv z) (here z≡x))
  f inv z∈xs | here  z≡x  | left⁺ | there z∈ys | left⁰ = z∈ys
  f inv z∈xs | here  z≡x  | left⁺ | here  z≡x′ | left⁰ = ⊥-elim $ lemma inv left⁰ left⁺

  abstract

    f∘f : ∀ {xs ys} (inv : x ∷ xs ≈-bag x ∷ ys) (p : z ∈ xs) →
          f (Bijection.inverse ∘ inv) (f inv p) ≡ p
    f∘f inv z∈xs with to (inv z) (there z∈xs) | sym (left-inverse-of (inv z) (there z∈xs))
    f∘f inv z∈xs | there z∈ys | left⁺ with from (inv z) (there z∈ys) | sym (right-inverse-of (inv z) (there z∈ys))
    f∘f inv z∈xs | there z∈ys | refl  | .(there z∈xs) | _ = refl
    f∘f inv z∈xs | here  z≡x  | left⁺ with to (inv z) (here z≡x) | sym (left-inverse-of (inv z) (here z≡x))
    f∘f inv z∈xs | here  z≡x  | left⁺ | there z∈ys | left⁰ with from (inv z) (there z∈ys) | sym (right-inverse-of (inv z) (there z∈ys))
    f∘f inv z∈xs | here  z≡x  | left⁺ | there z∈ys | refl  | .(here z≡x) | _ with from (inv z) (here z≡x)
                                                                                | sym (right-inverse-of (inv z) (here z≡x))
    f∘f inv z∈xs | here  z≡x  | refl  | there z∈ys | refl  | .(here z≡x) | _ | .(there z∈xs) | _ = refl
    f∘f inv z∈xs | here  z≡x  | left⁺ | here  z≡x′ | left⁰ = ⊥-elim $ lemma inv left⁰ left⁺

------------------------------------------------------------------------
-- The third definition of bag equality is sound with respect to the
-- other two

-- _∷_ preserves bag equality.

infixr 5 _∷-cong_

_∷-cong_ : ∀ {A : Set} {x y : A} {xs ys} →
           x ≡ y → xs ≈-bag ys → x ∷ xs ≈-bag y ∷ ys
_∷-cong_ {x = x} {xs = xs} {ys} refl xs≈ys z =
  z ∈ x ∷ xs        ↔⟨ Any-∷ ⟩
  (z ≡ x ⊎ z ∈ xs)  ↔⟨ Bijection.id ⊎-cong xs≈ys z ⟩
  (z ≡ x ⊎ z ∈ ys)  ↔⟨ Bijection.inverse Any-∷ ⟩∎
  z ∈ x ∷ ys        ∎

-- We can swap the first two elements of a list.

swap-first-two : ∀ {A : Set} {x y : A} {xs} →
                 x ∷ y ∷ xs ≈-bag y ∷ x ∷ xs
swap-first-two {x = x} {y} {xs} z =
  z ∈ x ∷ y ∷ xs                       ↔⟨ Any↔Any′ ⟩
  (z ≡ x ⊎ z ≡ y ⊎ Any′ (_≡_ z) xs)    ↔⟨ ⊎-assoc ⟩
  ((z ≡ x ⊎ z ≡ y) ⊎ Any′ (_≡_ z) xs)  ↔⟨ ⊎-comm ⊎-cong Bijection.id ⟩
  ((z ≡ y ⊎ z ≡ x) ⊎ Any′ (_≡_ z) xs)  ↔⟨ Bijection.inverse ⊎-assoc ⟩
  (z ≡ y ⊎ z ≡ x ⊎ Any′ (_≡_ z) xs)    ↔⟨ Bijection.inverse Any↔Any′ ⟩∎
  z ∈ y ∷ x ∷ xs                       ∎

-- The third definition of bag equality is sound with respect to the
-- first one.

≈″⇒≈ : ∀ {A : Set} {xs ys : List A} → xs ≈-bag″ ys → xs ≈-bag ys
≈″⇒≈ []                  = λ _ → Bijection.id
≈″⇒≈ (x ∷ xs≈ys)         = refl ∷-cong ≈″⇒≈ xs≈ys
≈″⇒≈ swap                = swap-first-two
≈″⇒≈ (trans xs≈ys ys≈zs) = λ z → _ ↔⟨ ≈″⇒≈ xs≈ys z ⟩ ≈″⇒≈ ys≈zs z

-- The other direction should also be provable, but I expect that this
-- requires some work.
