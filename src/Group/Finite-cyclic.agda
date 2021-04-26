------------------------------------------------------------------------
-- Finite cyclic groups
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Group.Finite-cyclic
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude as P renaming (_+_ to _⊕_)

open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence-relation equality-with-J
  using (Is-equivalence-relation)
open import Function-universe equality-with-J hiding (_∘_)
open import Group eq as G using (Group; Cyclic; Abelian)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as T using (∥_∥; ∣_∣)
open import Integer eq hiding (suc) renaming (_*_ to _⊛_)
import Nat equality-with-J as Nat
open import Quotient eq as Q using (_/_)

private
  module ℤG = Group ℤ-group

private
  variable
    n     : ℕ
    i j k : ℤ

------------------------------------------------------------------------
-- The "equality modulo n" relation

-- Equality modulo n.

infix 4 _≡_mod_

_≡_mod_ : ℤ → ℤ → ℕ → Type
i ≡ j mod n = ∥ (∃ λ k → i ≡ j + k *+ n) ∥

-- The relation _≡_mod n is an equivalence relation.

≡-mod-is-equivalence-relation :
  ∀ n → Is-equivalence-relation (_≡_mod n)
≡-mod-is-equivalence-relation n = λ where
  .Is-equivalence-relation.reflexive {x = i} →
    ∣ + 0
    , (i             ≡⟨ sym +-right-identity ⟩
       i + + 0       ≡⟨ cong (_+_ i) $ sym $ ℤG.id^+ n ⟩∎
       i + + 0 *+ n  ∎)
    ∣
  .Is-equivalence-relation.symmetric {x = i} {y = j} →
    T.∥∥-map λ (k , i≡j+kn) →
        - k
      , (j                        ≡⟨ sym +-right-identity ⟩
         j + + 0                  ≡⟨ cong (_+_ j) $ sym $ +-right-inverse (k *+ n) ⟩
         j + (k *+ n - k *+ n)    ≡⟨ cong (_+_ j) $ cong (_+_ (k *+ n)) $ ℤG.^+⁻¹ n ⟩
         j + (k *+ n + - k *+ n)  ≡⟨ +-assoc j ⟩
         j + k *+ n + - k *+ n    ≡⟨ cong (_+ - k *+ n) $ sym i≡j+kn ⟩∎
         i + - k *+ n             ∎)

  .Is-equivalence-relation.transitive {x = i} {y = j} {z = k} →
    T.rec (Π-closure ext 1 λ _ →
           T.truncation-is-proposition) λ (l₁ , i≡j+l₁n) →
    T.∥∥-map λ (l₂ , j≡k+l₂n) →
        l₂ + l₁
      , (i                        ≡⟨ i≡j+l₁n ⟩
         j + l₁ *+ n              ≡⟨ cong (_+ l₁ *+ n) j≡k+l₂n ⟩
         k + l₂ *+ n + l₁ *+ n    ≡⟨ sym $ +-assoc k ⟩
         k + (l₂ *+ n + l₁ *+ n)  ≡⟨ cong (_+_ k) $ sym $ *+-distrib-+ n ⟩∎
         k + (l₂ + l₁) *+ n       ∎)

-- If i and j are equal modulo n, then i + k and j + k are also equal
-- modulo n.

+-cong : ∀ n j → i ≡ j mod n → i + k ≡ j + k mod n
+-cong {i = i} {k = k} n j = T.∥∥-map λ (l , i≡j+ln) →
    l
  , (i + k             ≡⟨ cong (_+ k) i≡j+ln ⟩
     j + l *+ n + k    ≡⟨ sym $ +-assoc j ⟩
     j + (l *+ n + k)  ≡⟨ cong (_+_ j) $ +-comm (l *+ n) ⟩
     j + (k + l *+ n)  ≡⟨ +-assoc j ⟩∎
     j + k + l *+ n    ∎)

-- If i and j are equal modulo n, then - i and - j are also equal
-- modulo n.

negate-cong : ∀ n j → i ≡ j mod n → - i ≡ - j mod n
negate-cong {i = i} n j = T.∥∥-map λ (k , i≡j+kn) →
    - k
  , (- i               ≡⟨ cong -_ i≡j+kn ⟩
     - (j + k *+ n)    ≡⟨ ℤG.∘⁻¹ {p = j} ⟩
     - (k *+ n) + - j  ≡⟨ +-comm (- (k *+ n)) ⟩
     - j + - (k *+ n)  ≡⟨ cong (_+_ (- j)) $ ℤG.^+⁻¹ n ⟩∎
     - j + - k *+ n    ∎)

-- If i and j are equal modulo n, then i *+ m and j *+ m are equal
-- modulo m * n.

*+-cong : ∀ m → i ≡ j mod n → i *+ m ≡ j *+ m mod m * n
*+-cong {i = i} {j = j} {n = n} m = T.∥∥-map λ (k , i≡j+kn) →
    k
  , (i *+ m                 ≡⟨ cong (_*+ m) i≡j+kn ⟩
     (j + k *+ n) *+ m      ≡⟨ ℤG.∘^+≡^+∘^+ (+-comm j) m ⟩
     j *+ m + k *+ n *+ m   ≡⟨ cong (_+_ (j *+ m)) $ ℤG.^+^+≡^+* n ⟩
     j *+ m + k *+ (n * m)  ≡⟨ cong (_+_ (j *+ m)) $ cong (k *+_) $ Nat.*-comm n ⟩∎
     j *+ m + k *+ (m * n)  ∎)

-- If i and j are equal modulo 2 * n, then ⌊ i /2⌋ and ⌊ j /2⌋ are
-- equal modulo n.

⌊/2⌋-cong : ∀ j n → i ≡ j mod 2 * n → ⌊ i /2⌋ ≡ ⌊ j /2⌋ mod n
⌊/2⌋-cong {i = i} j n = T.∥∥-map λ (k , i≡j+k2n) →
    k
  , (⌊ i /2⌋                  ≡⟨ cong ⌊_/2⌋ i≡j+k2n ⟩
     ⌊ j + k *+ (2 * n) /2⌋   ≡⟨ cong (⌊_/2⌋ ∘ (_+_ j) ∘ (k *+_)) $ sym $ Nat.*-comm n ⟩
     ⌊ j + k *+ (n * 2) /2⌋   ≡⟨ cong (⌊_/2⌋ ∘ (_+_ j)) $ sym $ ℤG.^+^+≡^+* n ⟩
     ⌊ j + (k *+ n) *+ 2 /2⌋  ≡⟨ ⌊+*+2/2⌋≡ j ⟩∎
     ⌊ j /2⌋ + k *+ n         ∎)

-- It is not the case that 0 is equal to 1 modulo n, if n is at least
-- 2.

0≢1mod2+ : ∀ n → ¬ + 0 ≡ + 1 mod 2 ⊕ n
0≢1mod2+ n = T.rec ⊥-propositional $ uncurry lemma
  where
  lemma : ∀ k → + 0 ≢ + 1 + k *+ (2 ⊕ n)
  lemma (+ 0) =
    + 0 ≡ + 1 + + 0 *+ (2 ⊕ n)  ↝⟨ flip trans (cong (_+_ (+ 1)) $ ℤG.id^+ (2 ⊕ n)) ⟩
    + 0 ≡ + 1 + + 0             ↔⟨⟩
    + 0 ≡ + 1                   ↝⟨ +[1+]≢- ∘ sym ⟩□
    ⊥                           □
  lemma (+ suc k) =
    + 0 ≡ + 1 + + suc k *+ (2 ⊕ n)         ↝⟨ flip ¬+0 ∘ sym ⟩
    ¬ Positive (+ 1 + + suc k *+ (2 ⊕ n))  ↝⟨ _∘ >0→>0→+>0 (+ 1) (+ suc k *+ (2 ⊕ n)) _ ⟩
    ¬ Positive (+ suc k *+ (2 ⊕ n))        ↝⟨ _$ >0→*+suc> (+ suc k) (suc n) _ ⟩□
    ⊥                                      □
  lemma -[1+ zero ] =
    + 0 ≡ + 1 + -[1+ 0 ] *+ (2 ⊕ n)             ↝⟨ flip trans (+-assoc (+ 1) {j = -[1+ 0 ]} {k = -[1+ 0 ] *+ (1 ⊕ n)}) ⟩
    + 0 ≡ + 1 + -[1+ 0 ] + -[1+ 0 ] *+ (1 ⊕ n)  ↝⟨ flip trans +-left-identity ⟩
    + 0 ≡ -[1+ 0 ] *+ (1 ⊕ n)                   ↝⟨ flip ¬-0 ∘ sym ⟩
    ¬ Negative (-[1+ 0 ] *+ (1 ⊕ n))            ↝⟨ _$ <0→*+suc<0 -[1+ 0 ] n _ ⟩□
    ⊥                                           □
  lemma -[1+ suc k ] =
    + 0 ≡ + 1 + -[1+ suc k ] *+ (2 ⊕ n)                 ↝⟨ flip trans (+-assoc (+ 1) {j = -[1+ suc k ]} {k = -[1+ suc k ] *+ (1 ⊕ n)}) ⟩
    + 0 ≡ + 1 + -[1+ suc k ] + -[1+ suc k ] *+ (1 ⊕ n)  ↔⟨⟩
    + 0 ≡ -[1+ k ] + -[1+ suc k ] *+ (1 ⊕ n)            ↝⟨ flip ¬-0 ∘ sym ⟩
    ¬ Negative (-[1+ k ] + -[1+ suc k ] *+ (1 ⊕ n))     ↝⟨ _∘ <0→<0→+<0 -[1+ k ] (-[1+ suc k ] *+ (1 ⊕ n)) _ ⟩
    ¬ Negative (-[1+ suc k ] *+ (1 ⊕ n))                ↝⟨ _$ <0→*+suc<0 -[1+ suc k ] n _ ⟩□
    ⊥                                                   □

-- It is not the case that ⌊_/2⌋ distributes over _+_ modulo 2 ⊕ n
-- (for any n).

¬⌊+/2⌋≡⌊/2⌋+⌊/2⌋mod2+ :
  ¬ (∀ i j → ⌊ i + j /2⌋ ≡ ⌊ i /2⌋ + ⌊ j /2⌋ mod 2 ⊕ n)
¬⌊+/2⌋≡⌊/2⌋+⌊/2⌋mod2+ {n = n} =
  (∀ i j → ⌊ i + j /2⌋ ≡ ⌊ i /2⌋ + ⌊ j /2⌋ mod 2 ⊕ n)  ↝⟨ (_$ (+ 1)) ∘ (_$ (+ 1)) ⟩
  + 1 ≡ + 0 mod 2 ⊕ n                                  ↝⟨ ≡-mod-is-equivalence-relation (2 ⊕ n)
                                                            .Is-equivalence-relation.symmetric ⟩
  + 0 ≡ + 1 mod 2 ⊕ n                                  ↝⟨ 0≢1mod2+ n ⟩□
  ⊥                                                    □

------------------------------------------------------------------------
-- Finite cyclic groups

-- ℤ/[1+ n ]ℤ is the group of integers with addition modulo 1 + n (the
-- finite cyclic group of order 1 + n).

ℤ/[1+_]ℤ : ℕ → Group lzero
ℤ/[1+ n ]ℤ = λ where
    .Group.Carrier        → ℤ / (_≡_mod suc n)
    .Group.Carrier-is-set → Q./-is-set
    .Group._∘_            → _+′_
    .Group.id             → Q.[ + 0 ]
    .Group._⁻¹            → -′_
    .Group.left-identity  → left-identity
    .Group.right-identity → right-identity
    .Group.assoc          → assoc
    .Group.left-inverse   → left-inverse
    .Group.right-inverse  → right-inverse
  where
  _+′_ : ℤ / (_≡_mod suc n) → ℤ / (_≡_mod suc n) → ℤ / (_≡_mod suc n)
  _+′_ = Q.rec λ where
    .Q.[]ʳ i → _+_ i Q./-map λ j₁ j₂ →
      j₁ ≡ j₂ mod suc n            ↝⟨ +-cong (suc n) j₂ ⟩
      j₁ + i ≡ j₂ + i mod suc n    ↝⟨ ≡⇒↝ _ $ cong₂ (_≡_mod suc n) (+-comm j₁) (+-comm j₂) ⟩□
      i + j₁ ≡ i + j₂ mod suc n    □
    .Q.is-setʳ →
      Π-closure ext 2 λ _ →
      Q./-is-set
    .Q.[]-respects-relationʳ {x = i₁} {y = i₂} i₁≡i₂ →
      ⟨ext⟩ $ Q.elim-prop λ where
        .Q.is-propositionʳ _ → Q./-is-set
        .Q.[]ʳ j             →         $⟨ i₁≡i₂ ⟩
          i₁ ≡ i₂ mod suc n            ↝⟨ +-cong (suc n) i₂ ⟩
          i₁ + j ≡ i₂ + j mod suc n    ↝⟨ Q.[]-respects-relation ⟩□
          Q.[ i₁ + j ] ≡ Q.[ i₂ + j ]  □

  -′_ : ℤ / (_≡_mod suc n) → ℤ / (_≡_mod suc n)
  -′_ = -_ Q./-map λ i₁ i₂ →
    i₁ ≡ i₂ mod suc n      ↝⟨ negate-cong (suc n) i₂ ⟩□
    - i₁ ≡ - i₂ mod suc n  □

  left-identity : ∀ i → Q.[ + 0 ] +′ i ≡ i
  left-identity = Q.elim-prop λ where
    .Q.is-propositionʳ _ → Q./-is-set
    .Q.[]ʳ _             → cong Q.[_] +-left-identity

  right-identity : ∀ i → i +′ Q.[ + 0 ] ≡ i
  right-identity = Q.elim-prop λ where
    .Q.is-propositionʳ _ → Q./-is-set
    .Q.[]ʳ _             → cong Q.[_] +-right-identity

  assoc : ∀ i j k → (i +′ (j +′ k)) ≡ ((i +′ j) +′ k)
  assoc = Q.elim-prop λ where
    .Q.is-propositionʳ _ → Π-closure ext 1 λ _ →
                           Π-closure ext 1 λ _ →
                           Q./-is-set
    .Q.[]ʳ i             → Q.elim-prop λ where
      .Q.is-propositionʳ _ → Π-closure ext 1 λ _ →
                             Q./-is-set
      .Q.[]ʳ _             → Q.elim-prop λ where
        .Q.is-propositionʳ _ → Q./-is-set
        .Q.[]ʳ _             → cong Q.[_] $ +-assoc i

  left-inverse : ∀ i → ((-′ i) +′ i) ≡ Q.[ + 0 ]
  left-inverse = Q.elim-prop λ where
    .Q.is-propositionʳ _ → Q./-is-set
    .Q.[]ʳ i             → cong Q.[_] $ +-left-inverse i

  right-inverse : ∀ i → (i +′ (-′ i)) ≡ Q.[ + 0 ]
  right-inverse = Q.elim-prop λ where
    .Q.is-propositionʳ _ → Q./-is-set
    .Q.[]ʳ i             → cong Q.[_] $ +-right-inverse i

-- ℤ/[1+ n ]ℤ is cyclic.

cyclic : Cyclic ℤ/[1+ n ]ℤ
cyclic {n = n} =
  ∣ Q.[ + 1 ]
  , (Q.elim-prop λ where
       .Q.is-propositionʳ _ → T.truncation-is-proposition
       .Q.[]ʳ i             →
         ∣ i
         , (Q.[ i ]           ≡⟨ cong Q.[_] $ sym $ *-left-identity i ⟩
            Q.[ + 1 ⊛ i ]     ≡⟨ lemma i ⟩∎
            Q.[ + 1 ] ℤ/.^ i  ∎)
         ∣)
  ∣
  where
  module ℤ/ = Group ℤ/[1+ n ]ℤ

  *+-lemma : ∀ n → Q.[ + 1 *+ n ] ≡ Q.[ + 1 ] ℤ/.^+ n
  *+-lemma zero    = refl _
  *+-lemma (suc n) =
    Q.[ + 1 *+ suc n ]                ≡⟨⟩
    Q.[ + 1 ] ℤ/.∘ Q.[ + 1 *+ n ]     ≡⟨ cong (Q.[ + 1 ] ℤ/.∘_) $ *+-lemma n ⟩∎
    Q.[ + 1 ] ℤ/.∘ Q.[ + 1 ] ℤ/.^+ n  ∎

  lemma : ∀ i → Q.[ + 1 ⊛ i ] ≡ Q.[ + 1 ] ℤ/.^ i
  lemma (+ n)    = *+-lemma n
  lemma -[1+ n ] =
    Q.[ + 1 ⊛ -[1+ n ] ]           ≡⟨⟩
    Q.[ -[ 1 ] *+ suc n ]          ≡⟨ cong Q.[_] $ sym $ ℤG.^+⁻¹ {p = + 1} (suc n) ⟩
    Q.[ - (+ 1 *+ suc n) ]         ≡⟨⟩
    Q.[ + 1 *+ suc n ] ℤ/.⁻¹       ≡⟨ cong ℤ/._⁻¹ $ *+-lemma (suc n) ⟩
    (Q.[ + 1 ] ℤ/.^+ suc n) ℤ/.⁻¹  ≡⟨ ℤ/.^+⁻¹ {p = Q.[ + 1 ]} (suc n) ⟩
    (Q.[ + 1 ] ℤ/.⁻¹) ℤ/.^+ suc n  ≡⟨⟩
    Q.[ + 1 ] ℤ/.^ -[1+ n ]        ∎

-- ℤ/[1+ n ]ℤ is abelian.

abelian : Abelian ℤ/[1+ n ]ℤ
abelian = G.Cyclic→Abelian ℤ/[1+ _ ]ℤ cyclic

-- For finite cyclic groups of order at least 2 the number 0 is not
-- equal to 1 (assuming univalence).

0≢1 :
  ∀ n →
  _≢_ {A = Group.Carrier ℤ/[1+ suc n ]ℤ}
    Q.[ + 0 ] Q.[ + 1 ]
0≢1 n =
  Q.[ + 0 ] ≡ Q.[ + 1 ]  ↔⟨ inverse $
                            Q.related≃[equal]
                              (≡-mod-is-equivalence-relation (2 P.+ n))
                              T.truncation-is-proposition ⟩
  (+ 0 ≡ + 1 mod 2 ⊕ n)  ↝⟨ 0≢1mod2+ n ⟩□
  ⊥                      □

-- If any element in ℤ/2ℤ is added to itself we get 0.

private
  module ℤ/2ℤ = Group ℤ/[1+ 1 ]ℤ

+≡0 : ∀ i → i ℤ/2ℤ.∘ i ≡ ℤ/2ℤ.id
+≡0 = Q.elim-prop λ where
  .Q.is-propositionʳ _ → Q./-is-set
  .Q.[]ʳ i → Q.[]-respects-relation
    ∣ i
    , (i + i          ≡⟨ cong (_+_ i) $ sym +-right-identity ⟩
       i + (i + + 0)  ≡⟨⟩
       i *+ 2         ≡⟨ sym +-left-identity ⟩∎
       + 0 + i *+ 2   ∎)
    ∣
