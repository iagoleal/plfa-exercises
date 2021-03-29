module plfa.part1.Relations where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_;_*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm; *-suc; +-suc)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl

-- Orderings exercise
{- Fix a (small) category C and define Ĉ as the preorder such that
       X ≤ Y ⇔ ∃ f : X → Y.
  This is a preorder but not partial if there are isomorphic objects.
-}
{- If card(X) > 1, P(X) is a partial order by inclusion but not total.
-}

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s x) (s≤s y) = s≤s (≤-trans x y)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s x) (s≤s y) = cong suc (≤-antisym x y)

data Total (m n : ℕ) : Set where
  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero _ = forward z≤n
≤-total _ zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)


-- Exercise: show that multiplication is also monotonic

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q with *-monoʳ-≤ n p q p≤q
... | x = +-mono-≤ p q (n * p) (n * q) p≤q x

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤  m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n)
                                   (*-monoʳ-≤ n p q p≤q)

-------------------------------
-- * Strict inequality
-------------------------------

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- Exercises

-- Transitivity of <
<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- (weak) trichotomy of <
data Trichotomy (m n : ℕ) : Set where
  le : m < n → Trichotomy m n
  ge : n < m → Trichotomy m n
  eq : m ≡ n → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = eq refl
trichotomy zero (suc n) = le z<s
trichotomy (suc m) zero = ge z<s
trichotomy (suc m) (suc n) with trichotomy m n
... | le x = le (s<s x)
... | ge x = ge (s<s x)
... | eq x = eq (cong suc x)

-- Monotonicty of + over <
+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n  rewrite +-comm m p | +-comm n p  = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q) 

-- Exercise: Show that suc m ≤ n implies m < n, and conversely
≤-iff-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-iff-< zero (suc n) sm≰n = z<s
≤-iff-< (suc m) (suc n) (s≤s sm≤n) = s<s (≤-iff-< m n sm≤n)

<-iff-≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<-iff-≤ zero (suc n) m<n = s≤s z≤n
<-iff-≤ (suc m) (suc n) (s<s m<n) = s≤s (<-iff-≤ m n m<n)

-- Alternative proof that strict inequality is transitive
≤-suc : ∀ (n : ℕ) → n ≤ suc n
≤-suc zero = z≤n
≤-suc (suc n) = s≤s (≤-suc n)

<-trans-revisited : ∀ {m n p : ℕ}
  → m < n → n < p → m < p
<-trans-revisited {m} {n} {p} m<n n<p = ≤-iff-< m p sm≤p
  where sm≤n  = <-iff-≤ m n m<n
        sn≤p  = <-iff-≤ n p n<p
        n≤sn  = ≤-suc n
        sm≤sn = ≤-trans sm≤n n≤sn 
        sm≤p  = ≤-trans sm≤sn sn≤p

-----------------------
-- Even and Odd
-----------------------

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

-- Exercise: Show that the sum of two odd numbers is even.
o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc {m} x) (suc {n} y)
  rewrite +-suc m n = suc (suc (e+e≡e x y))

-- Exercise: Bitstring predicates
open import plfa.part1.Induction
    using (Bin; ⟨⟩; _O; _I; inc; from; to; Bin-inv-from-to)

-- Predicate for Bitstrings starting with ⟨⟩ I
data One : Bin -> Set where
  one : ∀ {b : Bin}
    → One (⟨⟩ I)
  bEven : ∀ {b : Bin}
    → One b
    → One (b O)
  bOdd : ∀ {b : Bin}
    → One b
    → One (b I)

-- Predicate for Bitstrings in canonical form
data Can : Bin → Set where
 zero : Can (⟨⟩ O)
 leading : ∀ {b : Bin}
   → One b
   → Can b

-- inc preserves starting with one
One-inc : ∀ {b : Bin} → One b -> One (inc b)
One-inc one = bEven one
One-inc (bEven n) = bOdd n
One-inc (bOdd n) = bEven (One-inc n)

-- inc preserves canonical form
Can-inc : ∀ {b : Bin} → Can b → Can (inc b)
Can-inc zero = leading one
Can-inc (leading n) = leading (One-inc n)

-- Image of 'to' function is canonical
Can-to : ∀ (n : ℕ) → Can (to n)
Can-to zero = zero
Can-to (suc n) = Can-inc (Can-to n)

-- to ∘ from is id for canonical bitstrings
One-≥-1 : ∀ {b : Bin} → One b → 1 ≤ from b
One-≥-1 one = s≤s z≤n
One-≥-1 (bEven {b} o) with One-≥-1 o
... | 1≤b rewrite sym (+-identityʳ 1) = +-mono-≤ 1 (from b) 0 (from b + 0) 1≤b z≤n
One-≥-1 (bOdd {b} o)
  rewrite +-comm (from b + (from b + 0)) 1 = s≤s z≤n

One->-0 : ∀ {b : Bin} → One b → 0 < from b
One->-0 {b} o = ≤-iff-< 0 (from b) (One-≥-1 o)

-- TODO: finish this
Can-to∘from-iso : ∀ {b : Bin} → Can b → to (from b) ≡ b
Can-to∘from-iso zero = refl
Can-to∘from-iso (leading x) = {!!}
