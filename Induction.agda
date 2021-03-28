module plfa.part1.Induction where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero    n p                       = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-identity : ∀ (n : ℕ) → n + zero ≡ n
+-identity zero = refl
+-identity (suc n) rewrite +-identity n = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite +-identity m = refl
+-comm m (suc n) rewrite +-suc m n | +-comm m n = refl

-- My answers

-- Addition swap
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p
  rewrite +-swap m n p
        | sym (+-suc n (m + p)) = refl

-- Distributive law for *
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p
        | +-assoc p (m * p) (n * p) = refl

-- Associative law for *
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite *-distrib-+ n (m * n) p
        | *-assoc m n p = refl

-- Commutative law for *
*-zero : ∀ (m : ℕ) → m * zero ≡ zero
*-zero zero = refl
*-zero (suc m) = *-zero m

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + (m * n)
*-suc zero n = refl
*-suc (suc m) n
  rewrite *-suc m n
        | (+-swap n m (m * n)) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n = sym (*-zero n)
*-comm (suc m) n
  rewrite *-comm m n = sym(*-suc n m)

-- Zero law for monus
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

-- Monus associates with addition
∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc zero n p
  rewrite 0∸n≡0 n
        | 0∸n≡0 p
        | 0∸n≡0 (n + p) = refl
∸-|-assoc (suc m) zero p = refl
∸-|-assoc (suc m) (suc n) p = ∸-|-assoc m n p

-- Exponentiation laws

^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p = sym (+-identity (m ^ p))
^-distribˡ-|-* m (suc n) p
  rewrite ^-distribˡ-|-* m n p
        | sym (*-assoc m (m ^ n) (m ^ p)) = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite ^-distribʳ-* m n p
        | *-assoc m n ((m ^ p) * (n ^ p))
        | sym (*-assoc  n (m ^ p)  (n ^ p))
        | *-comm n (m ^ p)
        | *-assoc (m ^ p) n (n ^ p)
        | sym (*-assoc m (m ^ p) (n * (n ^ p))) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero
  rewrite *-zero n = refl
^-*-assoc m n (suc p)
  rewrite ^-*-assoc m n p
        | sym (^-distribˡ-|-* m n (n * p))
        | sym (*-suc n p) = refl

-- Bin Laws
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (m O) = m I
inc (m I) = (inc m) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = 2 * (from x)
from (x I) = 2 * (from x) + 1

bin-inc-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
bin-inc-suc ⟨⟩ = refl
bin-inc-suc (b O)
  rewrite +-identity (from b)
        | +-comm (from b + from b) 1 = refl
bin-inc-suc (b I)
  rewrite bin-inc-suc b
        | +-identity (from b)
        | +-assoc (from b) (from b) 1
        | +-suc (from b) zero
        | +-identity (from b)
  = refl

bin-inv-from-to : ∀ (n : ℕ) → from (to n) ≡ n
bin-inv-from-to zero = refl
bin-inv-from-to (suc n)
  rewrite bin-inc-suc (to n) = cong suc (bin-inv-from-to n)

bin-cex-inv-to-from : to (from ⟨⟩) ≡ ⟨⟩ O
bin-cex-inv-to-from = begin to (from ⟨⟩) ≡⟨⟩ to 0 ≡⟨⟩ ⟨⟩ O ∎
