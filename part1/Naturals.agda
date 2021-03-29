module plfa.part1.Naturals where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


--* Definitions:
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 6  _+_  _∸_
infixl 7  _*_

-- Addition
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- Multiplication
_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

-- Monus
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

--------------
--* Exercises
--------------

-- Long-hand 7
seven : ℕ
seven = suc (suc (suc(suc(suc(suc(suc zero))))))

-- Addition exercise
_ : 3 + 4 ≡ 7
_  =  begin
  3 + 4
  ≡⟨⟩
  suc (2 + 4)
  ≡⟨⟩
  suc (suc (1 + 4))
  ≡⟨⟩
  suc(suc ( suc (0 + 4)))
  ≡⟨⟩
  suc(suc(suc(4)))
  ∎

-- Multiplication exercise
_ : 3 * 4 ≡ 12
_ = begin
  3 * 4
  ≡⟨⟩
  3 * 4
  ≡⟨⟩
  4 + (2 * 4)
  ≡⟨⟩
  4 + (4 + (1 * 4))
  ≡⟨⟩
  4 + (4 + 4)
  ≡⟨⟩
  12
  ∎

-- Exponentiation exercise
_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m * (m ^ n)

_  :  3 ^ 4 ≡ 81
_ = begin
    3 ^ 4
    ≡⟨⟩
    3 ^ (suc 3)
    ≡⟨⟩
    3 * (3 ^ 3)
    ≡⟨⟩
    3 * (3 * (3 ^ 2))
    ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩
    3 * (3 * (3 * (3 * (1))))
    ≡⟨⟩
    81
    ∎

-- Monus exercises
∸-example₁ = begin
  5 ∸ 3
  ≡⟨⟩
  4 ∸ 2
  ≡⟨⟩
  3 ∸ 1
  ≡⟨⟩
  2 ∸ 0
  ≡⟨⟩
  2
  ∎

∸-example₂ = begin
  3 ∸ 5
  ≡⟨⟩
  2 ∸ 4
  ≡⟨⟩
  1 ∸ 3
  ≡⟨⟩
  0 ∸ 2
  ≡⟨⟩
  0
  ∎

-- Bin Type exercise
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
