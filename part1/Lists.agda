{-# OPTIONS --rewriting #-}
module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

-- Exercise: Show that the reverse of one list appended to another is the reverse of the second appended to the reverse of the first
reverse-++-distrib : ∀ { A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys = sym (++-identityʳ (reverse ys))
reverse-++-distrib (x ∷ xs) ys
  rewrite reverse-++-distrib xs ys = ++-assoc (reverse ys) (reverse xs) [ x ]

-- Exercise: Show that reverse is an involution:

reverse-involutive : ∀ { A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs)
  rewrite reverse-++-distrib (reverse xs) [ x ] = cong (x ∷_) (reverse-involutive xs)

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎

-- Exercise: Prove that the map of a composition is equal to the composition of two maps
map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C)
  → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality thm
  where
   thm : _
   thm [] = refl
   thm (x ∷ xs) = begin
       (g ∘ f) x ∷ map (g ∘ f) xs
     ≡⟨ cong ((g ∘ f) x ∷_) (thm xs) ⟩
       g (f x) ∷ map g (map f xs)
     ≡⟨⟩
       map g (f x ∷ map f xs)
     ≡⟨⟩
       (map g ∘ map f) (x ∷ xs)
     ∎

-- Exercise: map-++-distribute
map-++-distribute : ∀ {A B : Set} {f : A → B} (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute [] ys = refl
map-++-distribute {A} {B} {f} (x ∷ xs) ys = cong (f x ∷_) (map-++-distribute xs ys)

-- Exercise map-Tree: Define a suitable map operator over trees
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node l x r) = node (map-Tree f g l) (g x) (map-Tree f g r)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

-- Exercise: Use fold to define a function to find the product of a list of numbers
product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl



foldr-++ : ∀ { A B : Set} (op : A → B → B) (e : B) (xs ys : List A)
  → foldr op e (xs ++ ys) ≡ foldr op (foldr op e ys) xs
foldr-++ _ _ [] ys = refl
foldr-++ op e (x ∷ xs) ys = cong (op x) (foldr-++ op e xs ys) 

-- Exercise: foldr-id and foldr-∷

foldr-id : ∀ {A : Set} (xs : List A)
  → foldr _∷_ [] xs ≡ xs
foldr-id [] = refl
foldr-id (x ∷ xs) = cong (x ∷_) (foldr-id xs)

foldr-∷ : ∀ {A : Set} (xs ys : List A)
  → xs ++ ys ≡ foldr _∷_ ys xs
foldr-∷ xs ys = begin
  xs ++ ys 
  ≡⟨ sym (foldr-id (xs ++ ys)) ⟩
  foldr _∷_ [] (xs ++ ys)
  ≡⟨ foldr-++ _∷_ [] xs ys  ⟩
  foldr _∷_ (foldr _∷_ [] ys) xs
  ≡⟨ cong (λ a → foldr _∷_ a xs) (foldr-id ys) ⟩
  foldr _∷_ ys xs
  ∎

-- Exercise: Show that map can be defined using fold
map-is-foldr : ∀ {A B : Set} {f : A → B}
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {A} {B} {f} = extensionality thm
  where
    thm : (x : List A) → map f x ≡ foldr (λ x₁ xs → f x₁ ∷ xs) [] x
    thm [] = refl
    thm (x ∷ xs) = cong (f x ∷_) (thm xs)

-- Exercise: Define a suitable fold function for the type of trees given earlier
fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node l x r) = g (fold-Tree f g l) x (fold-Tree f g r)

-- Exercise: Demonstrate an analogue of map-is-foldr for the type of trees.
map-is-fold-Tree : ∀ {A B C D : Set} {f : A → C} {g : B → D}
  → map-Tree f g ≡ fold-Tree (λ x → leaf (f x)) (λ l x r → node l (g x) r)
map-is-fold-Tree {A} {B} {C} {D} {f} {g} = extensionality thm
  where
   thm : _
   thm (leaf x) = refl
   thm (node l x r) rewrite thm l | thm r = refl

-- Exercise: sum-downFrom
downFrom : ℕ → List ℕ
downFrom zero     =  [ 0 ]
downFrom (suc n)  =  (suc n) ∷ downFrom n

_ : downFrom 3 ≡ [ 3 , 2 , 1 , 0 ]
_ = refl

open import plfa.part1.Induction using (*-distrib-+; +-suc; *-suc; *-comm)
-- Recognize addition definition on both arguments
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
{-# REWRITE +-identityʳ +-suc *-suc *-identityʳ #-}

sum-formula : ∀ {n : ℕ}
  → sum (downFrom n) * 2 ≡ n * (n + 1)
sum-formula {zero} = refl
sum-formula {suc n}
  rewrite *-distrib-+ n (sum (downFrom n)) 2
        | sum-formula {n}
        | *-comm n 2
        = cong (suc ∘ suc) (+-assoc n n (n * suc n))

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

-- Exercise: Define a function foldl which is analogous to foldr, but where operations associate to the left rather than the right.

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl op e [] = e
foldl op e (x ∷ xs) =  foldl op (op e x) xs

_ : ∀ {A B : Set} {_⊗_ : A → B → B} {e : B} {x y z : A}
  → foldr _⊗_ e [ x , y , z ] ≡ x ⊗ (y ⊗ (z ⊗ e))
_ = refl

_ : ∀ {A B : Set} {_⊗_ : B → A → B} {e : B} {x y z : A}
  → foldl _⊗_ e [ x , y , z ]  ≡  ((e ⊗ x) ⊗ y) ⊗ z
_ = refl

-- Exercise: Show that if _⊗_ and e form a monoid, then foldr _⊗_ e and foldl _⊗_ e always compute the same result.
foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl {A} _⊗_ e record { assoc = assoc
                                   ; identityˡ = identityˡ
                                   ; identityʳ = identityʳ
                                   } = extensionality thm
 where
   thm : (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
   thm [] = refl
   thm [ x ] rewrite identityˡ x | identityʳ x = refl
   thm [ x , y ] rewrite identityˡ x | identityʳ y = refl
   thm [ x , y , z ] rewrite identityˡ x | identityʳ z = sym (assoc x y z)
   thm (x ∷ y ∷ z ∷ w ∷ xs)
     rewrite thm ( y ∷ z ∷ w ∷ xs)
           | identityˡ x 
           | identityˡ y
           | assoc x ((y ⊗ z) ⊗ w) (foldl _⊗_ e xs) = {!!}
