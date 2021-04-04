{-# OPTIONS --rewriting #-}
module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import Function using (_∘_)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M


-- Exercise: Show that universals distribute over conjunction
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
  { to = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
  ; from = λ {⟨ f , g ⟩ a → ⟨ f a , g a ⟩}
  ; from∘to = λ _ → refl
  ; to∘from = λ {⟨ _ , _ ⟩ → refl}
  } 

-- Exercise: Show that a disjunction of universals implies a universal of disjunctions: 
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) = inj₁ ∘ f
⊎∀-implies-∀⊎ (inj₂ g) = inj₂ ∘ g

-- Exercise: ∀-×
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

∀-× : ∀ {B : Tri → Set}
  → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc 
∀-× {B} = record
  { to = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
  ; from = back
  ; from∘to = λ f → ∀-extensionality λ {aa → refl ; bb → refl; cc → refl}
  ; to∘from = λ y → refl
  }
  where
    back : B aa × B bb × B cc → (x : Tri) → B x
    back x aa = proj₁ x
    back x bb = (proj₁ ∘ proj₂) x
    back x cc = (proj₂ ∘ proj₂) x

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y


∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

-- Exercise: Show that existentials distribute over disjunction
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ {A} {B} {C} = record
  { to = front
  ; from = back
  ; from∘to = λ { ⟨ _ , inj₁ _ ⟩ → refl ; ⟨ _ , inj₂ _ ⟩ → refl}
  ; to∘from = λ { (inj₁ ⟨ _ , _ ⟩) → refl ; (inj₂ ⟨ _ , _ ⟩) → refl}
  }
 where
   front : ∃[ x ] (B x ⊎ C x) → ∃[ x ] B x ⊎ ∃[ x ] C x
   front ⟨ a , inj₁ x ⟩ = inj₁ ⟨ a , x ⟩
   front ⟨ a , inj₂ y ⟩ = inj₂ ⟨ a , y ⟩
   back : ∃[ x ] B x ⊎ ∃[ x ] C x → ∃[ x ] (B x ⊎ C x)
   back (inj₁ ⟨ x , y ⟩) = ⟨ x , inj₁ y ⟩
   back (inj₂ ⟨ x , y ⟩) = ⟨ x , inj₂ y ⟩

-- Exercise: Show that an existential of conjunctions implies a conjunction of existentials
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ fst , snd ⟩ ⟩ = ⟨ ⟨ a , fst ⟩ , ⟨ a , snd ⟩ ⟩


-- Exercise: ∃-⊎
∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ = record
  { to = λ { ⟨ aa , p ⟩ → inj₁ p
           ; ⟨ bb , p ⟩ → inj₂ (inj₁ p)
           ; ⟨ cc , p ⟩ → inj₂ (inj₂ p)
           }
  ; from = λ { (inj₁ x) → ⟨ aa , x ⟩
             ; (inj₂ (inj₁ x)) → ⟨ bb , x ⟩
             ; (inj₂ (inj₂ x)) → ⟨ cc , x ⟩
             }
  ; from∘to = λ { ⟨ aa , x₁ ⟩ → refl
                ; ⟨ bb , x₁ ⟩ → refl
                ; ⟨ cc , x₁ ⟩ → refl
                }
  ; to∘from = λ { (inj₁ x) → refl
                ; (inj₂ (inj₁ x)) → refl
                ; (inj₂ (inj₂ y)) → refl
                }
  }

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩


∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)

-- Exercise
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm; *-suc; +-suc; +-assoc)

-- Recognize addition definition on both arguments
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
{-# REWRITE +-identityʳ +-suc #-}


even-∃' : ∀ {n : ℕ} → even n → ∃[ m ] (2 * m      ≡ n)
odd-∃'  : ∀ {n : ℕ} →  odd n → ∃[ m ] (2 * m + 1  ≡ n)
∃-even' : ∀ {n : ℕ} → ∃[ m ] (2 * m     ≡ n) → even n
∃-odd'  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n

even-∃' even-zero = ⟨ zero , refl ⟩
even-∃' (even-suc o) with odd-∃' o
... | ⟨ x , refl ⟩
  rewrite +-identityʳ x
        | +-identityʳ (suc x)
        | +-assoc x x 1
        | +-suc x 0
  = ⟨ suc x , refl ⟩

odd-∃' (odd-suc e) with even-∃' e
... | ⟨ x , refl ⟩ = ⟨ x , refl ⟩

∃-even' ⟨ zero , refl ⟩ = even-zero
∃-even' ⟨ suc x , refl ⟩ = even-suc (∃-odd' ⟨ x , refl ⟩)

∃-odd' ⟨ x , refl ⟩ = odd-suc (∃-even' ⟨ x , refl ⟩)


-- Exercise: Show that y ≤ z holds if and only if there exists a x such that x + y ≡ z.
open import plfa.part1.Relations using (_≤_; z≤n; s≤s;≤-refl; ≤-antisym; ≤-trans; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
open import plfa.part1.Isomorphism using (_⇔_)

∃-|-≤ : ∀ { y z : ℕ } → (y ≤ z) ⇔ (∃[ x ] ( x + y ≡ z))
∃-|-≤ {y} {z} = record
  { to = g
  ; from = f
  }
 where
  g : ∀ { m n : ℕ } → (m ≤ n) → (∃[ x ] ( x + m ≡ n))
  g {m} {n} z≤n = ⟨ n , refl ⟩
  g (s≤s {m} {n} m≤n) with g m≤n
  ... | ⟨ x , p ⟩ = ⟨ x , cong suc p ⟩
  f : _
  f ⟨ zero , refl ⟩ = ≤-refl
  f ⟨ suc x , refl ⟩ = +-monoˡ-≤  0 (suc x) y z≤n

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }

-- Exercise: Show that existential of a negation implies negation of a universal

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , p ⟩  = λ f → p (f x)

-- Exercise: Bin
open import plfa.part1.Induction
    using (Bin; ⟨⟩; _O; _I; inc; from; to; Bin-inv-from-to; Bin-inc-suc)

open import plfa.part1.Relations
    using (One; one; bEven; bOdd; Can; zero; leading; Can-to; Can-to∘from-iso)

≡One : ∀{b : Bin} (o o' : One b) → o ≡ o'
≡One one one = refl
≡One {b O} (bEven {b} o) (bEven {b} o') = cong bEven (≡One o o')
≡One (bOdd o) (bOdd o') = cong bOdd (≡One o o')

≡Can : ∀{b : Bin} (cb : Can b) (cb' : Can b) → cb ≡ cb'
≡Can zero zero = refl
≡Can zero (leading (bEven ()))
≡Can (leading (bEven ())) zero
≡Can (leading x) (leading y) = cong leading (≡One x y)

first : ∀ {A : Set} {B : A → Set} → Σ A B → A
first ⟨ x , _ ⟩ = x

proj₁≡→Can≡ : {cb cb′ : ∃[ b ](Can b)} → first cb ≡ first cb′ → cb ≡ cb′
proj₁≡→Can≡ {⟨ x , p ⟩} {⟨ _ , q ⟩} refl with ≡Can q p
... | refl = refl

ℕ-≃-∃Can : ℕ ≃ ∃[ b ](Can b)
ℕ-≃-∃Can = record
  { to = go
  ; from = come
  ; from∘to = surj
  ; to∘from = inj
  }
 where
  go : _
  go zero = ⟨ ⟨⟩ O , zero ⟩
  go (suc n) = ⟨ to (suc n) , Can-to (suc n) ⟩
  come : _
  come ⟨ x , p ⟩ = from x
  surj : _
  surj zero = refl
  surj (suc n) = Bin-inv-from-to (suc n)
  inj : _
  inj = {!!}
