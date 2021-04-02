module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_;≃-trans; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , _ ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ _ , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ _ , _ ⟩ = refl

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record
  { to      = λ {⟨ a , b ⟩ → ⟨ b , a ⟩ }
  ; from    = λ {⟨ b , a ⟩ → ⟨ a , b ⟩ }
  ; from∘to = λ {⟨ a , b ⟩ → refl}
  ; to∘from = λ { ⟨ b , a ⟩ → refl}
  }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record
  { to      = λ { ⟨ ⟨ a , b ⟩ , c ⟩ → ⟨ a , ⟨ b , c ⟩ ⟩}
  ; from    = λ { ⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ a , b ⟩ , c ⟩ }
  ; from∘to = λ { ⟨ ⟨ a , b ⟩ , c ⟩ → refl }
  ; to∘from = λ { ⟨ a , ⟨ b , c ⟩ ⟩ → refl }
  }

-- Exercise: Show that A ⇔ B is isomorphic to (A → B) × (B → A).
open import plfa.part1.Isomorphism
  using (_⇔_)

open _⇔_

⇔≃× : { A B : Set } → A ⇔ B ≃ (A → B) × (B → A)
⇔≃×  = record
  { to      = λ z → ⟨ to z , from z ⟩
  ; from    = λ { ⟨ f , g ⟩ → record { to = f ; from = g } }
  ; from∘to = λ x → refl
  ; to∘from = λ { ⟨ f , g ⟩ → refl}
  }

data ⊤ : Set where

  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ _ = refl

truth′ : ⊤′
truth′ = _

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ { ⟨ t , a ⟩ → a}
    ; from    = λ {a → ⟨ tt , a ⟩}
    ; from∘to = λ { ⟨ tt , x ⟩ → refl}
    ; to∘from = λ y → refl
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} = ≃-trans ×-comm ⊤-identityˡ

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ a) = f a
case-⊎ f g (inj₂ b) = g b

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

-- Exercise: Show sum is commutative up to isomorphism.
⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to      = λ {(inj₁ a) → inj₂ a ; (inj₂ b) → inj₁ b}
  ; from    = λ {(inj₁ b) → inj₂ b ; (inj₂ a) → inj₁ a}
  ; from∘to = λ { (inj₁ a) → refl ; (inj₂ b) → refl}
  ; to∘from = λ { (inj₁ b) → refl ; (inj₂ a) → refl}
  }

-- Exercise: Show sum is associative up to isomorphism.
⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ ( B ⊎ C)
⊎-assoc {A} {B} {C} = record
  { to      = go
  ; from    = come
  ; from∘to = f
  ; to∘from = g
  }
 where
  go = case-⊎ (case-⊎ inj₁ (inj₂ ∘ inj₁)) (inj₂ ∘ inj₂)
  come = case-⊎ (inj₁ ∘ inj₁) (case-⊎ (inj₁ ∘ inj₂) inj₂) 
  f : (x : (A ⊎ B) ⊎ C) → come (go x) ≡ x
  f (inj₁ (inj₁ _)) = refl
  f (inj₁ (inj₂ _)) = refl
  f (inj₂ _) = refl
  g : (y : A ⊎ B ⊎ C) → go (come y) ≡ y
  g (inj₁ _) = refl
  g (inj₂ (inj₁ _)) = refl
  g (inj₂ (inj₂ _)) = refl

data ⊥ : Set where
  -- no clauses!

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- Exercise: Show empty is the left identity of sums up to isomorphism.
⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A   
⊥-identityˡ = record
  { to = λ { (inj₁ ()) ; (inj₂ a) → a }
  ; from = inj₂
  ; from∘to = λ { (inj₁ ()) ; (inj₂ a) → refl }
  ; to∘from = λ a → refl
  }

-- Exercise: Show empty is the right identity of sums up to isomorphism.
⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A   
⊥-identityʳ = ≃-trans ⊎-comm ⊥-identityˡ

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ { f ⟨ a , b ⟩ → f a b}
    ; from    =  λ f a b → f ⟨ a , b ⟩
    ; from∘to = λ _ → refl
    ; to∘from =  λ f → extensionality λ{ ⟨ x , y ⟩ → refl }
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ f → ⟨ f ∘ inj₁ , f ∘ inj₂  ⟩
    ; from    = λ {⟨ f , g ⟩ → case-⊎ f g }
    ; from∘to = λ f → extensionality λ { (inj₁ x) → refl ; (inj₂ x) → refl }
    ; to∘from = λ {⟨ f , g ⟩ → refl}
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
    ; from    = λ {⟨ f , g ⟩ x → ⟨ f x , g x ⟩}
    ; from∘to = λ f → extensionality λ x → η-× ( f x)
    ; to∘from = λ {⟨ f , g ⟩ → refl}
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }
    
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }

-- Exercise: weak distributive law
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

-- Exercise: Show that a disjunct of conjuncts implies a conjunct of disjuncts: 

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ x , y ⟩) = ⟨ inj₂ x , inj₂ y ⟩

{- Counterexample to converse
    (⊤ ⊎ ⊥) × (⊤ ⊎ ⊥) ≃ ⊤
    (⊤ × ⊥) ⊎ (⊤ × ⊥) ≃ ⊥
-}
