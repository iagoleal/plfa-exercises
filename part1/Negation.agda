module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat                              using (ℕ; zero; suc)
open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.Sum                              using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product                          using (_×_; _,_; proj₁; proj₂)
open import plfa.part1.Isomorphism                using (_≃_; extensionality)
open import Function using (_∘_)

¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ ( x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))


-- Exercise: Using negation, show that strict inequality is irreflexive, that is, n < n holds for no n.

open import plfa.part1.Relations
  using (_<_; z<s; s<s; <-trans; +-monoʳ-<)

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive {suc n} (s<s x) = <-irreflexive x

-- Exercise: Show that strict inequality satisfies trichotomy
data Trichotomy (m n : ℕ) : Set where
  le : m < n → ¬ (m ≡ n) → ¬ (n < m) → Trichotomy m n
  ge : n < m → ¬ (m ≡ n) → ¬ (m < n) → Trichotomy m n
  eq : m ≡ n → ¬ (m < n) → ¬ (n < m) → Trichotomy m n

suc-≡ : ∀ { m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-≡ refl = refl

suc-< : ∀ {m n : ℕ} → suc m < suc n → m < n
suc-< (s<s m<n) = m<n


trichotomy : ∀ {m n : ℕ} → Trichotomy m n
trichotomy {zero} {zero} = eq refl (λ ()) (λ ())
trichotomy {zero} {suc n} = le z<s (λ ()) (λ ())
trichotomy {suc m} {zero} = ge z<s (λ ()) (λ ())
trichotomy {suc m} {suc n} with trichotomy {m} {n}
... | le l e g = le (s<s l) (e ∘ suc-≡) (g ∘ suc-<)
... | ge g e l = ge (s<s g) (e ∘ suc-≡) (l ∘ suc-<) 
... | eq e l g = eq (cong suc e) (l ∘ suc-<) (g ∘ suc-<)

-- Exercise: Show that conjunction, disjunction, and negation are related by a version of De Morgan’s Law.

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ f → ( f ∘ inj₁ , f ∘ inj₂ )
    ; from    = λ {( f , g ) → [ f , g ]}
    ; from∘to = λ f → extensionality λ { (inj₁ x) → refl ; (inj₂ x) → refl }
    ; to∘from = λ {( f , g ) → refl}
    }

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× {A} {B} = →-distrib-⊎ {A} {B} {⊥}

{-
 ¬ (⊥ × ⊥) ≃ ¬ ⊥ ≃ ⊥ → ⊥ ≃ ⊤
 (¬ ⊥) ⊎ (¬ ⊥) ≃ (⊥ → ⊥) ⊎ (⊥ → ⊥) ≃ 2 × ⊤
-}

¬⊎-implies-¬× : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B) 
¬⊎-implies-¬× (inj₁ ¬a) = λ { (a , b) → ¬a a}
¬⊎-implies-¬× (inj₂ ¬b) = λ { (a , b) → ¬b b}

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ z → z (inj₂ (λ x → z (inj₁ x)))

-- Exercise: Classical
{-
  Excluded Middle: A ⊎ ¬ A, for all A
  Double Negation Elimination: ¬ ¬ A → A, for all A
  Peirce’s Law: ((A → B) → A) → A, for all A and B.
  Implication as disjunction: (A → B) → ¬ A ⊎ B, for all A and B.
  De Morgan: ¬ (¬ A × ¬ B) → A ⊎ B, for all A and B.
-}


-- Exercise: Show that any negated formula is stable, and that the conjunction of two stable formulas is stable.
Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable ¬¬¬a a = ¬¬¬-elim ¬¬¬a a

×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable sa sb = λ ¬¬axb →
             sa (λ ¬a → ¬¬axb λ {(a , b) → ¬a a})
           , sb (λ ¬b → ¬¬axb λ {(a , b) → ¬b b})
