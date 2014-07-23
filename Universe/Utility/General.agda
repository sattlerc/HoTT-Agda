{-# OPTIONS --without-K #-}
module Universe.Utility.General where

open import lib.Basics

open import lib.types.Nat hiding (_+_)
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Unit


-- A readable notation for the join of universe levels.
infixr 8  _⊔_

_⊔_ : ULevel → ULevel → ULevel
_⊔_ = lmax


-- Important detail: addition operator adjustment.
_+_ : ℕ → ℕ → ℕ
a + b = b lib.types.Nat.+ a  -- n + 1 should mean S n (author preference)!

{- Since natural numbers and universe levels use
   different types, we require a translation operation. -}
｢_｣ : ℕ → ULevel
｢ 0   ｣ = lzero
｢ S n ｣ = lsucc ｢ n ｣
 

{- The (function) exponentiation operator. For convenience, we
   choose to define it via postcomposition in the recursion step. -}
infix 10 _^_

_^_ : ∀ {i} {A : Set i} → (A → A) → ℕ → A → A
f ^ 0   = idf _ 
f ^ S n = f ^ n ∘ f


{- The rest of this file contains the remainder of the library type material
   that could not yet be merged into the community's HoTT library due to
   organizational issues. -}

module _ {i j} {A : Type i} {B : A → Type j} where
  module _ (h : is-contr A) where
    Π₁-contr : Π A B ≃ B (fst h)
    Π₁-contr = Π₁-Unit ∘e equiv-Π-l _ (snd (contr-equiv-Unit h ⁻¹)) ⁻¹

    Σ₁-contr : Σ A B ≃ B (fst h)
    Σ₁-contr = Σ₁-Unit ∘e equiv-Σ-fst _ (snd (contr-equiv-Unit h ⁻¹)) ⁻¹

  module _ (h : (a : A) → is-contr (B a)) where
    Σ₂-contr : Σ A B ≃ A
    Σ₂-contr = Σ₂-Unit ∘e equiv-Σ-snd (λ _ → contr-equiv-Unit (h _))

    Π₂-contr : Π A B ≃ ⊤
    Π₂-contr = Π₂-Unit ∘e equiv-Π-r (λ _ → contr-equiv-Unit (h _))

×-comm : ∀ {i j} {A : Type i} {B : Type j} → (A × B) ≃ (B × A)
×-comm = equiv (λ {(a , b) → (b , a)})
               (λ {(b , a) → (a , b)})
               (λ _ → idp) (λ _ → idp)

Σ-comm-snd : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
           → Σ (Σ A B) (λ ab → C (fst ab)) ≃ Σ (Σ A C) (λ ac → B (fst ac))
Σ-comm-snd {A = A} {B} {C} = 
  Σ (Σ A B) (λ ab → C (fst ab))  ≃⟨ Σ-assoc ⟩
  Σ A (λ a → B a × C a)          ≃⟨ equiv-Σ-snd (λ _ → ×-comm) ⟩
  Σ A (λ a → C a × B a)          ≃⟨ Σ-assoc ⁻¹ ⟩
  Σ (Σ A C) (λ ac → B (fst ac))  ≃∎


module _ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k} where
  ↓-cst→app-equiv : {x x' : A} {p : x == x'} {u : (b : B) → C x b} {u' : (b : B) → C x' b}
                  → ((b : B) → u b == u' b [ (λ x → C x b) ↓ p ]) ≃ (u == u' [ (λ x → (b : B) → C x b) ↓ p ])
  ↓-cst→app-equiv {p = idp} = equiv λ= app= (! ∘ λ=-η) (λ= ∘ app=-β)

module _ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k} where
  ↓-cst2-equiv : {x y : A} (p : x == y) {b : C x} {c : C y}
    (q : b == c [ C ↓ p ]) {u : B x} {v : B y}
    → (u == v [ B ↓ p ]) ≃ (u == v [ (λ xy → B (fst xy)) ↓ (pair= p q) ])
  ↓-cst2-equiv idp idp = ide _

module _ {i} {A B : Type i} (e : A ≃ B) {u : A} {v : B} where
  ↓-idf-ua-equiv : (–> e u == v) ≃ (u == v [ (λ x → x) ↓ (ua e) ])
  ↓-idf-ua-equiv = to-transp-equiv _ _ ⁻¹ ∘e (_ , pre∙-is-equiv (ap (λ z → z u) (ap coe (ap-idf (ua e)) ∙ ap –> (coe-equiv-β e))))

