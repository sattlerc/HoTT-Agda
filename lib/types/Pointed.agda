{-# OPTIONS  #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.Equivalences
open import lib.Univalence
open import lib.NType
open import lib.types.Pi
open import lib.types.Sigma

module lib.types.Pointed where

Ptd : ∀ i → Type (lsucc i)
Ptd i = Σ (Type i) (λ A → A)

Ptd₀ = Ptd lzero

∙[_,_] : ∀ {i} (A : Type i) (a : A) → Ptd i
∙[_,_] = _,_

_∙→_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
(A , a₀) ∙→ (B , b₀) = ∙[ Σ (A → B) (λ f → f a₀ == b₀) , ((λ _ → b₀), idp) ]

ptd[_,_] = ∙[_,_]
_ptd->_ = _∙→_

infixr 4 _∘ptd_

ptd-idf : ∀ {i} (X : Ptd i) → fst (X ∙→ X)
ptd-idf A = ((λ x → x) , idp)

ptd-cst : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ∙→ Y)
ptd-cst {Y = Y} = ((λ x → snd Y) , idp)

_∘ptd_ : ∀ {i j k} {A : Ptd i} {B : Ptd j} {C : Ptd k}
  (g : fst (B ∙→ C)) (f : fst (A ∙→ B)) → fst (A ∙→ C)
(g , gpt) ∘ptd (f , fpt) = (g ∘ f) , (ap g fpt ∙ gpt)

∘ptd-unit-l : ∀ {i j} {A : Ptd i} {B : Ptd j} (f : fst (A ∙→ B))
  → ptd-idf B ∘ptd f == f
∘ptd-unit-l (f , idp) = idp

∘ptd-assoc : ∀ {i j k l} {A : Ptd i} {B : Ptd j} {C : Ptd k} {D : Ptd l}
  (h : fst (C ∙→ D)) (g : fst (B ∙→ C)) (f : fst (A ∙→ B))
  → ((h ∘ptd g) ∘ptd f) == (h ∘ptd (g ∘ptd f))
∘ptd-assoc (h , hpt) (g , gpt) (f , fpt) = pair= idp (lemma fpt gpt hpt)
  where 
  lemma : ∀ {x} {y} (fpt : x == y) → ∀ gpt → ∀ hpt →
          ap (h ∘ g) fpt ∙ ap h gpt ∙ hpt == ap h (ap g fpt ∙ gpt) ∙ hpt
  lemma idp gpt hpt = idp

{- Obtaining equality of pointed types from an equivalence -}
ptd-ua : ∀ {i} {A B : Type i} {a₀ : A} {b₀ : B}
  (e : A ≃ B) → –> e a₀ == b₀ → ∙[ A , a₀ ] == ∙[ B , b₀ ]
ptd-ua e p = pair= (ua e) (↓-idf-ua-in e p)

∙→-level : ∀ {i j} {A : Ptd i} {B : Ptd j} {n : ℕ₋₂} 
  → has-level n (fst B) → has-level n (fst (A ∙→ B))
∙→-level pB = Σ-level (Π-level (λ _ → pB)) (λ _ → =-preserves-level _ pB)
