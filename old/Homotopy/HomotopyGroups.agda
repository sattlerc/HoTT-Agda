{-# OPTIONS  #-}

open import Base
open import Algebra.Groups
open import Integers
open import Homotopy.Truncation
open import Homotopy.Pointed
open import Homotopy.PathTruncation
open import Homotopy.Connected

-- Definitions and properties of homotopy groups
module Homotopy.HomotopyGroups {i} where

-- Loop space
Ω : (X : pType i) → pType i
Ω X = ⋆[ ⋆ X ≡ ⋆ X , refl ]

Ω-pregroup : (X : pType i) → pregroup i
Ω-pregroup X = record
  { carrier       = (⋆ X) ≡ (⋆ X)
  ; _∙_           = _∘_
  ; e             = refl
  ; _′            = !
  ; assoc         = concat-assoc
  ; right-unit    = refl-right-unit
  ; left-unit     = λ _ → refl
  ; right-inverse = opposite-right-inverse
  ; left-inverse  = opposite-left-inverse
  }

Ωⁿ-pregroup : (n : ℕ) ⦃ ≢0 : n ≢ O ⦄ (X : pType i) → pregroup i
Ωⁿ-pregroup O ⦃ ≢0 ⦄ X = abort-nondep (≢0 refl)
Ωⁿ-pregroup 1 X = Ω-pregroup X
Ωⁿ-pregroup (S (S n)) X = Ωⁿ-pregroup (S n) (Ω X)

-- Homotopy groups
πⁿ-group : (n : ℕ) ⦃ >0 : n ≢ O ⦄ (X : pType i) → group i
πⁿ-group n X = π₀-pregroup (Ωⁿ-pregroup n X)

fundamental-group : (X : pType i) → group i
fundamental-group X = πⁿ-group 1 ⦃ ℕ-S≢O 0 ⦄ X

-- Homotopy groups of loop space
πⁿ-group-from-πⁿΩ : (n : ℕ) ⦃ ≢0 : n ≢ 0 ⦄ (X : pType i)
  → πⁿ-group (S n) X ≡ πⁿ-group n (Ω X)
πⁿ-group-from-πⁿΩ O ⦃ ≢0 ⦄ X = abort-nondep (≢0 refl)
πⁿ-group-from-πⁿΩ 1 X = refl
πⁿ-group-from-πⁿΩ (S (S n)) X = refl

-- Homotopy groups of spaces of a given h-level
abstract
  truncated-πⁿ-group : (n : ℕ) ⦃ ≢0 : n ≢ 0 ⦄ (X : pType i)
    (p : is-truncated (n -1) ∣ X ∣)
    → πⁿ-group n X ≡ unit-group
  truncated-πⁿ-group O ⦃ ≢0 ⦄ X p = abort-nondep (≢0 refl)
  truncated-πⁿ-group 1 X p =
    unit-group-unique _
      (proj refl ,
      π₀-extend ⦃ p = λ x → truncated-is-truncated-S _ (π₀-is-set _ _ _) ⦄
        (λ x → ap proj (π₁ (p _ _ _ _))))
  truncated-πⁿ-group (S (S n)) X p =
    truncated-πⁿ-group (S n) (Ω X) (λ x y → p _ _ x y)


Ωⁿ : (n : ℕ) (X : pType i) → pType i
Ωⁿ 0 X = X
Ωⁿ (S n) X = Ω (Ωⁿ n X)

πⁿ : (n : ℕ) (X : pType i) → pType i
πⁿ n X = τ⋆ ⟨0⟩ (Ωⁿ n X)

other-πⁿ : (n : ℕ) (X : pType i) → pType i
other-πⁿ n X = Ωⁿ n (τ⋆ ⟨ n ⟩ X)

ap-Ω-equiv : (X Y : pType i) (e : X ≃⋆ Y)
  → Ω X ≃⋆ Ω Y
ap-Ω-equiv X Y e = transport (λ u → Ω X ≃⋆ Ω u) (pType-eq e) (id-equiv⋆ _)

τ⋆Ω-is-Ωτ⋆S : (n : ℕ₋₂) (X : pType i)
  → τ⋆ n (Ω X) ≃⋆ Ω (τ⋆ (S n) X)
τ⋆Ω-is-Ωτ⋆S n X = (τ-path-equiv-path-τ-S , refl)

τ⋆kΩⁿ-is-Ωⁿτ⋆n+k : (k n : ℕ) (X : pType i)
  → τ⋆ ⟨ k ⟩ (Ωⁿ n X) ≃⋆ Ωⁿ n (τ⋆ ⟨ n + k ⟩ X)
τ⋆kΩⁿ-is-Ωⁿτ⋆n+k k O X = id-equiv⋆ _
τ⋆kΩⁿ-is-Ωⁿτ⋆n+k k (S n) X =
  equiv-compose⋆ (τ⋆Ω-is-Ωτ⋆S _ _) (ap-Ω-equiv _ _
    (equiv-compose⋆ (τ⋆kΩⁿ-is-Ωⁿτ⋆n+k (S k) n _)
      (transport (λ u → Ωⁿ n (τ⋆ ⟨ n + S k ⟩ X) ≃⋆ Ωⁿ n (τ⋆ ⟨ u ⟩ X))
        (+S-is-S+ n k) (id-equiv⋆ _))))

πⁿ-is-other-πⁿ : (n : ℕ) (X : pType i) → πⁿ n X ≃⋆ other-πⁿ n X
πⁿ-is-other-πⁿ n X =
  transport (λ u → πⁿ n X ≃⋆ Ωⁿ n (τ⋆ ⟨ u ⟩ X)) (+0-is-id n)
    (τ⋆kΩⁿ-is-Ωⁿτ⋆n+k 0 n X)

contr-is-contr-Ω : (X : pType i) → (is-contr⋆ X → is-contr⋆ (Ω X))
contr-is-contr-Ω X p = ≡-is-truncated ⟨-2⟩ p

contr-is-contr-Ωⁿ : (n : ℕ) (X : pType i) → (is-contr⋆ X) → is-contr⋆ (Ωⁿ n X)
contr-is-contr-Ωⁿ O X p = p
contr-is-contr-Ωⁿ (S n) X p = contr-is-contr-Ω _ (contr-is-contr-Ωⁿ n X p)

connected-other-πⁿ : (k n : ℕ) (lt : k < S n) (X : pType i)
  → (is-connected⋆ ⟨ n ⟩ X → is-contr⋆ (other-πⁿ k X))
connected-other-πⁿ k n lt X p =
  contr-is-contr-Ωⁿ k _ (connected⋆-lt k n lt X p)

connected-πⁿ : (k n : ℕ) (lt : k < S n) (X : pType i)
  → (is-connected⋆ ⟨ n ⟩ X → is-contr⋆ (πⁿ k X))
connected-πⁿ k n lt X p =
  equiv-types-truncated _ (π₁ (πⁿ-is-other-πⁿ k X) ⁻¹)
                       (connected-other-πⁿ k n lt X p)
