{-# OPTIONS  #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Bool
open import lib.types.Lift
open import lib.types.Nat
open import lib.types.Pointed
open import lib.types.TLevel
open import lib.types.Suspension

module lib.types.IteratedSuspension where

Ptd-Susp^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
Ptd-Susp^ O X = X
Ptd-Susp^ (S n) X = Ptd-Susp (Ptd-Susp^ n X)

Ptd-Susp^-conn : ∀ {i} (n : ℕ) {X : Ptd i} {m : ℕ₋₂}
  → is-connected m (fst X) → is-connected ((n -2) +2+ m) (fst (Ptd-Susp^ n X))
Ptd-Susp^-conn O cX = cX
Ptd-Susp^-conn (S n) cX = Susp-conn (Ptd-Susp^-conn n cX)


Ptd-Sphere : ∀ {i} → (n : ℕ) → Ptd i
Ptd-Sphere n = Ptd-Susp^ n (Ptd-Lift Ptd-Bool)

Sphere : ∀ {i} → (n : ℕ) → Type i
Sphere n = fst (Ptd-Sphere n)
