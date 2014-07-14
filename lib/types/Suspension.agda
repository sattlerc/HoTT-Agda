{-# OPTIONS  #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.Unit

-- Suspension is defined as a particular case of pushout

module lib.types.Suspension where

module _ {i} (A : Type i) where

  suspension-span : Span
  suspension-span = span Unit Unit A (λ _ → tt) (λ _ → tt)

  Suspension : Type i
  Suspension = Pushout suspension-span

  north : Suspension
  north = left tt

  south : Suspension
  south = right tt

  merid : A → north == south
  merid x = glue x

  module SuspensionElim {j} {P : Suspension → Type j} (n : P north)
    (s : P south) (p : (x : A) → n == s [ P ↓ merid x ])
    = PushoutElim (λ _ → n) (λ _ → s) p

  open SuspensionElim public using () renaming (f to Suspension-elim)

  module SuspensionRec {j} {C : Type j} (n s : C) (p : A → n == s)
    = PushoutRec {d = suspension-span} (λ _ → n) (λ _ → s) p

  module SuspensionRecType {j} (n s : Type j) (p : A → n ≃ s)
    = PushoutRecType {d = suspension-span} (λ _ → n) (λ _ → s) p

suspension-ptd-span : ∀ {i} → Ptd i → Ptd-Span
suspension-ptd-span X =
  ptd-span Ptd-Unit Ptd-Unit X (ptd-cst {X = X}) (ptd-cst {X = X})

Ptd-Susp : ∀ {i} → Ptd i → Ptd i
Ptd-Susp (A , _) = ∙[ Suspension A , north A ]

module _ {i j} where

  module SuspFmap {A : Type i} {B : Type j} (f : A → B) =
    SuspensionRec A (north B) (south B) (merid B ∘ f)

  susp-fmap : {A : Type i} {B : Type j} (f : A → B)
    → (Suspension A → Suspension B)
  susp-fmap = SuspFmap.f

  ptd-susp-fmap : {X : Ptd i} {Y : Ptd j} (f : fst (X ∙→ Y))
    → fst (Ptd-Susp X ∙→ Ptd-Susp Y)
  ptd-susp-fmap (f , fpt) = (susp-fmap f , idp)
