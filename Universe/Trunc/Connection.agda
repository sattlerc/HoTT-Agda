{-# OPTIONS --without-K #-}

{- This module defines our notion of connectedness not requiring HITs.
   We define the generic n-connected version of a type, show that it is
   n-connected, and that it behaves like the original type above level n.
   We conclude by shoing this notion coincides with the usual notion.
   of connectedness in the presence of HITs. -}
module Universe.Trunc.Connection where

open import lib.Basics
open import lib.NType2
open import lib.Equivalences2
open import lib.types.Unit
open import lib.types.Nat hiding (_+_)
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Paths
open import lib.types.TLevel

open import Universe.Utility.General
open import Universe.Utility.Pointed
open import Universe.Utility.TruncUniverse

open import Universe.Trunc.Universal
open import Universe.Trunc.Basics
open import Universe.Trunc.TypeConstructors


open trunc-ty
open trunc-prop

{- Our plain MLTT connectedness predicate.
   Because of predicativity issues, it has to live in one universe higher
   than its argument type C. Internally, we really want to quantify over
   truncation operators not only at the level of C, but also at levels below C.
   This would be the same in a theory with cumulative universes, but we are
   working in Agda. Since we are only going to actually use the truncation
   operator at one level lower than C, we restrict ourselves to this specific
   assumption in this particular development for no particular reason other
   than brevity of presentation. The reason for this difference of one level
   will become apparent in the definition of 'connection'. -}
module _ {i} (n : ℕ₋₂) (C : Type (lsucc i)) where
  is-connected⋆ : Type (lsucc (lsucc i))
  is-connected⋆ = (Tr : (X : Type i) → trunc-ty n X (lsucc i))
                  (TrC : trunc-ty n C (lsucc i))
                → is-contr ⟦ type TrC ⟧

{- The (n+1)-connected version, or n-connection of some Type A at point a.
   Since we internally quantify over the type of truncations of a path space
   from a before being able to require an element in the truncation,
   predicativity issues force 'connection' to live in a universe one level
   higher than A.
   
   Take particular care in noting that the parameter n is in fact one-off,
   for example, The type 'connection (-2)' denotes the (-1)-connection. -}
module _ {i} (A : Type i) (a : A) where
  module _ (n : ℕ₋₂) where
    connection• : Type• (lsucc i)
    connection• =
      Σ• ((A , a)
        , ((λ b → (TrP : trunc-ty n (a == b) i) → ⟦ type TrP ⟧)
         , (λ TrP → cons TrP idp)))

    {- The base type of the (n+1)-connection base type:
      Σ A (λ b → (TrP : trunc-ty n (a == b) i) → ⟦ type TrP ⟧. -}
    connection : Type (lsucc i)
    connection = base connection•

    connection-is-connected : is-connected⋆ (S n) connection
    connection-is-connected Tr TrC = equiv-preserves-level (e ⁻¹) h where

      -- The supplied generic truncation operator is used only to truncate A.
      TrA : trunc-ty (S n) A (lsucc i)
      TrA = Tr A

      TrP : (b : A) → trunc-ty n (a == b) i
      TrP = trunc-path.trunc {j = i} TrA a

      {- This definition typechecks since
           Σ A (λ b → ⟦ type (TrP b) ⟧  ≡  Σ A (λ a → cons TrA a == cons TrA b)
         by construction of trunc-path.trunc. -}
      TrD : trunc-ty (S n) (Σ A (λ b → ⟦ type (TrP b) ⟧)) (lsucc i)
      TrD = trunc-Σ.trunc {j = lsucc i} TrA
              (λ b → trunc-self.trunc (Path-≤ (type TrA) (cons TrA a) b))

      u : connection ≃ Σ A (λ b → ⟦ type (TrP b) ⟧)
      u = equiv-Σ-snd {B = λ _ → Π _ _}  -- No idea why Agda wants this.
                      (λ b → Π₁-contr (trunc-inhab-contr {j = i} (TrP b)))

      e : ⟦ type TrC ⟧ ≃ ⟦ type TrD ⟧
      e = trunc-functor.fmap-equiv {j = lsucc i} TrC TrD u

      {- Note that
           ⟦ type TrD ⟧  ≡  Σ ⟦ type TrA ⟧ (λ tb → cons TrA a == tb)
         by construction of trunc-Σ.trunc. -}
      h : is-contr ⟦ type TrD ⟧
      h = pathfrom-is-contr (cons TrA a)

  -- the (n+1)-connection of A coincides with A on dimension n+2 and above.
  connection-higher-dim : (n : ℕ) → (Ω ^ (n + 2)) (connection• ⟨ n ⟩)
                                 ≃• (Ω ^ (n + 2)) (A , a)
  connection-higher-dim n =
    forget-Ω^-Σ•₂ _ (n + 2) (λ _ → Π-level (λ Tr → snd (type Tr)))

-- For the first time in the dependency chain, we assume HITs.
module with-hits where
  open import lib.types.Truncation
  open import lib.NConnected
  
  {- With the truncations of the HoTT community's library,
     our truncation types are always inhabited, and hence contractible. -}
  module _ {i j} where
    trunc : (n : ℕ₋₂) (A : Type i) → trunc-ty n A (i ⊔ j)
    trunc n A = record
      { type = (Trunc n A , Trunc-level)
      ; cons = [_]
      ; univ = λ U → is-eq
        (λ f → f ∘ [_]) (Trunc-rec (snd U)) (λ f → idp)
        (λ f → λ= (Trunc-elim (λ _ → =-preserves-level _ (snd U))
                              (λ a → idp)))}
      
    trunc-contr : {n : ℕ₋₂} {A : Type i} → is-contr (trunc-ty n A (i ⊔ j))
    trunc-contr = trunc-inhab-contr {j = j} (trunc _ _)

  -- Our connectedness⋆ is equivalent to HIT connectedness.
  module _ {i} {n : ℕ₋₂} {A : Type (lsucc i)} where
    conn⋆-conn : is-connected⋆ n A ≃ is-connected n A
    conn⋆-conn = Π₁-contr (trunc-contr {j = lsucc i})
              ∘e Π₁-contr (Π-level (λ _ → trunc-contr {j = lsucc i}))
