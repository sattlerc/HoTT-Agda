{-# OPTIONS  #-}

open import Base
open import Homotopy.Pointed
open import Homotopy.Connected

module Homotopy.Cover.HomotopyGroupSetIsomorphism {i}
  (A⋆ : pType i) (A⋆-is-conn : is-connected⋆ ⟨0⟩ A⋆) where
  open pType A⋆ renaming (∣_∣ to A ; ⋆ to a)

  open import Algebra.Groups
  open import Homotopy.Truncation
  open import Homotopy.HomotopyGroups {i}
  open import Homotopy.PathTruncation
  open import Homotopy.Cover.Def A
  open import Homotopy.Cover.Ribbon A⋆

  private
    module G = group (fundamental-group A⋆)
  open import Algebra.GroupSets (fundamental-group A⋆)

  {-
      Isomorphism between pi1(A)-sets and coverings.
  -}

  gset⇒covering : gset → covering
  gset⇒covering gset[ _ , act , _ ] = cov[ ribbon act , ribbon-is-set ]

  covering⇒action : ∀ cov → action (covering.fiber cov a)
  covering⇒action cov = act[ tracing cov , (λ _ → refl) , compose-tracing cov ]

  covering⇒gset : covering → gset
  covering⇒gset cov = let open covering cov in
    gset[ fiber a , covering⇒action cov , fiber-is-set a ]

  -- The first direction: covering -> gset -> covering

  -- From 0-connectedness we can get a (-1)-truncated base path.
  -- The challenge is to get this path.
  abstract
    [base-path] : ∀ a₂ → [ a ≡ a₂ ]
    [base-path] = connected-has-all-τ-paths A⋆-is-conn a

  -- Part 1: Show that the generated cover (ribbon) is fiberwisely
  --         equivalent to the original fiber.
  private
    module _ (cov : covering) where

      -- Suppose that we get the path, we can compute the ribbon easily.
      fiber+path⇒ribbon : ∀ a₂ (y : covering.fiber cov a₂) (p : a ≡ a₂)
        → ribbon (covering⇒action cov) a₂
      fiber+path⇒ribbon a₂ y p = trace (tracing cov y (proj $ ! p)) (proj p)

      abstract
        -- Our construction is "constant" with respect to paths.
        fiber+path⇒ribbon-is-path-irrelevant : ∀ a₂
          (y : covering.fiber cov a₂) (p₁ p₂ : a ≡ a₂)
          → fiber+path⇒ribbon a₂ y p₁ ≡ fiber+path⇒ribbon a₂ y p₂
        fiber+path⇒ribbon-is-path-irrelevant .a y p refl =
          trace (tracing cov y (proj $ ! p)) (proj p)
            ≡⟨ paste y (proj $ ! p) (proj p) ⟩
          trace y (proj $ (! p ∘ p))
            ≡⟨ ap (λ x → trace y (proj x)) $ opposite-left-inverse p ⟩∎
          trace y refl₀
            ∎

      -- Call the magical factorization library.
      open import Homotopy.Extensions.ToPropToConstSet

      -- Now we can read the (-1)-truncated path.
      fiber+path₋₁⇒ribbon : ∀ a₂ (y : covering.fiber cov a₂)
        → [ a ≡ a₂ ] → ribbon (covering⇒action cov) a₂
      fiber+path₋₁⇒ribbon a₂ y = cst-extend
        ⦃ ribbon-is-set a₂ ⦄
        (fiber+path⇒ribbon a₂ y)
        (fiber+path⇒ribbon-is-path-irrelevant a₂ y)

  -- So the conversion from fiber to ribbon is done.
  fiber⇒ribbon : ∀ cov a₂ → covering.fiber cov a₂ → ribbon (covering⇒action cov) a₂
  fiber⇒ribbon cov a₂ y = fiber+path₋₁⇒ribbon cov a₂ y $ [base-path] a₂

  -- The other direction is easy.
  ribbon⇒fiber : ∀ cov a₂ → ribbon (covering⇒action cov) a₂ → covering.fiber cov a₂
  ribbon⇒fiber cov a₂ = let open covering cov in
    ribbon-rec-nondep a₂ (fiber a₂) ⦃ fiber-is-set a₂ ⦄ (tracing cov) (compose-tracing cov)

  private
    -- Some routine computations.
    abstract
      ribbon⇒fiber⇒ribbon : ∀ cov a₂ r → fiber⇒ribbon cov a₂ (ribbon⇒fiber cov a₂ r) ≡ r
      ribbon⇒fiber⇒ribbon cov a₂ = ribbon-rec a₂
        (λ r → fiber⇒ribbon cov a₂ (ribbon⇒fiber cov a₂ r) ≡ r)
        ⦃ λ _ → ≡-is-set $ ribbon-is-set a₂ ⦄
        (λ y p → []-extend
          -- All ugly things will go away when bp = proj bp′
          ⦃ λ bp → ribbon-is-set a₂
                    (fiber+path₋₁⇒ribbon cov a₂ (tracing cov y p) bp)
                    (trace y p) ⦄
          (lemma a₂ y p)
          ([base-path] a₂))
        (λ _ _ _ → prop-has-all-paths (ribbon-is-set a₂ _ _) _ _)
        where
          abstract
            lemma : ∀ a₂ (y : covering.fiber cov a) (p : a ≡₀ a₂) (bp : a ≡ a₂)
              → trace {act = covering⇒action cov}
                  (tracing cov (tracing cov y p) (proj $ ! bp)) (proj bp)
              ≡ trace y p
            lemma .a y p refl =
              trace (tracing cov y p) refl₀
                ≡⟨ paste y p refl₀ ⟩
              trace y (p ∘₀ refl₀)
                ≡⟨ ap (trace y) $ refl₀-right-unit p ⟩∎
              trace y p
                ∎

      fiber⇒ribbon⇒fiber : ∀ cov a₂ y → ribbon⇒fiber cov a₂ (fiber⇒ribbon cov a₂ y) ≡ y
      fiber⇒ribbon⇒fiber cov a₂ y = let open covering cov in []-extend
        -- All ugly things will go away when bp = proj bp′
        ⦃ λ bp → fiber-is-set a₂
                  (ribbon⇒fiber cov a₂
                    (fiber+path₋₁⇒ribbon cov a₂ y bp))
                  y ⦄
        (lemma a₂ y)
        ([base-path] a₂)
        where
          abstract
            lemma : ∀ a₂ (y : covering.fiber cov a₂) (bp : a ≡ a₂)
              → tracing cov (tracing cov y (proj $ ! bp)) (proj bp)
              ≡ y
            lemma .a y refl = refl

  covering⇒gset⇒covering : ∀ cov → gset⇒covering (covering⇒gset cov) ≡ cov
  covering⇒gset⇒covering cov = covering-eq $ funext λ a₂
    → eq-to-path $ ribbon⇒fiber cov a₂ , iso-is-eq
        (ribbon⇒fiber cov a₂)
        (fiber⇒ribbon cov a₂)
        (fiber⇒ribbon⇒fiber cov a₂)
        (ribbon⇒fiber⇒ribbon cov a₂)

  -- The second direction : gset -> covering -> gset

  -- Part 2.1: The fiber over the point a is the carrier.
  ribbon-a⇒Y : ∀ {Y} {act : action Y} ⦃ _ : is-set Y ⦄ → ribbon act a → Y
  ribbon-a⇒Y {Y} {act} ⦃ Y-is-set ⦄ = let open action act in
    ribbon-rec-nondep a Y ⦃ Y-is-set ⦄ _∙_ assoc

  ribbon-a≃Y : ∀ {Y} {act : action Y} ⦃ _ : is-set Y ⦄ → ribbon act a ≃ Y
  ribbon-a≃Y {Y} {act} ⦃ Y-is-set ⦄ = let open action act in
    ribbon-a⇒Y ⦃ Y-is-set ⦄ , iso-is-eq _
      (λ y → trace y refl₀)
      (λ y → right-unit y)
      (ribbon-rec a
        (λ r → trace (ribbon-a⇒Y ⦃ Y-is-set ⦄ r) refl₀ ≡ r)
        ⦃ λ _ → ≡-is-set $ ribbon-is-set a ⦄
        (λ y p →
          trace (y ∙ p) refl₀
            ≡⟨ paste y p refl₀ ⟩
          trace y (p G.∙ refl₀)
            ≡⟨ ap (trace y) $ G.right-unit p ⟩∎
          trace y p
            ∎)
        (λ _ _ _ → prop-has-all-paths (ribbon-is-set a _ _) _ _))

  private
    -- Some lemmas to simplify the proofs.
    trans-eq-∙ : ∀ {Y₁ Y₂ : Set i} (Y≃ : Y₁ ≃ Y₂) (_∙_ : Y₁ → G.carrier → Y₁) (y₂ : Y₂) (g : G.carrier)
      → transport (λ Y → Y → G.carrier → Y) (eq-to-path Y≃) _∙_ y₂ g ≡ (Y≃ ☆ (inverse Y≃ y₂ ∙ g))
    trans-eq-∙ = equiv-induction
      (λ {Y₁ Y₂ : Set i} (Y≃ : Y₁ ≃ Y₂)
        → ∀ (_∙_ : Y₁ → G.carrier → Y₁) (y₂ : Y₂) (g : G.carrier)
        → transport (λ Y → Y → G.carrier → Y) (eq-to-path Y≃) _∙_ y₂ g ≡ (Y≃ ☆ (inverse Y≃ y₂ ∙ g)))
      (λ Y _∙_ y₂ g → ap (λ x → transport (λ Y → Y → G.carrier → Y) x _∙_ y₂ g)
                         $ path-to-eq-right-inverse refl)

  gset⇒covering⇒gset : ∀ gs → covering⇒gset (gset⇒covering gs) ≡ gs
  gset⇒covering⇒gset gset[ Y , act , Y-is-set ] =
    let
      open action act
      _⊙_ = tracing cov[ ribbon act , ribbon-is-set {Y} {act} ]
      ≃Y = ribbon-a≃Y ⦃ Y-is-set ⦄
      ⇒Y = ribbon-a⇒Y ⦃ Y-is-set ⦄
    in gset-eq
        (eq-to-path ≃Y)
        (funext λ y → funext $ π₀-extend ⦃ λ _ → ≡-is-set Y-is-set ⦄ λ p →
          transport (λ Y → Y → G.carrier → Y) (eq-to-path ≃Y) _⊙_ y (proj p)
            ≡⟨ trans-eq-∙ ≃Y _⊙_ y (proj p) ⟩
          ⇒Y (transport (ribbon act) p (trace y refl₀))
            ≡⟨ ap ⇒Y $ trans-trace act p y refl₀ ⟩∎
          y ∙ proj p
            ∎)

  -- Finally...

  gset-covering-eq : gset ≃ covering
  gset-covering-eq = gset⇒covering , iso-is-eq _ covering⇒gset
                        covering⇒gset⇒covering
                        gset⇒covering⇒gset

  {-
      Universality of the covering generated by the fundamental group itself.
  -}

  -- FIXME What's the established terminology for this?
  canonical-gset : gset
  canonical-gset = record
    { carrier = G.carrier
    ; act     = record
      { _∙_        = _∘₀_
      ; right-unit = refl₀-right-unit
      ; assoc      = concat₀-assoc
      }
    ; set     = π₀-is-set (a ≡ a)
    }

  -- FIXME What's the established terminology for this?
  canonical-covering : covering
  canonical-covering = gset⇒covering canonical-gset

  private
    module Universality where
      open covering canonical-covering
      open gset canonical-gset

      center′ : Σ A fiber
      center′ = (a , trace {act = act} refl₀ refl₀)

      center : τ ⟨1⟩ (Σ A fiber)
      center = proj center′

      private
        -- An ugly lemma for this development only
        trans-fiber≡cst-proj-Σ-eq : ∀ {i} (P : Set i) (Q : P → Set i)
          (a : P) (c : Σ P Q) {b₁ b₂} (p : b₁ ≡ b₂) (q : a ≡ π₁ c)
          (r : transport Q q b₁ ≡ π₂ c)
          → transport (λ r → (a , r) ≡₀ c) p (proj $ Σ-eq q r)
          ≡ proj (Σ-eq q (ap (transport Q q) (! p) ∘ r))
        trans-fiber≡cst-proj-Σ-eq P Q a c refl q r = refl

      abstract
        path-trace-fiber : ∀ {a₂} y (p : a ≡ a₂)
          → transport fiber (! p ∘ ! y) (trace (proj y) (proj p))
          ≡ trace refl₀ refl₀
        path-trace-fiber y refl =
          transport fiber (! y) (trace (proj y) refl₀)
            ≡⟨ trans-trace act (! y) (proj y) refl₀ ⟩
          trace (proj y) (proj $ ! y)
            ≡⟨ paste refl₀ (proj y) (proj $ ! y) ⟩
          trace refl₀ (proj $ y ∘ ! y)
            ≡⟨ ap (trace refl₀ ◯ proj) $ opposite-right-inverse y ⟩∎
          trace refl₀ refl₀
            ∎

      path-trace : ∀ {a₂} y p → (a₂ , trace {act = act} y p) ≡₀ center′
      path-trace {a₂} =
        π₀-extend ⦃ λ y → Π-is-set λ p → π₀-is-set ((a₂ , trace y p) ≡ center′) ⦄
          (λ y → π₀-extend ⦃ λ p → π₀-is-set ((a₂ , trace (proj y) p) ≡ center′) ⦄
            (λ p → proj $ Σ-eq (! p ∘ ! y) (path-trace-fiber y p)))

      abstract
        path-paste′ : ∀ {a₂} y loop p
          → transport (λ r → (a₂ , r) ≡₀ center′) (paste (proj y) (proj loop) (proj p))
              (path-trace (proj $ y ∘ loop) (proj p))
          ≡ path-trace (proj y) (proj $ loop ∘ p)
        path-paste′ y loop refl =
          transport (λ r → (a , r) ≡₀ center′) (paste (proj y) (proj loop) refl₀)
            (proj $ Σ-eq (! (y ∘ loop)) (path-trace-fiber (y ∘ loop) refl))
              ≡⟨ trans-fiber≡cst-proj-Σ-eq A fiber a center′
                    (paste (proj y) (proj loop) refl₀)
                    (! (y ∘ loop)) (path-trace-fiber (y ∘ loop) refl) ⟩
          proj (Σ-eq (! (y ∘ loop)) _)
              ≡⟨ ap proj $
                  ap2 (λ p q → Σ-eq p q)
                    (! (y ∘ loop)
                      ≡⟨ opposite-concat y loop ⟩
                    ! loop ∘ ! y
                      ≡⟨ ap (λ x → ! x ∘ ! y) $ ! $ refl-right-unit loop ⟩∎
                    ! (loop ∘ refl) ∘ ! y
                      ∎)
                    (prop-has-all-paths (ribbon-is-set a _ _) _ _) ⟩∎
          proj (Σ-eq (! (loop ∘ refl) ∘ ! y) (path-trace-fiber y (loop ∘ refl)))
              ∎

      abstract
        path-paste : ∀ {a₂} y loop p
          → transport (λ r → (a₂ , r) ≡₀ center′) (paste y loop p)
              (path-trace (y ∘₀ loop) p)
          ≡ path-trace y (loop ∘₀ p)
        path-paste {a₂} =
          π₀-extend ⦃ λ y → Π-is-set λ loop → Π-is-set λ p → ≡-is-set $ π₀-is-set _ ⦄
            (λ y → π₀-extend ⦃ λ loop → Π-is-set λ p → ≡-is-set $ π₀-is-set _ ⦄
              (λ loop → π₀-extend ⦃ λ p → ≡-is-set $ π₀-is-set _ ⦄
                (λ p → path-paste′ y loop p)))

      path′ : (y : Σ A fiber) → proj {n = ⟨1⟩} y ≡ center
      path′ y = τ-path-equiv-path-τ-S {n = ⟨0⟩} ☆
        ribbon-rec {act = act} (π₁ y)
          (λ r → (π₁ y , r) ≡₀ center′)
          ⦃ λ r → π₀-is-set ((π₁ y , r) ≡ center′) ⦄
          path-trace
          path-paste
          (π₂ y)

      path : (y : τ ⟨1⟩ (Σ A fiber)) → y ≡ center
      path = τ-extend {n = ⟨1⟩} ⦃ λ _ → ≡-is-truncated ⟨1⟩ $ τ-is-truncated ⟨1⟩ _ ⦄ path′

  canonical-covering-is-universal : is-universal canonical-covering
  canonical-covering-is-universal = Universality.center , Universality.path

  -- The other direction:  If a covering is universal, then the fiber
  -- is equivalent to the fundamental group.
  module _ (cov : covering) (cov-is-universal : is-universal cov) where
    open covering cov
    open action (covering⇒action cov)

    -- We need a point!
    module GiveMeAPoint (center : fiber a) where

      -- Goal: fiber a <-> fundamental group

      fiber-a⇒fg : fiber a → a ≡₀ a
      fiber-a⇒fg y = ap₀ π₁ $ connected-has-all-τ-paths
        cov-is-universal (a , center) (a , y)

      fg⇒fiber-a : a ≡₀ a → fiber a
      fg⇒fiber-a = tracing cov center

      fg⇒fiber-a⇒fg : ∀ p → fiber-a⇒fg (fg⇒fiber-a p) ≡ p
      fg⇒fiber-a⇒fg = π₀-extend ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄ λ p →
        ap₀ π₁ (connected-has-all-τ-paths
          cov-is-universal (a , center) (a , transport fiber p center))
            ≡⟨ ap (ap₀ π₁)
                  $ ! $ π₂ (connected-has-connected-paths cov-is-universal _ _)
                           (proj $ Σ-eq p refl) ⟩
        ap₀ π₁ (proj $ Σ-eq p refl)
            ≡⟨ ap proj $ base-path-Σ-eq p refl ⟩∎
        proj p
            ∎

      fiber-a⇒fg⇒fiber-a : ∀ y → fg⇒fiber-a (fiber-a⇒fg y) ≡ y
      fiber-a⇒fg⇒fiber-a y = π₀-extend
        ⦃ λ p → ≡-is-set {x = tracing cov center (ap₀ π₁ p)} {y = y}
                  $ fiber-is-set a ⦄
        (λ p →
          transport fiber (base-path p) center
            ≡⟨ trans-base-path p ⟩∎
          y
            ∎)
        (connected-has-all-τ-paths cov-is-universal (a , center) (a , y))

      fiber-a≃fg : fiber a ≃ (a ≡₀ a)
      fiber-a≃fg = fiber-a⇒fg , iso-is-eq _ fg⇒fiber-a
        fg⇒fiber-a⇒fg fiber-a⇒fg⇒fiber-a

    -- This is the best we can obtain, because there is no continuous
    -- choice of the center.
    [center] : [ fiber a ]
    [center] = τ-extend-nondep
      ⦃ prop-is-gpd []-is-prop ⦄
      (λ y → []-extend-nondep
        ⦃ []-is-prop ⦄
        (proj ◯ λ p → transport fiber p (π₂ y))
        (connected-has-all-τ-paths A⋆-is-conn (π₁ y) a))
      (π₁ cov-is-universal)

    -- [ isomorphism between the fiber and the fundamental group ]
    -- This is the best we can obtain, because there is no continuous
    -- choice of the center.
    [fiber-a≃fg] : [ fiber a ≃ (a ≡₀ a) ]
    [fiber-a≃fg] = []-extend-nondep ⦃ []-is-prop ⦄
      (proj ◯ GiveMeAPoint.fiber-a≃fg) [center]
