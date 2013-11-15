{-# OPTIONS --without-K #-}

{- ConnectednessAlt and the last submodule of Connection are the
   only modules importing real truncation types from the library.
   Except for that, Univalence is the only additional assumption
   to Agda MLTT we work with. -}
module Universe.index where

{- General utility funcions and type constructors for
   the pseudo-universe of types of fixed truncation level. -}
import Universe.Utility.General
import Universe.Utility.TruncUniverse

{- Pointed types.
   Corresponds to section 3 plus the first lemma of section 4,
   which used in multiple modules and thus belong here. -}
import Universe.Utility.Pointed

{- Homotopically complicated types.
   Corresponds to section 4 sans the initial lemma.
   Concludes with the main theorem that the n-types
   in the n-th universe from a strict n-type.
   Hierarchy and Trunc.* are mutually independent. -}
import Universe.Hierarchy

{- Connectedness constructions
   Corresponds to section 5.
   The first three modules develop a framework of
   truncations internal to MLTT+Univalence without truncations.
   Connection contains the main result of section 5.
   ConnectednessAlt is independent from the first four modules
   and presents a provably equivalent definition of n-connectedness
   using only propositional truncation (as remarked in the article
   and mentioned in an exercise in the HoTT book). -}
import Universe.Trunc.Universal
import Universe.Trunc.Basics
import Universe.Trunc.TypeConstructors
import Universe.Trunc.Connection
import Universe.Trunc.ConnectednessAlt
