------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over booleans
------------------------------------------------------------------------

-- See README.Data.Nat for examples of how to use similar solvers

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Bool.Solver where

import Algebra.Solver.Ring.Simple as Solver using ( module ∨-∧-Solver)
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR using (AlmostCommutativeRing)
open import Data.Bool.Properties

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _∨_ and _∧_

module ∨-∧-Solver =
  Solver (ACR.fromCommutativeSemiring ∨-∧-commutativeSemiring) _≟_

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _xor_ and _∧_

module xor-∧-Solver =
  Solver (ACR.fromCommutativeRing xor-∧-commutativeRing) _≟_
