/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/
module

public import Solution

open KrohnRhodes

-- The main theorem and the structure it produces.
#check @krohn_rhodes_prime_decomposition
#print KRFactorTowerGrp

-- Expected: [propext, Classical.choice, Quot.sound] (no sorryAx).
#print axioms krohn_rhodes_prime_decomposition
