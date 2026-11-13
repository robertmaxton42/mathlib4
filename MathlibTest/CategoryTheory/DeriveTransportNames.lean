module

import Mathlib.Tactic.CategoryTheory.DeriveTransport
import Mathlib.CategoryTheory.Balanced
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Sifted
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Subobject.WellPowered

/-! Every class and lemma used by the `deriving` handlers in
`Mathlib.Tactic.CategoryTheory.DeriveTransport` exists. -/

open Lean Mathlib.Deriving.CategoryTransport in
run_meta do
  let env ← getEnv
  for (cls, lems) in equivalenceLemmas ++ adjunctionLemmas do
    for n in #[cls] ++ lems do
      unless env.contains n do throwError "unknown constant `{n}`"
  for n in equivalenceClasses ++ adjunctionClasses.map (·.1) do
    unless env.contains n do throwError "unknown constant `{n}`"
