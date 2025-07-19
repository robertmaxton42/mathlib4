/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/

import Mathlib.CategoryTheory.Limits.Shapes.Images.OfShape
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-! # Regular categories of a given shape

  For a cardinal κ, a κ-ary regular category is a finitely complete category in which every κ-small
  cospan factors as a strong epi cospan followed by a monomorphism. It can be shown that this
  definition summarizes a number of related standard definitions:

  * If κ = 1, we recover the definition of a regular category
  * If κ = ω, we recover the definition of a (finitary) coherent category
  * For larger cardinals, we recover the definition of increasingly infinitary coherent categories

  However, in Mathlib it is not very convenient to work with cardinals, so instead we define
  `RegularCategoryForShape` for some shape `J`, replacing the



-/

namespace CategoryTheory
open Limits

universe w v u
variable (J : Type w) (C : Type u) [Category.{v} C]

-- Technical debt marker: if we ever generalize `MorphismProperty` to families of morphisms,
-- we should use that here instead of a bespoke class.

class StrongEpiCospanOfShapeStableUnderPullback [HasPullbacks C] : Prop where
  strongEpiCospan_stable {X : J → C} {Y Z : C} (F : (i : J) → X i ⟶ Z) [StrongEpiCospan F]
    (g : Y ⟶ Z) : StrongEpiCospan (fun i ↦ pullback.snd (F i) g) := by infer_instance

class RegularCategoryForShape : Prop extends HasFiniteLimits C where
  strong_cospan_images : HasStrongEpiCospanImagesOfShape J C
  strong_cospan_stable : StrongEpiCospanOfShapeStableUnderPullback J C
