module

import Mathlib.Tactic.CategoryTheory.DeriveTransport
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Types.Monomorphisms

open CategoryTheory Limits

universe w w' v u

namespace DeriveTransportTest

/-! ## Transporting along an equivalence -/

/-- A one-field structure wrapping `Type u`. -/
structure Wrap : Type (u + 1) where
  of ::
  obj : Type u

instance : Category.{u} Wrap.{u} where
  Hom X Y := X.obj ⟶ Y.obj
  id X := 𝟙 X.obj
  comp f g := f ≫ g

/-- The equivalence with `Type u`. -/
def Wrap.equiv : Wrap.{u} ≌ Type u where
  functor := { obj X := X.obj, map f := f }
  inverse := { obj X := .of X, map f := f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

deriving instance HasLimits, HasColimits for Wrap

/-- info: DeriveTransportTest.instHasLimitsWrap.{u} : HasLimits Wrap -/
#guard_msgs in
#check instHasLimitsWrap

example : HasLimits Wrap.{u} := inferInstance
example : HasColimits Wrap.{u} := inferInstance
example : HasPullbacks Wrap.{u} := inferInstance
example : HasFiniteLimits Wrap.{u} := inferInstance
example : HasTerminal Wrap.{u} := inferInstance

-- Asking for an instance which already exists is a warning.
/-- warning: `Wrap` already has a `HasPullbacks` instance; nothing to derive -/
#guard_msgs in
deriving instance HasPullbacks for Wrap

-- Parameters of the class become parameters of the instance, with hypotheses for the target.
deriving instance HasLimitsOfShape, HasColimitsOfSize for Wrap

/--
info: DeriveTransportTest.instHasLimitsOfShapeWrapOfType.{u, w_1, w_2} {J : Type w_1} [Category.{w_2, w_1} J]
  [inst : HasLimitsOfShape J (Type u)] : HasLimitsOfShape J Wrap
-/
#guard_msgs in
#check instHasLimitsOfShapeWrapOfType

example {J : Type} [Category.{0} J] : HasLimitsOfShape J Wrap.{0} := inferInstance
example : HasColimitsOfSize.{0, 0} Wrap.{0} := inferInstance

deriving instance LocallySmall, EssentiallySmall, Balanced for Wrap

example : LocallySmall.{u} Wrap.{u} := inferInstance
example : Balanced Wrap.{u} := inferInstance

-- A closed hypothesis which cannot be found by instance search is an error.
/--
error: failed to derive `IsIdempotentComplete` for `Wrap` along an equivalence:
  using `Wrap.equiv`: failed to synthesize
    IsIdempotentComplete (Type u)
-/
#guard_msgs in
deriving instance IsIdempotentComplete for Wrap

/-! The equivalence may also go the other way. -/

/-- Another one-field structure wrapping `Type u`. -/
structure Wrap₂ : Type (u + 1) where
  of ::
  obj : Type u

instance : Category.{u} Wrap₂.{u} where
  Hom X Y := X.obj ⟶ Y.obj
  id X := 𝟙 X.obj
  comp f g := f ≫ g

/-- The equivalence from `Type u`. -/
def Wrap₂.equiv : Type u ≌ Wrap₂.{u} where
  functor := { obj X := .of X, map f := f }
  inverse := { obj X := X.obj, map f := f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

deriving instance HasFiniteLimits, HasFiniteColimits for Wrap₂

example : HasFiniteLimits Wrap₂.{u} := inferInstance
example : HasPushouts Wrap₂.{u} := inferInstance

/-! Parametrized categories. -/

/-- A one-field structure wrapping an arbitrary category. -/
structure Wrap' (C : Type u) [Category.{v} C] where
  of ::
  obj : C

instance (C : Type u) [Category.{v} C] : Category.{v} (Wrap' C) where
  Hom X Y := X.obj ⟶ Y.obj
  id X := 𝟙 X.obj
  comp f g := f ≫ g

/-- The equivalence with the wrapped category. -/
def Wrap'.equiv (C : Type u) [Category.{v} C] : Wrap' C ≌ C where
  functor := { obj X := X.obj, map f := f }
  inverse := { obj X := .of X, map f := f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

deriving instance HasLimits, HasFiniteProducts, IsFiltered for Wrap'

/--
info: DeriveTransportTest.instHasLimitsWrap'.{v, u} {C : Type u} [Category.{v, u} C] [inst : HasLimits C] :
  HasLimits (Wrap' C)
-/
#guard_msgs in
#check instHasLimitsWrap'

example : HasLimits (Wrap' (Type u)) := inferInstance
example : HasFiniteProducts (Wrap' (Type u)) := inferInstance
example (C : Type u) [Category.{v} C] [IsFiltered C] : IsFiltered (Wrap' C) := inferInstance

/-! ## Using adjunctions -/

/-- The forgetful functor. -/
def Wrap.forget : Wrap.{u} ⥤ Type u := Wrap.equiv.functor

/-- The free functor. -/
def Wrap.free : Type u ⥤ Wrap.{u} := Wrap.equiv.inverse

/-- The adjunction between them. -/
def Wrap.adj : Wrap.free.{u} ⊣ Wrap.forget := Wrap.equiv.symm.toAdjunction

deriving instance PreservesLimits, PreservesLimitsOfShape, PreservesColimitsOfSize for Wrap

example : PreservesLimits Wrap.forget.{u} := inferInstance
example : PreservesColimits Wrap.free.{u} := inferInstance
example : PreservesFiniteLimits Wrap.forget.{u} := inferInstance

/--
info: DeriveTransportTest.instPreservesLimitsOfShapeWrapForget.{u, w_1, w_2} {J : Type w_1} [Category.{w_2, w_1} J] :
  PreservesLimitsOfShape J Wrap.forget
-/
#guard_msgs in
#check instPreservesLimitsOfShapeWrapForget

/--
warning: the right adjoints of the adjunctions involving `Wrap` already have `PreservesFiniteLimits` instances; nothing to derive
-/
#guard_msgs in
deriving instance PreservesFiniteLimits for Wrap

-- `Reflects` and `Creates` need the functor to reflect isomorphisms.
/--
error: failed to derive `ReflectsLimits` for the right adjoint of any adjunction involving `Wrap`:
  using the right adjoint of `Wrap.adj`: failed to prove
    ReflectsLimits Wrap.forget
-/
#guard_msgs in
deriving instance ReflectsLimits for Wrap

instance : Wrap.forget.{u}.ReflectsIsomorphisms :=
  inferInstanceAs (Wrap.equiv.functor.ReflectsIsomorphisms)

deriving instance ReflectsLimits, ReflectsLimitsOfShape, CreatesLimits, CreatesLimitsOfShape
  for Wrap

example : ReflectsLimits Wrap.forget.{u} := inferInstance
noncomputable example : CreatesLimits Wrap.forget.{u} := inferInstance

/--
info: DeriveTransportTest.instReflectsLimitsOfShapeWrapForgetOfHasLimitsOfShape.{u, w_1, w_2} {J : Type w_1}
  [Category.{w_2, w_1} J] [inst : HasLimitsOfShape J Wrap] : ReflectsLimitsOfShape J Wrap.forget
-/
#guard_msgs in
#check instReflectsLimitsOfShapeWrapForgetOfHasLimitsOfShape

end DeriveTransportTest
