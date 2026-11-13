/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public meta import Lean.Elab.Deriving.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Deriving category-level properties along equivalences and adjunctions

This file installs deriving handlers so that properties of categories and functors which are
invariant under equivalence, or which follow from an adjunction, can be transported with
`deriving instance`.

## Along equivalences

Suppose `Foo` is a structure (or other inductive type) with a `Category` instance, and there is an
equivalence `e : Foo ≌ D` (or `e : D ≌ Foo`). Then
```
deriving instance HasLimits, HasPullbacks, HasFiniteColimits for Foo
```
creates instances `HasLimits Foo`, `HasPullbacks Foo` and `HasFiniteColimits Foo`, transported
from the corresponding instances for `D`. This works for any property which is invariant under
equivalence and is registered below (see `equivalenceLemmas`), such as `HasLimitsOfShape`,
`HasColimitsOfSize`, `IsFiltered`, `EssentiallySmall`, `WellPowered`, `EnoughProjectives`, ...

The equivalence is looked for among the declarations in the namespace `Foo` and the declarations
of the current file.

Parameters are handled as follows:
* parameters of the equivalence (e.g. `R` in `Foo.equiv (R : Type u) [Ring R] : Foo R ≌ Bar R`)
  become parameters of the instance;
* parameters of the class other than the category (e.g. the shape `J` in `HasLimitsOfShape J C`,
  or the universes in `HasLimitsOfSize.{w, w'} C`) become parameters of the instance;
* if the transported property for `D` cannot be found by instance search and it depends on one of
  these parameters, it becomes a hypothesis of the instance. For example
  `deriving instance HasLimitsOfShape for Foo` produces
  `instance {J} [Category J] [HasLimitsOfShape J D] : HasLimitsOfShape J Foo`.

## Along adjunctions

Likewise, if `adj : L ⊣ R` is an adjunction involving the category `Foo` (as the source or the
target of `L`), declared in the namespace `Foo` or in the current file, then
```
deriving instance PreservesLimits, PreservesColimitsOfShape, ReflectsLimits, CreatesLimits for Foo
```
creates, for each such adjunction, the corresponding instances: the classes about limits are
derived for the right adjoint `R`, and the classes about colimits for the left adjoint `L`.
For example, if `adj : free ⊣ forget Foo` then `deriving instance PreservesLimits for Foo`
produces `PreservesLimits (forget Foo)`, and `deriving instance PreservesColimits for Foo`
produces `PreservesColimits free`.

* `Preserves(Co)Limit(s)(OfShape/OfSize)` follow from `L` being a left adjoint or `R` being a right
  adjoint.
* `Reflects(Co)Limit(s)(OfShape/OfSize)` additionally use that the functor reflects isomorphisms
  and that its source has the relevant (co)limits.
* `Creates(Co)Limit(s)(OfShape/OfSize)` use either monadicity (resp. comonadicity) or, as for
  `Reflects`, that the functor reflects isomorphisms and that its source has the relevant
  (co)limits.

As above, missing hypotheses that depend on the shape or on the universe parameters become
hypotheses of the derived instance (e.g. `deriving instance ReflectsLimitsOfShape for Foo` produces
`instance {J} [Category J] [HasLimitsOfShape J Foo] : ReflectsLimitsOfShape J (forget Foo)`),
while other missing hypotheses (such as `(forget Foo).ReflectsIsomorphisms`) are errors.

## Limitations

* Lean only runs deriving handlers when the target of `deriving instance ... for T` is not a
  definition: if `T` is a `def`, Lean uses "delta deriving" instead, which unfolds `T`. So this is
  meant for categories defined as structures (e.g. one-field structures wrapping another
  category), which is the intended use case.
* Only `Prop`-valued properties are transported along equivalences, since they are the ones
  which do not cause definitional equality issues. (The `Creates` classes are data, but there is
  no definitional equality to preserve there in practice.)
-/

public meta section

namespace Mathlib.Deriving.CategoryTransport

open Lean Elab Command Term Meta

/-- What kind of declaration a deriving handler looks for. -/
inductive WitnessKind where
  /-- An equivalence of categories `C ≌ D`. -/
  | equivalence
  /-- An adjunction `L ⊣ R`. -/
  | adjunction
  deriving Inhabited

/-- Lemmas used to transport a class along an equivalence of categories, keyed by the class.

Each lemma must have conclusion either the class (applied to a category `C`), or an `Iff` with the
class on one side. The remaining explicit/implicit hypotheses whose type is an equivalence or a
functor are filled in with the equivalence (or its inverse, functor or inverse functor),
and instance hypotheses are found by instance search. -/
def equivalenceLemmas : List (Name × Array Name) := [
  (`CategoryTheory.Limits.HasLimitsOfShape,
    #[`CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence]),
  (`CategoryTheory.Limits.HasColimitsOfShape,
    #[`CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence]),
  (`CategoryTheory.Limits.HasLimitsOfSize,
    #[`CategoryTheory.Adjunction.has_limits_of_equivalence]),
  (`CategoryTheory.Limits.HasColimitsOfSize,
    #[`CategoryTheory.Adjunction.has_colimits_of_equivalence]),
  (`CategoryTheory.Limits.HasStrongEpiMonoFactorisations,
    #[`CategoryTheory.Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence]),
  (`CategoryTheory.IsFiltered, #[`CategoryTheory.IsFiltered.of_equivalence]),
  (`CategoryTheory.IsCofiltered, #[`CategoryTheory.IsCofiltered.of_equivalence]),
  (`CategoryTheory.IsFilteredOrEmpty, #[`CategoryTheory.IsFilteredOrEmpty.of_equivalence]),
  (`CategoryTheory.IsCofilteredOrEmpty, #[`CategoryTheory.IsCofilteredOrEmpty.of_equivalence]),
  (`CategoryTheory.IsConnected, #[`CategoryTheory.isConnected_of_equivalent]),
  (`CategoryTheory.IsPreconnected, #[`CategoryTheory.isPreconnected_of_equivalent]),
  (`CategoryTheory.IsSifted, #[`CategoryTheory.IsSifted.isSifted_of_equiv]),
  (`CategoryTheory.EssentiallySmall, #[`CategoryTheory.essentiallySmall_congr]),
  (`CategoryTheory.LocallySmall, #[`CategoryTheory.locallySmall_congr]),
  (`CategoryTheory.WellPowered, #[`CategoryTheory.wellPowered_of_equiv]),
  (`CategoryTheory.IsIdempotentComplete,
    #[`CategoryTheory.Idempotents.isIdempotentComplete_iff_of_equivalence]),
  (`CategoryTheory.EnoughProjectives, #[`CategoryTheory.Equivalence.enoughProjectives_iff]),
  (`CategoryTheory.EnoughInjectives, #[`CategoryTheory.EnoughInjectives.of_equivalence]),
  (`CategoryTheory.Balanced, #[`CategoryTheory.Functor.balanced_of_preserves]),
  (`CategoryTheory.HasSeparator, #[`CategoryTheory.HasSeparator.of_equivalence]),
  (`CategoryTheory.HasCoseparator, #[`CategoryTheory.HasCoseparator.of_equivalence])]

/-- Classes for which a deriving handler transporting along an equivalence is registered.

Abbreviations (such as `HasPullbacks`) and classes which are structures whose fields are
transportable (such as `HasFiniteLimits`) do not need an entry in `equivalenceLemmas`. -/
def equivalenceClasses : Array Name :=
  (equivalenceLemmas.map (·.1)).toArray ++ #[
  `CategoryTheory.Limits.HasLimits,
  `CategoryTheory.Limits.HasColimits,
  `CategoryTheory.Limits.HasFiniteLimits,
  `CategoryTheory.Limits.HasFiniteColimits,
  `CategoryTheory.Limits.HasProductsOfShape,
  `CategoryTheory.Limits.HasCoproductsOfShape,
  `CategoryTheory.Limits.HasProducts,
  `CategoryTheory.Limits.HasCoproducts,
  `CategoryTheory.Limits.HasFiniteProducts,
  `CategoryTheory.Limits.HasFiniteCoproducts,
  `CategoryTheory.Limits.HasBinaryProducts,
  `CategoryTheory.Limits.HasBinaryCoproducts,
  `CategoryTheory.Limits.HasTerminal,
  `CategoryTheory.Limits.HasInitial,
  `CategoryTheory.Limits.HasPullbacks,
  `CategoryTheory.Limits.HasPushouts,
  `CategoryTheory.Limits.HasEqualizers,
  `CategoryTheory.Limits.HasCoequalizers,
  `CategoryTheory.Limits.HasWidePullbacks,
  `CategoryTheory.Limits.HasWidePushouts,
  `CategoryTheory.Limits.HasFiniteWidePullbacks,
  `CategoryTheory.Limits.HasFiniteWidePushouts,
  `CategoryTheory.Limits.HasFilteredColimitsOfSize,
  `CategoryTheory.Limits.HasFilteredColimits,
  `CategoryTheory.Limits.HasCofilteredLimitsOfSize,
  `CategoryTheory.Limits.HasCofilteredLimits]

/-- Lemmas used to prove a class given an adjunction, keyed by the class.

Before these are tried, the left (resp. right) adjoint of the adjunction is registered as a local
instance of `Functor.IsLeftAdjoint` (resp. `Functor.IsRightAdjoint`), so that classes which follow
from these (such as `PreservesLimitsOfShape`) are found by instance search. -/
def adjunctionLemmas : List (Name × Array Name) := [
  (`CategoryTheory.Limits.ReflectsLimit,
    #[`CategoryTheory.Limits.reflectsLimit_of_reflectsIsomorphisms]),
  (`CategoryTheory.Limits.ReflectsColimit,
    #[`CategoryTheory.Limits.reflectsColimit_of_reflectsIsomorphisms]),
  (`CategoryTheory.Limits.ReflectsLimitsOfShape,
    #[`CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms]),
  (`CategoryTheory.Limits.ReflectsColimitsOfShape,
    #[`CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms]),
  (`CategoryTheory.Limits.ReflectsLimitsOfSize,
    #[`CategoryTheory.Limits.reflectsLimits_of_reflectsIsomorphisms]),
  (`CategoryTheory.Limits.ReflectsColimitsOfSize,
    #[`CategoryTheory.Limits.reflectsColimits_of_reflectsIsomorphisms]),
  (`CategoryTheory.CreatesLimit,
    #[`CategoryTheory.createsLimitOfReflectsIsomorphismsOfPreserves]),
  (`CategoryTheory.CreatesColimit,
    #[`CategoryTheory.createsColimitOfReflectsIsomorphismsOfPreserves]),
  (`CategoryTheory.CreatesLimitsOfShape,
    #[`CategoryTheory.createsLimitsOfShapeOfReflectsIsomorphismsOfPreserves]),
  (`CategoryTheory.CreatesColimitsOfShape,
    #[`CategoryTheory.createsColimitsOfShapeOfReflectsIsomorphismsOfPreserves]),
  (`CategoryTheory.CreatesLimitsOfSize,
    #[`CategoryTheory.monadicCreatesLimits,
      `CategoryTheory.createsLimitsOfReflectsIsomorphismsOfPreserves]),
  (`CategoryTheory.CreatesColimitsOfSize,
    #[`CategoryTheory.comonadicCreatesColimits,
      `CategoryTheory.createsColimitsOfReflectsIsomorphismsOfPreserves])]

/-- Classes for which a deriving handler using an adjunction is registered, together with whether
they are derived for the left adjoint (`true`, for colimits) or the right adjoint (`false`, for
limits). -/
def adjunctionClasses : Array (Name × Bool) :=
  (limitClasses.map (·, false)) ++ (colimitClasses.map (·, true))
where
  /-- The classes derived for right adjoints. -/
  limitClasses : Array Name := #[
    `CategoryTheory.Limits.PreservesLimit,
    `CategoryTheory.Limits.PreservesLimitsOfShape,
    `CategoryTheory.Limits.PreservesLimitsOfSize,
    `CategoryTheory.Limits.PreservesLimits,
    `CategoryTheory.Limits.PreservesFiniteLimits,
    `CategoryTheory.Limits.PreservesFiniteProducts,
    `CategoryTheory.Limits.ReflectsLimit,
    `CategoryTheory.Limits.ReflectsLimitsOfShape,
    `CategoryTheory.Limits.ReflectsLimitsOfSize,
    `CategoryTheory.Limits.ReflectsLimits,
    `CategoryTheory.CreatesLimit,
    `CategoryTheory.CreatesLimitsOfShape,
    `CategoryTheory.CreatesLimitsOfSize,
    `CategoryTheory.CreatesLimits]
  /-- The classes derived for left adjoints. -/
  colimitClasses : Array Name := #[
    `CategoryTheory.Limits.PreservesColimit,
    `CategoryTheory.Limits.PreservesColimitsOfShape,
    `CategoryTheory.Limits.PreservesColimitsOfSize,
    `CategoryTheory.Limits.PreservesColimits,
    `CategoryTheory.Limits.PreservesFiniteColimits,
    `CategoryTheory.Limits.PreservesFiniteCoproducts,
    `CategoryTheory.Limits.ReflectsColimit,
    `CategoryTheory.Limits.ReflectsColimitsOfShape,
    `CategoryTheory.Limits.ReflectsColimitsOfSize,
    `CategoryTheory.Limits.ReflectsColimits,
    `CategoryTheory.CreatesColimit,
    `CategoryTheory.CreatesColimitsOfShape,
    `CategoryTheory.CreatesColimitsOfSize,
    `CategoryTheory.CreatesColimits]

/-! ### The proof search -/

/-- Context for `solve`. -/
structure Ctx where
  /-- Terms used to fill in hypotheses of lemmas whose type is a functor, an equivalence or an
  adjunction. -/
  witnesses : Array Expr
  /-- The lemmas to use, keyed by the head symbol of the goal. -/
  lemmas : List (Name × Array Name)
  /-- Whether instance hypotheses of lemmas which cannot be synthesized may be recorded as
  hypotheses of the derived instance. -/
  allowAbstract : Bool
  /-- The free variables which an abstracted hypothesis may depend on. -/
  outer : FVarIdSet
  /-- An abstracted hypothesis must depend on one of these free variables or universe levels. -/
  triggerFVars : FVarIdSet
  /-- See `triggerFVars`. -/
  triggerLevels : Array Name

/-- State for `solve`: the hypotheses recorded so far. -/
structure State where
  /-- The types of the hypotheses to add to the derived instance. -/
  hyps : Array Expr := #[]

/-- The monad for `solve`. -/
abbrev SolveM := ReaderT Ctx <| StateRefT State MetaM

/-- Instance search, returning `none` on failure (including exceptions). -/
def trySynth (ty : Expr) : MetaM (Option Expr) := do
  try synthInstance? ty catch _ => return none

/-- Whether `ty` may become a hypothesis of the derived instance, according to `ctx`. -/
def isAbstractable (ctx : Ctx) (ty : Expr) (allowAll := false) : MetaM Bool := do
  let ty ← instantiateMVars ty
  if ty.hasMVar || ty.hasLooseBVars then return false
  if ty.hasAnyFVar (!ctx.outer.contains ·) then return false
  let newLevel := (collectLevelParams {} ty).params.any ctx.triggerLevels.contains
  -- With `allowAll`, any hypothesis depending on a local variable may be abstracted.
  if allowAll then return ty.hasFVar || newLevel
  return ty.hasAnyFVar ctx.triggerFVars.contains || newLevel

/-- Find an instance of `ty`, or (if allowed) record it as a hypothesis of the derived instance
and return a placeholder. -/
def synthOrAbstract (ty : Expr) : SolveM Expr := do
  let ty ← instantiateMVars ty
  if let some p ← trySynth ty then return p
  let ctx ← read
  if ctx.allowAbstract && (← isAbstractable ctx ty) then
    unless (← get).hyps.contains ty do
      modify fun s => { s with hyps := s.hyps.push ty }
    return ← mkSorry ty false
  throwError "failed to synthesize{indentExpr ty}"

/-- Whether `ty` is the type of a functor, an equivalence or an adjunction. -/
def isWitnessType (ty : Expr) : Bool :=
  ty.isAppOf ``CategoryTheory.Functor || ty.isAppOf ``CategoryTheory.Equivalence ||
    ty.isAppOf ``CategoryTheory.Adjunction

mutual

/-- Try to prove `goal` using the lemma `lem`. -/
partial def tryLemma (lem : Name) (goal : Expr) : SolveM (Option Expr) := do
  unless (← getEnv).contains lem do return none
  let saved ← liftMetaM saveState
  let st ← get
  try
    let c ← mkConstWithFreshMVarLevels lem
    let (args, bis, concl) ← forallMetaTelescope (← inferType c)
    -- For an `Iff` lemma, the side of the `Iff` which we need to provide, and whether this is
    -- the right-hand side.
    let mut other : Option (Expr × Bool) := none
    if concl.isAppOfArity ``Iff 2 then
      if ← isDefEq goal concl.appFn!.appArg! then
        other := some (concl.appArg!, true)
      else if ← isDefEq goal concl.appArg! then
        other := some (concl.appFn!.appArg!, false)
      else
        failure
    else
      unless ← isDefEq goal concl do failure
    for a in args, bi in bis do
      if bi.isInstImplicit || (← a.mvarId!.isAssigned) then continue
      let ty ← whnfR (← instantiateMVars (← inferType a))
      unless isWitnessType ty do continue
      for w in (← read).witnesses do
        if ← isDefEq a w then break
    for a in args, bi in bis do
      if bi.isInstImplicit && !(← a.mvarId!.isAssigned) then
        a.mvarId!.assign (← synthOrAbstract (← inferType a))
    for a in args do
      unless ← a.mvarId!.isAssigned do failure
    let mut p := mkAppN c args
    if let some (ty, isRight) := other then
      let q ← synthOrAbstract ty
      p ← mkAppM (if isRight then ``Iff.mpr else ``Iff.mp) #[p, q]
    let proof ← instantiateMVars p
    if proof.hasExprMVar then failure
    return some proof
  catch _ =>
    liftMetaM saved.restore
    set st
    return none

/-- Try to prove the class `goal` by applying its constructor (if it is a structure) and proving
each field. -/
partial def tryCtor (goal : Expr) (fuel : Nat) : SolveM (Option Expr) := do
  let .const n us := goal.getAppFn | return none
  let env ← getEnv
  unless isStructure env n && (← isClass? goal).isSome do return none
  let ctor := getStructureCtor env n
  let params := goal.getAppArgs
  unless params.size == ctor.numParams do return none
  let saved ← liftMetaM saveState
  let st ← get
  try
    let mut e := mkAppN (mkConst ctor.name us) params
    let mut ty ← instantiateForall (← instantiateTypeLevelParams ctor.toConstantVal us) params
    for _ in [:ctor.numFields] do
      let .forallE _ d b _ ← whnf ty | failure
      let p ← solve d.consumeTypeAnnotations fuel
      e := mkApp e p
      ty := b.instantiate1 p
    return some e
  catch _ =>
    liftMetaM saved.restore
    set st
    return none

/-- Prove `goal`, using instance search, the lemmas in the context, unfolding reducible
definitions, introducing universally quantified variables and applying constructors. -/
partial def solve (goal : Expr) (fuel : Nat := 8) : SolveM Expr := do
  if fuel = 0 then throwError "maximum recursion depth reached"
  let goal ← instantiateMVars goal
  if (← isClass? goal).isSome then
    if let some p ← trySynth goal then return p
  let mut g := goal
  repeat
    if let .const n _ := g.getAppFn then
      for lem in (((← read).lemmas.lookup n).getD #[]) do
        if let some p ← tryLemma lem g then return p
    let g' ← whnfR g
    if g' == g then break
    g := g'
  if g.isForall then
    return ← forallTelescope g fun xs b => do mkLambdaFVars xs (← solve b (fuel - 1))
  if let some p ← tryCtor g (fuel - 1) then return p
  throwError "failed to prove{indentExpr goal}"

end

/-- Introduce local declarations with the given types as instance-implicit hypotheses. -/
def withInstHyps {α} (tys : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  go 0 #[]
where
  /-- Implementation of `withInstHyps`. -/
  go (i : Nat) (xs : Array Expr) : MetaM α := do
    if h : i < tys.size then
      withLocalDecl `inst .instImplicit tys[i] fun x => go (i + 1) (xs.push x)
    else k xs

/-- Run `solve` on `goal`, first recording the hypotheses which are needed and then running it
again with these hypotheses as local instances. Calls `k` with the hypotheses and the proof. -/
def solveWithHyps {α} (ctx : Ctx) (goal : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let (p, st) ← (solve goal |>.run ctx).run {}
  if st.hyps.isEmpty then return ← k #[] p
  withInstHyps st.hyps fun hyps => do
    k hyps (← (solve goal |>.run { ctx with allowAbstract := false }).run' {})

/-! ### Building the instance -/

/-- The level metavariables occurring in `l`. -/
def levelMVars (l : Level) (acc : Array LMVarId := #[]) : Array LMVarId :=
  match l with
  | .mvar id => if acc.contains id then acc else acc.push id
  | .succ l => levelMVars l acc
  | .max l₁ l₂ | .imax l₁ l₂ => levelMVars l₂ (levelMVars l₁ acc)
  | _ => acc

/-- Elaborate the class `cls` with its last explicit argument (the "subject") set to `subject`.

The remaining universe levels become new universe parameters, avoiding the names in `avoid`, and
the remaining arguments become local variables (instance-implicit arguments after the subject
are synthesized if possible). Calls `k` with the new local variables, the new universe parameters,
the arguments of the class, the index of the subject and the elaborated class. -/
def withClassGoal {α} (cls : Name) (subject : Expr) (avoid : List Name)
    (k : Array Expr → Array Name → Array Expr → Nat → Expr → MetaM α) : MetaM α := do
  let c ← mkConstWithFreshMVarLevels cls
  let (ms, bis, _) ← forallMetaTelescopeReducing (← inferType c)
  let some idx := (List.range ms.size).reverse.find? (bis[·]!.isExplicit)
    | throwError "`{.ofConstName cls}` has no explicit arguments"
  unless ← isDefEq ms[idx]! subject do
    throwError "cannot apply `{.ofConstName cls}` to{indentExpr subject}"
  -- The `Category` instance on the subject determines its morphism universe.
  for i in [idx + 1:ms.size] do
    let ty ← instantiateMVars (← inferType ms[i]!)
    if bis[i]!.isInstImplicit && ty.isAppOf ``CategoryTheory.Category && !ty.hasExprMVar then
      if let some p ← trySynth ty then
        ms[i]!.mvarId!.assign p
  -- Turn the remaining universe level metavariables into universe parameters.
  let mut newLevels := #[]
  let mut n := 1
  for u in c.constLevels! do
    for id in levelMVars (← instantiateLevelMVars u) do
      unless ← isLevelMVarAssigned id do
        let mut name := Name.mkSimple s!"w_{n}"
        while avoid.contains name do
          n := n + 1
          name := Name.mkSimple s!"w_{n}"
        n := n + 1
        assignLevelMVar id (.param name)
        newLevels := newLevels.push name
  let rec go (i : Nat) (params : Array Expr) : MetaM α := do
    if h : i < ms.size then
      let m := ms[i]
      if ← m.mvarId!.isAssigned then return ← go (i + 1) params
      let ty ← instantiateMVars (← inferType m)
      let bi := if bis[i]!.isInstImplicit then .instImplicit else .implicit
      if i > idx && bis[i]!.isInstImplicit then
        if let some p ← trySynth ty then
          m.mvarId!.assign p
          return ← go (i + 1) params
      if i > idx then
        -- An instance argument after the subject which could not be synthesized: it must
        -- depend on the new parameters.
        unless ty.hasAnyFVar (fun f => params.contains (.fvar f)) ||
            (collectLevelParams {} ty).params.any newLevels.contains do
          throwError "failed to synthesize{indentExpr ty}"
      withLocalDecl (← m.mvarId!.getDecl).userName bi ty fun x => do
        m.mvarId!.assign x
        go (i + 1) (params.push x)
    else
      let args ← ms.mapM instantiateMVars
      k params newLevels args idx (mkAppN (← instantiateMVars c) args)
  go 0 #[]

/-- Rebuild the class application `@cls args` with the subject (at index `idx`) replaced by
`subject`. Instance-implicit arguments after the subject are re-synthesized when possible;
the types of those which cannot be synthesized are returned in the first component, together with
the corresponding free variables passed to `k`. -/
def withSubjectReplaced {α} (c : Expr) (args : Array Expr) (idx : Nat) (subject : Expr)
    (k : Array Expr → Array Expr → Expr → MetaM α) : MetaM α := do
  let rec go (i : Nat) (ty : Expr) (acc : Array Expr) (hyps hypTys : Array Expr) :
      MetaM α := do
    if h : i < args.size then
      let .forallE n d b bi ← whnf ty | throwError "unexpected class type"
      if i == idx then
        go (i + 1) (b.instantiate1 subject) (acc.push subject) hyps hypTys
      else if i > idx && bi.isInstImplicit then
        if let some p ← trySynth d then
          go (i + 1) (b.instantiate1 p) (acc.push p) hyps hypTys
        else
          withLocalDecl n .instImplicit d fun x =>
            go (i + 1) (b.instantiate1 x) (acc.push x) (hyps.push x) (hypTys.push d)
      else
        go (i + 1) (b.instantiate1 args[i]) (acc.push args[i]) hyps hypTys
    else
      k hyps hypTys (mkAppN c acc)
  go 0 (← inferType c) #[] #[] #[]

/-- The type, value and universe parameters of the instance `∀ binders, goal` with proof `proof`.
Explicit binders are made implicit. The universe parameters are those of `baseLevels` which occur,
followed by those in `newLevels`, renamed to `w_1, w_2, ...` in order of occurrence. -/
def mkInstance (binders : Array Expr) (goal proof : Expr) (baseLevels : List Name)
    (newLevels : Array Name) :
    MetaM (Expr × Expr × List Name) := do
  let bis ← binders.filterMapM fun x => do
    let decl ← x.fvarId!.getDecl
    return if decl.binderInfo.isExplicit then some (x.fvarId!, BinderInfo.implicit) else none
  let (type, value) ← withNewBinderInfos bis do
    return (← mkForallFVars binders goal, ← mkLambdaFVars binders proof)
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar then
    throwError "the derived instance contains metavariables:{indentExpr type}"
  let occurring := (collectLevelParams (collectLevelParams {} type) value).params
  let fresh := occurring.filter newLevels.contains
  let mut renamed := #[]
  let mut i := 1
  while renamed.size < fresh.size do
    let n := Name.mkSimple s!"w_{i}"
    i := i + 1
    unless occurring.contains n && !fresh.contains n do renamed := renamed.push n
  let subst (e : Expr) := e.instantiateLevelParams fresh.toList (renamed.toList.map .param)
  let rename (n : Name) := (fresh.idxOf? n).elim n (renamed[·]!)
  let levels := baseLevels.filter occurring.contains ++
    (occurring.filter (!baseLevels.contains ·)).toList.map rename
  return (subst type, subst value, levels)

/-- Add the instance with the given type, value and universe parameters, returning its name. -/
def addInstanceDecl (type value : Expr) (levelParams : List Name) : TermElabM Name := do
  let mut name := (← getCurrNamespace) ++ (← NameGen.mkBaseNameWithSuffix "inst" type)
  name ← liftMacroM <| mkUnusedBaseName name
  if ← isProp type then
    addDecl (← mkThmOrUnsafeDef { name, levelParams, type, value })
    addInstance name .global (eval_prio default)
  else
    let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
    addDecl <| .defnDecl
      (← mkDefinitionValInferringUnsafe name levelParams type value hints)
    modifyEnv (addNoncomputable · name)
    registerInstance name .global (eval_prio default)
  addDeclarationRangesFromSyntax name (← getRef)
  return name

/-- Check that every non-instance binder occurs in the type of the instance, so that it can be
determined by unification. -/
def checkDetermined (binders : Array Expr) (goal : Expr) : MetaM Unit := do
  let mut ty := goal
  for x in binders.reverse do
    let decl ← x.fvarId!.getDecl
    unless decl.binderInfo.isInstImplicit do
      unless ty.containsFVar x.fvarId! do
        throwError "the argument `{x}` would not be determined by the derived instance"
    ty ← mkForallFVars #[x] ty

/-! ### Looking for equivalences and adjunctions -/

/-- If `ty` is (after telescoping) an equivalence or an adjunction involving the type `T`,
return `true`. -/
def isWitnessFor (kind : WitnessKind) (T : Name) (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ b => do
    let b ← whnfR b
    let isT (e : Expr) := e.getAppFn.isConstOf T
    match kind with
    | .equivalence =>
      if b.isAppOfArity ``CategoryTheory.Equivalence 4 then
        let args := b.getAppArgs
        return isT args[0]! != isT args[1]!
      return false
    | .adjunction =>
      if b.isAppOfArity ``CategoryTheory.Adjunction 6 then
        -- The first four arguments are the two categories and their instances.
        return b.getAppArgs[:4].any isT
      return false

/-- Find the declarations in the namespace `T` or in the current module which are equivalences
or adjunctions (according to `kind`) involving `T`. -/
def findWitnesses (kind : WitnessKind) (T : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let cands := env.constants.fold (init := #[]) fun acc n ci =>
    if (privateToUserName n).isInternalDetail then acc
    else if !(ci matches .defnInfo _ || ci matches .opaqueInfo _) then acc
    else if (T.isPrefixOf n && n != T) || (env.getModuleIdxFor? n).isNone then acc.push n
    else acc
  let cands := cands.qsort (fun a b =>
    (T.isPrefixOf a && !T.isPrefixOf b) ||
      (T.isPrefixOf a == T.isPrefixOf b && a.toString < b.toString))
  cands.filterM fun n => do
    try isWitnessFor kind T (← getConstInfo n).type catch _ => return false

/-! ### The deriving handlers -/

/-- Derive the class `cls` for the category `T` from the equivalence `wName`. -/
def deriveFromEquivalence (cls T wName : Name) : TermElabM (Option Name) := do
  let some (type, value, levelParams) ← go | return none
  addInstanceDecl type value levelParams
where
  /-- Compute the type, value and universe parameters of the instance, or return `none` if the
  instance already exists. -/
  go : MetaM (Option (Expr × Expr × List Name)) := do
    let info ← getConstInfo wName
    let w ← mkConstWithLevelParams wName
    forallTelescopeReducing info.type fun xs wTy => do
      let wTy ← whnfR wTy
      let w := mkAppN w xs
      let args := wTy.getAppArgs
      let (e, D) ← if args[0]!.getAppFn.isConstOf T then pure (w, args[1]!)
        else pure (← mkAppM ``CategoryTheory.Equivalence.symm #[w], args[0]!)
      let C := (← whnfR (← inferType e)).getAppArgs[0]!
      let witnesses := #[e, ← mkAppM ``CategoryTheory.Equivalence.symm #[e],
        ← mkAppM ``CategoryTheory.Equivalence.functor #[e],
        ← mkAppM ``CategoryTheory.Equivalence.inverse #[e]]
      withClassGoal cls C info.levelParams fun params newLevels clsArgs idx goal => do
        if (← trySynth goal).isSome then return none
        let c := goal.getAppFn
        -- The class for `D`, and the instance arguments it needs.
        withSubjectReplaced c clsArgs idx D fun hyps hypTys goalD => do
          let ctx₀ : Ctx := {
            witnesses, lemmas := equivalenceLemmas, allowAbstract := true,
            outer := (xs ++ params ++ hyps).foldl (·.insert ·.fvarId!) {},
            triggerFVars := (params ++ hyps).foldl (·.insert ·.fvarId!) {},
            triggerLevels := newLevels }
          for ty in hypTys do
            unless ← isAbstractable ctx₀ ty (allowAll := true) do
              throwError "failed to synthesize{indentExpr ty}"
          let some _ ← trySynth goalD | do
            unless ← isAbstractable ctx₀ goalD (allowAll := true) do
              throwError "failed to synthesize{indentExpr goalD}"
            withLocalDecl `inst .instImplicit goalD fun h => do
              let hyps := hyps.push h
              let ctx := { ctx₀ with outer := ctx₀.outer.insert h.fvarId! }
              solveWithHyps ctx goal fun hyps' p => do
                let binders := xs ++ params ++ hyps ++ hyps'
                checkDetermined (xs ++ params) goal
                some <$> mkInstance binders goal p info.levelParams newLevels
          solveWithHyps ctx₀ goal fun hyps' p => do
            let binders := xs ++ params ++ hyps ++ hyps'
            checkDetermined (xs ++ params) goal
            some <$> mkInstance binders goal p info.levelParams newLevels

/-- Derive the class `cls` for the functor `F` (one of the functors of the adjunction `wName`),
returning the name of the new instance. -/
def deriveFromAdjunction (cls wName : Name) (useLeft : Bool) : TermElabM (Option Name) := do
  let some (type, value, levelParams) ← go | return none
  addInstanceDecl type value levelParams
where
  /-- Compute the type, value and universe parameters of the instance, or return `none` if the
  instance already exists. -/
  go : MetaM (Option (Expr × Expr × List Name)) := do
    let info ← getConstInfo wName
    let w ← mkConstWithLevelParams wName
    forallTelescopeReducing info.type fun xs wTy => do
      let wTy ← whnfR wTy
      let adj := mkAppN w xs
      let L := wTy.getAppArgs[4]!
      let R := wTy.getAppArgs[5]!
      let F := if useLeft then L else R
      withClassGoal cls F info.levelParams fun params newLevels _ _ goal => do
        if (← trySynth goal).isSome then return none
        let isLTy ← mkAppM ``CategoryTheory.Functor.IsLeftAdjoint #[L]
        let isRTy ← mkAppM ``CategoryTheory.Functor.IsRightAdjoint #[R]
        let isL ← mkAppM ``CategoryTheory.Adjunction.isLeftAdjoint #[adj]
        let isR ← mkAppM ``CategoryTheory.Adjunction.isRightAdjoint #[adj]
        withLocalDecl `instL .instImplicit isLTy fun hL =>
        withLocalDecl `instR .instImplicit isRTy fun hR => do
          let ctx : Ctx := {
            witnesses := #[adj], lemmas := adjunctionLemmas, allowAbstract := true,
            outer := (xs ++ params).foldl (·.insert ·.fvarId!) {},
            triggerFVars := params.foldl (·.insert ·.fvarId!) {},
            triggerLevels := newLevels }
          solveWithHyps ctx goal fun hyps p => do
            let p := ((← mkLambdaFVars #[hL, hR] p).beta #[isL, isR]).headBeta
            let binders := xs ++ params ++ hyps
            checkDetermined (xs ++ params) goal
            some <$> mkInstance binders goal p info.levelParams newLevels

/-- Derive `cls` for `T` along the first equivalence for which this works. -/
def deriveAlongEquivalence (cls T : Name) : TermElabM Unit := do
  let ws ← findWitnesses .equivalence T
  if ws.isEmpty then
    throwError "could not find an equivalence `{.ofConstName T} ≌ _` or `_ ≌ {.ofConstName T}` \
      in the namespace `{privateToUserName T}` or in the current file"
  let mut errors : Array MessageData := #[]
  for wName in ws do
    let saved ← saveState
    try
      if (← deriveFromEquivalence cls T wName).isNone then
        logWarning m!"`{.ofConstName T}` already has a `{.ofConstName cls}` instance; \
          nothing to derive"
      return
    catch ex =>
      errors := errors.push m!"using `{.ofConstName wName}`: {ex.toMessageData}"
      saved.restore
  throwError "failed to derive `{.ofConstName cls}` for `{.ofConstName T}` along an \
    equivalence:{indentD <| MessageData.joinSep errors.toList "\n"}"

/-- Derive `cls` for the left adjoints (if `useLeft`) or right adjoints (otherwise) of all
adjunctions involving `T`, whenever this works. -/
def deriveFromAdjunctions (cls T : Name) (useLeft : Bool) : TermElabM Unit := do
  let ws ← findWitnesses .adjunction T
  if ws.isEmpty then
    throwError "could not find an adjunction involving `{.ofConstName T}` in the namespace \
      `{privateToUserName T}` or in the current file"
  let side := if useLeft then "left" else "right"
  let mut errors : Array MessageData := #[]
  let mut success := false
  let mut existing := false
  for wName in ws do
    let saved ← saveState
    try
      if (← deriveFromAdjunction cls wName useLeft).isSome then
        success := true
      else
        existing := true
    catch ex =>
      errors := errors.push m!"using the {side} adjoint of `{.ofConstName wName}`: \
        {ex.toMessageData}"
      saved.restore
  if success then return
  if existing then
    logWarning m!"the {side} adjoints of the adjunctions involving `{.ofConstName T}` already \
      have `{.ofConstName cls}` instances; nothing to derive"
    return
  throwError "failed to derive `{.ofConstName cls}` for the {side} adjoint of any adjunction \
    involving `{.ofConstName T}`:{indentD <| MessageData.joinSep errors.toList "\n"}"

/-- The deriving handler for a class transported along equivalences. -/
def mkEquivalenceHandler (cls : Name) : DerivingHandler := fun declNames => do
  if declNames.size != 1 then return false
  liftTermElabM <| deriveAlongEquivalence cls declNames[0]!
  return true

/-- The deriving handler for a class obtained from adjunctions. -/
def mkAdjunctionHandler (cls : Name) (useLeft : Bool) : DerivingHandler := fun declNames => do
  if declNames.size != 1 then return false
  liftTermElabM <| deriveFromAdjunctions cls declNames[0]! useLeft
  return true

initialize
  for cls in equivalenceClasses do
    registerDerivingHandler cls (mkEquivalenceHandler cls)
  for (cls, useLeft) in adjunctionClasses do
    registerDerivingHandler cls (mkAdjunctionHandler cls useLeft)

end Mathlib.Deriving.CategoryTransport
