import EvmCompiler.StackFreeCfg.Compiler
import EvmCompiler.StackFreeCfg.Contract
import EvmCompiler.StackFreeCfg.PrimitiveAdapter
import EvmCompiler.TypedCfg.Contract

namespace EvmCompiler
namespace StackFreeCfg
namespace Preservation

/-!
Top-down preservation interface for the StackFreeCfg -> TypedCfg pass.

This file intentionally contains no proof bodies. It fixes the public theorem
shape before the local proof work starts, so the implementation proofs can use
stack layouts and typed labels internally without leaking them above this
adjacent boundary.
-/

abbrev SourceResult :=
  Except Exception Observation

abbrev TargetResult :=
  Except TypedCfg.EVMException TypedCfg.Outcome

/--
Initial-state relation for running a compiled whole StackFreeCfg program.

The compiled CFG entry block has empty input shape. The only source-visible
part of the target state at entry is the shared EVM/Yul state; the target stack
starts empty.
-/
structure InitialRel (shared : SharedState) (target : TypedCfg.EVMState) :
    Prop where
  shared_eq : target.toSharedState = shared
  stack_empty : target.stack = []

/--
Result relation for the adjacent compiler proof.

This relation is allowed to mention `TypedCfg` outcomes because it is exactly
the StackFreeCfg -> TypedCfg boundary. It is not exported as the observation
model for higher source layers.
-/
inductive ResultRel : SourceResult → TargetResult → Prop where
  | regular {source : Observation} {target : TypedCfg.RunState}
      (hMode : source.mode = .regular)
      (hScope : source.scope = [])
      (hShared : target.evm.toSharedState = source.shared)
      (hStack : target.evm.stack = [])
      (hReturns : target.returns = []) :
      ResultRel (.ok source) (.ok (.fallthrough target))
  | halt {source : Observation} {target : TypedCfg.RunState}
      {kind : Assembly.HaltKind}
      (hMode : source.mode = .halt kind)
      (hShared : target.evm.toSharedState = source.shared) :
      ResultRel (.ok source) (.ok (.halt kind target))
  | invalidMode {source : Observation} {target : TypedCfg.RunState}
      (hMode : source.mode = .invalid) :
      ResultRel (.ok source) (.ok (.invalid target))
  | invalidError {target : TypedCfg.RunState} :
      ResultRel (.error .invalid) (.ok (.invalid target))
  | outOfFuel {source : Observation} {label : TypedCfg.Label}
      {target : TypedCfg.RunState}
      (hMode : source.mode = .outOfFuel)
      (hShared : target.evm.toSharedState = source.shared) :
      ResultRel (.ok source) (.ok (.outOfFuel label target))
  | primitiveError {error : TypedCfg.EVMException} :
      ResultRel (.error (.primitive error)) (.error error)

namespace Internal

/-!
Internal proof vocabulary for the adjacent StackFreeCfg -> TypedCfg proof.

These definitions may mention `TypedCfg.Shape`, labels, and runtime stacks
because they live exactly at the compiler boundary that hides those details.
They should not be used by higher layers, which should target `Observation` and
`Program.CompilePreserves` above.
-/

abbrev Shape :=
  TypedCfg.Shape

abbrev Label :=
  TypedCfg.Label

def StoreScoped (scope : List Name) (vars : Store.T) : Prop :=
  ∀ name, name ∉ scope → vars name = none

namespace StoreScoped

theorem empty (scope : List Name) :
    StoreScoped scope Store.empty := by
  intro _name _hNotMem
  rfl

theorem restrictTo (scope : List Name) (vars : Store.T) :
    StoreScoped scope (Store.restrictTo scope vars) := by
  intro name hNotMem
  simp [Store.restrictTo, hNotMem]

theorem insert_of_mem {scope : List Name} {vars : Store.T}
    {name : Name} {value : Word}
    (hMem : name ∈ scope)
    (hScoped : StoreScoped scope vars) :
    StoreScoped scope (Store.insert vars name value) := by
  intro key hNotMem
  by_cases hEq : key = name
  · subst key
    exact False.elim (hNotMem hMem)
  · simp [Store.insert, hEq, hScoped key hNotMem]

theorem insertMany {scope names : List Name} {values : List Word}
    {vars vars' : Store.T}
    (hInsert : Store.insertMany names values vars = some vars')
    (hNames : ∀ name, name ∈ names → name ∈ scope)
    (hScoped : StoreScoped scope vars) :
    StoreScoped scope vars' := by
  induction names generalizing values vars with
  | nil =>
      cases values with
      | nil =>
          simp [Store.insertMany] at hInsert
          cases hInsert
          exact hScoped
      | cons _ _ =>
          simp [Store.insertMany] at hInsert
  | cons name names ih =>
      cases values with
      | nil =>
          simp [Store.insertMany] at hInsert
      | cons value values =>
          simp [Store.insertMany] at hInsert
          exact
            ih hInsert
              (fun key hMem => hNames key (List.mem_cons_of_mem name hMem))
              (insert_of_mem
                (hNames name List.mem_cons_self) hScoped)

theorem assignMany {scope names : List Name} {values : List Word}
    {vars vars' : Store.T}
    (hAssign : Store.assignMany names values vars = some vars')
    (hNames : ∀ name, name ∈ names → name ∈ scope)
    (hScoped : StoreScoped scope vars) :
    StoreScoped scope vars' := by
  induction names generalizing values vars with
  | nil =>
      cases values with
      | nil =>
          simp [Store.assignMany] at hAssign
          cases hAssign
          exact hScoped
      | cons _ _ =>
          simp [Store.assignMany] at hAssign
  | cons name names ih =>
      cases values with
      | nil =>
          simp [Store.assignMany] at hAssign
      | cons value values =>
          by_cases hContains : Store.contains vars name
          · simp [Store.assignMany, hContains] at hAssign
            exact
              ih hAssign
                (fun key hMem => hNames key (List.mem_cons_of_mem name hMem))
                (insert_of_mem
                  (hNames name List.mem_cons_self) hScoped)
          · simp [Store.assignMany, hContains] at hAssign

end StoreScoped

def SlotMatchesStore (vars : Store.T) :
    TypedCfg.Slot → Word → Prop
  | .literal expected, value =>
      (TypedCfg.Slot.literal expected).matchesValue value = true
  | .local name, value => vars name = some value
  | .word, _value => True
  | .temp _scope _index, _value => True
  | .returnPC _site, _value => True
  | .returnValue name _index, value => vars name = some value

def ShapeMatchesStore (vars : Store.T) :
    Shape → EvmYul.Stack Word → Prop
  | [], [] => True
  | slot :: shapeRest, value :: stackRest =>
      SlotMatchesStore vars slot value ∧
        ShapeMatchesStore vars shapeRest stackRest
  | _, _ => False

structure StateRel (scope : List Name) (shape : Shape)
    (source : State) (target : TypedCfg.RunState) : Prop where
  store_scoped : StoreScoped scope source.vars
  shared_eq : target.evm.toSharedState = source.shared
  stack : ShapeMatchesStore source.vars shape target.evm.stack

namespace StateRel

theorem shared_eq_of {scope : List Name} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (h : StateRel scope shape source target) :
    target.evm.toSharedState = source.shared :=
  h.shared_eq

end StateRel

namespace SlotMatchesStore

theorem matchesValue {vars : Store.T} {slot : TypedCfg.Slot} {value : Word}
    (h : SlotMatchesStore vars slot value) :
    slot.matchesValue value = true := by
  cases slot <;> simp [SlotMatchesStore, TypedCfg.Slot.matchesValue] at h ⊢
  exact h

end SlotMatchesStore

namespace ShapeMatchesStore

theorem matchesStack {vars : Store.T} {shape : Shape}
    {stack : EvmYul.Stack Word}
    (h : ShapeMatchesStore vars shape stack) :
    shape.matchesStack stack = true := by
  induction shape generalizing stack with
  | nil =>
      cases stack with
      | nil => rfl
      | cons _ _ => simp [ShapeMatchesStore] at h
  | cons slot rest ih =>
      cases stack with
      | nil =>
          simp [ShapeMatchesStore] at h
      | cons value stackRest =>
          simp [ShapeMatchesStore] at h
          simp [TypedCfg.Shape.matchesStack,
            SlotMatchesStore.matchesValue h.1, ih h.2]

end ShapeMatchesStore

namespace StateRel

theorem block_input_matches {scope : List Name} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (h : StateRel scope shape source target) :
    shape.matchesStack target.evm.stack = true :=
  ShapeMatchesStore.matchesStack h.stack

end StateRel

namespace Mode

def kont? (ctx : Compiler.Context) : Mode → Option Compiler.Kont
  | .regular => some ctx.regular
  | .brk => ctx.break?
  | .cont => ctx.continue?
  | .leave => ctx.leave?
  | .halt _ | .invalid | .outOfFuel => none

end Mode

inductive FragmentResultRel (ctx : Compiler.Context) :
    Except Exception Outcome → Except TypedCfg.EVMException TypedCfg.Outcome →
      Prop where
  | jump {source : Outcome} {target : TypedCfg.RunState}
      {kont : Compiler.Kont}
      (hKont : Mode.kont? ctx source.mode = some kont)
      (hState : StateRel source.scope kont.shape source.state target) :
      FragmentResultRel ctx (.ok source) (.ok (.jump kont.label target))
  | halt {source : Outcome} {target : TypedCfg.RunState}
      {kind : Assembly.HaltKind}
      (hMode : source.mode = .halt kind)
      (hShared : target.evm.toSharedState = source.state.shared) :
      FragmentResultRel ctx (.ok source) (.ok (.halt kind target))
  | invalidMode {source : Outcome} {target : TypedCfg.RunState}
      (hMode : source.mode = .invalid) :
      FragmentResultRel ctx (.ok source) (.ok (.invalid target))
  | invalidError {target : TypedCfg.RunState} :
      FragmentResultRel ctx (.error .invalid) (.ok (.invalid target))
  | outOfFuel {source : Outcome} {label : Label}
      {target : TypedCfg.RunState}
      (hMode : source.mode = .outOfFuel)
      (hShared : target.evm.toSharedState = source.state.shared) :
      FragmentResultRel ctx (.ok source) (.ok (.outOfFuel label target))
  | primitiveError {error : TypedCfg.EVMException} :
      FragmentResultRel ctx (.error (.primitive error)) (.error error)

def StmtSound (cfg : TypedCfg.Program) (program : Program)
    (sourceCtx : Ctx) (targetCtx : Compiler.Context)
    (stmt : Stmt) (label : Label) (shape : Shape) : Prop :=
  ∀ fuel source target,
    StateRel sourceCtx.scope shape source target →
      FragmentResultRel targetCtx
        (Stmt.run fuel PrimitiveSemantics.canonical program sourceCtx stmt
          source)
        (TypedCfg.Program.runFrom fuel cfg label target)

def SeqSound (cfg : TypedCfg.Program) (program : Program)
    (sourceCtx : Ctx) (targetCtx : Compiler.Context)
    (stmts : List Stmt) (label : Label) (shape : Shape) : Prop :=
  ∀ fuel source target,
    StateRel sourceCtx.scope shape source target →
      FragmentResultRel targetCtx
        (StmtList.run fuel PrimitiveSemantics.canonical program sourceCtx stmts
          source)
        (TypedCfg.Program.runFrom fuel cfg label target)

def BlockSound (cfg : TypedCfg.Program) (program : Program)
    (sourceCtx : Ctx) (targetCtx : Compiler.Context)
    (block : Block) (label : Label) (shape : Shape) : Prop :=
  ∀ fuel source target,
    StateRel sourceCtx.scope shape source target →
      FragmentResultRel targetCtx
        (Block.run fuel PrimitiveSemantics.canonical program sourceCtx block
          source)
        (TypedCfg.Program.runFrom fuel cfg label target)

end Internal

namespace Program

def CompilesTo (program : Program) (target : TypedCfg.CheckedProgram) : Prop :=
  Compiler.Program.toCheckedCfg? program = some target

theorem accepted?_of_compilesTo {program : Program}
    {target : TypedCfg.CheckedProgram}
    (h : CompilesTo program target) :
    Program.accepted? program = true := by
  unfold CompilesTo at h
  unfold Compiler.Program.toCheckedCfg? at h
  unfold Compiler.Program.toCfg? at h
  by_cases hAccepted : Program.accepted? program
  · exact hAccepted
  · simp [hAccepted] at h

theorem checked_of_compilesTo {program : Program}
    {target : TypedCfg.CheckedProgram}
    (_h : CompilesTo program target) :
    target.program.typeCheck? = some () :=
  target.checked

theorem toCfg?_of_compilesTo {program : Program}
    {target : TypedCfg.CheckedProgram}
    (h : CompilesTo program target) :
    Compiler.Program.toCfg? program = some target.program := by
  unfold CompilesTo at h
  unfold Compiler.Program.toCheckedCfg? at h
  cases hCfg : Compiler.Program.toCfg? program with
  | none =>
      simp [hCfg] at h
  | some cfg =>
      unfold TypedCfg.Program.check? at h
      by_cases hCheck : cfg.typeCheck? = some ()
      · simp [hCfg, hCheck] at h
        cases h
        rfl
      · simp [hCfg, hCheck] at h

/--
The adjacent whole-program preservation property we want to prove next.

This is partial in the standard verified-compiler sense: if the checked
compiler succeeds, running the generated typed CFG is related to running the
StackFreeCfg source interpreter with the canonical shared primitive semantics.
-/
def PreservesCompiled (program : Program) (target : TypedCfg.CheckedProgram) :
    Prop :=
  ∀ fuel sourceShared targetInitial,
    InitialRel sourceShared targetInitial →
      ResultRel
        (Program.runObserved PrimitiveSemantics.canonical fuel program
          sourceShared)
        (TypedCfg.Program.run fuel target.program targetInitial)

/--
Public theorem target for this pass.

The future theorem should prove this `Prop`, rather than taking generated
layout witnesses, replay certificates, or per-callee obligations as inputs.
-/
def CompilePreserves : Prop :=
  ∀ program target,
    CompilesTo program target →
      PreservesCompiled program target

end Program

theorem initial_stateRel {shared : SharedState} {target : TypedCfg.EVMState}
    (h : InitialRel shared target) :
    Internal.StateRel [] [] ({ shared := shared } : State)
      (TypedCfg.RunState.initial target) := by
  constructor
  · intro name hMem
    rfl
  · simp [TypedCfg.RunState.initial, h.shared_eq]
  · simp [Internal.ShapeMatchesStore, TypedCfg.RunState.initial,
      h.stack_empty]

end Preservation
end StackFreeCfg
end EvmCompiler
