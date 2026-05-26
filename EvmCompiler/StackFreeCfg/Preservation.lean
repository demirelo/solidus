import EvmCompiler.StackFreeCfg.PreservationSupport
import EvmCompiler.StackFreeCfg.PrimitiveAdapter

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
  PreservationSupport.Shape

abbrev Label :=
  PreservationSupport.Label

abbrev StoreScoped :=
  PreservationSupport.StoreScoped

abbrev SlotMatchesStore :=
  PreservationSupport.SlotMatchesStore

abbrev ShapeMatchesStore :=
  PreservationSupport.ShapeMatchesStore

abbrev StateRel :=
  PreservationSupport.StateRel

namespace StateRel

theorem shared_eq_of {scope : List Name} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (h : StateRel scope shape source target) :
    target.evm.toSharedState = source.shared :=
  PreservationSupport.StateRel.shared_eq_of h

theorem block_input_matches {scope : List Name} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (h : StateRel scope shape source target) :
    shape.matchesStack target.evm.stack = true :=
  PreservationSupport.StateRel.block_input_matches h

theorem restrictSource {scope : List Name} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (h : StateRel scope shape source target) :
    StateRel scope shape (source.restrictTo scope) target :=
  PreservationSupport.StateRel.restrictSource h

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

theorem stmt_zero {cfg : TypedCfg.Program} {program : Program}
    {sourceCtx : Ctx} {targetCtx : Compiler.Context}
    {stmt : Stmt} {label : Label} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (hCheck : cfg.typeCheck? = some ())
    (hLabelShape : cfg.labelShape? label = some shape)
    (hRel : StateRel sourceCtx.scope shape source target) :
    FragmentResultRel targetCtx
      (Stmt.run 0 PrimitiveSemantics.canonical program sourceCtx stmt source)
      (TypedCfg.Program.runFrom 0 cfg label target) := by
  rw [PreservationSupport.TypedProgram.runFrom_zero_of_labelShape?_stateRel
    (program := cfg) (label := label) (shape := shape)
    (scope := sourceCtx.scope) (source := source) (target := target)
    hCheck hLabelShape hRel]
  exact FragmentResultRel.outOfFuel rfl
    (StateRel.shared_eq_of (StateRel.restrictSource hRel))

theorem seq_zero {cfg : TypedCfg.Program} {program : Program}
    {sourceCtx : Ctx} {targetCtx : Compiler.Context}
    {stmts : List Stmt} {label : Label} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (hCheck : cfg.typeCheck? = some ())
    (hLabelShape : cfg.labelShape? label = some shape)
    (hRel : StateRel sourceCtx.scope shape source target) :
    FragmentResultRel targetCtx
      (StmtList.run 0 PrimitiveSemantics.canonical program sourceCtx stmts
        source)
      (TypedCfg.Program.runFrom 0 cfg label target) := by
  rw [PreservationSupport.TypedProgram.runFrom_zero_of_labelShape?_stateRel
    (program := cfg) (label := label) (shape := shape)
    (scope := sourceCtx.scope) (source := source) (target := target)
    hCheck hLabelShape hRel]
  exact FragmentResultRel.outOfFuel rfl
    (StateRel.shared_eq_of (StateRel.restrictSource hRel))

theorem block_zero {cfg : TypedCfg.Program} {program : Program}
    {sourceCtx : Ctx} {targetCtx : Compiler.Context}
    {block : Block} {label : Label} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (hCheck : cfg.typeCheck? = some ())
    (hLabelShape : cfg.labelShape? label = some shape)
    (hRel : StateRel sourceCtx.scope shape source target) :
    FragmentResultRel targetCtx
      (Block.run 0 PrimitiveSemantics.canonical program sourceCtx block
        source)
      (TypedCfg.Program.runFrom 0 cfg label target) := by
  rw [PreservationSupport.TypedProgram.runFrom_zero_of_labelShape?_stateRel
    (program := cfg) (label := label) (shape := shape)
    (scope := sourceCtx.scope) (source := source) (target := target)
    hCheck hLabelShape hRel]
  exact FragmentResultRel.outOfFuel rfl
    (StateRel.shared_eq_of (StateRel.restrictSource hRel))

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
  · rw [TypedCfg.RunState.initial, h.stack_empty]
    trivial

end Preservation
end StackFreeCfg
end EvmCompiler
