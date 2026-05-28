import EvmCompiler.Assembly.Bytecode

namespace EvmCompiler
namespace Assembly

/-!
Gas-parametric target execution.

The ordinary assembly target semantics is intentionally gasless: `GAS` reads the
current `gasAvailable` field, while the semantics does not perform the gas
deductions that EVMYulLean's `EVM.X` performs before executing an opcode.  This
module adds the first piece of the stronger route: a target semantics where the
observable result of `GAS` is supplied by an explicit oracle.  Non-`GAS`
instructions keep the existing gasless behavior.

This is not yet the final `EVM.X` adequacy theorem.  It is the layer that lets
the source/target compiler proof become parametric in the same gas observations
that a later gas-aware EVM proof will instantiate from the concrete `X` run.
-/

namespace GasParametric

/--
Oracle for the value returned by each dynamic `GAS` instruction.

The cursor carried by the semantics is the request index: when execution reaches
`GAS` at cursor `n`, the instruction pushes `oracle n` and the next request uses
cursor `n + 1`.  A finite successful run only constrains the oracle entries it
actually reads.
-/
abbrev GasOracle := Nat → Word

namespace GasOracle

def withAnswer (base : GasOracle) (cursor : Nat) (answer : Word) :
    GasOracle :=
  fun request => if request = cursor then answer else base request

@[simp] theorem withAnswer_self (base : GasOracle) (cursor : Nat)
    (answer : Word) :
    withAnswer base cursor answer cursor = answer := by
  simp [withAnswer]

theorem withAnswer_of_ne {base : GasOracle} {cursor request : Nat}
    {answer : Word} (hNe : request ≠ cursor) :
    withAnswer base cursor answer request = base request := by
  simp [withAnswer, hNe]

theorem withAnswer_of_lt {base : GasOracle} {cursor request : Nat}
    {answer : Word} (hLt : request < cursor) :
    withAnswer base cursor answer request = base request := by
  exact withAnswer_of_ne (Nat.ne_of_lt hLt)

theorem withAnswer_of_gt {base : GasOracle} {cursor request : Nat}
    {answer : Word} (hGt : cursor < request) :
    withAnswer base cursor answer request = base request := by
  exact withAnswer_of_ne (Nat.ne_of_gt hGt)

end GasOracle

def TargetInstr.usesGas : TargetInstr → Bool
  | .prim .gas => true
  | _ => false

def PrimOp.stepWithGasOracle (oracle : GasOracle) (cursor : Nat)
    (op : PrimOp) (state : EVMState) :
    Except EVMException (EVMState × Nat) :=
  match op with
  | .gas =>
      .ok
        ( state.replaceStackAndIncrPC (state.stack.push (oracle cursor))
        , cursor + 1
        )
  | _ => do
      let state' ← op.step state
      pure (state', cursor)

def Target.stepInstrWithGasOracle (oracle : GasOracle) (cursor : Nat)
    (instr : TargetInstr) (state : EVMState) :
    Except EVMException (EVMState × Nat) :=
  match instr with
  | .prim op => PrimOp.stepWithGasOracle oracle cursor op state
  | _ => do
      let state' ← Target.stepInstr instr state
      pure (state', cursor)

def Target.stepInstrResultWithGasOracle (oracle : GasOracle) (cursor : Nat)
    (instr : TargetInstr) (state : EVMState) :
    Except EVMException (StepResult × Nat) := do
  let (state', cursor') ← Target.stepInstrWithGasOracle oracle cursor instr state
  match instr.haltKind? with
  | some kind =>
      pure (.halted { kind := kind, state := state', output := kind.output state' },
        cursor')
  | none =>
      pure (.running state', cursor')

def Target.runListResultWithGasOracle (oracle : GasOracle) :
    List TargetInstr → Nat → EVMState → Except EVMException (StepResult × Nat)
  | [], cursor, state => .ok (.running state, cursor)
  | instr :: rest, cursor, state => do
      let (result, cursor') ←
        Target.stepInstrResultWithGasOracle oracle cursor instr state
      match result with
      | .running state' =>
          Target.runListResultWithGasOracle oracle rest cursor' state'
      | .halted halt =>
          .ok (.halted halt, cursor')

def Target.stepResultWithGasOracle (target : TargetProgram)
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (StepResult × Nat) :=
  match target.fetch state.pc.toNat with
  | some instr => Target.stepInstrResultWithGasOracle oracle cursor instr state
  | none => .error .InvalidInstruction

def Target.runNResultWithGasOracle (target : TargetProgram)
    (oracle : GasOracle) : Nat → Nat → EVMState →
      Except EVMException (StepResult × Nat)
  | 0, cursor, state => .ok (.running state, cursor)
  | fuel + 1, cursor, state => do
      let (result, cursor') ←
        Target.stepResultWithGasOracle target oracle cursor state
      match result with
      | .running state' =>
          Target.runNResultWithGasOracle target oracle fuel cursor' state'
      | .halted halt =>
          .ok (.halted halt, cursor')

def sourceStepAtWithGasOracle (program : Program) (_pc : Nat) (instr : Instr)
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (StepResult × Nat) := do
  let (state', cursor') ←
    match instr with
    | .label _ =>
        Target.stepInstrWithGasOracle oracle cursor .jumpdest state
    | .prim op =>
        PrimOp.stepWithGasOracle oracle cursor op state
    | .push value =>
        Target.stepInstrWithGasOracle oracle cursor (.push32 value) state
    | .jump target => do
        let dest ← (Program.labelPc program target).elim Source.invalid pure
        pure (Source.jumpPc dest state, cursor)
    | .jumpi target => do
        let dest ← (Program.labelPc program target).elim Source.invalid pure
        match state.stack.pop with
        | some (stack, cond) =>
            let pc' :=
              if cond != EvmYul.UInt256.ofNat 0 then
                EvmYul.UInt256.ofNat dest
              else
                Source.jumpiFallthroughPc state
            pure ({ state with pc := pc', stack := stack }, cursor)
        | none =>
            .error .StackUnderflow
  match instr.haltKind? with
  | some kind =>
      pure (.halted { kind := kind, state := state', output := kind.output state' },
        cursor')
  | none =>
      pure (.running state', cursor')

def sourceStepResultWithGasOracle (program : Program)
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (StepResult × Nat) :=
  match Program.instrAtPc program state.pc.toNat with
  | some (pc, instr) =>
      sourceStepAtWithGasOracle program pc instr oracle cursor state
  | none => .error .InvalidInstruction

def sourceRunNResultWithGasOracle (program : Program)
    (oracle : GasOracle) : Nat → Nat → EVMState →
      Except EVMException (StepResult × Nat)
  | 0, cursor, state => .ok (.running state, cursor)
  | fuel + 1, cursor, state => do
      let (result, cursor') ←
        sourceStepResultWithGasOracle program oracle cursor state
      match result with
      | .running state' =>
          sourceRunNResultWithGasOracle program oracle fuel cursor' state'
      | .halted halt =>
          .ok (.halted halt, cursor')

def compiledStepResultWithGasOracle (program : Program)
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (StepResult × Nat) :=
  match emitCurrent? program state with
  | some code => Target.runListResultWithGasOracle oracle code cursor state
  | none => .error .InvalidInstruction

def compiledRunNResultWithGasOracle (program : Program)
    (oracle : GasOracle) : Nat → Nat → EVMState →
      Except EVMException (StepResult × Nat)
  | 0, cursor, state => .ok (.running state, cursor)
  | fuel + 1, cursor, state => do
      let (result, cursor') ←
        compiledStepResultWithGasOracle program oracle cursor state
      match result with
      | .running state' =>
          compiledRunNResultWithGasOracle program oracle fuel cursor' state'
      | .halted halt =>
          .ok (.halted halt, cursor')

inductive BlockTraceResult (program : Program) (target : TargetProgram)
    (oracle : GasOracle) : Nat → Nat → EVMState → StepResult → Nat → Prop where
  | done (cursor : Nat) (state : EVMState) :
      BlockTraceResult program target oracle 0 cursor state (.running state)
        cursor
  | stepRunning {fuel cursor cursorMid cursorFinal : Nat}
      {state mid : EVMState} {result : StepResult}
      {pc : Nat} {instr : Instr} {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResultWithGasOracle oracle
            (emitted.map LocatedTarget.instr) cursor state =
          .ok (.running mid, cursorMid))
      (hRest :
        BlockTraceResult program target oracle fuel cursorMid mid result
          cursorFinal) :
      BlockTraceResult program target oracle (fuel + 1) cursor state result
        cursorFinal
  | stepHalted {fuel cursor cursorFinal : Nat}
      {state : EVMState} {halt : Halt}
      {pc : Nat} {instr : Instr} {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResultWithGasOracle oracle
            (emitted.map LocatedTarget.instr) cursor state =
          .ok (.halted halt, cursorFinal)) :
      BlockTraceResult program target oracle (fuel + 1) cursor state
        (.halted halt) cursorFinal

@[simp] theorem PrimOp.stepWithGasOracle_gas
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    PrimOp.stepWithGasOracle oracle cursor .gas state =
      .ok
        ( state.replaceStackAndIncrPC (state.stack.push (oracle cursor))
        , cursor + 1
        ) := by
  rfl

@[simp] theorem Target.stepInstrResultWithGasOracle_gas
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    Target.stepInstrResultWithGasOracle oracle cursor (.prim .gas) state =
      .ok
        ( .running
            (state.replaceStackAndIncrPC (state.stack.push (oracle cursor)))
        , cursor + 1
        ) := by
  simp [Target.stepInstrResultWithGasOracle,
    Target.stepInstrWithGasOracle, TargetInstr.haltKind?, PrimOp.haltKind?]

theorem Target.runListResultWithGasOracle_nil
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    Target.runListResultWithGasOracle oracle [] cursor state =
      .ok (.running state, cursor) := by
  rfl

theorem Target.runListResultWithGasOracle_single
    (oracle : GasOracle) (cursor : Nat) (instr : TargetInstr)
    (state : EVMState) :
    Target.runListResultWithGasOracle oracle [instr] cursor state =
      Target.stepInstrResultWithGasOracle oracle cursor instr state := by
  cases h : Target.stepInstrResultWithGasOracle oracle cursor instr state with
  | error e =>
      unfold Target.runListResultWithGasOracle
      rw [h]
      rfl
  | ok result =>
      unfold Target.runListResultWithGasOracle
      rw [h]
      cases result with
      | mk step cursor' =>
          cases step <;> rfl

theorem PrimOp.stepWithGasOracle_of_ne_gas
    {oracle : GasOracle} {cursor : Nat} {op : PrimOp}
    {state state' : EVMState}
    (hNe : op ≠ .gas) (hStep : op.step state = .ok state') :
    PrimOp.stepWithGasOracle oracle cursor op state = .ok (state', cursor) := by
  cases op <;> simp [PrimOp.stepWithGasOracle] at hNe ⊢
  all_goals
    rw [hStep]
    simp

theorem Target.stepInstrWithGasOracle_of_not_usesGas
    {oracle : GasOracle} {cursor : Nat} {instr : TargetInstr}
    {state state' : EVMState}
    (hNoGas : TargetInstr.usesGas instr = false)
    (hStep : Target.stepInstr instr state = .ok state') :
    Target.stepInstrWithGasOracle oracle cursor instr state =
      .ok (state', cursor) := by
  cases instr with
  | prim op =>
      cases op <;>
        simp [TargetInstr.usesGas, Target.stepInstrWithGasOracle,
          PrimOp.stepWithGasOracle, Target.stepInstr] at hNoGas hStep ⊢
      all_goals
        rw [hStep]
        simp
  | push32 value =>
      simpa [Target.stepInstrWithGasOracle, Target.stepInstr] using hStep
  | jump =>
      simp [Target.stepInstrWithGasOracle, Target.stepInstr] at hStep ⊢
      rw [hStep]
      simp
  | jumpi =>
      simp [Target.stepInstrWithGasOracle, Target.stepInstr] at hStep ⊢
      rw [hStep]
      simp
  | jumpdest =>
      simpa [Target.stepInstrWithGasOracle, Target.stepInstr] using hStep

theorem Target.stepInstrResultWithGasOracle_of_not_usesGas
    {oracle : GasOracle} {cursor : Nat} {instr : TargetInstr}
    {state : EVMState} {result : StepResult}
    (hNoGas : TargetInstr.usesGas instr = false)
    (hStep : Target.stepInstrResult instr state = .ok result) :
    Target.stepInstrResultWithGasOracle oracle cursor instr state =
      .ok (result, cursor) := by
  unfold Target.stepInstrResult at hStep
  cases hBase : Target.stepInstr instr state with
  | error err =>
      rw [hBase] at hStep
      cases hStep
  | ok state' =>
      rw [hBase] at hStep
      have hOracleStep :=
        Target.stepInstrWithGasOracle_of_not_usesGas (oracle := oracle)
          (cursor := cursor) (instr := instr) (state := state)
          (state' := state') hNoGas hBase
      unfold Target.stepInstrResultWithGasOracle
      rw [hOracleStep]
      cases hKind : instr.haltKind? <;> simp [hKind] at hStep ⊢
      · cases hStep
        rfl
      · cases hStep
        rfl

theorem Target.runListResultWithGasOracle_of_forall_not_usesGas
    {oracle : GasOracle} {cursor : Nat} {code : List TargetInstr}
    {state : EVMState} {result : StepResult}
    (hNoGas : ∀ instr, instr ∈ code → TargetInstr.usesGas instr = false)
    (hRun : Target.runListResult code state = .ok result) :
    Target.runListResultWithGasOracle oracle code cursor state =
      .ok (result, cursor) := by
  induction code generalizing cursor state with
  | nil =>
      simp [Target.runListResult, Target.runListResultWithGasOracle] at hRun ⊢
      cases hRun
      rfl
  | cons instr rest ih =>
      unfold Target.runListResult at hRun
      cases hStep : Target.stepInstrResult instr state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepResult =>
          rw [hStep] at hRun
          have hStepOracle :=
            Target.stepInstrResultWithGasOracle_of_not_usesGas
              (oracle := oracle) (cursor := cursor) (instr := instr)
              (state := state) (result := stepResult)
              (hNoGas instr (by simp)) hStep
          unfold Target.runListResultWithGasOracle
          rw [hStepOracle]
          cases stepResult with
          | running state' =>
              exact ih
                (fun instr hMem => hNoGas instr (by simp [hMem]))
                hRun
          | halted halt =>
              cases hRun
              rfl

theorem PrimOp.stepWithGasOracle_cursor_le
    {oracle : GasOracle} {cursor : Nat} {op : PrimOp}
    {state state' : EVMState} {cursor' : Nat}
    (hStep : PrimOp.stepWithGasOracle oracle cursor op state =
      .ok (state', cursor')) :
    cursor ≤ cursor' := by
  unfold PrimOp.stepWithGasOracle at hStep
  split at hStep
  · cases hStep
    exact Nat.le_succ cursor
  · cases hBase : op.step state with
    | error err =>
        simp [hBase, Bind.bind, Except.bind] at hStep
    | ok state'' =>
        simp [hBase, Bind.bind, Except.bind] at hStep
        rcases hStep with ⟨_, hCursor⟩
        omega

theorem Target.stepInstrWithGasOracle_cursor_le
    {oracle : GasOracle} {cursor : Nat} {instr : TargetInstr}
    {state state' : EVMState} {cursor' : Nat}
    (hStep : Target.stepInstrWithGasOracle oracle cursor instr state =
      .ok (state', cursor')) :
    cursor ≤ cursor' := by
  cases instr with
  | prim op =>
      exact PrimOp.stepWithGasOracle_cursor_le hStep
  | push32 value =>
      unfold Target.stepInstrWithGasOracle at hStep
      cases hBase : Target.stepInstr (TargetInstr.push32 value) state with
      | error err =>
          simp [hBase, Bind.bind, Except.bind] at hStep
      | ok state'' =>
          simp [hBase, Bind.bind, Except.bind] at hStep
          rcases hStep with ⟨_, hCursor⟩
          omega
  | jump =>
      unfold Target.stepInstrWithGasOracle at hStep
      cases hBase : Target.stepInstr TargetInstr.jump state with
      | error err =>
          simp [hBase, Bind.bind, Except.bind] at hStep
      | ok state'' =>
          simp [hBase, Bind.bind, Except.bind] at hStep
          rcases hStep with ⟨_, hCursor⟩
          omega
  | jumpi =>
      unfold Target.stepInstrWithGasOracle at hStep
      cases hBase : Target.stepInstr TargetInstr.jumpi state with
      | error err =>
          simp [hBase, Bind.bind, Except.bind] at hStep
      | ok state'' =>
          simp [hBase, Bind.bind, Except.bind] at hStep
          rcases hStep with ⟨_, hCursor⟩
          omega
  | jumpdest =>
      unfold Target.stepInstrWithGasOracle at hStep
      cases hBase : Target.stepInstr TargetInstr.jumpdest state with
      | error err =>
          simp [hBase, Bind.bind, Except.bind] at hStep
      | ok state'' =>
          simp [hBase, Bind.bind, Except.bind] at hStep
          rcases hStep with ⟨_, hCursor⟩
          omega

theorem PrimOp.stepWithGasOracle_withAnswer_of_run_le
    {oracle : GasOracle} {cursor answerCursor : Nat} {answer : Word}
    {op : PrimOp} {state state' : EVMState} {cursor' : Nat}
    (hRun : PrimOp.stepWithGasOracle oracle cursor op state =
      .ok (state', cursor'))
    (hLe : cursor' ≤ answerCursor) :
    PrimOp.stepWithGasOracle
        (GasOracle.withAnswer oracle answerCursor answer) cursor op state =
      .ok (state', cursor') := by
  cases op <;> simp [PrimOp.stepWithGasOracle] at hRun ⊢
  case gas =>
    rcases hRun with ⟨hState, hCursor⟩
    subst state'
    subst cursor'
    have hLt : cursor < answerCursor := Nat.lt_of_succ_le hLe
    simp [GasOracle.withAnswer_of_lt hLt]
  all_goals exact hRun

theorem Target.stepInstrWithGasOracle_withAnswer_of_run_le
    {oracle : GasOracle} {cursor answerCursor : Nat} {answer : Word}
    {instr : TargetInstr} {state state' : EVMState} {cursor' : Nat}
    (hRun : Target.stepInstrWithGasOracle oracle cursor instr state =
      .ok (state', cursor'))
    (hLe : cursor' ≤ answerCursor) :
    Target.stepInstrWithGasOracle
        (GasOracle.withAnswer oracle answerCursor answer) cursor instr state =
      .ok (state', cursor') := by
  cases instr with
  | prim op =>
      exact
        PrimOp.stepWithGasOracle_withAnswer_of_run_le
          (answer := answer) hRun hLe
  | push32 value =>
      simpa [Target.stepInstrWithGasOracle] using hRun
  | jump =>
      simpa [Target.stepInstrWithGasOracle] using hRun
  | jumpi =>
      simpa [Target.stepInstrWithGasOracle] using hRun
  | jumpdest =>
      simpa [Target.stepInstrWithGasOracle] using hRun

theorem Target.stepInstrResultWithGasOracle_cursor_le
    {oracle : GasOracle} {cursor : Nat} {instr : TargetInstr}
    {state : EVMState} {result : StepResult} {cursor' : Nat}
    (hRun : Target.stepInstrResultWithGasOracle oracle cursor instr state =
      .ok (result, cursor')) :
    cursor ≤ cursor' := by
  unfold Target.stepInstrResultWithGasOracle at hRun
  cases hStep : Target.stepInstrWithGasOracle oracle cursor instr state with
  | error err =>
      rw [hStep] at hRun
      simp [Bind.bind, Except.bind] at hRun
  | ok pair =>
      rcases pair with ⟨state', cursorMid⟩
      have hLeStep := Target.stepInstrWithGasOracle_cursor_le hStep
      rw [hStep] at hRun
      cases hKind : instr.haltKind? <;>
        simp [hKind, Bind.bind, Except.bind] at hRun
      · rcases hRun with ⟨_, hCursor⟩
        omega
      · rcases hRun with ⟨_, hCursor⟩
        omega

theorem Target.runListResultWithGasOracle_cursor_le
    {oracle : GasOracle} {cursor : Nat} {code : List TargetInstr}
    {state : EVMState} {result : StepResult} {cursorFinal : Nat}
    (hRun : Target.runListResultWithGasOracle oracle code cursor state =
      .ok (result, cursorFinal)) :
    cursor ≤ cursorFinal := by
  induction code generalizing cursor state with
  | nil =>
      simp [Target.runListResultWithGasOracle] at hRun
      rcases hRun with ⟨_, hCursor⟩
      omega
  | cons instr rest ih =>
      unfold Target.runListResultWithGasOracle at hRun
      cases hStep :
          Target.stepInstrResultWithGasOracle oracle cursor instr state with
      | error err =>
          rw [hStep] at hRun
          simp [Bind.bind, Except.bind] at hRun
      | ok pair =>
          rcases pair with ⟨stepResult, cursorMid⟩
          have hLeStep :=
            Target.stepInstrResultWithGasOracle_cursor_le hStep
          rw [hStep] at hRun
          cases stepResult with
          | running mid =>
              have hLeTail := ih hRun
              exact Nat.le_trans hLeStep hLeTail
          | halted halt =>
              simp [Bind.bind, Except.bind] at hRun
              rcases hRun with ⟨_, hCursor⟩
              omega

theorem Target.stepInstrResultWithGasOracle_withAnswer_of_run_le
    {oracle : GasOracle} {cursor answerCursor : Nat} {answer : Word}
    {instr : TargetInstr} {state : EVMState} {result : StepResult}
    {cursor' : Nat}
    (hRun : Target.stepInstrResultWithGasOracle oracle cursor instr state =
      .ok (result, cursor'))
    (hLe : cursor' ≤ answerCursor) :
    Target.stepInstrResultWithGasOracle
        (GasOracle.withAnswer oracle answerCursor answer) cursor instr state =
      .ok (result, cursor') := by
  cases instr with
  | prim op =>
      cases op <;>
        simp [Target.stepInstrResultWithGasOracle,
          Target.stepInstrWithGasOracle, PrimOp.stepWithGasOracle,
          TargetInstr.haltKind?, PrimOp.haltKind?] at hRun ⊢
      case gas =>
        rcases hRun with ⟨hResult, hCursor⟩
        subst result
        have hLt : cursor < answerCursor := by omega
        simpa [GasOracle.withAnswer_of_lt hLt] using hCursor
      all_goals
        exact hRun
  | push32 value =>
      simpa [Target.stepInstrResultWithGasOracle,
        Target.stepInstrWithGasOracle, TargetInstr.haltKind?] using hRun
  | jump =>
      simpa [Target.stepInstrResultWithGasOracle,
        Target.stepInstrWithGasOracle, TargetInstr.haltKind?] using hRun
  | jumpi =>
      simpa [Target.stepInstrResultWithGasOracle,
        Target.stepInstrWithGasOracle, TargetInstr.haltKind?] using hRun
  | jumpdest =>
      simpa [Target.stepInstrResultWithGasOracle,
        Target.stepInstrWithGasOracle, TargetInstr.haltKind?] using hRun

theorem Target.runListResultWithGasOracle_withAnswer_of_run_le
    {oracle : GasOracle} {cursor answerCursor : Nat} {answer : Word}
    {code : List TargetInstr} {state : EVMState} {result : StepResult}
    {cursorFinal : Nat}
    (hRun : Target.runListResultWithGasOracle oracle code cursor state =
      .ok (result, cursorFinal))
    (hLe : cursorFinal ≤ answerCursor) :
    Target.runListResultWithGasOracle
        (GasOracle.withAnswer oracle answerCursor answer) code cursor state =
      .ok (result, cursorFinal) := by
  induction code generalizing cursor state with
  | nil =>
      simp [Target.runListResultWithGasOracle] at hRun ⊢
      exact hRun
  | cons instr rest ih =>
      unfold Target.runListResultWithGasOracle at hRun ⊢
      cases hStep :
          Target.stepInstrResultWithGasOracle oracle cursor instr state with
      | error err =>
          rw [hStep] at hRun
          simp [Bind.bind, Except.bind] at hRun
      | ok pair =>
          rcases pair with ⟨stepResult, cursorMid⟩
          rw [hStep] at hRun
          cases stepResult with
          | running mid =>
              have hTailCursorLe :=
                Target.runListResultWithGasOracle_cursor_le hRun
              have hStepLe : cursorMid ≤ answerCursor :=
                Nat.le_trans hTailCursorLe hLe
              have hStepExtend :=
                Target.stepInstrResultWithGasOracle_withAnswer_of_run_le
                  (answer := answer) hStep hStepLe
              rw [hStepExtend]
              exact ih hRun
          | halted halt =>
              simp [Bind.bind, Except.bind] at hRun
              rcases hRun with ⟨hResult, hCursor⟩
              have hStepLe : cursorMid ≤ answerCursor := by omega
              have hStepExtend :=
                Target.stepInstrResultWithGasOracle_withAnswer_of_run_le
                  (answer := answer) hStep hStepLe
              rw [hStepExtend]
              simp [Bind.bind, Except.bind]
              cases hResult
              cases hCursor
              exact ⟨rfl, rfl⟩

theorem Target.stepResultWithGasOracle_cursor_le
    {target : TargetProgram} {oracle : GasOracle} {cursor : Nat}
    {state : EVMState} {result : StepResult} {cursor' : Nat}
    (hRun : Target.stepResultWithGasOracle target oracle cursor state =
      .ok (result, cursor')) :
    cursor ≤ cursor' := by
  unfold Target.stepResultWithGasOracle at hRun
  cases hFetch : target.fetch state.pc.toNat with
  | none =>
      rw [hFetch] at hRun
      cases hRun
  | some instr =>
      rw [hFetch] at hRun
      exact Target.stepInstrResultWithGasOracle_cursor_le hRun

theorem Target.runNResultWithGasOracle_cursor_le
    {target : TargetProgram} {oracle : GasOracle} {fuel cursor : Nat}
    {state : EVMState} {result : StepResult} {cursorFinal : Nat}
    (hRun : Target.runNResultWithGasOracle target oracle fuel cursor state =
      .ok (result, cursorFinal)) :
    cursor ≤ cursorFinal := by
  induction fuel generalizing cursor state with
  | zero =>
      simp [Target.runNResultWithGasOracle] at hRun
      rcases hRun with ⟨_, hCursor⟩
      omega
  | succ fuel ih =>
      unfold Target.runNResultWithGasOracle at hRun
      cases hStep :
          Target.stepResultWithGasOracle target oracle cursor state with
      | error err =>
          rw [hStep] at hRun
          simp [Bind.bind, Except.bind] at hRun
      | ok pair =>
          rcases pair with ⟨stepResult, cursorMid⟩
          have hLeStep := Target.stepResultWithGasOracle_cursor_le hStep
          rw [hStep] at hRun
          cases stepResult with
          | running mid =>
              exact Nat.le_trans hLeStep (ih hRun)
          | halted halt =>
              simp [Bind.bind, Except.bind] at hRun
              rcases hRun with ⟨_, hCursor⟩
              omega

theorem Target.stepResultWithGasOracle_withAnswer_of_run_le
    {target : TargetProgram} {oracle : GasOracle}
    {cursor answerCursor : Nat} {answer : Word}
    {state : EVMState} {result : StepResult} {cursor' : Nat}
    (hRun : Target.stepResultWithGasOracle target oracle cursor state =
      .ok (result, cursor'))
    (hLe : cursor' ≤ answerCursor) :
    Target.stepResultWithGasOracle target
        (GasOracle.withAnswer oracle answerCursor answer) cursor state =
      .ok (result, cursor') := by
  unfold Target.stepResultWithGasOracle at hRun ⊢
  cases hFetch : target.fetch state.pc.toNat with
  | none =>
      rw [hFetch] at hRun
      cases hRun
  | some instr =>
      rw [hFetch] at hRun
      simpa [hFetch] using
        Target.stepInstrResultWithGasOracle_withAnswer_of_run_le
          (answer := answer) hRun hLe

theorem Target.runNResultWithGasOracle_withAnswer_of_run_le
    {target : TargetProgram} {oracle : GasOracle}
    {fuel cursor answerCursor : Nat} {answer : Word}
    {state : EVMState} {result : StepResult} {cursorFinal : Nat}
    (hRun : Target.runNResultWithGasOracle target oracle fuel cursor state =
      .ok (result, cursorFinal))
    (hLe : cursorFinal ≤ answerCursor) :
    Target.runNResultWithGasOracle target
        (GasOracle.withAnswer oracle answerCursor answer) fuel cursor state =
      .ok (result, cursorFinal) := by
  induction fuel generalizing cursor state with
  | zero =>
      simp [Target.runNResultWithGasOracle] at hRun ⊢
      exact hRun
  | succ fuel ih =>
      unfold Target.runNResultWithGasOracle at hRun ⊢
      cases hStep :
          Target.stepResultWithGasOracle target oracle cursor state with
      | error err =>
          rw [hStep] at hRun
          simp [Bind.bind, Except.bind] at hRun
      | ok pair =>
          rcases pair with ⟨stepResult, cursorMid⟩
          rw [hStep] at hRun
          cases stepResult with
          | running mid =>
              have hTailCursorLe :=
                Target.runNResultWithGasOracle_cursor_le hRun
              have hStepLe : cursorMid ≤ answerCursor :=
                Nat.le_trans hTailCursorLe hLe
              have hStepExtend :=
                Target.stepResultWithGasOracle_withAnswer_of_run_le
                  (answer := answer) hStep hStepLe
              rw [hStepExtend]
              exact ih hRun
          | halted halt =>
              simp [Bind.bind, Except.bind] at hRun
              rcases hRun with ⟨hResult, hCursor⟩
              have hStepLe : cursorMid ≤ answerCursor := by omega
              have hStepExtend :=
                Target.stepResultWithGasOracle_withAnswer_of_run_le
                  (answer := answer) hStep hStepLe
              rw [hStepExtend]
              simp [Bind.bind, Except.bind]
              cases hResult
              cases hCursor
              exact ⟨rfl, rfl⟩

theorem sourceStepAtWithGasOracle_cursor_le
    {program : Program} {pc : Nat} {instr : Instr}
    {oracle : GasOracle} {cursor : Nat} {state : EVMState}
    {result : StepResult} {cursor' : Nat}
    (hRun :
      sourceStepAtWithGasOracle program pc instr oracle cursor state =
        .ok (result, cursor')) :
    cursor ≤ cursor' := by
  cases instr with
  | label name =>
      exact
        Target.stepInstrResultWithGasOracle_cursor_le
          (oracle := oracle) (instr := .jumpdest) (by
            simpa [sourceStepAtWithGasOracle, Instr.haltKind?,
              Target.stepInstrResultWithGasOracle,
              Target.stepInstrWithGasOracle, TargetInstr.haltKind?] using hRun)
  | prim op =>
      exact
        Target.stepInstrResultWithGasOracle_cursor_le
          (oracle := oracle) (instr := .prim op) (by
            simpa [sourceStepAtWithGasOracle,
              Target.stepInstrResultWithGasOracle,
              Target.stepInstrWithGasOracle] using hRun)
  | push value =>
      exact
        Target.stepInstrResultWithGasOracle_cursor_le
          (oracle := oracle) (instr := .push32 value) (by
            simpa [sourceStepAtWithGasOracle, Instr.haltKind?,
              Target.stepInstrResultWithGasOracle,
              Target.stepInstrWithGasOracle, TargetInstr.haltKind?] using hRun)
  | jump target =>
      unfold sourceStepAtWithGasOracle at hRun
      cases hDest : Program.labelPc program target with
      | none =>
          simp [hDest, Source.invalid, Bind.bind, Except.bind] at hRun
      | some dest =>
          simp [hDest, Bind.bind, Except.bind, Instr.haltKind?] at hRun
          rcases hRun with ⟨_, hCursor⟩
          omega
  | jumpi target =>
      unfold sourceStepAtWithGasOracle at hRun
      cases hDest : Program.labelPc program target with
      | none =>
          simp [hDest, Source.invalid, Bind.bind, Except.bind] at hRun
      | some dest =>
          cases hPop : state.stack.pop with
          | none =>
              simp [hDest, hPop, Bind.bind, Except.bind] at hRun
              change
                (Except.error EvmYul.EVM.ExecutionException.StackUnderflow :
                  Except EVMException (StepResult × Nat)) =
                    Except.ok (result, cursor') at hRun
              cases hRun
          | some pair =>
              rcases pair with ⟨stack, cond⟩
              simp [hDest, hPop, Bind.bind, Except.bind, Instr.haltKind?] at hRun
              rcases hRun with ⟨_, hCursor⟩
              omega

theorem sourceStepResultWithGasOracle_cursor_le
    {program : Program} {oracle : GasOracle} {cursor : Nat}
    {state : EVMState} {result : StepResult} {cursor' : Nat}
    (hRun : sourceStepResultWithGasOracle program oracle cursor state =
      .ok (result, cursor')) :
    cursor ≤ cursor' := by
  unfold sourceStepResultWithGasOracle at hRun
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      rw [hAt] at hRun
      cases hRun
  | some current =>
      rcases current with ⟨pc, instr⟩
      rw [hAt] at hRun
      exact sourceStepAtWithGasOracle_cursor_le hRun

theorem sourceRunNResultWithGasOracle_cursor_le
    {program : Program} {oracle : GasOracle} {fuel cursor : Nat}
    {state : EVMState} {result : StepResult} {cursorFinal : Nat}
    (hRun : sourceRunNResultWithGasOracle program oracle fuel cursor state =
      .ok (result, cursorFinal)) :
    cursor ≤ cursorFinal := by
  induction fuel generalizing cursor state with
  | zero =>
      simp [sourceRunNResultWithGasOracle] at hRun
      rcases hRun with ⟨_, hCursor⟩
      omega
  | succ fuel ih =>
      unfold sourceRunNResultWithGasOracle at hRun
      cases hStep :
          sourceStepResultWithGasOracle program oracle cursor state with
      | error err =>
          rw [hStep] at hRun
          simp [Bind.bind, Except.bind] at hRun
      | ok pair =>
          rcases pair with ⟨stepResult, cursorMid⟩
          have hLeStep := sourceStepResultWithGasOracle_cursor_le hStep
          rw [hStep] at hRun
          cases stepResult with
          | running mid =>
              exact Nat.le_trans hLeStep (ih hRun)
          | halted halt =>
              simp [Bind.bind, Except.bind] at hRun
              rcases hRun with ⟨_, hCursor⟩
              omega

theorem sourceStepAtWithGasOracle_withAnswer_of_run_le
    {program : Program} {pc : Nat} {instr : Instr}
    {oracle : GasOracle} {cursor answerCursor : Nat} {answer : Word}
    {state : EVMState} {result : StepResult} {cursor' : Nat}
    (hRun :
      sourceStepAtWithGasOracle program pc instr oracle cursor state =
        .ok (result, cursor'))
    (hLe : cursor' ≤ answerCursor) :
    sourceStepAtWithGasOracle program pc instr
        (GasOracle.withAnswer oracle answerCursor answer) cursor state =
      .ok (result, cursor') := by
  cases instr with
  | label name =>
      simpa [sourceStepAtWithGasOracle, Instr.haltKind?,
        Target.stepInstrResultWithGasOracle, Target.stepInstrWithGasOracle,
        TargetInstr.haltKind?] using
          Target.stepInstrResultWithGasOracle_withAnswer_of_run_le
            (oracle := oracle) (instr := .jumpdest) (answer := answer) (by
              simpa [sourceStepAtWithGasOracle, Instr.haltKind?,
                Target.stepInstrResultWithGasOracle,
                Target.stepInstrWithGasOracle, TargetInstr.haltKind?] using hRun)
            hLe
  | prim op =>
      simpa [sourceStepAtWithGasOracle,
        Target.stepInstrResultWithGasOracle, Target.stepInstrWithGasOracle] using
          Target.stepInstrResultWithGasOracle_withAnswer_of_run_le
            (oracle := oracle) (instr := .prim op) (answer := answer) (by
              simpa [sourceStepAtWithGasOracle,
                Target.stepInstrResultWithGasOracle,
                Target.stepInstrWithGasOracle] using hRun)
            hLe
  | push value =>
      simpa [sourceStepAtWithGasOracle, Instr.haltKind?,
        Target.stepInstrResultWithGasOracle, Target.stepInstrWithGasOracle,
        TargetInstr.haltKind?] using
          Target.stepInstrResultWithGasOracle_withAnswer_of_run_le
            (oracle := oracle) (instr := .push32 value) (answer := answer) (by
              simpa [sourceStepAtWithGasOracle, Instr.haltKind?,
                Target.stepInstrResultWithGasOracle,
                Target.stepInstrWithGasOracle, TargetInstr.haltKind?] using hRun)
            hLe
  | jump target =>
      simpa [sourceStepAtWithGasOracle] using hRun
  | jumpi target =>
      simpa [sourceStepAtWithGasOracle] using hRun

theorem sourceStepResultWithGasOracle_withAnswer_of_run_le
    {program : Program} {oracle : GasOracle}
    {cursor answerCursor : Nat} {answer : Word}
    {state : EVMState} {result : StepResult} {cursor' : Nat}
    (hRun : sourceStepResultWithGasOracle program oracle cursor state =
      .ok (result, cursor'))
    (hLe : cursor' ≤ answerCursor) :
    sourceStepResultWithGasOracle program
        (GasOracle.withAnswer oracle answerCursor answer) cursor state =
      .ok (result, cursor') := by
  unfold sourceStepResultWithGasOracle at hRun ⊢
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      rw [hAt] at hRun
      cases hRun
  | some current =>
      rcases current with ⟨pc, instr⟩
      rw [hAt] at hRun
      simpa [hAt] using
        sourceStepAtWithGasOracle_withAnswer_of_run_le
          (answer := answer) hRun hLe

theorem sourceRunNResultWithGasOracle_withAnswer_of_run_le
    {program : Program} {oracle : GasOracle}
    {fuel cursor answerCursor : Nat} {answer : Word}
    {state : EVMState} {result : StepResult} {cursorFinal : Nat}
    (hRun : sourceRunNResultWithGasOracle program oracle fuel cursor state =
      .ok (result, cursorFinal))
    (hLe : cursorFinal ≤ answerCursor) :
    sourceRunNResultWithGasOracle program
        (GasOracle.withAnswer oracle answerCursor answer) fuel cursor state =
      .ok (result, cursorFinal) := by
  induction fuel generalizing cursor state with
  | zero =>
      simp [sourceRunNResultWithGasOracle] at hRun ⊢
      exact hRun
  | succ fuel ih =>
      unfold sourceRunNResultWithGasOracle at hRun ⊢
      cases hStep :
          sourceStepResultWithGasOracle program oracle cursor state with
      | error err =>
          rw [hStep] at hRun
          simp [Bind.bind, Except.bind] at hRun
      | ok pair =>
          rcases pair with ⟨stepResult, cursorMid⟩
          rw [hStep] at hRun
          cases stepResult with
          | running mid =>
              have hTailCursorLe :=
                sourceRunNResultWithGasOracle_cursor_le hRun
              have hStepLe : cursorMid ≤ answerCursor :=
                Nat.le_trans hTailCursorLe hLe
              have hStepExtend :=
                sourceStepResultWithGasOracle_withAnswer_of_run_le
                  (answer := answer) hStep hStepLe
              rw [hStepExtend]
              exact ih hRun
          | halted halt =>
              simp [Bind.bind, Except.bind] at hRun
              rcases hRun with ⟨hResult, hCursor⟩
              have hStepLe : cursorMid ≤ answerCursor := by omega
              have hStepExtend :=
                sourceStepResultWithGasOracle_withAnswer_of_run_le
                  (answer := answer) hStep hStepLe
              rw [hStepExtend]
              simp [Bind.bind, Except.bind]
              cases hResult
              cases hCursor
              exact ⟨rfl, rfl⟩

theorem run_push_jump_result_withGasOracle
    (oracle : GasOracle) (cursor dest : Nat) (state : EVMState) :
    Target.runListResultWithGasOracle oracle
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        cursor state =
      .ok (.running (Source.jumpPc dest state), cursor) := by
  rfl

theorem run_push_jumpi_result_withGasOracle
    (oracle : GasOracle) (cursor dest : Nat) (state : EVMState) :
    Target.runListResultWithGasOracle oracle
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        cursor state =
      match state.stack.pop with
      | some (stack, cond) =>
          .ok
            (.running
              { state with
                pc :=
                  if cond != EvmYul.UInt256.ofNat 0 then
                    EvmYul.UInt256.ofNat dest
                  else
                    Source.jumpiFallthroughPc state
                stack := stack
              },
              cursor)
      | none =>
          .error .StackUnderflow := by
  cases state with
  | mk shared pc stack execLength =>
  cases stack with
  | nil => rfl
  | cons _ _ => rfl

theorem stepAt_emit_result_sound_withGasOracle
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {oracle : GasOracle}
    {cursor : Nat} {state : EVMState} {result : StepResult}
    {cursor' : Nat}
    (hEmit : emitInstr? program pc instr = some located)
    (hStep :
      sourceStepAtWithGasOracle program pc instr oracle cursor state =
        .ok (result, cursor')) :
    Target.runListResultWithGasOracle oracle
        (located.map LocatedTarget.instr) cursor state =
      .ok (result, cursor') := by
  cases instr with
  | label name =>
      simp [emitInstr?, sourceStepAtWithGasOracle] at hEmit hStep
      subst located
      simpa [Target.runListResultWithGasOracle_single] using hStep
  | prim op =>
      simp [emitInstr?, sourceStepAtWithGasOracle] at hEmit hStep
      subst located
      simpa [Target.runListResultWithGasOracle_single,
        Target.stepInstrResultWithGasOracle,
        Target.stepInstrWithGasOracle] using hStep
  | push value =>
      simp [emitInstr?, sourceStepAtWithGasOracle] at hEmit hStep
      subst located
      simpa [Target.runListResultWithGasOracle_single] using hStep
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest, sourceStepAtWithGasOracle, Source.jumpPc,
            Instr.haltKind?] at hEmit hStep
          subst located
          change
            Target.runListResultWithGasOracle oracle
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jump]
                cursor state =
              .ok (result, cursor')
          rw [run_push_jump_result_withGasOracle]
          cases hStep
          rfl
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest, sourceStepAtWithGasOracle,
            Instr.haltKind?] at hEmit hStep
          subst located
          change
            Target.runListResultWithGasOracle oracle
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jumpi]
                cursor state =
              .ok (result, cursor')
          rw [run_push_jumpi_result_withGasOracle]
          cases hPop : state.stack.pop with
          | none =>
              simp [hPop] at hStep
          | some pair =>
              cases pair with
              | mk stack cond =>
                  simp [hPop] at hStep ⊢
                  cases hStep
                  exact ⟨rfl, rfl⟩

theorem assemble_source_step_current_result_sound_withGasOracle
    {program : Program} {target : TargetProgram} {oracle : GasOracle}
    {cursor cursor' : Nat} {state : EVMState} {result : StepResult}
    (hAsm : assemble? program = some target)
    (hStep :
      sourceStepResultWithGasOracle program oracle cursor state =
        .ok (result, cursor')) :
    ∃ pc instr emitted before after,
      Program.instrAtPc program state.pc.toNat = some (pc, instr) ∧
        emitInstr? program pc instr = some emitted ∧
        target.code = before ++ emitted ++ after ∧
        Target.runListResultWithGasOracle oracle
            (emitted.map LocatedTarget.instr) cursor state =
          .ok (result, cursor') := by
  unfold sourceStepResultWithGasOracle at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some current =>
      cases current with
      | mk pc instr =>
          simp [hAt] at hStep
          obtain ⟨before, emitted, after, hTargetBlock, hEmitInstr⟩ :=
            Preservation.assemble_covers_current_pc hAsm hAt
          exact
            ⟨pc, instr, emitted, before, after, rfl, hEmitInstr,
              hTargetBlock,
              stepAt_emit_result_sound_withGasOracle hEmitInstr hStep⟩

theorem compile_runN_result_block_trace_sound_withGasOracle
    {program : Program} {target : TargetProgram} {oracle : GasOracle}
    {fuel cursor cursorFinal : Nat} {state : EVMState}
    {result : StepResult}
    (hCompile : compile? program = some target)
    (hRun :
      sourceRunNResultWithGasOracle program oracle fuel cursor state =
        .ok (result, cursorFinal)) :
    Accepted program ∧
      BlockTraceResult program target oracle fuel cursor state result
        cursorFinal := by
  refine ⟨Preservation.compile?_some_accepted hCompile, ?_⟩
  have hAsm := Preservation.compile?_some_assemble hCompile
  induction fuel generalizing cursor state with
  | zero =>
      simp [sourceRunNResultWithGasOracle] at hRun
      rcases hRun with ⟨hResult, hCursor⟩
      subst result
      subst cursorFinal
      exact BlockTraceResult.done cursor state
  | succ fuel ih =>
      unfold sourceRunNResultWithGasOracle at hRun
      cases hStep : sourceStepResultWithGasOracle program oracle cursor state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, cursorMid⟩
          rw [hStep] at hRun
          obtain
            ⟨pc, instr, emitted, before, after,
              hAt, hEmit, hTargetBlock, hBlockRun⟩ :=
            assemble_source_step_current_result_sound_withGasOracle
              hAsm hStep
          cases stepResult with
          | running mid =>
              exact
                BlockTraceResult.stepRunning hAt hEmit hTargetBlock
                  hBlockRun (ih hRun)
          | halted halt =>
              cases hRun
              exact
                BlockTraceResult.stepHalted hAt hEmit hTargetBlock hBlockRun

theorem compile_runN_result_bytecode_bridge_checked_withGasOracle
    {program : Program} {target : TargetProgram} {oracle : GasOracle}
    {fuel cursor cursorFinal : Nat} {state : EVMState}
    {result : StepResult}
    (hCompile : compile? program = some target)
    (hSafety : Bytecode.DecodeSafety target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hRun :
      sourceRunNResultWithGasOracle program oracle fuel cursor state =
        .ok (result, cursorFinal)) :
    Accepted program ∧
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
        BlockTraceResult program target oracle fuel cursor state result
          cursorFinal := by
  obtain ⟨hAccepted, hTrace⟩ :=
    compile_runN_result_block_trace_sound_withGasOracle hCompile hRun
  exact
    ⟨hAccepted,
      Bytecode.compile_encoding_correct_of_jumpdests hCompile hSafety hJumpdest,
      hTrace⟩

end GasParametric

end Assembly
end EvmCompiler
