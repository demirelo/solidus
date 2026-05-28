import EvmCompiler.Assembly.TopLevel
import EvmCompiler.Assembly.GasParametric

namespace EvmCompiler
namespace Assembly

namespace GasAware

def installCodeAndGas (target : TargetProgram) (gas : Nat)
    (state : EVMState) : EVMState :=
  { state with
    gasAvailable := EvmYul.UInt256.ofNat gas
    executionEnv := { state.executionEnv with code := Bytecode.encodeTarget target }
  }

theorem installCodeAndGas_idempotent (target : TargetProgram) (gas : Nat)
    (state : EVMState) :
    installCodeAndGas target gas (installCodeAndGas target gas state) =
      installCodeAndGas target gas state := by
  simp [installCodeAndGas]

def validJumps (target : TargetProgram) : Array EvmYul.UInt256 :=
  EvmYul.EVM.D_J (Bytecode.encodeTarget target) (EvmYul.UInt256.ofNat 0)

theorem target_fetch_some_exists {target : TargetProgram} {pc : Nat}
    {instr : TargetInstr}
    (hFetch : target.fetch pc = some instr) :
    ∃ located, located ∈ target.code ∧ located.pc = pc ∧
      located.instr = instr := by
  cases target with
  | mk code =>
      unfold TargetProgram.fetch at hFetch
      induction code with
      | nil =>
          simp at hFetch
      | cons head rest ih =>
          by_cases hPc : head.pc = pc
          · simp [hPc] at hFetch
            exact ⟨head, by simp, hPc, by simpa using hFetch⟩
          · simp [hPc] at hFetch
            obtain ⟨located, hMem, hLocatedPc, hInstr⟩ := ih hFetch
            exact ⟨located, by simp [hMem], hLocatedPc, hInstr⟩

theorem decode_installed_of_fetch
    {target : TargetProgram} {gas : Nat} {initial : EVMState}
    {instr : TargetInstr}
    (hEncoding : Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hFetch : target.fetch initial.pc.toNat = some instr) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas initial).toState.executionEnv.code
        (installCodeAndGas target gas initial).pc =
      some (instr.op, instr.arg) := by
  obtain ⟨located, hMem, hPc, hInstr⟩ := target_fetch_some_exists hFetch
  have hDecode := hEncoding.decodes located hMem
  unfold Bytecode.decodeAt at hDecode
  subst instr
  rw [hPc] at hDecode
  simpa [installCodeAndGas, Bytecode.uint256_ofNat_toNat] using hDecode

theorem decode_installed_gas_of_fetch
    {target : TargetProgram} {gas : Nat} {initial : EVMState}
    (hEncoding : Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hFetch : target.fetch initial.pc.toNat = some (.prim .gas)) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas initial).toState.executionEnv.code
        (installCodeAndGas target gas initial).pc =
      some (EvmYul.Operation.GAS, none) := by
  simpa using
    decode_installed_of_fetch (target := target) (gas := gas)
      (initial := initial) (instr := .prim .gas) hEncoding hFetch

/--
Successful `X` results preserve the same non-gas final state as the gasless
source run.  Revert needs a separate output/projection theorem because
EVMYulLean's `ExecutionResult.revert` does not carry the final `EVM.State`.
-/
def XSuccessErasesTo (sourceFinal : EVMState) :
    EvmYul.EVM.ExecutionResult EVMState → Prop
  | .success evmFinal _output => eraseGas evmFinal = eraseGas sourceFinal
  | .revert _gas _output => False

def XRunsSuccessfullyAbove (target : TargetProgram) (initial sourceFinal : EVMState)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gasBound ≤ gas →
      gas < EvmYul.UInt256.size →
        ∃ result,
          EvmYul.EVM.X evmFuel (validJumps target)
              (installCodeAndGas target gas initial) =
            .ok result ∧
            XSuccessErasesTo sourceFinal result

/--
Result-level agreement for the gas-aware `X` runner.

The running case compares gas-erased states and requires the eventual EVM
success output to be empty, matching ordinary non-terminal completion as seen by
message-call return data. Terminal success compares both the gas-erased halted
state and output. Revert in EVMYulLean does not carry the final state, so the
result-level contract compares the revert output and halt kind only.
-/
def XResultAgrees (targetResult : StepResult) :
    EvmYul.EVM.ExecutionResult EVMState → Prop
  | .success evmFinal output =>
      match targetResult with
      | .running state =>
          eraseGas evmFinal = eraseGas state ∧ output = ByteArray.empty
      | .halted halt =>
          halt.kind ≠ .revert ∧
            eraseGas evmFinal = eraseGas halt.state ∧
              output = halt.output
  | .revert _gas output =>
      match targetResult with
      | .running _ => False
      | .halted halt => halt.kind = .revert ∧ output = halt.output

namespace StepResult

def finalState : StepResult → EVMState
  | .running state => state
  | .halted halt => halt.state

def output : StepResult → ByteArray
  | .running _ => ByteArray.empty
  | .halted halt => halt.output

end StepResult

def XExecutionResultOutput :
    EvmYul.EVM.ExecutionResult EVMState → ByteArray
  | .success _ output => output
  | .revert _ output => output

namespace XResultAgrees

theorem output {targetResult : StepResult}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hAgrees : XResultAgrees targetResult result) :
    XExecutionResultOutput result = StepResult.output targetResult := by
  cases result with
  | success evmFinal output =>
      cases targetResult with
      | running state =>
          exact hAgrees.2
      | halted halt =>
          exact hAgrees.2.2
  | revert gas output =>
      cases targetResult with
      | running state =>
          cases hAgrees
      | halted halt =>
          exact hAgrees.2

theorem success_erasesToFinalState {targetResult : StepResult}
    {evmFinal : EVMState} {output : ByteArray}
    (hAgrees : XResultAgrees targetResult (.success evmFinal output)) :
    eraseGas evmFinal = eraseGas (StepResult.finalState targetResult) := by
  cases targetResult with
  | running state =>
      exact hAgrees.1
  | halted halt =>
      exact hAgrees.2.1

theorem success_accountMap {targetResult : StepResult}
    {evmFinal : EVMState} {output : ByteArray}
    (hAgrees : XResultAgrees targetResult (.success evmFinal output)) :
    evmFinal.accountMap =
      (StepResult.finalState targetResult).accountMap := by
  have hErase := success_erasesToFinalState hAgrees
  simpa [eraseGas, StepResult.finalState] using
    congrArg (fun state : EVMState => state.accountMap) hErase

end XResultAgrees

def XRunsResultSuccessfullyAbove (target : TargetProgram) (initial : EVMState)
    (targetResult : StepResult) (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gasBound ≤ gas →
      gas < EvmYul.UInt256.size →
        ∃ result,
          EvmYul.EVM.X evmFuel (validJumps target)
              (installCodeAndGas target gas initial) =
            .ok result ∧
            XResultAgrees targetResult result

/--
The gas-analysis certificate needed to move from the gasless block trace to
EVMYulLean's gas-aware `X` runner.

This is intentionally an assumption interface, not a trusted constant.  A later
proof can replace a caller-provided value of this structure with a computed
bound derived from the finite block trace and EVMYulLean's gas cost functions.
-/
structure SufficientGasForX
    (target : TargetProgram) (initial sourceFinal : EVMState) where
  evmFuel : Nat
  gasBound : Nat
  runsAboveBound : XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound

/--
Alias used at theorem boundaries: these are the explicit gas-aware preconditions
not yet derived from the gasless block trace.
-/
abbrev XPreconditionAssumptions :=
  SufficientGasForX

/--
Result-level gas-analysis certificate for the theorem path whose source
semantics can halt.  This is the explicit gas/resource boundary for connecting
the gasless result trace to EVMYulLean's gas-aware `X` runner.
-/
structure SufficientGasForXResult
    (target : TargetProgram) (initial : EVMState)
    (targetResult : StepResult) where
  evmFuel : Nat
  gasBound : Nat
  runsAboveBound :
    XRunsResultSuccessfullyAbove target initial targetResult evmFuel gasBound

abbrev XResultPreconditionAssumptions :=
  SufficientGasForXResult

@[simp] theorem memoryExpansionCost_gas (state : EVMState) :
    EvmYul.EVM.memoryExpansionCost state EvmYul.Operation.GAS = 0 := by
  unfold EvmYul.EVM.memoryExpansionCost
  change EvmYul.EVM.Cₘ state.activeWords -
      EvmYul.EVM.Cₘ state.activeWords = 0
  exact Nat.sub_self _

@[simp] theorem opcodeCost_gas (state : EVMState) :
    EvmYul.EVM.C' state EvmYul.Operation.GAS = GasConstants.Gbase := by
  rfl

/--
The value that concrete EVM execution exposes to a `GAS` opcode after `X` has
paid the opcode gas cost for the step.

This is the per-request value that the oracle-parametric target semantics must
record for the corresponding dynamic `GAS` request.
-/
def gasAnswerAfterOpcodeCost (state : EVMState) (gasCost : Nat) : Word :=
  state.gasAvailable - EvmYul.UInt256.ofNat gasCost

@[simp] theorem UInt256_sub_zero (value : Word) :
    value - EvmYul.UInt256.ofNat 0 = value := by
  cases value with
  | mk val =>
      change
        EvmYul.UInt256.mk
            (val - (0 : Fin EvmYul.UInt256.size)) =
          EvmYul.UInt256.mk val
      rw [sub_zero]

/--
Local replay fact for the dynamic `GAS` opcode.

`EVM.step` first increments the execution counter and deducts the supplied
opcode gas cost, then the primitive `GAS` semantics pushes the remaining
`gasAvailable`.  If the oracle returns exactly that word at the current cursor,
the oracle-parametric target `GAS` step has the same gas-erased observable
state and advances the oracle cursor by one.
-/
theorem evm_step_gas_matches_oracle_step
    (fuel gasCost cursor : Nat) (state : EVMState)
    (oracle : GasParametric.GasOracle)
    (hOracle : oracle cursor = gasAnswerAfterOpcodeCost state gasCost) :
    ∃ evmFinal targetFinal cursor',
      EvmYul.EVM.step (fuel + 1) gasCost
          (some (EvmYul.Operation.GAS, none)) state = .ok evmFinal ∧
      GasParametric.Target.stepInstrResultWithGasOracle oracle cursor
          (.prim .gas) state = .ok (.running targetFinal, cursor') ∧
      eraseGas evmFinal = eraseGas targetFinal ∧
      cursor' = cursor + 1 := by
  let paidState : EVMState :=
    { state with
      execLength := state.execLength + 1
      gasAvailable := gasAnswerAfterOpcodeCost state gasCost }
  let evmFinal : EVMState :=
    paidState.replaceStackAndIncrPC (state.stack.push paidState.gasAvailable)
  let targetFinal : EVMState :=
    state.replaceStackAndIncrPC (state.stack.push (oracle cursor))
  refine ⟨evmFinal, targetFinal, cursor + 1, ?_, ?_, ?_, rfl⟩
  · rfl
  · simp [targetFinal]
  · simp [evmFinal, targetFinal, paidState, eraseGas, hOracle,
      gasAnswerAfterOpcodeCost, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

/--
One concrete `EVM.X` peel for a decoded `GAS` opcode.

Once `X` decodes `GAS`, the resource precheck charges no memory-expansion gas,
charges the base opcode cost, runs the ordinary EVM step with that base cost, and
then recurses because `GAS` is non-terminal.
-/
theorem evm_X_gas_peel
    (fuel : Nat) (validJumps : Array Word) (state : EVMState)
    (hDecode :
      EvmYul.EVM.decode state.toState.executionEnv.code state.pc =
        some (EvmYul.Operation.GAS, none))
    (hGas : GasConstants.Gbase ≤ state.gasAvailable.toNat)
    (hStack : state.stack.length < 1024) :
    EvmYul.EVM.X (fuel + 2) validJumps state =
      match
        EvmYul.EVM.step (fuel + 1) GasConstants.Gbase
          (some (EvmYul.Operation.GAS, none)) state
      with
      | .ok evmFinal => EvmYul.EVM.X (fuel + 1) validJumps evmFinal
      | .error e => .error e := by
  have hGasCheck : ¬ state.gasAvailable.toNat < GasConstants.Gbase :=
    Nat.not_lt_of_ge hGas
  have hStackCheck : ¬ state.stack.length + 1 > 1024 :=
    Nat.not_lt_of_ge (Nat.succ_le_of_lt hStack)
  conv_lhs =>
    rw [EvmYul.EVM.X]
  simp [hDecode, hGasCheck, hStackCheck,
      EvmYul.EVM.δ, EvmYul.EVM.α, EvmYul.Operation.isCreate]
  change
    (match
        EvmYul.EVM.step (fuel + 1) GasConstants.Gbase
          (some (EvmYul.Operation.GAS, none)) state
      with
      | .ok evmFinal => EvmYul.EVM.X (fuel + 1) validJumps evmFinal
      | .error e => .error e) =
    match
      EvmYul.EVM.step (fuel + 1) GasConstants.Gbase
        (some (EvmYul.Operation.GAS, none)) state
    with
    | .ok evmFinal => EvmYul.EVM.X (fuel + 1) validJumps evmFinal
    | .error e => .error e
  rfl

/--
Concrete `GAS` request replay at the `EVM.X` boundary.

If the bytecode decoder is about to execute `GAS`, and the oracle answer at the
current cursor is the post-cost gas word from the concrete EVM step, then the
oracle-parametric target step consumes exactly that request and matches the
concrete `X` peel after erasing gas accounting fields.
-/
theorem evm_X_gas_request_matches_oracle_step
    (fuel cursor : Nat) (validJumps : Array Word) (state : EVMState)
    (oracle : GasParametric.GasOracle)
    (hDecode :
      EvmYul.EVM.decode state.toState.executionEnv.code state.pc =
        some (EvmYul.Operation.GAS, none))
    (hGas : GasConstants.Gbase ≤ state.gasAvailable.toNat)
    (hStack : state.stack.length < 1024)
    (hOracle :
      oracle cursor = gasAnswerAfterOpcodeCost state GasConstants.Gbase) :
    ∃ evmFinal targetFinal cursor',
      EvmYul.EVM.step (fuel + 1) GasConstants.Gbase
          (some (EvmYul.Operation.GAS, none)) state = .ok evmFinal ∧
      GasParametric.Target.stepInstrResultWithGasOracle oracle cursor
          (.prim .gas) state = .ok (.running targetFinal, cursor') ∧
      EvmYul.EVM.X (fuel + 2) validJumps state =
        EvmYul.EVM.X (fuel + 1) validJumps evmFinal ∧
      eraseGas evmFinal = eraseGas targetFinal ∧
      cursor' = cursor + 1 := by
  obtain ⟨evmFinal, targetFinal, cursor', hStep, hTarget, hErase, hCursor⟩ :=
    evm_step_gas_matches_oracle_step fuel GasConstants.Gbase cursor state
      oracle hOracle
  refine ⟨evmFinal, targetFinal, cursor', hStep, hTarget, ?_, hErase, hCursor⟩
  rw [evm_X_gas_peel fuel validJumps state hDecode hGas hStack, hStep]

/--
One concrete `GAS` request can extend any existing answer stream.

The later whole-run replay proof should build the oracle by extending it at the
current dynamic request cursor.  This lemma removes the pointwise oracle
premise for one decoded `GAS` step: the chosen answer is exactly the concrete
post-cost gas word pushed by the gasful EVM step.
-/
theorem evm_X_gas_request_extends_oracle_step
    (fuel cursor : Nat) (validJumps : Array Word) (state : EVMState)
    (baseOracle : GasParametric.GasOracle)
    (hDecode :
      EvmYul.EVM.decode state.toState.executionEnv.code state.pc =
        some (EvmYul.Operation.GAS, none))
    (hGas : GasConstants.Gbase ≤ state.gasAvailable.toNat)
    (hStack : state.stack.length < 1024) :
    ∃ evmFinal targetFinal cursor',
      EvmYul.EVM.step (fuel + 1) GasConstants.Gbase
          (some (EvmYul.Operation.GAS, none)) state = .ok evmFinal ∧
      GasParametric.Target.stepInstrResultWithGasOracle
          (GasParametric.GasOracle.withAnswer baseOracle cursor
            (gasAnswerAfterOpcodeCost state GasConstants.Gbase))
          cursor (.prim .gas) state =
        .ok (.running targetFinal, cursor') ∧
      EvmYul.EVM.X (fuel + 2) validJumps state =
        EvmYul.EVM.X (fuel + 1) validJumps evmFinal ∧
      eraseGas evmFinal = eraseGas targetFinal ∧
      cursor' = cursor + 1 := by
  exact
    evm_X_gas_request_matches_oracle_step fuel cursor validJumps state
      (GasParametric.GasOracle.withAnswer baseOracle cursor
        (gasAnswerAfterOpcodeCost state GasConstants.Gbase))
      hDecode hGas hStack (by simp)

/--
Installed-code specialization of the concrete `GAS` replay step.

This discharges the decoder premise of `evm_X_gas_request_matches_oracle_step`
from the bytecode encoding proof and the target fetch result, so the request
stream is tied to the compiled code currently installed for `EVM.X`.
-/
theorem evm_X_installed_gas_request_matches_oracle_step
    (fuel cursor gas : Nat) (target : TargetProgram) (initial : EVMState)
    (oracle : GasParametric.GasOracle)
    (hEncoding : Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hFetch : target.fetch initial.pc.toNat = some (.prim .gas))
    (hGas : GasConstants.Gbase ≤
      (installCodeAndGas target gas initial).gasAvailable.toNat)
    (hStack : initial.stack.length < 1024)
    (hOracle :
      oracle cursor =
        gasAnswerAfterOpcodeCost (installCodeAndGas target gas initial)
          GasConstants.Gbase) :
    ∃ evmFinal targetFinal cursor',
      EvmYul.EVM.step (fuel + 1) GasConstants.Gbase
          (some (EvmYul.Operation.GAS, none))
          (installCodeAndGas target gas initial) = .ok evmFinal ∧
      GasParametric.Target.stepInstrResultWithGasOracle oracle cursor
          (.prim .gas) (installCodeAndGas target gas initial) =
        .ok (.running targetFinal, cursor') ∧
      EvmYul.EVM.X (fuel + 2) (validJumps target)
          (installCodeAndGas target gas initial) =
        EvmYul.EVM.X (fuel + 1) (validJumps target) evmFinal ∧
      eraseGas evmFinal = eraseGas targetFinal ∧
      cursor' = cursor + 1 := by
  have hDecode :=
    decode_installed_gas_of_fetch (target := target) (gas := gas)
      (initial := initial) hEncoding hFetch
  have hStackInstalled :
      (installCodeAndGas target gas initial).stack.length < 1024 := by
    simpa [installCodeAndGas] using hStack
  exact
    evm_X_gas_request_matches_oracle_step fuel cursor (validJumps target)
      (installCodeAndGas target gas initial) oracle hDecode hGas
      hStackInstalled hOracle

/--
Installed-code version of `evm_X_gas_request_extends_oracle_step`.

For a target fetch of `.prim .gas`, the compiled bytecode decoder sees EVM
`GAS`, and extending the answer stream at the current cursor with the concrete
post-base-cost gas word is enough to replay this dynamic request.
-/
theorem evm_X_installed_gas_request_extends_oracle_step
    (fuel cursor gas : Nat) (target : TargetProgram) (initial : EVMState)
    (baseOracle : GasParametric.GasOracle)
    (hEncoding : Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hFetch : target.fetch initial.pc.toNat = some (.prim .gas))
    (hGas : GasConstants.Gbase ≤
      (installCodeAndGas target gas initial).gasAvailable.toNat)
    (hStack : initial.stack.length < 1024) :
    ∃ evmFinal targetFinal cursor',
      EvmYul.EVM.step (fuel + 1) GasConstants.Gbase
          (some (EvmYul.Operation.GAS, none))
          (installCodeAndGas target gas initial) = .ok evmFinal ∧
      GasParametric.Target.stepInstrResultWithGasOracle
          (GasParametric.GasOracle.withAnswer baseOracle cursor
            (gasAnswerAfterOpcodeCost (installCodeAndGas target gas initial)
              GasConstants.Gbase))
          cursor (.prim .gas) (installCodeAndGas target gas initial) =
        .ok (.running targetFinal, cursor') ∧
      EvmYul.EVM.X (fuel + 2) (validJumps target)
          (installCodeAndGas target gas initial) =
        EvmYul.EVM.X (fuel + 1) (validJumps target) evmFinal ∧
      eraseGas evmFinal = eraseGas targetFinal ∧
      cursor' = cursor + 1 := by
  exact
    evm_X_installed_gas_request_matches_oracle_step fuel cursor gas target
      initial
      (GasParametric.GasOracle.withAnswer baseOracle cursor
        (gasAnswerAfterOpcodeCost (installCodeAndGas target gas initial)
          GasConstants.Gbase))
      hEncoding hFetch hGas hStack (by simp)

/--
Oracle-parametric target run evidence at the lower `X` boundary.

This does not yet prove that `EVM.X` itself produced the `oracle` answers.
It prevents the oracle/cursor from being merely decorative in the boundary:
the result being compared to `X` must also be reachable by running the target
program under that exact answer stream and cursor discipline.
-/
def TargetOracleResultRun (target : TargetProgram)
    (oracle : GasParametric.GasOracle) (cursor : Nat)
    (initial : EVMState) (targetResult : StepResult) (cursorFinal : Nat) :
    Prop :=
  ∃ targetFuel,
    GasParametric.Target.runNResultWithGasOracle target oracle targetFuel
        cursor initial =
      .ok (targetResult, cursorFinal)

namespace TargetOracleResultRun

theorem withAnswer_of_cursorFinal_le
    {target : TargetProgram} {oracle : GasParametric.GasOracle}
    {cursor answerCursor : Nat} {answer : Word} {initial : EVMState}
    {targetResult : StepResult} {cursorFinal : Nat}
    (hRun :
      TargetOracleResultRun target oracle cursor initial targetResult
        cursorFinal)
    (hLe : cursorFinal ≤ answerCursor) :
    TargetOracleResultRun target
        (GasParametric.GasOracle.withAnswer oracle answerCursor answer)
        cursor initial targetResult cursorFinal := by
  rcases hRun with ⟨targetFuel, hTargetRun⟩
  exact
    ⟨targetFuel,
      GasParametric.Target.runNResultWithGasOracle_withAnswer_of_run_le
        (answer := answer) hTargetRun hLe⟩

end TargetOracleResultRun

/--
Concrete-gas `X` agreement for an oracle-parametric assembly result.

The oracle and cursors are part of the surrounding run evidence; `EVM.X` itself
does not take an oracle.  The eventual replay proof must show that the concrete
gasful run induces those oracle answers at the dynamic `GAS` instructions, and
that its gas-erased execution is the target oracle run named by the first
conjunct.
-/
def XRunsOracleResultSuccessfullyAtGas (target : TargetProgram)
    (initial : EVMState) (gas : Nat) (oracle : GasParametric.GasOracle)
    (cursor : Nat) (targetResult : StepResult) (cursorFinal : Nat)
    (evmFuel : Nat) : Prop :=
  TargetOracleResultRun target oracle cursor initial targetResult
      cursorFinal ∧
    ∃ result,
      EvmYul.EVM.X evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok result ∧
      XResultAgrees targetResult result

namespace XRunsOracleResultSuccessfullyAtGas

theorem withAnswer_of_cursorFinal_le
    {target : TargetProgram} {initial : EVMState} {gas : Nat}
    {oracle : GasParametric.GasOracle} {cursor answerCursor : Nat}
    {answer : Word} {targetResult : StepResult} {cursorFinal evmFuel : Nat}
    (hRuns :
      XRunsOracleResultSuccessfullyAtGas target initial gas oracle cursor
        targetResult cursorFinal evmFuel)
    (hLe : cursorFinal ≤ answerCursor) :
    XRunsOracleResultSuccessfullyAtGas target initial gas
        (GasParametric.GasOracle.withAnswer oracle answerCursor answer)
        cursor targetResult cursorFinal evmFuel := by
  exact
    ⟨TargetOracleResultRun.withAnswer_of_cursorFinal_le
        (answer := answer) hRuns.1 hLe,
      hRuns.2⟩

end XRunsOracleResultSuccessfullyAtGas

/--
Sufficient-gas package for the oracle-parametric route.

The target result here is produced by `Assembly.GasParametric`, so any observed
`GAS` values have already been fixed by the explicit oracle.  Unlike the older
gasless sufficient-gas package, this route is for one installed gas amount:
different starting gas can make `GAS` push different words, so a future
gas-aware `EVM.X` adequacy proof should instantiate the oracle for the concrete
gasful run being compared.
-/
structure SufficientGasForXOracleResult
    (target : TargetProgram) (initial : EVMState)
    (gas : Nat) (oracle : GasParametric.GasOracle) (cursor : Nat)
    (targetResult : StepResult) (cursorFinal : Nat) where
  evmFuel : Nat
  gasBound : Nat
  gasAboveBound : gasBound ≤ gas
  gasFitsUInt256 : gas < EvmYul.UInt256.size
  runsAtGas :
    XRunsOracleResultSuccessfullyAtGas target initial gas oracle cursor
      targetResult cursorFinal evmFuel

abbrev XOracleResultPreconditionAssumptions :=
  SufficientGasForXOracleResult

namespace SufficientGasForXOracleResult

def withAnswer_of_cursorFinal_le
    {target : TargetProgram} {initial : EVMState} {gas : Nat}
    {oracle : GasParametric.GasOracle} {cursor answerCursor : Nat}
    {answer : Word} {targetResult : StepResult} {cursorFinal : Nat}
    (hGasForX :
      SufficientGasForXOracleResult target initial gas oracle cursor
        targetResult cursorFinal)
    (hLe : cursorFinal ≤ answerCursor) :
    SufficientGasForXOracleResult target initial gas
        (GasParametric.GasOracle.withAnswer oracle answerCursor answer)
        cursor targetResult cursorFinal where
  evmFuel := hGasForX.evmFuel
  gasBound := hGasForX.gasBound
  gasAboveBound := hGasForX.gasAboveBound
  gasFitsUInt256 := hGasForX.gasFitsUInt256
  runsAtGas :=
    XRunsOracleResultSuccessfullyAtGas.withAnswer_of_cursorFinal_le
      (answer := answer) hGasForX.runsAtGas hLe

end SufficientGasForXOracleResult

theorem SufficientGasForXResult.runsAtInstalledGas {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult} {gas : Nat}
    (hGasForX :
      SufficientGasForXResult target (installCodeAndGas target gas initial)
        targetResult)
    (hGas : hGasForX.gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    ∃ result,
      EvmYul.EVM.X hGasForX.evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok result ∧
      XResultAgrees targetResult result := by
  simpa [installCodeAndGas_idempotent] using
    hGasForX.runsAboveBound gas hGas hUInt256

theorem SufficientGasForXOracleResult.runsAtInstalledGas
    {target : TargetProgram} {initial : EVMState}
    {gas : Nat} {oracle : GasParametric.GasOracle} {cursor : Nat}
    {targetResult : StepResult} {cursorFinal : Nat}
    (hGasForX :
      SufficientGasForXOracleResult target
        (installCodeAndGas target gas initial) gas oracle cursor targetResult
        cursorFinal) :
    ∃ result,
      EvmYul.EVM.X hGasForX.evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok result ∧
      XResultAgrees targetResult result := by
  simpa [installCodeAndGas_idempotent,
    XRunsOracleResultSuccessfullyAtGas] using hGasForX.runsAtGas.2

theorem XRunsSuccessfullyAbove.not_out_of_gas {target : TargetProgram}
    {initial sourceFinal : EVMState} {evmFuel gasBound gas : Nat}
    (hRuns : XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound)
    (hGas : gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    EvmYul.EVM.X evmFuel (validJumps target)
        (installCodeAndGas target gas initial) ≠
      .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain ⟨result, hRun, _hProject⟩ := hRuns gas hGas hUInt256
  rw [hRun]
  intro hImpossible
  cases hImpossible

theorem XRunsResultSuccessfullyAbove.not_out_of_gas {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    {evmFuel gasBound gas : Nat}
    (hRuns :
      XRunsResultSuccessfullyAbove target initial targetResult evmFuel
        gasBound)
    (hGas : gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    EvmYul.EVM.X evmFuel (validJumps target)
        (installCodeAndGas target gas initial) ≠
      .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain ⟨result, hRun, _hProject⟩ := hRuns gas hGas hUInt256
  rw [hRun]
  intro hImpossible
  cases hImpossible

theorem compile_whole_program_result_X_withGasOracle {program : Program}
    {target : TargetProgram} {oracle : GasParametric.GasOracle}
    {fuel gas cursor cursorFinal : Nat} {initial : EVMState}
    {targetResult : StepResult}
    (hCompile : compile? program = some target)
    (hDecodeWindow : Bytecode.TargetFitsDecodeWindow target)
    (hJumpdestCorrect : Bytecode.JumpdestCorrect target)
    (hRun :
      GasParametric.sourceRunNResultWithGasOracle program oracle fuel cursor
          initial =
        .ok (targetResult, cursorFinal))
    (hPreconditions :
      XOracleResultPreconditionAssumptions target initial gas oracle cursor
        targetResult cursorFinal) :
    Accepted program ∧
      Bytecode.compileBytes? program = some (Bytecode.encodeTarget target) ∧
        Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
          target.GasOpcodeBoundary ∧
            GasParametric.BlockTraceResult program target oracle fuel cursor
              initial targetResult cursorFinal ∧
              TargetOracleResultRun target oracle cursor initial targetResult
                cursorFinal ∧
              hPreconditions.gasBound ≤ gas ∧
                gas < EvmYul.UInt256.size ∧
                  ∃ result,
                    EvmYul.EVM.X hPreconditions.evmFuel (validJumps target)
                        (installCodeAndGas target gas initial) =
                      .ok result ∧
                      XResultAgrees targetResult result := by
  obtain ⟨hAccepted, hEncoding, hTrace⟩ :=
    GasParametric.compile_runN_result_bytecode_bridge_checked_withGasOracle
      hCompile (Bytecode.compile_decodeSafety hCompile hDecodeWindow)
      hJumpdestCorrect hRun
  refine
    ⟨hAccepted, ?_, hEncoding, TargetProgram.gas_opcode_boundary target,
      hTrace, hPreconditions.runsAtGas.1, ?_⟩
  · simp [Bytecode.compileBytes?, hCompile]
  · exact
      ⟨hPreconditions.gasAboveBound, hPreconditions.gasFitsUInt256,
        hPreconditions.runsAtGas.2⟩

/--
Reusable package produced by the gas-aware bridge theorem.

Higher compiler layers should depend on this structure rather than destructing
large conjunctions: it names the bytecode facts, runtime-boundary facts,
gasless block trace, and sufficient-gas `X` behavior that the bridge provides.
-/
structure XBridgeCertificate
    (program : Program) (target : TargetProgram) (fuel : Nat)
    (initial sourceFinal : EVMState) : Prop where
  accepted : Accepted program
  compileBytes_eq : Bytecode.compileBytes? program = some (Bytecode.encodeTarget target)
  encodingCorrect : Bytecode.EncodingCorrect target (Bytecode.encodeTarget target)
  gasOpcodeBoundary : target.GasOpcodeBoundary
  gasOracle : GasOracleAssumption program initial
  outOfGasPolicy : OutOfGasPolicyAssumption program initial
  currentContractProjection : CurrentContractProjectionAssumption program initial
  externalInteraction : ExternalInteractionAssumption program target initial
  blockTrace :
    ∃ targetFinal,
      Preservation.BlockTrace program target fuel initial targetFinal ∧
        eraseGas targetFinal = eraseGas sourceFinal
  sufficientGas :
    ∃ evmFuel gasBound,
      XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound

namespace XBridgeCertificate

theorem exists_sufficient_gas {program : Program} {target : TargetProgram}
    {fuel : Nat} {initial sourceFinal : EVMState}
    (cert : XBridgeCertificate program target fuel initial sourceFinal) :
    ∃ evmFuel gasBound,
      ∀ gas,
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            ∃ result,
              EvmYul.EVM.X evmFuel (validJumps target)
                  (installCodeAndGas target gas initial) =
                .ok result ∧
                XSuccessErasesTo sourceFinal result :=
  cert.sufficientGas

theorem not_out_of_gas_above_bound {program : Program} {target : TargetProgram}
    {fuel : Nat} {initial sourceFinal : EVMState}
    (cert : XBridgeCertificate program target fuel initial sourceFinal) :
    ∃ evmFuel gasBound,
      ∀ gas,
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (validJumps target)
                (installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain ⟨evmFuel, gasBound, hRuns⟩ := cert.sufficientGas
  exact
    ⟨evmFuel, gasBound, fun gas hGas hUInt256 =>
      hRuns.not_out_of_gas hGas hUInt256⟩

end XBridgeCertificate

/--
Primary gas-aware bridge theorem.

This theorem packages the existing compiler-correctness theorem together with
the explicit `XPreconditionAssumptions` certificate into a single named
artifact for higher compiler layers.
-/
theorem compile_whole_program_X_bridge {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hPreconditions : XPreconditionAssumptions target initial sourceFinal) :
    XBridgeCertificate program target fuel initial sourceFinal := by
  obtain
    ⟨hAccepted, hBytes, hEncoding, hGasOpcode,
      hGasOracle, hOutOfGas, hProjection,
      targetFinal, hTrace, hErase⟩ :=
    compile_whole_program_sound hCompile hRuntime hRun
  exact
    { accepted := hAccepted
      compileBytes_eq := hBytes
      encodingCorrect := hEncoding
      gasOpcodeBoundary := hGasOpcode
      gasOracle := hGasOracle
      outOfGasPolicy := hOutOfGas
      currentContractProjection := hProjection
      externalInteraction := hRuntime.externalInteraction
      blockTrace := ⟨targetFinal, hTrace, hErase⟩
      sufficientGas :=
        ⟨hPreconditions.evmFuel, hPreconditions.gasBound,
          hPreconditions.runsAboveBound⟩ }

/--
Gas-aware whole-program bridge to EVMYulLean `X`.

The compiler proof supplies the accepted-program, bytecode, and gas-erased
block-trace facts.  `SufficientGasForX` supplies the remaining gas-aware runner
analysis: an EVM fuel amount and a gas bound such that every larger UInt256 gas
input makes `X` return successfully and project to the same non-gas result.
-/
theorem compile_whole_program_X_sufficient_gas {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hSufficientGas : SufficientGasForX target initial sourceFinal) :
    Accepted program ∧
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
        ∃ targetFinal evmFuel gasBound,
          Preservation.BlockTrace program target fuel initial targetFinal ∧
            eraseGas targetFinal = eraseGas sourceFinal ∧
              XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound ∧
                ∀ gas,
                  gasBound ≤ gas →
                  gas < EvmYul.UInt256.size →
                      EvmYul.EVM.X evmFuel (validJumps target)
                          (installCodeAndGas target gas initial) ≠
                        .error EvmYul.EVM.ExecutionException.OutOfGass := by
  let cert :=
    compile_whole_program_X_bridge hCompile hRuntime hRun hSufficientGas
  obtain ⟨targetFinal, hTrace, hErase⟩ := cert.blockTrace
  obtain ⟨evmFuel, gasBound, hRuns⟩ := cert.sufficientGas
  refine
    ⟨cert.accepted, cert.encodingCorrect, targetFinal, evmFuel,
      gasBound, hTrace, hErase, hRuns, ?_⟩
  intro gas hGas hUInt256
  exact hRuns.not_out_of_gas hGas hUInt256

/--
Direct existential sufficient-gas statement for EVMYulLean `X`.

Under the bytecode/runtime assumptions and the explicit gas-aware `X`
preconditions, successful source execution implies that there is an EVM fuel
and gas bound such that every larger UInt256 gas input makes `X` return
successfully and preserve the gas-erased final state.
-/
theorem compile_whole_program_X_exists_sufficient_gas {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hPreconditions : XPreconditionAssumptions target initial sourceFinal) :
    Accepted program ∧
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
        ∃ evmFuel gasBound,
          ∀ gas,
            gasBound ≤ gas →
              gas < EvmYul.UInt256.size →
                ∃ result,
                  EvmYul.EVM.X evmFuel (validJumps target)
                      (installCodeAndGas target gas initial) =
                    .ok result ∧
                    XSuccessErasesTo sourceFinal result := by
  let cert := compile_whole_program_X_bridge hCompile hRuntime hRun hPreconditions
  obtain ⟨evmFuel, gasBound, hRuns⟩ := cert.exists_sufficient_gas
  exact ⟨cert.accepted, cert.encodingCorrect, evmFuel, gasBound, hRuns⟩

/--
No-out-of-gas corollary for callers that only need the gas safety part of the
`X` bridge.  The stronger theorem above additionally returns a successful
`ExecutionResult` with the gas-erased projection.
-/
theorem compile_whole_program_X_no_out_of_gas_above_bound {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hPreconditions : XPreconditionAssumptions target initial sourceFinal) :
    Accepted program ∧
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
        ∃ evmFuel gasBound,
          ∀ gas,
            gasBound ≤ gas →
              gas < EvmYul.UInt256.size →
                EvmYul.EVM.X evmFuel (validJumps target)
                    (installCodeAndGas target gas initial) ≠
                  .error EvmYul.EVM.ExecutionException.OutOfGass := by
  let cert := compile_whole_program_X_bridge hCompile hRuntime hRun hPreconditions
  obtain ⟨evmFuel, gasBound, hNoOutOfGas⟩ := cert.not_out_of_gas_above_bound
  exact ⟨cert.accepted, cert.encodingCorrect, evmFuel, gasBound, hNoOutOfGas⟩

end GasAware

end Assembly
end EvmCompiler
