import EvmCompiler.Assembly.TopLevel

namespace EvmCompiler
namespace Assembly

namespace GasAware

def installCodeAndGas (target : TargetProgram) (gas : Nat)
    (state : EVMState) : EVMState :=
  { state with
    gasAvailable := EvmYul.UInt256.ofNat gas
    executionEnv := { state.executionEnv with code := Bytecode.encodeTarget target }
  }

def validJumps (target : TargetProgram) : Array EvmYul.UInt256 :=
  EvmYul.EVM.D_J (Bytecode.encodeTarget target) (EvmYul.UInt256.ofNat 0)

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

The running case compares gas-erased states. Terminal success compares both the
gas-erased halted state and output. Revert in EVMYulLean does not carry the
final state, so the result-level contract compares the revert output and halt
kind only.
-/
def XResultAgrees (targetResult : StepResult) :
    EvmYul.EVM.ExecutionResult EVMState → Prop
  | .success evmFinal output =>
      match targetResult with
      | .running state => eraseGas evmFinal = eraseGas state
      | .halted halt =>
          halt.kind ≠ .revert ∧
            eraseGas evmFinal = eraseGas halt.state ∧
              output = halt.output
  | .revert _gas output =>
      match targetResult with
      | .running _ => False
      | .halted halt => halt.kind = .revert ∧ output = halt.output

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
