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
  obtain
    ⟨hAccepted, _hBytes, hEncoding, _hNoGas, _hNoExternal,
      _hGasOracle, _hOutsideWorld, _hOutOfGas, _hProjection,
      targetFinal, hTrace, hErase⟩ :=
    compile_whole_program_sound hCompile hRuntime hRun
  refine
    ⟨hAccepted, hEncoding, targetFinal, hSufficientGas.evmFuel,
      hSufficientGas.gasBound, hTrace, hErase,
      hSufficientGas.runsAboveBound, ?_⟩
  intro gas hGas hUInt256
  exact hSufficientGas.runsAboveBound.not_out_of_gas hGas hUInt256

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
  obtain
    ⟨hAccepted, hEncoding, _targetFinal, evmFuel, gasBound,
      _hTrace, _hErase, hRuns, _hNoOutOfGas⟩ :=
    compile_whole_program_X_sufficient_gas hCompile hRuntime hRun hPreconditions
  exact ⟨hAccepted, hEncoding, evmFuel, gasBound, hRuns⟩

end GasAware

end Assembly
end EvmCompiler
