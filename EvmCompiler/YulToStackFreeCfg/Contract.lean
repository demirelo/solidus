import EvmCompiler.YulToStackFreeCfg.Accepted
import EvmCompiler.StackFreeCfg.Contract

namespace EvmCompiler
namespace YulToStackFreeCfg

/-!
Source-surface contract for the Yul-to-StackFreeCfg boundary.

This module does not prove preservation. It records the exact executable gate
that future preservation proofs should target, and keeps the boundary phrased in
terms of imported Yul syntax plus StackFreeCfg observations.
-/

namespace TargetYul

/--
The imported Yul semantics targeted by this compiler pass.

This is intentionally a value-level record in Lean, so future audits can cite
the concrete dependency being compiled from without chasing `lake-manifest`.
-/
def repository : String :=
  "https://github.com/danrobinson/EVMYulLean.git"

def branch : String :=
  "codex/solidity-loop-post-success-defeq"

def revision : String :=
  "5d7511d768bd35622a9f151324650f57707684f2"

end TargetYul

/--
Reason an imported-Yul contract is outside the currently lowerable bridge
surface.

`coverage` means the AST uses a shape this lowering pass does not support.
`sourceWF` means the source shape is malformed for the Yul/StackFreeCfg source
contract, such as an out-of-scope variable or illegal control effect.
`lowering` means the executable lowerer failed after the source gates passed.
`stackFreeAccepted` means the generated StackFreeCfg program failed the
StackFreeCfg source acceptedness gate.
-/
inductive RejectionReason where
  | coverage
  | sourceWF
  | lowering
  | stackFreeAccepted
  deriving DecidableEq, Repr

inductive LoweringGate where
  | accepted (program : StackFreeCfg.Program)
  | rejected (reason : RejectionReason)
  deriving Repr

namespace LoweringGate

def accepted? : LoweringGate → Bool
  | .accepted _ => true
  | .rejected _ => false

def toProgram? : LoweringGate → Option StackFreeCfg.Program
  | .accepted program => some program
  | .rejected _ => none

end LoweringGate

namespace Contract

/--
The public executable gate for compiling one imported-Yul contract to
StackFreeCfg.

This is deliberately decomposed instead of delegating to `lowerAccepted?`, so
failed checks remain inspectable by the next layer or by tests. It is still a
source-boundary gate, not a preservation theorem.
-/
noncomputable def lowerGate (layout : ObjectLayout)
    (contract : AstContract) : LoweringGate :=
  if Coverage.contract? layout contract then
    if SourceWF.contract? layout contract then
      match lower? layout contract with
      | none => .rejected .lowering
      | some program =>
          if StackFreeCfg.Program.accepted? program then
            .accepted program
          else
            .rejected .stackFreeAccepted
    else
      .rejected .sourceWF
  else
    .rejected .coverage

end Contract

namespace Program

noncomputable def lowerGate (layout : ObjectLayout)
    (program : EvmCompiler.Yul.Program) : LoweringGate :=
  Contract.lowerGate layout program.contract

noncomputable def lowerObserved? (layout : ObjectLayout)
    (prim : StackFreeCfg.PrimitiveSemantics) (fuel : Nat)
    (program : EvmCompiler.Yul.Program)
    (shared : StackFreeCfg.SharedState) :
    Option (Except StackFreeCfg.Exception StackFreeCfg.Observation) :=
  match lowerGate layout program with
  | .accepted lowered =>
      some (StackFreeCfg.Program.runObserved prim fuel lowered shared)
  | .rejected _ => none

end Program

end YulToStackFreeCfg
end EvmCompiler
