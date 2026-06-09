import EvmCompiler.Objects.Syntax
import EvmCompiler.Functions.CallAwareSpill
import EvmCompiler.Functions.Compiler
import EvmCompiler.Functions.ScratchFrameSpill

namespace EvmCompiler
namespace Objects

namespace Object

def toFunctions (object : Object) : Functions.Program :=
  object.code

theorem toFunctions_wf {object : Object}
    (hWF : object.WF) :
    object.toFunctions.WF := by
  cases object with
  | mk name code data objects =>
      exact hWF.left

end Object

namespace Program

def toFunctions (program : Program) : Functions.Program :=
  program.root.toFunctions

def toExpressions? (program : Program) : Option Expressions.Program :=
  Functions.Inline.Program.toExpressions? program.toFunctions

def callAwareSpillFallbackScratchWords : Nat :=
  64

def scratchFrameSpillFallbackWords : Nat :=
  8192

def compileCallAwareSpillFallback? (program : Program) :
    Option Assembly.TargetProgram := do
  let (_range, _plan, _exprProgram, target) ←
    Functions.CallAwareSpill.compileTargetPlannedPrealloc?
      callAwareSpillFallbackScratchWords program.toFunctions
  some target

def compileCallAwareSpillWithSwitchFallback? (program : Program) :
    Option Assembly.TargetProgram := do
  let (_range, _plan, _exprProgram, target) ←
    Functions.CallAwareSpill.compileTargetPlannedPreallocWithSwitchFallback?
      callAwareSpillFallbackScratchWords program.toFunctions
  some target

def compileScratchFrameSpillFallback? (program : Program) :
    Option Assembly.TargetProgram :=
  Functions.ScratchFrameSpill.compileTarget?
    scratchFrameSpillFallbackWords program.toFunctions

def compile? (program : Program) :
    Option Assembly.TargetProgram :=
  match Functions.Inline.Program.compileExecutable? program.toFunctions with
  | some target => some target
  | none =>
      match compileCallAwareSpillFallback? program with
      | some target => some target
      | none =>
          match compileCallAwareSpillWithSwitchFallback? program with
          | some target => some target
          | none => compileScratchFrameSpillFallback? program

def Accepted (program : Program) : Prop :=
  program.WF ∧ Functions.Inline.Program.Accepted program.toFunctions

def SourceAccepted (program : Program) : Prop :=
  program.WF ∧ Functions.Inline.Program.SourceAccepted program.toFunctions

theorem sourceAccepted_of_accepted {program : Program}
    (hAccepted : Accepted program) :
    SourceAccepted program :=
  ⟨hAccepted.1,
    Functions.Inline.Program.sourceAccepted_of_accepted hAccepted.2⟩

theorem toFunctions_wf {program : Program}
    (hWF : program.WF) :
    program.toFunctions.WF := by
  exact Object.toFunctions_wf hWF

end Program

namespace SourceAcceptedCheck

mutual
  def Object.wf? : Objects.Object → Bool
    | .mk _name code _data objects =>
        Functions.SourceAcceptedCheck.Program.wf? code &&
          ObjectList.wf? objects

  def ObjectList.wf? : List Objects.Object → Bool
    | [] => true
    | object :: rest => Object.wf? object && ObjectList.wf? rest
end

namespace Program

def wf? (program : Objects.Program) : Bool :=
  Object.wf? program.root

def sourceAccepted? (program : Objects.Program) : Bool :=
  wf? program &&
    Functions.SourceAcceptedCheck.Program.sourceAccepted? program.toFunctions

end Program

mutual
  theorem Object.wf_of_check :
      ∀ {object : Objects.Object},
        Object.wf? object = true →
          object.WF := by
    intro object hCheck
    cases object with
    | mk name code data objects =>
        have hAnd :
            Functions.SourceAcceptedCheck.Program.wf? code = true ∧
              ObjectList.wf? objects = true :=
          by simpa [Object.wf?] using hCheck
        exact
          ⟨Functions.SourceAcceptedCheck.Program.wf_of_check hAnd.1,
            ObjectList.wf_of_check hAnd.2⟩

  theorem ObjectList.wf_of_check :
      ∀ {objects : List Objects.Object},
        ObjectList.wf? objects = true →
          Objects.ObjectList.WF objects := by
    intro objects hCheck
    cases objects with
    | nil =>
        trivial
    | cons object rest =>
        have hAnd :
            Object.wf? object = true ∧ ObjectList.wf? rest = true :=
          by simpa [ObjectList.wf?] using hCheck
        exact
          ⟨Object.wf_of_check hAnd.1,
            ObjectList.wf_of_check hAnd.2⟩
end

theorem Program.wf_of_check {program : Objects.Program}
    (hCheck : Program.wf? program = true) :
    program.WF := by
  exact Object.wf_of_check hCheck

theorem Program.sourceAccepted_of_check {program : Objects.Program}
    (hCheck : Program.sourceAccepted? program = true) :
    program.SourceAccepted := by
  have hAnd :
      Program.wf? program = true ∧
        Functions.SourceAcceptedCheck.Program.sourceAccepted?
            program.toFunctions =
          true :=
    by simpa [Program.sourceAccepted?] using hCheck
  exact
    ⟨Program.wf_of_check hAnd.1,
      Functions.SourceAcceptedCheck.Program.sourceAccepted_of_check hAnd.2⟩

end SourceAcceptedCheck

end Objects
end EvmCompiler
