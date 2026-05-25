import EvmCompiler.Objects.Syntax
import EvmCompiler.Functions.Compiler

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

def compile? (program : Program) :
    Option Assembly.TargetProgram :=
  Functions.Inline.Program.compile? program.toFunctions

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

end Objects
end EvmCompiler
