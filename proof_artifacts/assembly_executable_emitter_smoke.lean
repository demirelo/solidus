import EvmCompiler.Assembly.Accepted

open EvmCompiler

namespace AssemblyExecutableEmitterSmoke

def largeProgram : Assembly.Program :=
  (List.range 12000).map fun _ => Assembly.Instr.prim .pop

def largeExecutableEmissionLength : Option Nat :=
  (Assembly.emitExecutable? largeProgram).map List.length

example : largeExecutableEmissionLength = some 12000 := by
  native_decide

def largeExecutableCompileLength : Option Nat :=
  (Assembly.compileExecutable? largeProgram).map fun target => target.code.length

example : largeExecutableCompileLength = some 12000 := by
  native_decide

end AssemblyExecutableEmitterSmoke
