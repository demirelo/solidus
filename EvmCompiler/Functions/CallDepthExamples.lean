import EvmCompiler.Functions.CallDepth

namespace EvmCompiler
namespace Functions
namespace CallDepth
namespace Examples

def emptyBlock : Block :=
  { stmts := [] }

def leaf : FunDef :=
  { name := "leaf"
    params := []
    returns := []
    body := emptyBlock }

def mid : FunDef :=
  { name := "mid"
    params := []
    returns := []
    body := { stmts := [.call [] "leaf" []] } }

def root : FunDef :=
  { name := "root"
    params := []
    returns := []
    body := { stmts := [.call [] "mid" []] } }

def acyclicProgram : Program :=
  { functions := [root, mid, leaf]
    body := { stmts := [.call [] "root" []] } }

example :
    Program.maxInternalCallDepth? acyclicProgram = some 3 := by
  native_decide

example :
    (Program.stackDepthCheck? acyclicProgram).isSome = true := by
  native_decide

def recursive : FunDef :=
  { name := "loop"
    params := []
    returns := []
    body := { stmts := [.call [] "loop" []] } }

def recursiveProgram : Program :=
  { functions := [recursive]
    body := { stmts := [.call [] "loop" []] } }

example :
    Program.maxInternalCallDepth? recursiveProgram = none := by
  native_decide

example :
    (Program.stackDepthCheck? recursiveProgram).isNone = true := by
  native_decide

def mutualA : FunDef :=
  { name := "mutualA"
    params := []
    returns := []
    body := { stmts := [.call [] "mutualB" []] } }

def mutualB : FunDef :=
  { name := "mutualB"
    params := []
    returns := []
    body := { stmts := [.call [] "mutualA" []] } }

def mutualRecursiveProgram : Program :=
  { functions := [mutualA, mutualB]
    body := { stmts := [.call [] "mutualA" []] } }

example :
    Program.maxInternalCallDepth? mutualRecursiveProgram = none := by
  native_decide

example :
    (Program.stackDepthCheck? mutualRecursiveProgram).isNone = true := by
  native_decide

def unresolvedProgram : Program :=
  { functions := []
    body := { stmts := [.call [] "missing" []] } }

example :
    Program.maxInternalCallDepth? unresolvedProgram = none := by
  native_decide

def chainName (index : Nat) : Name :=
  s!"chain_{index}"

def chainFunctionsFrom : Nat → Nat → List FunDef
  | 0, _index => []
  | count + 1, index =>
      { name := chainName index
        params := []
        returns := []
        body :=
          if count = 0 then
            emptyBlock
          else
            { stmts := [.call [] (chainName (index + 1)) []] } } ::
        chainFunctionsFrom count (index + 1)

def chainProgram (count : Nat) : Program :=
  { functions := chainFunctionsFrom count 0
    body :=
      if count = 0 then
        emptyBlock
      else
        { stmts := [.call [] (chainName 0) []] } }

example :
    Program.maxInternalCallDepth? (chainProgram 58) = some 58 := by
  native_decide

example :
    Program.stackResourceChecked (chainProgram 58) = true := by
  native_decide

example :
    Program.maxInternalCallDepth? (chainProgram 59) = some 59 := by
  native_decide

example :
    Program.stackResourceChecked (chainProgram 59) = false := by
  native_decide

end Examples
end CallDepth
end Functions
end EvmCompiler
