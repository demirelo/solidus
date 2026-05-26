import EvmCompiler.TypedCfg.Semantics
import EvmCompiler.Assembly.Accepted

namespace EvmCompiler
namespace TypedCfg

namespace ProcLabel

def dispatch (name : Name) : Label :=
  Assembly.Label.named ("typedcfg:proc:" ++ name ++ ":dispatch")

def dispatchCase (name : Name) (idx : Nat) : Label :=
  Assembly.Label.named
    ("typedcfg:proc:" ++ name ++ ":dispatch:" ++ toString idx)

end ProcLabel

structure CallSite where
  callLabel : Label
  procName : Name
  token : Word
  returnLabel : Label
  deriving DecidableEq, Repr

namespace CallSite

def forProc (name : Name) (site : CallSite) : Bool :=
  decide (site.procName = name)

end CallSite

namespace StackShuffle

def swapInstr? : Nat → Option Assembly.Instr
  | 1 => some (.prim .swap1)
  | 2 => some (.prim .swap2)
  | 3 => some (.prim .swap3)
  | 4 => some (.prim .swap4)
  | 5 => some (.prim .swap5)
  | 6 => some (.prim .swap6)
  | 7 => some (.prim .swap7)
  | 8 => some (.prim .swap8)
  | 9 => some (.prim .swap9)
  | 10 => some (.prim .swap10)
  | 11 => some (.prim .swap11)
  | 12 => some (.prim .swap12)
  | 13 => some (.prim .swap13)
  | 14 => some (.prim .swap14)
  | 15 => some (.prim .swap15)
  | 16 => some (.prim .swap16)
  | _ => none

def dupInstr? : Nat → Option Assembly.Instr
  | 1 => some (.prim .dup1)
  | 2 => some (.prim .dup2)
  | 3 => some (.prim .dup3)
  | 4 => some (.prim .dup4)
  | 5 => some (.prim .dup5)
  | 6 => some (.prim .dup6)
  | 7 => some (.prim .dup7)
  | 8 => some (.prim .dup8)
  | 9 => some (.prim .dup9)
  | 10 => some (.prim .dup10)
  | 11 => some (.prim .dup11)
  | 12 => some (.prim .dup12)
  | 13 => some (.prim .dup13)
  | 14 => some (.prim .dup14)
  | 15 => some (.prim .dup15)
  | 16 => some (.prim .dup16)
  | _ => none

def sinkTopUnder? : Nat → Option Assembly.Program
  | 0 => some []
  | depth + 1 => do
      let instr ← swapInstr? (depth + 1)
      let rest ← sinkTopUnder? depth
      some (instr :: rest)

def liftBuriedToTop? : Nat → Option Assembly.Program
  | 0 => some []
  | depth + 1 => do
      let rest ← liftBuriedToTop? depth
      let instr ← swapInstr? (depth + 1)
      some (rest ++ [instr])

def removeBuriedUnder? (depth : Nat) : Option Assembly.Program := do
  let code ← liftBuriedToTop? depth
  some (code ++ [.prim .pop])

def removeManyBuriedUnder? (depth : Nat) :
    Nat → Option Assembly.Program
  | 0 => some []
  | count + 1 => do
      let head ← removeBuriedUnder? depth
      let tail ← removeManyBuriedUnder? depth count
      some (head ++ tail)

end StackShuffle

namespace Instr

def pushZeros : Nat → Assembly.Program
  | 0 => []
  | n + 1 => .push (EvmYul.UInt256.ofNat 0) :: pushZeros n

def popMany : Nat → Assembly.Program
  | 0 => []
  | n + 1 => .prim .pop :: popMany n

def dup? : Nat → Option Assembly.Program
  | 0 => some [.prim .dup1]
  | 1 => some [.prim .dup2]
  | 2 => some [.prim .dup3]
  | 3 => some [.prim .dup4]
  | 4 => some [.prim .dup5]
  | 5 => some [.prim .dup6]
  | 6 => some [.prim .dup7]
  | 7 => some [.prim .dup8]
  | 8 => some [.prim .dup9]
  | 9 => some [.prim .dup10]
  | 10 => some [.prim .dup11]
  | 11 => some [.prim .dup12]
  | 12 => some [.prim .dup13]
  | 13 => some [.prim .dup14]
  | 14 => some [.prim .dup15]
  | 15 => some [.prim .dup16]
  | _ => none

def swap? : Nat → Option Assembly.Program
  | 0 => some [.prim .swap1]
  | 1 => some [.prim .swap2]
  | 2 => some [.prim .swap3]
  | 3 => some [.prim .swap4]
  | 4 => some [.prim .swap5]
  | 5 => some [.prim .swap6]
  | 6 => some [.prim .swap7]
  | 7 => some [.prim .swap8]
  | 8 => some [.prim .swap9]
  | 9 => some [.prim .swap10]
  | 10 => some [.prim .swap11]
  | 11 => some [.prim .swap12]
  | 12 => some [.prim .swap13]
  | 13 => some [.prim .swap14]
  | 14 => some [.prim .swap15]
  | 15 => some [.prim .swap16]
  | _ => none

def localDepthFrom? (name : Name) : Shape → Nat → Option Nat
  | [], _depth => none
  | .local slotName :: rest, depth =>
      if slotName = name then
        some depth
      else
        localDepthFrom? name rest (depth + 1)
  | _slot :: rest, depth =>
      localDepthFrom? name rest (depth + 1)

def localDepth? (name : Name) (shape : Shape) : Option Nat :=
  localDepthFrom? name shape 0

def localDepthUnderTop? (name : Name) : Shape → Option Nat
  | _top :: rest => localDepth? name rest
  | [] => none

def storeLocalCode? (depth : Nat) : Option Assembly.Program := do
  let swap ← swap? depth
  some (swap ++ [.prim .pop])

def lowerAssignLocalsWithShape? :
    List Name → Shape → Option (Assembly.Program × Shape)
  | [], shape => some ([], shape)
  | name :: names, shape => do
      let depth ← localDepthUnderTop? name shape
      let head ← storeLocalCode? depth
      let shape' ← (TypedCfg.Instr.storeLocal name depth).type? shape
      let (tail, output) ← lowerAssignLocalsWithShape? names shape'
      some (head ++ tail, output)

def lowerDupLocalsForReturn? :
    List Name → Shape → Option (Assembly.Program × Shape)
  | [], shape => some ([], shape)
  | name :: names, shape => do
      let depth ← localDepth? name shape
      let head ← dup? depth
      let shape' ← (TypedCfg.Instr.dup depth).type? shape
      let (tail, output) ← lowerDupLocalsForReturn? names shape'
      some (head ++ tail, output)

def lowerReturnLocalsWithShape? (names : List Name) (shape : Shape) :
    Option Assembly.Program := do
  let (dupCode, _dupShape) ← lowerDupLocalsForReturn? names.reverse shape
  let cleanup ← StackShuffle.removeManyBuriedUnder? names.length shape.length
  some (dupCode ++ cleanup)

def lower? : Instr → Option Assembly.Program
  | .push value => some [.push value]
  | .prim op => some [.prim op]
  | .pop => some [.prim .pop]
  | .dup depth => dup? depth
  | .swap depth => swap? depth
  | .declareLocal _name => some []
  | .declareLocals _names => some []
  | .initLocals names => some (pushZeros names.length)
  | .loadLocal _name depth => dup? depth
  | .storeLocal _name depth => do
      storeLocalCode? depth
  | .assignLocals _names => none
  | .returnLocals _names => none
  | .unwind _target => none

def lowerWithShape? (instr : Instr) (shape : Shape) :
    Option (Assembly.Program × Shape) := do
  let output ← instr.type? shape
  match instr with
  | .unwind target =>
      some (popMany (shape.length - target.length), output)
  | .assignLocals names => do
      let (code, output') ← lowerAssignLocalsWithShape? names shape
      if output' = output then
        some (code, output)
      else
        none
  | .returnLocals names => do
      let code ← lowerReturnLocalsWithShape? names shape
      some (code, output)
  | _ => do
      let code ← instr.lower?
      some (code, output)

end Instr

namespace Terminator

def lower? (program : Program) (sites : List CallSite) (blockLabel : Label) :
    Terminator → Option Assembly.Program
  | .fallthrough => some []
  | .jump target => some [.jump target]
  | .jumpi target next => some [.jumpi target, .jump next]
  | .call name returnLabel => do
      let proc ← program.findProc? name
      let site ← sites.find?
        (fun site =>
          site.callLabel == blockLabel &&
            site.procName == name &&
              site.returnLabel == returnLabel)
      let shuffle ← StackShuffle.sinkTopUnder? proc.argc
      some ([.push site.token] ++ shuffle ++ [.jump proc.entry])
  | .ret name => do
      let _proc ← program.findProc? name
      some [.jump (ProcLabel.dispatch name)]
  | .halt kind =>
      match kind with
      | .stop => some [.prim .stop]
      | .return => some [.prim .return]
      | .revert => some [.prim .revert]
      | .selfdestruct => some [.prim .selfdestruct]
  | .invalid => some [.prim .invalid]

end Terminator

namespace Block

def lowerBodyWithShape? : List Instr → Shape → Option (Assembly.Program × Shape)
  | [], shape => some ([], shape)
  | instr :: rest, shape => do
      let (head, shape') ← instr.lowerWithShape? shape
      let (tail, output) ← lowerBodyWithShape? rest shape'
      some (head ++ tail, output)

def lowerBody? (body : List Instr) : Option Assembly.Program := do
  let (code, _output) ← lowerBodyWithShape? body []
  some code

def lower? (program : Program) (sites : List CallSite) (block : Block) :
    Option Assembly.Program := do
  let (body, _output) ← lowerBodyWithShape? block.body block.input
  let term ← block.term.lower? program sites block.label
  some (.label block.label :: body ++ term)

end Block

namespace Program

def collectCallSitesFrom : Nat → List Block → List CallSite
  | _idx, [] => []
  | idx, block :: rest =>
      let tail := collectCallSitesFrom (idx + 1) rest
      match block.term with
      | .call name returnLabel =>
          { callLabel := block.label
            procName := name
            token := EvmYul.UInt256.ofNat idx
            returnLabel := returnLabel } :: tail
      | _ => tail

def collectCallSites (program : Program) : List CallSite :=
  collectCallSitesFrom 0 program.blocks

def lowerBlocks? (program : Program) (sites : List CallSite) :
    List Block → Option Assembly.Program
  | [] => some []
  | block :: rest => do
      let head ← block.lower? program sites
      let tail ← lowerBlocks? program sites rest
      some (head ++ tail)

namespace Dispatch

def testsForRetc (name : Name) (retc : Nat) :
    Nat → List CallSite → Option Assembly.Program
  | _idx, [] => some []
  | idx, site :: rest => do
      let dup ← StackShuffle.dupInstr? (retc + 1)
      let tail ← testsForRetc name retc (idx + 1) rest
      some
        ([ dup
         , .push site.token
         , .prim .eq
         , .jumpi (ProcLabel.dispatchCase name idx)
         ] ++ tail)

def casesForRetc (name : Name) (retc : Nat) :
    Nat → List CallSite → Option Assembly.Program
  | _idx, [] => some []
  | idx, site :: rest => do
      let remove ← StackShuffle.removeBuriedUnder? retc
      let tail ← casesForRetc name retc (idx + 1) rest
      some
        ([.label (ProcLabel.dispatchCase name idx)] ++
          remove ++ [.jump site.returnLabel] ++ tail)

def forProc (proc : Procedure) (sites : List CallSite) :
    Option Assembly.Program := do
  let procSites := sites.filter (CallSite.forProc proc.name)
  let tests ← testsForRetc proc.name proc.retc 0 procSites
  let cases ← casesForRetc proc.name proc.retc 0 procSites
  some
    ([.label (ProcLabel.dispatch proc.name)] ++
      tests ++ [.prim .invalid] ++ cases)

def forProcs : List Procedure → List CallSite → Option Assembly.Program
  | [], _sites => some []
  | proc :: rest, sites => do
      let head ← forProc proc sites
      let tail ← forProcs rest sites
      some (head ++ tail)

end Dispatch

def lower? (program : Program) : Option Assembly.Program := do
  let sites := collectCallSites program
  let blocks ← lowerBlocks? program sites program.blocks
  let dispatch ← Dispatch.forProcs program.procedures sites
  some (blocks ++ dispatch)

def Lowerable (program : Program) : Prop :=
  ∃ asm, program.lower? = some asm

end Program

namespace CheckedProgram

def lower? (program : CheckedProgram) : Option Assembly.Program :=
  program.program.lower?

def assemble? (program : CheckedProgram) : Option Assembly.TargetProgram := do
  let asm ← program.lower?
  Assembly.compile? asm

end CheckedProgram

end TypedCfg
end EvmCompiler
