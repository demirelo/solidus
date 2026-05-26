import EvmCompiler.StackFreeCfg.Accepted
import EvmCompiler.TypedCfg

namespace EvmCompiler
namespace StackFreeCfg
namespace Compiler

/-!
Compiler from the stack-free source CFG to the typed stack CFG.

This is intentionally the first layer that mentions `TypedCfg.Shape`, local
depths, continuation labels, or procedure entry/return shapes. The
`StackFreeCfg` source syntax, source acceptedness, and source interpreter stay
stack-free; this module owns the implementation layout.
-/

abbrev Shape := TypedCfg.Shape
abbrev Label := TypedCfg.Label
abbrev LabelSupply := Nat

namespace LabelSupply

def label (supply : LabelSupply) (tag : Nat) : Label :=
  Assembly.Label.generated supply tag

def next (supply : LabelSupply) : LabelSupply :=
  supply + 1

def bump (supply count : LabelSupply) : LabelSupply :=
  supply + count

end LabelSupply

namespace Labels

def entry : Label :=
  Assembly.Label.named "stackfree:entry"

def endLabel : Label :=
  Assembly.Label.named "stackfree:end"

def procEntry (name : Name) : Label :=
  Assembly.Label.named ("stackfree:proc:" ++ name ++ ":entry")

def procBody (name : Name) : Label :=
  Assembly.Label.named ("stackfree:proc:" ++ name ++ ":body")

def procExit (name : Name) : Label :=
  Assembly.Label.named ("stackfree:proc:" ++ name ++ ":exit")

end Labels

structure Kont where
  label : Label
  shape : Shape
  deriving Repr

structure Context where
  regular : Kont
  break? : Option Kont := none
  continue? : Option Kont := none
  leave? : Option Kont := none
  deriving Repr

structure Result where
  blocks : List TypedCfg.Block
  next : LabelSupply
  deriving Repr

namespace Result

def append (left right : Result) : Result where
  blocks := left.blocks ++ right.blocks
  next := right.next

end Result

def invalidBlock (label : Label) (shape : Shape) : TypedCfg.Block where
  label := label
  input := shape
  body := []
  term := .invalid

def exitBlock (label : Label) (shape : Shape) (kont? : Option Kont) :
    TypedCfg.Block :=
  match kont? with
  | none => invalidBlock label shape
  | some kont =>
      { label := label
        input := shape
        body := [.unwind kont.shape]
        term := .jump kont.label }

def finalBlock (label : Label) (shape : Shape) : TypedCfg.Block where
  label := label
  input := shape
  body := []
  term := .fallthrough

namespace Layout

def locals (names : List Name) : Shape :=
  names.map TypedCfg.Slot.local

def pushedLocals (names : List Name) (shape : Shape) : Shape :=
  locals names ++ shape

def lookupDepth? (name : Name) : Shape → Nat → Option Nat
  | [], _depth => none
  | .local localName :: rest, depth =>
      if localName = name then
        some depth
      else
        lookupDepth? name rest (depth + 1)
  | _slot :: rest, depth => lookupDepth? name rest (depth + 1)

def hasLocal? (name : Name) (shape : Shape) : Bool :=
  (lookupDepth? name shape 0).isSome

def hasAllLocals? (names : List Name) (shape : Shape) : Bool :=
  names.all (fun name => hasLocal? name shape)

end Layout

namespace Expr

mutual
  def compile? (expr : Expr) (shape : Shape) :
      Option (List TypedCfg.Instr × Shape) :=
    match expr with
    | .literal value =>
        some ([.push value], .literal value :: shape)
    | .var name => do
        let depth ← Layout.lookupDepth? name shape 0
        let instr := TypedCfg.Instr.loadLocal name depth
        let shape' ← instr.type? shape
        some ([instr], shape')
    | .prim op args => do
        let (argCode, argShape) ← compileArgs? args shape
        let instr := TypedCfg.Instr.prim op
        let outShape ← instr.type? argShape
        some (argCode ++ [instr], outShape)

  def compileArgs? : List Expr → Shape →
      Option (List TypedCfg.Instr × Shape)
    | [], shape => some ([], shape)
    | arg :: rest, shape => do
        let (restCode, restShape) ← compileArgs? rest shape
        let (argCode, argShape) ← compileOne? arg restShape
        some (restCode ++ argCode, argShape)

  def compileOne? (expr : Expr) (shape : Shape) :
      Option (List TypedCfg.Instr × Shape) := do
    let (code, outShape) ← compile? expr shape
    match outShape with
    | _value :: rest =>
        if rest = shape then some (code, outShape) else none
    | _ => none
end

def compileN? (expr : Expr) (shape : Shape) (n : Nat) :
    Option (List TypedCfg.Instr × Shape) := do
  let (code, outShape) ← compile? expr shape
  if outShape.length = shape.length + n ∧ outShape.drop n = shape then
    some (code, outShape)
  else
    none

def compileZero? (expr : Expr) (shape : Shape) :
    Option (List TypedCfg.Instr) := do
  let (code, outShape) ← compile? expr shape
  if outShape = shape then some code else none

def compileCondition? (expr : Expr) (shape : Shape) :
    Option (List TypedCfg.Instr) := do
  let (code, outShape) ← compileOne? expr shape
  match outShape with
  | _cond :: rest => if rest = shape then some code else none
  | _ => none

def compileTerminalArgs? (args : List Expr) (shape : Shape)
    (argc : Nat) : Option (List TypedCfg.Instr) := do
  let (code, outShape) ← compileArgs? args shape
  if outShape.length = shape.length + argc ∧ outShape.drop argc = shape then
    some code
  else
    none

end Expr

namespace StmtCode

def pushZeros : Nat → List TypedCfg.Instr
  | 0 => []
  | n + 1 => .push zero :: pushZeros n

def decl? (names : List Name) (value? : Option Expr) (shape : Shape) :
    Option (List TypedCfg.Instr × Shape) := do
  let (valueCode, valueShape) ←
    match value? with
    | none =>
        let code := pushZeros names.length
        some (code, List.replicate names.length (TypedCfg.Slot.literal zero) ++ shape)
    | some value =>
        Expr.compileN? value shape names.length
  let instr := TypedCfg.Instr.declareLocals names
  let outShape ← instr.type? valueShape
  some (valueCode ++ [instr], outShape)

def assign? (names : List Name) (value : Expr) (shape : Shape) :
    Option (List TypedCfg.Instr × Shape) := do
  let (valueCode, valueShape) ← Expr.compileN? value shape names.length
  let instr := TypedCfg.Instr.assignLocals names
  let outShape ← instr.type? valueShape
  some (valueCode ++ [instr], outShape)

end StmtCode

mutual
  def Block.regularShape? (block : Block) (shape : Shape) : Option Shape :=
    match block with
    | ⟨[]⟩ => some shape
    | ⟨stmt :: rest⟩ =>
        match Stmt.regularShape? stmt shape with
        | none => none
        | some shape' => Block.regularShape? { stmts := rest } shape'

  def Stmt.regularShape? (stmt : Stmt) (shape : Shape) : Option Shape :=
    match stmt with
    | .expr expr => do
        let _ ← Expr.compileZero? expr shape
        some shape
    | .decl names value? => do
        let (_code, outShape) ← StmtCode.decl? names value? shape
        some outShape
    | .assign names value => do
        let (_code, outShape) ← StmtCode.assign? names value shape
        some outShape
    | .block body =>
        match Block.regularShape? body shape with
        | some _bodyShape => some shape
        | none => none
    | .if_ cond body => do
        let _ ← Expr.compileCondition? cond shape
        let _bodyShape? := Block.regularShape? body shape
        some shape
    | .switch scrutinee cases defaultBody => do
        let _ ← Expr.compileOne? scrutinee shape
        let casesOk ← SwitchCases.regularShape? cases shape
        let defaultOk ← SwitchDefault.regularShape? defaultBody shape
        if casesOk || defaultOk || defaultBody.isNone then some shape else none
    | .for_ init cond post body => do
      let loopShape ← Block.regularShape? init shape
      let _ ← Expr.compileCondition? cond loopShape
      let _ := post
      let _ := body
      some shape
    | .call targets functionName args => do
        let (argCode, argShape) ← Expr.compileArgs? args shape
        let _ := argCode
        let _ := functionName
        if argShape.length = shape.length + args.length ∧
            argShape.drop args.length = shape ∧
            Layout.hasAllLocals? targets shape = true then
          some shape
        else
          none
    | .brk | .cont | .leave | .terminal _ _ => none

  def SwitchCases.regularShape? (cases : List (Word × Block))
      (shape : Shape) : Option Bool :=
    match cases with
    | [] => some false
    | (_value, body) :: rest => do
        let bodyOk :=
          match Block.regularShape? body shape with
          | none => false
          | some _bodyShape => true
        let restOk ← SwitchCases.regularShape? rest shape
        some (bodyOk || restOk)

  def SwitchDefault.regularShape? (defaultBody : Option Block)
      (shape : Shape) : Option Bool :=
    match defaultBody with
    | none => some true
    | some body =>
        match Block.regularShape? body shape with
        | none => some false
        | some _bodyShape => some true
end

def callRegularShape? (program : Program) (targets : List Name)
    (functionName : Name) (args : List Expr) (shape : Shape) : Option Shape := do
  let proc ← program.findProc? functionName
  if args.length = proc.params.length ∧
      targets.length = proc.returns.length ∧
      Layout.hasAllLocals? targets shape then
    some shape
  else
    none

mutual
  def Block.toCfgFrom
      (program : Program) (block : Block) (ctx : Context)
      (label : Label) (shape : Shape) (supply : LabelSupply) :
      Option Result :=
    match block with
    | ⟨[]⟩ =>
        some { blocks := [exitBlock label shape (some ctx.regular)]
               next := supply }
    | ⟨stmt :: rest⟩ =>
        let regularShape? :=
          match stmt with
          | .call targets functionName args =>
              callRegularShape? program targets functionName args shape
          | _ => Stmt.regularShape? stmt shape
        match regularShape? with
        | none =>
            Stmt.toCfgFrom program stmt ctx label shape supply
        | some nextShape => do
            let restLabel := LabelSupply.label supply 0
            let stmtCtx :=
              { ctx with regular := { label := restLabel, shape := nextShape } }
            let stmtResult ←
              Stmt.toCfgFrom program stmt stmtCtx label shape
                (LabelSupply.next supply)
            let restResult ←
              Block.toCfgFrom program { stmts := rest } ctx restLabel nextShape
                stmtResult.next
            some (stmtResult.append restResult)

  def Stmt.toCfgFrom
      (program : Program) (stmt : Stmt) (ctx : Context)
      (label : Label) (shape : Shape) (supply : LabelSupply) :
      Option Result :=
    match stmt with
    | .expr expr => do
        let code ← Expr.compileZero? expr shape
        some
          { blocks :=
              [ { label := label
                  input := shape
                  body := code ++ [.unwind ctx.regular.shape]
                  term := .jump ctx.regular.label } ]
            next := supply }
    | .decl names value? => do
        let (code, _outShape) ← StmtCode.decl? names value? shape
        some
          { blocks :=
              [ { label := label
                  input := shape
                  body := code ++ [.unwind ctx.regular.shape]
                  term := .jump ctx.regular.label } ]
            next := supply }
    | .assign names value => do
        let (code, _outShape) ← StmtCode.assign? names value shape
        some
          { blocks :=
              [ { label := label
                  input := shape
                  body := code ++ [.unwind ctx.regular.shape]
                  term := .jump ctx.regular.label } ]
            next := supply }
    | .block body =>
        Block.toCfgFrom program body ctx label shape supply
    | .if_ cond body => do
        let condCode ← Expr.compileCondition? cond shape
        let bodyLabel := LabelSupply.label supply 0
        let endLabel := LabelSupply.label supply 1
        let endKont : Kont := { label := endLabel, shape := shape }
        let bodyResult ←
          Block.toCfgFrom program body { ctx with regular := endKont }
            bodyLabel shape (LabelSupply.bump supply 2)
        some
          { blocks :=
              [ { label := label
                  input := shape
                  body := condCode
                  term := .jumpi bodyLabel endLabel } ] ++
                bodyResult.blocks ++
              [exitBlock endLabel shape (some ctx.regular)]
            next := bodyResult.next }
    | .switch scrutinee cases defaultBody => do
        let (scrutineeCode, valueShape) ← Expr.compileOne? scrutinee shape
        let firstTestLabel := LabelSupply.label supply 0
        let endLabel := LabelSupply.label supply 1
        let defaultLabel := LabelSupply.label supply 2
        let endKont : Kont := { label := endLabel, shape := shape }
        let testResult ←
          SwitchCases.toCfgTests cases firstTestLabel defaultLabel
            (LabelSupply.bump supply 3) valueShape
        let caseResult ←
          SwitchCases.toCfgBodies program cases ctx endKont testResult.next
            valueShape shape
        let defaultResult ←
          SwitchDefault.toCfgBody program defaultBody ctx endKont defaultLabel
            caseResult.next valueShape shape
        some
          { blocks :=
              [ { label := label
                  input := shape
                  body := scrutineeCode
                  term := .jump firstTestLabel } ] ++
                testResult.blocks ++ caseResult.blocks ++
                defaultResult.blocks ++
              [exitBlock endLabel shape (some ctx.regular)]
            next := defaultResult.next }
    | .for_ init cond post body => do
        let loopShape ← Block.regularShape? init shape
        let condCode ← Expr.compileCondition? cond loopShape
        let loopLabel := LabelSupply.label supply 0
        let bodyLabel := LabelSupply.label supply 1
        let postLabel := LabelSupply.label supply 2
        let endLabel := LabelSupply.label supply 3
        let loopKont : Kont := { label := loopLabel, shape := loopShape }
        let postKont : Kont := { label := postLabel, shape := loopShape }
        let endKont : Kont := { label := endLabel, shape := loopShape }
        let initResult ←
          Block.toCfgFrom program init { ctx with regular := loopKont } label
            shape (LabelSupply.bump supply 4)
        let bodyCtx :=
          { ctx with
            regular := postKont
            break? := some endKont
            continue? := some postKont }
        let bodyResult ←
          Block.toCfgFrom program body bodyCtx bodyLabel loopShape
            initResult.next
        let postResult ←
          Block.toCfgFrom program post { ctx with regular := loopKont }
            postLabel loopShape bodyResult.next
        some
          { blocks :=
              initResult.blocks ++
              [ { label := loopLabel
                  input := loopShape
                  body := condCode
                  term := .jumpi bodyLabel endLabel } ] ++
                bodyResult.blocks ++ postResult.blocks ++
              [exitBlock endLabel loopShape (some ctx.regular)]
            next := postResult.next }
    | .brk =>
        some { blocks := [exitBlock label shape ctx.break?], next := supply }
    | .cont =>
        some { blocks := [exitBlock label shape ctx.continue?], next := supply }
    | .leave =>
        some { blocks := [exitBlock label shape ctx.leave?], next := supply }
    | .call targets functionName args => do
        let proc ← program.findProc? functionName
        if targets.length = proc.returns.length ∧
            args.length = proc.params.length ∧
            Layout.hasAllLocals? targets shape then
          let (argCode, _argShape) ← Expr.compileArgs? args shape
          let returnLabel := LabelSupply.label supply 0
          let returnShape := TypedCfg.Shape.pushWords proc.returns.length shape
          let returnBody := [TypedCfg.Instr.assignLocals targets]
          some
            { blocks :=
                [ { label := label
                    input := shape
                    body := argCode
                    term := .call functionName returnLabel }
                , { label := returnLabel
                    input := returnShape
                    body := returnBody ++ [.unwind ctx.regular.shape]
                    term := .jump ctx.regular.label } ]
              next := LabelSupply.next supply }
        else
          none
    | .terminal kind args => do
        let code ← Expr.compileTerminalArgs? args shape kind.argCount
        some
          { blocks :=
              [ { label := label
                  input := shape
                  body := code
                  term := .halt kind } ]
            next := supply }

  def SwitchCases.toCfgTests
      (cases : List (Word × Block)) (label defaultLabel : Label)
      (supply : LabelSupply) (valueShape : Shape) : Option Result :=
    match cases with
    | [] =>
        some
          { blocks :=
              [ { label := label
                  input := valueShape
                  body := []
                  term := .jump defaultLabel } ]
            next := supply }
    | (value, _body) :: rest => do
        let caseLabel := LabelSupply.label supply 0
        let nextTestLabel := LabelSupply.label supply 1
        let tail ←
          SwitchCases.toCfgTests rest nextTestLabel defaultLabel
            (LabelSupply.bump supply 2) valueShape
        some
          { blocks :=
              [ { label := label
                  input := valueShape
                  body := [.dup 0, .push value, .prim .eq]
                  term := .jumpi caseLabel nextTestLabel } ] ++ tail.blocks
            next := tail.next }

  def SwitchCases.toCfgBodies
      (program : Program) (cases : List (Word × Block)) (ctx : Context)
      (endKont : Kont) (supply : LabelSupply) (valueShape bodyShape : Shape) :
      Option Result :=
    match cases with
    | [] => some { blocks := [], next := supply }
    | (_value, body) :: rest => do
        let caseLabel := LabelSupply.label supply 0
        let bodyLabel := LabelSupply.label supply 1
        let bodyResult ←
          Block.toCfgFrom program body { ctx with regular := endKont }
            bodyLabel bodyShape (LabelSupply.bump supply 2)
        let restResult ←
          SwitchCases.toCfgBodies program rest ctx endKont bodyResult.next
            valueShape bodyShape
        some
          { blocks :=
              [ { label := caseLabel
                  input := valueShape
                  body := [.pop]
                  term := .jump bodyLabel } ] ++
                bodyResult.blocks ++ restResult.blocks
            next := restResult.next }

  def SwitchDefault.toCfgBody
      (program : Program) (defaultBody : Option Block) (ctx : Context)
      (endKont : Kont) (label : Label) (supply : LabelSupply)
      (valueShape bodyShape : Shape) : Option Result :=
    match defaultBody with
    | none =>
        some
          { blocks :=
              [ { label := label
                  input := valueShape
                  body := [.pop]
                  term := .jump endKont.label } ]
            next := supply }
    | some body => do
        let bodyLabel := LabelSupply.label supply 0
        let bodyResult ←
          Block.toCfgFrom program body { ctx with regular := endKont }
            bodyLabel bodyShape (LabelSupply.next supply)
        some
          { blocks :=
              [ { label := label
                  input := valueShape
                  body := [.pop]
                  term := .jump bodyLabel } ] ++ bodyResult.blocks
            next := bodyResult.next }
end

namespace Proc

def layout (proc : Proc) : Shape :=
  Layout.pushedLocals proc.returns (Layout.pushedLocals proc.params [])

def toProcedure (proc : Proc) : TypedCfg.Procedure where
  name := proc.name
  entry := Labels.procEntry proc.name
  argc := proc.params.length
  retc := proc.returns.length

def toCfgFrom (program : Program) (proc : Proc) (supply : LabelSupply) :
    Option Result := do
  let bodyShape := layout proc
  let exitKont : Kont := { label := Labels.procExit proc.name, shape := bodyShape }
  let bodyResult ←
    Block.toCfgFrom program proc.body
      { regular := exitKont, leave? := some exitKont }
      (Labels.procBody proc.name) bodyShape supply
  some
    { blocks :=
        [ { label := Labels.procEntry proc.name
            input := TypedCfg.Shape.pushWords proc.params.length []
            body := [.declareLocals proc.params, .initLocals proc.returns]
            term := .jump (Labels.procBody proc.name) } ] ++
          bodyResult.blocks ++
        [ { label := Labels.procExit proc.name
            input := bodyShape
            body := [.returnLocals proc.returns]
            term := .ret proc.name } ]
      next := bodyResult.next }

end Proc

namespace ProcList

def toTypedProcedures : List Proc → List TypedCfg.Procedure
  | [] => []
  | proc :: rest => Proc.toProcedure proc :: toTypedProcedures rest

def toCfgFrom (program : Program) :
    List Proc → LabelSupply → Option Result
  | [], supply => some { blocks := [], next := supply }
  | proc :: rest, supply => do
      let head ← Proc.toCfgFrom program proc supply
      let tail ← toCfgFrom program rest head.next
      some (head.append tail)

end ProcList

namespace Program

def toCfg? (program : Program) : Option TypedCfg.Program := do
  let endKont : Kont := { label := Labels.endLabel, shape := [] }
  let main ←
    Block.toCfgFrom program program.body { regular := endKont }
      Labels.entry [] 0
  let procs ← ProcList.toCfgFrom program program.procs main.next
  some
    { entry := Labels.entry
      procedures := ProcList.toTypedProcedures program.procs
      blocks := main.blocks ++ [finalBlock Labels.endLabel []] ++ procs.blocks }

def toCheckedCfg? (program : Program) : Option TypedCfg.CheckedProgram := do
  let cfg ← toCfg? program
  TypedCfg.Program.check? cfg

end Program

end Compiler
end StackFreeCfg
end EvmCompiler
