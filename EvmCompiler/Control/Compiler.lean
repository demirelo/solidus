import EvmCompiler.Control.Semantics

namespace EvmCompiler
namespace Control
namespace Compiler

abbrev Shape := TypedCfg.Shape
abbrev Label := TypedCfg.Label
abbrev LabelSupply := Nat

namespace LabelSupply

def label (supply : LabelSupply) (tag : Nat) : Label :=
  Assembly.Label.generated supply tag

def next (supply : LabelSupply) : LabelSupply :=
  supply + 1

end LabelSupply

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

namespace Expr

mutual
  def compile? (expr : Expr) (shape : Shape) :
      Option (List TypedCfg.Instr × Shape) :=
    match expr with
    | .literal value =>
        let instr := TypedCfg.Instr.push value
        let shape' := .literal value :: shape
        some ([instr], shape')
    | .prim op args => do
        let (argCode, argShape) ← compileArgs? args shape
        let instr := TypedCfg.Instr.prim op
        let outShape ← instr.type? argShape
        match outShape with
        | _value :: rest =>
            if rest = shape then
              some (argCode ++ [instr], outShape)
            else
              none
        | _ => none

  /--
  Compile arguments from right to left. The resulting target stack has argument
  values in source order, with the first argument on top.
  -/
  def compileArgs? : List Expr → Shape →
      Option (List TypedCfg.Instr × Shape)
    | [], shape => some ([], shape)
    | arg :: rest, shape => do
        let (restCode, restShape) ← compileArgs? rest shape
        let (argCode, argShape) ← compile? arg restShape
        some (restCode ++ argCode, argShape)
end

def compileCondition? (expr : Expr) (shape : Shape) :
    Option (List TypedCfg.Instr) := do
  let (code, outShape) ← compile? expr shape
  match outShape with
  | _cond :: rest => if rest = shape then some code else none
  | _ => none

def compileValue? (expr : Expr) (shape : Shape) :
    Option (List TypedCfg.Instr × Shape) := do
  let (code, outShape) ← compile? expr shape
  match outShape with
  | _value :: rest => if rest = shape then some (code, outShape) else none
  | _ => none

def compileTerminalArgs? (args : List Expr) (shape : Shape)
    (argc : Nat) : Option (List TypedCfg.Instr) := do
  let (code, outShape) ← compileArgs? args shape
  if outShape.length = shape.length + argc then
    some code
  else
    none

end Expr

namespace PrimStmt

def compile? (op : Assembly.PrimOp) (args : List Expr) (shape : Shape) :
    Option (List TypedCfg.Instr) := do
  let (argCode, argShape) ← Expr.compileArgs? args shape
  let instr := TypedCfg.Instr.prim op
  let outShape ← instr.type? argShape
  if outShape = shape then
    some (argCode ++ [instr])
  else
    none

end PrimStmt

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
    | .prim op args => do
        let _ ← PrimStmt.compile? op args shape
        some shape
    | .if_ cond body => do
        let _ ← Expr.compileCondition? cond shape
        match Block.regularShape? body shape with
        | none => some shape
        | some bodyShape => if bodyShape = shape then some shape else none
    | .switch scrutinee cases defaultBody => do
        let _ ← Expr.compileValue? scrutinee shape
        let casesOk ← SwitchCases.regularShape? cases shape
        let defaultOk ← SwitchDefault.regularShape? defaultBody shape
        if casesOk && defaultOk then some shape else none
    | .for_ init cond post body => do
        let initShape ← Block.regularShape? init shape
        let _ ← Expr.compileCondition? cond initShape
        let postShape? := Block.regularShape? post initShape
        let bodyShape? := Block.regularShape? body initShape
        match postShape?, bodyShape? with
        | some postShape, some bodyShape =>
            if postShape = initShape ∧ bodyShape = initShape then
              some initShape
            else
              none
        | _, _ => none
    | .brk | .cont | .leave | .terminal _ _ => none

  def SwitchCases.regularShape? (cases : List (Word × Block))
      (shape : Shape) : Option Bool :=
    match cases with
    | [] => some true
    | (_value, body) :: rest => do
        let bodyOk :=
          match Block.regularShape? body shape with
          | none => true
          | some bodyShape => bodyShape = shape
        let restOk ← SwitchCases.regularShape? rest shape
        some (bodyOk && restOk)

  def SwitchDefault.regularShape? (defaultBody : Option Block)
      (shape : Shape) : Option Bool :=
    match defaultBody with
    | none => some true
    | some body =>
        match Block.regularShape? body shape with
        | none => some true
        | some bodyShape => some (bodyShape = shape)
end

mutual
  def Block.toCfgFrom
      (block : Block) (ctx : Context) (label : Label) (shape : Shape)
      (supply : LabelSupply) : Option Result :=
    match block with
    | ⟨[]⟩ =>
        some { blocks := [exitBlock label shape (some ctx.regular)]
               next := supply }
    | ⟨stmt :: rest⟩ =>
        match Stmt.regularShape? stmt shape with
        | none =>
            Stmt.toCfgFrom stmt ctx label shape supply
        | some nextShape => do
            let restLabel := LabelSupply.label supply 0
            let stmtCtx :=
              { ctx with regular := { label := restLabel, shape := nextShape } }
            let stmtResult ← Stmt.toCfgFrom stmt stmtCtx label shape
              (LabelSupply.next supply)
            let restResult ←
              Block.toCfgFrom { stmts := rest } ctx restLabel nextShape
                stmtResult.next
            some (stmtResult.append restResult)

  def Stmt.toCfgFrom
      (stmt : Stmt) (ctx : Context) (label : Label) (shape : Shape)
      (supply : LabelSupply) : Option Result :=
    match stmt with
    | .prim op args => do
        let code ← PrimStmt.compile? op args shape
        some
          { blocks :=
              [ { label := label
                  input := shape
                  body := code ++ [.unwind ctx.regular.shape]
                  term := .jump ctx.regular.label } ]
            next := supply }
    | .if_ cond body => do
        let condCode ← Expr.compileCondition? cond shape
        let bodyLabel := LabelSupply.label supply 0
        let endLabel := LabelSupply.label supply 1
        let endKont : Kont := { label := endLabel, shape := shape }
        let bodyResult ←
          Block.toCfgFrom body { ctx with regular := endKont } bodyLabel shape
            (LabelSupply.next (LabelSupply.next supply))
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
        let (scrutineeCode, valueShape) ← Expr.compileValue? scrutinee shape
        let firstTestLabel := LabelSupply.label supply 0
        let endLabel := LabelSupply.label supply 1
        let defaultLabel := LabelSupply.label supply 2
        let endKont : Kont := { label := endLabel, shape := shape }
        let testResult ←
          SwitchCases.toCfgTests cases firstTestLabel defaultLabel
            (LabelSupply.next (LabelSupply.next (LabelSupply.next supply)))
            valueShape
        let caseResult ←
          SwitchCases.toCfgBodies cases ctx endKont testResult.next valueShape
            shape
        let defaultResult ←
          SwitchDefault.toCfgBody defaultBody ctx endKont defaultLabel
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
        let initShape ← Block.regularShape? init shape
        let condCode ← Expr.compileCondition? cond initShape
        let loopLabel := LabelSupply.label supply 0
        let bodyLabel := LabelSupply.label supply 1
        let postLabel := LabelSupply.label supply 2
        let endLabel := LabelSupply.label supply 3
        let loopKont : Kont := { label := loopLabel, shape := initShape }
        let postKont : Kont := { label := postLabel, shape := initShape }
        let endKont : Kont := { label := endLabel, shape := initShape }
        let initResult ←
          Block.toCfgFrom init { ctx with regular := loopKont } label shape
            (LabelSupply.next (LabelSupply.next (LabelSupply.next
              (LabelSupply.next supply))))
        let bodyCtx :=
          { ctx with
            regular := postKont
            break? := some endKont
            continue? := some postKont }
        let bodyResult ←
          Block.toCfgFrom body bodyCtx bodyLabel initShape initResult.next
        let postResult ←
          Block.toCfgFrom post { ctx with regular := loopKont } postLabel
            initShape bodyResult.next
        some
          { blocks :=
              initResult.blocks ++
              [ { label := loopLabel
                  input := initShape
                  body := condCode
                  term := .jumpi bodyLabel endLabel } ] ++
                bodyResult.blocks ++ postResult.blocks ++
              [exitBlock endLabel initShape (some ctx.regular)]
            next := postResult.next }
    | .brk =>
        some { blocks := [exitBlock label shape ctx.break?], next := supply }
    | .cont =>
        some { blocks := [exitBlock label shape ctx.continue?], next := supply }
    | .leave =>
        some { blocks := [exitBlock label shape ctx.leave?], next := supply }
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
            (LabelSupply.next (LabelSupply.next supply)) valueShape
        some
          { blocks :=
              [ { label := label
                  input := valueShape
                  body := [.dup 0, .push value, .prim .eq]
                  term := .jumpi caseLabel nextTestLabel } ] ++ tail.blocks
            next := tail.next }

  def SwitchCases.toCfgBodies
      (cases : List (Word × Block)) (ctx : Context) (endKont : Kont)
      (supply : LabelSupply) (valueShape bodyShape : Shape) : Option Result :=
    match cases with
    | [] => some { blocks := [], next := supply }
    | (_value, body) :: rest => do
        let caseLabel := LabelSupply.label supply 0
        let bodyLabel := LabelSupply.label supply 1
        let bodyResult ←
          Block.toCfgFrom body { ctx with regular := endKont } bodyLabel
            bodyShape (LabelSupply.next (LabelSupply.next supply))
        let restResult ←
          SwitchCases.toCfgBodies rest ctx endKont bodyResult.next valueShape
            bodyShape
        some
          { blocks :=
              [ { label := caseLabel
                  input := valueShape
                  body := [.pop]
                  term := .jump bodyLabel } ] ++
                bodyResult.blocks ++ restResult.blocks
            next := restResult.next }

  def SwitchDefault.toCfgBody
      (defaultBody : Option Block) (ctx : Context) (endKont : Kont)
      (label : Label) (supply : LabelSupply) (valueShape bodyShape : Shape) :
      Option Result :=
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
          Block.toCfgFrom body { ctx with regular := endKont } bodyLabel
            bodyShape (LabelSupply.next supply)
        some
          { blocks :=
              [ { label := label
                  input := valueShape
                  body := [.pop]
                  term := .jump bodyLabel } ] ++ bodyResult.blocks
            next := bodyResult.next }
end

namespace Program

def entryLabel : Label :=
  Assembly.Label.named "control:entry"

def endLabel : Label :=
  Assembly.Label.named "control:end"

def toCfg? (program : Program) : Option TypedCfg.Program := do
  if !program.accepted? then
    none
  else
    let endKont : Kont := { label := endLabel, shape := [] }
    let result ←
      Block.toCfgFrom program.body { regular := endKont } entryLabel [] 0
    some
      { entry := entryLabel
        blocks := result.blocks ++ [finalBlock endLabel []] }

def toCheckedCfg? (program : Program) : Option TypedCfg.CheckedProgram := do
  let cfg ← toCfg? program
  TypedCfg.Program.check? cfg

def compileCfg? (program : Program) : Option Assembly.Program := do
  let cfg ← toCheckedCfg? program
  TypedCfg.CheckedProgram.lower? cfg

end Program

end Compiler
end Control
end EvmCompiler
