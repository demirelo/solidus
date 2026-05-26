import EvmCompiler.Structured.Compiler
import EvmCompiler.TypedCfg

namespace EvmCompiler
namespace Structured
namespace Cfg

abbrev Shape := TypedCfg.Shape
abbrev Label := TypedCfg.Label

structure Kont where
  label : Label
  shape : Shape
  deriving Repr

structure Context where
  procs : List Proc := []
  regular : Kont
  break? : Option Kont := none
  continue? : Option Kont := none
  leave? : Option Kont := none

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

namespace BasicInstr

def toCfg : BasicInstr → TypedCfg.Instr
  | .push value => .push value
  | .op op => .prim op.toPrimOp

end BasicInstr

namespace Code

def toCfg (code : Code) : List TypedCfg.Instr :=
  code.map BasicInstr.toCfg

def type? : Code → Shape → Option Shape
  | [], shape => some shape
  | instr :: rest, shape => do
      let shape' ← (BasicInstr.toCfg instr).type? shape
      type? rest shape'

def conditionShape? (code : Code) (shape : Shape) : Option Shape := do
  let out ← type? code shape
  match out with
  | _cond :: rest => if rest = shape then some shape else none
  | _ => none

def valueShape? (code : Code) (shape : Shape) : Option Shape := do
  let out ← type? code shape
  match out with
  | _value :: rest => if rest = shape then some out else none
  | _ => none

end Code

mutual
  def Block.regularShape? (procs : List Proc) (block : Block)
      (shape : Shape) : Option Shape :=
    match block with
    | ⟨[]⟩ => some shape
    | ⟨stmt :: rest⟩ =>
        match Stmt.regularShape? procs stmt shape with
        | none => none
        | some shape' => Block.regularShape? procs { stmts := rest } shape'

  def Stmt.regularShape? (procs : List Proc) (stmt : Stmt)
      (shape : Shape) : Option Shape :=
    match stmt with
    | .code code =>
        Code.type? code shape
    | .if_ cond body => do
        let _ ← Code.conditionShape? cond shape
        match Block.regularShape? procs body shape with
        | none => some shape
        | some bodyShape => if bodyShape = shape then some shape else none
    | .switch scrutinee cases defaultBody => do
        let _ ← Code.valueShape? scrutinee shape
        let casesOk ← SwitchCases.regularShape? procs cases shape
        let defaultOk ← SwitchDefault.regularShape? procs defaultBody shape
        if casesOk && defaultOk then some shape else none
    | .for_ init cond post body => do
        let initShape ← Block.regularShape? procs init shape
        let _ ← Code.conditionShape? cond initShape
        let postShape? := Block.regularShape? procs post initShape
        let bodyShape? := Block.regularShape? procs body initShape
        match postShape?, bodyShape? with
        | some postShape, some bodyShape =>
            if postShape = initShape ∧ bodyShape = initShape then
              some initShape
            else
              none
        | _, _ => none
    | .call name => do
        let proc ← ProcList.lookup? name procs
        if proc.argc ≤ shape.length then
          some (TypedCfg.Shape.pushWords proc.retc
            (TypedCfg.Shape.pop proc.argc shape))
        else
          none
    | .brk | .cont | .leave | .terminal _ =>
        none

  def SwitchCases.regularShape? (procs : List Proc)
      (cases : List (Word × Block))
      (shape : Shape) : Option Bool :=
    match cases with
    | [] => some true
    | (_value, body) :: rest => do
        let bodyOk :=
          match Block.regularShape? procs body shape with
          | none => true
          | some bodyShape => bodyShape = shape
        let restOk ← SwitchCases.regularShape? procs rest shape
        some (bodyOk && restOk)

  def SwitchDefault.regularShape? (procs : List Proc)
      (defaultBody : Option Block)
      (shape : Shape) : Option Bool :=
    match defaultBody with
    | none => some true
    | some body =>
        match Block.regularShape? procs body shape with
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
        match Stmt.regularShape? ctx.procs stmt shape with
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
    | .code code => do
        let _ ← Code.type? code shape
        some
          { blocks :=
              [ { label := label
                  input := shape
                  body := Code.toCfg code ++ [.unwind ctx.regular.shape]
                  term := .jump ctx.regular.label } ]
            next := supply }
    | .if_ cond body => do
        let _ ← Code.conditionShape? cond shape
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
                  body := Code.toCfg cond
                  term := .jumpi bodyLabel endLabel } ] ++
                bodyResult.blocks ++
              [exitBlock endLabel shape (some ctx.regular)]
            next := bodyResult.next }
    | .switch scrutinee cases defaultBody => do
        let valueShape ← Code.valueShape? scrutinee shape
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
                  body := Code.toCfg scrutinee
                  term := .jump firstTestLabel } ] ++
                testResult.blocks ++ caseResult.blocks ++
                defaultResult.blocks ++
              [exitBlock endLabel shape (some ctx.regular)]
            next := defaultResult.next }
    | .for_ init cond post body => do
        let initShape ← Block.regularShape? ctx.procs init shape
        let _ ← Code.conditionShape? cond initShape
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
                  body := Code.toCfg cond
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
    | .terminal kind =>
        some
          { blocks :=
              [ { label := label
                  input := shape
                  body := []
                  term := .halt kind } ]
            next := supply }
    | .call name =>
        some
          { blocks :=
              [ { label := label
                  input := shape
                  body := []
                  term := .call name ctx.regular.label } ]
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

namespace Proc

def toTypedCfg (proc : Proc) : TypedCfg.Procedure where
  name := proc.name
  entry := ProcLabel.entry proc.name
  argc := proc.argc
  retc := proc.retc

def toCfgFrom (allProcs : List Proc) (proc : Proc)
    (supply : LabelSupply) : Option Result := do
  let returnShape := TypedCfg.Shape.pushWords proc.retc []
  let exitKont : Kont := { label := ProcLabel.exit proc.name, shape := returnShape }
  let result ←
    Block.toCfgFrom proc.body
      { procs := allProcs
        regular := exitKont
        leave? := some exitKont }
      (ProcLabel.entry proc.name) (TypedCfg.Shape.pushWords proc.argc []) supply
  some
    { blocks :=
        result.blocks ++
          [ { label := ProcLabel.exit proc.name
              input := returnShape
              body := []
              term := .ret proc.name } ]
      next := result.next }

end Proc

namespace ProcList

def toTypedCfg : List Proc → List TypedCfg.Procedure
  | [] => []
  | proc :: rest => Proc.toTypedCfg proc :: toTypedCfg rest

def toCfgFrom : List Proc → List Proc → LabelSupply → Option Result
  | _allProcs, [], supply => some { blocks := [], next := supply }
  | allProcs, proc :: rest, supply => do
      let head ← Proc.toCfgFrom allProcs proc supply
      let tail ← toCfgFrom allProcs rest head.next
      some (head.append tail)

end ProcList

namespace Program

def entryLabel : Label :=
  Assembly.Label.named "structured:entry"

def endLabel : Label :=
  Assembly.Label.named "structured:end"

def toCfg? (program : Program) : Option TypedCfg.Program := do
  let endKont : Kont := { label := endLabel, shape := [] }
  let result ←
    Block.toCfgFrom program.body
      { procs := program.procs, regular := endKont } entryLabel [] 0
  let procs ← ProcList.toCfgFrom program.procs program.procs result.next
  some
    { entry := entryLabel
      procedures := ProcList.toTypedCfg program.procs
      blocks := result.blocks ++ procs.blocks ++ [finalBlock endLabel []] }

def toCheckedCfg? (program : Program) : Option TypedCfg.CheckedProgram := do
  let cfg ← toCfg? program
  TypedCfg.Program.check? cfg

def compileCfg? (program : Program) : Option Assembly.Program := do
  let cfg ← toCheckedCfg? program
  TypedCfg.CheckedProgram.lower? cfg

end Program

end Cfg
end Structured
end EvmCompiler
