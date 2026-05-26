import EvmCompiler.Structured.Compiler

namespace EvmCompiler
namespace Structured

/-!
Typed continuation facade for the procedure-aware Structured compiler.

The current backend still emits labeled assembly directly.  This module names
the control invariant that the proof should expose publicly: labels are not
bare branch targets, they are continuations with declared symbolic stack shapes,
and every control transfer produces an explicit conformance obligation.
-/

namespace TypedContinuations

inductive Shape where
  | any
  | unreachable
  | named (name : String)
  | join (scope tag : Nat)
  | loop (scope tag : Nat)
  | afterCode (input : Shape) (code : Code)
  | afterCondition (input : Shape) (cond : Code)
  | afterSwitchPop (input : Shape) (scrutinee : Code)
  | procEntry (name : Name) (argc : Nat)
  | procExit (name : Name) (retc : Nat)
  | callReturn (name : Name) (token : Word)
  | programEnd
  deriving DecidableEq, Repr

namespace Shape

def mainEntry : Shape :=
  .named "structured:main:entry"

def switchValue (input : Shape) (scrutinee : Code) : Shape :=
  .afterCode input scrutinee

end Shape

inductive Target where
  | fallthrough
  | labeled (label : Assembly.Label)
  deriving DecidableEq, Repr

namespace Target

def label? : Target → Option Assembly.Label
  | .fallthrough => none
  | .labeled label => some label

end Target

structure Kont where
  target : Target
  shape : Shape
  deriving DecidableEq, Repr

namespace Kont

def fallthrough (shape : Shape) : Kont :=
  { target := .fallthrough, shape := shape }

def label (label : Assembly.Label) (shape : Shape) : Kont :=
  { target := .labeled label, shape := shape }

def label? (kont : Kont) : Option Assembly.Label :=
  kont.target.label?

end Kont

inductive Mode where
  | regular
  | brk
  | cont
  | leave
  deriving DecidableEq, Repr

structure Context where
  procs : List Proc := []
  regular : Kont
  break? : Option Kont := none
  continue? : Option Kont := none
  leave? : Option Kont := none

namespace Context

def toCompileContext (ctx : Context) : CompileContext where
  procs := ctx.procs
  breakLabel? := ctx.break?.bind Kont.label?
  continueLabel? := ctx.continue?.bind Kont.label?
  leaveLabel? := ctx.leave?.bind Kont.label?

def continuation? (ctx : Context) : Mode → Option Kont
  | .regular => some ctx.regular
  | .brk => ctx.break?
  | .cont => ctx.continue?
  | .leave => ctx.leave?

def withoutLoop (ctx : Context) : Context :=
  { ctx with break? := none, continue? := none }

end Context

structure LabelDecl where
  label : Assembly.Label
  shape : Shape
  deriving DecidableEq, Repr

abbrev LabelMap := List LabelDecl

namespace LabelMap

def Declares (labels : LabelMap) (label : Assembly.Label) (shape : Shape) :
    Prop :=
  { label := label, shape := shape } ∈ labels

def DeclaresKont (labels : LabelMap) (kont : Kont) : Prop :=
  match kont.target with
  | .fallthrough => True
  | .labeled label => labels.Declares label kont.shape

theorem DeclaresKont.mono {oldLabels newLabels : LabelMap} {kont : Kont}
    (hSub : ∀ decl, decl ∈ oldLabels → decl ∈ newLabels)
    (hDeclared : oldLabels.DeclaresKont kont) :
    newLabels.DeclaresKont kont := by
  cases kont with
  | mk target shape =>
      cases target with
      | fallthrough =>
          simp [DeclaresKont]
      | labeled label =>
          exact hSub { label := label, shape := shape } hDeclared

end LabelMap

namespace Kont

def declarations (kont : Kont) : LabelMap :=
  match kont.target with
  | .fallthrough => []
  | .labeled label => [{ label := label, shape := kont.shape }]

theorem declared_in_declarations (kont : Kont) :
    kont.declarations.DeclaresKont kont := by
  cases kont with
  | mk target shape =>
      cases target with
      | fallthrough =>
          simp [LabelMap.DeclaresKont]
      | labeled label =>
          simp [declarations, LabelMap.DeclaresKont, LabelMap.Declares]

end Kont

namespace Context

def TargetsDeclared (labels : LabelMap) (ctx : Context) : Prop :=
  labels.DeclaresKont ctx.regular ∧
    (∀ kont, ctx.break? = some kont → labels.DeclaresKont kont) ∧
    (∀ kont, ctx.continue? = some kont → labels.DeclaresKont kont) ∧
    (∀ kont, ctx.leave? = some kont → labels.DeclaresKont kont)

end Context

inductive TransferKind where
  | fallthrough
  | jump
  | conditionalTrue
  | conditionalFalse
  | switchCase
  | switchDefault
  | loopBack
  | callEntry
  | dispatchReturn
  | invalid
  deriving DecidableEq, Repr

inductive TransferTarget where
  | kont (kont : Kont)
  | terminal (kind : Assembly.HaltKind)
  | invalid
  deriving DecidableEq, Repr

structure TransferObligation where
  source : Shape
  target : TransferTarget
  kind : TransferKind
  deriving DecidableEq, Repr

namespace TransferObligation

def toKont (source : Shape) (kont : Kont) (kind : TransferKind) :
    TransferObligation :=
  { source := source, target := .kont kont, kind := kind }

def terminal (source : Shape) (kind : Assembly.HaltKind) :
    TransferObligation :=
  { source := source, target := .terminal kind, kind := .fallthrough }

def invalid (source : Shape) : TransferObligation :=
  { source := source, target := .invalid, kind := .invalid }

end TransferObligation

namespace TransferTarget

def Declared (labels : LabelMap) : TransferTarget → Prop
  | .kont targetKont => labels.DeclaresKont targetKont
  | .terminal _kind => True
  | .invalid => True

theorem Declared.mono {oldLabels newLabels : LabelMap}
    {target : TransferTarget}
    (hSub : ∀ decl, decl ∈ oldLabels → decl ∈ newLabels)
    (hDeclared : target.Declared oldLabels) :
    target.Declared newLabels := by
  cases target with
  | kont targetKont =>
      exact LabelMap.DeclaresKont.mono hSub hDeclared
  | terminal _kind =>
      trivial
  | invalid =>
      trivial

end TransferTarget

namespace TransferObligation

def TargetDeclared (labels : LabelMap) (transfer : TransferObligation) :
    Prop :=
  transfer.target.Declared labels

theorem TargetDeclared.mono {oldLabels newLabels : LabelMap}
    {transfer : TransferObligation}
    (hSub : ∀ decl, decl ∈ oldLabels → decl ∈ newLabels)
    (hDeclared : transfer.TargetDeclared oldLabels) :
    transfer.TargetDeclared newLabels :=
  TransferTarget.Declared.mono hSub hDeclared

theorem TargetDeclared.append_left {labels extra : LabelMap}
    {transfer : TransferObligation}
    (hDeclared : transfer.TargetDeclared labels) :
    transfer.TargetDeclared (labels ++ extra) :=
  TargetDeclared.mono (fun decl hMem => by simp [hMem]) hDeclared

theorem TargetDeclared.append_right {labels extra : LabelMap}
    {transfer : TransferObligation}
    (hDeclared : transfer.TargetDeclared labels) :
    transfer.TargetDeclared (extra ++ labels) :=
  TargetDeclared.mono (fun decl hMem => by simp [hMem]) hDeclared

theorem toKont_targetDeclared (source : Shape) (kont : Kont)
    (kind : TransferKind) :
    (toKont source kont kind).TargetDeclared kont.declarations := by
  exact Kont.declared_in_declarations kont

theorem terminal_targetDeclared (source : Shape) (kind : Assembly.HaltKind)
    (labels : LabelMap) :
    (terminal source kind).TargetDeclared labels := by
  trivial

theorem invalid_targetDeclared (source : Shape) (labels : LabelMap) :
    (invalid source).TargetDeclared labels := by
  trivial

end TransferObligation

structure ReturnKont where
  site : CallSite
  deriving DecidableEq, Repr

namespace ReturnKont

def continuation (ret : ReturnKont) : Kont :=
  Kont.label ret.site.returnLabel
    (Shape.callReturn ret.site.procName ret.site.token)

def Declared (labels : LabelMap) (ret : ReturnKont) : Prop :=
  labels.DeclaresKont ret.continuation

theorem Declared.mono {oldLabels newLabels : LabelMap} {ret : ReturnKont}
    (hSub : ∀ decl, decl ∈ oldLabels → decl ∈ newLabels)
    (hDeclared : ret.Declared oldLabels) :
    ret.Declared newLabels :=
  LabelMap.DeclaresKont.mono hSub hDeclared

theorem Declared.append_left {labels extra : LabelMap} {ret : ReturnKont}
    (hDeclared : ret.Declared labels) :
    ret.Declared (labels ++ extra) :=
  Declared.mono (fun decl hMem => by simp [hMem]) hDeclared

theorem Declared.append_right {labels extra : LabelMap} {ret : ReturnKont}
    (hDeclared : ret.Declared labels) :
    ret.Declared (extra ++ labels) :=
  Declared.mono (fun decl hMem => by simp [hMem]) hDeclared

theorem declared_in_site_declaration (ret : ReturnKont) :
    ret.Declared
      [{ label := ret.site.returnLabel
         shape := Shape.callReturn ret.site.procName ret.site.token }] := by
  simp [Declared, continuation, Kont.label, LabelMap.DeclaresKont,
    LabelMap.Declares]

end ReturnKont

structure Result where
  compiled : CompileResult
  entryShape : Shape
  fallthroughShape : Shape
  labels : LabelMap
  transfers : List TransferObligation
  returnKonts : List ReturnKont
  deriving Repr

namespace Result

def appendMeta (left right : Result) (compiled : CompileResult)
    (entryShape fallthroughShape : Shape) : Result where
  compiled := compiled
  entryShape := entryShape
  fallthroughShape := fallthroughShape
  labels := left.labels ++ right.labels
  transfers := left.transfers ++ right.transfers
  returnKonts := left.returnKonts ++ right.returnKonts

def allLabels (ambient : LabelMap) (result : Result) : LabelMap :=
  ambient ++ result.labels

@[simp]
theorem allLabels_nil (result : Result) :
    result.allLabels [] = result.labels := by
  simp [allLabels]

def TargetsDeclared (ambient : LabelMap) (result : Result) : Prop :=
  (∀ transfer, transfer ∈ result.transfers →
    transfer.TargetDeclared (result.allLabels ambient)) ∧
  (∀ ret, ret ∈ result.returnKonts →
    ret.Declared (result.allLabels ambient))

def SelfDeclared (result : Result) : Prop :=
  (∀ transfer, transfer ∈ result.transfers →
    transfer.TargetDeclared result.labels) ∧
  (∀ ret, ret ∈ result.returnKonts →
    ret.Declared result.labels)

theorem appendMeta_selfDeclared {left right : Result}
    {compiled : CompileResult} {entryShape fallthroughShape : Shape}
    (hLeft : left.SelfDeclared) (hRight : right.SelfDeclared) :
    (appendMeta left right compiled entryShape fallthroughShape).SelfDeclared := by
  constructor
  · intro transfer hMem
    simp [appendMeta] at hMem
    cases hMem with
    | inl hLeftMem =>
        have hDeclared : transfer.TargetDeclared left.labels := by
          simpa [allLabels] using hLeft.1 transfer hLeftMem
        exact
          TransferObligation.TargetDeclared.append_left
            (labels := left.labels) (extra := right.labels) hDeclared
    | inr hRightMem =>
        have hDeclared : transfer.TargetDeclared right.labels := by
          simpa [allLabels] using hRight.1 transfer hRightMem
        exact
          TransferObligation.TargetDeclared.append_right
            (labels := right.labels) (extra := left.labels) hDeclared
  · intro ret hMem
    simp [appendMeta] at hMem
    cases hMem with
    | inl hLeftMem =>
        have hDeclared : ret.Declared left.labels := by
          simpa [allLabels] using hLeft.2 ret hLeftMem
        exact
          ReturnKont.Declared.append_left
            (labels := left.labels) (extra := right.labels) hDeclared
    | inr hRightMem =>
        have hDeclared : ret.Declared right.labels := by
          simpa [allLabels] using hRight.2 ret hRightMem
        exact
          ReturnKont.Declared.append_right
            (labels := right.labels) (extra := left.labels) hDeclared

end Result

namespace Exit

def transfer (entry : Shape) : Option Kont → TransferObligation
  | some kont => TransferObligation.toKont entry kont .jump
  | none => TransferObligation.invalid entry

def declarations : Option Kont → LabelMap
  | some kont => kont.declarations
  | none => []

theorem transfer_targetDeclared (entry : Shape) (target : Option Kont) :
    (transfer entry target).TargetDeclared (declarations target) := by
  cases target with
  | none =>
      exact TransferObligation.invalid_targetDeclared entry []
  | some kont =>
      exact TransferObligation.toKont_targetDeclared entry kont .jump

end Exit

mutual
  noncomputable def Block.typedFromCtx
      (block : Block) (ctx : Context) (supply : LabelSupply)
      (entry : Shape) : Result :=
    let compiled := Block.compileFromCtx block ctx.toCompileContext supply
    match block with
    | ⟨[]⟩ =>
        { compiled := compiled
          entryShape := entry
          fallthroughShape := entry
          labels := Exit.declarations ctx.break?
          transfers := []
          returnKonts := [] }
    | ⟨stmt :: rest⟩ =>
        let typedStmt := Stmt.typedFromCtxCore stmt ctx supply entry
        let typedRest :=
          Block.typedFromCtx { stmts := rest } ctx typedStmt.compiled.next
            typedStmt.fallthroughShape
        Result.appendMeta typedStmt typedRest compiled entry
          typedRest.fallthroughShape

  noncomputable def Stmt.typedFromCtxCore
      (stmt : Stmt) (ctx : Context) (supply : LabelSupply)
      (entry : Shape) : Result :=
    let compiled := Stmt.compileFromCtxCore stmt ctx.toCompileContext supply
    match stmt with
    | .code code =>
        { compiled := compiled
          entryShape := entry
          fallthroughShape := .afterCode entry code
          labels := Exit.declarations ctx.continue?
          transfers := []
          returnKonts := [] }
    | .if_ cond body =>
        let bodyLabel := LabelSupply.label supply 0
        let endLabel := LabelSupply.label supply 1
        let bodyShape := .afterCondition entry cond
        let endShape := Shape.join supply 1
        let endKont := Kont.label endLabel endShape
        let bodyCtx := { ctx with regular := endKont }
        let typedBody :=
          Block.typedFromCtx body bodyCtx (LabelSupply.next supply) bodyShape
        { compiled := compiled
          entryShape := entry
          fallthroughShape := endShape
          labels :=
            { label := bodyLabel, shape := bodyShape } ::
              { label := endLabel, shape := endShape } ::
                typedBody.labels
          transfers :=
            TransferObligation.toKont bodyShape
              (Kont.label bodyLabel bodyShape) .conditionalTrue ::
            TransferObligation.toKont bodyShape endKont .conditionalFalse ::
            TransferObligation.toKont typedBody.fallthroughShape endKont
              .fallthrough ::
            typedBody.transfers
          returnKonts := typedBody.returnKonts }
    | .switch scrutinee cases defaultBody =>
        let endLabel := LabelSupply.label supply 0
        let defaultLabel := LabelSupply.label supply 1
        let valueShape := Shape.switchValue entry scrutinee
        let bodyShape := Shape.afterSwitchPop entry scrutinee
        let endShape := Shape.join supply 0
        let endKont := Kont.label endLabel endShape
        let typedCases :=
          SwitchCases.typedFromCtx cases ctx endKont valueShape bodyShape
            supply (LabelSupply.next supply) 0
        let typedDefault :=
          SwitchDefault.typedFromCtx defaultBody ctx endKont
            (Kont.label defaultLabel valueShape) bodyShape typedCases.compiled.next
        { compiled := compiled
          entryShape := entry
          fallthroughShape := endShape
          labels :=
            { label := endLabel, shape := endShape } ::
              { label := defaultLabel, shape := valueShape } ::
                typedCases.labels ++ typedDefault.labels
          transfers :=
            TransferObligation.toKont valueShape
              (Kont.label defaultLabel valueShape) .switchDefault ::
            typedCases.transfers ++ typedDefault.transfers
          returnKonts := typedCases.returnKonts ++ typedDefault.returnKonts }
    | .for_ init cond post body =>
        let loopLabel := LabelSupply.label supply 0
        let bodyLabel := LabelSupply.label supply 1
        let postLabel := LabelSupply.label supply 2
        let endLabel := LabelSupply.label supply 3
        let loopShape := Shape.loop supply 0
        let bodyShape := Shape.afterCondition loopShape cond
        let postShape := Shape.loop supply 2
        let endShape := Shape.join supply 3
        let loopKont := Kont.label loopLabel loopShape
        let postKont := Kont.label postLabel postShape
        let endKont := Kont.label endLabel endShape
        let loopOuterCtx := { ctx.withoutLoop with regular := loopKont }
        let typedInit :=
          Block.typedFromCtx init loopOuterCtx (LabelSupply.next supply) entry
        let bodyCtx :=
          { ctx with
            regular := postKont
            break? := some endKont
            continue? := some postKont }
        let typedBody :=
          Block.typedFromCtx body bodyCtx typedInit.compiled.next bodyShape
        let typedPost :=
          Block.typedFromCtx post loopOuterCtx typedBody.compiled.next postShape
        { compiled := compiled
          entryShape := entry
          fallthroughShape := endShape
          labels :=
            { label := loopLabel, shape := loopShape } ::
            { label := bodyLabel, shape := bodyShape } ::
            { label := postLabel, shape := postShape } ::
            { label := endLabel, shape := endShape } ::
              typedInit.labels ++ typedBody.labels ++ typedPost.labels
          transfers :=
            TransferObligation.toKont typedInit.fallthroughShape loopKont
              .fallthrough ::
            TransferObligation.toKont bodyShape
              (Kont.label bodyLabel bodyShape) .conditionalTrue ::
            TransferObligation.toKont loopShape endKont .conditionalFalse ::
            TransferObligation.toKont typedBody.fallthroughShape postKont
              .fallthrough ::
            TransferObligation.toKont typedPost.fallthroughShape loopKont
              .loopBack ::
              typedInit.transfers ++ typedBody.transfers ++ typedPost.transfers
          returnKonts :=
            typedInit.returnKonts ++ typedBody.returnKonts ++
              typedPost.returnKonts }
    | .brk =>
        { compiled := compiled
          entryShape := entry
          fallthroughShape := .unreachable
          labels := Exit.declarations ctx.break?
          transfers := [Exit.transfer entry ctx.break?]
          returnKonts := [] }
    | .cont =>
        { compiled := compiled
          entryShape := entry
          fallthroughShape := .unreachable
          labels := Exit.declarations ctx.continue?
          transfers := [Exit.transfer entry ctx.continue?]
          returnKonts := [] }
    | .leave =>
        { compiled := compiled
          entryShape := entry
          fallthroughShape := .unreachable
          labels := Exit.declarations ctx.leave?
          transfers := [Exit.transfer entry ctx.leave?]
          returnKonts := [] }
    | .call name =>
        let returnLabel := LabelSupply.label supply 0
        let token := Stmt.callToken supply
        match ProcList.lookup? name ctx.procs with
        | none =>
            { compiled := compiled
              entryShape := entry
              fallthroughShape := .unreachable
              labels := []
              transfers := [TransferObligation.invalid entry]
              returnKonts := [] }
        | some proc =>
            let returnShape := Shape.callReturn name token
            let entryKont :=
              Kont.label (ProcLabel.entry name) (.procEntry name proc.argc)
            let site : CallSite :=
              { procName := name, token := token, returnLabel := returnLabel }
            { compiled := compiled
              entryShape := entry
              fallthroughShape := returnShape
              labels :=
                { label := returnLabel, shape := returnShape } ::
                  entryKont.declarations
              transfers := [TransferObligation.toKont entry entryKont .callEntry]
              returnKonts := [{ site := site }] }
    | .terminal kind =>
        { compiled := compiled
          entryShape := entry
          fallthroughShape := .unreachable
          labels := []
          transfers := [TransferObligation.terminal entry kind]
          returnKonts := [] }

  noncomputable def SwitchCases.typedFromCtx
      (cases : List (Word × Block)) (ctx : Context) (endKont : Kont)
      (valueShape bodyShape : Shape) (base supply : LabelSupply) (idx : Nat) :
      Result :=
    let compiled :=
      SwitchCases.compileFromCtx cases ctx.toCompileContext
        (match endKont.target with
        | .labeled label => label
        | .fallthrough => ProcLabel.programEnd) base supply idx
    match cases with
    | [] =>
        { compiled := compiled
          entryShape := valueShape
          fallthroughShape := valueShape
          labels := []
          transfers := []
          returnKonts := [] }
    | (_value, body) :: rest =>
        let caseLabel := LabelSupply.label base (idx + 2)
        let bodyCtx := { ctx with regular := endKont }
        let typedBody := Block.typedFromCtx body bodyCtx supply bodyShape
        let typedRest :=
          SwitchCases.typedFromCtx rest ctx endKont valueShape bodyShape base
            typedBody.compiled.next (idx + 1)
        { compiled := compiled
          entryShape := valueShape
          fallthroughShape := typedRest.fallthroughShape
          labels :=
            { label := caseLabel, shape := valueShape } ::
              endKont.declarations ++ typedBody.labels ++ typedRest.labels
          transfers :=
            TransferObligation.toKont valueShape
              (Kont.label caseLabel valueShape) .switchCase ::
            TransferObligation.toKont typedBody.fallthroughShape endKont
              .jump ::
              typedBody.transfers ++ typedRest.transfers
          returnKonts := typedBody.returnKonts ++ typedRest.returnKonts }

  noncomputable def SwitchDefault.typedFromCtx
      (defaultBody : Option Block) (ctx : Context) (endKont defaultKont : Kont)
      (bodyShape : Shape) (supply : LabelSupply) : Result :=
    let compiled :=
      SwitchDefault.compileFromCtx defaultBody ctx.toCompileContext
        (match endKont.target with
        | .labeled label => label
        | .fallthrough => ProcLabel.programEnd)
        (match defaultKont.target with
        | .labeled label => label
        | .fallthrough => ProcLabel.programEnd)
        supply
    match defaultBody with
    | none =>
        { compiled := compiled
          entryShape := defaultKont.shape
          fallthroughShape := endKont.shape
          labels := []
          transfers := [TransferObligation.toKont bodyShape endKont .jump]
          returnKonts := [] }
    | some body =>
        let bodyCtx := { ctx with regular := endKont }
        let typedBody := Block.typedFromCtx body bodyCtx supply bodyShape
        { compiled := compiled
          entryShape := defaultKont.shape
          fallthroughShape := endKont.shape
          labels := endKont.declarations ++ typedBody.labels
          transfers :=
            TransferObligation.toKont typedBody.fallthroughShape endKont
              .jump ::
            typedBody.transfers
          returnKonts := typedBody.returnKonts }
end

namespace Dispatch

def typedCasesForRetc (proc : Proc) (sites : List CallSite)
    (supply : LabelSupply) : LabelMap :=
  (sites.filter (CallSite.forProc proc.name)).zipIdx.flatMap
    (fun indexed =>
      let site := indexed.1
      [ { label := LabelSupply.label supply indexed.2
          shape := Shape.procExit proc.name proc.retc }
      , { label := site.returnLabel
          shape := Shape.callReturn site.procName site.token } ])

def typedTransfersForRetc (proc : Proc) (sites : List CallSite)
    (supply : LabelSupply) : List TransferObligation :=
  (sites.filter (CallSite.forProc proc.name)).zipIdx.flatMap
    (fun indexed =>
      let site := indexed.1
      let caseKont :=
        Kont.label (LabelSupply.label supply indexed.2)
          (Shape.procExit proc.name proc.retc)
      let returnKont :=
        Kont.label site.returnLabel (Shape.callReturn site.procName site.token)
      [ TransferObligation.toKont (Shape.procExit proc.name proc.retc)
          caseKont .dispatchReturn
      , TransferObligation.toKont (Shape.procExit proc.name proc.retc)
          returnKont .dispatchReturn
      ])

end Dispatch

namespace CompiledProcBodies

noncomputable def typedEmit :
    List CompiledProcBody → List CallSite → LabelSupply →
      LabelMap × List TransferObligation
  | [], _sites, _supply => ([], [])
  | procBody :: rest, sites, supply =>
      let dispatch := Dispatch.forProc procBody.proc sites supply
      let emittedRest := typedEmit rest sites dispatch.next
      ( Dispatch.typedCasesForRetc procBody.proc sites supply ++ emittedRest.1
      , Dispatch.typedTransfersForRetc procBody.proc sites supply ++
          emittedRest.2 )

end CompiledProcBodies

namespace Proc

noncomputable def typedBody (allProcs : List Proc) (proc : Proc)
    (supply : LabelSupply) : Result :=
  let entryShape := Shape.procEntry proc.name proc.argc
  let exitShape := Shape.procExit proc.name proc.retc
  let exitKont := Kont.label (ProcLabel.exit proc.name) exitShape
  let ctx : Context :=
    { procs := allProcs
      regular := exitKont
      leave? := some exitKont }
  let body := Block.typedFromCtx proc.body ctx supply entryShape
  let compiled := Proc.compileBody allProcs proc supply
  { compiled :=
      { code := compiled.code, next := compiled.next, calls := compiled.calls }
    entryShape := entryShape
    fallthroughShape := exitShape
    labels :=
      { label := ProcLabel.entry proc.name, shape := entryShape } ::
      { label := ProcLabel.exit proc.name, shape := exitShape } ::
        body.labels
    transfers :=
      TransferObligation.toKont body.fallthroughShape exitKont .fallthrough ::
        body.transfers
    returnKonts := body.returnKonts }

end Proc

namespace ProcBodies

noncomputable def typed
    (allProcs : List Proc) : List Proc → LabelSupply → List Result
  | [], _supply => []
  | proc :: rest, supply =>
      let body := Proc.typedBody allProcs proc supply
      body :: typed allProcs rest body.compiled.next

end ProcBodies

namespace Program

noncomputable def typedInterface (program : Program) : Result :=
  let mainExit := Kont.label ProcLabel.programEnd Shape.programEnd
  let mainCtx : Context := { procs := program.procs, regular := mainExit }
  let main := Block.typedFromCtx program.body mainCtx 0 Shape.mainEntry
  let (compiledProcBodies, bodyNext, procCalls) :=
    ProcBodies.compile program.procs program.procs main.compiled.next
  let allCalls := main.compiled.calls ++ procCalls
  let procBodies := ProcBodies.typed program.procs program.procs main.compiled.next
  let emittedProcs :=
    CompiledProcBodies.typedEmit compiledProcBodies allCalls bodyNext
  let compiled := program.compileResult
  { compiled := compiled
    entryShape := Shape.mainEntry
    fallthroughShape := Shape.programEnd
    labels :=
      { label := ProcLabel.programEnd, shape := Shape.programEnd } ::
        main.labels ++ procBodies.flatMap (fun body => body.labels) ++
          emittedProcs.1
    transfers :=
      TransferObligation.toKont main.fallthroughShape mainExit .jump ::
        main.transfers ++ procBodies.flatMap (fun body => body.transfers) ++
          emittedProcs.2
    returnKonts :=
      main.returnKonts ++ procBodies.flatMap (fun body => body.returnKonts) }

@[simp]
theorem typedInterface_compiled (program : Program) :
    (Program.typedInterface program).compiled = program.compileResult := by
  rfl

def TypedBoundary (program : Program) : Prop :=
  (Program.typedInterface program).TargetsDeclared []

end Program

end TypedContinuations

end Structured
end EvmCompiler
