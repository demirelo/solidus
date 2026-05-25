import EvmCompiler.Structured.Semantics

namespace EvmCompiler
namespace Structured

abbrev LabelSupply := Nat

namespace LabelSupply

def label (supply : LabelSupply) (tag : Nat) : Assembly.Label :=
  Assembly.Label.generated supply tag

def next (supply : LabelSupply) : LabelSupply :=
  supply + 1

end LabelSupply

namespace ProcLabel

def entry (name : Name) : Assembly.Label :=
  Assembly.Label.named ("proc:" ++ name ++ ":entry")

def exit (name : Name) : Assembly.Label :=
  Assembly.Label.named ("proc:" ++ name ++ ":exit")

def programEnd : Assembly.Label :=
  Assembly.Label.named "structured:program:end"

end ProcLabel

structure CallSite where
  procName : Name
  token : Word
  returnLabel : Assembly.Label
  deriving DecidableEq, Repr

namespace CallSite

def forProc (name : Name) (site : CallSite) : Bool :=
  decide (site.procName = name)

end CallSite

structure CompileResult where
  code : Assembly.Program
  next : LabelSupply
  calls : List CallSite
  deriving DecidableEq, Repr

namespace CompileResult

def append (left right : CompileResult) : CompileResult where
  code := left.code ++ right.code
  next := right.next
  calls := left.calls ++ right.calls

end CompileResult

structure CompileContext where
  procs : List Proc := []
  breakLabel? : Option Assembly.Label := none
  continueLabel? : Option Assembly.Label := none
  leaveLabel? : Option Assembly.Label := none

namespace StackShuffle

def swapInstr : Nat → Assembly.Instr
  | 1 => .prim .swap1
  | 2 => .prim .swap2
  | 3 => .prim .swap3
  | 4 => .prim .swap4
  | 5 => .prim .swap5
  | 6 => .prim .swap6
  | 7 => .prim .swap7
  | 8 => .prim .swap8
  | 9 => .prim .swap9
  | 10 => .prim .swap10
  | 11 => .prim .swap11
  | 12 => .prim .swap12
  | 13 => .prim .swap13
  | 14 => .prim .swap14
  | 15 => .prim .swap15
  | 16 => .prim .swap16
  | _ => .prim .invalid

def dupInstr : Nat → Assembly.Instr
  | 1 => .prim .dup1
  | 2 => .prim .dup2
  | 3 => .prim .dup3
  | 4 => .prim .dup4
  | 5 => .prim .dup5
  | 6 => .prim .dup6
  | 7 => .prim .dup7
  | 8 => .prim .dup8
  | 9 => .prim .dup9
  | 10 => .prim .dup10
  | 11 => .prim .dup11
  | 12 => .prim .dup12
  | 13 => .prim .dup13
  | 14 => .prim .dup14
  | 15 => .prim .dup15
  | 16 => .prim .dup16
  | _ => .prim .invalid

/-- Move the top stack item below `depth` visible items, preserving their order. -/
def sinkTopUnder : Nat → Assembly.Program
  | 0 => []
  | depth + 1 => swapInstr (depth + 1) :: sinkTopUnder depth

/--
Move the item below `depth` visible items to the top, preserving visible-item
order after the final `POP`.
-/
def liftBuriedToTop : Nat → Assembly.Program
  | 0 => []
  | depth + 1 => liftBuriedToTop depth ++ [swapInstr (depth + 1)]

def removeBuriedUnder (depth : Nat) : Assembly.Program :=
  liftBuriedToTop depth ++ [Assembly.Instr.prim .pop]

end StackShuffle

namespace Stmt

def jumpOrInvalid : Option Assembly.Label → Assembly.Program
  | some label => [Assembly.Instr.jump label]
  | none => [Assembly.Instr.prim .invalid]

def switchTestCode (value : Word) : Code :=
  [BasicInstr.op .dup1, BasicInstr.push value, BasicInstr.op .eq]

def switchTest (base : LabelSupply) (idx : Nat) (value : Word) :
    Assembly.Program :=
  (switchTestCode value).toAssembly ++
    [Assembly.Instr.jumpi (LabelSupply.label base (idx + 2))]

def switchTests (base : LabelSupply) : Nat → List (Word × Block) →
    Assembly.Program
  | _idx, [] => []
  | idx, (value, _body) :: rest =>
      switchTest base idx value ++ switchTests base (idx + 1) rest

def callToken (supply : LabelSupply) : Word :=
  EvmYul.UInt256.ofNat supply

end Stmt

mutual
  def Block.compileFromCtx
      (block : Block) (ctx : CompileContext) (supply : LabelSupply) :
      CompileResult :=
    match block with
    | ⟨[]⟩ => { code := [], next := supply, calls := [] }
    | ⟨stmt :: rest⟩ =>
        let compiledStmt := Stmt.compileFromCtxCore stmt ctx supply
        let compiledRest :=
          Block.compileFromCtx { stmts := rest } ctx compiledStmt.next
        compiledStmt.append compiledRest

  def Stmt.compileFromCtxCore
      (stmt : Stmt) (ctx : CompileContext) (supply : LabelSupply) :
      CompileResult :=
    match stmt with
    | .code code =>
        { code := code.toAssembly, next := supply, calls := [] }
    | .if_ cond body =>
        let bodyLabel := LabelSupply.label supply 0
        let endLabel := LabelSupply.label supply 1
        let compiledBody := Block.compileFromCtx body ctx (LabelSupply.next supply)
        { code :=
            cond.toAssembly ++
              [ Assembly.Instr.jumpi bodyLabel
              , Assembly.Instr.jump endLabel
              , Assembly.Instr.label bodyLabel
              ] ++
              compiledBody.code ++
              [Assembly.Instr.label endLabel]
          next := compiledBody.next
          calls := compiledBody.calls }
    | .switch scrutinee cases defaultBody =>
        let endLabel := LabelSupply.label supply 0
        let defaultLabel := LabelSupply.label supply 1
        let compiledCases :=
          SwitchCases.compileFromCtx cases ctx endLabel supply
            (LabelSupply.next supply) 0
        let compiledDefault :=
          SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
            compiledCases.next
        { code :=
            scrutinee.toAssembly ++
              Stmt.switchTests supply 0 cases ++
              [Assembly.Instr.jump defaultLabel] ++
              compiledCases.code ++
              compiledDefault.code ++
              [Assembly.Instr.label endLabel]
          next := compiledDefault.next
          calls := compiledCases.calls ++ compiledDefault.calls }
    | .for_ init cond post body =>
        let loopLabel := LabelSupply.label supply 0
        let bodyLabel := LabelSupply.label supply 1
        let postLabel := LabelSupply.label supply 2
        let endLabel := LabelSupply.label supply 3
        let loopOuterCtx : CompileContext :=
          { ctx with breakLabel? := none, continueLabel? := none }
        let compiledInit :=
          Block.compileFromCtx init loopOuterCtx (LabelSupply.next supply)
        let bodyCtx : CompileContext :=
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
        let compiledBody := Block.compileFromCtx body bodyCtx compiledInit.next
        let compiledPost := Block.compileFromCtx post loopOuterCtx compiledBody.next
        { code :=
            compiledInit.code ++
              [Assembly.Instr.label loopLabel] ++
              cond.toAssembly ++
              [ Assembly.Instr.jumpi bodyLabel
              , Assembly.Instr.jump endLabel
              , Assembly.Instr.label bodyLabel
              ] ++
              compiledBody.code ++
              [Assembly.Instr.label postLabel] ++
              compiledPost.code ++
              [ Assembly.Instr.jump loopLabel
              , Assembly.Instr.label endLabel
              ]
          next := compiledPost.next
          calls := compiledInit.calls ++ compiledBody.calls ++ compiledPost.calls }
    | .brk =>
        { code := Stmt.jumpOrInvalid ctx.breakLabel?, next := supply, calls := [] }
    | .cont =>
        { code := Stmt.jumpOrInvalid ctx.continueLabel?, next := supply, calls := [] }
    | .leave =>
        { code := Stmt.jumpOrInvalid ctx.leaveLabel?, next := supply, calls := [] }
    | .call name =>
        let returnLabel := LabelSupply.label supply 0
        let token := Stmt.callToken supply
        match ProcList.lookup? name ctx.procs with
        | none =>
            { code := [Assembly.Instr.prim .invalid]
              next := LabelSupply.next supply
              calls := [] }
        | some proc =>
            { code :=
                [Assembly.Instr.push token] ++
                  StackShuffle.sinkTopUnder proc.argc ++
                  [ Assembly.Instr.jump (ProcLabel.entry name)
                  , Assembly.Instr.label returnLabel
                  ]
              next := LabelSupply.next supply
              calls :=
                [{ procName := name, token := token, returnLabel := returnLabel }] }
    | .terminal kind =>
        { code := [Assembly.Instr.prim kind.toPrimOp], next := supply, calls := [] }

  def SwitchCases.compileFromCtx
      (cases : List (Word × Block)) (ctx : CompileContext)
      (endLabel : Assembly.Label) (base supply : LabelSupply) (idx : Nat) :
      CompileResult :=
    match cases with
    | [] => { code := [], next := supply, calls := [] }
    | (_value, body) :: rest =>
        let caseLabel := LabelSupply.label base (idx + 2)
        let compiledBody := Block.compileFromCtx body ctx supply
        let compiledHead : CompileResult :=
          { code :=
              [ Assembly.Instr.label caseLabel
              , Assembly.Instr.prim .pop
              ] ++
              compiledBody.code ++
              [Assembly.Instr.jump endLabel]
            next := compiledBody.next
            calls := compiledBody.calls }
        let compiledTail :=
          SwitchCases.compileFromCtx rest ctx endLabel base compiledHead.next
            (idx + 1)
        compiledHead.append compiledTail

  def SwitchDefault.compileFromCtx
      (defaultBody : Option Block) (ctx : CompileContext)
      (endLabel defaultLabel : Assembly.Label) (supply : LabelSupply) :
      CompileResult :=
    match defaultBody with
    | none =>
        { code :=
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            ]
          next := supply
          calls := [] }
    | some body =>
        let compiledBody := Block.compileFromCtx body ctx supply
        { code :=
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            ] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel]
          next := compiledBody.next
          calls := compiledBody.calls }
end

namespace CompilerFacts

namespace GeneratedNoCallCreate

set_option linter.unusedSimpArgs false in
theorem swapInstr (depth : Nat) :
    (StackShuffle.swapInstr depth).usesCallCreate = false := by
  by_cases h1 : depth = 1
  · subst depth; rfl
  by_cases h2 : depth = 2
  · subst depth; rfl
  by_cases h3 : depth = 3
  · subst depth; rfl
  by_cases h4 : depth = 4
  · subst depth; rfl
  by_cases h5 : depth = 5
  · subst depth; rfl
  by_cases h6 : depth = 6
  · subst depth; rfl
  by_cases h7 : depth = 7
  · subst depth; rfl
  by_cases h8 : depth = 8
  · subst depth; rfl
  by_cases h9 : depth = 9
  · subst depth; rfl
  by_cases h10 : depth = 10
  · subst depth; rfl
  by_cases h11 : depth = 11
  · subst depth; rfl
  by_cases h12 : depth = 12
  · subst depth; rfl
  by_cases h13 : depth = 13
  · subst depth; rfl
  by_cases h14 : depth = 14
  · subst depth; rfl
  by_cases h15 : depth = 15
  · subst depth; rfl
  by_cases h16 : depth = 16
  · subst depth; rfl
  simp [StackShuffle.swapInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, Assembly.Instr.usesCallCreate,
    Assembly.PrimOp.isCallCreate]

set_option linter.unusedSimpArgs false in
theorem dupInstr (depth : Nat) :
    (StackShuffle.dupInstr depth).usesCallCreate = false := by
  by_cases h1 : depth = 1
  · subst depth; rfl
  by_cases h2 : depth = 2
  · subst depth; rfl
  by_cases h3 : depth = 3
  · subst depth; rfl
  by_cases h4 : depth = 4
  · subst depth; rfl
  by_cases h5 : depth = 5
  · subst depth; rfl
  by_cases h6 : depth = 6
  · subst depth; rfl
  by_cases h7 : depth = 7
  · subst depth; rfl
  by_cases h8 : depth = 8
  · subst depth; rfl
  by_cases h9 : depth = 9
  · subst depth; rfl
  by_cases h10 : depth = 10
  · subst depth; rfl
  by_cases h11 : depth = 11
  · subst depth; rfl
  by_cases h12 : depth = 12
  · subst depth; rfl
  by_cases h13 : depth = 13
  · subst depth; rfl
  by_cases h14 : depth = 14
  · subst depth; rfl
  by_cases h15 : depth = 15
  · subst depth; rfl
  by_cases h16 : depth = 16
  · subst depth; rfl
  simp [StackShuffle.dupInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, Assembly.Instr.usesCallCreate,
    Assembly.PrimOp.isCallCreate]

theorem all_false_of_usesCallCreate_false {program : Assembly.Program}
    (hProgram : Assembly.Program.usesCallCreate program = false) :
    ∀ instr ∈ program, instr.usesCallCreate = false := by
  simpa [Assembly.Program.usesCallCreate] using hProgram

theorem sinkTopUnder (depth : Nat) :
    Assembly.Program.usesCallCreate (StackShuffle.sinkTopUnder depth) = false := by
  induction depth with
  | zero =>
      rfl
  | succ depth ih =>
      have hRest := all_false_of_usesCallCreate_false ih
      simp [StackShuffle.sinkTopUnder, Assembly.Program.usesCallCreate,
        swapInstr]
      exact hRest

theorem liftBuriedToTop (depth : Nat) :
    Assembly.Program.usesCallCreate (StackShuffle.liftBuriedToTop depth) = false := by
  induction depth with
  | zero =>
      rfl
  | succ depth ih =>
      have hRest := all_false_of_usesCallCreate_false ih
      simp [StackShuffle.liftBuriedToTop, Assembly.Program.usesCallCreate,
        swapInstr]
      exact hRest

theorem removeBuriedUnder (depth : Nat) :
    Assembly.Program.usesCallCreate (StackShuffle.removeBuriedUnder depth) = false := by
  have hRest := all_false_of_usesCallCreate_false (liftBuriedToTop depth)
  simp [StackShuffle.removeBuriedUnder, Assembly.Program.usesCallCreate,
    Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate]
  exact hRest

theorem switchTestCode (value : Word) :
    (Stmt.switchTestCode value).usesCallCreate = false := by
  rfl

set_option linter.unusedSimpArgs false in
theorem switchTest (base : LabelSupply) (idx : Nat) (value : Word) :
    Assembly.Program.usesCallCreate (Stmt.switchTest base idx value) = false := by
  have hCodeAsm :
      Assembly.Program.usesCallCreate (Stmt.switchTestCode value).toAssembly =
        false := by
    simpa [Code.toAssembly_usesCallCreate] using switchTestCode value
  have hCodeAll := all_false_of_usesCallCreate_false hCodeAsm
  simp [Stmt.switchTest, Code.toAssembly_usesCallCreate, switchTestCode,
    Assembly.Program.usesCallCreate, Assembly.Program.usesCallCreate_append,
    Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate]
  exact hCodeAll

set_option linter.unusedSimpArgs false in
theorem switchTests (base : LabelSupply) (idx : Nat)
    (cases : List (Word × Block)) :
    Assembly.Program.usesCallCreate (Stmt.switchTests base idx cases) = false := by
  induction cases generalizing idx with
  | nil =>
      rfl
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      have hTestAll := all_false_of_usesCallCreate_false
        (switchTest base idx value)
      have hRestAll := all_false_of_usesCallCreate_false (ih (idx + 1))
      simp [Stmt.switchTests, Assembly.Program.usesCallCreate_append,
        Assembly.Program.usesCallCreate, switchTest, ih]
      exact ⟨hTestAll, hRestAll⟩

end GeneratedNoCallCreate

set_option linter.unusedSimpArgs false in
theorem block_compileFromCtx_noCallCreate (block : Block) :
    ∀ ctx supply,
      block.usesCallCreate = false →
        Assembly.Program.usesCallCreate
          (Block.compileFromCtx block ctx supply).code = false := by
  exact Block.rec
    (motive_1 := fun block => ∀ ctx supply,
      block.usesCallCreate = false →
        Assembly.Program.usesCallCreate
          (Block.compileFromCtx block ctx supply).code = false)
    (motive_2 := fun stmt => ∀ ctx supply,
      stmt.usesCallCreate = false →
        Assembly.Program.usesCallCreate
          (Stmt.compileFromCtxCore stmt ctx supply).code = false)
    (motive_3 := fun stmts => ∀ ctx supply,
      StmtList.usesCallCreate stmts = false →
        Assembly.Program.usesCallCreate
          (Block.compileFromCtx { stmts := stmts } ctx supply).code = false)
    (motive_4 := fun cases => ∀ ctx endLabel base supply idx,
      CaseList.usesCallCreate cases = false →
        Assembly.Program.usesCallCreate
          (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).code = false)
    (motive_5 := fun defaultBody => ∀ ctx endLabel defaultLabel supply,
      Default.usesCallCreate defaultBody = false →
        Assembly.Program.usesCallCreate
          (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel supply).code = false)
    (motive_6 := fun pair => ∀ ctx supply,
      pair.2.usesCallCreate = false →
        Assembly.Program.usesCallCreate
          (Block.compileFromCtx pair.2 ctx supply).code = false)
    (fun _stmts hStmts => hStmts)
    (fun code => by
      intro ctx supply hCode
      simpa [Stmt.compileFromCtxCore, Stmt.usesCallCreate,
        Code.toAssembly_usesCallCreate] using hCode)
    (fun cond body hBody => by
      intro ctx supply hStmt
      have hParts :
          cond.usesCallCreate = false ∧ body.usesCallCreate = false := by
        simpa [Stmt.usesCallCreate] using hStmt
      have hCondAsm :
          Assembly.Program.usesCallCreate cond.toAssembly = false := by
        simpa [Code.toAssembly_usesCallCreate] using hParts.1
      have hCompiledBody :=
        hBody ctx (LabelSupply.next supply) hParts.2
      have hCondAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCondAsm
      have hBodyAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCompiledBody
      simp [Stmt.compileFromCtxCore, Assembly.Program.usesCallCreate,
        Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate,
        hCondAsm, hCompiledBody]
      exact ⟨hCondAll, hBodyAll⟩)
    (fun scrutinee cases defaultBody hCases hDefault => by
      intro ctx supply hStmt
      have hParts :
          scrutinee.usesCallCreate = false ∧
            CaseList.usesCallCreate cases = false ∧
              Default.usesCallCreate defaultBody = false := by
        simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
      have hScrutineeAsm :
          Assembly.Program.usesCallCreate scrutinee.toAssembly = false := by
        simpa [Code.toAssembly_usesCallCreate] using hParts.1
      have hCompiledCases :=
        hCases ctx (LabelSupply.label supply 0) supply (LabelSupply.next supply)
          0 hParts.2.1
      have hCompiledDefault :=
        hDefault ctx (LabelSupply.label supply 0) (LabelSupply.label supply 1)
          (SwitchCases.compileFromCtx cases ctx (LabelSupply.label supply 0)
            supply (LabelSupply.next supply) 0).next hParts.2.2
      have hScrutineeAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hScrutineeAsm
      have hTestsAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false
          (GeneratedNoCallCreate.switchTests supply 0 cases)
      have hCasesAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCompiledCases
      have hDefaultAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCompiledDefault
      simp [Stmt.compileFromCtxCore, Assembly.Program.usesCallCreate,
        Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate,
        hScrutineeAsm, hCompiledCases, hCompiledDefault]
      exact ⟨hScrutineeAll, hTestsAll, hCasesAll, hDefaultAll⟩)
    (fun init cond post body hInit hPost hBody => by
      intro ctx supply hStmt
      have hParts :
          init.usesCallCreate = false ∧ cond.usesCallCreate = false ∧
            post.usesCallCreate = false ∧ body.usesCallCreate = false := by
        simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
      have hCondAsm :
          Assembly.Program.usesCallCreate cond.toAssembly = false := by
        simpa [Code.toAssembly_usesCallCreate] using hParts.2.1
      let loopOuterCtx : CompileContext :=
        { ctx with breakLabel? := none, continueLabel? := none }
      let compiledInit :=
        Block.compileFromCtx init loopOuterCtx (LabelSupply.next supply)
      let bodyCtx : CompileContext :=
        { ctx with
          breakLabel? := some (LabelSupply.label supply 3)
          continueLabel? := some (LabelSupply.label supply 2) }
      have hCompiledInit :=
        hInit loopOuterCtx (LabelSupply.next supply) hParts.1
      have hCompiledBody :=
        hBody bodyCtx compiledInit.next hParts.2.2.2
      have hCompiledPost :=
        hPost loopOuterCtx (Block.compileFromCtx body bodyCtx compiledInit.next).next
          hParts.2.2.1
      have hInitAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCompiledInit
      have hCondAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCondAsm
      have hBodyAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCompiledBody
      have hPostAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCompiledPost
      simp [Stmt.compileFromCtxCore, Assembly.Program.usesCallCreate,
        Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate,
        hCondAsm, hCompiledInit, hCompiledBody, hCompiledPost, loopOuterCtx,
        bodyCtx, compiledInit]
      exact ⟨hInitAll, hCondAll, hBodyAll, hPostAll⟩)
    (by
      intro ctx supply _hStmt
      cases hBreak : ctx.breakLabel? <;>
        simp [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid,
          Assembly.Program.usesCallCreate, Assembly.Instr.usesCallCreate,
          Assembly.PrimOp.isCallCreate, hBreak])
    (by
      intro ctx supply _hStmt
      cases hContinue : ctx.continueLabel? <;>
        simp [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid,
          Assembly.Program.usesCallCreate, Assembly.Instr.usesCallCreate,
          Assembly.PrimOp.isCallCreate, hContinue])
    (by
      intro ctx supply _hStmt
      cases hLeave : ctx.leaveLabel? <;>
        simp [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid,
          Assembly.Program.usesCallCreate, Assembly.Instr.usesCallCreate,
          Assembly.PrimOp.isCallCreate, hLeave])
    (fun name => by
      intro ctx supply _hStmt
      cases hLookup : ProcList.lookup? name ctx.procs with
      | none =>
          simp [Stmt.compileFromCtxCore, hLookup,
            Assembly.Program.usesCallCreate, Assembly.Instr.usesCallCreate,
            Assembly.PrimOp.isCallCreate]
      | some proc =>
          have hSinkAll :=
            GeneratedNoCallCreate.all_false_of_usesCallCreate_false
              (GeneratedNoCallCreate.sinkTopUnder proc.argc)
          simp [Stmt.compileFromCtxCore, hLookup,
            Assembly.Program.usesCallCreate, Assembly.Instr.usesCallCreate,
            Assembly.PrimOp.isCallCreate, GeneratedNoCallCreate.sinkTopUnder]
          exact hSinkAll)
    (fun kind => by
      intro ctx supply _hStmt
      cases kind <;>
        simp [Stmt.compileFromCtxCore, Assembly.Program.usesCallCreate,
          Assembly.Instr.usesCallCreate, Assembly.HaltKind.toPrimOp,
          Assembly.PrimOp.isCallCreate])
    (by
      intro ctx supply _hStmts
      simp [Block.compileFromCtx, Assembly.Program.usesCallCreate])
    (fun head tail hHead hTail => by
      intro ctx supply hStmts
      have hParts :
          head.usesCallCreate = false ∧ StmtList.usesCallCreate tail = false := by
        simpa [StmtList.usesCallCreate] using hStmts
      have hCompiledHead := hHead ctx supply hParts.1
      have hCompiledTail :=
        hTail ctx (Stmt.compileFromCtxCore head ctx supply).next hParts.2
      simp [Block.compileFromCtx, CompileResult.append,
        Assembly.Program.usesCallCreate_append, hCompiledHead, hCompiledTail])
    (by
      intro ctx endLabel base supply idx _hCases
      simp [SwitchCases.compileFromCtx, Assembly.Program.usesCallCreate])
    (fun head tail hHead hTail => by
      intro ctx endLabel base supply idx hCases
      rcases head with ⟨value, body⟩
      have hParts :
          body.usesCallCreate = false ∧ CaseList.usesCallCreate tail = false := by
        simpa [CaseList.usesCallCreate] using hCases
      have hCompiledBody := hHead ctx supply hParts.1
      have hCompiledTail :=
        hTail ctx endLabel base (Block.compileFromCtx body ctx supply).next
          (idx + 1) hParts.2
      have hBodyAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCompiledBody
      have hTailAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCompiledTail
      simp [SwitchCases.compileFromCtx, CompileResult.append,
        Assembly.Program.usesCallCreate, Assembly.Instr.usesCallCreate,
        Assembly.PrimOp.isCallCreate, hCompiledBody, hCompiledTail]
      exact ⟨hBodyAll, hTailAll⟩)
    (by
      intro ctx endLabel defaultLabel supply _hDefault
      simp [SwitchDefault.compileFromCtx, Assembly.Program.usesCallCreate,
        Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate])
    (fun body hBody => by
      intro ctx endLabel defaultLabel supply hDefault
      have hCompiledBody := hBody ctx supply (by simpa [Default.usesCallCreate] using hDefault)
      have hBodyAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCompiledBody
      simp [SwitchDefault.compileFromCtx, Assembly.Program.usesCallCreate,
        Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate,
        hCompiledBody]
      exact hBodyAll)
    (fun _value body hBody => by
      intro ctx supply hPair
      exact hBody ctx supply hPair)
    block

theorem call_compileFromCtxCore_code_of_lookup
    {ctx : CompileContext} {name : Name} {supply : LabelSupply}
    {proc : Proc}
    (hLookup : ProcList.lookup? name ctx.procs = some proc) :
    (Stmt.compileFromCtxCore (.call name) ctx supply).code =
      [Assembly.Instr.push (Stmt.callToken supply)] ++
        StackShuffle.sinkTopUnder proc.argc ++
        [ Assembly.Instr.jump (ProcLabel.entry name)
        , Assembly.Instr.label (LabelSupply.label supply 0)
        ] := by
  simp [Stmt.compileFromCtxCore, hLookup]

theorem exists_call_compileFromCtxCore_code_of_contains
    {ctx : CompileContext} {name : Name} {supply : LabelSupply}
    (hContains : ProcList.contains ctx.procs name) :
    ∃ proc,
      ProcList.lookup? name ctx.procs = some proc ∧
        (Stmt.compileFromCtxCore (.call name) ctx supply).code =
          [Assembly.Instr.push (Stmt.callToken supply)] ++
            StackShuffle.sinkTopUnder proc.argc ++
            [ Assembly.Instr.jump (ProcLabel.entry name)
            , Assembly.Instr.label (LabelSupply.label supply 0)
            ] := by
  rcases ProcList.exists_lookup?_of_contains hContains with ⟨proc, hLookup⟩
  exact
    ⟨proc, hLookup,
      call_compileFromCtxCore_code_of_lookup (ctx := ctx) (name := name)
        (supply := supply) hLookup⟩

end CompilerFacts

structure CompiledProcBody where
  proc : Proc
  code : Assembly.Program
  next : LabelSupply
  calls : List CallSite

namespace Proc

def compileBody (allProcs : List Proc) (proc : Proc)
    (supply : LabelSupply) :
    CompiledProcBody :=
  let ctx : CompileContext :=
    { procs := allProcs, leaveLabel? := some (ProcLabel.exit proc.name) }
  let compiledBody := Block.compileFromCtx proc.body ctx supply
  { proc := proc
    code :=
      [Assembly.Instr.label (ProcLabel.entry proc.name)] ++
        compiledBody.code ++
        [Assembly.Instr.label (ProcLabel.exit proc.name)]
    next := compiledBody.next
    calls := compiledBody.calls }

end Proc

namespace ProcBodies

def compile :
    List Proc → List Proc → LabelSupply →
      List CompiledProcBody × LabelSupply × List CallSite
  | _allProcs, [], supply => ([], supply, [])
  | allProcs, proc :: rest, supply =>
      let compiled := Proc.compileBody allProcs proc supply
      let (compiledRest, next, callsRest) :=
        compile allProcs rest compiled.next
      (compiled :: compiledRest, next, compiled.calls ++ callsRest)

end ProcBodies

namespace Dispatch

def testsForRetc (base : LabelSupply) (retc : Nat) :
    Nat → List CallSite → Assembly.Program
  | _idx, [] => []
  | idx, site :: rest =>
      [ StackShuffle.dupInstr (retc + 1)
      , Assembly.Instr.push site.token
      , Assembly.Instr.prim .eq
      , Assembly.Instr.jumpi (LabelSupply.label base idx)
      ] ++ testsForRetc base retc (idx + 1) rest

def casesForRetc (base : LabelSupply) (retc : Nat) :
    Nat → List CallSite → Assembly.Program
  | _idx, [] => []
  | idx, site :: rest =>
      [Assembly.Instr.label (LabelSupply.label base idx)] ++
        StackShuffle.removeBuriedUnder retc ++
        [Assembly.Instr.jump site.returnLabel] ++
        casesForRetc base retc (idx + 1) rest

def forProc (proc : Proc) (sites : List CallSite) (supply : LabelSupply) :
    CompileResult :=
  let procSites := sites.filter (CallSite.forProc proc.name)
  { code :=
      testsForRetc supply proc.retc 0 procSites ++
        [Assembly.Instr.prim .invalid] ++
        casesForRetc supply proc.retc 0 procSites
    next := LabelSupply.next supply
    calls := [] }

end Dispatch

namespace CompiledProcBodies

def emit :
    List CompiledProcBody → List CallSite → LabelSupply → CompileResult
  | [], _sites, supply => { code := [], next := supply, calls := [] }
  | procBody :: rest, sites, supply =>
      let dispatch := Dispatch.forProc procBody.proc sites supply
      let emittedRest := emit rest sites dispatch.next
      { code := procBody.code ++ dispatch.code ++ emittedRest.code
        next := emittedRest.next
        calls := [] }

end CompiledProcBodies

namespace Program

def compileResult (program : Program) : CompileResult :=
  let mainCtx : CompileContext := { procs := program.procs }
  let main := Block.compileFromCtx program.body mainCtx 0
  let (procBodies, bodyNext, procCalls) :=
    ProcBodies.compile program.procs program.procs main.next
  let allCalls := main.calls ++ procCalls
  let emittedProcs := CompiledProcBodies.emit procBodies allCalls bodyNext
  { code :=
      main.code ++
        [Assembly.Instr.jump ProcLabel.programEnd] ++
        emittedProcs.code ++
        [Assembly.Instr.label ProcLabel.programEnd]
    next := emittedProcs.next
    calls := allCalls }

def compile (program : Program) : Assembly.Program :=
  program.compileResult.code

def CallTokensUnique (program : Program) : Prop :=
  (program.compileResult.calls.map CallSite.token).Nodup

end Program

namespace CompilerFacts

set_option linter.unusedSimpArgs false in
theorem proc_compileBody_noCallCreate
    (allProcs : List Proc) (proc : Proc) (supply : LabelSupply)
    (hProc : proc.usesCallCreate = false) :
    Assembly.Program.usesCallCreate
      (Proc.compileBody allProcs proc supply).code = false := by
  have hBody :=
    block_compileFromCtx_noCallCreate proc.body
      { procs := allProcs, leaveLabel? := some (ProcLabel.exit proc.name) }
      supply (by simpa [Proc.usesCallCreate] using hProc)
  have hBodyAll :=
    GeneratedNoCallCreate.all_false_of_usesCallCreate_false hBody
  simp [Proc.compileBody, Assembly.Program.usesCallCreate,
    Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate, hBody]
  exact hBodyAll

set_option linter.unusedSimpArgs false in
theorem dispatch_testsForRetc_noCallCreate
    (base : LabelSupply) (retc idx : Nat) (sites : List CallSite) :
    Assembly.Program.usesCallCreate
      (Dispatch.testsForRetc base retc idx sites) = false := by
  induction sites generalizing idx with
  | nil =>
      rfl
  | cons site rest ih =>
      have hDup := GeneratedNoCallCreate.dupInstr (retc + 1)
      have hRestAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false (ih (idx + 1))
      simp [Dispatch.testsForRetc, Assembly.Program.usesCallCreate,
        Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate,
        GeneratedNoCallCreate.dupInstr, ih]
      exact ⟨hDup, hRestAll⟩

set_option linter.unusedSimpArgs false in
theorem dispatch_casesForRetc_noCallCreate
    (base : LabelSupply) (retc idx : Nat) (sites : List CallSite) :
    Assembly.Program.usesCallCreate
      (Dispatch.casesForRetc base retc idx sites) = false := by
  induction sites generalizing idx with
  | nil =>
      rfl
  | cons site rest ih =>
      have hRemoveAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false
          (GeneratedNoCallCreate.removeBuriedUnder retc)
      have hRestAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false (ih (idx + 1))
      simp [Dispatch.casesForRetc, Assembly.Program.usesCallCreate,
        Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate,
        GeneratedNoCallCreate.removeBuriedUnder, ih]
      exact ⟨hRemoveAll, hRestAll⟩

set_option linter.unusedSimpArgs false in
theorem dispatch_forProc_noCallCreate
    (proc : Proc) (sites : List CallSite) (supply : LabelSupply) :
    Assembly.Program.usesCallCreate
      (Dispatch.forProc proc sites supply).code = false := by
  have hTests :=
    dispatch_testsForRetc_noCallCreate supply proc.retc 0
      (sites.filter (CallSite.forProc proc.name))
  have hCases :=
    dispatch_casesForRetc_noCallCreate supply proc.retc 0
      (sites.filter (CallSite.forProc proc.name))
  have hTestsAll :=
    GeneratedNoCallCreate.all_false_of_usesCallCreate_false hTests
  have hCasesAll :=
    GeneratedNoCallCreate.all_false_of_usesCallCreate_false hCases
  simp [Dispatch.forProc, Assembly.Program.usesCallCreate,
    Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate,
    hTests, hCases]
  exact ⟨hTestsAll, hCasesAll⟩

set_option linter.unusedSimpArgs false in
theorem compiledProcBodies_emit_noCallCreate :
    ∀ (bodies : List CompiledProcBody) (sites : List CallSite)
      (supply : LabelSupply),
      (∀ body ∈ bodies, Assembly.Program.usesCallCreate body.code = false) →
        Assembly.Program.usesCallCreate
          (CompiledProcBodies.emit bodies sites supply).code = false
  | [], _sites, _supply, _hBodies => by
      simp [CompiledProcBodies.emit, Assembly.Program.usesCallCreate]
  | body :: rest, sites, supply, hBodies => by
      have hBody := hBodies body (by simp)
      have hRestBodies :
          ∀ body' ∈ rest, Assembly.Program.usesCallCreate body'.code = false := by
        intro body' hMem
        exact hBodies body' (by simp [hMem])
      have hDispatch := dispatch_forProc_noCallCreate body.proc sites supply
      have hRest :=
        compiledProcBodies_emit_noCallCreate rest sites
          (Dispatch.forProc body.proc sites supply).next hRestBodies
      have hBodyAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hBody
      have hDispatchAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hDispatch
      have hRestAll :=
        GeneratedNoCallCreate.all_false_of_usesCallCreate_false hRest
      simp [CompiledProcBodies.emit, Assembly.Program.usesCallCreate,
        Assembly.Program.usesCallCreate_append, hBody, hDispatch, hRest]
      exact ⟨hBodyAll, hDispatchAll, hRestAll⟩

set_option linter.unusedSimpArgs false in
theorem procBodies_compile_bodies_noCallCreate :
    ∀ (procs allProcs : List Proc) (supply : LabelSupply),
      ProcList.usesCallCreate procs = false →
        ∀ body ∈ (ProcBodies.compile allProcs procs supply).1,
          Assembly.Program.usesCallCreate body.code = false
  | [], _allProcs, _supply, _hProcs, body, hMem => by
      simp [ProcBodies.compile] at hMem
  | proc :: rest, allProcs, supply, hProcs, body, hMem => by
      have hParts :
          proc.usesCallCreate = false ∧ ProcList.usesCallCreate rest = false := by
        simpa [ProcList.usesCallCreate] using hProcs
      let compiled := Proc.compileBody allProcs proc supply
      have hCompiled :=
        proc_compileBody_noCallCreate allProcs proc supply hParts.1
      have hRest :=
        procBodies_compile_bodies_noCallCreate rest allProcs compiled.next
          hParts.2
      simp [ProcBodies.compile, compiled] at hMem
      rcases hMem with hEq | hMem
      · cases hEq
        exact hCompiled
      · exact hRest body hMem

set_option linter.unusedSimpArgs false in
theorem procBodies_compile_emit_noCallCreate
    (procs allProcs : List Proc) (supply : LabelSupply)
    (sites : List CallSite)
    (hProcs : ProcList.usesCallCreate procs = false) :
    Assembly.Program.usesCallCreate
      (CompiledProcBodies.emit
        (ProcBodies.compile allProcs procs supply).1
        sites
        (ProcBodies.compile allProcs procs supply).2.1).code = false := by
  exact compiledProcBodies_emit_noCallCreate
    (ProcBodies.compile allProcs procs supply).1 sites
    (ProcBodies.compile allProcs procs supply).2.1
    (procBodies_compile_bodies_noCallCreate procs allProcs supply hProcs)

set_option linter.unusedSimpArgs false in
theorem program_compile_noCallCreate (program : Program)
    (hProgram : program.usesCallCreate = false) :
    Assembly.Program.usesCallCreate program.compile = false := by
  have hParts :
      ProcList.usesCallCreate program.procs = false ∧
        program.body.usesCallCreate = false := by
    simpa [Program.usesCallCreate] using hProgram
  let mainCtx : CompileContext := { procs := program.procs }
  let main := Block.compileFromCtx program.body mainCtx 0
  let procBodies := ProcBodies.compile program.procs program.procs main.next
  have hMain :=
    block_compileFromCtx_noCallCreate program.body mainCtx 0 hParts.2
  have hEmitted :=
    procBodies_compile_emit_noCallCreate program.procs program.procs main.next
      (main.calls ++ procBodies.2.2) hParts.1
  have hMainAll :=
    GeneratedNoCallCreate.all_false_of_usesCallCreate_false hMain
  have hEmittedAll :=
    GeneratedNoCallCreate.all_false_of_usesCallCreate_false hEmitted
  simp [Program.compile, Program.compileResult, mainCtx, main, procBodies,
    Assembly.Program.usesCallCreate, Assembly.Program.usesCallCreate_append,
    Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate, hMain,
    hEmitted]
  exact ⟨hMainAll, hEmittedAll⟩

end CompilerFacts

end Structured
end EvmCompiler
