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

structure CompileResult where
  code : Assembly.Program
  next : LabelSupply
  deriving DecidableEq, Repr

namespace CompileResult

def append (left right : CompileResult) : CompileResult where
  code := left.code ++ right.code
  next := right.next

end CompileResult

namespace Code

theorem toAssembly_labels (code : Code) :
    Assembly.Program.labels code.toAssembly = [] := by
  induction code with
  | nil =>
      rfl
  | cons instr rest ih =>
      cases instr <;> simpa [Code.toAssembly, BasicInstr.toAssembly, Assembly.Program.labels] using ih

theorem toAssembly_labelPcFrom_none (code : Code) (base : Nat)
    (target : Assembly.Label) :
    Assembly.Program.labelPcFrom code.toAssembly base target = none := by
  exact
    Assembly.Program.labelPcFrom_none_of_not_mem_labels
      code.toAssembly base (by simp [toAssembly_labels])

theorem toAssembly_labelPc_none (code : Code) (target : Assembly.Label) :
    Assembly.Program.labelPc code.toAssembly target = none := by
  exact
    Assembly.Program.labelPc_none_of_not_mem_labels
      code.toAssembly (by simp [toAssembly_labels])

end Code

mutual
  def Block.compileFrom : LabelSupply → Block → CompileResult
    | supply, ⟨[]⟩ =>
        { code := [], next := supply }
    | supply, ⟨stmt :: rest⟩ =>
        let compiledStmt := Stmt.compileFrom supply stmt
        let compiledRest := Block.compileFrom compiledStmt.next ⟨rest⟩
        compiledStmt.append compiledRest

  def Stmt.compileFrom : LabelSupply → Stmt → CompileResult
    | supply, Stmt.code code =>
        { code := code.toAssembly, next := supply }
    | supply, Stmt.ifElse cond thenBody elseBody =>
        let thenLabel := LabelSupply.label supply 0
        let endLabel := LabelSupply.label supply 1
        let afterLabels := LabelSupply.next supply
        let compiledElse := Block.compileFrom afterLabels elseBody
        let compiledThen := Block.compileFrom compiledElse.next thenBody
        { code :=
            cond.toAssembly ++
              [Assembly.Instr.jumpi thenLabel] ++
              compiledElse.code ++
              [ Assembly.Instr.jump endLabel
              , Assembly.Instr.label thenLabel
              ] ++
              compiledThen.code ++
              [Assembly.Instr.label endLabel]
          next := compiledThen.next }
    | supply, Stmt.for_ init cond post body =>
        let loopLabel := LabelSupply.label supply 0
        let bodyLabel := LabelSupply.label supply 1
        let endLabel := LabelSupply.label supply 2
        let afterLabels := LabelSupply.next supply
        let compiledInit := Block.compileFrom afterLabels init
        let compiledBody := Block.compileFrom compiledInit.next body
        let compiledPost := Block.compileFrom compiledBody.next post
        { code :=
            compiledInit.code ++
              [Assembly.Instr.label loopLabel] ++
              cond.toAssembly ++
              [ Assembly.Instr.jumpi bodyLabel
              , Assembly.Instr.jump endLabel
              , Assembly.Instr.label bodyLabel
              ] ++
              compiledBody.code ++
              compiledPost.code ++
              [ Assembly.Instr.jump loopLabel
              , Assembly.Instr.label endLabel
              ]
          next := compiledPost.next }
end

namespace Block

def compile (block : Block) : Assembly.Program :=
  (compileFrom 0 block).code

end Block

namespace Program

def compile (program : Program) : Assembly.Program :=
  program.body.compile

def compile? (program : Program) : Option Assembly.TargetProgram :=
  Assembly.compile? program.compile

end Program

end Structured
end EvmCompiler
