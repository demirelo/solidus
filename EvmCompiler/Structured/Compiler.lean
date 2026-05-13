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

namespace Label

def generatedScopeGe (supply : LabelSupply) : Assembly.Label → Prop
  | .generated scope _ => supply ≤ scope
  | .named _ => False

def generatedScopeLt (supply : LabelSupply) : Assembly.Label → Prop
  | .generated scope _ => scope < supply
  | .named _ => False

theorem generatedScopeGe_mono {low high : LabelSupply} {label : Assembly.Label}
    (hLowHigh : low ≤ high)
    (hLabel : generatedScopeGe high label) :
    generatedScopeGe low label := by
  cases label with
  | named name =>
      exact hLabel
  | generated scope tag =>
      exact Nat.le_trans hLowHigh hLabel

theorem generatedScopeGe_self (supply tag : Nat) :
    generatedScopeGe supply (Assembly.Label.generated supply tag) := by
  simp [generatedScopeGe]

theorem generatedScopeGe_next_self_false (supply tag : Nat) :
    ¬ generatedScopeGe (LabelSupply.next supply)
        (Assembly.Label.generated supply tag) := by
  simp [generatedScopeGe, LabelSupply.next]

theorem generatedScopeLt_mono {low high : LabelSupply} {label : Assembly.Label}
    (hLowHigh : low ≤ high)
    (hLabel : generatedScopeLt low label) :
    generatedScopeLt high label := by
  cases label with
  | named name =>
      exact hLabel
  | generated scope tag =>
      exact Nat.lt_of_lt_of_le hLabel hLowHigh

theorem generatedScopeLt_self_false (supply tag : Nat) :
    ¬ generatedScopeLt supply (Assembly.Label.generated supply tag) := by
  simp [generatedScopeLt]

end Label

namespace AssemblyProgram

def labelsGe (supply : LabelSupply) (program : Assembly.Program) : Prop :=
  ∀ label,
    label ∈ Assembly.Program.labels program →
      Label.generatedScopeGe supply label

def labelsLt (supply : LabelSupply) (program : Assembly.Program) : Prop :=
  ∀ label,
    label ∈ Assembly.Program.labels program →
      Label.generatedScopeLt supply label

theorem labelsGe_mono {low high : LabelSupply} {program : Assembly.Program}
    (hLowHigh : low ≤ high)
    (hLabels : labelsGe high program) :
    labelsGe low program := by
  intro label hMem
  exact Label.generatedScopeGe_mono hLowHigh (hLabels label hMem)

theorem labelsGe_nil (supply : LabelSupply) :
    labelsGe supply ([] : Assembly.Program) := by
  intro label hMem
  simp [Assembly.Program.labels] at hMem

theorem labelsLt_mono {low high : LabelSupply} {program : Assembly.Program}
    (hLowHigh : low ≤ high)
    (hLabels : labelsLt low program) :
    labelsLt high program := by
  intro label hMem
  exact Label.generatedScopeLt_mono hLowHigh (hLabels label hMem)

theorem labelsLt_nil (supply : LabelSupply) :
    labelsLt supply ([] : Assembly.Program) := by
  intro label hMem
  simp [Assembly.Program.labels] at hMem

theorem labelsGe_append {supply : LabelSupply}
    {left right : Assembly.Program}
    (hLeft : labelsGe supply left)
    (hRight : labelsGe supply right) :
    labelsGe supply (left ++ right) := by
  intro label hMem
  rw [Assembly.Program.labels_append] at hMem
  cases (List.mem_append.mp hMem) with
  | inl hLeftMem =>
      exact hLeft label hLeftMem
  | inr hRightMem =>
      exact hRight label hRightMem

theorem labelsLt_append {supply : LabelSupply}
    {left right : Assembly.Program}
    (hLeft : labelsLt supply left)
    (hRight : labelsLt supply right) :
    labelsLt supply (left ++ right) := by
  intro label hMem
  rw [Assembly.Program.labels_append] at hMem
  cases (List.mem_append.mp hMem) with
  | inl hLeftMem =>
      exact hLeft label hLeftMem
  | inr hRightMem =>
      exact hRight label hRightMem

theorem labelsGe_cons_label {supply : LabelSupply}
    {label : Assembly.Label} {rest : Assembly.Program}
    (hLabel : Label.generatedScopeGe supply label)
    (hRest : labelsGe supply rest) :
    labelsGe supply (Assembly.Instr.label label :: rest) := by
  intro query hMem
  simp [Assembly.Program.labels] at hMem
  cases hMem with
  | inl hEq =>
      cases hEq
      exact hLabel
  | inr hRestMem =>
      exact hRest query hRestMem

theorem labelsGe_cons_nonlabel {supply : LabelSupply}
    {instr : Assembly.Instr} {rest : Assembly.Program}
    (hInstr : ∀ label, instr ≠ Assembly.Instr.label label)
    (hRest : labelsGe supply rest) :
    labelsGe supply (instr :: rest) := by
  cases instr with
  | label name =>
      exfalso
      exact hInstr name rfl
  | prim op =>
      simpa [labelsGe, Assembly.Program.labels] using hRest
  | push value =>
      simpa [labelsGe, Assembly.Program.labels] using hRest
  | jump target =>
      simpa [labelsGe, Assembly.Program.labels] using hRest
  | jumpi target =>
      simpa [labelsGe, Assembly.Program.labels] using hRest

theorem labelsLt_cons_label {supply : LabelSupply}
    {label : Assembly.Label} {rest : Assembly.Program}
    (hLabel : Label.generatedScopeLt supply label)
    (hRest : labelsLt supply rest) :
    labelsLt supply (Assembly.Instr.label label :: rest) := by
  intro query hMem
  simp [Assembly.Program.labels] at hMem
  cases hMem with
  | inl hEq =>
      cases hEq
      exact hLabel
  | inr hRestMem =>
      exact hRest query hRestMem

theorem labelsLt_cons_nonlabel {supply : LabelSupply}
    {instr : Assembly.Instr} {rest : Assembly.Program}
    (hInstr : ∀ label, instr ≠ Assembly.Instr.label label)
    (hRest : labelsLt supply rest) :
    labelsLt supply (instr :: rest) := by
  cases instr with
  | label name =>
      exfalso
      exact hInstr name rfl
  | prim op =>
      simpa [labelsLt, Assembly.Program.labels] using hRest
  | push value =>
      simpa [labelsLt, Assembly.Program.labels] using hRest
  | jump target =>
      simpa [labelsLt, Assembly.Program.labels] using hRest
  | jumpi target =>
      simpa [labelsLt, Assembly.Program.labels] using hRest

theorem labelsGe_single_label {supply : LabelSupply}
    {label : Assembly.Label}
    (hLabel : Label.generatedScopeGe supply label) :
    labelsGe supply [Assembly.Instr.label label] := by
  intro query hMem
  simp [Assembly.Program.labels] at hMem
  cases hMem
  simpa using hLabel

theorem labelsGe_single_nonlabel {supply : LabelSupply}
    {instr : Assembly.Instr}
    (hInstr : ∀ label, instr ≠ Assembly.Instr.label label) :
    labelsGe supply [instr] := by
  intro query hMem
  cases instr <;> simp [Assembly.Program.labels] at hMem
  exact (hInstr _ rfl).elim

theorem labelsLt_single_label {supply : LabelSupply}
    {label : Assembly.Label}
    (hLabel : Label.generatedScopeLt supply label) :
    labelsLt supply [Assembly.Instr.label label] := by
  intro query hMem
  simp [Assembly.Program.labels] at hMem
  cases hMem
  simpa using hLabel

theorem labelsLt_single_nonlabel {supply : LabelSupply}
    {instr : Assembly.Instr}
    (hInstr : ∀ label, instr ≠ Assembly.Instr.label label) :
    labelsLt supply [instr] := by
  intro query hMem
  cases instr <;> simp [Assembly.Program.labels] at hMem
  exact (hInstr _ rfl).elim

theorem not_mem_generated_of_labelsGe_next {program : Assembly.Program}
    {supply tag : Nat}
    (hLabels : labelsGe (LabelSupply.next supply) program) :
    Assembly.Label.generated supply tag ∉ Assembly.Program.labels program := by
  intro hMem
  exact
    Label.generatedScopeGe_next_self_false supply tag
      (hLabels (Assembly.Label.generated supply tag) hMem)

theorem not_mem_generated_of_labelsGe_gt {program : Assembly.Program}
    {lower supply tag : Nat}
    (hSupply : supply < lower)
    (hLabels : labelsGe lower program) :
    Assembly.Label.generated supply tag ∉ Assembly.Program.labels program := by
  intro hMem
  have hGe := hLabels (Assembly.Label.generated supply tag) hMem
  exact Nat.not_lt_of_ge hGe hSupply

theorem not_mem_generated_of_labelsLt {program : Assembly.Program}
    {supply tag : Nat}
    (hLabels : labelsLt supply program) :
    Assembly.Label.generated supply tag ∉ Assembly.Program.labels program := by
  intro hMem
  exact
    Label.generatedScopeLt_self_false supply tag
      (hLabels (Assembly.Label.generated supply tag) hMem)

end AssemblyProgram

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

theorem toAssembly_labelsGe (supply : LabelSupply) (code : Code) :
    AssemblyProgram.labelsGe supply code.toAssembly := by
  intro label hMem
  simp [toAssembly_labels] at hMem

theorem toAssembly_labelsLt (supply : LabelSupply) (code : Code) :
    AssemblyProgram.labelsLt supply code.toAssembly := by
  intro label hMem
  simp [toAssembly_labels] at hMem

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

namespace CompilerFacts

theorem block_compileFrom_next_ge :
    ∀ block supply, supply ≤ (Block.compileFrom supply block).next :=
  Block.rec
    (motive_1 := fun block =>
      ∀ supply, supply ≤ (Block.compileFrom supply block).next)
    (motive_2 := fun stmt =>
      ∀ supply, supply ≤ (Stmt.compileFrom supply stmt).next)
    (motive_3 := fun stmts =>
      ∀ supply, supply ≤ (Block.compileFrom supply { stmts := stmts }).next)
    (fun _stmts ih supply => ih supply)
    (fun _code supply => by
      simp [Stmt.compileFrom])
    (fun _cond thenBody elseBody ihThen ihElse supply => by
      simp [Stmt.compileFrom, LabelSupply.next]
      have hElse := ihElse (supply + 1)
      have hThen :=
        ihThen (Block.compileFrom (supply + 1) elseBody).next
      exact Nat.le_trans (Nat.le_trans (Nat.le_succ supply) hElse) hThen)
    (fun init _cond _post body ihInit ihPost ihBody supply => by
      simp [Stmt.compileFrom, LabelSupply.next]
      have hInit := ihInit (supply + 1)
      have hBody := ihBody (Block.compileFrom (supply + 1) init).next
      have hPost :=
        ihPost
          (Block.compileFrom
            (Block.compileFrom (supply + 1) init).next body).next
      exact
        Nat.le_trans
          (Nat.le_trans (Nat.le_trans (Nat.le_succ supply) hInit) hBody)
          hPost)
    (fun supply => by
      simp [Block.compileFrom])
    (fun head _tail ihHead ihTail supply => by
      simp [Block.compileFrom, CompileResult.append]
      exact
        Nat.le_trans (ihHead supply)
          (ihTail (Stmt.compileFrom supply head).next))

theorem stmt_compileFrom_next_ge :
    ∀ stmt supply, supply ≤ (Stmt.compileFrom supply stmt).next :=
  Stmt.rec
    (motive_1 := fun block =>
      ∀ supply, supply ≤ (Block.compileFrom supply block).next)
    (motive_2 := fun stmt =>
      ∀ supply, supply ≤ (Stmt.compileFrom supply stmt).next)
    (motive_3 := fun stmts =>
      ∀ supply, supply ≤ (Block.compileFrom supply { stmts := stmts }).next)
    (fun _stmts ih supply => ih supply)
    (fun _code supply => by
      simp [Stmt.compileFrom])
    (fun _cond thenBody elseBody ihThen ihElse supply => by
      simp [Stmt.compileFrom, LabelSupply.next]
      have hElse := ihElse (supply + 1)
      have hThen :=
        ihThen (Block.compileFrom (supply + 1) elseBody).next
      exact Nat.le_trans (Nat.le_trans (Nat.le_succ supply) hElse) hThen)
    (fun init _cond _post body ihInit ihPost ihBody supply => by
      simp [Stmt.compileFrom, LabelSupply.next]
      have hInit := ihInit (supply + 1)
      have hBody := ihBody (Block.compileFrom (supply + 1) init).next
      have hPost :=
        ihPost
          (Block.compileFrom
            (Block.compileFrom (supply + 1) init).next body).next
      exact
        Nat.le_trans
          (Nat.le_trans (Nat.le_trans (Nat.le_succ supply) hInit) hBody)
          hPost)
    (fun supply => by
      simp [Block.compileFrom])
    (fun head _tail ihHead ihTail supply => by
      simp [Block.compileFrom, CompileResult.append]
      exact
        Nat.le_trans (ihHead supply)
          (ihTail (Stmt.compileFrom supply head).next))

theorem block_compileFrom_labelsGe :
    ∀ block supply,
      AssemblyProgram.labelsGe supply (Block.compileFrom supply block).code :=
  Block.rec
    (motive_1 := fun block =>
      ∀ supply,
        AssemblyProgram.labelsGe supply (Block.compileFrom supply block).code)
    (motive_2 := fun stmt =>
      ∀ supply,
        AssemblyProgram.labelsGe supply (Stmt.compileFrom supply stmt).code)
    (motive_3 := fun stmts =>
      ∀ supply,
        AssemblyProgram.labelsGe supply
          (Block.compileFrom supply { stmts := stmts }).code)
    (fun _stmts ih supply => ih supply)
    (fun code supply => by
      simpa [Stmt.compileFrom] using Code.toAssembly_labelsGe supply code)
    (fun cond thenBody elseBody ihThen ihElse supply => by
      intro query hMem
      simp [Stmt.compileFrom, Assembly.Program.labels_append,
        Assembly.Program.labels, Code.toAssembly_labels] at hMem
      rcases hMem with hElseMem | hThenLabel | hThenMem | hEndLabel
      · exact
          AssemblyProgram.labelsGe_mono (Nat.le_succ supply)
            (ihElse (supply + 1)) query hElseMem
      · cases hThenLabel
        exact Label.generatedScopeGe_self supply 0
      · have hElseNext :
            supply ≤ (Block.compileFrom (supply + 1) elseBody).next :=
          Nat.le_trans (Nat.le_succ supply)
            (block_compileFrom_next_ge elseBody (supply + 1))
        exact
          AssemblyProgram.labelsGe_mono hElseNext
            (ihThen (Block.compileFrom (supply + 1) elseBody).next)
            query hThenMem
      · cases hEndLabel
        exact Label.generatedScopeGe_self supply 1)
    (fun init cond post body ihInit ihPost ihBody supply => by
      intro query hMem
      simp [Stmt.compileFrom, Assembly.Program.labels_append,
        Assembly.Program.labels, Code.toAssembly_labels] at hMem
      rcases hMem with
        hInitMem | hLoopLabel | hBodyLabel | hBodyMem | hPostMem | hEndLabel
      · exact
          AssemblyProgram.labelsGe_mono (Nat.le_succ supply)
            (ihInit (supply + 1)) query hInitMem
      · cases hLoopLabel
        exact Label.generatedScopeGe_self supply 0
      · cases hBodyLabel
        exact Label.generatedScopeGe_self supply 1
      · have hInitNext :
            supply ≤ (Block.compileFrom (supply + 1) init).next :=
          Nat.le_trans (Nat.le_succ supply)
            (block_compileFrom_next_ge init (supply + 1))
        exact
          AssemblyProgram.labelsGe_mono hInitNext
            (ihBody (Block.compileFrom (supply + 1) init).next)
            query hBodyMem
      · have hBodyNext :
            supply ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next := by
          have hInitNext :
              supply ≤ (Block.compileFrom (supply + 1) init).next :=
            Nat.le_trans (Nat.le_succ supply)
              (block_compileFrom_next_ge init (supply + 1))
          exact
            Nat.le_trans hInitNext
              (block_compileFrom_next_ge body
                (Block.compileFrom (supply + 1) init).next)
        exact
          AssemblyProgram.labelsGe_mono hBodyNext
            (ihPost
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next)
            query hPostMem
      · cases hEndLabel
        exact Label.generatedScopeGe_self supply 2)
    (fun supply => by
      simpa [Block.compileFrom] using AssemblyProgram.labelsGe_nil supply)
    (fun head _tail ihHead ihTail supply => by
      simp [Block.compileFrom, CompileResult.append]
      exact
        AssemblyProgram.labelsGe_append (ihHead supply)
          (AssemblyProgram.labelsGe_mono
            (stmt_compileFrom_next_ge head supply)
            (ihTail (Stmt.compileFrom supply head).next)))

theorem stmt_compileFrom_labelsGe :
    ∀ stmt supply,
      AssemblyProgram.labelsGe supply (Stmt.compileFrom supply stmt).code :=
  Stmt.rec
    (motive_1 := fun block =>
      ∀ supply,
        AssemblyProgram.labelsGe supply (Block.compileFrom supply block).code)
    (motive_2 := fun stmt =>
      ∀ supply,
        AssemblyProgram.labelsGe supply (Stmt.compileFrom supply stmt).code)
    (motive_3 := fun stmts =>
      ∀ supply,
        AssemblyProgram.labelsGe supply
          (Block.compileFrom supply { stmts := stmts }).code)
    (fun _stmts ih supply => ih supply)
    (fun code supply => by
      simpa [Stmt.compileFrom] using Code.toAssembly_labelsGe supply code)
    (fun cond thenBody elseBody ihThen ihElse supply => by
      intro query hMem
      simp [Stmt.compileFrom, Assembly.Program.labels_append,
        Assembly.Program.labels, Code.toAssembly_labels] at hMem
      rcases hMem with hElseMem | hThenLabel | hThenMem | hEndLabel
      · exact
          AssemblyProgram.labelsGe_mono (Nat.le_succ supply)
            (ihElse (supply + 1)) query hElseMem
      · cases hThenLabel
        exact Label.generatedScopeGe_self supply 0
      · have hElseNext :
            supply ≤ (Block.compileFrom (supply + 1) elseBody).next :=
          Nat.le_trans (Nat.le_succ supply)
            (block_compileFrom_next_ge elseBody (supply + 1))
        exact
          AssemblyProgram.labelsGe_mono hElseNext
            (ihThen (Block.compileFrom (supply + 1) elseBody).next)
            query hThenMem
      · cases hEndLabel
        exact Label.generatedScopeGe_self supply 1)
    (fun init cond post body ihInit ihPost ihBody supply => by
      intro query hMem
      simp [Stmt.compileFrom, Assembly.Program.labels_append,
        Assembly.Program.labels, Code.toAssembly_labels] at hMem
      rcases hMem with
        hInitMem | hLoopLabel | hBodyLabel | hBodyMem | hPostMem | hEndLabel
      · exact
          AssemblyProgram.labelsGe_mono (Nat.le_succ supply)
            (ihInit (supply + 1)) query hInitMem
      · cases hLoopLabel
        exact Label.generatedScopeGe_self supply 0
      · cases hBodyLabel
        exact Label.generatedScopeGe_self supply 1
      · have hInitNext :
            supply ≤ (Block.compileFrom (supply + 1) init).next :=
          Nat.le_trans (Nat.le_succ supply)
            (block_compileFrom_next_ge init (supply + 1))
        exact
          AssemblyProgram.labelsGe_mono hInitNext
            (ihBody (Block.compileFrom (supply + 1) init).next)
            query hBodyMem
      · have hBodyNext :
            supply ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next := by
          have hInitNext :
              supply ≤ (Block.compileFrom (supply + 1) init).next :=
            Nat.le_trans (Nat.le_succ supply)
              (block_compileFrom_next_ge init (supply + 1))
          exact
            Nat.le_trans hInitNext
              (block_compileFrom_next_ge body
                (Block.compileFrom (supply + 1) init).next)
        exact
          AssemblyProgram.labelsGe_mono hBodyNext
            (ihPost
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next)
            query hPostMem
      · cases hEndLabel
        exact Label.generatedScopeGe_self supply 2)
    (fun supply => by
      simpa [Block.compileFrom] using AssemblyProgram.labelsGe_nil supply)
    (fun head _tail ihHead ihTail supply => by
      simp [Block.compileFrom, CompileResult.append]
      exact
        AssemblyProgram.labelsGe_append (ihHead supply)
          (AssemblyProgram.labelsGe_mono
            (stmt_compileFrom_next_ge head supply)
            (ihTail (Stmt.compileFrom supply head).next)))

theorem block_compileFrom_labelsLt :
    ∀ block supply,
      AssemblyProgram.labelsLt (Block.compileFrom supply block).next
        (Block.compileFrom supply block).code :=
  Block.rec
    (motive_1 := fun block =>
      ∀ supply,
        AssemblyProgram.labelsLt (Block.compileFrom supply block).next
          (Block.compileFrom supply block).code)
    (motive_2 := fun stmt =>
      ∀ supply,
        AssemblyProgram.labelsLt (Stmt.compileFrom supply stmt).next
          (Stmt.compileFrom supply stmt).code)
    (motive_3 := fun stmts =>
      ∀ supply,
        AssemblyProgram.labelsLt (Block.compileFrom supply { stmts := stmts }).next
          (Block.compileFrom supply { stmts := stmts }).code)
    (fun _stmts ih supply => ih supply)
    (fun code supply => by
      simpa [Stmt.compileFrom] using Code.toAssembly_labelsLt supply code)
    (fun cond thenBody elseBody ihThen ihElse supply => by
      intro query hMem
      simp [Stmt.compileFrom, Assembly.Program.labels_append,
        Assembly.Program.labels, Code.toAssembly_labels] at hMem
      rcases hMem with hElseMem | hThenLabel | hThenMem | hEndLabel
      · simp [Stmt.compileFrom]
        exact
          AssemblyProgram.labelsLt_mono
            (block_compileFrom_next_ge thenBody
              (Block.compileFrom (supply + 1) elseBody).next)
            (ihElse (supply + 1)) query hElseMem
      · cases hThenLabel
        simp [Stmt.compileFrom, Label.generatedScopeLt, LabelSupply.label]
        have hElse :
            supply + 1 ≤ (Block.compileFrom (supply + 1) elseBody).next :=
          block_compileFrom_next_ge elseBody (supply + 1)
        have hThen :
            (Block.compileFrom (supply + 1) elseBody).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) elseBody).next thenBody).next :=
          block_compileFrom_next_ge thenBody
            (Block.compileFrom (supply + 1) elseBody).next
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
          (Nat.le_trans hElse hThen)
      · simp [Stmt.compileFrom]
        exact ihThen (Block.compileFrom (supply + 1) elseBody).next
          query hThenMem
      · cases hEndLabel
        simp [Stmt.compileFrom, Label.generatedScopeLt, LabelSupply.label]
        have hElse :
            supply + 1 ≤ (Block.compileFrom (supply + 1) elseBody).next :=
          block_compileFrom_next_ge elseBody (supply + 1)
        have hThen :
            (Block.compileFrom (supply + 1) elseBody).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) elseBody).next thenBody).next :=
          block_compileFrom_next_ge thenBody
            (Block.compileFrom (supply + 1) elseBody).next
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
          (Nat.le_trans hElse hThen))
    (fun init cond post body ihInit ihPost ihBody supply => by
      intro query hMem
      simp [Stmt.compileFrom, Assembly.Program.labels_append,
        Assembly.Program.labels, Code.toAssembly_labels] at hMem
      rcases hMem with
        hInitMem | hLoopLabel | hBodyLabel | hBodyMem | hPostMem | hEndLabel
      · simp [Stmt.compileFrom]
        have hInitBody :
            (Block.compileFrom (supply + 1) init).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next :=
          block_compileFrom_next_ge body
            (Block.compileFrom (supply + 1) init).next
        have hBodyPost :
            (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next ≤
              (Block.compileFrom
                (Block.compileFrom
                  (Block.compileFrom (supply + 1) init).next body).next post).next :=
          block_compileFrom_next_ge post
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
        exact
          AssemblyProgram.labelsLt_mono (Nat.le_trans hInitBody hBodyPost)
            (ihInit (supply + 1)) query hInitMem
      · cases hLoopLabel
        simp [Stmt.compileFrom, Label.generatedScopeLt, LabelSupply.label]
        have hInit :
            supply + 1 ≤ (Block.compileFrom (supply + 1) init).next :=
          block_compileFrom_next_ge init (supply + 1)
        have hBody :
            (Block.compileFrom (supply + 1) init).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next :=
          block_compileFrom_next_ge body
            (Block.compileFrom (supply + 1) init).next
        have hPost :
            (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next ≤
              (Block.compileFrom
                (Block.compileFrom
                  (Block.compileFrom (supply + 1) init).next body).next post).next :=
          block_compileFrom_next_ge post
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
          (Nat.le_trans hInit (Nat.le_trans hBody hPost))
      · cases hBodyLabel
        simp [Stmt.compileFrom, Label.generatedScopeLt, LabelSupply.label]
        have hInit :
            supply + 1 ≤ (Block.compileFrom (supply + 1) init).next :=
          block_compileFrom_next_ge init (supply + 1)
        have hBody :
            (Block.compileFrom (supply + 1) init).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next :=
          block_compileFrom_next_ge body
            (Block.compileFrom (supply + 1) init).next
        have hPost :
            (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next ≤
              (Block.compileFrom
                (Block.compileFrom
                  (Block.compileFrom (supply + 1) init).next body).next post).next :=
          block_compileFrom_next_ge post
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
          (Nat.le_trans hInit (Nat.le_trans hBody hPost))
      · simp [Stmt.compileFrom]
        have hBodyPost :
            (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next ≤
              (Block.compileFrom
                (Block.compileFrom
                  (Block.compileFrom (supply + 1) init).next body).next post).next :=
          block_compileFrom_next_ge post
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
        exact
          AssemblyProgram.labelsLt_mono hBodyPost
            (ihBody (Block.compileFrom (supply + 1) init).next)
            query hBodyMem
      · simp [Stmt.compileFrom]
        exact
          ihPost
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
            query hPostMem
      · cases hEndLabel
        simp [Stmt.compileFrom, Label.generatedScopeLt, LabelSupply.label]
        have hInit :
            supply + 1 ≤ (Block.compileFrom (supply + 1) init).next :=
          block_compileFrom_next_ge init (supply + 1)
        have hBody :
            (Block.compileFrom (supply + 1) init).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next :=
          block_compileFrom_next_ge body
            (Block.compileFrom (supply + 1) init).next
        have hPost :
            (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next ≤
              (Block.compileFrom
                (Block.compileFrom
                  (Block.compileFrom (supply + 1) init).next body).next post).next :=
          block_compileFrom_next_ge post
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
          (Nat.le_trans hInit (Nat.le_trans hBody hPost)))
    (fun supply => by
      simpa [Block.compileFrom] using AssemblyProgram.labelsLt_nil supply)
    (fun head _tail ihHead ihTail supply => by
      simp [Block.compileFrom, CompileResult.append]
      exact
        AssemblyProgram.labelsLt_append
          (AssemblyProgram.labelsLt_mono
            (block_compileFrom_next_ge { stmts := _tail }
              (Stmt.compileFrom supply head).next)
            (ihHead supply))
          (ihTail (Stmt.compileFrom supply head).next))

theorem stmt_compileFrom_labelsLt :
    ∀ stmt supply,
      AssemblyProgram.labelsLt (Stmt.compileFrom supply stmt).next
        (Stmt.compileFrom supply stmt).code :=
  Stmt.rec
    (motive_1 := fun block =>
      ∀ supply,
        AssemblyProgram.labelsLt (Block.compileFrom supply block).next
          (Block.compileFrom supply block).code)
    (motive_2 := fun stmt =>
      ∀ supply,
        AssemblyProgram.labelsLt (Stmt.compileFrom supply stmt).next
          (Stmt.compileFrom supply stmt).code)
    (motive_3 := fun stmts =>
      ∀ supply,
        AssemblyProgram.labelsLt (Block.compileFrom supply { stmts := stmts }).next
          (Block.compileFrom supply { stmts := stmts }).code)
    (fun _stmts ih supply => ih supply)
    (fun code supply => by
      simpa [Stmt.compileFrom] using Code.toAssembly_labelsLt supply code)
    (fun cond thenBody elseBody ihThen ihElse supply => by
      intro query hMem
      simp [Stmt.compileFrom, Assembly.Program.labels_append,
        Assembly.Program.labels, Code.toAssembly_labels] at hMem
      rcases hMem with hElseMem | hThenLabel | hThenMem | hEndLabel
      · simp [Stmt.compileFrom]
        exact
          AssemblyProgram.labelsLt_mono
            (block_compileFrom_next_ge thenBody
              (Block.compileFrom (supply + 1) elseBody).next)
            (ihElse (supply + 1)) query hElseMem
      · cases hThenLabel
        simp [Stmt.compileFrom, Label.generatedScopeLt, LabelSupply.label]
        have hElse :
            supply + 1 ≤ (Block.compileFrom (supply + 1) elseBody).next :=
          block_compileFrom_next_ge elseBody (supply + 1)
        have hThen :
            (Block.compileFrom (supply + 1) elseBody).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) elseBody).next thenBody).next :=
          block_compileFrom_next_ge thenBody
            (Block.compileFrom (supply + 1) elseBody).next
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
          (Nat.le_trans hElse hThen)
      · simp [Stmt.compileFrom]
        exact ihThen (Block.compileFrom (supply + 1) elseBody).next
          query hThenMem
      · cases hEndLabel
        simp [Stmt.compileFrom, Label.generatedScopeLt, LabelSupply.label]
        have hElse :
            supply + 1 ≤ (Block.compileFrom (supply + 1) elseBody).next :=
          block_compileFrom_next_ge elseBody (supply + 1)
        have hThen :
            (Block.compileFrom (supply + 1) elseBody).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) elseBody).next thenBody).next :=
          block_compileFrom_next_ge thenBody
            (Block.compileFrom (supply + 1) elseBody).next
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
          (Nat.le_trans hElse hThen))
    (fun init cond post body ihInit ihPost ihBody supply => by
      intro query hMem
      simp [Stmt.compileFrom, Assembly.Program.labels_append,
        Assembly.Program.labels, Code.toAssembly_labels] at hMem
      rcases hMem with
        hInitMem | hLoopLabel | hBodyLabel | hBodyMem | hPostMem | hEndLabel
      · simp [Stmt.compileFrom]
        have hInitBody :
            (Block.compileFrom (supply + 1) init).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next :=
          block_compileFrom_next_ge body
            (Block.compileFrom (supply + 1) init).next
        have hBodyPost :
            (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next ≤
              (Block.compileFrom
                (Block.compileFrom
                  (Block.compileFrom (supply + 1) init).next body).next post).next :=
          block_compileFrom_next_ge post
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
        exact
          AssemblyProgram.labelsLt_mono (Nat.le_trans hInitBody hBodyPost)
            (ihInit (supply + 1)) query hInitMem
      · cases hLoopLabel
        simp [Stmt.compileFrom, Label.generatedScopeLt, LabelSupply.label]
        have hInit :
            supply + 1 ≤ (Block.compileFrom (supply + 1) init).next :=
          block_compileFrom_next_ge init (supply + 1)
        have hBody :
            (Block.compileFrom (supply + 1) init).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next :=
          block_compileFrom_next_ge body
            (Block.compileFrom (supply + 1) init).next
        have hPost :
            (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next ≤
              (Block.compileFrom
                (Block.compileFrom
                  (Block.compileFrom (supply + 1) init).next body).next post).next :=
          block_compileFrom_next_ge post
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
          (Nat.le_trans hInit (Nat.le_trans hBody hPost))
      · cases hBodyLabel
        simp [Stmt.compileFrom, Label.generatedScopeLt, LabelSupply.label]
        have hInit :
            supply + 1 ≤ (Block.compileFrom (supply + 1) init).next :=
          block_compileFrom_next_ge init (supply + 1)
        have hBody :
            (Block.compileFrom (supply + 1) init).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next :=
          block_compileFrom_next_ge body
            (Block.compileFrom (supply + 1) init).next
        have hPost :
            (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next ≤
              (Block.compileFrom
                (Block.compileFrom
                  (Block.compileFrom (supply + 1) init).next body).next post).next :=
          block_compileFrom_next_ge post
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
          (Nat.le_trans hInit (Nat.le_trans hBody hPost))
      · simp [Stmt.compileFrom]
        have hBodyPost :
            (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next ≤
              (Block.compileFrom
                (Block.compileFrom
                  (Block.compileFrom (supply + 1) init).next body).next post).next :=
          block_compileFrom_next_ge post
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
        exact
          AssemblyProgram.labelsLt_mono hBodyPost
            (ihBody (Block.compileFrom (supply + 1) init).next)
            query hBodyMem
      · simp [Stmt.compileFrom]
        exact
          ihPost
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
            query hPostMem
      · cases hEndLabel
        simp [Stmt.compileFrom, Label.generatedScopeLt, LabelSupply.label]
        have hInit :
            supply + 1 ≤ (Block.compileFrom (supply + 1) init).next :=
          block_compileFrom_next_ge init (supply + 1)
        have hBody :
            (Block.compileFrom (supply + 1) init).next ≤
              (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next :=
          block_compileFrom_next_ge body
            (Block.compileFrom (supply + 1) init).next
        have hPost :
            (Block.compileFrom
                (Block.compileFrom (supply + 1) init).next body).next ≤
              (Block.compileFrom
                (Block.compileFrom
                  (Block.compileFrom (supply + 1) init).next body).next post).next :=
          block_compileFrom_next_ge post
            (Block.compileFrom
              (Block.compileFrom (supply + 1) init).next body).next
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
          (Nat.le_trans hInit (Nat.le_trans hBody hPost)))
    (fun supply => by
      simpa [Block.compileFrom] using AssemblyProgram.labelsLt_nil supply)
    (fun head _tail ihHead ihTail supply => by
      simp [Block.compileFrom, CompileResult.append]
      exact
        AssemblyProgram.labelsLt_append
          (AssemblyProgram.labelsLt_mono
            (block_compileFrom_next_ge { stmts := _tail }
              (Stmt.compileFrom supply head).next)
            (ihHead supply))
          (ihTail (Stmt.compileFrom supply head).next))

theorem ifElse_then_labelPc {pre post : Assembly.Program}
    {supply : LabelSupply} {cond : Code} {thenBody elseBody : Block}
    (hPreLt : AssemblyProgram.labelsLt supply pre) :
    Assembly.Program.labelPc
      (pre ++ (Stmt.compileFrom supply
        (Stmt.ifElse cond thenBody elseBody)).code ++ post)
      (LabelSupply.label supply 0) =
        some (Assembly.Program.byteLength
          (pre ++ cond.toAssembly ++
            [Assembly.Instr.jumpi (LabelSupply.label supply 0)] ++
            (Block.compileFrom (LabelSupply.next supply) elseBody).code ++
            [Assembly.Instr.jump (LabelSupply.label supply 1)])) := by
  let thenLabel := LabelSupply.label supply 0
  let endLabel := LabelSupply.label supply 1
  let compiledElse := Block.compileFrom (LabelSupply.next supply) elseBody
  let compiledThen := Block.compileFrom compiledElse.next thenBody
  have hNotMem :
      thenLabel ∉ Assembly.Program.labels
        (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel] ++
          compiledElse.code ++ [Assembly.Instr.jump endLabel]) := by
    intro hMem
    have hElseNot :
        thenLabel ∉ Assembly.Program.labels compiledElse.code := by
      unfold thenLabel compiledElse
      exact
        AssemblyProgram.not_mem_generated_of_labelsGe_next
          (block_compileFrom_labelsGe elseBody (LabelSupply.next supply))
    have hPreNot : thenLabel ∉ Assembly.Program.labels pre := by
      unfold thenLabel
      exact AssemblyProgram.not_mem_generated_of_labelsLt hPreLt
    simp [Assembly.Program.labels_append, Assembly.Program.labels,
      Code.toAssembly_labels, hPreNot, hElseNot] at hMem
  have hEq :=
    Assembly.Program.labelPc_append_label_eq
      (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel] ++
        compiledElse.code ++ [Assembly.Instr.jump endLabel])
      (compiledThen.code ++ [Assembly.Instr.label endLabel] ++ post)
      (target := thenLabel) hNotMem
  simpa [Stmt.compileFrom, thenLabel, endLabel, compiledElse, compiledThen,
    LabelSupply.next, List.append_assoc] using hEq

theorem ifElse_end_labelPc {pre post : Assembly.Program}
    {supply : LabelSupply} {cond : Code} {thenBody elseBody : Block}
    (hPreLt : AssemblyProgram.labelsLt supply pre) :
    Assembly.Program.labelPc
      (pre ++ (Stmt.compileFrom supply
        (Stmt.ifElse cond thenBody elseBody)).code ++ post)
      (LabelSupply.label supply 1) =
        some (Assembly.Program.byteLength
          (pre ++ cond.toAssembly ++
            [Assembly.Instr.jumpi (LabelSupply.label supply 0)] ++
            (Block.compileFrom (LabelSupply.next supply) elseBody).code ++
            [ Assembly.Instr.jump (LabelSupply.label supply 1)
            , Assembly.Instr.label (LabelSupply.label supply 0)
            ] ++
            (Block.compileFrom
              (Block.compileFrom (LabelSupply.next supply) elseBody).next
              thenBody).code)) := by
  let thenLabel := LabelSupply.label supply 0
  let endLabel := LabelSupply.label supply 1
  let compiledElse := Block.compileFrom (LabelSupply.next supply) elseBody
  let compiledThen := Block.compileFrom compiledElse.next thenBody
  have hSupplyLtElse : supply < compiledElse.next := by
    unfold compiledElse
    exact
      Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
        (block_compileFrom_next_ge elseBody (LabelSupply.next supply))
  have hNotMem :
      endLabel ∉ Assembly.Program.labels
        (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel] ++
          compiledElse.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
          compiledThen.code) := by
    intro hMem
    have hPreNot :
        Assembly.Label.generated supply 1 ∉ Assembly.Program.labels pre := by
      exact AssemblyProgram.not_mem_generated_of_labelsLt hPreLt
    have hElseNot :
        Assembly.Label.generated supply 1 ∉
          Assembly.Program.labels compiledElse.code := by
      unfold compiledElse
      exact
        AssemblyProgram.not_mem_generated_of_labelsGe_gt
          (lower := LabelSupply.next supply) (supply := supply) (tag := 1)
          (Nat.lt_succ_self supply)
          (block_compileFrom_labelsGe elseBody (LabelSupply.next supply))
    have hThenNot :
        Assembly.Label.generated supply 1 ∉
          Assembly.Program.labels compiledThen.code := by
      unfold compiledThen
      exact
        AssemblyProgram.not_mem_generated_of_labelsGe_gt
          (lower := compiledElse.next) (supply := supply) (tag := 1)
          hSupplyLtElse
          (block_compileFrom_labelsGe thenBody compiledElse.next)
    unfold thenLabel endLabel at hMem
    simp [Assembly.Program.labels_append, Assembly.Program.labels,
      Code.toAssembly_labels, LabelSupply.label] at hMem
    rcases hMem with hPre | hElse | hThen
    · exact hPreNot hPre
    · exact hElseNot hElse
    · exact hThenNot hThen
  have hEq :=
    Assembly.Program.labelPc_append_label_eq
      (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel] ++
        compiledElse.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
        compiledThen.code)
      post (target := endLabel) hNotMem
  simpa [Stmt.compileFrom, thenLabel, endLabel, compiledElse, compiledThen,
    LabelSupply.next, List.append_assoc] using hEq

theorem for_loop_labelPc {pre suffix : Assembly.Program}
    {supply : LabelSupply} {init post body : Block} {cond : Code}
    (hPreLt : AssemblyProgram.labelsLt supply pre) :
    Assembly.Program.labelPc
      (pre ++ (Stmt.compileFrom supply
        (Stmt.for_ init cond post body)).code ++ suffix)
      (LabelSupply.label supply 0) =
        some (Assembly.Program.byteLength
          (pre ++
            (Block.compileFrom (LabelSupply.next supply) init).code)) := by
  let loopLabel := LabelSupply.label supply 0
  let bodyLabel := LabelSupply.label supply 1
  let endLabel := LabelSupply.label supply 2
  let compiledInit := Block.compileFrom (LabelSupply.next supply) init
  let compiledBody := Block.compileFrom compiledInit.next body
  let compiledPost := Block.compileFrom compiledBody.next post
  have hNotMem :
      loopLabel ∉ Assembly.Program.labels (pre ++ compiledInit.code) := by
    intro hMem
    have hPreNot : loopLabel ∉ Assembly.Program.labels pre := by
      unfold loopLabel
      exact AssemblyProgram.not_mem_generated_of_labelsLt hPreLt
    have hInitNot : loopLabel ∉ Assembly.Program.labels compiledInit.code := by
      unfold loopLabel compiledInit
      exact
        AssemblyProgram.not_mem_generated_of_labelsGe_next
          (block_compileFrom_labelsGe init (LabelSupply.next supply))
    simp [Assembly.Program.labels_append, hPreNot, hInitNot] at hMem
  have hEq :=
    Assembly.Program.labelPc_append_label_eq
      (pre ++ compiledInit.code)
      (cond.toAssembly ++
        [ Assembly.Instr.jumpi bodyLabel
        , Assembly.Instr.jump endLabel
        , Assembly.Instr.label bodyLabel
        ] ++
        compiledBody.code ++ compiledPost.code ++
        [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
        suffix)
      (target := loopLabel) hNotMem
  simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel, compiledInit,
    compiledBody, compiledPost, LabelSupply.next, List.append_assoc] using hEq

theorem for_body_labelPc {pre suffix : Assembly.Program}
    {supply : LabelSupply} {init post body : Block} {cond : Code}
    (hPreLt : AssemblyProgram.labelsLt supply pre) :
    Assembly.Program.labelPc
      (pre ++ (Stmt.compileFrom supply
        (Stmt.for_ init cond post body)).code ++ suffix)
      (LabelSupply.label supply 1) =
        some (Assembly.Program.byteLength
          (pre ++
            (Block.compileFrom (LabelSupply.next supply) init).code ++
            [Assembly.Instr.label (LabelSupply.label supply 0)] ++
            cond.toAssembly ++
            [ Assembly.Instr.jumpi (LabelSupply.label supply 1)
            , Assembly.Instr.jump (LabelSupply.label supply 2)
            ])) := by
  let loopLabel := LabelSupply.label supply 0
  let bodyLabel := LabelSupply.label supply 1
  let endLabel := LabelSupply.label supply 2
  let compiledInit := Block.compileFrom (LabelSupply.next supply) init
  let compiledBody := Block.compileFrom compiledInit.next body
  let compiledPost := Block.compileFrom compiledBody.next post
  have hNotMem :
      bodyLabel ∉ Assembly.Program.labels
        (pre ++ compiledInit.code ++ [Assembly.Instr.label loopLabel] ++
          cond.toAssembly ++
          [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel]) := by
    intro hMem
    have hPreNot :
        Assembly.Label.generated supply 1 ∉ Assembly.Program.labels pre := by
      exact AssemblyProgram.not_mem_generated_of_labelsLt hPreLt
    have hInitNot :
        Assembly.Label.generated supply 1 ∉
          Assembly.Program.labels compiledInit.code := by
      unfold compiledInit
      exact
        AssemblyProgram.not_mem_generated_of_labelsGe_next
          (block_compileFrom_labelsGe init (LabelSupply.next supply))
    unfold loopLabel bodyLabel endLabel at hMem
    simp [Assembly.Program.labels_append, Assembly.Program.labels,
      Code.toAssembly_labels, LabelSupply.label] at hMem
    rcases hMem with hPre | hInit
    · exact hPreNot hPre
    · exact hInitNot hInit
  have hEq :=
    Assembly.Program.labelPc_append_label_eq
      (pre ++ compiledInit.code ++ [Assembly.Instr.label loopLabel] ++
        cond.toAssembly ++
        [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel])
      (compiledBody.code ++ compiledPost.code ++
        [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
        suffix)
      (target := bodyLabel) hNotMem
  simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel, compiledInit,
    compiledBody, compiledPost, LabelSupply.next, List.append_assoc] using hEq

theorem for_end_labelPc {pre suffix : Assembly.Program}
    {supply : LabelSupply} {init post body : Block} {cond : Code}
    (hPreLt : AssemblyProgram.labelsLt supply pre) :
    Assembly.Program.labelPc
      (pre ++ (Stmt.compileFrom supply
        (Stmt.for_ init cond post body)).code ++ suffix)
      (LabelSupply.label supply 2) =
        some (Assembly.Program.byteLength
          (pre ++
            (Block.compileFrom (LabelSupply.next supply) init).code ++
            [Assembly.Instr.label (LabelSupply.label supply 0)] ++
            cond.toAssembly ++
            [ Assembly.Instr.jumpi (LabelSupply.label supply 1)
            , Assembly.Instr.jump (LabelSupply.label supply 2)
            , Assembly.Instr.label (LabelSupply.label supply 1)
            ] ++
            (Block.compileFrom
              (Block.compileFrom (LabelSupply.next supply) init).next
              body).code ++
            (Block.compileFrom
              (Block.compileFrom
                (Block.compileFrom (LabelSupply.next supply) init).next
                body).next
              post).code ++
            [Assembly.Instr.jump (LabelSupply.label supply 0)])) := by
  let loopLabel := LabelSupply.label supply 0
  let bodyLabel := LabelSupply.label supply 1
  let endLabel := LabelSupply.label supply 2
  let compiledInit := Block.compileFrom (LabelSupply.next supply) init
  let compiledBody := Block.compileFrom compiledInit.next body
  let compiledPost := Block.compileFrom compiledBody.next post
  have hSupplyLtInit : supply < compiledInit.next := by
    unfold compiledInit
    exact
      Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
        (block_compileFrom_next_ge init (LabelSupply.next supply))
  have hSupplyLtBody : supply < compiledBody.next := by
    exact
      Nat.lt_of_lt_of_le hSupplyLtInit
        (block_compileFrom_next_ge body compiledInit.next)
  have hNotMem :
      endLabel ∉ Assembly.Program.labels
        (pre ++ compiledInit.code ++ [Assembly.Instr.label loopLabel] ++
          cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ compiledPost.code ++
          [Assembly.Instr.jump loopLabel]) := by
    intro hMem
    have hPreNot :
        Assembly.Label.generated supply 2 ∉ Assembly.Program.labels pre := by
      exact AssemblyProgram.not_mem_generated_of_labelsLt hPreLt
    have hInitNot :
        Assembly.Label.generated supply 2 ∉
          Assembly.Program.labels compiledInit.code := by
      unfold compiledInit
      exact
        AssemblyProgram.not_mem_generated_of_labelsGe_next
          (block_compileFrom_labelsGe init (LabelSupply.next supply))
    have hBodyNot :
        Assembly.Label.generated supply 2 ∉
          Assembly.Program.labels compiledBody.code := by
      unfold compiledBody
      exact
        AssemblyProgram.not_mem_generated_of_labelsGe_gt
          (lower := compiledInit.next) (supply := supply) (tag := 2)
          hSupplyLtInit
          (block_compileFrom_labelsGe body compiledInit.next)
    have hPostNot :
        Assembly.Label.generated supply 2 ∉
          Assembly.Program.labels compiledPost.code := by
      unfold compiledPost
      exact
        AssemblyProgram.not_mem_generated_of_labelsGe_gt
          (lower := compiledBody.next) (supply := supply) (tag := 2)
          hSupplyLtBody
          (block_compileFrom_labelsGe post compiledBody.next)
    unfold loopLabel bodyLabel endLabel at hMem
    simp [Assembly.Program.labels_append, Assembly.Program.labels,
      Code.toAssembly_labels, LabelSupply.label] at hMem
    rcases hMem with hPre | hInit | hBody | hPost
    · exact hPreNot hPre
    · exact hInitNot hInit
    · exact hBodyNot hBody
    · exact hPostNot hPost
  have hEq :=
    Assembly.Program.labelPc_append_label_eq
      (pre ++ compiledInit.code ++ [Assembly.Instr.label loopLabel] ++
        cond.toAssembly ++
        [ Assembly.Instr.jumpi bodyLabel
        , Assembly.Instr.jump endLabel
        , Assembly.Instr.label bodyLabel
        ] ++
        compiledBody.code ++ compiledPost.code ++
        [Assembly.Instr.jump loopLabel])
      suffix (target := endLabel) hNotMem
  simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel, compiledInit,
    compiledBody, compiledPost, LabelSupply.next, List.append_assoc] using hEq

end CompilerFacts

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
