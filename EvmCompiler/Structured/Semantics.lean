import EvmCompiler.Structured.Syntax

namespace EvmCompiler
namespace Structured

def invalid {α : Type} : Except EVMException α :=
  .error .InvalidInstruction

namespace BasicOp

def step (op : BasicOp) (state : EVMState) : Except EVMException EVMState :=
  Assembly.Target.stepInstr (Assembly.TargetInstr.prim op.toPrimOp) state

end BasicOp

namespace BasicInstr

def step : BasicInstr → EVMState → Except EVMException EVMState
  | .push value, state =>
      Assembly.Target.stepInstr (Assembly.TargetInstr.push32 value) state
  | .op basicOp, state =>
      basicOp.step state

end BasicInstr

namespace Code

def run : Code → EVMState → Except EVMException EVMState
  | [], state => .ok state
  | instr :: rest, state => do
      let state' ← instr.step state
      run rest state'

def popCondition (state : EVMState) :
    Except EVMException (EVMState × Bool) :=
  match state.stack.pop with
  | some (stack, cond) =>
      .ok ({ state with stack := stack }, cond != EvmYul.UInt256.ofNat 0)
  | none =>
      .error .StackUnderflow

def runCondition (code : Code) (state : EVMState) :
    Except EVMException (EVMState × Bool) := do
  let state' ← run code state
  popCondition state'

end Code

mutual
  /--
  Fuel-indexed structured block execution.

  Fuel is only a totality device for recursive structured control.  A successful
  run is the semantic fact used by preservation; running out of this source fuel
  is reported as `InvalidInstruction`, not as EVM gas.
  -/
  def Block.run : Nat → Block → EVMState → Except EVMException EVMState
    | 0, _block, _state =>
        invalid
    | _fuel + 1, ⟨[]⟩, state =>
        .ok state
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let state' ← Stmt.run fuel stmt state
        Block.run fuel ⟨rest⟩ state'

  def Stmt.runForLoop (fuel : Nat) (cond : Code) (post body : Block)
      (state : EVMState) : Except EVMException EVMState :=
    match fuel with
    | 0 =>
        invalid
    | fuel' + 1 => do
        let (stateAfterCond, condTrue) ← Code.runCondition cond state
        if condTrue then
          let stateAfterBody ← Block.run fuel' body stateAfterCond
          let stateAfterPost ← Block.run fuel' post stateAfterBody
          Stmt.runForLoop fuel' cond post body stateAfterPost
        else
          .ok stateAfterCond

  def Stmt.run : Nat → Stmt → EVMState → Except EVMException EVMState
    | _fuel, Stmt.code code, state =>
        Code.run code state
    | 0, Stmt.ifElse _cond _thenBody _elseBody, _state =>
        invalid
    | fuel + 1, Stmt.ifElse cond thenBody elseBody, state => do
        let (stateAfterCond, condTrue) ← Code.runCondition cond state
        if condTrue then
          Block.run fuel thenBody stateAfterCond
        else
          Block.run fuel elseBody stateAfterCond
    | 0, Stmt.for_ _init _cond _post _body, _state =>
        invalid
    | fuel + 1, Stmt.for_ init cond post body, state => do
        let stateAfterInit ← Block.run fuel init state
        Stmt.runForLoop fuel cond post body stateAfterInit
end

namespace Program

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException EVMState :=
  Block.run fuel program.body state

end Program

mutual
  /--
  Relational semantics for blocks, shaped to match the executable
  fuel-indexed evaluator but easier to induct over in compiler proofs.

  The `fuel + 1` in the block constructors mirrors `Block.run`: a zero-fuel
  block execution is invalid even for an empty block.
  -/
  inductive Block.Eval : Nat → Block → EVMState → EVMState → Prop where
    | nil {fuel : Nat} {state : EVMState} :
        Block.Eval (fuel + 1) ⟨[]⟩ state state
    | cons {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state mid final : EVMState}
        (hStmt : Stmt.Eval fuel stmt state mid)
        (hRest : Block.Eval fuel ⟨rest⟩ mid final) :
        Block.Eval (fuel + 1) ⟨stmt :: rest⟩ state final

  inductive Stmt.Eval : Nat → Stmt → EVMState → EVMState → Prop where
    | code {fuel : Nat} {code : Code} {state final : EVMState}
        (hCode : Code.run code state = .ok final) :
        Stmt.Eval fuel (.code code) state final
    | ifTrue {fuel : Nat} {cond : Code} {thenBody elseBody : Block}
        {state stateAfterCond final : EVMState}
        (hCond : Code.runCondition cond state = .ok (stateAfterCond, true))
        (hThen : Block.Eval fuel thenBody stateAfterCond final) :
        Stmt.Eval (fuel + 1) (.ifElse cond thenBody elseBody) state final
    | ifFalse {fuel : Nat} {cond : Code} {thenBody elseBody : Block}
        {state stateAfterCond final : EVMState}
        (hCond : Code.runCondition cond state = .ok (stateAfterCond, false))
        (hElse : Block.Eval fuel elseBody stateAfterCond final) :
        Stmt.Eval (fuel + 1) (.ifElse cond thenBody elseBody) state final
    | for_ {fuel : Nat} {init post body : Block} {cond : Code}
        {state stateAfterInit final : EVMState}
        (hInit : Block.Eval fuel init state stateAfterInit)
        (hLoop : For.Eval fuel cond post body stateAfterInit final) :
        Stmt.Eval (fuel + 1) (.for_ init cond post body) state final

  inductive For.Eval :
      Nat → Code → Block → Block → EVMState → EVMState → Prop where
    | false {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond : EVMState}
        (hCond : Code.runCondition cond state = .ok (stateAfterCond, false)) :
        For.Eval (fuel + 1) cond post body state stateAfterCond
    | true {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond stateAfterBody stateAfterPost final : EVMState}
        (hCond : Code.runCondition cond state = .ok (stateAfterCond, true))
        (hBody : Block.Eval fuel body stateAfterCond stateAfterBody)
        (hPost : Block.Eval fuel post stateAfterBody stateAfterPost)
        (hLoop : For.Eval fuel cond post body stateAfterPost final) :
        For.Eval (fuel + 1) cond post body state final
end

mutual
  theorem Block.eval_of_run {fuel : Nat} {block : Block}
      {state final : EVMState}
      (hRun : Block.run fuel block state = .ok final) :
      Block.Eval fuel block state final := by
    cases fuel with
    | zero =>
        simp [Block.run, invalid] at hRun
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                simp [Block.run] at hRun
                cases hRun
                exact Block.Eval.nil
            | cons stmt rest =>
                unfold Block.run at hRun
                cases hStmt : Stmt.run fuel stmt state with
                | error err =>
                    rw [hStmt] at hRun
                    cases hRun
                | ok mid =>
                    rw [hStmt] at hRun
                    exact
                      Block.Eval.cons
                        (Stmt.eval_of_run hStmt)
                        (Block.eval_of_run hRun)

  theorem Stmt.eval_of_run {fuel : Nat} {stmt : Stmt}
      {state final : EVMState}
      (hRun : Stmt.run fuel stmt state = .ok final) :
      Stmt.Eval fuel stmt state final := by
    cases stmt with
    | code code =>
        cases fuel with
        | zero =>
            simp [Stmt.run] at hRun
            exact Stmt.Eval.code hRun
        | succ fuel =>
            simp [Stmt.run] at hRun
            exact Stmt.Eval.code hRun
    | ifElse cond thenBody elseBody =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun
            cases hCond : Code.runCondition cond state with
            | error err =>
                rw [hCond] at hRun
                cases hRun
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                rw [hCond] at hRun
                cases condTrue with
                | false =>
                    simp at hRun
                    exact
                      Stmt.Eval.ifFalse hCond
                        (Block.eval_of_run hRun)
                | true =>
                    simp at hRun
                    exact
                      Stmt.Eval.ifTrue hCond
                        (Block.eval_of_run hRun)
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun
            cases hInit : Block.run fuel init state with
            | error err =>
                rw [hInit] at hRun
                cases hRun
            | ok stateAfterInit =>
                rw [hInit] at hRun
                exact
                  Stmt.Eval.for_
                    (Block.eval_of_run hInit)
                    (For.eval_of_run hRun)

  theorem For.eval_of_run {fuel : Nat} {cond : Code} {post body : Block}
      {state final : EVMState}
      (hRun : Stmt.runForLoop fuel cond post body state = .ok final) :
      For.Eval fuel cond post body state final := by
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, invalid] at hRun
    | succ fuel =>
        unfold Stmt.runForLoop at hRun
        cases hCond : Code.runCondition cond state with
        | error err =>
            rw [hCond] at hRun
            cases hRun
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue⟩
            rw [hCond] at hRun
            cases condTrue with
            | false =>
                simp at hRun
                cases hRun
                exact For.Eval.false hCond
            | true =>
                change
                  (do
                    let stateAfterBody ← Block.run fuel body stateAfterCond
                    let stateAfterPost ← Block.run fuel post stateAfterBody
                    Stmt.runForLoop fuel cond post body stateAfterPost) =
                    Except.ok final at hRun
                cases hBody : Block.run fuel body stateAfterCond with
                | error err =>
                    rw [hBody] at hRun
                    cases hRun
                | ok stateAfterBody =>
                    rw [hBody] at hRun
                    change
                      (do
                        let stateAfterPost ← Block.run fuel post stateAfterBody
                        Stmt.runForLoop fuel cond post body stateAfterPost) =
                        Except.ok final at hRun
                    cases hPost : Block.run fuel post stateAfterBody with
                    | error err =>
                        rw [hPost] at hRun
                        cases hRun
                    | ok stateAfterPost =>
                        rw [hPost] at hRun
                        change
                          Stmt.runForLoop fuel cond post body stateAfterPost =
                            Except.ok final at hRun
                        exact
                          For.Eval.true hCond
                            (Block.eval_of_run hBody)
                            (Block.eval_of_run hPost)
                            (For.eval_of_run hRun)
end

namespace Program

theorem eval_of_run {fuel : Nat} {program : Program}
    {state final : EVMState}
    (hRun : run fuel program state = .ok final) :
    Block.Eval fuel program.body state final := by
  unfold run at hRun
  exact Block.eval_of_run hRun

end Program

/--
The structured layer abstracts away from the concrete assembly program counter.
It also inherits the gas-erasure boundary of the assembly layer.
-/
def eraseControl (state : EVMState) : EVMState :=
  { Assembly.eraseGas state with pc := EvmYul.UInt256.ofNat 0 }

theorem eraseControl_with_pc (state : EVMState) (pc : Word) :
    eraseControl { state with pc := pc } = eraseControl state := by
  cases state
  rfl

theorem eraseControl_with_stack (state : EVMState) (stack : EvmYul.Stack Word) :
    eraseControl { state with stack := stack } =
      { eraseControl state with stack := stack } := by
  cases state
  rfl

theorem stack_eq_of_eraseControl_eq {left right : EVMState}
    (h : eraseControl left = eraseControl right) :
    left.stack = right.stack := by
  cases left
  cases right
  simp [eraseControl, Assembly.eraseGas] at h
  exact h.2

theorem eraseControl_replaceStackAndIncrPC_of_eq {left right : EVMState}
    {leftStack rightStack : EvmYul.Stack Word}
    {pcΔ : Nat}
    (hEq : eraseControl left = eraseControl right)
    (hStack : leftStack = rightStack) :
    eraseControl (left.replaceStackAndIncrPC leftStack (pcΔ := pcΔ)) =
      eraseControl (right.replaceStackAndIncrPC rightStack (pcΔ := pcΔ)) := by
  cases left
  cases right
  cases hStack
  simp [eraseControl, Assembly.eraseGas] at hEq ⊢
  exact ⟨hEq.1, rfl⟩

theorem execBinOp_projected_of_eraseControl_eq
    (f : EvmYul.Primop.Binary) {source target source' : EVMState}
    (hEq : eraseControl target = eraseControl source)
    (hStep : EvmYul.EVM.execBinOp f source = .ok source') :
    ∃ target',
      EvmYul.EVM.execBinOp f target = .ok target' ∧
        eraseControl target' = eraseControl source' := by
  unfold EvmYul.EVM.execBinOp at hStep ⊢
  have hStack := stack_eq_of_eraseControl_eq hEq
  cases hPop : source.stack.pop2 with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a, b⟩
      have hTargetPop : target.stack.pop2 = some (rest, a, b) := by
        rw [hStack, hPop]
      rw [hPop] at hStep
      rw [hTargetPop]
      simp at hStep
      cases hStep
      refine ⟨target.replaceStackAndIncrPC (rest.push (f a b)), rfl, ?_⟩
      exact eraseControl_replaceStackAndIncrPC_of_eq hEq rfl

theorem execUnOp_projected_of_eraseControl_eq
    (f : EvmYul.Primop.Unary) {source target source' : EVMState}
    (hEq : eraseControl target = eraseControl source)
    (hStep : EvmYul.EVM.execUnOp f source = .ok source') :
    ∃ target',
      EvmYul.EVM.execUnOp f target = .ok target' ∧
        eraseControl target' = eraseControl source' := by
  unfold EvmYul.EVM.execUnOp at hStep ⊢
  have hStack := stack_eq_of_eraseControl_eq hEq
  cases hPop : source.stack.pop with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a⟩
      have hTargetPop : target.stack.pop = some (rest, a) := by
        rw [hStack, hPop]
      rw [hPop] at hStep
      rw [hTargetPop]
      simp at hStep
      cases hStep
      refine ⟨target.replaceStackAndIncrPC (rest.push (f a)), rfl, ?_⟩
      exact eraseControl_replaceStackAndIncrPC_of_eq hEq rfl

namespace BasicInstr

theorem step_projected_of_eraseControl_eq {instr : BasicInstr}
    {source target source' : EVMState}
    (hEq : eraseControl target = eraseControl source)
    (hStep : instr.step source = .ok source') :
    ∃ target',
      instr.step target = .ok target' ∧
        eraseControl target' = eraseControl source' := by
  cases instr with
  | push value =>
      unfold BasicInstr.step at hStep
      simp [Assembly.Target.stepInstr] at hStep
      have hStack := stack_eq_of_eraseControl_eq hEq
      cases hStep
      refine
        ⟨target.replaceStackAndIncrPC (target.stack.push value) (pcΔ := 33),
          ?_, ?_⟩
      · unfold BasicInstr.step
        simp [Assembly.Target.stepInstr]
      exact
        eraseControl_replaceStackAndIncrPC_of_eq hEq
          (by rw [hStack])
  | op op =>
      cases op with
      | add =>
          unfold BasicInstr.step BasicOp.step at hStep ⊢
          change EvmYul.EVM.execBinOp EvmYul.UInt256.add source = .ok source' at hStep
          exact execBinOp_projected_of_eraseControl_eq EvmYul.UInt256.add hEq hStep
      | sub =>
          unfold BasicInstr.step BasicOp.step at hStep ⊢
          change EvmYul.EVM.execBinOp EvmYul.UInt256.sub source = .ok source' at hStep
          exact execBinOp_projected_of_eraseControl_eq EvmYul.UInt256.sub hEq hStep
      | lt =>
          unfold BasicInstr.step BasicOp.step at hStep ⊢
          change EvmYul.EVM.execBinOp EvmYul.UInt256.lt source = .ok source' at hStep
          exact execBinOp_projected_of_eraseControl_eq EvmYul.UInt256.lt hEq hStep
      | gt =>
          unfold BasicInstr.step BasicOp.step at hStep ⊢
          change EvmYul.EVM.execBinOp EvmYul.UInt256.gt source = .ok source' at hStep
          exact execBinOp_projected_of_eraseControl_eq EvmYul.UInt256.gt hEq hStep
      | eq =>
          unfold BasicInstr.step BasicOp.step at hStep ⊢
          change EvmYul.EVM.execBinOp EvmYul.UInt256.eq source = .ok source' at hStep
          exact execBinOp_projected_of_eraseControl_eq EvmYul.UInt256.eq hEq hStep
      | iszero =>
          unfold BasicInstr.step BasicOp.step at hStep ⊢
          change EvmYul.EVM.execUnOp EvmYul.UInt256.isZero source = .ok source' at hStep
          exact execUnOp_projected_of_eraseControl_eq EvmYul.UInt256.isZero hEq hStep

end BasicInstr

namespace Code

theorem run_projected_of_eraseControl_eq {code : Code}
    {source target source' : EVMState}
    (hEq : eraseControl target = eraseControl source)
    (hRun : run code source = .ok source') :
    ∃ target',
      run code target = .ok target' ∧
        eraseControl target' = eraseControl source' := by
  induction code generalizing source target with
  | nil =>
      simp [run] at hRun
      cases hRun
      exact ⟨target, by simp [run], hEq⟩
  | cons instr rest ih =>
      unfold run at hRun ⊢
      cases hStep : instr.step source with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok sourceMid =>
          rw [hStep] at hRun
          obtain ⟨targetMid, hTargetStep, hMidEq⟩ :=
            BasicInstr.step_projected_of_eraseControl_eq hEq hStep
          rw [hTargetStep]
          exact ih hMidEq hRun

theorem popCondition_projected_of_eraseControl_eq
    {source target source' : EVMState} {condTrue : Bool}
    (hEq : eraseControl target = eraseControl source)
    (hPop : popCondition source = .ok (source', condTrue)) :
    ∃ target',
      popCondition target = .ok (target', condTrue) ∧
        eraseControl target' = eraseControl source' := by
  unfold popCondition at hPop ⊢
  have hStack := stack_eq_of_eraseControl_eq hEq
  cases hSourcePop : source.stack.pop with
  | none =>
      rw [hSourcePop] at hPop
      cases hPop
  | some popped =>
      rcases popped with ⟨rest, cond⟩
      have hTargetPop : target.stack.pop = some (rest, cond) := by
        rw [hStack, hSourcePop]
      rw [hSourcePop] at hPop
      rw [hTargetPop]
      simp at hPop
      cases hPop.1
      cases hPop.2
      refine ⟨{ target with stack := rest }, ?_, ?_⟩
      · rfl
      calc
        eraseControl { target with stack := rest }
            = { eraseControl target with stack := rest } := eraseControl_with_stack target rest
        _ = { eraseControl source with stack := rest } := by rw [hEq]
        _ = eraseControl { source with stack := rest } := (eraseControl_with_stack source rest).symm

theorem runCondition_projected_of_eraseControl_eq {code : Code}
    {source target source' : EVMState} {condTrue : Bool}
    (hEq : eraseControl target = eraseControl source)
    (hRun : runCondition code source = .ok (source', condTrue)) :
    ∃ target',
      runCondition code target = .ok (target', condTrue) ∧
        eraseControl target' = eraseControl source' := by
  unfold runCondition at hRun ⊢
  cases hCode : run code source with
  | error err =>
      rw [hCode] at hRun
      cases hRun
  | ok sourceMid =>
      rw [hCode] at hRun
      obtain ⟨targetMid, hTargetCode, hMidEq⟩ :=
        run_projected_of_eraseControl_eq hEq hCode
      rw [hTargetCode]
      exact popCondition_projected_of_eraseControl_eq hMidEq hRun

end Code

mutual
  theorem Block.run_projected_of_eraseControl_eq {fuel : Nat} {block : Block}
      {source target source' : EVMState}
      (hEq : eraseControl target = eraseControl source)
      (hRun : Block.run fuel block source = .ok source') :
      ∃ target',
        Block.run fuel block target = .ok target' ∧
          eraseControl target' = eraseControl source' := by
    cases fuel with
    | zero =>
        simp [Block.run, invalid] at hRun
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                simp [Block.run] at hRun ⊢
                cases hRun
                exact hEq
            | cons stmt rest =>
                unfold Block.run at hRun ⊢
                cases hStmt : Stmt.run fuel stmt source with
                | error err =>
                    rw [hStmt] at hRun
                    cases hRun
                | ok sourceMid =>
                    rw [hStmt] at hRun
                    obtain ⟨targetMid, hTargetStmt, hMidEq⟩ :=
                      Stmt.run_projected_of_eraseControl_eq hEq hStmt
                    rw [hTargetStmt]
                    exact Block.run_projected_of_eraseControl_eq hMidEq hRun

  theorem Stmt.runForLoop_projected_of_eraseControl_eq {fuel : Nat}
      {cond : Code} {post body : Block}
      {source target source' : EVMState}
      (hEq : eraseControl target = eraseControl source)
      (hRun : Stmt.runForLoop fuel cond post body source = .ok source') :
      ∃ target',
        Stmt.runForLoop fuel cond post body target = .ok target' ∧
          eraseControl target' = eraseControl source' := by
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, invalid] at hRun
    | succ fuel =>
        unfold Stmt.runForLoop at hRun ⊢
        cases hCond : Code.runCondition cond source with
        | error err =>
            rw [hCond] at hRun
            cases hRun
        | ok condResult =>
            rcases condResult with ⟨sourceAfterCond, condTrue⟩
            rw [hCond] at hRun
            obtain ⟨targetAfterCond, hTargetCond, hCondEq⟩ :=
              Code.runCondition_projected_of_eraseControl_eq hEq hCond
            rw [hTargetCond]
            cases condTrue with
            | false =>
                change Except.ok sourceAfterCond = Except.ok source' at hRun
                change
                  ∃ target',
                    Except.ok targetAfterCond = Except.ok target' ∧
                      eraseControl target' = eraseControl source'
                cases hRun
                exact ⟨targetAfterCond, rfl, hCondEq⟩
            | true =>
                change
                  (do
                    let stateAfterBody ← Block.run fuel body sourceAfterCond
                    let stateAfterPost ← Block.run fuel post stateAfterBody
                    Stmt.runForLoop fuel cond post body stateAfterPost) =
                    Except.ok source' at hRun
                change
                  ∃ target',
                    (do
                      let stateAfterBody ← Block.run fuel body targetAfterCond
                      let stateAfterPost ← Block.run fuel post stateAfterBody
                      Stmt.runForLoop fuel cond post body stateAfterPost) =
                        Except.ok target' ∧
                      eraseControl target' = eraseControl source'
                cases hBody : Block.run fuel body sourceAfterCond with
                | error err =>
                    rw [hBody] at hRun
                    cases hRun
                | ok sourceAfterBody =>
                    rw [hBody] at hRun
                    change
                      (do
                        let stateAfterPost ← Block.run fuel post sourceAfterBody
                        Stmt.runForLoop fuel cond post body stateAfterPost) =
                        Except.ok source' at hRun
                    obtain ⟨targetAfterBody, hTargetBody, hBodyEq⟩ :=
                      Block.run_projected_of_eraseControl_eq hCondEq hBody
                    rw [hTargetBody]
                    change
                      ∃ target',
                        (do
                          let stateAfterPost ← Block.run fuel post targetAfterBody
                          Stmt.runForLoop fuel cond post body stateAfterPost) =
                            Except.ok target' ∧
                          eraseControl target' = eraseControl source'
                    cases hPost : Block.run fuel post sourceAfterBody with
                    | error err =>
                        rw [hPost] at hRun
                        cases hRun
                    | ok sourceAfterPost =>
                        rw [hPost] at hRun
                        change
                          Stmt.runForLoop fuel cond post body sourceAfterPost =
                            Except.ok source' at hRun
                        obtain ⟨targetAfterPost, hTargetPost, hPostEq⟩ :=
                          Block.run_projected_of_eraseControl_eq hBodyEq hPost
                        rw [hTargetPost]
                        change
                          ∃ target',
                            Stmt.runForLoop fuel cond post body targetAfterPost =
                              Except.ok target' ∧
                            eraseControl target' = eraseControl source'
                        exact
                          Stmt.runForLoop_projected_of_eraseControl_eq
                            hPostEq hRun

  theorem Stmt.run_projected_of_eraseControl_eq {fuel : Nat} {stmt : Stmt}
      {source target source' : EVMState}
      (hEq : eraseControl target = eraseControl source)
      (hRun : Stmt.run fuel stmt source = .ok source') :
      ∃ target',
        Stmt.run fuel stmt target = .ok target' ∧
          eraseControl target' = eraseControl source' := by
    cases stmt with
    | code code =>
        cases fuel with
        | zero =>
            simp [Stmt.run] at hRun ⊢
            exact Code.run_projected_of_eraseControl_eq hEq hRun
        | succ fuel =>
            simp [Stmt.run] at hRun ⊢
            exact Code.run_projected_of_eraseControl_eq hEq hRun
    | ifElse cond thenBody elseBody =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun ⊢
            cases hCond : Code.runCondition cond source with
            | error err =>
                rw [hCond] at hRun
                cases hRun
            | ok condResult =>
                rcases condResult with ⟨sourceAfterCond, condTrue⟩
                rw [hCond] at hRun
                obtain ⟨targetAfterCond, hTargetCond, hCondEq⟩ :=
                  Code.runCondition_projected_of_eraseControl_eq hEq hCond
                rw [hTargetCond]
                cases condTrue with
                | false =>
                    simp at hRun ⊢
                    exact Block.run_projected_of_eraseControl_eq hCondEq hRun
                | true =>
                    simp at hRun ⊢
                    exact Block.run_projected_of_eraseControl_eq hCondEq hRun
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun ⊢
            cases hInit : Block.run fuel init source with
            | error err =>
                rw [hInit] at hRun
                cases hRun
            | ok sourceAfterInit =>
                rw [hInit] at hRun
                obtain ⟨targetAfterInit, hTargetInit, hInitEq⟩ :=
                  Block.run_projected_of_eraseControl_eq hEq hInit
                rw [hTargetInit]
                exact
                  Stmt.runForLoop_projected_of_eraseControl_eq
                    hInitEq hRun
end

namespace Program

theorem run_projected_of_eraseControl_eq {fuel : Nat} {program : Program}
    {source target source' : EVMState}
    (hEq : eraseControl target = eraseControl source)
    (hRun : run fuel program source = .ok source') :
    ∃ target',
      run fuel program target = .ok target' ∧
        eraseControl target' = eraseControl source' := by
  unfold run at hRun ⊢
  exact Block.run_projected_of_eraseControl_eq hEq hRun

end Program

end Structured
end EvmCompiler
