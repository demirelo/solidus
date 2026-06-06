import EvmCompiler.Yul.ObjectModel

namespace EvmCompiler
namespace Yul
namespace ObjectModel

/-
Independent source semantics for the Yul object layer.

This interpreter runs over `ObjectModel.Expr`/`Stmt` directly.  The object
layout is part of the semantic runtime, so `datasize` and `dataoffset` read the
source object layout table, while `datacopy` executes as the source-level
object builtin by evaluating its three operands and applying Yul `CODECOPY` to
the current `ExecutionEnv.codeBytes`.  The compiler/lowering layer is
responsible for constructing this runtime from the source object and proving it
matches the emitted image; callers do not supply layout certificates to the
public compiler.
-/
namespace Source

abbrev State := ReferenceState
abbrev Exception := ReferenceException
abbrev Literal := Word

structure Runtime where
  contract : Contract
  layout : ObjectLayout
  codeImage : ByteArray
  installedContract : AstContract
  linkerSymbols : List (Name × Word) := []
  immutableValues : List (Name × Word) := []
  immutableReferences : List (Name × List ImmutableReference) := []

def installCodeImage (runtime : Runtime) : State → State
  | .Ok shared store =>
      .Ok
        { shared with
          executionEnv :=
            { shared.executionEnv with
              code := runtime.installedContract
              codeBytes := runtime.codeImage } }
        store
  | .OutOfFuel => .OutOfFuel
  | .Checkpoint jump => .Checkpoint jump

def headResult :
    Except Exception (State × List Literal) →
      Except Exception (State × Literal)
  | .ok (state, values) => .ok (state, List.head! values)
  | .error exception => .error exception

def consResult (value : Literal) :
    Except Exception (State × List Literal) →
      Except Exception (State × List Literal)
  | .ok (state, values) => .ok (state, value :: values)
  | .error exception => .error exception

def reverseResult :
    Except Exception (State × List Literal) →
      Except Exception (State × List Literal)
  | .ok (state, values) => .ok (state, values.reverse)
  | .error exception => .error exception

def multifillResult (vars : List Name) :
    Except Exception (State × List Literal) → Except Exception State
  | .ok (state, values) => .ok (state.multifill vars values)
  | .error exception => .error exception

def layoutSize? (runtime : Runtime) (name : Name) : Option Literal :=
  Objects.ObjectLayout.size? runtime.layout name

def layoutOffset? (runtime : Runtime) (name : Name) : Option Literal :=
  Objects.ObjectLayout.offset? runtime.layout name

def linkerSymbol? (runtime : Runtime) (name : Name) : Option Literal :=
  findNamed? runtime.linkerSymbols name

def immutableValue? (runtime : Runtime) (name : Name) : Option Literal :=
  findNamed? runtime.immutableValues name

def immutableReferences? (runtime : Runtime) (name : Name) :
    Option (List ImmutableReference) :=
  match collectNamedLists runtime.immutableReferences name with
  | [] => none
  | head :: tail => some (head :: tail)

def patchStmt? (reference : ImmutableReference) (base value : Expr) :
    Option Stmt :=
  if reference.isPatchable then
    some
      (.exprStmtCall
        (.call (.inl ((.StackMemFlow .MSTORE : EvmYul.Operation .Yul)))
          [ .call (.inl ((.StopArith .ADD : EvmYul.Operation .Yul)))
              [base, .lit (EvmYul.UInt256.ofNat reference.start)]
          , value ]))
  else
    none

namespace ImmutableReferenceList

def patchStmts? : List ImmutableReference → Expr → Expr → Option (List Stmt)
  | [], _base, _value => some []
  | reference :: rest, base, value => do
      let head ← patchStmt? reference base value
      let tail ← patchStmts? rest base value
      some (head :: tail)

end ImmutableReferenceList

def lookupFunction? (contract : Contract) (functionName : AstFunctionName) :
    Option FunctionDefinition :=
  contract.functions.find? (fun entry => entry.1 == functionName) |>.map Prod.snd

def selectSwitchCase (cond : Literal)
    (defaultBody : List Stmt) :
    List (Literal × List Stmt) → List Stmt
  | [] => defaultBody
  | (value, body) :: cases =>
      if value = cond then body else selectSwitchCase cond defaultBody cases

mutual
  def evalTail (fuel : Nat) (runtime : Runtime) (args : List Expr) :
      Except Exception (State × Literal) →
        Except Exception (State × List Literal)
    | .ok (state, value) =>
        match fuel with
        | 0 => .error .OutOfFuel
        | fuel' + 1 => consResult value (evalArgs fuel' runtime args state)
    | .error exception => .error exception

  def evalArgs (fuel : Nat) (runtime : Runtime) (args : List Expr)
      (state : State) : Except Exception (State × List Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | fuel' + 1 =>
        match args with
        | [] => .ok (state, [])
        | arg :: rest =>
            evalTail fuel' runtime rest
              (eval fuel' runtime arg state)

  def call (fuel : Nat) (runtime : Runtime) (args : List Literal)
      (functionName? : Option AstFunctionName) (state : State) :
      Except Exception (State × List Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | fuel' + 1 =>
        match functionName? with
        | none =>
            let fn : FunctionDefinition :=
              { params := []
                returns := []
                body := [runtime.contract.dispatcher] }
            let state₁ :=
              EvmYul.Yul.State.mkOk
                (EvmYul.Yul.State.initcall fn.params fn.returns args state)
            match exec fuel' runtime (.block fn.body) state₁ with
            | .error exception => .error exception
            | .ok state₂ =>
                let state₃ :=
                  EvmYul.Yul.State.setStore
                    (EvmYul.Yul.State.overwrite?
                      (EvmYul.Yul.State.reviveJump state₂) state)
                    state
                .ok (state₃, fn.returns.map state₂.lookup!)
        | some functionName =>
            match
                state.sharedState.accountMap.find?
                  state.executionEnv.codeOwner with
            | none =>
                .error (.MissingContract (s!"{state.executionEnv.codeOwner}"))
            | some _contractAccount =>
                match lookupFunction? runtime.contract functionName with
                | none =>
                    .error (.MissingContractFunction functionName)
                | some fn =>
                    let state₁ :=
                      EvmYul.Yul.State.mkOk
                        (EvmYul.Yul.State.initcall
                          fn.params fn.returns args state)
                    match exec fuel' runtime (.block fn.body) state₁ with
                    | .error exception => .error exception
                    | .ok state₂ =>
                        let state₃ :=
                          EvmYul.Yul.State.setStore
                            (EvmYul.Yul.State.overwrite?
                              (EvmYul.Yul.State.reviveJump state₂) state)
                            state
                        .ok (state₃, fn.returns.map state₂.lookup!)

  def callDispatcher (fuel : Nat) (runtime : Runtime) (state : State) :
      Except Exception (State × List Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | fuel' + 1 =>
        let fn : FunctionDefinition :=
          { params := []
            returns := []
            body := [runtime.contract.dispatcher] }
        let state₁ :=
          EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall fn.params fn.returns [] state)
        match exec fuel' runtime (.block fn.body) state₁ with
        | .error exception => .error exception
        | .ok state₂ =>
            let state₃ :=
              EvmYul.Yul.State.setStore
                (EvmYul.Yul.State.overwrite?
                  (EvmYul.Yul.State.reviveJump state₂) state)
                state
            .ok (state₃, fn.returns.map state₂.lookup!)

  def evalPrimCall (fuel : Nat) (prim : PrimOp) :
      Except Exception (State × List Literal) →
        Except Exception (State × Literal)
    | .ok (state, args) => headResult (EvmYul.Yul.primCall fuel state prim args)
    | .error exception => .error exception

  def evalCall (fuel : Nat) (runtime : Runtime) (functionName : AstFunctionName) :
      Except Exception (State × List Literal) →
        Except Exception (State × Literal)
    | .ok (state, args) =>
        match fuel with
        | 0 => .error .OutOfFuel
        | fuel' + 1 => headResult (call fuel' runtime args (some functionName) state)
    | .error exception => .error exception

  def execPrimCall (fuel : Nat) (prim : PrimOp) (vars : List Name) :
      Except Exception (State × List Literal) → Except Exception State
    | .ok (state, args) =>
        multifillResult vars (EvmYul.Yul.primCall fuel state prim args)
    | .error exception => .error exception

  def execCall (fuel : Nat) (runtime : Runtime)
      (functionName : AstFunctionName) (vars : List Name) :
      Except Exception (State × List Literal) → Except Exception State
    | .ok (state, args) =>
        match fuel with
        | 0 => .error .OutOfFuel
        | fuel' + 1 =>
            multifillResult vars
              (call fuel' runtime args (some functionName) state)
    | .error exception => .error exception

  def evalValues (fuel : Nat) (runtime : Runtime) (expr : Expr)
      (state : State) : Except Exception (State × List Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | fuel' + 1 =>
        match expr with
        | .call (.inl prim) args =>
            match reverseResult (evalArgs fuel' runtime args.reverse state) with
            | .ok (state, args) => EvmYul.Yul.primCall fuel' state prim args
            | .error exception => .error exception
        | .call (.inr functionName) args =>
            match reverseResult (evalArgs fuel' runtime args.reverse state) with
            | .ok (state, args) =>
                call fuel' runtime args (some functionName) state
            | .error exception => .error exception
        | .var name =>
            match state.lookup? name with
            | some value => .ok (state, [value])
            | none => .error (.UnknownIdentifier name)
        | .lit value => .ok (state, [value])
        | .datasize name =>
            match layoutSize? runtime name with
            | some value => .ok (state, [value])
            | none => .error .InvalidArguments
        | .dataoffset name =>
            match layoutOffset? runtime name with
            | some value => .ok (state, [value])
            | none => .error .InvalidArguments
        | .linkersymbol name =>
            match linkerSymbol? runtime name with
            | some value => .ok (state, [value])
            | none => .error .InvalidArguments
        | .loadimmutable name =>
            match immutableValue? runtime name with
            | some value => .ok (state, [value])
            | none => .error .InvalidArguments
        | .memoryguard size => .ok (state, [size])
        | .datacopy dst offset size =>
            match
                reverseResult
                  (evalArgs fuel' runtime [dst, offset, size].reverse state) with
            | .ok (state, args) =>
                EvmYul.Yul.primCall fuel' state
                  ((.Env .CODECOPY : EvmYul.Operation .Yul)) args
            | .error exception => .error exception

  def eval (fuel : Nat) (runtime : Runtime) (expr : Expr)
      (state : State) : Except Exception (State × Literal) :=
    headResult (evalValues fuel runtime expr state)

  def execSeq (fuel : Nat) (runtime : Runtime) (stmts : List Stmt)
      (state : State) : Except Exception State :=
    match fuel with
    | 0 => .error .OutOfFuel
    | fuel' + 1 =>
        match stmts with
        | [] => .ok state
        | stmt :: rest =>
            match exec fuel' runtime stmt state with
            | .error exception => .error exception
            | .ok state₁ =>
                match state₁ with
                | .Ok _ _ => execSeq fuel' runtime rest state₁
                | .OutOfFuel => .ok state₁
                | .Checkpoint _ => .ok state₁

  def exec (fuel : Nat) (runtime : Runtime) (stmt : Stmt)
      (state : State) : Except Exception State :=
    match fuel with
    | 0 => .error .OutOfFuel
    | fuel' + 1 =>
        match stmt with
        | .block body =>
            match execSeq fuel' runtime body state with
            | .error exception => .error exception
            | .ok state₁ => .ok (state₁.restrictStoreTo state.store)
        | .let_ vars value? =>
            match EvmYul.Yul.checkDeclaration state vars with
            | .error exception => .error exception
            | .ok () =>
                match value? with
                | none => .ok (state.zeroFill vars)
                | some value =>
                    multifillResult vars (evalValues fuel' runtime value state)
        | .assign vars value =>
            match EvmYul.Yul.checkAssignment state vars with
            | .error exception => .error exception
            | .ok () =>
                multifillResult vars (evalValues fuel' runtime value state)
        | .exprStmtCall expr =>
            match expr with
            | .call (.inl prim) args =>
                execPrimCall fuel' prim []
                  (reverseResult (evalArgs fuel' runtime args.reverse state))
            | .call (.inr functionName) args =>
                execCall fuel' runtime functionName []
                  (reverseResult (evalArgs fuel' runtime args.reverse state))
            | .datacopy dst offset size =>
                execPrimCall fuel'
                  ((.Env .CODECOPY : EvmYul.Operation .Yul)) []
                  (reverseResult
                    (evalArgs fuel' runtime
                      [dst, offset, size].reverse state))
            | _ => .error .InvalidExpression
        | .switch scrutinee cases defaultBody =>
            match eval fuel' runtime scrutinee state with
            | .error exception => .error exception
            | .ok (state₁, cond) =>
                exec fuel' runtime
                  (.block (selectSwitchCase cond defaultBody cases)) state₁
        | .for_ cond post body => loop fuel' runtime cond post body state
        | .if_ cond body =>
            match eval fuel' runtime cond state with
            | .error exception => .error exception
            | .ok (state₁, cond) =>
                if cond ≠ EvmYul.UInt256.ofNat 0 then
                  exec fuel' runtime (.block body) state₁
                else
                  .ok state₁
        | .setimmutable offset name value =>
            match immutableReferences? runtime name with
            | none => .error .InvalidArguments
            | some references =>
                match
                    ImmutableReferenceList.patchStmts? references offset value
                with
                | none => .error .InvalidArguments
                | some patchStmts =>
                    match execSeq fuel' runtime patchStmts state with
                    | .error exception => .error exception
                    | .ok state₁ => .ok (state₁.restrictStoreTo state.store)
        | .continue => .ok (EvmYul.Yul.State.setContinue state)
        | .break => .ok (EvmYul.Yul.State.setBreak state)
        | .leave => .ok (EvmYul.Yul.State.setLeave state)

  def loop (fuel : Nat) (runtime : Runtime) (cond : Expr)
      (post body : List Stmt) (state : State) : Except Exception State :=
    match fuel with
    | 0 => .error .OutOfFuel
    | 1 => .error .OutOfFuel
    | fuel' + 1 + 1 =>
        match eval fuel' runtime cond (EvmYul.Yul.State.mkOk state) with
        | .error exception => .error exception
        | .ok (state₁, value) =>
            if value = EvmYul.UInt256.ofNat 0 then
              .ok (EvmYul.Yul.State.overwrite? state₁ state)
            else
              match exec fuel' runtime (.block body) state₁ with
              | .error exception => .error exception
              | .ok state₂ =>
                  match state₂ with
                  | .OutOfFuel =>
                      .ok (EvmYul.Yul.State.overwrite? state₂ state)
                  | .Checkpoint (.Break _ _) =>
                      .ok
                        (EvmYul.Yul.State.overwrite?
                          (EvmYul.Yul.State.reviveJump state₂) state)
                  | .Checkpoint (.Leave _ _) =>
                      .ok (EvmYul.Yul.State.overwrite? state₂ state)
                  | .Checkpoint (.Continue _ _) | _ =>
                      match
                          exec fuel' runtime (.block post)
                            (EvmYul.Yul.State.reviveJump state₂) with
                      | .error exception => .error exception
                      | .ok state₃ =>
                          let state₄ := EvmYul.Yul.State.overwrite? state₃ state
                          match state₃ with
                          | .OutOfFuel => .ok state₄
                          | .Checkpoint (.Leave _ _) => .ok state₄
                          | _ =>
                              match
                                  exec fuel' runtime
                                    (.for_ cond post body) state₄ with
                              | .error exception => .error exception
                              | .ok state₅ =>
                                  .ok (EvmYul.Yul.State.overwrite? state₅ state)
end

def runContract (runtime : Runtime) (fuel : Nat) (state : State) :
    Except Exception ReferenceResult :=
  match callDispatcher fuel runtime (installCodeImage runtime state) with
  | .ok (state', _rets) => .ok (.regular state')
  | .error (.YulHalt state' value) => .ok (.yulHalt state' value)
  | .error (.Revert stateBeforeRevert) => .ok (.revert stateBeforeRevert)
  | .error exception => .error exception

namespace Runtime

def withCodeImage (runtime : Runtime) (codeImage : ByteArray) : Runtime :=
  { runtime with codeImage := codeImage }

def checkedMode (runtime : Runtime) : LayoutMode :=
  .checkedWith runtime.layout runtime.linkerSymbols runtime.immutableValues
    runtime.immutableReferences

@[simp] theorem checkedMode_withCodeImage
    (runtime : Runtime) (codeImage : ByteArray) :
    (withCodeImage runtime codeImage).checkedMode = runtime.checkedMode := by
  rfl

noncomputable def ofCheckedProgram? (program : Program) : Option Runtime := do
  let lower ← Program.toObjects? program
  let layout ← Objects.Program.payloadLayout? lower
  let image ← Objects.Program.bytecodeImage? lower
  let installedContract ← program.root.code.toAst? (Program.checkedMode program layout)
  some
    { contract := program.root.code
      layout := layout
      codeImage := image
      installedContract := installedContract
      linkerSymbols := program.linkerSymbols
      immutableValues := program.immutableValues
      immutableReferences := program.immutableReferences }

theorem ofCheckedProgram?_checked {program : Program} {runtime : Runtime}
    (hRuntime : ofCheckedProgram? program = some runtime) :
    ∃ lower : Objects.Program,
      Program.toObjects? program = some lower ∧
        Objects.Program.payloadLayout? lower = some runtime.layout ∧
          Objects.Program.bytecodeImage? lower = some runtime.codeImage ∧
            program.root.code.toAst? (Program.checkedMode program runtime.layout) =
              some runtime.installedContract ∧
              runtime.contract = program.root.code ∧
                runtime.linkerSymbols = program.linkerSymbols ∧
                  runtime.immutableValues = program.immutableValues ∧
                    runtime.immutableReferences = program.immutableReferences := by
  unfold ofCheckedProgram? at hRuntime
  cases hLower : Program.toObjects? program with
  | none =>
      simp [hLower] at hRuntime
  | some lower =>
      cases hLayout : Objects.Program.payloadLayout? lower with
      | none =>
          simp [hLower, hLayout] at hRuntime
      | some layout =>
          cases hImage : Objects.Program.bytecodeImage? lower with
          | none =>
              simp [hLower, hLayout, hImage] at hRuntime
              | some image =>
                  cases hContract :
                  program.root.code.toAst? (Program.checkedMode program layout) with
              | none =>
                  simp [hLower, hLayout, hImage, hContract] at hRuntime
              | some installedContract =>
                  simp [hLower, hLayout, hImage, hContract] at hRuntime
                  subst hRuntime
                  exact ⟨lower, rfl, hLayout, hImage, hContract, rfl, rfl,
                    rfl, rfl⟩

end Runtime

namespace Program

noncomputable def sourceRun? (fuel : Nat) (program : Program)
    (state : State) : Option (Except Exception ReferenceResult) := do
  let runtime ← Runtime.ofCheckedProgram? program
  some (runContract runtime fuel state)

noncomputable def sourceRunWithCodeImage? (fuel : Nat) (program : Program)
    (codeImage : ByteArray) (state : State) :
    Option (Except Exception ReferenceResult) := do
  let runtime ← Runtime.ofCheckedProgram? program
  some (runContract (Runtime.withCodeImage runtime codeImage) fuel state)

noncomputable def sourceRunWithCodeSuffix? (fuel : Nat) (program : Program)
    (suffix : ByteArray) (state : State) :
    Option (Except Exception ReferenceResult) := do
  let image ← ObjectModel.Program.bytecodeImage? program
  sourceRunWithCodeImage? fuel program (image ++ suffix) state

theorem sourceRun?_checked {fuel : Nat} {program : Program}
    {state : State} {result : Except Exception ReferenceResult}
    (hRun : sourceRun? fuel program state = some result) :
    ∃ runtime : Runtime,
      Runtime.ofCheckedProgram? program = some runtime ∧
        runContract runtime fuel state = result := by
  unfold sourceRun? at hRun
  cases hRuntime : Runtime.ofCheckedProgram? program with
  | none =>
      simp [hRuntime] at hRun
  | some runtime =>
      have hResult : runContract runtime fuel state = result := by
        simpa [hRuntime] using hRun
      exact ⟨runtime, rfl, hResult⟩

theorem sourceRunWithCodeImage?_checked {fuel : Nat} {program : Program}
    {codeImage : ByteArray} {state : State}
    {result : Except Exception ReferenceResult}
    (hRun :
      sourceRunWithCodeImage? fuel program codeImage state = some result) :
    ∃ runtime : Runtime,
      Runtime.ofCheckedProgram? program = some runtime ∧
        runContract (Runtime.withCodeImage runtime codeImage) fuel state =
          result := by
  unfold sourceRunWithCodeImage? at hRun
  cases hRuntime : Runtime.ofCheckedProgram? program with
  | none =>
      simp [hRuntime] at hRun
  | some runtime =>
      have hResult :
          runContract (Runtime.withCodeImage runtime codeImage) fuel state =
            result := by
        simpa [hRuntime] using hRun
      exact ⟨runtime, rfl, hResult⟩

end Program

theorem evalValues_datasize {runtime : Runtime} {fuel : Nat}
    {state : State} {name : Name} {value : Literal}
    (hLookup : layoutSize? runtime name = some value) :
    evalValues (fuel + 1) runtime (.datasize name) state =
      .ok (state, [value]) := by
  have hLookup' : Objects.ObjectLayout.size? runtime.layout name = some value := by
    simpa [layoutSize?] using hLookup
  simp [evalValues, layoutSize?, hLookup']

theorem evalValues_dataoffset {runtime : Runtime} {fuel : Nat}
    {state : State} {name : Name} {value : Literal}
    (hLookup : layoutOffset? runtime name = some value) :
    evalValues (fuel + 1) runtime (.dataoffset name) state =
      .ok (state, [value]) := by
  have hLookup' : Objects.ObjectLayout.offset? runtime.layout name = some value := by
    simpa [layoutOffset?] using hLookup
  simp [evalValues, layoutOffset?, hLookup']

theorem evalValues_datacopy {runtime : Runtime} {fuel : Nat}
    {state : State} {dst offset size : Expr}
    {stateAfterArgs : State} {args : List Literal}
    (hArgs :
      reverseResult
        (evalArgs fuel runtime [dst, offset, size].reverse state) =
          .ok (stateAfterArgs, args)) :
    evalValues (fuel + 1) runtime (.datacopy dst offset size) state =
      EvmYul.Yul.primCall fuel stateAfterArgs
        ((.Env .CODECOPY : EvmYul.Operation .Yul)) args := by
  have hArgs' :
      reverseResult (evalArgs fuel runtime [size, offset, dst] state) =
        .ok (stateAfterArgs, args) := by
    simpa using hArgs
  simp [evalValues, hArgs']

end Source
end ObjectModel
end Yul
end EvmCompiler
