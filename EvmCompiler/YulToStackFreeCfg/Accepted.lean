import EvmCompiler.YulToStackFreeCfg.Compiler

namespace EvmCompiler
namespace YulToStackFreeCfg

/-!
Executable coverage checker for the Yul-to-StackFreeCfg lowering pass.

This is intentionally a source-surface checker, not a preservation proof. It
records the Yul AST shapes that this pass knows how to lower before the later
theorem relates imported Yul execution to `StackFreeCfg` execution.
-/

namespace Coverage

def primArity? (prim : EvmYul.Operation .Yul) (argc : Nat) :
    Option Nat :=
  match Prim.toAssembly? prim with
  | none => none
  | some op =>
      match StackFreeCfg.Prim.sourceArity? op with
      | some (inputArity, outputArity) =>
          if inputArity = argc then some outputArity else none
      | none => none

def primExpr? (prim : EvmYul.Operation .Yul) (argc : Nat) : Bool :=
  primArity? prim argc |>.isSome

def primStmt? (prim : EvmYul.Operation .Yul) (argc : Nat) : Bool :=
  match Prim.terminal? prim with
  | some kind => argc = kind.argCount
  | none =>
      if Prim.invalid? prim then
        argc = 0
      else
        match Prim.toAssembly? prim with
        | none => false
        | some op =>
            match StackFreeCfg.Prim.sourceArity? op with
            | some (inputArity, outputArity) =>
                inputArity = argc && outputArity = 0
            | none => false

def objectExpr? (layout : ObjectLayout) (name : Name)
    (args : List AstExpr) : Bool :=
  (ObjectBuiltin.lowerExpr? layout name args).isSome

mutual
  def exprArity? (env : Env) : AstExpr → Option Nat
    | .Lit _value => some 1
    | .Var _name => some 1
    | .Call (.inl prim) args =>
        if exprList? env args then
          primArity? prim args.length
        else
          none
    | .Call (.inr functionName) args =>
        if functionName = "memoryguard" then
          if args.length = 1 && exprList? env args then some 1 else none
        else if objectExpr? env.objectLayout functionName args then
          some 1
        else
          match env.findSignature? functionName with
          | some sig =>
              if sig.params = args.length && exprList? env args then
                some sig.returns
              else
                none
          | none => none

  def expr? (env : Env) (expr : AstExpr) : Bool :=
    (exprArity? env expr).isSome

  def exprArityIs? (env : Env) (expr : AstExpr) (arity : Nat) : Bool :=
    decide (exprArity? env expr = some arity)

  def exprList? (env : Env) : List AstExpr → Bool
    | [] => true
    | expr :: rest => exprArityIs? env expr 1 && exprList? env rest

  def callStmt? (env : Env) (targets : List Name) (functionName : Name)
      (args : List AstExpr) : Bool :=
    match env.findSignature? functionName with
    | some sig =>
        targets.length = sig.returns && args.length = sig.params &&
          exprList? env args
    | none => false

  def stmt? (env : Env) : AstStmt → Bool
    | .Block stmts => stmtList? env stmts
    | .Let _vars none => true
    | .Let vars (some (.Call (.inr functionName) args)) =>
        if objectExpr? env.objectLayout functionName args then
          vars.length = 1
        else
          callStmt? env (identNames vars) functionName args
    | .Let vars (some expr) => exprArityIs? env expr vars.length
    | .Assign vars (.Call (.inr functionName) args) =>
        if objectExpr? env.objectLayout functionName args then
          vars.length = 1
        else
          callStmt? env (identNames vars) functionName args
    | .Assign vars expr => exprArityIs? env expr vars.length
    | .ExprStmtCall (.Call (.inl prim) args) =>
        exprList? env args && primStmt? prim args.length
    | .ExprStmtCall (.Call (.inr functionName) args) =>
        if functionName = "datacopy" then
          args.length = 3 && exprList? env args
        else
          callStmt? env [] functionName args
    | .ExprStmtCall _ => false
    | .Switch scrutinee cases defaultBody =>
        exprArityIs? env scrutinee 1 && cases? env cases &&
          stmtList? env defaultBody
    | .For cond post body =>
        exprArityIs? env cond 1 && stmtList? env post && stmtList? env body
    | .If cond body =>
        exprArityIs? env cond 1 && stmtList? env body
    | .Continue | .Break | .Leave => true

  def stmtList? (env : Env) : List AstStmt → Bool
    | [] => true
    | stmt :: rest => stmt? env stmt && stmtList? env rest

  def cases? (env : Env) : List (Word × List AstStmt) → Bool
    | [] => true
    | (_value, body) :: rest => stmtList? env body && cases? env rest
end

def functionDefinition? (env : Env) :
    AstFunctionDefinition → Bool
  | .Def _params _returns body => stmtList? env body

def functions? (env : Env) :
    List (Name × AstFunctionDefinition) → Bool
  | [] => true
  | (_name, fn) :: rest =>
      functionDefinition? env fn && functions? env rest

noncomputable def contract? (layout : ObjectLayout)
    (contract : AstContract) : Bool :=
  let entries := Contract.functionEntries contract
  let env : Env :=
    { signatures := Contract.signatures entries, objectLayout := layout }
  stmt? env contract.dispatcher && functions? env entries

noncomputable def program? (layout : ObjectLayout)
    (program : EvmCompiler.Yul.Program) : Bool :=
  contract? layout program.contract

end Coverage

namespace SourceWF

def containsAll? (env names : List Name) : Bool :=
  names.all (fun name => decide (name ∈ env))

def disjoint? (names env : List Name) : Bool :=
  names.all (fun name => decide (name ∉ env))

def nonempty? (names : List Name) : Bool :=
  !names.isEmpty

def canDeclare? (env names : List Name) : Bool :=
  nonempty? names && decide names.Nodup && disjoint? names env

def canAssign? (env names : List Name) : Bool :=
  nonempty? names && decide names.Nodup && containsAll? env names

def extend (env names : List Name) : List Name :=
  names ++ env

def reservedFunctionName? : Name → Bool
  | "datasize" | "dataoffset" | "datacopy"
  | "linkersymbol" | "loadimmutable" | "setimmutable"
  | "memoryguard" => true
  | name => name.startsWith "verbatim"

def functionNamesAccepted? (names : List Name) : Bool :=
  decide names.Nodup && names.all (fun name => !reservedFunctionName? name)

def caseValues : List (Word × List AstStmt) → List Word
  | [] => []
  | (value, _body) :: rest => value :: caseValues rest

mutual
  def exprArity? (env : Env) (scope : List Name) :
      AstExpr → Option Nat
    | .Lit _value => some 1
    | .Var name =>
        if identName name ∈ scope then some 1 else none
    | .Call (.inl prim) args =>
        if exprList? env scope args then
          Coverage.primArity? prim args.length
        else
          none
    | .Call (.inr functionName) args =>
        if functionName = "memoryguard" then
          if args.length = 1 && exprList? env scope args then some 1 else none
        else if Coverage.objectExpr? env.objectLayout functionName args then
          some 1
        else
          match env.findSignature? functionName with
          | some sig =>
              if sig.params = args.length && exprList? env scope args then
                some sig.returns
              else
                none
          | none => none

  def exprArityIs? (env : Env) (scope : List Name)
      (expr : AstExpr) (arity : Nat) : Bool :=
    decide (exprArity? env scope expr = some arity)

  def exprList? (env : Env) (scope : List Name) : List AstExpr → Bool
    | [] => true
    | expr :: rest =>
        exprArityIs? env scope expr 1 && exprList? env scope rest

  def callStmt? (env : Env) (scope : List Name) (targets : List Name)
      (functionName : Name) (args : List AstExpr) : Bool :=
    match env.findSignature? functionName with
    | some sig =>
        targets.length = sig.returns && args.length = sig.params &&
          exprList? env scope args
    | none => false

  def stmtOutScope? (scope : List Name) : AstStmt → Option (List Name)
    | .Let vars _value? =>
        let names := identNames vars
        if canDeclare? scope names then
          some (extend scope names)
        else
          none
    | _ => some scope

  def stmt? (env : Env) (canBreak canContinue canLeave : Bool)
      (scope : List Name) : AstStmt → Bool
    | .Block stmts =>
        stmtList? env canBreak canContinue canLeave scope stmts
    | .Let vars none =>
        canDeclare? scope (identNames vars)
    | .Let vars (some (.Call (.inr functionName) args)) =>
        let names := identNames vars
        canDeclare? scope names &&
          if Coverage.objectExpr? env.objectLayout functionName args then
            names.length = 1
          else
            callStmt? env scope names functionName args
    | .Let vars (some expr) =>
        let names := identNames vars
        canDeclare? scope names &&
          exprArityIs? env scope expr names.length
    | .Assign vars (.Call (.inr functionName) args) =>
        let names := identNames vars
        canAssign? scope names &&
          if Coverage.objectExpr? env.objectLayout functionName args then
            names.length = 1
          else
            callStmt? env scope names functionName args
    | .Assign vars expr =>
        let names := identNames vars
        canAssign? scope names &&
          exprArityIs? env scope expr names.length
    | .ExprStmtCall (.Call (.inl prim) args) =>
        exprList? env scope args && Coverage.primStmt? prim args.length
    | .ExprStmtCall (.Call (.inr functionName) args) =>
        if functionName = "datacopy" then
          args.length = 3 && exprList? env scope args
        else
          callStmt? env scope [] functionName args
    | .ExprStmtCall _ => false
    | .Switch scrutinee cases defaultBody =>
        exprArityIs? env scope scrutinee 1 &&
          decide (caseValues cases).Nodup &&
          cases? env canBreak canContinue canLeave scope cases &&
          stmtList? env canBreak canContinue canLeave scope defaultBody
    | .For cond post body =>
        exprArityIs? env scope cond 1 &&
          stmtList? env false false canLeave scope post &&
          stmtList? env true true canLeave scope body
    | .If cond body =>
        exprArityIs? env scope cond 1 &&
          stmtList? env canBreak canContinue canLeave scope body
    | .Continue => canContinue
    | .Break => canBreak
    | .Leave => canLeave

  def stmtList? (env : Env) (canBreak canContinue canLeave : Bool)
      (scope : List Name) : List AstStmt → Bool
    | [] => true
    | stmt :: rest =>
        stmt? env canBreak canContinue canLeave scope stmt &&
          match stmtOutScope? scope stmt with
          | some scope' =>
              stmtList? env canBreak canContinue canLeave scope' rest
          | none => false

  def cases? (env : Env) (canBreak canContinue canLeave : Bool)
      (scope : List Name) : List (Word × List AstStmt) → Bool
    | [] => true
    | (_value, body) :: rest =>
        stmtList? env canBreak canContinue canLeave scope body &&
          cases? env canBreak canContinue canLeave scope rest
end

def functionDefinition? (env : Env) :
    AstFunctionDefinition → Bool
  | .Def params returns body =>
      let names := identNames returns ++ identNames params
      decide names.Nodup &&
        stmtList? env false false true names body

def functions? (env : Env) :
    List (Name × AstFunctionDefinition) → Bool
  | [] => true
  | (_name, fn) :: rest =>
      functionDefinition? env fn && functions? env rest

noncomputable def contract? (layout : ObjectLayout)
    (contract : AstContract) : Bool :=
  let entries := Contract.functionEntries contract
  let env : Env :=
    { signatures := Contract.signatures entries, objectLayout := layout }
  functionNamesAccepted? (entries.map Prod.fst) &&
    stmt? env false false false [] contract.dispatcher &&
    functions? env entries

noncomputable def program? (layout : ObjectLayout)
    (program : EvmCompiler.Yul.Program) : Bool :=
  contract? layout program.contract

end SourceWF

namespace Contract

noncomputable def lowerAccepted? (layout : ObjectLayout)
    (contract : AstContract) : Option StackFreeCfg.Program := do
  if Coverage.contract? layout contract && SourceWF.contract? layout contract then
    let program ← lower? layout contract
    if StackFreeCfg.Program.accepted? program then
      some program
    else
      none
  else
    none

end Contract

namespace Program

noncomputable def lowerAccepted? (layout : ObjectLayout)
    (program : EvmCompiler.Yul.Program) : Option StackFreeCfg.Program :=
  Contract.lowerAccepted? layout program.contract

end Program

end YulToStackFreeCfg
end EvmCompiler
