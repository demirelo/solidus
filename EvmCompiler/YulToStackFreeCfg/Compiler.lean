import EvmCompiler.StackFreeCfg.Accepted
import EvmCompiler.Yul.Syntax

namespace EvmCompiler
namespace YulToStackFreeCfg

abbrev Name := StackFreeCfg.Name
abbrev Word := StackFreeCfg.Word
abbrev AstExpr := EvmCompiler.Yul.AstExpr
abbrev AstStmt := EvmCompiler.Yul.AstStmt
abbrev AstFunctionDefinition := EvmCompiler.Yul.AstFunctionDefinition
abbrev AstContract := EvmCompiler.Yul.AstContract

namespace Prim

def toAssembly? : EvmYul.Operation .Yul → Option Assembly.PrimOp
  | .StopArith .STOP => none
  | .StopArith .ADD => some .add
  | .StopArith .MUL => some .mul
  | .StopArith .SUB => some .sub
  | .StopArith .DIV => some .div
  | .StopArith .SDIV => some .sdiv
  | .StopArith .MOD => some .mod
  | .StopArith .SMOD => some .smod
  | .StopArith .ADDMOD => some .addmod
  | .StopArith .MULMOD => some .mulmod
  | .StopArith .EXP => some .exp
  | .StopArith .SIGNEXTEND => some .signextend
  | .CompBit .LT => some .lt
  | .CompBit .GT => some .gt
  | .CompBit .SLT => some .slt
  | .CompBit .SGT => some .sgt
  | .CompBit .EQ => some .eq
  | .CompBit .ISZERO => some .iszero
  | .CompBit .AND => some .and
  | .CompBit .OR => some .or
  | .CompBit .XOR => some .xor
  | .CompBit .NOT => some .not
  | .CompBit .BYTE => some .byte
  | .CompBit .SHL => some .shl
  | .CompBit .SHR => some .shr
  | .CompBit .SAR => some .sar
  | .Keccak .KECCAK256 => some .keccak256
  | .Env .ADDRESS => some .address
  | .Env .BALANCE => some .balance
  | .Env .ORIGIN => some .origin
  | .Env .CALLER => some .caller
  | .Env .CALLVALUE => some .callvalue
  | .Env .CALLDATALOAD => some .calldataload
  | .Env .CALLDATASIZE => some .calldatasize
  | .Env .CALLDATACOPY => some .calldatacopy
  | .Env .CODESIZE => some .codesize
  | .Env .CODECOPY => some .codecopy
  | .Env .GASPRICE => some .gasprice
  | .Env .EXTCODESIZE => some .extcodesize
  | .Env .EXTCODECOPY => some .extcodecopy
  | .Env .RETURNDATASIZE => some .returndatasize
  | .Env .RETURNDATACOPY => some .returndatacopy
  | .Env .EXTCODEHASH => some .extcodehash
  | .Block .BLOCKHASH => some .blockhash
  | .Block .COINBASE => some .coinbase
  | .Block .TIMESTAMP => some .timestamp
  | .Block .NUMBER => some .number
  | .Block .PREVRANDAO => some .prevrandao
  | .Block .GASLIMIT => some .gaslimit
  | .Block .CHAINID => some .chainid
  | .Block .SELFBALANCE => some .selfbalance
  | .Block .BASEFEE => some .basefee
  | .Block .BLOBHASH => some .blobhash
  | .Block .BLOBBASEFEE => some .blobbasefee
  | .StackMemFlow .POP => some .pop
  | .StackMemFlow .MLOAD => some .mload
  | .StackMemFlow .MSTORE => some .mstore
  | .StackMemFlow .SLOAD => some .sload
  | .StackMemFlow .SSTORE => some .sstore
  | .StackMemFlow .MSTORE8 => some .mstore8
  | .StackMemFlow .MSIZE => some .msize
  | .StackMemFlow .GAS => some .gas
  | .StackMemFlow .TLOAD => some .tload
  | .StackMemFlow .TSTORE => some .tstore
  | .StackMemFlow .MCOPY => some .mcopy
  | .Log .LOG0 => some .log0
  | .Log .LOG1 => some .log1
  | .Log .LOG2 => some .log2
  | .Log .LOG3 => some .log3
  | .Log .LOG4 => some .log4
  | .System .CREATE => some .create
  | .System .CALL => some .call
  | .System .CALLCODE => some .callcode
  | .System .RETURN => none
  | .System .DELEGATECALL => some .delegatecall
  | .System .CREATE2 => some .create2
  | .System .STATICCALL => some .staticcall
  | .System .REVERT => none
  | .System .INVALID => some .invalid
  | .System .SELFDESTRUCT => none

def terminal? : EvmYul.Operation .Yul → Option Assembly.HaltKind
  | .StopArith .STOP => some .stop
  | .System .RETURN => some .return
  | .System .REVERT => some .revert
  | .System .SELFDESTRUCT => some .selfdestruct
  | _ => none

end Prim

structure ObjectLayout where
  dataSize? : Name → Option Word := fun _ => none
  dataOffset? : Name → Option Word := fun _ => none

namespace Fresh

structure State where
  used : List Name := []
  next : Nat := 0

def initial (used : List Name) : State :=
  { used, next := 0 }

def tempPrefix : String :=
  "__sf_cfg_tmp_"

def tempName (idx : Nat) : Name :=
  tempPrefix ++ toString idx

def fresh? (state : State) : Option (Name × State) :=
  let rec go (idx remaining : Nat) : Option (Name × State) :=
    match remaining with
    | 0 => none
    | remaining' + 1 =>
        let candidate := tempName idx
        if state.used.contains candidate then
          go (idx + 1) remaining'
        else
          some (candidate,
            { used := candidate :: state.used, next := idx + 1 })
  go state.next (state.used.length + state.next + 1)

end Fresh

structure Env where
  signatures : List StackFreeCfg.Signature.T
  objectLayout : ObjectLayout := {}

namespace Env

def findSignature? (env : Env) (name : Name) : Option StackFreeCfg.Signature.T :=
  StackFreeCfg.Signature.find? env.signatures name

end Env

def identName (name : EvmYul.Identifier) : Name :=
  name

def identNames (names : List EvmYul.Identifier) : List Name :=
  names.map identName

namespace ObjectBuiltin

def objectName? : AstExpr → Option Name
  | .Var name => some (identName name)
  | _ => none

def lowerExpr? (layout : ObjectLayout) (name : Name) (args : List AstExpr) :
    Option StackFreeCfg.Expr :=
  match name, args with
  | "datasize", [arg] => do
      let objectName ← objectName? arg
      let value ← layout.dataSize? objectName
      some (.literal value)
  | "dataoffset", [arg] => do
      let objectName ← objectName? arg
      let value ← layout.dataOffset? objectName
      some (.literal value)
  | _, _ => none

end ObjectBuiltin

namespace Names

mutual
  def expr : AstExpr → List Name
    | .Lit _value => []
    | .Var name => [identName name]
    | .Call (.inl _prim) args => exprList args
    | .Call (.inr functionName) args => functionName :: exprList args

  def exprList : List AstExpr → List Name
    | [] => []
    | head :: rest => expr head ++ exprList rest

  def stmt : AstStmt → List Name
    | .Block stmts => stmtList stmts
    | .Let vars none => identNames vars
    | .Let vars (some value) => identNames vars ++ expr value
    | .Assign vars value => identNames vars ++ expr value
    | .ExprStmtCall value => expr value
    | .Switch scrutinee cases defaultBody =>
        expr scrutinee ++ casesList cases ++ stmtList defaultBody
    | .For cond post body =>
        expr cond ++ stmtList post ++ stmtList body
    | .If cond body =>
        expr cond ++ stmtList body
    | .Continue | .Break | .Leave => []

  def stmtList : List AstStmt → List Name
    | [] => []
    | head :: rest => stmt head ++ stmtList rest

  def casesList : List (Word × List AstStmt) → List Name
    | [] => []
    | (_value, body) :: rest => stmtList body ++ casesList rest
end

def functionDefinition : AstFunctionDefinition → List Name
  | .Def params returns body =>
      identNames params ++ identNames returns ++ stmtList body

end Names

mutual
  def lowerExpr? (env : Env) (state : Fresh.State) :
      AstExpr → Option (List StackFreeCfg.Stmt × StackFreeCfg.Expr × Fresh.State)
    | .Lit value => some ([], .literal value, state)
    | .Var name => some ([], .var (identName name), state)
    | .Call (.inl prim) args => do
        let op ← Prim.toAssembly? prim
        let (pre, lowerArgs, state') ← lowerExprArgs? env state args
        some (pre, .prim op lowerArgs, state')
    | .Call (.inr functionName) args =>
        match ObjectBuiltin.lowerExpr? env.objectLayout functionName args with
        | some expr => some ([], expr, state)
        | none => do
            let sig ← env.findSignature? functionName
            if sig.returns = 1 then
              let (pre, lowerArgs, state') ← lowerExprArgs? env state args
              let (tmp, state'') ← Fresh.fresh? state'
              some
                (pre ++ [.decl [tmp] none,
                  .call [tmp] functionName lowerArgs],
                  .var tmp, state'')
            else
              none

  def lowerExprArgs? (env : Env) :
      Fresh.State → List AstExpr →
        Option (List StackFreeCfg.Stmt × List StackFreeCfg.Expr × Fresh.State)
    | state, [] => some ([], [], state)
    | state, arg :: rest => do
        let (preRest, lowerRest, state') ← lowerExprArgs? env state rest
        let (preHead, lowerHead, state'') ← lowerExpr? env state' arg
        some (preRest ++ preHead, lowerHead :: lowerRest, state'')

  def lowerStmt? (env : Env) (state : Fresh.State) :
      AstStmt → Option (List StackFreeCfg.Stmt × Fresh.State)
    | .Block stmts => do
        let (block, state') ← lowerBlock? env state stmts
        some ([.block block], state')
    | .Let vars none =>
        some ([.decl (identNames vars) none], state)
    | .Let vars (some (.Call (.inr functionName) args)) =>
        match ObjectBuiltin.lowerExpr? env.objectLayout functionName args with
        | some expr =>
            some ([.decl (identNames vars) (some expr)], state)
        | none => do
            let (pre, lowerArgs, state') ← lowerExprArgs? env state args
            some
              (pre ++ [.decl (identNames vars) none,
                .call (identNames vars) functionName lowerArgs],
                state')
    | .Let vars (some expr) => do
        let (pre, lowerExpr, state') ← lowerExpr? env state expr
        some (pre ++ [.decl (identNames vars) (some lowerExpr)], state')
    | .Assign vars (.Call (.inr functionName) args) =>
        match ObjectBuiltin.lowerExpr? env.objectLayout functionName args with
        | some expr =>
            some ([.assign (identNames vars) expr], state)
        | none => do
            let (pre, lowerArgs, state') ← lowerExprArgs? env state args
            some (pre ++ [.call (identNames vars) functionName lowerArgs], state')
    | .Assign vars expr => do
        let (pre, lowerExpr, state') ← lowerExpr? env state expr
        some (pre ++ [.assign (identNames vars) lowerExpr], state')
    | .ExprStmtCall (.Call (.inl prim) args) =>
        match Prim.terminal? prim with
        | some kind => do
            let (pre, lowerArgs, state') ← lowerExprArgs? env state args
            some (pre ++ [.terminal kind lowerArgs], state')
        | none => do
            let (pre, lowerExpr, state') ← lowerExpr? env state
              (.Call (.inl prim) args)
            some (pre ++ [.expr lowerExpr], state')
    | .ExprStmtCall (.Call (.inr functionName) args) =>
        if functionName = "datacopy" then
          match args with
          | [dst, objectArg, size] => do
              let objectName ← ObjectBuiltin.objectName? objectArg
              let offset ← env.objectLayout.dataOffset? objectName
              let (preSize, sizeExpr, state') ← lowerExpr? env state size
              let (preDst, dstExpr, state'') ← lowerExpr? env state' dst
              some
                (preSize ++ preDst ++
                  [.expr (.prim .codecopy
                    [dstExpr, .literal offset, sizeExpr])],
                  state'')
          | _ => none
        else do
          let (pre, lowerArgs, state') ← lowerExprArgs? env state args
          some (pre ++ [.call [] functionName lowerArgs], state')
    | .ExprStmtCall _ => none
    | .Switch scrutinee cases defaultBody => do
        let (pre, lowerScrutinee, state') ← lowerExpr? env state scrutinee
        let (lowerCases, state'') ← lowerCases? env state' cases
        let (lowerDefault, state''') ←
          if defaultBody.isEmpty then
            some (none, state'')
          else do
            let (block, stateDefault) ←
              lowerBlock? env state'' defaultBody
            some (some block, stateDefault)
        some
          (pre ++ [.switch lowerScrutinee lowerCases lowerDefault],
            state''')
    | .For cond post body => do
        let (preCond, lowerCond, state') ← lowerExpr? env state cond
        let (postBlock, state'') ← lowerBlock? env state' post
        let (bodyBlock, state''') ← lowerBlock? env state'' body
        let breakIfFalse : StackFreeCfg.Stmt :=
          .if_ (.prim .iszero [lowerCond]) { stmts := [.brk] }
        let initBlock : StackFreeCfg.Block := { stmts := [] }
        let guardedBody : StackFreeCfg.Block :=
          { stmts := preCond ++ [breakIfFalse] ++ bodyBlock.stmts }
        some ([.for_ initBlock (.literal (EvmYul.UInt256.ofNat 1)) postBlock
          guardedBody], state''')
    | .If cond body => do
        let (pre, lowerCond, state') ← lowerExpr? env state cond
        let (bodyBlock, state'') ← lowerBlock? env state' body
        some (pre ++ [.if_ lowerCond bodyBlock], state'')
    | .Continue => some ([.cont], state)
    | .Break => some ([.brk], state)
    | .Leave => some ([.leave], state)

  def lowerStmtList? (env : Env) :
      Fresh.State → List AstStmt → Option (List StackFreeCfg.Stmt × Fresh.State)
    | state, [] => some ([], state)
    | state, stmt :: rest => do
        let (head, state') ← lowerStmt? env state stmt
        let (tail, state'') ← lowerStmtList? env state' rest
        some (head ++ tail, state'')

  def lowerBlock? (env : Env) (state : Fresh.State) (stmts : List AstStmt) :
      Option (StackFreeCfg.Block × Fresh.State) := do
    let (lower, state') ← lowerStmtList? env state stmts
    some ({ stmts := lower }, state')

  def lowerCases? (env : Env) :
      Fresh.State → List (Word × List AstStmt) →
        Option (List (Word × StackFreeCfg.Block) × Fresh.State)
    | state, [] => some ([], state)
    | state, (value, body) :: rest => do
        let (lowerBody, state') ← lowerBlock? env state body
        let (lowerRest, state'') ← lowerCases? env state' rest
        some ((value, lowerBody) :: lowerRest, state'')
end

namespace Expr
def lower? := lowerExpr?
def lowerArgs? := lowerExprArgs?
end Expr

namespace Stmt
def lower? := lowerStmt?
end Stmt

namespace StmtList
def lower? := lowerStmtList?
def lowerBlock? := YulToStackFreeCfg.lowerBlock?
end StmtList

namespace Cases
def lower? := lowerCases?
end Cases

namespace FunctionDefinition

def lower? (env : Env) (state : Fresh.State) (name : Name) :
    AstFunctionDefinition → Option (StackFreeCfg.Proc × Fresh.State)
  | .Def params returns body => do
      let (lowerBody, state') ← StmtList.lowerBlock? env state body
      some
        ({ name := name
           params := identNames params
           returns := identNames returns
           body := lowerBody },
          state')

end FunctionDefinition

namespace Contract

noncomputable def functionEntries (contract : AstContract) :
    List (Name × AstFunctionDefinition) :=
  contract.functions.keys.toList.filterMap fun name =>
    match contract.functions.lookup name with
    | some fn => some (name, fn)
    | none => none

def signatures (entries : List (Name × AstFunctionDefinition)) :
    List StackFreeCfg.Signature.T :=
  entries.map fun (name, fn) =>
    { name := name
      params := fn.params.length
      returns := fn.rets.length }

def namesInFunction : AstFunctionDefinition → List Name
  | fn => Names.functionDefinition fn

def usedNames (dispatcher : AstStmt)
    (entries : List (Name × AstFunctionDefinition)) : List Name :=
  Names.stmt dispatcher ++
    entries.flatMap fun (name, fn) => name :: namesInFunction fn

def lowerFunctions? (env : Env) :
    Fresh.State → List (Name × AstFunctionDefinition) →
      Option (List StackFreeCfg.Proc × Fresh.State)
  | state, [] => some ([], state)
  | state, (name, fn) :: rest => do
      let (proc, state') ← FunctionDefinition.lower? env state name fn
      let (procs, state'') ← lowerFunctions? env state' rest
      some (proc :: procs, state'')

noncomputable def lower? (layout : ObjectLayout) (contract : AstContract) :
    Option StackFreeCfg.Program := do
  let entries := functionEntries contract
  let env : Env := { signatures := signatures entries, objectLayout := layout }
  let initial := Fresh.initial (usedNames contract.dispatcher entries)
  let (body, state) ← Stmt.lower? env initial contract.dispatcher
  let (procs, _state') ← lowerFunctions? env state entries
  some { procs := procs, body := { stmts := body } }

end Contract

namespace Program

noncomputable def lower? (layout : ObjectLayout) (program : EvmCompiler.Yul.Program) :
    Option StackFreeCfg.Program :=
  Contract.lower? layout program.contract

end Program

end YulToStackFreeCfg
end EvmCompiler
