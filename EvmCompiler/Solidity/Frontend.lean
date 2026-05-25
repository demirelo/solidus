import EvmCompiler.Yul.Compiler
import EvmCompiler.Objects.Layout
import EvmCompiler.Assembly.ByteEncoding

namespace EvmCompiler
namespace Solidity
namespace Frontend

abbrev Name := String
abbrev Word := EvmYul.UInt256
abbrev AstExpr := EvmYul.Yul.Ast.Expr
abbrev AstStmt := EvmYul.Yul.Ast.Stmt
abbrev AstFunctionDefinition := EvmYul.Yul.Ast.FunctionDefinition
abbrev AstContract := EvmYul.Yul.Ast.YulContract

/--
The kind of Yul call as it appears in solc's Yul AST.

The existing compiler backend can lower primitive EVM/Yul operations and user
functions through `EvmYul.Yul.Ast.Expr.Call`. Object and dialect builtins are
kept here so the front-end import remains structural even before the backend
has object/data-section support.
-/
inductive CallKind where
  | primitive
  | user
  | objectBuiltin
  | dialectBuiltin
  deriving BEq, DecidableEq, Inhabited, Repr

namespace CallKind

def backendRepresentable : CallKind → Bool
  | .primitive => true
  | .user => true
  | .objectBuiltin => false
  | .dialectBuiltin => false

end CallKind

inductive Expr where
  | lit (value : Word)
  | stringLit (value : String)
  | var (name : Name)
  | call (kind : CallKind) (callee : Name) (args : List Expr)
  deriving Inhabited, Repr

inductive Stmt where
  | block (stmts : List Stmt)
  | letDecl (names : List Name) (value : Option Expr)
  | assign (names : List Name) (value : Expr)
  | exprStmt (expr : Expr)
  | switch (scrutinee : Expr) (cases : List (Word × List Stmt))
      (default : List Stmt)
  | forLoop (condition : Expr) (post : List Stmt) (body : List Stmt)
  | ifThen (condition : Expr) (body : List Stmt)
  | break
  | continue
  | leave
  deriving Inhabited, Repr

structure FunctionDef where
  params : List Name
  returns : List Name
  body : List Stmt
  deriving Inhabited, Repr

structure DataSection where
  name? : Option Name
  bytes : List UInt8
  deriving Inhabited, Repr

inductive ObjectItemRef where
  | data (index : Nat)
  | object (index : Nat)
  deriving BEq, DecidableEq, Inhabited, Repr

structure Object where
  name : Name
  dispatcher : List Stmt
  functions : List (Name × FunctionDef)
  data : List DataSection
  objects : List Object
  items : List ObjectItemRef
  deriving Inhabited, Repr

structure Program where
  source : String
  contract : String
  object : Object
  deriving Inhabited, Repr

namespace StringLiteral

def maxBytes : Nat :=
  32

def packBytes (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0

def word? (value : String) : Option Word :=
  let bytes := value.toUTF8.toList
  if bytes.length <= maxBytes then
    some
      (EvmYul.UInt256.ofNat
        (packBytes bytes * 256 ^ (maxBytes - bytes.length)))
  else
    none

end StringLiteral

/--
A visible layout witness for Yul object/data pseudo-builtins.

Resolving through this structure only replaces `datasize("name")` and
`dataoffset("name")` with literals before entering the current backend
`Yul.Program`.  The executable `bytecodeImageUnchecked?` path below computes
its own object/data layout and appends payload bytes; this witness remains for
the older code-only conversion path and for checked layout theorem work.
-/
structure ObjectLayout.Entry where
  name : Name
  offset : Word
  size : Word
  deriving Inhabited, Repr

structure ObjectLayout where
  entries : List ObjectLayout.Entry
  deriving Inhabited, Repr

namespace ObjectLayout

def findEntry? (layout : ObjectLayout) (name : Name) :
    Option ObjectLayout.Entry :=
  layout.entries.find? fun entry => entry.name == name

def offset? (layout : ObjectLayout) (name : Name) : Option Word := do
  let entry ← layout.findEntry? name
  some entry.offset

def size? (layout : ObjectLayout) (name : Name) : Option Word := do
  let entry ← layout.findEntry? name
  some entry.size

end ObjectLayout

namespace DataSection

def toObjects (dataSection : DataSection) : Objects.DataSection :=
  { name? := dataSection.name?
    bytes := dataSection.bytes }

namespace List

def toObjects : List DataSection → List Objects.DataSection :=
  List.map DataSection.toObjects

end List

def size (dataSection : DataSection) : Word :=
  EvmYul.UInt256.ofNat dataSection.bytes.length

def sizeEntry? (dataSection : DataSection) : Option (Name × Word) :=
  match dataSection.name? with
  | some name => some (name, dataSection.size)
  | none => none

def sizeEntries : List DataSection → List (Name × Word)
  | [] => []
  | dataSection :: rest =>
      match dataSection.sizeEntry? with
      | some entry => entry :: sizeEntries rest
      | none => sizeEntries rest

def offsetEntryFromNat? (base : Nat) (dataSection : DataSection) :
    Option (Name × Word) :=
  match dataSection.name? with
  | some name => some (name, EvmYul.UInt256.ofNat base)
  | none => none

def offsetEntriesFromNat : Nat → List DataSection → List (Name × Word)
  | _, [] => []
  | base, dataSection :: rest =>
      let tail :=
        offsetEntriesFromNat (base + dataSection.bytes.length) rest
      match dataSection.offsetEntryFromNat? base with
      | some entry => entry :: tail
      | none => tail

namespace List

def payloadBytes : List DataSection → List UInt8
  | [] => []
  | sect :: rest => sect.bytes ++ payloadBytes rest

theorem toObjects_payloadBytes (sections : List DataSection) :
    Objects.DataSection.Sections.payloadBytes (toObjects sections) =
      payloadBytes sections := by
  induction sections with
  | nil =>
      rfl
  | cons sect rest ih =>
      cases sect with
      | mk name? bytes =>
          have hRest :
              Objects.DataSection.Sections.payloadBytes
                  (List.map DataSection.toObjects rest) =
                payloadBytes rest := by
            simpa [toObjects] using ih
          simp [toObjects, payloadBytes, DataSection.toObjects,
            Objects.DataSection.Sections.payloadBytes, hRest]

theorem toObjects_namedSizeEntries (sections : List DataSection) :
    Objects.DataSection.Sections.namedSizeEntries (toObjects sections) =
      DataSection.sizeEntries sections := by
  induction sections with
  | nil =>
      rfl
  | cons sect rest ih =>
      cases sect with
      | mk name? bytes =>
          have hRest :
              Objects.DataSection.Sections.namedSizeEntries
                  (List.map DataSection.toObjects rest) =
                DataSection.sizeEntries rest := by
            simpa [toObjects] using ih
          cases name? <;>
            simp [toObjects, DataSection.toObjects,
              DataSection.sizeEntries, DataSection.sizeEntry?,
              DataSection.size, Objects.DataSection.Sections.namedSizeEntries,
              Objects.DataSection.namedSizeEntry?, Objects.DataSection.size,
              Objects.DataSection.byteLength, hRest]

theorem toObjects_namedOffsetEntriesFromNat
    (base : Nat) (sections : List DataSection) :
    Objects.DataSection.Sections.namedOffsetEntriesFromNat base
        (toObjects sections) =
      DataSection.offsetEntriesFromNat base sections := by
  induction sections generalizing base with
  | nil =>
      rfl
  | cons sect rest ih =>
      cases sect with
      | mk name? bytes =>
          have hRest :
              Objects.DataSection.Sections.namedOffsetEntriesFromNat
                  (base + bytes.length) (List.map DataSection.toObjects rest) =
                DataSection.offsetEntriesFromNat (base + bytes.length) rest := by
            simpa [toObjects] using ih (base + bytes.length)
          cases name? <;>
            simp [toObjects, DataSection.toObjects,
              DataSection.offsetEntriesFromNat,
              DataSection.offsetEntryFromNat?,
              Objects.DataSection.Sections.namedOffsetEntriesFromNat,
              Objects.DataSection.namedOffsetEntryFromNat?,
              Objects.DataSection.byteLength, hRest]

end List

end DataSection

structure ImmutableReference where
  start : Nat
  length : Nat
  deriving Inhabited, Repr

namespace ImmutableReference

def patchLength : Nat :=
  32

def isPatchable (reference : ImmutableReference) : Bool :=
  reference.length == patchLength

end ImmutableReference

mutual
  def Expr.loweringFuel : Expr → Nat
    | .lit _ => 1
    | .stringLit _ => 1
    | .var _ => 1
    | .call _ _ args => Expr.List.loweringFuel args + 1

  def Expr.List.loweringFuel : List Expr → Nat
    | [] => 1
    | expr :: rest =>
        Expr.loweringFuel expr + Expr.List.loweringFuel rest + 1
end

mutual
  def Stmt.loweringFuel : Stmt → Nat
    | .block stmts => Stmt.List.loweringFuel stmts + 1
    | .letDecl _ none => 1
    | .letDecl _ (some value) => Expr.loweringFuel value + 1
    | .assign _ value => Expr.loweringFuel value + 1
    | .exprStmt expr => Expr.loweringFuel expr + 1
    | .switch scrutinee cases default =>
        Expr.loweringFuel scrutinee +
          Stmt.CaseList.loweringFuel cases +
          Stmt.List.loweringFuel default + 1
    | .forLoop condition post body =>
        Expr.loweringFuel condition +
          Stmt.List.loweringFuel post +
          Stmt.List.loweringFuel body + 1
    | .ifThen condition body =>
        Expr.loweringFuel condition + Stmt.List.loweringFuel body + 1
    | .break => 1
    | .continue => 1
    | .leave => 1

  def Stmt.List.loweringFuel : List Stmt → Nat
    | [] => 1
    | stmt :: rest =>
        Stmt.loweringFuel stmt + Stmt.List.loweringFuel rest + 1

  def Stmt.CaseList.loweringFuel :
      List (Word × List Stmt) → Nat
    | [] => 1
    | (_value, body) :: rest =>
        Stmt.List.loweringFuel body + Stmt.CaseList.loweringFuel rest + 1
end

namespace FunctionDef

def loweringFuel (fn : FunctionDef) : Nat :=
  Stmt.List.loweringFuel fn.body + 1

namespace List

def loweringFuel : List (Name × FunctionDef) → Nat
  | [] => 1
  | (_name, fn) :: rest => fn.loweringFuel + loweringFuel rest + 1

end List
end FunctionDef

namespace Bytecode

def concat (chunks : List (List UInt8)) : List UInt8 :=
  chunks.foldr (· ++ ·) []

end Bytecode

/--
Resolution context for object pseudo-builtins at the Solidity front-end
boundary.

Offsets for named local data sections can be computed from typed byte payloads
once the object-layer base address is supplied.  Other offsets still come from
a visible layout witness, because they depend on final code/object placement.
Sizes for named local data sections are computed from the typed byte payloads
imported from solc, so `datasize("dataName")` no longer needs an external size
witness for those sections.
-/
structure ObjectBuiltinContext where
  layout : ObjectLayout
  dataSizes : List (Name × Word)
  dataOffsets : List (Name × Word)
  linkerSymbols : List (Name × Word)
  immutableValues : List (Name × Word) := []
  immutableReferences : List (Name × List ImmutableReference) := []
  selfSize? : Option (Name × Word) := none
  deriving Inhabited, Repr

namespace ObjectBuiltinContext

def ofLayout (layout : ObjectLayout) : ObjectBuiltinContext :=
  { layout := layout
    dataSizes := []
    dataOffsets := []
    linkerSymbols := [] }

def findDataSize? (context : ObjectBuiltinContext) (name : Name) :
    Option Word := do
  let entry ← context.dataSizes.find? fun entry => entry.fst == name
  some entry.snd

def findDataOffset? (context : ObjectBuiltinContext) (name : Name) :
    Option Word := do
  let entry ← context.dataOffsets.find? fun entry => entry.fst == name
  some entry.snd

def findLinkerSymbol? (context : ObjectBuiltinContext) (name : Name) :
    Option Word := do
  let entry ← context.linkerSymbols.find? fun entry => entry.fst == name
  some entry.snd

def findImmutableValue? (context : ObjectBuiltinContext) (name : Name) :
    Option Word := do
  let entry ← context.immutableValues.find? fun entry => entry.fst == name
  some entry.snd

def collectImmutableReferences
    (entries : List (Name × List ImmutableReference)) (name : Name) :
    List ImmutableReference :=
  entries.foldr
    (fun entry refs =>
      if entry.fst == name then
        entry.snd ++ refs
      else
        refs)
    []

def findImmutableReferences? (context : ObjectBuiltinContext) (name : Name) :
    Option (List ImmutableReference) :=
  let refs := collectImmutableReferences context.immutableReferences name
  match refs with
  | [] => none
  | _ :: _ => some refs

def findSelfSize? (context : ObjectBuiltinContext) (name : Name) :
    Option Word :=
  match context.selfSize? with
  | some (selfName, size) =>
      if selfName == name then
        some size
      else
        none
  | none => none

def size? (context : ObjectBuiltinContext) (name : Name) : Option Word :=
  match context.findDataSize? name with
  | some size => some size
  | none =>
      match context.findSelfSize? name with
      | some size => some size
      | none => context.layout.size? name

def offset? (context : ObjectBuiltinContext) (name : Name) : Option Word :=
  match context.findDataOffset? name with
  | some offset => some offset
  | none => context.layout.offset? name

end ObjectBuiltinContext

namespace Primitive

def ofName? : Name → Option (EvmYul.Operation .Yul)
  | "stop" => some .STOP
  | "add" => some .ADD
  | "mul" => some .MUL
  | "sub" => some .SUB
  | "div" => some .DIV
  | "sdiv" => some .SDIV
  | "mod" => some .MOD
  | "smod" => some .SMOD
  | "addmod" => some .ADDMOD
  | "mulmod" => some .MULMOD
  | "exp" => some .EXP
  | "signextend" => some .SIGNEXTEND
  | "lt" => some .LT
  | "gt" => some .GT
  | "slt" => some .SLT
  | "sgt" => some .SGT
  | "eq" => some .EQ
  | "iszero" => some .ISZERO
  | "and" => some .AND
  | "or" => some .OR
  | "xor" => some .XOR
  | "not" => some .NOT
  | "byte" => some .BYTE
  | "shl" => some .SHL
  | "shr" => some .SHR
  | "sar" => some .SAR
  | "keccak256" => some .KECCAK256
  | "sha3" => some .KECCAK256
  | "address" => some .ADDRESS
  | "balance" => some .BALANCE
  | "origin" => some .ORIGIN
  | "caller" => some .CALLER
  | "callvalue" => some .CALLVALUE
  | "calldataload" => some .CALLDATALOAD
  | "calldatasize" => some .CALLDATASIZE
  | "calldatacopy" => some .CALLDATACOPY
  | "codesize" => some .CODESIZE
  | "codecopy" => some .CODECOPY
  | "gasprice" => some .GASPRICE
  | "extcodesize" => some .EXTCODESIZE
  | "extcodecopy" => some .EXTCODECOPY
  | "returndatasize" => some .RETURNDATASIZE
  | "returndatacopy" => some .RETURNDATACOPY
  | "extcodehash" => some .EXTCODEHASH
  | "blockhash" => some .BLOCKHASH
  | "coinbase" => some .COINBASE
  | "timestamp" => some .TIMESTAMP
  | "number" => some .NUMBER
  | "prevrandao" => some .PREVRANDAO
  | "difficulty" => some .PREVRANDAO
  | "gaslimit" => some .GASLIMIT
  | "chainid" => some .CHAINID
  | "selfbalance" => some .SELFBALANCE
  | "basefee" => some .BASEFEE
  | "blobhash" => some .BLOBHASH
  | "blobbasefee" => some .BLOBBASEFEE
  | "pop" => some .POP
  | "mload" => some .MLOAD
  | "mstore" => some .MSTORE
  | "sload" => some .SLOAD
  | "sstore" => some .SSTORE
  | "mstore8" => some .MSTORE8
  | "msize" => some .MSIZE
  | "gas" => some .GAS
  | "tload" => some .TLOAD
  | "tstore" => some .TSTORE
  | "mcopy" => some .MCOPY
  | "log0" => some .LOG0
  | "log1" => some .LOG1
  | "log2" => some .LOG2
  | "log3" => some .LOG3
  | "log4" => some .LOG4
  | "create" => some .CREATE
  | "call" => some .CALL
  | "callcode" => some .CALLCODE
  | "return" => some .RETURN
  | "delegatecall" => some .DELEGATECALL
  | "create2" => some .CREATE2
  | "staticcall" => some .STATICCALL
  | "revert" => some .REVERT
  | "invalid" => some .INVALID
  | "selfdestruct" => some .SELFDESTRUCT
  | _ => none

end Primitive

mutual
  def Expr.loadImmutableNames : Expr → List Name
    | .lit _ => []
    | .stringLit _ => []
    | .var _ => []
    | .call .objectBuiltin "loadimmutable" [.stringLit name] => [name]
    | .call _ _ args => Expr.List.loadImmutableNames args

  def Expr.List.loadImmutableNames : List Expr → List Name
    | [] => []
    | expr :: rest =>
        Expr.loadImmutableNames expr ++ Expr.List.loadImmutableNames rest
end

mutual
  def Stmt.loadImmutableNames : Stmt → List Name
    | .block stmts => Stmt.List.loadImmutableNames stmts
    | .letDecl _ none => []
    | .letDecl _ (some value) => value.loadImmutableNames
    | .assign _ value => value.loadImmutableNames
    | .exprStmt expr => expr.loadImmutableNames
    | .switch scrutinee cases default =>
        scrutinee.loadImmutableNames ++
          Stmt.CaseList.loadImmutableNames cases ++
          Stmt.List.loadImmutableNames default
    | .forLoop condition post body =>
        condition.loadImmutableNames ++
          Stmt.List.loadImmutableNames post ++
          Stmt.List.loadImmutableNames body
    | .ifThen condition body =>
        condition.loadImmutableNames ++ Stmt.List.loadImmutableNames body
    | .break => []
    | .continue => []
    | .leave => []

  def Stmt.List.loadImmutableNames : List Stmt → List Name
    | [] => []
    | stmt :: rest =>
        Stmt.loadImmutableNames stmt ++ Stmt.List.loadImmutableNames rest

  def Stmt.CaseList.loadImmutableNames :
      List (Word × List Stmt) → List Name
    | [] => []
    | (_value, body) :: rest =>
        Stmt.List.loadImmutableNames body ++
          Stmt.CaseList.loadImmutableNames rest
end

namespace NameList

def insertUnique (name : Name) : List Name → List Name
  | [] => [name]
  | head :: rest =>
      if head == name then
        head :: rest
      else
        head :: insertUnique name rest

def unique : List Name → List Name
  | [] => []
  | name :: rest => insertUnique name (unique rest)

end NameList

namespace FunctionDef

def loadImmutableNames (fn : FunctionDef) : List Name :=
  Stmt.List.loadImmutableNames fn.body

namespace List

def loadImmutableNames : List (Name × FunctionDef) → List Name
  | [] => []
  | (_name, fn) :: rest =>
      fn.loadImmutableNames ++ loadImmutableNames rest

end List
end FunctionDef

namespace Object

def loadImmutableNames (object : Object) : List Name :=
  NameList.unique
    (Stmt.List.loadImmutableNames object.dispatcher ++
      FunctionDef.List.loadImmutableNames object.functions)

end Object

namespace ImmutableReference

def patchStmt? (reference : ImmutableReference) (base value : Expr) :
    Option Stmt :=
  if reference.isPatchable then
    some
      (.exprStmt
        (.call .primitive "mstore"
          [ .call .primitive "add"
              [base, .lit (EvmYul.UInt256.ofNat reference.start)]
          , value ]))
  else
    none

namespace List

def patchStmts? : List ImmutableReference → Expr → Expr → Option (List Stmt)
  | [], _base, _value => some []
  | reference :: rest, base, value => do
      let head ← reference.patchStmt? base value
      let tail ← patchStmts? rest base value
      some (head :: tail)

end List
end ImmutableReference

namespace ImmutableReference

def markerBase : Nat :=
  2 ^ 255

def markerValue (index : Nat) : Word :=
  EvmYul.UInt256.ofNat (markerBase + index + 1)

def markerEntriesFromNat : Nat → List Name → List (Name × Word)
  | _, [] => []
  | index, name :: rest =>
      (name, markerValue index) :: markerEntriesFromNat (index + 1) rest

def zeroEntries : List Name → List (Name × Word)
  | [] => []
  | name :: rest => (name, EvmYul.UInt256.ofNat 0) :: zeroEntries rest

end ImmutableReference

namespace Bytecode

def startsWithAt (needle bytes : List UInt8) (start : Nat) : Bool :=
  (bytes.drop start).take needle.length == needle

def findOccurrencesAux (needle bytes : List UInt8) :
    Nat → Nat → List Nat → List Nat
  | _start, 0, acc => acc.reverse
  | start, fuel + 1, acc =>
      let acc :=
        if startsWithAt needle bytes start then
          start :: acc
        else
          acc
      findOccurrencesAux needle bytes (start + 1) fuel acc

def findOccurrences (needle bytes : List UInt8) : List Nat :=
  match needle with
  | [] => []
  | _ :: _ => findOccurrencesAux needle bytes 0 (bytes.length + 1) []

def immutableReferencesForMarker (bytes : List UInt8) (value : Word) :
    List ImmutableReference :=
  (findOccurrences (Assembly.Bytecode.encodeWord32 value) bytes).map
    fun start => { start := start, length := ImmutableReference.patchLength }

def immutableReferenceEntries (bytes : List UInt8) :
    List (Name × Word) → List (Name × List ImmutableReference)
  | [] => []
  | (name, value) :: rest =>
      (name, immutableReferencesForMarker bytes value) ::
        immutableReferenceEntries bytes rest

end Bytecode

mutual
  def Expr.toYul? : Expr → Option AstExpr
    | .lit value => some (.Lit value)
    | .stringLit value => do
        let word ← StringLiteral.word? value
        some (.Lit word)
    | .var name => some (.Var name)
    | .call .primitive callee args => do
        let op ← Primitive.ofName? callee
        let args' ← Expr.List.toYul? args
        some (.Call (.inl op) args')
    | .call .user callee args => do
        let args' ← Expr.List.toYul? args
        some (.Call (.inr callee) args')
    | .call .objectBuiltin _ _ => none
    | .call .dialectBuiltin _ _ => none

  def Expr.List.toYul? : List Expr → Option (List AstExpr)
    | [] => some []
    | expr :: rest => do
        let head ← Expr.toYul? expr
        let tail ← Expr.List.toYul? rest
        some (head :: tail)

  def Stmt.toYul? : Stmt → Option AstStmt
    | .block stmts => do
        let stmts' ← Stmt.List.toYul? stmts
        some (.Block stmts')
    | .letDecl names none =>
        some (.Let names none)
    | .letDecl names (some value) => do
        let value' ← value.toYul?
        some (.Let names (some value'))
    | .assign names value => do
        let value' ← value.toYul?
        some (.Assign names value')
    | .exprStmt expr => do
        let expr' ← expr.toYul?
        some (.ExprStmtCall expr')
    | .switch scrutinee cases default => do
        let scrutinee' ← scrutinee.toYul?
        let cases' ← Stmt.CaseList.toYul? cases
        let default' ← Stmt.List.toYul? default
        some (.Switch scrutinee' cases' default')
    | .forLoop condition post body => do
        let condition' ← condition.toYul?
        let post' ← Stmt.List.toYul? post
        let body' ← Stmt.List.toYul? body
        some (.For condition' post' body')
    | .ifThen condition body => do
        let condition' ← condition.toYul?
        let body' ← Stmt.List.toYul? body
        some (.If condition' body')
    | .break => some .Break
    | .continue => some .Continue
    | .leave => some .Leave

  def Stmt.List.toYul? : List Stmt → Option (List AstStmt)
    | [] => some []
    | stmt :: rest => do
        let head ← Stmt.toYul? stmt
        let tail ← Stmt.List.toYul? rest
        some (head :: tail)

  def Stmt.CaseList.toYul? : List (Word × List Stmt) →
      Option (List (Word × List AstStmt))
    | [] => some []
    | (value, body) :: rest => do
        let body' ← Stmt.List.toYul? body
        let rest' ← Stmt.CaseList.toYul? rest
        some ((value, body') :: rest')

  def FunctionDef.toYul? (fn : FunctionDef) :
      Option AstFunctionDefinition := do
    let body ← Stmt.List.toYul? fn.body
    some (.Def fn.params fn.returns body)

  def FunctionDef.List.toYul? : List (Name × FunctionDef) →
      Option (List (Name × AstFunctionDefinition))
    | [] => some []
    | (name, fn) :: rest => do
        let fn' ← FunctionDef.toYul? fn
        let rest' ← FunctionDef.List.toYul? rest
        some ((name, fn') :: rest')
end

mutual
  def Expr.resolveObjectBuiltinsIn? (expr : Expr)
      (context : ObjectBuiltinContext) : Option Expr :=
    match expr with
    | .lit value => some (.lit value)
    | .stringLit value => some (.stringLit value)
    | .var name => some (.var name)
    | .call .objectBuiltin "datasize" [.stringLit name] => do
        let size ← context.size? name
        some (.lit size)
    | .call .objectBuiltin "dataoffset" [.stringLit name] => do
        let offset ← context.offset? name
        some (.lit offset)
    | .call .objectBuiltin "linkersymbol" [.stringLit name] => do
        let value ← context.findLinkerSymbol? name
        some (.lit value)
    | .call .objectBuiltin "loadimmutable" [.stringLit name] => do
        let value ← context.findImmutableValue? name
        some (.lit value)
    | .call .objectBuiltin "datacopy" [target, offset, size] => do
        let target' ← Expr.resolveObjectBuiltinsIn? target context
        let offset' ← Expr.resolveObjectBuiltinsIn? offset context
        let size' ← Expr.resolveObjectBuiltinsIn? size context
        some (.call .primitive "codecopy" [target', offset', size'])
    | .call kind callee args => do
        let args' ← Expr.List.resolveObjectBuiltinsIn? args context
        some (.call kind callee args')

  def Expr.List.resolveObjectBuiltinsIn? (exprs : List Expr)
      (context : ObjectBuiltinContext) : Option (List Expr) :=
    match exprs with
    | [] => some []
    | expr :: rest => do
        let head ← Expr.resolveObjectBuiltinsIn? expr context
        let tail ← Expr.List.resolveObjectBuiltinsIn? rest context
        some (head :: tail)

  def Stmt.resolveObjectBuiltinsIn? (stmt : Stmt)
      (context : ObjectBuiltinContext) : Option Stmt :=
    match stmt with
    | .block stmts => do
        let stmts' ← Stmt.List.resolveObjectBuiltinsIn? stmts context
        some (.block stmts')
    | .letDecl names none =>
        some (.letDecl names none)
    | .letDecl names (some value) => do
        let value' ← value.resolveObjectBuiltinsIn? context
        some (.letDecl names (some value'))
    | .assign names value => do
        let value' ← value.resolveObjectBuiltinsIn? context
        some (.assign names value')
    | .exprStmt (.call .objectBuiltin "setimmutable"
          [base, .stringLit name, value]) => do
        let base' ← base.resolveObjectBuiltinsIn? context
        let value' ← value.resolveObjectBuiltinsIn? context
        let references ← context.findImmutableReferences? name
        let stmts ←
          ImmutableReference.List.patchStmts? references base' value'
        some (.block stmts)
    | .exprStmt expr => do
        let expr' ← expr.resolveObjectBuiltinsIn? context
        some (.exprStmt expr')
    | .switch scrutinee cases default => do
        let scrutinee' ← scrutinee.resolveObjectBuiltinsIn? context
        let cases' ← Stmt.CaseList.resolveObjectBuiltinsIn? cases context
        let default' ← Stmt.List.resolveObjectBuiltinsIn? default context
        some (.switch scrutinee' cases' default')
    | .forLoop condition post body => do
        let condition' ← condition.resolveObjectBuiltinsIn? context
        let post' ← Stmt.List.resolveObjectBuiltinsIn? post context
        let body' ← Stmt.List.resolveObjectBuiltinsIn? body context
        some (.forLoop condition' post' body')
    | .ifThen condition body => do
        let condition' ← condition.resolveObjectBuiltinsIn? context
        let body' ← Stmt.List.resolveObjectBuiltinsIn? body context
        some (.ifThen condition' body')
    | .break => some .break
    | .continue => some .continue
    | .leave => some .leave

  def Stmt.List.resolveObjectBuiltinsIn? (stmts : List Stmt)
      (context : ObjectBuiltinContext) : Option (List Stmt) :=
    match stmts with
    | [] => some []
    | stmt :: rest => do
        let head ← Stmt.resolveObjectBuiltinsIn? stmt context
        let tail ← Stmt.List.resolveObjectBuiltinsIn? rest context
        some (head :: tail)

  def Stmt.CaseList.resolveObjectBuiltinsIn?
      (cases : List (Word × List Stmt)) (context : ObjectBuiltinContext) :
      Option (List (Word × List Stmt)) :=
    match cases with
    | [] => some []
    | (value, body) :: rest => do
        let body' ← Stmt.List.resolveObjectBuiltinsIn? body context
        let rest' ← Stmt.CaseList.resolveObjectBuiltinsIn? rest context
        some ((value, body') :: rest')

  def FunctionDef.resolveObjectBuiltinsIn? (fn : FunctionDef)
      (context : ObjectBuiltinContext) : Option FunctionDef := do
    let body ← Stmt.List.resolveObjectBuiltinsIn? fn.body context
    some { params := fn.params, returns := fn.returns, body := body }

  def FunctionDef.List.resolveObjectBuiltinsIn?
      (functions : List (Name × FunctionDef)) (context : ObjectBuiltinContext) :
      Option (List (Name × FunctionDef)) :=
    match functions with
    | [] => some []
    | (name, fn) :: rest => do
        let fn' ← FunctionDef.resolveObjectBuiltinsIn? fn context
        let rest' ← FunctionDef.List.resolveObjectBuiltinsIn? rest context
        some ((name, fn') :: rest')
end

namespace Expr

def resolveObjectBuiltins? (expr : Expr) (layout : ObjectLayout) :
    Option Expr :=
  expr.resolveObjectBuiltinsIn? (ObjectBuiltinContext.ofLayout layout)

namespace List

def resolveObjectBuiltins? (exprs : List Expr) (layout : ObjectLayout) :
    Option (List Expr) :=
  Expr.List.resolveObjectBuiltinsIn? exprs
    (ObjectBuiltinContext.ofLayout layout)

end List
end Expr

namespace Stmt

def resolveObjectBuiltins? (stmt : Stmt) (layout : ObjectLayout) :
    Option Stmt :=
  stmt.resolveObjectBuiltinsIn? (ObjectBuiltinContext.ofLayout layout)

namespace List

def resolveObjectBuiltins? (stmts : List Stmt) (layout : ObjectLayout) :
    Option (List Stmt) :=
  Stmt.List.resolveObjectBuiltinsIn? stmts
    (ObjectBuiltinContext.ofLayout layout)

end List

namespace CaseList

def resolveObjectBuiltins? (cases : List (Word × List Stmt))
    (layout : ObjectLayout) :
    Option (List (Word × List Stmt)) :=
  Stmt.CaseList.resolveObjectBuiltinsIn? cases
    (ObjectBuiltinContext.ofLayout layout)

end CaseList
end Stmt

namespace FunctionDef

def resolveObjectBuiltins? (fn : FunctionDef) (layout : ObjectLayout) :
    Option FunctionDef :=
  fn.resolveObjectBuiltinsIn? (ObjectBuiltinContext.ofLayout layout)

namespace List

def resolveObjectBuiltins? (functions : List (Name × FunctionDef))
    (layout : ObjectLayout) :
    Option (List (Name × FunctionDef)) :=
  FunctionDef.List.resolveObjectBuiltinsIn? functions
    (ObjectBuiltinContext.ofLayout layout)

end List
end FunctionDef

namespace Expr

theorem resolveObjectBuiltins_datacopy_codecopy
    {context : ObjectBuiltinContext} {target offset size : Expr}
    {target' offset' size' : Expr}
    (hTarget : target.resolveObjectBuiltinsIn? context = some target')
    (hOffset : offset.resolveObjectBuiltinsIn? context = some offset')
    (hSize : size.resolveObjectBuiltinsIn? context = some size') :
    Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "datacopy" [target, offset, size]) context =
      some (.call .primitive "codecopy" [target', offset', size']) := by
  simp [Expr.resolveObjectBuiltinsIn?, hTarget, hOffset, hSize]

theorem resolveObjectBuiltins_datasize_namedData
    {name : Name} {bytes : List UInt8} {layout : ObjectLayout} :
    Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "datasize" [.stringLit name])
        { layout := layout
          dataSizes := DataSection.sizeEntries [
            DataSection.mk (some name) bytes
          ]
          dataOffsets := []
          linkerSymbols := [] } =
      some (.lit (EvmYul.UInt256.ofNat bytes.length)) := by
  simp [Expr.resolveObjectBuiltinsIn?, ObjectBuiltinContext.size?,
    ObjectBuiltinContext.findDataSize?, DataSection.sizeEntries,
    DataSection.sizeEntry?, DataSection.size]

theorem resolveObjectBuiltins_dataoffset_namedDataBase
    {name : Name} {bytes : List UInt8} {layout : ObjectLayout} {base : Nat} :
    Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "dataoffset" [.stringLit name])
        { layout := layout
          dataSizes := []
          dataOffsets := DataSection.offsetEntriesFromNat base [
            DataSection.mk (some name) bytes
          ]
          linkerSymbols := [] } =
      some (.lit (EvmYul.UInt256.ofNat base)) := by
  simp [Expr.resolveObjectBuiltinsIn?, ObjectBuiltinContext.offset?,
    ObjectBuiltinContext.findDataOffset?, DataSection.offsetEntriesFromNat,
    DataSection.offsetEntryFromNat?]

theorem toYul_after_resolveObjectBuiltins_datasize_namedData
    {name : Name} {bytes : List UInt8} {layout : ObjectLayout} :
    (Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "datasize" [.stringLit name])
        { layout := layout
          dataSizes := DataSection.sizeEntries [
            DataSection.mk (some name) bytes
          ]
          dataOffsets := []
          linkerSymbols := [] } >>= Expr.toYul?) =
      some (.Lit (EvmYul.UInt256.ofNat bytes.length)) := by
  simp [resolveObjectBuiltins_datasize_namedData, Expr.toYul?]

theorem toYul_after_resolveObjectBuiltins_dataoffset_namedDataBase
    {name : Name} {bytes : List UInt8} {layout : ObjectLayout} {base : Nat} :
    (Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "dataoffset" [.stringLit name])
        { layout := layout
          dataSizes := []
          dataOffsets := DataSection.offsetEntriesFromNat base [
            DataSection.mk (some name) bytes
          ]
          linkerSymbols := [] } >>= Expr.toYul?) =
      some (.Lit (EvmYul.UInt256.ofNat base)) := by
  simp [resolveObjectBuiltins_dataoffset_namedDataBase, Expr.toYul?]

theorem toYul_after_resolveObjectBuiltins_datacopy_codecopy
    {context : ObjectBuiltinContext} {target offset size : Expr}
    {target' offset' size' : Expr}
    {targetYul offsetYul sizeYul : AstExpr}
    (hTarget : target.resolveObjectBuiltinsIn? context = some target')
    (hOffset : offset.resolveObjectBuiltinsIn? context = some offset')
    (hSize : size.resolveObjectBuiltinsIn? context = some size')
    (hTargetYul : target'.toYul? = some targetYul)
    (hOffsetYul : offset'.toYul? = some offsetYul)
    (hSizeYul : size'.toYul? = some sizeYul) :
    (Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "datacopy" [target, offset, size])
        context >>= Expr.toYul?) =
      some
        (.Call (.inl ((.Env .CODECOPY : EvmYul.Operation .Yul)))
          [targetYul, offsetYul, sizeYul]) := by
  simp [resolveObjectBuiltins_datacopy_codecopy hTarget hOffset hSize,
    Expr.toYul?, Expr.List.toYul?, Primitive.ofName?, hTargetYul, hOffsetYul,
    hSizeYul]

end Expr

namespace FunctionPrep

namespace Expr

mutual
  def names {results : Nat} : Functions.Expr results → List Name
    | .lit _value => []
    | .var name => [name]
    | .code _code => []
    | .prim _op args => ExprSeq.names args

  def ExprSeq.names {results : Nat} :
      Locals.ExprSeq results → List Name
    | .nil => []
    | .cons head tail => names head ++ ExprSeq.names tail
end

end Expr

def anyNameIn (needles haystack : List Name) : Bool :=
  needles.any fun name => haystack.contains name

mutual
  def Stmt.touchNames : Functions.Stmt → List Name
    | .expr expr => Expr.names expr
    | .let_ name value => name :: Expr.names value
    | .assign name value => name :: Expr.names value
    | .block body => Block.touchNames body
    | .if_ cond body => Expr.names cond ++ Block.touchNames body
    | .switch scrutinee cases defaultBody =>
        Expr.names scrutinee ++
          CaseList.touchNames cases ++ Default.touchNames defaultBody
    | .for_ init cond post body =>
        Block.touchNames init ++ Expr.names cond ++
          Block.touchNames post ++ Block.touchNames body
    | .brk => []
    | .cont => []
    | .leave => []
    | .call targets _functionName args =>
        targets ++ args.foldr (fun arg names => Expr.names arg ++ names) []
    | .terminal _kind => []
    | .terminalArgs _kind args => Expr.ExprSeq.names args
  termination_by stmt => sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.touchNames (block : Functions.Block) : List Name :=
    StmtList.touchNames block.stmts
  termination_by sizeOf block
  decreasing_by
    cases block
    simp_wf

  def StmtList.touchNames : List Functions.Stmt → List Name
    | [] => []
    | stmt :: rest => Stmt.touchNames stmt ++ StmtList.touchNames rest
  termination_by stmts => sizeOf stmts
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | exact List.sizeOf_lt_sizeOf_of_mem (by assumption)
      | omega

  def CaseList.touchNames :
      List (Word × Functions.Block) → List Name
    | [] => []
    | (_value, body) :: rest =>
        Block.touchNames body ++ CaseList.touchNames rest
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Default.touchNames : Option Functions.Block → List Name
    | none => []
    | some body => Block.touchNames body
  termination_by defaultBody => sizeOf defaultBody
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def Stmt.declaredNames : Functions.Stmt → List Name
    | .let_ name _value => [name]
    | .block body => Block.declaredNames body
    | .if_ _cond body => Block.declaredNames body
    | .switch _scrutinee cases defaultBody =>
        CaseList.declaredNames cases ++ Default.declaredNames defaultBody
    | .for_ init _cond post body =>
        Block.declaredNames init ++
          Block.declaredNames post ++ Block.declaredNames body
    | _ => []
  termination_by stmt => sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.declaredNames (block : Functions.Block) : List Name :=
    StmtList.declaredNames block.stmts
  termination_by sizeOf block
  decreasing_by
    cases block
    simp_wf

  def StmtList.declaredNames : List Functions.Stmt → List Name
    | [] => []
    | stmt :: rest => Stmt.declaredNames stmt ++ StmtList.declaredNames rest
  termination_by stmts => sizeOf stmts
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def CaseList.declaredNames :
      List (Word × Functions.Block) → List Name
    | [] => []
    | (_value, body) :: rest =>
        Block.declaredNames body ++ CaseList.declaredNames rest
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Default.declaredNames : Option Functions.Block → List Name
    | none => []
    | some body => Block.declaredNames body
  termination_by defaultBody => sizeOf defaultBody
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def letName? : Functions.Stmt → Option Name
  | .let_ name _value => some name
  | _ => none

def splitAfterLastTouch (names : List Name) :
    List Functions.Stmt → List Functions.Stmt × List Functions.Stmt
  | [] => ([], [])
  | stmt :: rest =>
      let (inside, outside) := splitAfterLastTouch names rest
      if anyNameIn names (Stmt.touchNames stmt) then
        (stmt :: inside, outside)
      else
        match inside with
        | [] => ([], stmt :: outside)
        | _ => (stmt :: inside, outside)

def StmtList.scopeLetLifetimesMappedFuel :
    Nat → List Functions.Stmt → List Functions.Stmt
  | 0, stmts => stmts
  | _fuel + 1, [] => []
  | fuel + 1, stmt :: rest =>
      match letName? stmt with
      | some name =>
          let (inside, outside) := splitAfterLastTouch [name] rest
          let declaredInside := StmtList.declaredNames inside
          let outsideTouches := StmtList.touchNames outside
          if anyNameIn declaredInside outsideTouches then
            stmt :: StmtList.scopeLetLifetimesMappedFuel fuel rest
          else
            .block
                { stmts :=
                    stmt ::
                      StmtList.scopeLetLifetimesMappedFuel fuel inside } ::
              StmtList.scopeLetLifetimesMappedFuel fuel outside
      | none =>
          stmt :: StmtList.scopeLetLifetimesMappedFuel fuel rest
termination_by fuel stmts => (fuel, sizeOf stmts)
decreasing_by
  all_goals simp_wf
  all_goals omega

mutual
  def Stmt.scopeLetLifetimes : Functions.Stmt → Functions.Stmt
    | .block body => .block (Block.scopeLetLifetimes body)
    | .if_ cond body => .if_ cond (Block.scopeLetLifetimes body)
    | .switch scrutinee cases defaultBody =>
        .switch scrutinee (CaseList.scopeLetLifetimes cases)
          (Default.scopeLetLifetimes defaultBody)
    | .for_ init cond post body =>
        .for_ (Block.scopeLetLifetimes init) cond
          (Block.scopeLetLifetimes post) (Block.scopeLetLifetimes body)
    | stmt => stmt
  termination_by stmt => sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.scopeLetLifetimes (block : Functions.Block) :
      Functions.Block :=
    { stmts := StmtList.scopeLetLifetimes block.stmts }
  termination_by sizeOf block
  decreasing_by
    cases block
    simp_wf

  def StmtList.scopeLetLifetimes :
      List Functions.Stmt → List Functions.Stmt
    | stmts =>
        let mapped := stmts.map Stmt.scopeLetLifetimes
        StmtList.scopeLetLifetimesMappedFuel (mapped.length + 1) mapped
  termination_by stmts => sizeOf stmts
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | exact List.sizeOf_lt_sizeOf_of_mem (by assumption)
      | omega

  def CaseList.scopeLetLifetimes :
      List (Word × Functions.Block) → List (Word × Functions.Block)
    | [] => []
    | (value, body) :: rest =>
        (value, Block.scopeLetLifetimes body) ::
          CaseList.scopeLetLifetimes rest
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Default.scopeLetLifetimes :
      Option Functions.Block → Option Functions.Block
    | none => none
    | some body => some (Block.scopeLetLifetimes body)
  termination_by defaultBody => sizeOf defaultBody
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

namespace FunDef

def scopeLetLifetimes (fn : Functions.FunDef) : Functions.FunDef :=
  { fn with body := Block.scopeLetLifetimes fn.body }

end FunDef

namespace Program

def scopeLetLifetimes (program : Functions.Program) :
    Functions.Program :=
  { functions := program.functions.map FunDef.scopeLetLifetimes
    body := Block.scopeLetLifetimes program.body }

end Program

end FunctionPrep

namespace Object

namespace ItemRef

def objectsFromNat : Nat → List Object → List ObjectItemRef
  | _, [] => []
  | index, _object :: rest =>
      .object index :: objectsFromNat (index + 1) rest

def dataFromNat : Nat → List DataSection → List ObjectItemRef
  | _, [] => []
  | index, _dataSection :: rest =>
      .data index :: dataFromNat (index + 1) rest

end ItemRef

def defaultItems (object : Object) : List ObjectItemRef :=
  ItemRef.objectsFromNat 0 object.objects ++
    ItemRef.dataFromNat 0 object.data

def effectiveItems (object : Object) : List ObjectItemRef :=
  match object.items with
  | [] => object.defaultItems
  | items => items

def dataSizeEntries (object : Object) : List (Name × Word) :=
  DataSection.sizeEntries object.data

def dataOffsetEntriesFromNat (object : Object) (base : Nat) :
    List (Name × Word) :=
  DataSection.offsetEntriesFromNat base object.data

def builtinContext (object : Object) (layout : ObjectLayout) :
    ObjectBuiltinContext :=
  { layout := layout
    dataSizes := object.dataSizeEntries
    dataOffsets := []
    linkerSymbols := [] }

def builtinContextWithLocalDataBase (object : Object) (layout : ObjectLayout)
    (base : Nat) : ObjectBuiltinContext :=
  { layout := layout
    dataSizes := object.dataSizeEntries
    dataOffsets := object.dataOffsetEntriesFromNat base
    linkerSymbols := [] }

def builtinContextWithLinkerSymbols
    (object : Object) (layout : ObjectLayout)
    (linkerSymbols : List (Name × Word)) : ObjectBuiltinContext :=
  { layout := layout
    dataSizes := object.dataSizeEntries
    dataOffsets := []
    linkerSymbols := linkerSymbols }

def builtinContextWithLocalDataBaseAndLinkerSymbols
    (object : Object) (layout : ObjectLayout) (base : Nat)
    (linkerSymbols : List (Name × Word)) : ObjectBuiltinContext :=
  { layout := layout
    dataSizes := object.dataSizeEntries
    dataOffsets := object.dataOffsetEntriesFromNat base
    linkerSymbols := linkerSymbols }

def resolveObjectBuiltinsIn? (object : Object)
    (context : ObjectBuiltinContext) : Option Object := do
  let dispatcher ← Stmt.List.resolveObjectBuiltinsIn? object.dispatcher context
  let functions ←
    FunctionDef.List.resolveObjectBuiltinsIn? object.functions context
  some
    { name := object.name
      dispatcher := dispatcher
      functions := functions
      data := object.data
      objects := object.objects
      items := object.items }

def resolveObjectBuiltins? (object : Object)
    (layout : ObjectLayout) : Option Object :=
  object.resolveObjectBuiltinsIn? (object.builtinContext layout)

def resolveObjectBuiltinsWithLocalDataBase? (object : Object)
    (layout : ObjectLayout) (base : Nat) : Option Object :=
  object.resolveObjectBuiltinsIn?
    (object.builtinContextWithLocalDataBase layout base)

def resolveObjectBuiltinsWithLinkerSymbols? (object : Object)
    (layout : ObjectLayout) (linkerSymbols : List (Name × Word)) :
    Option Object :=
  object.resolveObjectBuiltinsIn?
    (object.builtinContextWithLinkerSymbols layout linkerSymbols)

def resolveObjectBuiltinsWithLocalDataBaseAndLinkerSymbols? (object : Object)
    (layout : ObjectLayout) (base : Nat)
    (linkerSymbols : List (Name × Word)) : Option Object :=
  object.resolveObjectBuiltinsIn?
    (object.builtinContextWithLocalDataBaseAndLinkerSymbols
      layout base linkerSymbols)

end Object

structure ObjectImage where
  name : Name
  bytes : List UInt8
  immutableReferences : List (Name × List ImmutableReference) := []
  deriving Inhabited, Repr

namespace ObjectImage

def size (image : ObjectImage) : Nat :=
  image.bytes.length

def layoutEntryFromNat (base : Nat) (image : ObjectImage) :
    ObjectLayout.Entry :=
  { name := image.name
    offset := EvmYul.UInt256.ofNat base
    size := EvmYul.UInt256.ofNat image.size }

def layoutEntriesFromNat : Nat → List ObjectImage → List ObjectLayout.Entry
  | _, [] => []
  | base, image :: rest =>
      image.layoutEntryFromNat base ::
        layoutEntriesFromNat (base + image.size) rest

def bytesAll (images : List ObjectImage) : List UInt8 :=
  Bytecode.concat (images.map (fun image => image.bytes))

def totalSize (images : List ObjectImage) : Nat :=
  images.foldl (fun acc image => acc + image.size) 0

def immutableReferenceEntries : List ObjectImage →
    List (Name × List ImmutableReference)
  | [] => []
  | image :: rest =>
      image.immutableReferences ++ immutableReferenceEntries rest

end ObjectImage

namespace ObjectItemRef

def payloadSize? (dataSections : List DataSection)
    (objectImages : List ObjectImage) : ObjectItemRef → Option Nat
  | .data index => do
      let dataSection ← dataSections[index]?
      some dataSection.bytes.length
  | .object index => do
      let image ← objectImages[index]?
      some image.size

def payloadBytes? (dataSections : List DataSection)
    (objectImages : List ObjectImage) : ObjectItemRef → Option (List UInt8)
  | .data index => do
      let dataSection ← dataSections[index]?
      some dataSection.bytes
  | .object index => do
      let image ← objectImages[index]?
      some image.bytes

namespace List

def objectLayoutEntriesFromNat? (dataSections : List DataSection)
    (objectImages : List ObjectImage) :
    Nat → List ObjectItemRef → Option (List ObjectLayout.Entry)
  | _, [] => some []
  | base, item :: rest => do
      let itemSize ← item.payloadSize? dataSections objectImages
      let tail ←
        objectLayoutEntriesFromNat?
          dataSections objectImages (base + itemSize) rest
      match item with
      | .data _ => some tail
      | .object index => do
          let image ← objectImages[index]?
          some (image.layoutEntryFromNat base :: tail)

def dataOffsetEntriesFromNat? (dataSections : List DataSection)
    (objectImages : List ObjectImage) :
    Nat → List ObjectItemRef → Option (List (Name × Word))
  | _, [] => some []
  | base, item :: rest => do
      let itemSize ← item.payloadSize? dataSections objectImages
      let tail ←
        dataOffsetEntriesFromNat?
          dataSections objectImages (base + itemSize) rest
      match item with
      | .object _ => some tail
      | .data index => do
          let dataSection ← dataSections[index]?
          match dataSection.offsetEntryFromNat? base with
          | some entry => some (entry :: tail)
          | none => some tail

def payloadBytes? (dataSections : List DataSection)
    (objectImages : List ObjectImage) :
    List ObjectItemRef → Option (List UInt8)
  | [] => some []
  | item :: rest => do
      let head ← item.payloadBytes? dataSections objectImages
      let tail ← payloadBytes? dataSections objectImages rest
      some (head ++ tail)

end List
end ObjectItemRef

namespace Object

def functionMap (entries : List (Name × AstFunctionDefinition)) :
    Finmap (fun (_ : EvmYul.Yul.Ast.YulFunctionName) =>
      AstFunctionDefinition) :=
  entries.foldl
    (fun acc entry => acc.insert entry.fst entry.snd)
    (∅ : Finmap (fun (_ : EvmYul.Yul.Ast.YulFunctionName) =>
      AstFunctionDefinition))

def toYulContract? (object : Object) : Option AstContract := do
  let dispatcher ← Stmt.toYul? (.block object.dispatcher)
  let functions ← FunctionDef.List.toYul? object.functions
  some
    { dispatcher := dispatcher
      functions := functionMap functions }

def toYulProgram? (object : Object) : Option Yul.Program := do
  let contract ← Object.toYulContract? object
  some { contract := contract }

def toYulProgramWithLayout? (object : Object) (layout : ObjectLayout) :
    Option Yul.Program := do
  let resolved ← object.resolveObjectBuiltins? layout
  Object.toYulProgram? resolved

def toYulProgramWithLocalDataBase? (object : Object) (layout : ObjectLayout)
    (base : Nat) : Option Yul.Program := do
  let resolved ← object.resolveObjectBuiltinsWithLocalDataBase? layout base
  Object.toYulProgram? resolved

noncomputable def lowerCode? (object : Object) :
    Option Functions.Program := do
  let contract ← object.toYulContract?
  let lower ← Yul.Contract.toObjects? contract
  some lower.root.code

def lowerCodeUnchecked? (object : Object) :
    Option Functions.Program := do
  let dispatcher ← Stmt.List.toYul? object.dispatcher
  let dispatcher := Yul.Stmt.List.simplifyForUnchecked dispatcher
  let functionsYul ← FunctionDef.List.toYul? object.functions
  let functionsYul := Yul.FunctionList.simplifyForUnchecked functionsYul
  let initial :=
    Yul.Fresh.initial
      (Yul.Stmt.List.names dispatcher ++
        Yul.FunctionList.names functionsYul)
  let fuel :=
    Stmt.List.loweringFuel object.dispatcher +
      FunctionDef.List.loweringFuel object.functions + 1
  let (bodyStmts, state) ←
    Yul.Stmt.List.toFunctionsFuel? fuel initial dispatcher
  let (functions, _state) ←
    Yul.FunctionList.toFunDefsFuel? fuel state functionsYul
  some
    (FunctionPrep.Program.scopeLetLifetimes
      { functions := functions, body := { stmts := bodyStmts } })

def lowerCodeUncheckedWithLayout? (object : Object)
    (layout : ObjectLayout) : Option Functions.Program := do
  let resolved ← object.resolveObjectBuiltins? layout
  resolved.lowerCodeUnchecked?

def lowerCodeUncheckedWithLocalDataBase? (object : Object)
    (layout : ObjectLayout) (base : Nat) : Option Functions.Program := do
  let resolved ← object.resolveObjectBuiltinsWithLocalDataBase? layout base
  resolved.lowerCodeUnchecked?

def compileCodeUncheckedIn? (object : Object)
    (context : ObjectBuiltinContext) : Option Assembly.TargetProgram := do
  let resolved ← object.resolveObjectBuiltinsIn? context
  let code ← resolved.lowerCodeUnchecked?
  Functions.Program.compile? code

def codeBytesUncheckedIn? (object : Object)
    (context : ObjectBuiltinContext) : Option (List UInt8) := do
  let target ← object.compileCodeUncheckedIn? context
  some (Assembly.Bytecode.encodeTarget target).toList

mutual
  noncomputable def toObjects? (object : Object) :
      Option Objects.Object := do
    let code ← object.lowerCode?
    let objects ← List.toObjects? object.objects
    some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)
  termination_by sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  noncomputable def List.toObjects? (objects : List Object) :
      Option (List Objects.Object) :=
    match objects with
    | [] => some []
    | object :: rest => do
        let head ← Object.toObjects? object
        let tail ← List.toObjects? rest
        some (head :: tail)
  termination_by sizeOf objects
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def toObjectsUnchecked? (object : Object) :
      Option Objects.Object := do
    let code ← object.lowerCodeUnchecked?
    let objects ← List.toObjectsUnchecked? object.objects
    some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)
  termination_by sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  def List.toObjectsUnchecked? (objects : List Object) :
      Option (List Objects.Object) :=
    match objects with
    | [] => some []
    | object :: rest => do
        let head ← Object.toObjectsUnchecked? object
        let tail ← List.toObjectsUnchecked? rest
        some (head :: tail)
  termination_by sizeOf objects
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  noncomputable def toObjectsWithLayout? (object : Object)
      (layout : ObjectLayout) : Option Objects.Object := do
    let resolved ← object.resolveObjectBuiltins? layout
    let code ← resolved.lowerCode?
    let objects ← List.toObjectsWithLayout? object.objects layout
    some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)
  termination_by sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  noncomputable def List.toObjectsWithLayout?
      (objects : List Object) (layout : ObjectLayout) :
      Option (List Objects.Object) :=
    match objects with
    | [] => some []
    | object :: rest => do
        let head ← Object.toObjectsWithLayout? object layout
        let tail ← List.toObjectsWithLayout? rest layout
        some (head :: tail)
  termination_by sizeOf objects
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def toObjectsUncheckedWithLayout? (object : Object)
      (layout : ObjectLayout) : Option Objects.Object := do
    let resolved ← object.resolveObjectBuiltins? layout
    let code ← resolved.lowerCodeUnchecked?
    let objects ← List.toObjectsUncheckedWithLayout? object.objects layout
    some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)
  termination_by sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  def List.toObjectsUncheckedWithLayout?
      (objects : List Object) (layout : ObjectLayout) :
      Option (List Objects.Object) :=
    match objects with
    | [] => some []
    | object :: rest => do
        let head ← Object.toObjectsUncheckedWithLayout? object layout
        let tail ← List.toObjectsUncheckedWithLayout? rest layout
        some (head :: tail)
  termination_by sizeOf objects
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

noncomputable def toObjectsWithLocalDataBase? (object : Object)
    (layout : ObjectLayout) (base : Nat) : Option Objects.Object := do
  let resolved ← object.resolveObjectBuiltinsWithLocalDataBase? layout base
  let code ← resolved.lowerCode?
  let objects ← List.toObjectsWithLayout? object.objects layout
  some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)

def toObjectsUncheckedWithLocalDataBase? (object : Object)
    (layout : ObjectLayout) (base : Nat) : Option Objects.Object := do
  let resolved ← object.resolveObjectBuiltinsWithLocalDataBase? layout base
  let code ← resolved.lowerCodeUnchecked?
  let objects ← List.toObjectsUncheckedWithLayout? object.objects layout
  some
      (Objects.Object.mk object.name code
        (DataSection.List.toObjects object.data) objects)

mutual
  def bytecodeImageUncheckedWithLinkerSymbols?
      (object : Object) (linkerSymbols : List (Name × Word)) :
      Option ObjectImage := do
    let childImages ←
      List.bytecodeImagesUncheckedWithLinkerSymbols?
        object.objects linkerSymbols
    let childImmutableReferences :=
      ObjectImage.immutableReferenceEntries childImages
    let immutableNames := object.loadImmutableNames
    let zeroImmutableValues :=
      ImmutableReference.zeroEntries immutableNames
    let markerImmutableValues :=
      ImmutableReference.markerEntriesFromNat 0 immutableNames
    let items := object.effectiveItems
    let layout0 ←
      ObjectItemRef.List.objectLayoutEntriesFromNat?
        object.data childImages 0 items
    let dataOffsets0 ←
      ObjectItemRef.List.dataOffsetEntriesFromNat?
        object.data childImages 0 items
    let payload ← ObjectItemRef.List.payloadBytes? object.data childImages items
    let placeholderLayout : ObjectLayout := { entries := layout0 }
    let placeholderContext : ObjectBuiltinContext :=
      { layout := placeholderLayout
        dataSizes := object.dataSizeEntries
        dataOffsets := dataOffsets0
        linkerSymbols := linkerSymbols
        immutableValues := zeroImmutableValues
        immutableReferences := childImmutableReferences
        selfSize? := some (object.name, EvmYul.UInt256.ofNat 0) }
    let placeholderCode ← object.codeBytesUncheckedIn? placeholderContext
    let codeBase := placeholderCode.length
    let selfSize := EvmYul.UInt256.ofNat (codeBase + payload.length)
    let layout ←
      ObjectItemRef.List.objectLayoutEntriesFromNat?
        object.data childImages codeBase items
    let dataOffsets ←
      ObjectItemRef.List.dataOffsetEntriesFromNat?
        object.data childImages codeBase items
    let context : ObjectBuiltinContext :=
      { layout := { entries := layout }
        dataSizes := object.dataSizeEntries
        dataOffsets := dataOffsets
        linkerSymbols := linkerSymbols
        immutableValues := zeroImmutableValues
        immutableReferences := childImmutableReferences
        selfSize? := some (object.name, selfSize) }
    let code ← object.codeBytesUncheckedIn? context
    let markerContext : ObjectBuiltinContext :=
      { context with immutableValues := markerImmutableValues }
    let markerCode ← object.codeBytesUncheckedIn? markerContext
    let immutableReferences :=
      Bytecode.immutableReferenceEntries markerCode markerImmutableValues
    some
      { name := object.name
        bytes := code ++ payload
        immutableReferences := immutableReferences }
  termination_by sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  def List.bytecodeImagesUncheckedWithLinkerSymbols?
      (objects : List Object) (linkerSymbols : List (Name × Word)) :
      Option (List ObjectImage) :=
    match objects with
    | [] => some []
    | object :: rest => do
        let head ←
          Object.bytecodeImageUncheckedWithLinkerSymbols?
            object linkerSymbols
        let tail ←
          List.bytecodeImagesUncheckedWithLinkerSymbols?
            rest linkerSymbols
        some (head :: tail)
  termination_by sizeOf objects
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def bytecodeImageUnchecked? (object : Object) : Option ObjectImage :=
  object.bytecodeImageUncheckedWithLinkerSymbols? []

def bytecodeUncheckedImageWithLinkerSymbols?
    (object : Object) (linkerSymbols : List (Name × Word)) :
    Option ByteArray := do
  let image ← object.bytecodeImageUncheckedWithLinkerSymbols? linkerSymbols
  some (Assembly.Bytecode.ofList image.bytes)

def bytecodeUncheckedImage? (object : Object) : Option ByteArray := do
  object.bytecodeUncheckedImageWithLinkerSymbols? []

end Object

namespace Program

def toYulProgram? (program : Program) : Option Yul.Program :=
  Object.toYulProgram? program.object

noncomputable def toObjects? (program : Program) : Option Objects.Program := do
  let root ← Object.toObjects? program.object
  some { root := root }

def toObjectsUnchecked? (program : Program) : Option Objects.Program := do
  let root ← Object.toObjectsUnchecked? program.object
  some { root := root }

def compileUnchecked? (program : Program) :
    Option Assembly.TargetProgram := do
  let lower ← program.toObjectsUnchecked?
  Objects.Program.compile? lower

def bytecodeUnchecked? (program : Program) : Option ByteArray := do
  let target ← program.compileUnchecked?
  some (Assembly.Bytecode.encodeTarget target)

def resolveObjectBuiltins? (program : Program) (layout : ObjectLayout) :
    Option Program := do
  let object ← Object.resolveObjectBuiltins? program.object layout
  some { source := program.source, contract := program.contract, object := object }

def toYulProgramWithLayout? (program : Program) (layout : ObjectLayout) :
    Option Yul.Program := do
  let resolved ← program.resolveObjectBuiltins? layout
  resolved.toYulProgram?

noncomputable def toObjectsWithLayout? (program : Program)
    (layout : ObjectLayout) : Option Objects.Program := do
  let root ← Object.toObjectsWithLayout? program.object layout
  some { root := root }

def toObjectsUncheckedWithLayout? (program : Program)
    (layout : ObjectLayout) : Option Objects.Program := do
  let root ← Object.toObjectsUncheckedWithLayout? program.object layout
  some { root := root }

def compileUncheckedWithLayout? (program : Program)
    (layout : ObjectLayout) : Option Assembly.TargetProgram := do
  let lower ← program.toObjectsUncheckedWithLayout? layout
  Objects.Program.compile? lower

def bytecodeUncheckedWithLayout? (program : Program)
    (layout : ObjectLayout) : Option ByteArray := do
  let target ← program.compileUncheckedWithLayout? layout
  some (Assembly.Bytecode.encodeTarget target)

def resolveObjectBuiltinsWithLocalDataBase? (program : Program)
    (layout : ObjectLayout) (base : Nat) : Option Program := do
  let object ←
    Object.resolveObjectBuiltinsWithLocalDataBase?
      program.object layout base
  some { source := program.source, contract := program.contract, object := object }

def toYulProgramWithLocalDataBase? (program : Program)
    (layout : ObjectLayout) (base : Nat) : Option Yul.Program := do
  let resolved ← program.resolveObjectBuiltinsWithLocalDataBase? layout base
  resolved.toYulProgram?

noncomputable def toObjectsWithLocalDataBase? (program : Program)
    (layout : ObjectLayout) (base : Nat) : Option Objects.Program := do
  let root ← Object.toObjectsWithLocalDataBase? program.object layout base
  some { root := root }

def toObjectsUncheckedWithLocalDataBase? (program : Program)
    (layout : ObjectLayout) (base : Nat) : Option Objects.Program := do
  let root ← Object.toObjectsUncheckedWithLocalDataBase?
    program.object layout base
  some { root := root }

def compileUncheckedWithLocalDataBase? (program : Program)
    (layout : ObjectLayout) (base : Nat) : Option Assembly.TargetProgram := do
  let lower ← program.toObjectsUncheckedWithLocalDataBase? layout base
  Objects.Program.compile? lower

def bytecodeUncheckedWithLocalDataBase? (program : Program)
    (layout : ObjectLayout) (base : Nat) : Option ByteArray := do
  let target ← program.compileUncheckedWithLocalDataBase? layout base
  some (Assembly.Bytecode.encodeTarget target)

def bytecodeImageUnchecked? (program : Program) : Option ByteArray :=
  program.object.bytecodeUncheckedImage?

def bytecodeImageUncheckedWithLinkerSymbols?
    (program : Program) (linkerSymbols : List (Name × Word)) :
    Option ByteArray :=
  program.object.bytecodeUncheckedImageWithLinkerSymbols? linkerSymbols

end Program

end Frontend
end Solidity
end EvmCompiler
