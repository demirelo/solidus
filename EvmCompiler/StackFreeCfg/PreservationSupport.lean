import EvmCompiler.StackFreeCfg.Compiler
import EvmCompiler.StackFreeCfg.Contract
import EvmCompiler.TypedCfg.Contract

namespace EvmCompiler
namespace StackFreeCfg
namespace PreservationSupport

/-!
Compositional proof support for the adjacent StackFreeCfg -> TypedCfg pass.

This module is intentionally internal to that adjacent boundary: it may mention
`TypedCfg.Shape`, slots, and runtime stacks, but it does not change the
source-facing `StackFreeCfg` semantics and should not be imported by higher
layers directly.
-/

abbrev Shape :=
  TypedCfg.Shape

abbrev Label :=
  TypedCfg.Label

def StoreScoped (scope : List Name) (vars : Store.T) : Prop :=
  ∀ name, name ∉ scope → vars name = none

namespace StoreScoped

theorem empty (scope : List Name) :
    StoreScoped scope Store.empty := by
  intro _name _hNotMem
  rfl

theorem restrictTo (scope : List Name) (vars : Store.T) :
    StoreScoped scope (Store.restrictTo scope vars) := by
  intro name hNotMem
  simp [Store.restrictTo, hNotMem]

theorem mono_scope {inner outer : List Name} {vars : Store.T}
    (hSubset : ∀ name, name ∈ inner → name ∈ outer)
    (hScoped : StoreScoped inner vars) :
    StoreScoped outer vars := by
  intro name hNotMem
  exact hScoped name (fun hMem => hNotMem (hSubset name hMem))

theorem restrictTo_eq_self {scope : List Name} {vars : Store.T}
    (hScoped : StoreScoped scope vars) :
    Store.restrictTo scope vars = vars := by
  funext name
  by_cases hMem : name ∈ scope
  · simp [Store.restrictTo, hMem]
  · simp [Store.restrictTo, hMem, hScoped name hMem]

theorem insert_of_mem {scope : List Name} {vars : Store.T}
    {name : Name} {value : Word}
    (hMem : name ∈ scope)
    (hScoped : StoreScoped scope vars) :
    StoreScoped scope (Store.insert vars name value) := by
  intro key hNotMem
  by_cases hEq : key = name
  · subst key
    exact False.elim (hNotMem hMem)
  · simp [Store.insert, hEq, hScoped key hNotMem]

theorem insertMany_of_mem {scope names : List Name} {values : List Word}
    {vars vars' : Store.T}
    (hNames : ∀ name, name ∈ names → name ∈ scope)
    (hScoped : StoreScoped scope vars)
    (hInsert : Store.insertMany names values vars = some vars') :
    StoreScoped scope vars' := by
  induction names generalizing values vars vars' with
  | nil =>
      cases values with
      | nil =>
          change some vars = some vars' at hInsert
          cases hInsert
          exact hScoped
      | cons _value _values =>
          change (none : Option Store.T) = some vars' at hInsert
          cases hInsert
  | cons name names ih =>
      cases values with
      | nil =>
          change (none : Option Store.T) = some vars' at hInsert
          cases hInsert
      | cons value values =>
          change Store.insertMany names values (Store.insert vars name value) =
            some vars' at hInsert
          have hHead : name ∈ scope := hNames name (by simp)
          have hTail : ∀ key, key ∈ names → key ∈ scope := by
            intro key hMem
            exact hNames key (by simp [hMem])
          exact ih hTail (insert_of_mem hHead hScoped) hInsert

theorem assignMany_of_mem {scope names : List Name} {values : List Word}
    {vars vars' : Store.T}
    (hNames : ∀ name, name ∈ names → name ∈ scope)
    (hScoped : StoreScoped scope vars)
    (hAssign : Store.assignMany names values vars = some vars') :
    StoreScoped scope vars' := by
  induction names generalizing values vars vars' with
  | nil =>
      cases values with
      | nil =>
          change some vars = some vars' at hAssign
          cases hAssign
          exact hScoped
      | cons _value _values =>
          change (none : Option Store.T) = some vars' at hAssign
          cases hAssign
  | cons name names ih =>
      cases values with
      | nil =>
          change (none : Option Store.T) = some vars' at hAssign
          cases hAssign
      | cons value values =>
          by_cases hContains : Store.contains vars name
          · simp [Store.assignMany, hContains] at hAssign
            have hHead : name ∈ scope := hNames name (by simp)
            have hTail : ∀ key, key ∈ names → key ∈ scope := by
              intro key hMem
              exact hNames key (by simp [hMem])
            exact ih hTail (insert_of_mem hHead hScoped) hAssign
          · simp [Store.assignMany, hContains] at hAssign

end StoreScoped

namespace Store

theorem insertMany_length_eq {names : List Name} {values : List Word}
    {vars vars' : Store.T}
    (hInsert : Store.insertMany names values vars = some vars') :
    names.length = values.length := by
  induction names generalizing values vars vars' with
  | nil =>
      cases values with
      | nil =>
          exact rfl
      | cons _value _values =>
          change (none : Option Store.T) = some vars' at hInsert
          cases hInsert
  | cons name names ih =>
      cases values with
      | nil =>
          change (none : Option Store.T) = some vars' at hInsert
          cases hInsert
      | cons value values =>
          change Store.insertMany names values (Store.insert vars name value) =
            some vars' at hInsert
          simpa using ih hInsert

theorem insertMany_lookup_of_not_mem {key : Name} {names : List Name}
    {values : List Word}
    {vars vars' : Store.T}
    (hNotMem : key ∉ names)
    (hInsert : Store.insertMany names values vars = some vars') :
    vars' key = vars key := by
  induction names generalizing values vars vars' with
  | nil =>
      cases values with
      | nil =>
          change some vars = some vars' at hInsert
          cases hInsert
          rfl
      | cons _value _values =>
          change (none : Option Store.T) = some vars' at hInsert
          cases hInsert
  | cons name names ih =>
      cases values with
      | nil =>
          change (none : Option Store.T) = some vars' at hInsert
          cases hInsert
      | cons value values =>
          change Store.insertMany names values (Store.insert vars name value) =
            some vars' at hInsert
          have hKeyNe : key ≠ name := by
            intro hEq
            exact hNotMem (by simp [hEq])
          have hTailNot : key ∉ names := by
            intro hMem
            exact hNotMem (by simp [hMem])
          rw [ih hTailNot hInsert]
          simp [Store.insert, hKeyNe]

end Store

namespace State

theorem insertMany?_scoped {scope names : List Name} {values : List Word}
    {state state' : State}
    (hNames : ∀ name, name ∈ names → name ∈ scope)
    (hScoped : StoreScoped scope state.vars)
    (hInsert : state.insertMany? names values = some state') :
    StoreScoped scope state'.vars := by
  unfold State.insertMany? at hInsert
  cases hVars : Store.insertMany names values state.vars with
  | none =>
      simp [hVars] at hInsert
  | some vars' =>
      simp [hVars] at hInsert
      cases hInsert
      exact StoreScoped.insertMany_of_mem hNames hScoped hVars

theorem assignMany?_scoped {scope names : List Name} {values : List Word}
    {state state' : State}
    (hNames : ∀ name, name ∈ names → name ∈ scope)
    (hScoped : StoreScoped scope state.vars)
    (hAssign : state.assignMany? names values = some state') :
    StoreScoped scope state'.vars := by
  unfold State.assignMany? at hAssign
  cases hVars : Store.assignMany names values state.vars with
  | none =>
      simp [hVars] at hAssign
  | some vars' =>
      simp [hVars] at hAssign
      cases hAssign
      exact StoreScoped.assignMany_of_mem hNames hScoped hVars

end State

namespace ShapeNames

def slot : TypedCfg.Slot → List Name
  | .local name => [name]
  | .returnValue name _index => [name]
  | .word | .literal _ | .temp _ _ | .returnPC _ => []

def shape : Shape → List Name
  | [] => []
  | slot :: rest => ShapeNames.slot slot ++ shape rest

end ShapeNames

def SlotMatchesStore (vars : Store.T) :
    TypedCfg.Slot → Word → Prop
  | .literal expected, value =>
      (TypedCfg.Slot.literal expected).matchesValue value = true
  | .local name, value => vars name = some value
  | .word, _value => True
  | .temp _scope _index, _value => True
  | .returnPC _site, _value => True
  | .returnValue name _index, value => vars name = some value

def ShapeMatchesStore (vars : Store.T) :
    Shape → EvmYul.Stack Word → Prop
  | [], [] => True
  | slot :: shapeRest, value :: stackRest =>
      SlotMatchesStore vars slot value ∧
        ShapeMatchesStore vars shapeRest stackRest
  | _, _ => False

namespace SlotMatchesStore

theorem matchesValue {vars : Store.T} {slot : TypedCfg.Slot} {value : Word}
    (h : SlotMatchesStore vars slot value) :
    slot.matchesValue value = true := by
  cases slot <;> simp [SlotMatchesStore, TypedCfg.Slot.matchesValue] at h ⊢
  exact h

theorem changeVars {vars vars' : Store.T} {slot : TypedCfg.Slot}
    {value : Word}
    (hAgree : ∀ name, name ∈ ShapeNames.slot slot → vars' name = vars name)
    (h : SlotMatchesStore vars slot value) :
    SlotMatchesStore vars' slot value := by
  cases slot with
  | word => trivial
  | literal expected =>
      simpa [SlotMatchesStore] using h
  | «local» name =>
      simp [SlotMatchesStore, ShapeNames.slot] at hAgree h ⊢
      rw [hAgree]
      exact h
  | temp _scope _index => trivial
  | returnPC _site => trivial
  | returnValue name _index =>
      simp [SlotMatchesStore, ShapeNames.slot] at hAgree h ⊢
      rw [hAgree]
      exact h

end SlotMatchesStore

namespace ShapeMatchesStore

theorem length_eq {vars : Store.T} {shape : Shape}
    {stack : EvmYul.Stack Word}
    (h : ShapeMatchesStore vars shape stack) :
    shape.length = stack.length := by
  induction shape generalizing stack with
  | nil =>
      cases stack with
      | nil => rfl
      | cons _ _ => simp [ShapeMatchesStore] at h
  | cons _slot rest ih =>
      cases stack with
      | nil =>
          simp [ShapeMatchesStore] at h
      | cons _value stackRest =>
          simp [ShapeMatchesStore] at h
          simpa using ih h.2

theorem matchesStack {vars : Store.T} {shape : Shape}
    {stack : EvmYul.Stack Word}
    (h : ShapeMatchesStore vars shape stack) :
    shape.matchesStack stack = true := by
  induction shape generalizing stack with
  | nil =>
      cases stack with
      | nil => rfl
      | cons _ _ => simp [ShapeMatchesStore] at h
  | cons slot rest ih =>
      cases stack with
      | nil =>
          simp [ShapeMatchesStore] at h
      | cons value stackRest =>
          simp [ShapeMatchesStore] at h
          simp [TypedCfg.Shape.matchesStack,
            SlotMatchesStore.matchesValue h.1, ih h.2]

theorem append {vars : Store.T} {shape1 shape2 : Shape}
    {stack1 stack2 : EvmYul.Stack Word}
    (h1 : ShapeMatchesStore vars shape1 stack1)
    (h2 : ShapeMatchesStore vars shape2 stack2) :
    ShapeMatchesStore vars (shape1 ++ shape2) (stack1 ++ stack2) := by
  induction shape1 generalizing stack1 with
  | nil =>
      cases stack1 with
      | nil => simpa using h2
      | cons _ _ => simp [ShapeMatchesStore] at h1
  | cons slot rest ih =>
      cases stack1 with
      | nil =>
          simp [ShapeMatchesStore] at h1
      | cons value stackRest =>
          simp [ShapeMatchesStore] at h1 ⊢
          exact ⟨h1.1, ih h1.2⟩

theorem pushWords {vars : Store.T} {n : Nat} {values : List Word}
    {shape : Shape} {stack : EvmYul.Stack Word}
    (hLen : values.length = n)
    (h : ShapeMatchesStore vars shape stack) :
    ShapeMatchesStore vars (TypedCfg.Shape.pushWords n shape)
      (values ++ stack) := by
  rw [← hLen]
  clear hLen n
  induction values with
  | nil =>
      simpa [TypedCfg.Shape.pushWords] using h
  | cons _value rest ih =>
      change True ∧
        ShapeMatchesStore vars
          (List.replicate rest.length TypedCfg.Slot.word ++ shape)
          (rest ++ stack)
      exact ⟨trivial, by simpa [TypedCfg.Shape.pushWords] using ih⟩

theorem changeVars {vars vars' : Store.T} {shape : Shape}
    {stack : EvmYul.Stack Word}
    (hAgree : ∀ name, name ∈ ShapeNames.shape shape → vars' name = vars name)
    (h : ShapeMatchesStore vars shape stack) :
    ShapeMatchesStore vars' shape stack := by
  induction shape generalizing stack with
  | nil =>
      cases stack with
      | nil => trivial
      | cons _ _ => simp [ShapeMatchesStore] at h
  | cons slot rest ih =>
      cases stack with
      | nil =>
          simp [ShapeMatchesStore] at h
      | cons value stackRest =>
          simp [ShapeMatchesStore] at h ⊢
          constructor
          · exact SlotMatchesStore.changeVars
              (vars := vars) (vars' := vars') (slot := slot)
              (value := value)
              (by
                intro name hMem
                exact hAgree name (by
                  simp [ShapeNames.shape, hMem]))
              h.1
          · exact ih
              (by
                intro name hMem
                exact hAgree name (by
                  simp [ShapeNames.shape, hMem]))
              h.2

theorem changeVars_of_insertMany_disjoint {vars vars' : Store.T}
    {names : List Name} {values : List Word} {shape : Shape}
    {stack : EvmYul.Stack Word}
    (hDisjoint : ∀ name, name ∈ ShapeNames.shape shape → name ∉ names)
    (hInsert : Store.insertMany names values vars = some vars')
    (h : ShapeMatchesStore vars shape stack) :
    ShapeMatchesStore vars' shape stack :=
  changeVars
    (by
      intro name hMem
      exact Store.insertMany_lookup_of_not_mem
        (hDisjoint name hMem) hInsert)
    h

theorem locals_of_insertMany {names : List Name} {values : List Word}
    {vars vars' : Store.T}
    (hNoDup : names.Nodup)
    (hInsert : Store.insertMany names values vars = some vars') :
    ShapeMatchesStore vars' (Compiler.Layout.locals names) values := by
  induction names generalizing values vars vars' with
  | nil =>
      cases values with
      | nil =>
          trivial
      | cons _value _values =>
          change (none : Option Store.T) = some vars' at hInsert
          cases hInsert
  | cons name names ih =>
      cases values with
      | nil =>
          change (none : Option Store.T) = some vars' at hInsert
          cases hInsert
      | cons value values =>
          change Store.insertMany names values (Store.insert vars name value) =
            some vars' at hInsert
          have hTailNoDup : names.Nodup := hNoDup.tail
          have hNameNotMem : name ∉ names := by
            exact hNoDup.notMem
          simp [Compiler.Layout.locals, ShapeMatchesStore, SlotMatchesStore]
          constructor
          · rw [Store.insertMany_lookup_of_not_mem hNameNotMem hInsert]
            simp [Store.insert]
          · exact ih hTailNoDup hInsert

end ShapeMatchesStore

structure StateRel (scope : List Name) (shape : Shape)
    (source : State) (target : TypedCfg.RunState) : Prop where
  store_scoped : StoreScoped scope source.vars
  shared_eq : target.evm.toSharedState = source.shared
  stack : ShapeMatchesStore source.vars shape target.evm.stack

namespace StateRel

theorem shared_eq_of {scope : List Name} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (h : StateRel scope shape source target) :
    target.evm.toSharedState = source.shared :=
  h.shared_eq

theorem block_input_matches {scope : List Name} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (h : StateRel scope shape source target) :
    shape.matchesStack target.evm.stack = true :=
  ShapeMatchesStore.matchesStack h.stack

theorem restrictSource {scope : List Name} {shape : Shape}
    {source : State} {target : TypedCfg.RunState}
    (h : StateRel scope shape source target) :
    StateRel scope shape (source.restrictTo scope) target := by
  constructor
  · exact StoreScoped.restrictTo scope source.vars
  · simp [State.restrictTo, h.shared_eq]
  · exact ShapeMatchesStore.changeVars
      (vars := source.vars) (vars' := Store.restrictTo scope source.vars)
      (by
        intro name _hMem
        by_cases hMemScope : name ∈ scope
        · simp [Store.restrictTo, hMemScope]
        · simp [Store.restrictTo, hMemScope, h.store_scoped name hMemScope])
      h.stack

end StateRel

namespace ExprCompiler

theorem compileN?_shape {expr : StackFreeCfg.Expr} {shape outShape : Shape}
    {code : List TypedCfg.Instr} {n : Nat}
    (h : StackFreeCfg.Compiler.Expr.compileN? expr shape n =
      some (code, outShape)) :
    outShape.length = shape.length + n ∧ outShape.drop n = shape := by
  unfold StackFreeCfg.Compiler.Expr.compileN? at h
  cases hCompile : StackFreeCfg.Compiler.Expr.compile? expr shape with
  | none =>
      simp [hCompile] at h
  | some result =>
      cases result with
      | mk code' outShape' =>
          by_cases hCheck :
              outShape'.length = shape.length + n ∧
                outShape'.drop n = shape
          · simp [hCompile, hCheck] at h
            rw [← h.2]
            exact hCheck
          · simp [hCompile, hCheck] at h

theorem compileOne?_shape {expr : StackFreeCfg.Expr} {shape outShape : Shape}
    {code : List TypedCfg.Instr}
    (h : StackFreeCfg.Compiler.Expr.compileOne? expr shape =
      some (code, outShape)) :
    ∃ slot, outShape = slot :: shape := by
  unfold StackFreeCfg.Compiler.Expr.compileOne? at h
  cases hCompile : StackFreeCfg.Compiler.Expr.compile? expr shape with
  | none =>
      simp [hCompile] at h
  | some result =>
      cases result with
      | mk code' outShape' =>
          cases outShape' with
          | nil =>
              simp [hCompile] at h
          | cons slot rest =>
              by_cases hRest : rest = shape
              · simp [hCompile, hRest] at h
                rcases h with ⟨_hCode, hShape⟩
                exact ⟨slot, hShape.symm⟩
              · simp [hCompile, hRest] at h

theorem compileCondition?_code {expr : StackFreeCfg.Expr}
    {shape : Shape} {code : List TypedCfg.Instr}
    (h : StackFreeCfg.Compiler.Expr.compileCondition? expr shape = some code) :
    ∃ slot, StackFreeCfg.Compiler.Expr.compileOne? expr shape =
      some (code, slot :: shape) := by
  unfold StackFreeCfg.Compiler.Expr.compileCondition? at h
  cases hCompile : StackFreeCfg.Compiler.Expr.compileOne? expr shape with
  | none =>
      simp [hCompile] at h
  | some result =>
      cases result with
      | mk code' outShape =>
          cases outShape with
          | nil =>
              simp [hCompile] at h
          | cons slot rest =>
              by_cases hRest : rest = shape
              · simp [hCompile, hRest] at h
                cases h
                exact ⟨slot, by simp [hRest]⟩
              · simp [hCompile, hRest] at h

end ExprCompiler

namespace StmtCode

theorem declareLocals_type?_shape {names : List Name} {valueShape shape outShape : Shape}
    (hDrop : valueShape.drop names.length = shape)
    (hType :
      (TypedCfg.Instr.declareLocals names).type? valueShape =
        some outShape) :
    outShape = Compiler.Layout.locals names ++ shape := by
  unfold TypedCfg.Instr.type? at hType
  by_cases hLe : names.length ≤ valueShape.length
  · simp [hLe] at hType
    have hRest : TypedCfg.Shape.pop names.length valueShape = shape := by
      simpa [TypedCfg.Shape.pop] using hDrop
    rw [← hType.2]
    simp [Compiler.Layout.locals, TypedCfg.Instr.ShapeOps.locals, hRest]
  · simp [hLe] at hType

theorem assignLocals_type?_shape {names : List Name} {valueShape shape outShape : Shape}
    (hDrop : valueShape.drop names.length = shape)
    (hType :
      (TypedCfg.Instr.assignLocals names).type? valueShape =
        some outShape) :
    outShape = shape := by
  unfold TypedCfg.Instr.type? at hType
  by_cases hLe : names.length ≤ valueShape.length
  · simp [hLe] at hType
    rw [← hType.2]
    simpa [TypedCfg.Shape.pop] using hDrop
  · simp [hLe] at hType

theorem decl?_shape {names : List Name} {value? : Option Expr}
    {shape outShape : Shape} {code : List TypedCfg.Instr}
    (h :
      Compiler.StmtCode.decl? names value? shape = some (code, outShape)) :
    outShape = Compiler.Layout.locals names ++ shape := by
  unfold Compiler.StmtCode.decl? at h
  cases value? with
  | none =>
      cases hType :
          (TypedCfg.Instr.declareLocals names).type?
            (List.replicate names.length (TypedCfg.Slot.literal zero) ++
              shape) with
      | none =>
          simp [hType] at h
      | some typedShape =>
          simp [hType] at h
          rw [← h.2]
          have hDrop :
              (List.replicate names.length (TypedCfg.Slot.literal zero) ++
                shape).drop names.length = shape := by
            induction names with
            | nil => rfl
            | cons _ names ih =>
                simp [List.replicate]
          exact declareLocals_type?_shape hDrop hType
  | some value =>
      cases hCompile :
          Compiler.Expr.compileN? value shape names.length with
      | none =>
          simp [hCompile] at h
      | some result =>
          cases result with
          | mk valueCode valueShape =>
              cases hType :
                  (TypedCfg.Instr.declareLocals names).type? valueShape with
              | none =>
                  simp [hCompile, hType] at h
              | some typedShape =>
                  simp [hCompile, hType] at h
                  rw [← h.2]
                  exact
                    declareLocals_type?_shape
                      (ExprCompiler.compileN?_shape hCompile).2 hType

theorem assign?_shape {names : List Name} {value : Expr}
    {shape outShape : Shape} {code : List TypedCfg.Instr}
    (h :
      Compiler.StmtCode.assign? names value shape =
        some (code, outShape)) :
    outShape = shape := by
  unfold Compiler.StmtCode.assign? at h
  cases hCompile :
      Compiler.Expr.compileN? value shape names.length with
  | none =>
      simp [hCompile] at h
  | some result =>
      cases result with
      | mk valueCode valueShape =>
          cases hType :
              (TypedCfg.Instr.assignLocals names).type? valueShape with
          | none =>
              simp [hCompile, hType] at h
          | some typedShape =>
              simp [hCompile, hType] at h
              rw [← h.2]
              exact
                assignLocals_type?_shape
                  (ExprCompiler.compileN?_shape hCompile).2 hType

end StmtCode

end PreservationSupport
end StackFreeCfg
end EvmCompiler
