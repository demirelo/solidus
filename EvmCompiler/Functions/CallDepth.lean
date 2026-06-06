import EvmCompiler.Functions.Compiler
import EvmCompiler.Functions.SourceDirect
import EvmCompiler.Structured.Preservation

namespace EvmCompiler
namespace Functions
namespace CallDepth

namespace List

def maxNat : List Nat → Nat
  | [] => 0
  | head :: rest => max head (maxNat rest)

def maxOptionNat? : List (Option Nat) → Option Nat
  | [] => some 0
  | none :: _rest => none
  | some head :: rest => do
      let tail ← maxOptionNat? rest
      some (max head tail)

end List

mutual
  def blockInternalCalls : Block → List Name
    | ⟨stmts⟩ => stmtListInternalCalls stmts

  def stmtInternalCalls : Stmt → List Name
    | .expr _ => []
    | .let_ _ _ => []
    | .assign _ _ => []
    | .block body => blockInternalCalls body
    | .if_ _ body => blockInternalCalls body
    | .switch _ cases defaultBody =>
        caseListInternalCalls cases ++ defaultInternalCalls defaultBody
    | .for_ init _ post body =>
        blockInternalCalls init ++ blockInternalCalls post ++
          blockInternalCalls body
    | .brk | .cont | .leave => []
    | .call _targets functionName _args => [functionName]
    | .terminal _ => []
    | .terminalArgs _ _ => []

  def stmtListInternalCalls : List Stmt → List Name
    | [] => []
    | stmt :: rest => stmtInternalCalls stmt ++ stmtListInternalCalls rest

  def caseListInternalCalls : List (Word × Block) → List Name
    | [] => []
    | (_value, body) :: rest =>
        blockInternalCalls body ++ caseListInternalCalls rest

  def defaultInternalCalls : Option Block → List Name
    | none => []
    | some body => blockInternalCalls body
end

namespace FunDef

def internalCalls (fn : FunDef) : List Name :=
  blockInternalCalls fn.body

/--
Worst-case number of source stack words added by one hidden return frame for a
call to this function, assuming the function arguments have already been
split off the visible EVM stack.
-/
def sourceReturnFrameWords (fn : FunDef) : Nat :=
  17 - fn.params.length

end FunDef

namespace FunList

def maxSourceReturnFrameWords : List FunDef → Nat
  | [] => 0
  | fn :: rest =>
      max (FunDef.sourceReturnFrameWords fn)
        (maxSourceReturnFrameWords rest)

theorem sourceReturnFrameWords_le_max_of_find?
    {name : Name} :
    ∀ {functions : List FunDef} {fn : FunDef},
      FunList.find? name functions = some fn →
        FunDef.sourceReturnFrameWords fn ≤
          maxSourceReturnFrameWords functions
  | [], _fn, hFind => by
      simp [FunList.find?] at hFind
  | head :: rest, fn, hFind => by
      by_cases hName : head.name = name
      · simp [FunList.find?, hName] at hFind
        cases hFind
        exact Nat.le_max_left (FunDef.sourceReturnFrameWords head)
          (maxSourceReturnFrameWords rest)
      · simp [FunList.find?, hName] at hFind
        have hTail :=
          sourceReturnFrameWords_le_max_of_find? (functions := rest)
            (fn := fn) hFind
        change FunDef.sourceReturnFrameWords fn ≤
          max (FunDef.sourceReturnFrameWords head)
            (maxSourceReturnFrameWords rest)
        exact Nat.le_trans hTail
          (Nat.le_max_right (FunDef.sourceReturnFrameWords head)
            (maxSourceReturnFrameWords rest))

end FunList

inductive FunctionPath (functions : List FunDef) : Name → Nat → Prop where
  | here {name : Name} {fn : FunDef}
      (hFind : FunList.find? name functions = some fn) :
      FunctionPath functions name 0
  | call {name callee : Name} {fn : FunDef} {depth : Nat}
      (hFind : FunList.find? name functions = some fn)
      (hCall : callee ∈ FunDef.internalCalls fn)
      (hTail : FunctionPath functions callee depth) :
      FunctionPath functions name (depth + 1)

inductive FunctionPathFrameWords (functions : List FunDef) :
    Name → Nat → Prop where
  | here {name : Name} {fn : FunDef}
      (hFind : FunList.find? name functions = some fn) :
      FunctionPathFrameWords functions name
        (FunDef.sourceReturnFrameWords fn)
  | call {name callee : Name} {fn : FunDef} {tailWords : Nat}
      (hFind : FunList.find? name functions = some fn)
      (hCall : callee ∈ FunDef.internalCalls fn)
      (hTail : FunctionPathFrameWords functions callee tailWords) :
      FunctionPathFrameWords functions name
        (FunDef.sourceReturnFrameWords fn + tailWords)

inductive FunctionPathFrameWordsTo (functions : List FunDef) :
    Name → Name → Nat → Prop where
  | here {name : Name} {fn : FunDef}
      (hFind : FunList.find? name functions = some fn) :
      FunctionPathFrameWordsTo functions name name
        (FunDef.sourceReturnFrameWords fn)
  | call {name callee target : Name} {fn : FunDef} {tailWords : Nat}
      (hFind : FunList.find? name functions = some fn)
      (hCall : callee ∈ FunDef.internalCalls fn)
      (hTail : FunctionPathFrameWordsTo functions callee target tailWords) :
      FunctionPathFrameWordsTo functions name target
        (FunDef.sourceReturnFrameWords fn + tailWords)

inductive FunctionPathTo (functions : List FunDef) :
    Name → Name → Nat → Prop where
  | here {name : Name} {fn : FunDef}
      (hFind : FunList.find? name functions = some fn) :
      FunctionPathTo functions name name 0
  | call {name callee target : Name} {fn : FunDef} {depth : Nat}
      (hFind : FunList.find? name functions = some fn)
      (hCall : callee ∈ FunDef.internalCalls fn)
      (hTail : FunctionPathTo functions callee target depth) :
      FunctionPathTo functions name target (depth + 1)

namespace FunctionPathTo

theorem toFunctionPath {functions : List FunDef}
    {root target : Name} {depth : Nat}
    (hPath : FunctionPathTo functions root target depth) :
    FunctionPath functions root depth := by
  induction hPath with
  | here hFind =>
      exact FunctionPath.here hFind
  | call hFind hCall _hTail hTailPath =>
      exact FunctionPath.call hFind hCall hTailPath

theorem snoc {functions : List FunDef}
    {root current callee : Name} {depth : Nat}
    (hPath : FunctionPathTo functions root current depth)
    {currentFn calleeFn : FunDef}
    (hCurrentFind : FunList.find? current functions = some currentFn)
    (hCall : callee ∈ FunDef.internalCalls currentFn)
    (hCalleeFind : FunList.find? callee functions = some calleeFn) :
    FunctionPathTo functions root callee (depth + 1) := by
  induction hPath generalizing callee currentFn calleeFn with
  | here _hFind =>
      exact
        FunctionPathTo.call hCurrentFind hCall
          (FunctionPathTo.here hCalleeFind)
  | call hFind hHeadCall _hTail hTailSnoc =>
      exact
        FunctionPathTo.call hFind hHeadCall
          (hTailSnoc hCurrentFind hCall hCalleeFind)

end FunctionPathTo

namespace FunctionPathFrameWordsTo

theorem toFunctionPathFrameWords {functions : List FunDef}
    {root target : Name} {words : Nat}
    (hPath : FunctionPathFrameWordsTo functions root target words) :
    FunctionPathFrameWords functions root words := by
  induction hPath with
  | here hFind =>
      exact FunctionPathFrameWords.here hFind
  | call hFind hCall _hTail hTailPath =>
      exact FunctionPathFrameWords.call hFind hCall hTailPath

theorem snoc {functions : List FunDef}
    {root current callee : Name} {words : Nat}
    (hPath : FunctionPathFrameWordsTo functions root current words)
    {currentFn calleeFn : FunDef}
    (hCurrentFind : FunList.find? current functions = some currentFn)
    (hCall : callee ∈ FunDef.internalCalls currentFn)
    (hCalleeFind : FunList.find? callee functions = some calleeFn) :
    FunctionPathFrameWordsTo functions root callee
      (words + FunDef.sourceReturnFrameWords calleeFn) := by
  induction hPath generalizing callee currentFn calleeFn with
  | here hFind =>
      rw [hFind] at hCurrentFind
      cases hCurrentFind
      exact
        FunctionPathFrameWordsTo.call hFind hCall
          (FunctionPathFrameWordsTo.here hCalleeFind)
  | call hFind hHeadCall _hTail hTailSnoc =>
      simpa [Nat.add_assoc] using
        FunctionPathFrameWordsTo.call hFind hHeadCall
          (hTailSnoc hCurrentFind hCall hCalleeFind)

end FunctionPathFrameWordsTo

namespace Program

def mainInternalCalls (program : Program) : List Name :=
  blockInternalCalls program.body

def maxSourceReturnFrameWords (program : Program) : Nat :=
  FunList.maxSourceReturnFrameWords program.functions

theorem sourceReturnFrameWords_le_max_of_find?
    {program : Program} {name : Name} {fn : FunDef}
    (hFind : FunList.find? name program.functions = some fn) :
    FunDef.sourceReturnFrameWords fn ≤
      maxSourceReturnFrameWords program :=
  FunList.sourceReturnFrameWords_le_max_of_find? hFind

mutual
  def maxDepthFrom? (functions : List FunDef) :
      Nat → List Name → Name → Option Nat
    | 0, _stack, _name => none
    | fuel + 1, stack, name =>
        if name ∈ stack then
          none
        else
          match FunList.find? name functions with
          | none => none
          | some fn =>
              maxDepthCalls? functions fuel (name :: stack)
                (FunDef.internalCalls fn)

  def maxDepthCalls? (functions : List FunDef) :
      Nat → List Name → List Name → Option Nat
    | _fuel, _stack, [] => some 0
    | fuel, stack, name :: rest => do
        let headDepth ← maxDepthFrom? functions fuel stack name
        let tailDepth ← maxDepthCalls? functions fuel stack rest
        some (max (headDepth + 1) tailDepth)
end

/--
Maximum active internal return-frame depth reachable from the program body.

The result counts internal call edges, not the main frame.  Cycles and
unresolved function names return `none`.
-/
def maxInternalCallDepth? (program : Program) : Option Nat :=
  maxDepthCalls? program.functions (program.functions.length + 1) []
    (mainInternalCalls program)

mutual
  def maxFrameWordsFrom? (functions : List FunDef) :
      Nat → List Name → Name → Option Nat
    | 0, _stack, _name => none
    | fuel + 1, stack, name =>
        if name ∈ stack then
          none
        else
          match FunList.find? name functions with
          | none => none
          | some fn => do
              let tailWords ← maxFrameWordsCalls? functions fuel
                (name :: stack) (FunDef.internalCalls fn)
              some (FunDef.sourceReturnFrameWords fn + tailWords)

  def maxFrameWordsCalls? (functions : List FunDef) :
      Nat → List Name → List Name → Option Nat
    | _fuel, _stack, [] => some 0
    | fuel, stack, name :: rest => do
        let headWords ← maxFrameWordsFrom? functions fuel stack name
        let tailWords ← maxFrameWordsCalls? functions fuel stack rest
        some (max headWords tailWords)
end

/--
Maximum accumulated hidden-return-frame words reachable from the program body.

Unlike `maxSourceReturnFrameWords * maxInternalCallDepth`, this sums the actual
per-callee hidden frame sizes along each acyclic path and takes the maximum over
branches. Cycles and unresolved function names return `none`.
-/
def maxActiveFrameWords? (program : Program) : Option Nat :=
  maxFrameWordsCalls? program.functions (program.functions.length + 1) []
    (mainInternalCalls program)

mutual
  theorem maxDepthFrom?_sound (functions : List FunDef) :
      ∀ {fuel : Nat} {stack : List Name} {name : Name}
        {depth pathLen : Nat},
        maxDepthFrom? functions fuel stack name = some depth →
        FunctionPath functions name pathLen →
          pathLen ≤ depth
    | 0, _stack, _name, _depth, _pathLen, hDepth, _hPath => by
        simp [maxDepthFrom?] at hDepth
    | fuel + 1, stack, name, depth, pathLen, hDepth, hPath => by
        unfold maxDepthFrom? at hDepth
        by_cases hCycle : name ∈ stack
        · simp [hCycle] at hDepth
        · simp [hCycle] at hDepth
          cases hFind : FunList.find? name functions with
          | none =>
              simp [hFind] at hDepth
          | some fn =>
              simp [hFind] at hDepth
              cases hPath with
              | here hPathFind =>
                  exact Nat.zero_le depth
              | call hPathFind hCall hTail =>
                  rw [hFind] at hPathFind
                  cases hPathFind
                  exact
                    maxDepthCalls?_sound functions hDepth hCall hTail
  termination_by fuel _ _ _ _ => (fuel, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem maxDepthCalls?_sound (functions : List FunDef) :
      ∀ {fuel : Nat} {stack calls : List Name} {depth : Nat}
        {name : Name} {pathLen : Nat},
        maxDepthCalls? functions fuel stack calls = some depth →
        name ∈ calls →
        FunctionPath functions name pathLen →
          pathLen + 1 ≤ depth
    | fuel, stack, [], _depth, _name, _pathLen, _hDepth, hMem, _hPath => by
        simp at hMem
    | fuel, stack, head :: rest, depth, name, pathLen, hDepth, hMem,
        hPath => by
        unfold maxDepthCalls? at hDepth
        cases hHead :
            maxDepthFrom? functions fuel stack head with
        | none =>
            simp [hHead] at hDepth
        | some headDepth =>
            cases hTail :
                maxDepthCalls? functions fuel stack rest with
            | none =>
                simp [hHead, hTail] at hDepth
            | some tailDepth =>
                simp [hHead, hTail] at hDepth
                cases hDepth
                have hMem' : name = head ∨ name ∈ rest := by
                  simpa using hMem
                rcases hMem' with hName | hRest
                · cases hName
                  have hBound :=
                    maxDepthFrom?_sound functions hHead hPath
                  omega
                · have hBound :=
                    maxDepthCalls?_sound functions hTail hRest hPath
                  omega
  termination_by fuel _ calls _ _ _ => (fuel, calls.length + 1)
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  theorem maxFrameWordsFrom?_sound (functions : List FunDef) :
      ∀ {fuel : Nat} {stack : List Name} {name : Name}
        {bound pathWords : Nat},
        maxFrameWordsFrom? functions fuel stack name = some bound →
        FunctionPathFrameWords functions name pathWords →
          pathWords ≤ bound
    | 0, _stack, _name, _bound, _pathWords, hBound, _hPath => by
        simp [maxFrameWordsFrom?] at hBound
    | fuel + 1, stack, name, bound, pathWords, hBound, hPath => by
        unfold maxFrameWordsFrom? at hBound
        by_cases hCycle : name ∈ stack
        · simp [hCycle] at hBound
        · simp [hCycle] at hBound
          cases hFind : FunList.find? name functions with
          | none =>
              simp [hFind] at hBound
          | some fn =>
              simp [hFind] at hBound
              cases hCalls :
                  maxFrameWordsCalls? functions fuel (name :: stack)
                    (FunDef.internalCalls fn) with
              | none =>
                  simp [hCalls] at hBound
              | some tailBound =>
                  simp [hCalls] at hBound
                  cases hPath with
                  | here hPathFind =>
                      rw [hFind] at hPathFind
                      cases hPathFind
                      omega
                  | call hPathFind hCall hTail =>
                      rw [hFind] at hPathFind
                      cases hPathFind
                      have hTailBound :=
                        maxFrameWordsCalls?_sound functions hCalls hCall
                          hTail
                      omega
  termination_by fuel _ _ _ _ => (fuel, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem maxFrameWordsCalls?_sound (functions : List FunDef) :
      ∀ {fuel : Nat} {stack calls : List Name} {bound : Nat}
        {name : Name} {pathWords : Nat},
        maxFrameWordsCalls? functions fuel stack calls = some bound →
        name ∈ calls →
        FunctionPathFrameWords functions name pathWords →
          pathWords ≤ bound
    | fuel, stack, [], _bound, _name, _pathWords, _hBound, hMem,
        _hPath => by
        simp at hMem
    | fuel, stack, head :: rest, bound, name, pathWords, hBound, hMem,
        hPath => by
        unfold maxFrameWordsCalls? at hBound
        cases hHead :
            maxFrameWordsFrom? functions fuel stack head with
        | none =>
            simp [hHead] at hBound
        | some headBound =>
            cases hTail :
                maxFrameWordsCalls? functions fuel stack rest with
            | none =>
                simp [hHead, hTail] at hBound
            | some tailBound =>
                simp [hHead, hTail] at hBound
                cases hBound
                have hMem' : name = head ∨ name ∈ rest := by
                  simpa using hMem
                rcases hMem' with hName | hRest
                · cases hName
                  have hBound :=
                    maxFrameWordsFrom?_sound functions hHead hPath
                  omega
                · have hBound :=
                    maxFrameWordsCalls?_sound functions hTail hRest hPath
                  omega
  termination_by fuel _ calls _ _ _ => (fuel, calls.length + 1)
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

theorem maxInternalCallDepth?_sound
    {program : Program} {depth : Nat}
    (hDepth : maxInternalCallDepth? program = some depth)
    {name : Name} {pathLen : Nat}
    (hRoot : name ∈ mainInternalCalls program)
    (hPath : FunctionPath program.functions name pathLen) :
    pathLen + 1 ≤ depth :=
  maxDepthCalls?_sound program.functions hDepth hRoot hPath

theorem maxActiveFrameWords?_sound
    {program : Program} {bound : Nat}
    (hBound : maxActiveFrameWords? program = some bound)
    {name : Name} {pathWords : Nat}
    (hRoot : name ∈ mainInternalCalls program)
    (hPath : FunctionPathFrameWords program.functions name pathWords) :
    pathWords ≤ bound :=
  maxFrameWordsCalls?_sound program.functions hBound hRoot hPath

theorem maxInternalCallDepth?_pathTo_bound
    {program : Program} {depth : Nat}
    (hDepth : maxInternalCallDepth? program = some depth)
    {root target : Name} {pathLen : Nat}
    (hRoot : root ∈ mainInternalCalls program)
    (hPath : FunctionPathTo program.functions root target pathLen) :
    pathLen + 1 ≤ depth :=
  maxInternalCallDepth?_sound hDepth hRoot hPath.toFunctionPath

def stackBudgetOk? (depth : Nat) : Bool :=
  decide (16 + 17 * depth + 17 ≤ 1024)

def stackFrameWordSumBudgetOk? (frameWords : Nat) : Bool :=
  decide (16 + frameWords + 17 ≤ 1024)

def stackFrameWordSumVisibleBudgetOk? (visibleWords frameWords : Nat) :
    Bool :=
  decide (visibleWords + frameWords + 17 ≤ 1024)

structure StackDepthCheckResult (program : Program) : Type where
  depth : Nat
  checked : maxInternalCallDepth? program = some depth
  budget : 16 + 17 * depth + 17 ≤ 1024

structure StackFrameWordSumCheckResult (program : Program) : Type where
  frameWords : Nat
  checked : maxActiveFrameWords? program = some frameWords
  budget : 16 + frameWords + 17 ≤ 1024

structure StackFrameWordSumVisibleCheckResult (program : Program)
    (visibleWords : Nat) : Type where
  frameWords : Nat
  checked : maxActiveFrameWords? program = some frameWords
  budget : visibleWords + frameWords + 17 ≤ 1024

def stackDepthCheck? (program : Program) :
    Option (StackDepthCheckResult program) :=
  match hDepth : maxInternalCallDepth? program with
  | none => none
  | some depth =>
      if hBudget : 16 + 17 * depth + 17 ≤ 1024 then
        some
          { depth := depth
            checked := hDepth
            budget := hBudget }
      else
        none

def stackFrameWordSumCheck? (program : Program) :
    Option (StackFrameWordSumCheckResult program) :=
  match hFrameWords : maxActiveFrameWords? program with
  | none => none
  | some frameWords =>
      if hBudget : 16 + frameWords + 17 ≤ 1024 then
        some
          { frameWords := frameWords
            checked := hFrameWords
            budget := hBudget }
      else
        none

def stackFrameWordSumVisibleCheck? (program : Program)
    (visibleWords : Nat) :
    Option (StackFrameWordSumVisibleCheckResult program visibleWords) :=
  match hFrameWords : maxActiveFrameWords? program with
  | none => none
  | some frameWords =>
      if hBudget : visibleWords + frameWords + 17 ≤ 1024 then
        some
          { frameWords := frameWords
            checked := hFrameWords
            budget := hBudget }
      else
        none

theorem stackDepthCheck?_eq_some
    {program : Program} {check : StackDepthCheckResult program}
    (_hCheck : stackDepthCheck? program = some check) :
    maxInternalCallDepth? program = some check.depth ∧
      16 + 17 * check.depth + 17 ≤ 1024 := by
  exact ⟨check.checked, check.budget⟩

theorem stackFrameWordSumCheck?_eq_some
    {program : Program} {check : StackFrameWordSumCheckResult program}
    (_hCheck : stackFrameWordSumCheck? program = some check) :
    maxActiveFrameWords? program = some check.frameWords ∧
      16 + check.frameWords + 17 ≤ 1024 := by
  exact ⟨check.checked, check.budget⟩

theorem stackFrameWordSumVisibleCheck?_eq_some
    {program : Program} {visibleWords : Nat}
    {check : StackFrameWordSumVisibleCheckResult program visibleWords}
    (_hCheck :
      stackFrameWordSumVisibleCheck? program visibleWords = some check) :
    maxActiveFrameWords? program = some check.frameWords ∧
      visibleWords + check.frameWords + 17 ≤ 1024 := by
  exact ⟨check.checked, check.budget⟩

theorem StackDepthCheckResult.path_bound
    {program : Program} (check : StackDepthCheckResult program)
    {name : Name} {pathLen : Nat}
    (hRoot : name ∈ mainInternalCalls program)
    (hPath : FunctionPath program.functions name pathLen) :
    pathLen + 1 ≤ check.depth :=
  maxInternalCallDepth?_sound check.checked hRoot hPath

theorem StackFrameWordSumCheckResult.path_words_bound
    {program : Program} (check : StackFrameWordSumCheckResult program)
    {name : Name} {pathWords : Nat}
    (hRoot : name ∈ mainInternalCalls program)
    (hPath : FunctionPathFrameWords program.functions name pathWords) :
    pathWords ≤ check.frameWords :=
  maxActiveFrameWords?_sound check.checked hRoot hPath

theorem StackFrameWordSumVisibleCheckResult.path_words_bound
    {program : Program} {visibleWords : Nat}
    (check : StackFrameWordSumVisibleCheckResult program visibleWords)
    {name : Name} {pathWords : Nat}
    (hRoot : name ∈ mainInternalCalls program)
    (hPath : FunctionPathFrameWords program.functions name pathWords) :
    pathWords ≤ check.frameWords :=
  maxActiveFrameWords?_sound check.checked hRoot hPath

theorem StackDepthCheckResult.pathTo_bound
    {program : Program} (check : StackDepthCheckResult program)
    {root target : Name} {pathLen : Nat}
    (hRoot : root ∈ mainInternalCalls program)
    (hPath : FunctionPathTo program.functions root target pathLen) :
    pathLen + 1 ≤ check.depth :=
  maxInternalCallDepth?_pathTo_bound check.checked hRoot hPath

inductive ActiveCallChain (program : Program) : List Name → Prop where
  | main :
      ActiveCallChain program []
  | root {name : Name} {fn : FunDef}
      (hRoot : name ∈ mainInternalCalls program)
      (hFind : FunList.find? name program.functions = some fn) :
      ActiveCallChain program [name]
  | push {active : List Name} {caller callee : Name}
      (hActive : ActiveCallChain program active)
      (hCaller : active.getLast? = some caller)
      {callerFn calleeFn : FunDef}
      (hCallerFind :
        FunList.find? caller program.functions = some callerFn)
      (hCall : callee ∈ FunDef.internalCalls callerFn)
      (hCalleeFind :
        FunList.find? callee program.functions = some calleeFn) :
      ActiveCallChain program (active ++ [callee])

namespace ActiveCallChain

theorem path {program : Program} :
    ∀ {active : List Name},
      ActiveCallChain program active →
        active = [] ∨
          ∃ root current pathLen,
            root ∈ mainInternalCalls program ∧
              active.getLast? = some current ∧
              active.length = pathLen + 1 ∧
              FunctionPathTo program.functions root current pathLen
  | _active, hChain => by
      induction hChain with
      | main =>
          exact Or.inl rfl
      | root hRoot hFind =>
          exact
            Or.inr
              ⟨_, _, 0, hRoot, by simp, by simp,
                FunctionPathTo.here hFind⟩
      | push hActive hCaller hCallerFind hCall hCalleeFind ih =>
          rcases ih with hEmpty | hPath
          · cases hEmpty
            simp at hCaller
          · rcases hPath with
              ⟨root, current, pathLen, hRoot, hLast, hLength, hPathTo⟩
            rw [hLast] at hCaller
            cases hCaller
            exact
              Or.inr
                ⟨root, _, pathLen + 1, hRoot, by simp,
                  by simp [hLength],
                  FunctionPathTo.snoc hPathTo hCallerFind hCall
                    hCalleeFind⟩

end ActiveCallChain

structure ActiveCallStack (program : Program)
    (active : List Name) : Prop where
  chain : ActiveCallChain program active

namespace ActiveCallStack

theorem main {program : Program} :
    ActiveCallStack program [] where
  chain := ActiveCallChain.main

theorem root {program : Program} {name : Name} {fn : FunDef}
    (hRoot : name ∈ mainInternalCalls program)
    (hFind : FunList.find? name program.functions = some fn) :
    ActiveCallStack program [name] where
  chain := ActiveCallChain.root hRoot hFind

theorem push {program : Program}
    {active : List Name} {caller callee : Name}
    (hActive : ActiveCallStack program active)
    (hCaller : active.getLast? = some caller)
    {callerFn calleeFn : FunDef}
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn) :
    ActiveCallStack program (active ++ [callee]) where
  chain :=
    ActiveCallChain.push hActive.chain hCaller hCallerFind hCall
      hCalleeFind

theorem path {program : Program} {active : List Name}
    (hActive : ActiveCallStack program active) :
    active = [] ∨
      ∃ root current pathLen,
        root ∈ mainInternalCalls program ∧
          active.getLast? = some current ∧
          active.length = pathLen + 1 ∧
          FunctionPathTo program.functions root current pathLen :=
  hActive.chain.path

theorem length_le_depth {program : Program}
    (check : StackDepthCheckResult program)
    {active : List Name}
    (hActive : ActiveCallStack program active) :
    active.length ≤ check.depth := by
  rcases hActive.path with hEmpty | hPath
  · cases hEmpty
    simp
  · rcases hPath with
      ⟨root, current, pathLen, hRoot, _hLast, hLength, hPathTo⟩
    have hBound := check.pathTo_bound hRoot hPathTo
    omega

theorem push_length_le_depth {program : Program}
    (check : StackDepthCheckResult program)
    {active : List Name} {caller callee : Name}
    (hActive : ActiveCallStack program active)
    (hCaller : active.getLast? = some caller)
    {callerFn calleeFn : FunDef}
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn) :
    (active ++ [callee]).length ≤ check.depth :=
  length_le_depth check
    (push hActive hCaller hCallerFind hCall hCalleeFind)

end ActiveCallStack

inductive ActiveCallFrameWords (program : Program) :
    List Name → Nat → Prop where
  | main :
      ActiveCallFrameWords program [] 0
  | root {name : Name} {fn : FunDef}
      (hRoot : name ∈ mainInternalCalls program)
      (hFind : FunList.find? name program.functions = some fn) :
      ActiveCallFrameWords program [name]
        (FunDef.sourceReturnFrameWords fn)
  | push {active : List Name} {words : Nat} {caller callee : Name}
      (hActive : ActiveCallFrameWords program active words)
      (hCaller : active.getLast? = some caller)
      {callerFn calleeFn : FunDef}
      (hCallerFind :
        FunList.find? caller program.functions = some callerFn)
      (hCall : callee ∈ FunDef.internalCalls callerFn)
      (hCalleeFind :
        FunList.find? callee program.functions = some calleeFn) :
      ActiveCallFrameWords program (active ++ [callee])
        (words + FunDef.sourceReturnFrameWords calleeFn)

namespace ActiveCallFrameWords

theorem toActiveCallStack {program : Program} :
    ∀ {active : List Name} {words : Nat},
      ActiveCallFrameWords program active words →
        ActiveCallStack program active
  | _active, _words, hWords => by
      induction hWords with
      | main =>
          exact ActiveCallStack.main
      | root hRoot hFind =>
          exact ActiveCallStack.root hRoot hFind
      | push _hActive hCaller hCallerFind hCall hCalleeFind ih =>
          exact
            ActiveCallStack.push ih hCaller hCallerFind hCall hCalleeFind

theorem path {program : Program} :
    ∀ {active : List Name} {words : Nat},
      ActiveCallFrameWords program active words →
        (active = [] ∧ words = 0) ∨
          ∃ root current,
            root ∈ mainInternalCalls program ∧
              active.getLast? = some current ∧
              FunctionPathFrameWordsTo program.functions root current words
  | _active, _words, hWords => by
      induction hWords with
      | main =>
          exact Or.inl ⟨rfl, rfl⟩
      | root hRoot hFind =>
          exact
            Or.inr
              ⟨_, _, hRoot, by simp,
                FunctionPathFrameWordsTo.here hFind⟩
      | push _hActive hCaller hCallerFind hCall hCalleeFind ih =>
          rcases ih with hEmpty | hPath
          · rcases hEmpty with ⟨hActiveEmpty, _hWordsZero⟩
            rw [hActiveEmpty] at hCaller
            simp at hCaller
          · rcases hPath with
              ⟨root, current, hRoot, hLast, hPathTo⟩
            rw [hLast] at hCaller
            cases hCaller
            exact
              Or.inr
                ⟨root, _, hRoot, by simp,
                  FunctionPathFrameWordsTo.snoc hPathTo hCallerFind hCall
                    hCalleeFind⟩

theorem words_le_check {program : Program}
    (check : StackFrameWordSumCheckResult program)
    {active : List Name} {words : Nat}
    (hWords : ActiveCallFrameWords program active words) :
    words ≤ check.frameWords := by
  rcases hWords.path with hEmpty | hPath
  · rcases hEmpty with ⟨hActive, hWordsEq⟩
    subst active
    subst words
    exact Nat.zero_le check.frameWords
  · rcases hPath with ⟨root, _current, hRoot, _hLast, hPathTo⟩
    exact check.path_words_bound hRoot hPathTo.toFunctionPathFrameWords

theorem words_le_visible_check {program : Program} {visibleWords : Nat}
    (check : StackFrameWordSumVisibleCheckResult program visibleWords)
    {active : List Name} {words : Nat}
    (hWords : ActiveCallFrameWords program active words) :
    words ≤ check.frameWords := by
  rcases hWords.path with hEmpty | hPath
  · rcases hEmpty with ⟨hActive, hWordsEq⟩
    subst active
    subst words
    exact Nat.zero_le check.frameWords
  · rcases hPath with ⟨root, _current, hRoot, _hLast, hPathTo⟩
    exact check.path_words_bound hRoot hPathTo.toFunctionPathFrameWords

end ActiveCallFrameWords

end Program

structure StackBudget : Type where
  depth : Nat
  budget : 16 + 17 * depth + 17 ≤ 1024

structure FrameWordStackBudget : Type where
  depth : Nat
  frameWords : Nat
  budget : 16 + frameWords * depth + 17 ≤ 1024

namespace StackBudget

def toFrameWordStackBudget (budget : StackBudget) :
    FrameWordStackBudget where
  depth := budget.depth
  frameWords := 17
  budget := budget.budget

end StackBudget

namespace Program.StackDepthCheckResult

def toStackBudget {program : Program}
    (check : Program.StackDepthCheckResult program) :
    StackBudget where
  depth := check.depth
  budget := check.budget

end Program.StackDepthCheckResult

structure HiddenReturnsShape (depth : Nat)
    (returns : List Structured.ReturnDest) : Prop where
  lengthLe : returns.length ≤ depth
  callersLe :
    ∀ frame, frame ∈ returns → frame.callerStack.length ≤ 16

namespace HiddenReturnsShape

theorem nil (depth : Nat) :
    HiddenReturnsShape depth [] where
  lengthLe := by simp
  callersLe := by
    intro frame hMem
    simp at hMem

theorem cons {depth : Nat} {frame : Structured.ReturnDest}
    {returns : List Structured.ReturnDest}
    (hCaller : frame.callerStack.length ≤ 16)
    (hTail : HiddenReturnsShape depth returns) :
    HiddenReturnsShape (depth + 1) (frame :: returns) where
  lengthLe := by
    have hLen := hTail.lengthLe
    simp
    omega
  callersLe := by
    intro candidate hMem
    have hMem' : candidate = frame ∨ candidate ∈ returns := by
      simpa using hMem
    rcases hMem' with hHead | hTailMem
    · cases hHead
      exact hCaller
    · exact hTail.callersLe candidate hTailMem

theorem weaken {depth depth' : Nat}
    {returns : List Structured.ReturnDest}
    (hShape : HiddenReturnsShape depth returns)
    (hLe : depth ≤ depth') :
    HiddenReturnsShape depth' returns where
  lengthLe := le_trans hShape.lengthLe hLe
  callersLe := hShape.callersLe

theorem tail_of_cons {depth : Nat} {frame : Structured.ReturnDest}
    {returns : List Structured.ReturnDest}
    (hShape : HiddenReturnsShape (depth + 1) (frame :: returns)) :
    HiddenReturnsShape depth returns where
  lengthLe := by
    have hLen := hShape.lengthLe
    simp at hLen
    omega
  callersLe := by
    intro candidate hMem
    exact hShape.callersLe candidate (by simp [hMem])

theorem cons_of_splitArgs?
    {depth argc retc : Nat}
    {stack args callerStack : EvmYul.Stack Word}
    {returns : List Structured.ReturnDest}
    (hSplit :
      Structured.StackFrame.splitArgs? argc stack =
        some (args, callerStack))
    (hStack : stack.length ≤ 16)
    (hTail : HiddenReturnsShape depth returns) :
    HiddenReturnsShape (depth + 1)
      ({ callerStack := callerStack, retc := retc } :: returns) := by
  have hAppend :=
    Structured.Preservation.Frame.StackFrameFacts.splitArgs?_append hSplit
  have hCaller : callerStack.length ≤ 16 := by
    have hLen : args.length + callerStack.length = stack.length := by
      rw [← hAppend]
      simp
    omega
  exact cons hCaller hTail

theorem of_popReturn? {depth : Nat} {state returned : Structured.RunState}
    {frame : Structured.ReturnDest}
    (hShape : HiddenReturnsShape (depth + 1) state.returns)
    (hPop : state.popReturn? = some (frame, returned)) :
    HiddenReturnsShape depth returned.returns := by
  have hReturns :=
    Structured.Preservation.Frame.RunState.popReturn?_returns_eq hPop
  rw [hReturns] at hShape
  exact tail_of_cons hShape

end HiddenReturnsShape

structure RuntimeFrameShape (depth : Nat)
    (source : Structured.RunState) : Prop where
  visibleLe : source.evm.stack.length ≤ 16
  returnsLe : source.returns.length ≤ depth
  callersLe :
    ∀ frame, frame ∈ source.returns → frame.callerStack.length ≤ 16

namespace RuntimeFrameShape

theorem hiddenReturnsShape {depth : Nat}
    {source : Structured.RunState}
    (hShape : RuntimeFrameShape depth source) :
    HiddenReturnsShape depth source.returns where
  lengthLe := hShape.returnsLe
  callersLe := hShape.callersLe

theorem of_hiddenReturnsShape
    {depth : Nat} {source : Structured.RunState}
    (hVisible : source.evm.stack.length ≤ 16)
    (hHidden : HiddenReturnsShape depth source.returns) :
    RuntimeFrameShape depth source where
  visibleLe := hVisible
  returnsLe := hHidden.lengthLe
  callersLe := hHidden.callersLe

theorem of_sourceDirectStateRel
    {depth : Nat} {layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hHidden : HiddenReturnsShape depth hiddenReturns)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    RuntimeFrameShape depth target := by
  rcases hRel with ⟨hLowerRel, hReturns⟩
  rcases hLowerRel with ⟨_hSharedRel, hStackRel⟩
  have hVisible : target.evm.stack.length ≤ 16 := by
    rw [hStackRel.1]
    exact hLayout
  refine of_hiddenReturnsShape hVisible ?_
  cases hReturns
  exact hHidden

theorem callState_of_splitArgs?
    {depth argc retc : Nat} {state : Structured.RunState}
    {args callerStack : EvmYul.Stack Word}
    (hShape : RuntimeFrameShape depth state)
    (hSplit :
      Structured.StackFrame.splitArgs? argc state.evm.stack =
        some (args, callerStack)) :
    RuntimeFrameShape (depth + 1)
      ((state.withEVM { state.evm with stack := args }).pushReturn
        callerStack retc) := by
  have hAppend :=
    Structured.Preservation.Frame.StackFrameFacts.splitArgs?_append hSplit
  have hArgs : args.length ≤ 16 := by
    have hLen :
        (args ++ callerStack).length = state.evm.stack.length :=
      congrArg List.length hAppend
    simp at hLen
    have hVisible : state.evm.stack.length ≤ 16 := hShape.visibleLe
    omega
  refine of_hiddenReturnsShape ?_ ?_
  · simpa [Structured.RunState.withEVM, Structured.RunState.pushReturn]
      using hArgs
  · simpa [Structured.RunState.withEVM, Structured.RunState.pushReturn]
      using
        HiddenReturnsShape.cons_of_splitArgs?
          (retc := retc) hSplit hShape.visibleLe
          hShape.hiddenReturnsShape

theorem hiddenReturnsShape_of_popReturn?
    {depth : Nat} {state returned : Structured.RunState}
    {frame : Structured.ReturnDest}
    (hShape : RuntimeFrameShape (depth + 1) state)
    (hPop : state.popReturn? = some (frame, returned)) :
    HiddenReturnsShape depth returned.returns :=
  HiddenReturnsShape.of_popReturn? hShape.hiddenReturnsShape hPop

theorem afterAttachReturns?
    {depth : Nat} {state returned : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hShape : RuntimeFrameShape (depth + 1) state)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16) :
    RuntimeFrameShape depth
      (returned.withEVM { state.evm with stack := stack }) := by
  have hStackEq :=
    Structured.Preservation.Frame.StackFrameFacts.attachReturns?_eq
      hAttach
  have hRetLen :=
    Structured.Preservation.Frame.StackFrameFacts.attachReturns?_length
      hAttach
  have hVisible : stack.length ≤ 16 := by
    rw [hStackEq]
    simp [hRetLen]
    omega
  refine of_hiddenReturnsShape ?_ ?_
  · simpa [Structured.RunState.withEVM] using hVisible
  · simpa [Structured.RunState.withEVM] using
      hiddenReturnsShape_of_popReturn? hShape hPop

theorem returnStackWeight_le :
    ∀ {returns : List Structured.ReturnDest},
      (∀ frame, frame ∈ returns → frame.callerStack.length ≤ 16) →
        Structured.Preservation.Frame.returnStackWeight returns ≤
          17 * returns.length
  | [], _hFrames => by
      simp [Structured.Preservation.Frame.returnStackWeight]
  | frame :: rest, hFrames => by
      have hFrame : frame.callerStack.length ≤ 16 := hFrames frame (by simp)
      have hRest :
          Structured.Preservation.Frame.returnStackWeight rest ≤
            17 * rest.length :=
        returnStackWeight_le
          (fun frame hMem => hFrames frame (by simp [hMem]))
      simp [Structured.Preservation.Frame.returnStackWeight]
      omega

theorem returnStackWeight_le_frameWords :
    ∀ {returns : List Structured.ReturnDest} {frameWords : Nat},
      (∀ frame, frame ∈ returns →
        frame.callerStack.length + 1 ≤ frameWords) →
        Structured.Preservation.Frame.returnStackWeight returns ≤
          frameWords * returns.length
  | [], _frameWords, _hFrames => by
      simp [Structured.Preservation.Frame.returnStackWeight]
  | frame :: rest, frameWords, hFrames => by
      have hFrame : frame.callerStack.length + 1 ≤ frameWords :=
        hFrames frame (by simp)
      have hRest :
          Structured.Preservation.Frame.returnStackWeight rest ≤
            frameWords * rest.length :=
        returnStackWeight_le_frameWords
          (fun frame hMem => hFrames frame (by simp [hMem]))
      simp [Structured.Preservation.Frame.returnStackWeight, Nat.mul_succ]
      omega

theorem callerFrameWords_le_of_splitArgs?
    {argc : Nat} {state : Structured.RunState}
    {args callerStack : EvmYul.Stack Word}
    (hSplit :
      Structured.StackFrame.splitArgs? argc state.evm.stack =
        some (args, callerStack))
    (hVisible : state.evm.stack.length ≤ 16) :
    callerStack.length + 1 ≤ 17 - argc := by
  have hAppend :=
    Structured.Preservation.Frame.StackFrameFacts.splitArgs?_append hSplit
  have hArgs :=
    Structured.Preservation.Frame.StackFrameFacts.splitArgs?_args_length
      hSplit
  have hLen :
      args.length + callerStack.length = state.evm.stack.length := by
    rw [← hAppend]
    simp
  omega

theorem callerFrameWords_le_programMax_of_splitArgs?
    {program : Program} {callee : Name} {calleeFn : FunDef}
    {state : Structured.RunState}
    {args callerStack : EvmYul.Stack Word}
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hSplit :
      Structured.StackFrame.splitArgs? calleeFn.params.length
          state.evm.stack =
        some (args, callerStack))
    (hVisible : state.evm.stack.length ≤ 16) :
    callerStack.length + 1 ≤ Program.maxSourceReturnFrameWords program := by
  have hFrame :
      callerStack.length + 1 ≤ FunDef.sourceReturnFrameWords calleeFn :=
    callerFrameWords_le_of_splitArgs? hSplit hVisible
  exact Nat.le_trans hFrame
    (Program.sourceReturnFrameWords_le_max_of_find? hCalleeFind)

theorem callerFrameWords_le_of_argCallerBound
    {argc : Nat} {callerStack : EvmYul.Stack Word}
    (hBound : argc + callerStack.length ≤ 16) :
    callerStack.length + 1 ≤ 17 - argc := by
  omega

theorem callerFrameWords_le_programMax_of_argCallerBound
    {program : Program} {callee : Name} {calleeFn : FunDef}
    {callerStack : EvmYul.Stack Word}
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hBound : calleeFn.params.length + callerStack.length ≤ 16) :
    callerStack.length + 1 ≤ Program.maxSourceReturnFrameWords program := by
  have hFrame :
      callerStack.length + 1 ≤ FunDef.sourceReturnFrameWords calleeFn :=
    callerFrameWords_le_of_argCallerBound hBound
  exact Nat.le_trans hFrame
    (Program.sourceReturnFrameWords_le_max_of_find? hCalleeFind)

theorem sourceStackHeadroomWithFrameWords
    {depth frameWords : Nat} {source : Structured.RunState}
    (hShape : RuntimeFrameShape depth source)
    (hFrames :
      ∀ frame, frame ∈ source.returns →
        frame.callerStack.length + 1 ≤ frameWords)
    (hBudget : 16 + frameWords * depth + 17 ≤ 1024) :
    Structured.Preservation.Frame.SourceStackHeadroom source := by
  unfold Structured.Preservation.Frame.SourceStackHeadroom
  unfold Structured.Preservation.Frame.sourceStackWeight
  have hReturns :=
    returnStackWeight_le_frameWords (returns := source.returns)
      (frameWords := frameWords) hFrames
  have hReturnsLen : source.returns.length ≤ depth := hShape.returnsLe
  have hVisible : source.evm.stack.length ≤ 16 := hShape.visibleLe
  have hDepth :
      Structured.Preservation.Frame.returnStackWeight source.returns ≤
        frameWords * depth := by
    have hMul :
        frameWords * source.returns.length ≤ frameWords * depth := by
      exact Nat.mul_le_mul_left frameWords hReturnsLen
    omega
  omega

theorem sourceStackHeadroom
    {depth : Nat} {source : Structured.RunState}
    (hShape : RuntimeFrameShape depth source)
    (hBudget : 16 + 17 * depth + 17 ≤ 1024) :
    Structured.Preservation.Frame.SourceStackHeadroom source := by
  unfold Structured.Preservation.Frame.SourceStackHeadroom
  unfold Structured.Preservation.Frame.sourceStackWeight
  have hReturns :=
    returnStackWeight_le hShape.callersLe
  have hReturnsLen : source.returns.length ≤ depth := hShape.returnsLe
  have hVisible : source.evm.stack.length ≤ 16 := hShape.visibleLe
  have hDepth :
      Structured.Preservation.Frame.returnStackWeight source.returns ≤
        17 * depth := by
    have hMul :
        17 * source.returns.length ≤ 17 * depth := by
      omega
    omega
  omega

theorem sourceStackWeight_callState_of_splitArgs?
    {argc retc : Nat} {state : Structured.RunState}
    {args callerStack : EvmYul.Stack Word}
    (hSplit :
      Structured.StackFrame.splitArgs? argc state.evm.stack =
        some (args, callerStack)) :
    Structured.Preservation.Frame.sourceStackWeight
      ((state.withEVM { state.evm with stack := args }).pushReturn
        callerStack retc) =
      Structured.Preservation.Frame.sourceStackWeight state + 1 := by
  have hAppend :=
    Structured.Preservation.Frame.StackFrameFacts.splitArgs?_append hSplit
  have hLen :
      args.length + callerStack.length = state.evm.stack.length := by
    rw [← hAppend]
    simp
  simp [Structured.Preservation.Frame.sourceStackWeight,
    Structured.Preservation.Frame.returnStackWeight,
    Structured.RunState.withEVM, Structured.RunState.pushReturn]
  omega

theorem sourceStackWeight_afterAttachReturns?_eq
    {state returned : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack) :
    Structured.Preservation.Frame.sourceStackWeight state =
      Structured.Preservation.Frame.sourceStackWeight
        (returned.withEVM { state.evm with stack := stack }) + 1 := by
  have hReturns :=
    Structured.Preservation.Frame.RunState.popReturn?_returns_eq hPop
  have hStackEq :=
    Structured.Preservation.Frame.StackFrameFacts.attachReturns?_eq hAttach
  have hRetLen :=
    Structured.Preservation.Frame.StackFrameFacts.attachReturns?_length
      hAttach
  have hFinalStack :
      stack.length =
        state.evm.stack.length + frame.callerStack.length := by
    rw [hStackEq]
    simp [hRetLen]
  simp [Structured.Preservation.Frame.sourceStackWeight,
    Structured.Preservation.Frame.returnStackWeight,
    Structured.RunState.withEVM, hReturns, hFinalStack]
  omega

theorem sourceStackHeadroom_of_hiddenReturnsShape
    {depth : Nat} {source : Structured.RunState}
    (hVisible : source.evm.stack.length ≤ 16)
    (hHidden : HiddenReturnsShape depth source.returns)
    (hBudget : 16 + 17 * depth + 17 ≤ 1024) :
    Structured.Preservation.Frame.SourceStackHeadroom source :=
  sourceStackHeadroom
    (of_hiddenReturnsShape hVisible hHidden) hBudget

theorem sourceStackHeadroom_of_sourceDirectStateRel
    {depth : Nat} {layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hHidden : HiddenReturnsShape depth hiddenReturns)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target)
    (hBudget : 16 + 17 * depth + 17 ≤ 1024) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  sourceStackHeadroom
    (of_sourceDirectStateRel hLayout hHidden hRel) hBudget

theorem callState_sourceStackHeadroom_of_splitArgs?
    {depth argc retc : Nat} {state : Structured.RunState}
    {args callerStack : EvmYul.Stack Word}
    (hShape : RuntimeFrameShape depth state)
    (hSplit :
      Structured.StackFrame.splitArgs? argc state.evm.stack =
        some (args, callerStack))
    (hBudget : 16 + 17 * (depth + 1) + 17 ≤ 1024) :
    Structured.Preservation.Frame.SourceStackHeadroom
      ((state.withEVM { state.evm with stack := args }).pushReturn
        callerStack retc) :=
  sourceStackHeadroom
    (callState_of_splitArgs? hShape hSplit) hBudget

theorem afterAttachReturns_sourceStackHeadroom?
    {depth : Nat} {state returned : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hShape : RuntimeFrameShape (depth + 1) state)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16)
    (hBudget : 16 + 17 * depth + 17 ≤ 1024) :
    Structured.Preservation.Frame.SourceStackHeadroom
      (returned.withEVM { state.evm with stack := stack }) :=
  sourceStackHeadroom
    (afterAttachReturns? hShape hPop hAttach hReturnFrameVisible) hBudget

end RuntimeFrameShape

inductive ActiveHiddenFrameWordsContext (program : Program) :
    List Name → List Structured.ReturnDest → Prop where
  | main :
      ActiveHiddenFrameWordsContext program [] []
  | root {callee : Name} {calleeFn : FunDef}
      {frame : Structured.ReturnDest}
      (hRoot : callee ∈ Program.mainInternalCalls program)
      (hCalleeFind :
        FunList.find? callee program.functions = some calleeFn)
      (hFrame :
        frame.callerStack.length + 1 ≤
          FunDef.sourceReturnFrameWords calleeFn) :
      ActiveHiddenFrameWordsContext program [callee] [frame]
  | call {active : List Name}
      {hiddenReturns : List Structured.ReturnDest}
      {caller callee : Name} {callerFn calleeFn : FunDef}
      {frame : Structured.ReturnDest}
      (hContext :
        ActiveHiddenFrameWordsContext program active hiddenReturns)
      (hCaller : active.getLast? = some caller)
      (hCallerFind :
        FunList.find? caller program.functions = some callerFn)
      (hCall : callee ∈ FunDef.internalCalls callerFn)
      (hCalleeFind :
        FunList.find? callee program.functions = some calleeFn)
      (hFrame :
        frame.callerStack.length + 1 ≤
          FunDef.sourceReturnFrameWords calleeFn) :
      ActiveHiddenFrameWordsContext program (active ++ [callee])
        (frame :: hiddenReturns)

namespace ActiveHiddenFrameWordsContext

theorem activeWordsBound {program : Program} :
    ∀ {active : List Name}
      {hiddenReturns : List Structured.ReturnDest},
      ActiveHiddenFrameWordsContext program active hiddenReturns →
        ∃ words,
          Program.ActiveCallFrameWords program active words ∧
            Structured.Preservation.Frame.returnStackWeight hiddenReturns ≤
              words
  | _active, _hiddenReturns, hContext => by
      induction hContext with
      | main =>
          exact
            ⟨0, Program.ActiveCallFrameWords.main, by
              simp [Structured.Preservation.Frame.returnStackWeight]⟩
      | root hRoot hCalleeFind hFrame =>
          exact
            ⟨_, Program.ActiveCallFrameWords.root hRoot hCalleeFind, by
              simpa [Structured.Preservation.Frame.returnStackWeight]
                using hFrame⟩
      | call _hContext hCaller hCallerFind hCall hCalleeFind hFrame ih =>
          rename_i active hiddenReturns caller callee callerFn calleeFn frame
          rcases ih with ⟨words, hWords, hReturns⟩
          refine
            ⟨words + FunDef.sourceReturnFrameWords calleeFn, ?_, ?_⟩
          · exact
              Program.ActiveCallFrameWords.push hWords hCaller hCallerFind
                hCall hCalleeFind
          · have hSum :
                frame.callerStack.length + 1 +
                    Structured.Preservation.Frame.returnStackWeight
                      hiddenReturns ≤
                  words + FunDef.sourceReturnFrameWords calleeFn := by
                omega
            simpa [Structured.Preservation.Frame.returnStackWeight,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSum

theorem returnStackWeight_le_check {program : Program}
    {check : Program.StackFrameWordSumCheckResult program}
    {active : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    (hContext :
      ActiveHiddenFrameWordsContext program active hiddenReturns) :
    Structured.Preservation.Frame.returnStackWeight hiddenReturns ≤
      check.frameWords := by
  rcases hContext.activeWordsBound with
    ⟨words, hActiveWords, hReturnsWeight⟩
  have hWordsLe :
      words ≤ check.frameWords :=
    Program.ActiveCallFrameWords.words_le_check check hActiveWords
  exact Nat.le_trans hReturnsWeight hWordsLe

theorem returnStackWeight_le_visible_check {program : Program}
    {visibleWords : Nat}
    {check : Program.StackFrameWordSumVisibleCheckResult program visibleWords}
    {active : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    (hContext :
      ActiveHiddenFrameWordsContext program active hiddenReturns) :
    Structured.Preservation.Frame.returnStackWeight hiddenReturns ≤
      check.frameWords := by
  rcases hContext.activeWordsBound with
    ⟨words, hActiveWords, hReturnsWeight⟩
  have hWordsLe :
      words ≤ check.frameWords :=
    Program.ActiveCallFrameWords.words_le_visible_check check hActiveWords
  exact Nat.le_trans hReturnsWeight hWordsLe

theorem callersWordsLe_programMax {program : Program}
    {active : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    (hContext :
      ActiveHiddenFrameWordsContext program active hiddenReturns) :
    ∀ frame, frame ∈ hiddenReturns →
      frame.callerStack.length + 1 ≤
        Program.maxSourceReturnFrameWords program := by
  induction hContext with
  | main =>
      intro frame hMem
      simp at hMem
  | root _hRoot hCalleeFind hFrame =>
      intro frame hMem
      simp at hMem
      subst frame
      exact Nat.le_trans hFrame
        (Program.sourceReturnFrameWords_le_max_of_find? hCalleeFind)
  | call _hContext _hCaller _hCallerFind _hCall hCalleeFind hFrame ih =>
      intro frame hMem
      simp at hMem
      rcases hMem with hHead | hTail
      · subst frame
        exact Nat.le_trans hFrame
          (Program.sourceReturnFrameWords_le_max_of_find? hCalleeFind)
      · exact ih frame hTail

theorem afterReturn {program : Program}
    {active : List Name} {callee : Name}
    {frame : Structured.ReturnDest}
    {hiddenReturns : List Structured.ReturnDest}
    (hContext :
      ActiveHiddenFrameWordsContext program (active ++ [callee])
        (frame :: hiddenReturns)) :
    ActiveHiddenFrameWordsContext program active hiddenReturns := by
  generalize hActiveEq : active ++ [callee] = activeStack at hContext
  generalize hReturnsEq : frame :: hiddenReturns = returnsStack at hContext
  cases hContext with
  | main =>
      simp at hActiveEq
  | root _hRoot _hCalleeFind _hFrame =>
      cases active with
      | nil =>
          simp at hReturnsEq
          rcases hReturnsEq with ⟨_hFrameEq, hHiddenEq⟩
          subst hiddenReturns
          exact ActiveHiddenFrameWordsContext.main
      | cons head tail =>
          have hLen := congrArg List.length hActiveEq
          simp at hLen
  | call hContext _hCaller _hCallerFind _hCall _hCalleeFind _hFrame =>
      rename_i priorActive priorHidden priorCaller priorCallee priorCallerFn
        priorCalleeFn priorFrame
      have hActiveLen :
          active.length = priorActive.length := by
        have hLen := congrArg List.length hActiveEq
        simp at hLen
        omega
      have hActivePrefix :
          active = priorActive :=
        List.append_inj_left hActiveEq hActiveLen
      simp at hReturnsEq
      rcases hReturnsEq with ⟨_hFrameEq, hHiddenEq⟩
      subst priorActive
      subst priorHidden
      exact hContext

theorem sourceStackHeadroom {program : Program}
    {check : Program.StackFrameWordSumCheckResult program}
    {active : List Name} {source : Structured.RunState}
    (hContext :
      ActiveHiddenFrameWordsContext program active source.returns)
    (hVisible : source.evm.stack.length ≤ 16) :
    Structured.Preservation.Frame.SourceStackHeadroom source := by
  unfold Structured.Preservation.Frame.SourceStackHeadroom
  unfold Structured.Preservation.Frame.sourceStackWeight
  rcases hContext.activeWordsBound with
    ⟨words, hActiveWords, hReturnsWeight⟩
  have hWordsLe :
      words ≤ check.frameWords :=
    Program.ActiveCallFrameWords.words_le_check check hActiveWords
  have hReturnsLe :
      Structured.Preservation.Frame.returnStackWeight source.returns ≤
        check.frameWords :=
    Nat.le_trans hReturnsWeight hWordsLe
  have hBudget : 16 + check.frameWords + 17 ≤ 1024 := check.budget
  omega

theorem sourceStackHeadroom_of_visible_check {program : Program}
    {visibleWords : Nat}
    {check : Program.StackFrameWordSumVisibleCheckResult program visibleWords}
    {active : List Name} {source : Structured.RunState}
    (hContext :
      ActiveHiddenFrameWordsContext program active source.returns)
    (hVisible : source.evm.stack.length ≤ visibleWords) :
    Structured.Preservation.Frame.SourceStackHeadroom source := by
  unfold Structured.Preservation.Frame.SourceStackHeadroom
  unfold Structured.Preservation.Frame.sourceStackWeight
  rcases hContext.activeWordsBound with
    ⟨words, hActiveWords, hReturnsWeight⟩
  have hWordsLe :
      words ≤ check.frameWords :=
    Program.ActiveCallFrameWords.words_le_visible_check check hActiveWords
  have hReturnsLe :
      Structured.Preservation.Frame.returnStackWeight source.returns ≤
        check.frameWords :=
    Nat.le_trans hReturnsWeight hWordsLe
  have hBudget : visibleWords + check.frameWords + 17 ≤ 1024 :=
    check.budget
  omega

theorem sourceStackHeadroom_of_sourceDirectStateRel {program : Program}
    {check : Program.StackFrameWordSumCheckResult program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      ActiveHiddenFrameWordsContext program active hiddenReturns)
    (hLayout : layout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target := by
  unfold Structured.Preservation.Frame.SourceStackHeadroom
  unfold Structured.Preservation.Frame.sourceStackWeight
  rw [hRel.2]
  rcases hRel.1 with ⟨_hSharedRel, hStackRel⟩
  rcases hContext.activeWordsBound with
    ⟨words, hActiveWords, hReturnsWeight⟩
  have hVisible : target.evm.stack.length ≤ 16 := by
    rw [hStackRel.1]
    exact hLayout
  have hWordsLe :
      words ≤ check.frameWords :=
    Program.ActiveCallFrameWords.words_le_check check hActiveWords
  have hReturnsLe :
      Structured.Preservation.Frame.returnStackWeight hiddenReturns ≤
        check.frameWords :=
    Nat.le_trans hReturnsWeight hWordsLe
  have hBudget : 16 + check.frameWords + 17 ≤ 1024 := check.budget
  omega

theorem sourceStackHeadroom_of_sourceDirectStateRel_visible_check
    {program : Program} {visibleWords : Nat}
    {check : Program.StackFrameWordSumVisibleCheckResult program visibleWords}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      ActiveHiddenFrameWordsContext program active hiddenReturns)
    (hLayout : layout.length ≤ visibleWords)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target := by
  unfold Structured.Preservation.Frame.SourceStackHeadroom
  unfold Structured.Preservation.Frame.sourceStackWeight
  rw [hRel.2]
  rcases hRel.1 with ⟨_hSharedRel, hStackRel⟩
  rcases hContext.activeWordsBound with
    ⟨words, hActiveWords, hReturnsWeight⟩
  have hVisible : target.evm.stack.length ≤ visibleWords := by
    rw [hStackRel.1]
    exact hLayout
  have hWordsLe :
      words ≤ check.frameWords :=
    Program.ActiveCallFrameWords.words_le_visible_check check hActiveWords
  have hReturnsLe :
      Structured.Preservation.Frame.returnStackWeight hiddenReturns ≤
        check.frameWords :=
    Nat.le_trans hReturnsWeight hWordsLe
  have hBudget : visibleWords + check.frameWords + 17 ≤ 1024 :=
    check.budget
  omega

theorem sourceStackHeadroom_of_sourceDirectStateRel_layout_check
    {program : Program}
    {active layout : List Name}
    {check :
      Program.StackFrameWordSumVisibleCheckResult program layout.length}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      ActiveHiddenFrameWordsContext program active hiddenReturns)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  sourceStackHeadroom_of_sourceDirectStateRel_visible_check
    (check := check) hContext (Nat.le_refl layout.length) hRel

end ActiveHiddenFrameWordsContext

structure RuntimeCallStackShape (program : Program)
    (budget : StackBudget)
    (active : List Name)
    (source : Structured.RunState) : Prop where
  activeStack : Program.ActiveCallStack program active
  activeLengthLe : active.length ≤ budget.depth
  visibleLe : source.evm.stack.length ≤ 16
  returnsLength : source.returns.length = active.length
  callersLe :
    ∀ frame, frame ∈ source.returns → frame.callerStack.length ≤ 16

namespace RuntimeCallStackShape

theorem runtimeFrameShape {program : Program}
    {budget : StackBudget}
    {active : List Name} {source : Structured.RunState}
    (hShape : RuntimeCallStackShape program budget active source) :
    RuntimeFrameShape budget.depth source where
  visibleLe := hShape.visibleLe
  returnsLe := by
    rw [hShape.returnsLength]
    exact hShape.activeLengthLe
  callersLe := hShape.callersLe

theorem sourceStackHeadroom {program : Program}
    {budget : StackBudget}
    {active : List Name} {source : Structured.RunState}
    (hShape : RuntimeCallStackShape program budget active source) :
    Structured.Preservation.Frame.SourceStackHeadroom source :=
  RuntimeFrameShape.sourceStackHeadroom hShape.runtimeFrameShape
    budget.budget

theorem of_sourceDirectStateRelWithBound {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hActive : Program.ActiveCallStack program active)
    (hActiveLengthLe : active.length ≤ budget.depth)
    (hLayout : layout.length ≤ 16)
    (hReturnsLength : hiddenReturns.length = active.length)
    (hCallers :
      ∀ frame, frame ∈ hiddenReturns →
        frame.callerStack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    RuntimeCallStackShape program budget active target := by
  rcases hRel with ⟨hLowerRel, hReturns⟩
  rcases hLowerRel with ⟨_hSharedRel, hStackRel⟩
  refine
    { activeStack := hActive
      activeLengthLe := hActiveLengthLe
      visibleLe := ?_
      returnsLength := ?_
      callersLe := ?_ }
  · rw [hStackRel.1]
    exact hLayout
  · rw [hReturns]
    exact hReturnsLength
  · intro frame hMem
    rw [hReturns] at hMem
    exact hCallers frame hMem

theorem of_sourceDirectStateRel {program : Program}
    {check : Program.StackDepthCheckResult program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hActive : Program.ActiveCallStack program active)
    (hLayout : layout.length ≤ 16)
    (hReturnsLength : hiddenReturns.length = active.length)
    (hCallers :
      ∀ frame, frame ∈ hiddenReturns →
        frame.callerStack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    RuntimeCallStackShape program check.toStackBudget active target :=
  of_sourceDirectStateRelWithBound (budget := check.toStackBudget)
    hActive
    (Program.ActiveCallStack.length_le_depth check hActive)
    hLayout hReturnsLength hCallers hRel

theorem main_of_sourceDirectStateRel {program : Program}
    {budget : StackBudget}
    {layout : List Name}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hRel : SourceDirect.StateRel layout [] source target) :
    RuntimeCallStackShape program budget [] target :=
  of_sourceDirectStateRelWithBound
    Program.ActiveCallStack.main (by simp) hLayout (by simp)
    (by
      intro frame hMem
      simp at hMem)
    hRel

theorem sourceStackHeadroom_of_sourceDirectStateRel {program : Program}
    {check : Program.StackDepthCheckResult program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hActive : Program.ActiveCallStack program active)
    (hLayout : layout.length ≤ 16)
    (hReturnsLength : hiddenReturns.length = active.length)
    (hCallers :
      ∀ frame, frame ∈ hiddenReturns →
        frame.callerStack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  sourceStackHeadroom (program := program)
    (budget := check.toStackBudget)
    (of_sourceDirectStateRel (check := check) hActive hLayout
      hReturnsLength hCallers hRel)

theorem main_sourceStackHeadroom_of_sourceDirectStateRel
    {program : Program}
    {check : Program.StackDepthCheckResult program}
    {layout : List Name}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hRel : SourceDirect.StateRel layout [] source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  sourceStackHeadroom (program := program)
    (budget := check.toStackBudget)
    (main_of_sourceDirectStateRel (program := program)
      (budget := check.toStackBudget)
      hLayout hRel)

theorem rootCallState_of_splitArgs? {program : Program}
    {check : Program.StackDepthCheckResult program}
    {callee : Name} {calleeFn : FunDef}
    {argc retc : Nat} {state : Structured.RunState}
    {args callerStack : EvmYul.Stack Word}
    (hShape :
      RuntimeCallStackShape program check.toStackBudget [] state)
    (hRoot : callee ∈ Program.mainInternalCalls program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hSplit :
      Structured.StackFrame.splitArgs? argc state.evm.stack =
        some (args, callerStack)) :
    RuntimeCallStackShape program check.toStackBudget [callee]
      ((state.withEVM { state.evm with stack := args }).pushReturn
        callerStack retc) := by
  have hAppend :=
    Structured.Preservation.Frame.StackFrameFacts.splitArgs?_append
      hSplit
  have hArgs : args.length ≤ 16 := by
    have hLen :
        (args ++ callerStack).length = state.evm.stack.length :=
      congrArg List.length hAppend
    simp at hLen
    have hVisible : state.evm.stack.length ≤ 16 := hShape.visibleLe
    omega
  have hCaller : callerStack.length ≤ 16 := by
    have hLen :
        args.length + callerStack.length = state.evm.stack.length := by
      rw [← hAppend]
      simp
    have hVisible : state.evm.stack.length ≤ 16 := hShape.visibleLe
    omega
  refine
    { activeStack :=
        Program.ActiveCallStack.root hRoot hCalleeFind
      activeLengthLe :=
        Program.ActiveCallStack.length_le_depth check
          (Program.ActiveCallStack.root hRoot hCalleeFind)
      visibleLe := ?_
      returnsLength := ?_
      callersLe := ?_ }
  · simpa [Structured.RunState.withEVM, Structured.RunState.pushReturn]
      using hArgs
  · simp [Structured.RunState.withEVM, Structured.RunState.pushReturn,
      hShape.returnsLength]
  · intro frame hMem
    simp [Structured.RunState.withEVM, Structured.RunState.pushReturn]
      at hMem
    rcases hMem with hHead | hTail
    · cases hHead
      exact hCaller
    · exact hShape.callersLe frame hTail

theorem callState_of_splitArgs? {program : Program}
    {check : Program.StackDepthCheckResult program}
    {active : List Name} {caller callee : Name}
    {callerFn calleeFn : FunDef}
    {argc retc : Nat} {state : Structured.RunState}
    {args callerStack : EvmYul.Stack Word}
    (hShape :
      RuntimeCallStackShape program check.toStackBudget active state)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hSplit :
      Structured.StackFrame.splitArgs? argc state.evm.stack =
        some (args, callerStack)) :
    RuntimeCallStackShape program check.toStackBudget
      (active ++ [callee])
      ((state.withEVM { state.evm with stack := args }).pushReturn
        callerStack retc) := by
  have hAppend :=
    Structured.Preservation.Frame.StackFrameFacts.splitArgs?_append
      hSplit
  have hArgs : args.length ≤ 16 := by
    have hLen :
        (args ++ callerStack).length = state.evm.stack.length :=
      congrArg List.length hAppend
    simp at hLen
    have hVisible : state.evm.stack.length ≤ 16 := hShape.visibleLe
    omega
  have hCallerStack : callerStack.length ≤ 16 := by
    have hLen :
        args.length + callerStack.length = state.evm.stack.length := by
      rw [← hAppend]
      simp
    have hVisible : state.evm.stack.length ≤ 16 := hShape.visibleLe
    omega
  refine
    { activeStack :=
        Program.ActiveCallStack.push hShape.activeStack hCaller
          hCallerFind hCall hCalleeFind
      activeLengthLe :=
        Program.ActiveCallStack.length_le_depth check
          (Program.ActiveCallStack.push hShape.activeStack hCaller
            hCallerFind hCall hCalleeFind)
      visibleLe := ?_
      returnsLength := ?_
      callersLe := ?_ }
  · simpa [Structured.RunState.withEVM, Structured.RunState.pushReturn]
      using hArgs
  · simp [Structured.RunState.withEVM, Structured.RunState.pushReturn,
      hShape.returnsLength]
  · intro frame hMem
    simp [Structured.RunState.withEVM, Structured.RunState.pushReturn]
      at hMem
    rcases hMem with hHead | hTail
    · cases hHead
      exact hCallerStack
    · exact hShape.callersLe frame hTail

theorem afterAttachReturnsWithBound? {program : Program}
    {budget : StackBudget}
    {active : List Name} {callee : Name}
    {state returned : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hShape :
      RuntimeCallStackShape program budget (active ++ [callee]) state)
    (hActive : Program.ActiveCallStack program active)
    (hActiveLengthLe : active.length ≤ budget.depth)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16) :
    RuntimeCallStackShape program budget active
      (returned.withEVM { state.evm with stack := stack }) := by
  have hReturns :=
    Structured.Preservation.Frame.RunState.popReturn?_returns_eq hPop
  have hStackEq :=
    Structured.Preservation.Frame.StackFrameFacts.attachReturns?_eq
      hAttach
  have hRetLen :=
    Structured.Preservation.Frame.StackFrameFacts.attachReturns?_length
      hAttach
  have hVisible : stack.length ≤ 16 := by
    rw [hStackEq]
    simp [hRetLen]
    omega
  have hReturnedLength : returned.returns.length = active.length := by
    have hLength := hShape.returnsLength
    rw [hReturns] at hLength
    simp at hLength
    simpa using hLength
  refine
    { activeStack := hActive
      activeLengthLe := hActiveLengthLe
      visibleLe := ?_
      returnsLength := ?_
      callersLe := ?_ }
  · simpa [Structured.RunState.withEVM] using hVisible
  · simpa [Structured.RunState.withEVM] using hReturnedLength
  · intro candidate hMem
    simp [Structured.RunState.withEVM] at hMem
    exact hShape.callersLe candidate (by
      rw [hReturns]
      simp [hMem])

theorem afterAttachReturns? {program : Program}
    {check : Program.StackDepthCheckResult program}
    {active : List Name} {callee : Name}
    {state returned : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hShape :
      RuntimeCallStackShape program check.toStackBudget
        (active ++ [callee]) state)
    (hActive : Program.ActiveCallStack program active)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16) :
    RuntimeCallStackShape program check.toStackBudget active
      (returned.withEVM { state.evm with stack := stack }) :=
  afterAttachReturnsWithBound? hShape hActive
    (Program.ActiveCallStack.length_le_depth check hActive)
    hPop hAttach hReturnFrameVisible

theorem afterAttachReturns_sourceStackHeadroom? {program : Program}
    {budget : StackBudget}
    {active : List Name} {callee : Name}
    {state returned : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hShape :
      RuntimeCallStackShape program budget (active ++ [callee]) state)
    (hActive : Program.ActiveCallStack program active)
    (hActiveLengthLe : active.length ≤ budget.depth)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16) :
    Structured.Preservation.Frame.SourceStackHeadroom
      (returned.withEVM { state.evm with stack := stack }) :=
  sourceStackHeadroom
    (afterAttachReturnsWithBound? hShape hActive hActiveLengthLe hPop hAttach
      hReturnFrameVisible)

end RuntimeCallStackShape

/--
Budget-free source/direct preservation context.

This records the ordinary value/state relation plus the shape facts needed to
reconstruct a runtime call-stack invariant once a checked source-frame bound is
available.  In particular, it does not itself contain or imply EVM stack
headroom without the extra `active.length <= budget.depth` premise supplied by
the executable recurrence/resource checker.
-/
structure SourceDirectBaseContext (program : Program)
    (active layout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (source : Source.State) (target : Structured.RunState) : Prop where
  stateRel :
    SourceDirect.StateRel layout hiddenReturns source target
  activeStack : Program.ActiveCallStack program active
  layoutLength : layout.length ≤ 16
  hiddenReturnsLength : hiddenReturns.length = active.length
  callersLe :
    ∀ frame, frame ∈ hiddenReturns →
      frame.callerStack.length ≤ 16

namespace SourceDirectBaseContext

theorem visibleLe {program : Program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectBaseContext program active layout hiddenReturns source target) :
    target.evm.stack.length ≤ 16 := by
  rcases hContext.stateRel with ⟨hLowerRel, _hReturns⟩
  rcases hLowerRel with ⟨_hSharedRel, hStackRel⟩
  rw [hStackRel.1]
  exact hContext.layoutLength

theorem runtimeCallStackShape {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectBaseContext program active layout hiddenReturns source target)
    (hActiveLengthLe : active.length ≤ budget.depth) :
    RuntimeCallStackShape program budget active target :=
  RuntimeCallStackShape.of_sourceDirectStateRelWithBound
    hContext.activeStack hActiveLengthLe hContext.layoutLength
    hContext.hiddenReturnsLength hContext.callersLe hContext.stateRel

theorem sourceStackHeadroomWithBound {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectBaseContext program active layout hiddenReturns source target)
    (hActiveLengthLe : active.length ≤ budget.depth) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  (hContext.runtimeCallStackShape
    (budget := budget) hActiveLengthLe).sourceStackHeadroom

theorem main {program : Program}
    {layout : List Name}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hRel : SourceDirect.StateRel layout [] source target) :
    SourceDirectBaseContext program [] layout [] source target where
  stateRel := hRel
  activeStack := Program.ActiveCallStack.main
  layoutLength := hLayout
  hiddenReturnsLength := by simp
  callersLe := by
    intro frame hMem
    simp at hMem

theorem main_sourceStackHeadroomWithBound {program : Program}
    {budget : StackBudget}
    {layout : List Name}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hRel : SourceDirect.StateRel layout [] source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  (main (program := program) hLayout hRel).sourceStackHeadroomWithBound
    (budget := budget) (by simp)

theorem withStateRel {program : Program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectBaseContext program active layout hiddenReturns source
        target)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source' target') :
    SourceDirectBaseContext program active layout hiddenReturns source'
      target' where
  stateRel := hRel
  activeStack := hContext.activeStack
  layoutLength := hContext.layoutLength
  hiddenReturnsLength := hContext.hiddenReturnsLength
  callersLe := hContext.callersLe

theorem withStateRelLayout {program : Program}
    {active layout layout' : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectBaseContext program active layout hiddenReturns source
        target)
    (hLayout' : layout'.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout' hiddenReturns source' target') :
    SourceDirectBaseContext program active layout' hiddenReturns source'
      target' where
  stateRel := hRel
  activeStack := hContext.activeStack
  layoutLength := hLayout'
  hiddenReturnsLength := hContext.hiddenReturnsLength
  callersLe := hContext.callersLe

theorem of_regularBlockScopedOutcomeRel {program : Program}
    {active layout layout' returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectBaseContext program active layout hiddenReturns source
        target)
    (hLayout' : layout'.length ≤ 16)
    (hRel :
      SourceDirect.BlockScopedOutcomeRel returns layout' hiddenReturns
        (Source.Outcome.regular source')
        (Structured.Outcome.regular target')) :
    SourceDirectBaseContext program active layout' hiddenReturns source'
      target' :=
  hContext.withStateRelLayout hLayout'
    (SourceDirect.BlockScopedOutcomeRel.regular_stateRel hRel)

theorem of_regularStmtRunResultRel {program : Program}
    {active layout returns : List Name} {retc : Nat}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hContext :
      SourceDirectBaseContext program active layout hiddenReturns source
        target)
    (hLayout' : targetCtx.layout.length ≤ 16)
    (hRel :
      SourceDirect.StmtRunResultRel retc returns hiddenReturns
        (Source.Outcome.regular source', sourceCtx)
        (Structured.Outcome.regular target', targetCtx)) :
    SourceDirectBaseContext program active targetCtx.layout hiddenReturns
      source' target' :=
  hContext.withStateRelLayout hLayout'
    (SourceDirect.StmtRunResultRel.regular_stateRel hRel).1

theorem of_regularBlockOpenResultRel {program : Program}
    {active layout returns : List Name} {retc : Nat}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hContext :
      SourceDirectBaseContext program active layout hiddenReturns source
        target)
    (hLayout' : targetCtx.layout.length ≤ 16)
    (hRel :
      SourceDirect.BlockOpenResultRel retc returns hiddenReturns
        (Source.Outcome.regular source', sourceCtx)
        (Structured.Outcome.regular target', targetCtx)) :
    SourceDirectBaseContext program active targetCtx.layout hiddenReturns
      source' target' := by
  have hStateRel :
      SourceDirect.StateRel targetCtx.layout hiddenReturns source' target' := by
    simpa [SourceDirect.BlockOpenResultRel, Source.Outcome.regular,
      Locals.Source.Outcome.regular, Structured.Outcome.regular] using
      hRel.1
  exact hContext.withStateRelLayout hLayout' hStateRel

theorem rootCallBody {program : Program}
    {callerLayout calleeLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    (hCaller :
      SourceDirectBaseContext program [] callerLayout [] callerSource
        callerTarget)
    (hRoot : callee ∈ Program.mainInternalCalls program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    SourceDirectBaseContext program [callee] calleeLayout
      [{ callerStack := callerTarget.evm.stack, retc := retc }]
      calleeSource calleeTarget := by
  refine
    { stateRel := hRel
      activeStack := Program.ActiveCallStack.root hRoot hCalleeFind
      layoutLength := hCalleeLayout
      hiddenReturnsLength := ?_
      callersLe := ?_ }
  · simp
  · intro frame hMem
    have hFrame :
        frame =
          { callerStack := callerTarget.evm.stack, retc := retc } := by
      simpa using hMem
    cases hFrame
    exact hCaller.visibleLe

theorem callBody {program : Program}
    {active callerLayout calleeLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      SourceDirectBaseContext program active callerLayout hiddenReturns
        callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    SourceDirectBaseContext program (active ++ [callee]) calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget := by
  refine
    { stateRel := hRel
      activeStack :=
        Program.ActiveCallStack.push hCallerContext.activeStack hCaller
          hCallerFind hCall hCalleeFind
      layoutLength := hCalleeLayout
      hiddenReturnsLength := ?_
      callersLe := ?_ }
  · simp [hCallerContext.hiddenReturnsLength]
  · intro frame hMem
    simp at hMem
    rcases hMem with hHead | hTail
    · cases hHead
      exact hCallerContext.visibleLe
    · exact hCallerContext.callersLe frame hTail

theorem rootCallBodyTargetCtx {program : Program}
    {callerLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    (hCaller :
      SourceDirectBaseContext program [] callerLayout [] callerSource
        callerTarget)
    (hRoot : callee ∈ Program.mainInternalCalls program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeBound : SourceDirect.FrameBound.FunDef calleeFn)
    (hRel :
      SourceDirect.StateRel (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    SourceDirectBaseContext program [callee]
      (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
      [{ callerStack := callerTarget.evm.stack, retc := retc }]
      calleeSource calleeTarget :=
  rootCallBody hCaller hRoot hCalleeFind
    (SourceDirect.FrameBound.funDef_targetBodyCtx_layout_le16 hCalleeBound)
    hRel

theorem callBodyTargetCtx {program : Program}
    {active callerLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      SourceDirectBaseContext program active callerLayout hiddenReturns
        callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeBound : SourceDirect.FrameBound.FunDef calleeFn)
    (hRel :
      SourceDirect.StateRel (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    SourceDirectBaseContext program (active ++ [callee])
      (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget :=
  callBody hCallerContext hCaller hCallerFind hCall hCalleeFind
    (SourceDirect.FrameBound.funDef_targetBodyCtx_layout_le16 hCalleeBound)
    hRel

theorem afterAttachReturns? {program : Program}
    {active : List Name} {callee : Name}
    {calleeLayout callerLayout : List Name}
    {calleeHidden callerHidden : List Structured.ReturnDest}
    {calleeSource callerSource : Source.State}
    {state returned callerTarget : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hCalleeContext :
      SourceDirectBaseContext program (active ++ [callee]) calleeLayout
        calleeHidden calleeSource state)
    (hActive : Program.ActiveCallStack program active)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16)
    (hCallerTarget :
      callerTarget = returned.withEVM { state.evm with stack := stack })
    (hRel :
      SourceDirect.StateRel callerLayout callerHidden callerSource
        callerTarget) :
    SourceDirectBaseContext program active callerLayout callerHidden
      callerSource callerTarget := by
  subst callerTarget
  have hReturns :=
    Structured.Preservation.Frame.RunState.popReturn?_returns_eq hPop
  have hStackEq :=
    Structured.Preservation.Frame.StackFrameFacts.attachReturns?_eq
      hAttach
  have hRetLen :=
    Structured.Preservation.Frame.StackFrameFacts.attachReturns?_length
      hAttach
  have hVisible : stack.length ≤ 16 := by
    rw [hStackEq]
    simp [hRetLen]
    omega
  have hReturnedLength : returned.returns.length = active.length := by
    have hLength := hCalleeContext.hiddenReturnsLength
    rw [← hCalleeContext.stateRel.2] at hLength
    rw [hReturns] at hLength
    simp at hLength
    simpa using hLength
  refine
    { stateRel := hRel
      activeStack := hActive
      layoutLength := ?_
      hiddenReturnsLength := ?_
      callersLe := ?_ }
  · rcases hRel with ⟨hLowerRel, _hRelReturns⟩
    rcases hLowerRel with ⟨_hSharedRel, hStackRel⟩
    rw [← hStackRel.1]
    simpa [Structured.RunState.withEVM] using hVisible
  · have hRelReturns := hRel.2
    rw [← hRelReturns]
    simpa [Structured.RunState.withEVM] using hReturnedLength
  · intro candidate hMem
    have hRelReturns := hRel.2
    rw [← hRelReturns] at hMem
    simp [Structured.RunState.withEVM] at hMem
    exact hCalleeContext.callersLe candidate (by
      rw [← hCalleeContext.stateRel.2]
      rw [hReturns]
      simp [hMem])

end SourceDirectBaseContext

/--
Compatibility context for older proofs that only remember a uniform per-frame
word bound.  Prefer `SourceDirectWeightedFrameContext` for new stack checks:
it keeps the exact hidden-return frame accounting along the active source call
path and only projects to this coarser shape when an older theorem needs it.
-/
structure SourceDirectFrameWordsContext (program : Program)
    (frameWords : Nat)
    (active layout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (source : Source.State) (target : Structured.RunState) : Prop where
  base :
    SourceDirectBaseContext program active layout hiddenReturns source target
  callersWordsLe :
    ∀ frame, frame ∈ hiddenReturns →
      frame.callerStack.length + 1 ≤ frameWords

namespace SourceDirectFrameWordsContext

theorem visibleLe {program : Program} {frameWords : Nat}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectFrameWordsContext program frameWords active layout
        hiddenReturns source target) :
    target.evm.stack.length ≤ 16 :=
  hContext.base.visibleLe

theorem sourceStackHeadroomWithBound {program : Program}
    {budget : FrameWordStackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectFrameWordsContext program budget.frameWords active layout
        hiddenReturns source target)
    (hActiveLengthLe : active.length ≤ budget.depth) :
    Structured.Preservation.Frame.SourceStackHeadroom target := by
  have hHidden : HiddenReturnsShape budget.depth hiddenReturns :=
    { lengthLe := by
        rw [hContext.base.hiddenReturnsLength]
        exact hActiveLengthLe
      callersLe := hContext.base.callersLe }
  have hShape :
      RuntimeFrameShape budget.depth target :=
    RuntimeFrameShape.of_sourceDirectStateRel
      hContext.base.layoutLength hHidden hContext.base.stateRel
  apply RuntimeFrameShape.sourceStackHeadroomWithFrameWords hShape
  · intro frame hMem
    have hReturns := hContext.base.stateRel.2
    rw [hReturns] at hMem
    exact hContext.callersWordsLe frame hMem
  · exact budget.budget

theorem main {program : Program}
    {frameWords : Nat} {layout : List Name}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hRel : SourceDirect.StateRel layout [] source target) :
    SourceDirectFrameWordsContext program frameWords [] layout [] source
      target where
  base := SourceDirectBaseContext.main hLayout hRel
  callersWordsLe := by
    intro frame hMem
    simp at hMem

theorem withStateRel {program : Program}
    {frameWords : Nat}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectFrameWordsContext program frameWords active layout
        hiddenReturns source target)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source' target') :
    SourceDirectFrameWordsContext program frameWords active layout
      hiddenReturns source' target' where
  base := hContext.base.withStateRel hRel
  callersWordsLe := hContext.callersWordsLe

theorem withStateRelLayout {program : Program}
    {frameWords : Nat}
    {active layout layout' : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectFrameWordsContext program frameWords active layout
        hiddenReturns source target)
    (hLayout' : layout'.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout' hiddenReturns source' target') :
    SourceDirectFrameWordsContext program frameWords active layout'
      hiddenReturns source' target' where
  base := hContext.base.withStateRelLayout hLayout' hRel
  callersWordsLe := hContext.callersWordsLe

theorem of_regularBlockScopedOutcomeRel {program : Program}
    {frameWords : Nat}
    {active layout layout' returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectFrameWordsContext program frameWords active layout
        hiddenReturns source target)
    (hLayout' : layout'.length ≤ 16)
    (hRel :
      SourceDirect.BlockScopedOutcomeRel returns layout' hiddenReturns
        (Source.Outcome.regular source')
        (Structured.Outcome.regular target')) :
    SourceDirectFrameWordsContext program frameWords active layout'
      hiddenReturns source' target' :=
  hContext.withStateRelLayout hLayout'
    (SourceDirect.BlockScopedOutcomeRel.regular_stateRel hRel)

theorem of_regularStmtRunResultRel {program : Program}
    {frameWords : Nat}
    {active layout returns : List Name} {retc : Nat}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hContext :
      SourceDirectFrameWordsContext program frameWords active layout
        hiddenReturns source target)
    (hLayout' : targetCtx.layout.length ≤ 16)
    (hRel :
      SourceDirect.StmtRunResultRel retc returns hiddenReturns
        (Source.Outcome.regular source', sourceCtx)
        (Structured.Outcome.regular target', targetCtx)) :
    SourceDirectFrameWordsContext program frameWords active targetCtx.layout
      hiddenReturns source' target' :=
  hContext.withStateRelLayout hLayout'
    (SourceDirect.StmtRunResultRel.regular_stateRel hRel).1

theorem of_regularBlockOpenResultRel {program : Program}
    {frameWords : Nat}
    {active layout returns : List Name} {retc : Nat}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hContext :
      SourceDirectFrameWordsContext program frameWords active layout
        hiddenReturns source target)
    (hLayout' : targetCtx.layout.length ≤ 16)
    (hRel :
      SourceDirect.BlockOpenResultRel retc returns hiddenReturns
        (Source.Outcome.regular source', sourceCtx)
        (Structured.Outcome.regular target', targetCtx)) :
    SourceDirectFrameWordsContext program frameWords active targetCtx.layout
      hiddenReturns source' target' := by
  have hStateRel :
      SourceDirect.StateRel targetCtx.layout hiddenReturns source' target' := by
    simpa [SourceDirect.BlockOpenResultRel, Source.Outcome.regular,
      Locals.Source.Outcome.regular, Structured.Outcome.regular] using
      hRel.1
  exact hContext.withStateRelLayout hLayout' hStateRel

theorem rootCallBody {program : Program}
    {frameWords : Nat}
    {callerLayout calleeLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    (hCaller :
      SourceDirectFrameWordsContext program frameWords [] callerLayout []
        callerSource callerTarget)
    (hRoot : callee ∈ Program.mainInternalCalls program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCallerFrameWords :
      callerTarget.evm.stack.length + 1 ≤ frameWords)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    SourceDirectFrameWordsContext program frameWords [callee] calleeLayout
      [{ callerStack := callerTarget.evm.stack, retc := retc }]
      calleeSource calleeTarget where
  base :=
    SourceDirectBaseContext.rootCallBody hCaller.base hRoot hCalleeFind
      hCalleeLayout hRel
  callersWordsLe := by
    intro frame hMem
    have hFrame :
        frame =
          { callerStack := callerTarget.evm.stack, retc := retc } := by
      simpa using hMem
    cases hFrame
    exact hCallerFrameWords

theorem callBody {program : Program}
    {frameWords : Nat}
    {active callerLayout calleeLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      SourceDirectFrameWordsContext program frameWords active callerLayout
        hiddenReturns callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCallerFrameWords :
      callerTarget.evm.stack.length + 1 ≤ frameWords)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    SourceDirectFrameWordsContext program frameWords (active ++ [callee])
      calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget where
  base :=
    SourceDirectBaseContext.callBody hCallerContext.base hCaller hCallerFind
      hCall hCalleeFind hCalleeLayout hRel
  callersWordsLe := by
    intro frame hMem
    simp at hMem
    rcases hMem with hHead | hTail
    · cases hHead
      exact hCallerFrameWords
    · exact hCallerContext.callersWordsLe frame hTail

theorem rootCallBodyOfArgCallerBound {program : Program}
    {callerLayout calleeLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    (hCaller :
      SourceDirectFrameWordsContext program
        (Program.maxSourceReturnFrameWords program) [] callerLayout []
        callerSource callerTarget)
    (hRoot : callee ∈ Program.mainInternalCalls program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    SourceDirectFrameWordsContext program
      (Program.maxSourceReturnFrameWords program) [callee] calleeLayout
      [{ callerStack := callerTarget.evm.stack, retc := retc }]
      calleeSource calleeTarget :=
  rootCallBody hCaller hRoot hCalleeFind
    (RuntimeFrameShape.callerFrameWords_le_programMax_of_argCallerBound
      hCalleeFind
      hArgCallerBound)
    hCalleeLayout hRel

theorem callBodyOfArgCallerBound {program : Program}
    {active callerLayout calleeLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      SourceDirectFrameWordsContext program
        (Program.maxSourceReturnFrameWords program) active callerLayout
        hiddenReturns callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    SourceDirectFrameWordsContext program
      (Program.maxSourceReturnFrameWords program) (active ++ [callee])
      calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget :=
  callBody hCallerContext hCaller hCallerFind hCall hCalleeFind
    (RuntimeFrameShape.callerFrameWords_le_programMax_of_argCallerBound
      hCalleeFind
      hArgCallerBound)
    hCalleeLayout hRel

theorem rootCallBodyTargetCtxOfArgCallerBound {program : Program}
    {callerLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    (hCaller :
      SourceDirectFrameWordsContext program
        (Program.maxSourceReturnFrameWords program) [] callerLayout []
        callerSource callerTarget)
    (hRoot : callee ∈ Program.mainInternalCalls program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeBound : SourceDirect.FrameBound.FunDef calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    SourceDirectFrameWordsContext program
      (Program.maxSourceReturnFrameWords program) [callee]
      (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
      [{ callerStack := callerTarget.evm.stack, retc := retc }]
      calleeSource calleeTarget :=
  rootCallBodyOfArgCallerBound hCaller hRoot hCalleeFind hArgCallerBound
    (SourceDirect.FrameBound.funDef_targetBodyCtx_layout_le16 hCalleeBound)
    hRel

theorem callBodyTargetCtxOfArgCallerBound {program : Program}
    {active callerLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      SourceDirectFrameWordsContext program
        (Program.maxSourceReturnFrameWords program) active callerLayout
        hiddenReturns callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeBound : SourceDirect.FrameBound.FunDef calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    SourceDirectFrameWordsContext program
      (Program.maxSourceReturnFrameWords program) (active ++ [callee])
      (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget :=
  callBodyOfArgCallerBound hCallerContext hCaller hCallerFind hCall
    hCalleeFind hArgCallerBound
    (SourceDirect.FrameBound.funDef_targetBodyCtx_layout_le16 hCalleeBound)
    hRel

theorem afterAttachReturns? {program : Program}
    {frameWords : Nat}
    {active : List Name} {callee : Name}
    {calleeLayout callerLayout : List Name}
    {calleeHidden callerHidden : List Structured.ReturnDest}
    {calleeSource callerSource : Source.State}
    {state returned callerTarget : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hCalleeContext :
      SourceDirectFrameWordsContext program frameWords (active ++ [callee])
        calleeLayout calleeHidden calleeSource state)
    (hActive : Program.ActiveCallStack program active)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16)
    (hCallerTarget :
      callerTarget = returned.withEVM { state.evm with stack := stack })
    (hRel :
      SourceDirect.StateRel callerLayout callerHidden callerSource
        callerTarget) :
    SourceDirectFrameWordsContext program frameWords active callerLayout
      callerHidden callerSource callerTarget := by
  refine
    { base :=
        SourceDirectBaseContext.afterAttachReturns? hCalleeContext.base
          hActive hPop hAttach hReturnFrameVisible hCallerTarget hRel
      callersWordsLe := ?_ }
  subst callerTarget
  have hReturns :=
    Structured.Preservation.Frame.RunState.popReturn?_returns_eq hPop
  intro candidate hMem
  have hRelReturns := hRel.2
  rw [← hRelReturns] at hMem
  simp [Structured.RunState.withEVM] at hMem
  exact hCalleeContext.callersWordsLe candidate (by
    rw [← hCalleeContext.base.stateRel.2]
    rw [hReturns]
    simp [hMem])

end SourceDirectFrameWordsContext

structure SourceDirectWeightedFrameContext (program : Program)
    (active layout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (source : Source.State) (target : Structured.RunState) : Type where
  base :
    SourceDirectBaseContext program active layout hiddenReturns source target
  hidden :
    ActiveHiddenFrameWordsContext program active hiddenReturns

namespace SourceDirectWeightedFrameContext

theorem toFrameWordsContextProgramMax {program : Program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    SourceDirectFrameWordsContext program
      (Program.maxSourceReturnFrameWords program)
      active layout hiddenReturns source target where
  base := hContext.base
  callersWordsLe := hContext.hidden.callersWordsLe_programMax

theorem sourceStackWeight_le_layout_plus_activeWords {program : Program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    ∃ words,
      Program.ActiveCallFrameWords program active words ∧
        Structured.Preservation.Frame.sourceStackWeight target ≤
          layout.length + words := by
  rcases hContext.hidden.activeWordsBound with
    ⟨words, hActiveWords, hReturnsWeight⟩
  refine ⟨words, hActiveWords, ?_⟩
  unfold Structured.Preservation.Frame.sourceStackWeight
  rw [hContext.base.stateRel.2]
  rcases hContext.base.stateRel.1 with ⟨_hSharedRel, hStackRel⟩
  rw [hStackRel.1]
  exact Nat.add_le_add_left hReturnsWeight layout.length

theorem returnStackWeight_le_checked_frameWords {program : Program}
    {check : Program.StackFrameWordSumCheckResult program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.returnStackWeight hiddenReturns ≤
      check.frameWords :=
  hContext.hidden.returnStackWeight_le_check (check := check)

theorem returnStackWeight_le_visible_checked_frameWords
    {program : Program} {visibleWords : Nat}
    {check : Program.StackFrameWordSumVisibleCheckResult program visibleWords}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.returnStackWeight hiddenReturns ≤
      check.frameWords :=
  hContext.hidden.returnStackWeight_le_visible_check (check := check)

theorem sourceStackWeight_le_layout_plus_checked_frameWords
    {program : Program}
    {check : Program.StackFrameWordSumCheckResult program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.sourceStackWeight target ≤
      layout.length + check.frameWords := by
  rcases hContext.sourceStackWeight_le_layout_plus_activeWords with
    ⟨words, hActiveWords, hWeight⟩
  have hWordsLe :
      words ≤ check.frameWords :=
    Program.ActiveCallFrameWords.words_le_check check hActiveWords
  omega

theorem sourceStackWeight_le_checked_frameWords {program : Program}
    {check : Program.StackFrameWordSumCheckResult program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.sourceStackWeight target ≤
      16 + check.frameWords := by
  have hWeight :=
    hContext.sourceStackWeight_le_layout_plus_checked_frameWords
      (check := check)
  have hLayoutLe : layout.length ≤ 16 := hContext.base.layoutLength
  omega

theorem sourceStackWeight_le_layout_plus_visible_checked_frameWords
    {program : Program} {visibleWords : Nat}
    {check : Program.StackFrameWordSumVisibleCheckResult program visibleWords}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.sourceStackWeight target ≤
      layout.length + check.frameWords := by
  rcases hContext.sourceStackWeight_le_layout_plus_activeWords with
    ⟨words, hActiveWords, hWeight⟩
  have hWordsLe :
      words ≤ check.frameWords :=
    Program.ActiveCallFrameWords.words_le_visible_check check hActiveWords
  omega

theorem sourceStackHeadroom {program : Program}
    {check : Program.StackFrameWordSumCheckResult program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  ActiveHiddenFrameWordsContext.sourceStackHeadroom_of_sourceDirectStateRel
    (check := check) hContext.hidden hContext.base.layoutLength
    hContext.base.stateRel

theorem sourceStackHeadroom_of_visible_check
    {program : Program} {visibleWords : Nat}
    {check : Program.StackFrameWordSumVisibleCheckResult program visibleWords}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target)
    (hLayoutVisible : layout.length ≤ visibleWords) :
    Structured.Preservation.Frame.SourceStackHeadroom target := by
  unfold Structured.Preservation.Frame.SourceStackHeadroom
  have hWeight :
      Structured.Preservation.Frame.sourceStackWeight target ≤
        layout.length + check.frameWords :=
    hContext.sourceStackWeight_le_layout_plus_visible_checked_frameWords
      (check := check)
  have hBudget : visibleWords + check.frameWords + 17 ≤ 1024 :=
    check.budget
  omega

theorem sourceStackHeadroom_of_layout_check
    {program : Program}
    {active layout : List Name}
    {check :
      Program.StackFrameWordSumVisibleCheckResult program layout.length}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  hContext.sourceStackHeadroom_of_visible_check (check := check)
    (Nat.le_refl layout.length)

theorem sourceStackHeadroom_of_layout_budget {program : Program}
    {check : Program.StackFrameWordSumCheckResult program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target)
    (hBudget : layout.length + check.frameWords + 17 ≤ 1024) :
    Structured.Preservation.Frame.SourceStackHeadroom target := by
  unfold Structured.Preservation.Frame.SourceStackHeadroom
  have hWeight :
      Structured.Preservation.Frame.sourceStackWeight target ≤
        layout.length + check.frameWords :=
    hContext.sourceStackWeight_le_layout_plus_checked_frameWords
      (check := check)
  omega

def main {program : Program}
    {layout : List Name}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hRel : SourceDirect.StateRel layout [] source target) :
    SourceDirectWeightedFrameContext program [] layout [] source target where
  base := SourceDirectBaseContext.main hLayout hRel
  hidden := ActiveHiddenFrameWordsContext.main

def withStateRel {program : Program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source' target') :
    SourceDirectWeightedFrameContext program active layout hiddenReturns
      source' target' where
  base := hContext.base.withStateRel hRel
  hidden := hContext.hidden

def withStateRelLayout {program : Program}
    {active layout layout' : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target)
    (hLayout' : layout'.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout' hiddenReturns source' target') :
    SourceDirectWeightedFrameContext program active layout'
      hiddenReturns source' target' where
  base := hContext.base.withStateRelLayout hLayout' hRel
  hidden := hContext.hidden

def rootCallBodyOfArgCallerBound {program : Program}
    {callerLayout calleeLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    (hCaller :
      SourceDirectWeightedFrameContext program [] callerLayout []
        callerSource callerTarget)
    (hRoot : callee ∈ Program.mainInternalCalls program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    SourceDirectWeightedFrameContext program [callee] calleeLayout
      [{ callerStack := callerTarget.evm.stack, retc := retc }]
      calleeSource calleeTarget where
  base :=
    SourceDirectBaseContext.rootCallBody hCaller.base hRoot hCalleeFind
      hCalleeLayout hRel
  hidden :=
    ActiveHiddenFrameWordsContext.root hRoot hCalleeFind
      (RuntimeFrameShape.callerFrameWords_le_of_argCallerBound
        hArgCallerBound)

def callBodyOfArgCallerBound {program : Program}
    {active callerLayout calleeLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      SourceDirectWeightedFrameContext program active callerLayout
        hiddenReturns callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    SourceDirectWeightedFrameContext program (active ++ [callee])
      calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget where
  base :=
    SourceDirectBaseContext.callBody hCallerContext.base hCaller hCallerFind
      hCall hCalleeFind hCalleeLayout hRel
  hidden :=
    ActiveHiddenFrameWordsContext.call hCallerContext.hidden hCaller
      hCallerFind hCall hCalleeFind
      (RuntimeFrameShape.callerFrameWords_le_of_argCallerBound
        hArgCallerBound)

def rootCallBodyTargetCtxOfArgCallerBound {program : Program}
    {callerLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    (hCaller :
      SourceDirectWeightedFrameContext program [] callerLayout []
        callerSource callerTarget)
    (hRoot : callee ∈ Program.mainInternalCalls program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeBound : SourceDirect.FrameBound.FunDef calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    SourceDirectWeightedFrameContext program [callee]
      (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
      [{ callerStack := callerTarget.evm.stack, retc := retc }]
      calleeSource calleeTarget :=
  rootCallBodyOfArgCallerBound hCaller hRoot hCalleeFind hArgCallerBound
    (SourceDirect.FrameBound.funDef_targetBodyCtx_layout_le16 hCalleeBound)
    hRel

def callBodyTargetCtxOfArgCallerBound {program : Program}
    {active callerLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      SourceDirectWeightedFrameContext program active callerLayout
        hiddenReturns callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeBound : SourceDirect.FrameBound.FunDef calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    SourceDirectWeightedFrameContext program (active ++ [callee])
      (SourceDirect.FunDef.targetBodyCtx calleeFn).layout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget :=
  callBodyOfArgCallerBound hCallerContext hCaller hCallerFind hCall
    hCalleeFind hArgCallerBound
    (SourceDirect.FrameBound.funDef_targetBodyCtx_layout_le16 hCalleeBound)
    hRel

def afterAttachReturns? {program : Program}
    {active : List Name} {callee : Name}
    {calleeLayout callerLayout : List Name}
    {calleeHidden callerHidden : List Structured.ReturnDest}
    {calleeSource callerSource : Source.State}
    {state returned callerTarget : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hCalleeContext :
      SourceDirectWeightedFrameContext program (active ++ [callee])
        calleeLayout calleeHidden calleeSource state)
    (hActive : Program.ActiveCallStack program active)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16)
    (hCallerTarget :
      callerTarget = returned.withEVM { state.evm with stack := stack })
    (hRel :
      SourceDirect.StateRel callerLayout callerHidden callerSource
        callerTarget) :
    SourceDirectWeightedFrameContext program active callerLayout
      callerHidden callerSource callerTarget := by
  have hPopReturns :=
    Structured.Preservation.Frame.RunState.popReturn?_returns_eq hPop
  have hCalleeHidden :
      calleeHidden = frame :: callerHidden := by
    have hCalleeReturns := hCalleeContext.base.stateRel.2
    have hCallerReturns := hRel.2
    subst callerTarget
    simp [Structured.RunState.withEVM] at hCallerReturns
    rw [← hCalleeReturns, hPopReturns, hCallerReturns]
  have hHidden :
      ActiveHiddenFrameWordsContext program (active ++ [callee])
        (frame :: callerHidden) := by
    simpa [hCalleeHidden] using hCalleeContext.hidden
  refine
    { base :=
        SourceDirectBaseContext.afterAttachReturns? hCalleeContext.base
          hActive hPop hAttach hReturnFrameVisible hCallerTarget hRel
      hidden := ?_ }
  exact ActiveHiddenFrameWordsContext.afterReturn hHidden

end SourceDirectWeightedFrameContext

structure SourceFrameWordSumResourceBound (program : Program) : Type where
  check : Program.StackFrameWordSumCheckResult program

namespace SourceFrameWordSumResourceBound

theorem checked {program : Program}
    (bound : SourceFrameWordSumResourceBound program) :
    Program.maxActiveFrameWords? program = some bound.check.frameWords :=
  bound.check.checked

theorem budget {program : Program}
    (bound : SourceFrameWordSumResourceBound program) :
    16 + bound.check.frameWords + 17 ≤ 1024 :=
  bound.check.budget

theorem sourceStackHeadroom_of_weightedContext {program : Program}
    (bound : SourceFrameWordSumResourceBound program)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  SourceDirectWeightedFrameContext.sourceStackHeadroom
    (check := bound.check) context

theorem sourceStackHeadroom_of_weightedContext_layout_budget
    {program : Program}
    (bound : SourceFrameWordSumResourceBound program)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target)
    (hBudget : layout.length + bound.check.frameWords + 17 ≤ 1024) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  SourceDirectWeightedFrameContext.sourceStackHeadroom_of_layout_budget
    (check := bound.check) context hBudget

theorem returnStackWeight_le_checked_frameWords_of_weightedContext
    {program : Program}
    (bound : SourceFrameWordSumResourceBound program)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.returnStackWeight hiddenReturns ≤
      bound.check.frameWords :=
  SourceDirectWeightedFrameContext.returnStackWeight_le_checked_frameWords
    (check := bound.check) context

theorem sourceStackWeight_le_layout_plus_checked_frameWords_of_weightedContext
    {program : Program}
    (bound : SourceFrameWordSumResourceBound program)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.sourceStackWeight target ≤
      layout.length + bound.check.frameWords :=
  SourceDirectWeightedFrameContext.sourceStackWeight_le_layout_plus_checked_frameWords
    (check := bound.check) context

theorem sourceStackWeight_le_checked_frameWords_of_weightedContext
    {program : Program}
    (bound : SourceFrameWordSumResourceBound program)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.sourceStackWeight target ≤
      16 + bound.check.frameWords :=
  SourceDirectWeightedFrameContext.sourceStackWeight_le_checked_frameWords
    (check := bound.check) context

end SourceFrameWordSumResourceBound

structure SourceFrameWordSumVisibleResourceBound (program : Program)
    (visibleWords : Nat) : Type where
  check : Program.StackFrameWordSumVisibleCheckResult program visibleWords

namespace SourceFrameWordSumVisibleResourceBound

theorem checked {program : Program} {visibleWords : Nat}
    (bound :
      SourceFrameWordSumVisibleResourceBound program visibleWords) :
    Program.maxActiveFrameWords? program = some bound.check.frameWords :=
  bound.check.checked

theorem budget {program : Program} {visibleWords : Nat}
    (bound :
      SourceFrameWordSumVisibleResourceBound program visibleWords) :
    visibleWords + bound.check.frameWords + 17 ≤ 1024 :=
  bound.check.budget

theorem sourceStackHeadroom_of_weightedContext
    {program : Program} {visibleWords : Nat}
    (bound :
      SourceFrameWordSumVisibleResourceBound program visibleWords)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target)
    (hLayoutVisible : layout.length ≤ visibleWords) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  SourceDirectWeightedFrameContext.sourceStackHeadroom_of_visible_check
    (check := bound.check) context hLayoutVisible

theorem sourceStackHeadroom_of_weightedContext_layout_check
    {program : Program}
    {active layout : List Name}
    (bound :
      SourceFrameWordSumVisibleResourceBound program layout.length)
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  SourceDirectWeightedFrameContext.sourceStackHeadroom_of_layout_check
    (check := bound.check) context

theorem returnStackWeight_le_checked_frameWords_of_weightedContext
    {program : Program} {visibleWords : Nat}
    (bound :
      SourceFrameWordSumVisibleResourceBound program visibleWords)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.returnStackWeight hiddenReturns ≤
      bound.check.frameWords :=
  SourceDirectWeightedFrameContext.returnStackWeight_le_visible_checked_frameWords
    (check := bound.check) context

theorem sourceStackWeight_le_layout_plus_checked_frameWords_of_weightedContext
    {program : Program} {visibleWords : Nat}
    (bound :
      SourceFrameWordSumVisibleResourceBound program visibleWords)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectWeightedFrameContext program active layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.sourceStackWeight target ≤
      layout.length + bound.check.frameWords :=
  SourceDirectWeightedFrameContext.sourceStackWeight_le_layout_plus_visible_checked_frameWords
    (check := bound.check) context

end SourceFrameWordSumVisibleResourceBound

namespace Program

def sourceFrameWordSumResourceBound? (program : Program) :
    Option (SourceFrameWordSumResourceBound program) :=
  match stackFrameWordSumCheck? program with
  | none => none
  | some check => some { check := check }

theorem sourceFrameWordSumResourceBound?_eq_some
    {program : Program}
    {bound : SourceFrameWordSumResourceBound program}
    (hBound : sourceFrameWordSumResourceBound? program = some bound) :
    stackFrameWordSumCheck? program = some bound.check := by
  unfold sourceFrameWordSumResourceBound? at hBound
  cases hCheck : stackFrameWordSumCheck? program with
  | none =>
      simp [hCheck] at hBound
  | some check =>
      simp [hCheck] at hBound
      cases hBound
      rfl

theorem sourceFrameWordSumResourceBound?_sound
    {program : Program}
    {bound : SourceFrameWordSumResourceBound program}
    (hBound : sourceFrameWordSumResourceBound? program = some bound) :
    Program.maxActiveFrameWords? program = some bound.check.frameWords ∧
      16 + bound.check.frameWords + 17 ≤ 1024 := by
  have hCheck := sourceFrameWordSumResourceBound?_eq_some hBound
  exact stackFrameWordSumCheck?_eq_some hCheck

def sourceFrameWordSumVisibleResourceBound? (program : Program)
    (visibleWords : Nat) :
    Option (SourceFrameWordSumVisibleResourceBound program visibleWords) :=
  match stackFrameWordSumVisibleCheck? program visibleWords with
  | none => none
  | some check => some { check := check }

theorem sourceFrameWordSumVisibleResourceBound?_eq_some
    {program : Program} {visibleWords : Nat}
    {bound : SourceFrameWordSumVisibleResourceBound program visibleWords}
    (hBound :
      sourceFrameWordSumVisibleResourceBound? program visibleWords =
        some bound) :
    stackFrameWordSumVisibleCheck? program visibleWords =
      some bound.check := by
  unfold sourceFrameWordSumVisibleResourceBound? at hBound
  cases hCheck : stackFrameWordSumVisibleCheck? program visibleWords with
  | none =>
      simp [hCheck] at hBound
  | some check =>
      simp [hCheck] at hBound
      cases hBound
      rfl

theorem sourceFrameWordSumVisibleResourceBound?_sound
    {program : Program} {visibleWords : Nat}
    {bound : SourceFrameWordSumVisibleResourceBound program visibleWords}
    (hBound :
      sourceFrameWordSumVisibleResourceBound? program visibleWords =
        some bound) :
    Program.maxActiveFrameWords? program = some bound.check.frameWords ∧
      visibleWords + bound.check.frameWords + 17 ≤ 1024 := by
  have hCheck :=
    sourceFrameWordSumVisibleResourceBound?_eq_some hBound
  exact stackFrameWordSumVisibleCheck?_eq_some hCheck

end Program

/--
Source/direct preservation needs both the ordinary value/state relation and the
stack-resource invariant.  This compatibility package keeps the runtime shape
that many existing callbacks already thread.  New checker soundness facts should
prefer `SourceDirectBaseContext` plus an explicit checked depth bound, then build
this resource context with `SourceDirectBaseContext.toResourceContext`.
-/
structure SourceDirectResourceContext (program : Program)
    (budget : StackBudget)
    (active layout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (source : Source.State) (target : Structured.RunState) : Prop where
  stateRel :
    SourceDirect.StateRel layout hiddenReturns source target
  runtime :
    RuntimeCallStackShape program budget active target

namespace SourceDirectBaseContext

def toResourceContext {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectBaseContext program active layout hiddenReturns source target)
    (hActiveLengthLe : active.length ≤ budget.depth) :
    SourceDirectResourceContext program budget active layout hiddenReturns
      source target where
  stateRel := hContext.stateRel
  runtime := hContext.runtimeCallStackShape hActiveLengthLe

end SourceDirectBaseContext

namespace SourceDirectResourceContext

theorem toBase {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectResourceContext program budget active layout
        hiddenReturns source target) :
    SourceDirectBaseContext program active layout hiddenReturns source
      target := by
  rcases hContext.stateRel with ⟨hLowerRel, hReturns⟩
  rcases hLowerRel with ⟨_hSharedRel, hStackRel⟩
  refine
    { stateRel := hContext.stateRel
      activeStack := hContext.runtime.activeStack
      layoutLength := ?_
      hiddenReturnsLength := ?_
      callersLe := ?_ }
  · rw [← hStackRel.1]
    exact hContext.runtime.visibleLe
  · rw [← hReturns]
    exact hContext.runtime.returnsLength
  · intro frame hMem
    rw [← hReturns] at hMem
    exact hContext.runtime.callersLe frame hMem

theorem hiddenReturns_length {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectResourceContext program budget active layout
        hiddenReturns source target) :
    hiddenReturns.length = active.length := by
  have hReturns := hContext.stateRel.2
  rw [← hReturns]
  exact hContext.runtime.returnsLength

theorem withStateRel {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectResourceContext program budget active layout hiddenReturns
        source target)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source' target') :
    SourceDirectResourceContext program budget active layout hiddenReturns
      source' target' :=
  (hContext.toBase.withStateRel hRel).toResourceContext
    hContext.runtime.activeLengthLe

theorem withStateRelLayout {program : Program}
    {budget : StackBudget}
    {active layout layout' : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectResourceContext program budget active layout hiddenReturns
        source target)
    (hLayout' : layout'.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout' hiddenReturns source' target') :
    SourceDirectResourceContext program budget active layout' hiddenReturns
      source' target' :=
  (hContext.toBase.withStateRelLayout hLayout' hRel).toResourceContext
    hContext.runtime.activeLengthLe

theorem of_regularBlockScopedOutcomeRel {program : Program}
    {budget : StackBudget}
    {active layout layout' returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Source.State}
    {target target' : Structured.RunState}
    (hContext :
      SourceDirectResourceContext program budget active layout hiddenReturns
        source target)
    (hLayout' : layout'.length ≤ 16)
    (hRel :
      SourceDirect.BlockScopedOutcomeRel returns layout' hiddenReturns
        (Source.Outcome.regular source')
        (Structured.Outcome.regular target')) :
    SourceDirectResourceContext program budget active layout' hiddenReturns
      source' target' :=
  hContext.withStateRelLayout hLayout'
    (SourceDirect.BlockScopedOutcomeRel.regular_stateRel hRel)

theorem sourceStackHeadroom {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      SourceDirectResourceContext program budget active layout
        hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  hContext.runtime.sourceStackHeadroom

theorem of_sourceDirectStateRelWithBound {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hActive : Program.ActiveCallStack program active)
    (hActiveLengthLe : active.length ≤ budget.depth)
    (hLayout : layout.length ≤ 16)
    (hReturnsLength : hiddenReturns.length = active.length)
    (hCallers :
      ∀ frame, frame ∈ hiddenReturns →
        frame.callerStack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    SourceDirectResourceContext program budget active layout hiddenReturns
      source target where
  stateRel := hRel
  runtime :=
    RuntimeCallStackShape.of_sourceDirectStateRelWithBound
      (budget := budget) hActive
      hActiveLengthLe hLayout hReturnsLength hCallers hRel

theorem of_sourceDirectStateRel {program : Program}
    {check : Program.StackDepthCheckResult program}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hActive : Program.ActiveCallStack program active)
    (hLayout : layout.length ≤ 16)
    (hReturnsLength : hiddenReturns.length = active.length)
    (hCallers :
      ∀ frame, frame ∈ hiddenReturns →
        frame.callerStack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    SourceDirectResourceContext program check.toStackBudget
      active layout hiddenReturns
      source target :=
  of_sourceDirectStateRelWithBound
    (budget := check.toStackBudget) hActive
    (Program.ActiveCallStack.length_le_depth check hActive)
    hLayout hReturnsLength hCallers hRel

theorem main {program : Program}
    {budget : StackBudget}
    {layout : List Name}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hRel : SourceDirect.StateRel layout [] source target) :
    SourceDirectResourceContext program budget [] layout [] source target where
  stateRel := hRel
  runtime :=
    RuntimeCallStackShape.main_of_sourceDirectStateRel
      (program := program) (budget := budget) hLayout hRel

theorem main_sourceStackHeadroom {program : Program}
    {budget : StackBudget}
    {layout : List Name}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hRel : SourceDirect.StateRel layout [] source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  sourceStackHeadroom (main (program := program) (budget := budget)
    hLayout hRel)

theorem rootCallBody {program : Program}
    {budget : StackBudget}
    {callerLayout calleeLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    (hCaller :
      SourceDirectResourceContext program budget [] callerLayout []
        callerSource callerTarget)
    (hRoot : callee ∈ Program.mainInternalCalls program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeLength : [callee].length ≤ budget.depth)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    SourceDirectResourceContext program budget [callee] calleeLayout
      [{ callerStack := callerTarget.evm.stack, retc := retc }]
      calleeSource calleeTarget := by
  refine
    of_sourceDirectStateRelWithBound
      (budget := budget)
      (Program.ActiveCallStack.root hRoot hCalleeFind)
      hCalleeLength
      hCalleeLayout ?_ ?_ hRel
  · simp
  · intro frame hMem
    have hFrame :
        frame =
          { callerStack := callerTarget.evm.stack, retc := retc } := by
      simpa using hMem
    cases hFrame
    exact hCaller.runtime.visibleLe

theorem callBodyWithBound {program : Program}
    {budget : StackBudget}
    {active callerLayout calleeLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      SourceDirectResourceContext program budget active callerLayout
        hiddenReturns callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hNextLength : (active ++ [callee]).length ≤ budget.depth)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    SourceDirectResourceContext program budget (active ++ [callee])
      calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget := by
  refine
    of_sourceDirectStateRelWithBound
      (budget := budget)
      (Program.ActiveCallStack.push hCallerContext.runtime.activeStack
        hCaller hCallerFind hCall hCalleeFind)
      hNextLength
      hCalleeLayout ?_ ?_ hRel
  · simp [hiddenReturns_length hCallerContext]
  · intro frame hMem
    simp at hMem
    rcases hMem with hHead | hTail
    · cases hHead
      exact hCallerContext.runtime.visibleLe
    · have hMemReturns : frame ∈ callerTarget.returns := by
        rw [hCallerContext.stateRel.2]
        exact hTail
      exact hCallerContext.runtime.callersLe frame hMemReturns

theorem callBody {program : Program}
    {check : Program.StackDepthCheckResult program}
    {active callerLayout calleeLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      SourceDirectResourceContext program check.toStackBudget
        active callerLayout
        hiddenReturns callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    SourceDirectResourceContext program check.toStackBudget
      (active ++ [callee])
      calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget :=
  callBodyWithBound hCallerContext hCaller hCallerFind hCall hCalleeFind
    (Program.ActiveCallStack.length_le_depth check
      (Program.ActiveCallStack.push hCallerContext.runtime.activeStack
        hCaller hCallerFind hCall hCalleeFind))
    hCalleeLayout hRel

theorem afterAttachReturnsWithBound? {program : Program}
    {budget : StackBudget}
    {active : List Name} {callee : Name}
    {calleeLayout callerLayout : List Name}
    {calleeHidden callerHidden : List Structured.ReturnDest}
    {calleeSource callerSource : Source.State}
    {state returned callerTarget : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hCalleeContext :
      SourceDirectResourceContext program budget (active ++ [callee])
        calleeLayout calleeHidden calleeSource state)
    (hActive : Program.ActiveCallStack program active)
    (hActiveLengthLe : active.length ≤ budget.depth)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16)
    (hCallerTarget :
      callerTarget = returned.withEVM { state.evm with stack := stack })
    (hRel :
      SourceDirect.StateRel callerLayout callerHidden callerSource
        callerTarget) :
    SourceDirectResourceContext program budget active callerLayout
      callerHidden callerSource callerTarget := by
  subst callerTarget
  exact
    { stateRel := hRel
      runtime :=
        RuntimeCallStackShape.afterAttachReturnsWithBound?
          hCalleeContext.runtime hActive hActiveLengthLe hPop hAttach
          hReturnFrameVisible }

theorem afterAttachReturns? {program : Program}
    {check : Program.StackDepthCheckResult program}
    {active : List Name} {callee : Name}
    {calleeLayout callerLayout : List Name}
    {calleeHidden callerHidden : List Structured.ReturnDest}
    {calleeSource callerSource : Source.State}
    {state returned callerTarget : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    (hCalleeContext :
      SourceDirectResourceContext program check.toStackBudget
        (active ++ [callee])
        calleeLayout calleeHidden calleeSource state)
    (hActive : Program.ActiveCallStack program active)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16)
    (hCallerTarget :
      callerTarget = returned.withEVM { state.evm with stack := stack })
    (hRel :
      SourceDirect.StateRel callerLayout callerHidden callerSource
        callerTarget) :
    SourceDirectResourceContext program check.toStackBudget active
      callerLayout
      callerHidden callerSource callerTarget :=
  afterAttachReturnsWithBound? hCalleeContext hActive
    (Program.ActiveCallStack.length_le_depth check hActive)
    hPop hAttach hReturnFrameVisible hCallerTarget hRel

end SourceDirectResourceContext

/--
Source/direct resource context extended with a bounded transient structured stack
prefix.

Preservation traces visit assembly-instruction boundaries, including points where
the compiler has pushed temporary operands above the source/direct frame.  The
base source/direct context still proves the call-stack/resource invariant; this
wrapper records the extra visible prefix and the precise headroom budget needed
for the transient structured state.
-/
structure SourceDirectTransientResourceContext (program : Program)
    (budget : StackBudget)
    (active layout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (source : Source.State) (base target : Structured.RunState) : Type where
  baseContext :
    SourceDirectResourceContext program budget active layout hiddenReturns
      source base
  stackPrefix : EvmYul.Stack Structured.Word
  target_eq :
    target =
      base.withEVM { base.evm with stack := stackPrefix ++ base.evm.stack }
  headroom :
    stackPrefix.length +
        Structured.Preservation.Frame.sourceStackWeight base + 17 ≤ 1024

namespace SourceDirectTransientResourceContext

theorem sourceStackHeadroom {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {base target : Structured.RunState}
    (hContext :
      SourceDirectTransientResourceContext program budget active layout
        hiddenReturns source base target) :
    Structured.Preservation.Frame.SourceStackHeadroom target := by
  rcases hContext with
    ⟨hBaseContext, stackPrefix, hTarget, hHeadroom⟩
  subst target
  simp [Structured.Preservation.Frame.SourceStackHeadroom,
    Structured.Preservation.Frame.sourceStackWeight,
    Structured.RunState.withEVM, List.length_append] at hHeadroom ⊢
  omega

def of_base {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {base : Structured.RunState}
    (hContext :
      SourceDirectResourceContext program budget active layout hiddenReturns
        source base)
    (hHeadroom :
      Structured.Preservation.Frame.sourceStackWeight base + 17 ≤ 1024) :
    SourceDirectTransientResourceContext program budget active layout
      hiddenReturns source base base where
  baseContext := hContext
  stackPrefix := []
  target_eq := by simp [Structured.RunState.withEVM]
  headroom := by simpa using hHeadroom

def of_prefix {program : Program}
    {budget : StackBudget}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {base : Structured.RunState}
    (hContext :
      SourceDirectResourceContext program budget active layout hiddenReturns
        source base)
    (stackPrefix : EvmYul.Stack Structured.Word)
    (hHeadroom :
      stackPrefix.length +
          Structured.Preservation.Frame.sourceStackWeight base + 17 ≤ 1024) :
    SourceDirectTransientResourceContext program budget active layout
      hiddenReturns source base
      (base.withEVM
        { base.evm with stack := stackPrefix ++ base.evm.stack }) where
  baseContext := hContext
  stackPrefix := stackPrefix
  target_eq := rfl
  headroom := hHeadroom

end SourceDirectTransientResourceContext

namespace Program

/--
Semantic stack-resource safety over the budget-free source/direct base context.

This is the non-vacuous resource theorem shape: the context supplies the
ordinary source/direct state facts and active call-stack shape, while the
checked budget contributes the active-frame bound needed to derive EVM source
stack headroom.
-/
def StackResourceSafeFromBase (program : Program)
    (budget : StackBudget) : Prop :=
  ∀ {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState},
    SourceDirectBaseContext program active layout hiddenReturns source
      target →
      active.length ≤ budget.depth →
        Structured.Preservation.Frame.SourceStackHeadroom target

theorem stackResourceSafeFromBase_of_budget (program : Program)
    (budget : StackBudget) :
    StackResourceSafeFromBase program budget := by
  intro active layout hiddenReturns source target hContext hActiveLengthLe
  exact hContext.sourceStackHeadroomWithBound
    (budget := budget) hActiveLengthLe

/--
Compatibility stack-resource safety supplied by a checked stack budget.

The property is intentionally stated over the source/direct resource context,
not over arbitrary target states.  Later public Yul theorems must derive this
context for every actual preservation trace point; once they do, this predicate
turns the executable stack checker into the `Frame.SourceStackHeadroom` fact
needed by the gas-aware EVM replay.  The proof is routed through
`StackResourceSafeFromBase` so the checked budget is consumed before headroom is
projected from the compatibility context.
-/
def StackResourceSafe (program : Program)
    (budget : StackBudget) : Prop :=
  ∀ {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState},
    SourceDirectResourceContext program budget active layout hiddenReturns
      source target →
      Structured.Preservation.Frame.SourceStackHeadroom target

theorem stackResourceSafe_of_budget (program : Program)
    (budget : StackBudget) :
    StackResourceSafe program budget := by
  intro active layout hiddenReturns source target hContext
  exact
    stackResourceSafeFromBase_of_budget program budget hContext.toBase
      hContext.runtime.activeLengthLe

/--
Checked semantic stack-resource check result.

The executable checker supplies the budget; `baseSafe` is the verified semantic
resource theorem over budget-free source/direct contexts, and `safe` is the
compatibility projection consumed by existing preservation callbacks.
-/
structure StackResourceCheckResult (program : Program) : Type where
  budget : StackBudget
  baseSafe : StackResourceSafeFromBase program budget
  safe : StackResourceSafe program budget

namespace StackDepthCheckResult

def toStackResourceCheckResult {program : Program}
    (check : StackDepthCheckResult program) :
    StackResourceCheckResult program where
  budget := check.toStackBudget
  baseSafe := stackResourceSafeFromBase_of_budget program
    check.toStackBudget
  safe := stackResourceSafe_of_budget program check.toStackBudget

theorem stackResourceSafe {program : Program}
    (check : StackDepthCheckResult program) :
    StackResourceSafe program check.toStackBudget :=
  (toStackResourceCheckResult check).safe

end StackDepthCheckResult

def stackResourceCheck? (program : Program) :
    Option (StackResourceCheckResult program) :=
  match stackDepthCheck? program with
  | none => none
  | some check => some check.toStackResourceCheckResult

theorem stackResourceCheck?_eq_some
    {program : Program} {check : StackResourceCheckResult program}
    (hCheck : stackResourceCheck? program = some check) :
    ∃ depthCheck : StackDepthCheckResult program,
      stackDepthCheck? program = some depthCheck ∧
        check = depthCheck.toStackResourceCheckResult ∧
        StackResourceSafe program check.budget := by
  unfold stackResourceCheck? at hCheck
  cases hDepth : stackDepthCheck? program with
  | none =>
      simp [hDepth] at hCheck
  | some depthCheck =>
      simp [hDepth] at hCheck
      cases hCheck
      exact
        ⟨depthCheck, rfl, rfl,
          depthCheck.toStackResourceCheckResult.safe⟩

theorem stackResourceSafe_of_stackResourceCheck?
    {program : Program} {check : StackResourceCheckResult program}
    (hCheck : stackResourceCheck? program = some check) :
    StackResourceSafe program check.budget := by
  rcases stackResourceCheck?_eq_some hCheck with
    ⟨_depthCheck, _hDepth, _hEq, hSafe⟩
  exact hSafe

def stackResourceChecked (program : Program) : Bool :=
  (stackResourceCheck? program).isSome

theorem stackResourceCheck?_of_stackResourceChecked
    {program : Program}
    (hChecked : stackResourceChecked program = true) :
    ∃ check : StackResourceCheckResult program,
      stackResourceCheck? program = some check := by
  unfold stackResourceChecked at hChecked
  cases hCheck : stackResourceCheck? program with
  | none =>
      simp [hCheck] at hChecked
  | some check =>
      exact ⟨check, by simp⟩

theorem stackResourceSafe_of_stackResourceChecked
    {program : Program}
    (hChecked : stackResourceChecked program = true) :
    ∃ check : StackResourceCheckResult program,
      StackResourceSafe program check.budget := by
  rcases stackResourceCheck?_of_stackResourceChecked hChecked with
    ⟨check, hCheck⟩
  exact ⟨check, stackResourceSafe_of_stackResourceCheck? hCheck⟩

end Program

end CallDepth
end Functions
end EvmCompiler
