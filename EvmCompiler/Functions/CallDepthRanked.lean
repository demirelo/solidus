import EvmCompiler.Functions.CallDepth

namespace EvmCompiler
namespace Functions
namespace CallDepth
namespace Ranked

/--
A node in the checked ranked call-state graph.

The `rank` is an abstract, checker-owned natural measure.  The current public
inference assigns every function rank zero, so it only accepts acyclic internal
call graphs.  Bounded recursive source cycles need an additional source-state
analysis that proves which ranked dynamic states can actually take each call;
plain finite rank edges are not enough to justify a raw recursive body.
-/
structure Node where
  functionName : Name
  rank : Nat
  deriving DecidableEq, Repr

structure Edge where
  src : Node
  dst : Node
  deriving DecidableEq, Repr

namespace Edge

def successors (edges : List Edge) (node : Node) : List Node :=
  edges.foldr
    (fun edge acc =>
      if edge.src = node then
        edge.dst :: acc
      else
        acc)
    []

theorem dst_mem_successors_of_mem
    {edges : List Edge} {edge : Edge} {node : Node}
    (hMem : edge ∈ edges)
    (hSrc : edge.src = node) :
    edge.dst ∈ successors edges node := by
  induction edges with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold successors
      simp at hMem
      rcases hMem with hHead | hRest
      · subst head
        simp [hSrc]
      · by_cases hHeadSrc : head.src = node
        · have hTail := ih hRest
          simp [hHeadSrc]
          exact Or.inr (by simpa [successors] using hTail)
        · have hTail := ih hRest
          simp [hHeadSrc]
          simpa [successors] using hTail

theorem mem_successors_exists_mem
    {edges : List Edge} {node next : Node}
    (hSucc : next ∈ successors edges node) :
    ∃ edge, edge ∈ edges ∧ edge.src = node ∧ edge.dst = next := by
  induction edges with
  | nil =>
      simp [successors] at hSucc
  | cons head rest ih =>
      unfold successors at hSucc
      by_cases hHeadSrc : head.src = node
      · simp [hHeadSrc] at hSucc
        rcases hSucc with hNext | hTail
        · exact ⟨head, by simp, hHeadSrc, hNext.symm⟩
        · rcases ih hTail with ⟨edge, hMem, hSrc, hDst⟩
          exact ⟨edge, by simp [hMem], hSrc, hDst⟩
      · simp [hHeadSrc] at hSucc
        rcases ih hSucc with ⟨edge, hMem, hSrc, hDst⟩
        exact ⟨edge, by simp [hMem], hSrc, hDst⟩

end Edge

inductive Path (edges : List Edge) : Node → Nat → Prop where
  | here {node : Node} :
      Path edges node 0
  | step {node next : Node} {depth : Nat}
      (hEdge : next ∈ Edge.successors edges node)
      (hTail : Path edges next depth) :
      Path edges node (depth + 1)

inductive PathTo (edges : List Edge) : Node → Node → Nat → Prop where
  | here {node : Node} :
      PathTo edges node node 0
  | step {node next target : Node} {depth : Nat}
      (hEdge : next ∈ Edge.successors edges node)
      (hTail : PathTo edges next target depth) :
      PathTo edges node target (depth + 1)

namespace PathTo

theorem toPath {edges : List Edge} {root target : Node} {depth : Nat}
    (hPath : PathTo edges root target depth) :
    Path edges root depth := by
  induction hPath with
  | here =>
      exact Path.here
  | step hEdge _hTail hTailPath =>
      exact Path.step hEdge hTailPath

theorem snoc {edges : List Edge}
    {root current next : Node} {depth : Nat}
    (hPath : PathTo edges root current depth)
    (hEdge : next ∈ Edge.successors edges current) :
    PathTo edges root next (depth + 1) := by
  induction hPath with
  | here =>
      exact PathTo.step hEdge PathTo.here
  | step hHead _hTail hTailSnoc =>
      exact PathTo.step hHead (hTailSnoc hEdge)

end PathTo

/--
An abstract concrete-call chain.

`DirectCall` is deliberately a parameter: current acyclic checking can
instantiate it with function-name call edges, while path-sensitive checkers can
later instantiate it with source/direct frames carrying argument abstractions.
-/
inductive ConcreteCallChain {Frame : Type} (DirectCall : Frame → Frame → Prop) :
    Frame → Nat → Prop where
  | here {frame : Frame} :
      ConcreteCallChain DirectCall frame 0
  | step {frame next : Frame} {depth : Nat}
      (hCall : DirectCall frame next)
      (hTail : ConcreteCallChain DirectCall next depth) :
      ConcreteCallChain DirectCall frame (depth + 1)

namespace ConcreteCallChain

theorem mono {Frame : Type}
    {DirectCall₁ DirectCall₂ : Frame → Frame → Prop}
    (hDirect :
      ∀ {frame next}, DirectCall₁ frame next → DirectCall₂ frame next) :
    ∀ {frame depth},
      ConcreteCallChain DirectCall₁ frame depth →
        ConcreteCallChain DirectCall₂ frame depth := by
  intro frame depth hChain
  induction hChain with
  | here =>
      exact ConcreteCallChain.here
  | step hCall _hTail ih =>
      exact ConcreteCallChain.step (hDirect hCall) ih

end ConcreteCallChain

inductive ConcreteCallChainTo {Frame : Type}
    (DirectCall : Frame → Frame → Prop) :
    Frame → Frame → Nat → Prop where
  | here {frame : Frame} :
      ConcreteCallChainTo DirectCall frame frame 0
  | step {frame next target : Frame} {depth : Nat}
      (hCall : DirectCall frame next)
      (hTail : ConcreteCallChainTo DirectCall next target depth) :
      ConcreteCallChainTo DirectCall frame target (depth + 1)

namespace ConcreteCallChainTo

theorem to_chain {Frame : Type}
    {DirectCall : Frame → Frame → Prop}
    {root current : Frame} {depth : Nat}
    (hChain : ConcreteCallChainTo DirectCall root current depth) :
    ConcreteCallChain DirectCall root depth := by
  induction hChain with
  | here =>
      exact ConcreteCallChain.here
  | step hCall _hTail ih =>
      exact ConcreteCallChain.step hCall ih

theorem snoc {Frame : Type}
    {DirectCall : Frame → Frame → Prop}
    {root current next : Frame} {depth : Nat}
    (hChain : ConcreteCallChainTo DirectCall root current depth)
    (hCall : DirectCall current next) :
    ConcreteCallChainTo DirectCall root next (depth + 1) := by
  induction hChain with
  | here =>
      exact ConcreteCallChainTo.step hCall ConcreteCallChainTo.here
  | step hHead _hTail ih =>
      exact ConcreteCallChainTo.step hHead (ih hCall)

end ConcreteCallChainTo

inductive ConcreteFrameStack {Frame : Type}
    (RootFrame : Frame → Prop)
    (DirectCall : Frame → Frame → Prop) :
    List Frame → Prop where
  | empty :
      ConcreteFrameStack RootFrame DirectCall []
  | root {frame : Frame}
      (hRoot : RootFrame frame) :
      ConcreteFrameStack RootFrame DirectCall [frame]
  | snoc {frames : List Frame} {current next : Frame}
      (hStack : ConcreteFrameStack RootFrame DirectCall frames)
      (hLast : frames.getLast? = some current)
      (hCall : DirectCall current next) :
      ConcreteFrameStack RootFrame DirectCall (frames ++ [next])

namespace ConcreteFrameStack

theorem to_chain_to {Frame : Type}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    {frames : List Frame} {current : Frame}
    (hStack : ConcreteFrameStack RootFrame DirectCall frames)
    (hLast : frames.getLast? = some current) :
    ∃ root depth,
      RootFrame root ∧
        ConcreteCallChainTo DirectCall root current depth ∧
        frames.length = depth + 1 := by
  induction hStack generalizing current with
  | empty =>
      simp at hLast
  | root hRoot =>
      simp at hLast
      cases hLast
      exact
        ⟨_, 0, hRoot, ConcreteCallChainTo.here, by simp⟩
  | snoc hStack hPrevLast hCall ih =>
      simp at hLast
      subst current
      rcases ih hPrevLast with
        ⟨root, depth, hRoot, hChainTo, hLength⟩
      exact
        ⟨root, depth + 1, hRoot,
          ConcreteCallChainTo.snoc hChainTo hCall, by simp [hLength]⟩

theorem length_le_depth {Frame : Type}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    {frames : List Frame} {maxFrames : Nat}
    (hStack : ConcreteFrameStack RootFrame DirectCall frames)
    (hBound :
      ∀ {frame depth},
        RootFrame frame →
          ConcreteCallChain DirectCall frame depth →
            depth + 1 ≤ maxFrames) :
    frames.length ≤ maxFrames := by
  induction hStack with
  | empty =>
      simp
  | root hRoot =>
      have hDepth := hBound hRoot ConcreteCallChain.here
      simpa using hDepth
  | snoc hStack hLast hCall =>
      rcases to_chain_to hStack hLast with
        ⟨root, depth, hRoot, hChainTo, hLength⟩
      have hDepth :=
        hBound hRoot
          ((ConcreteCallChainTo.snoc hChainTo hCall).to_chain)
      simp [hLength] at hDepth ⊢
      omega

end ConcreteFrameStack

def GraphStep (edges : List Edge) (node next : Node) : Prop :=
  next ∈ Edge.successors edges node

theorem graphStepChain_to_path
    {edges : List Edge} {node : Node} {depth : Nat}
    (hChain : ConcreteCallChain (GraphStep edges) node depth) :
    Path edges node depth := by
  induction hChain with
  | here =>
      exact Path.here
  | step hStep _hTail hTailPath =>
      exact Path.step hStep hTailPath

structure RootedGraphDepthBound
    (edges : List Edge) (roots : List Node) (bound : Nat) : Prop where
  chain_bound :
    ∀ {root depth},
      root ∈ roots →
        ConcreteCallChain (GraphStep edges) root depth →
          depth + 1 ≤ bound

def CallChainDepthBound {Frame : Type}
    (RootFrame : Frame → Prop)
    (DirectCall : Frame → Frame → Prop)
    (bound : Nat) : Prop :=
  ∀ {frame depth},
    RootFrame frame →
      ConcreteCallChain DirectCall frame depth →
        depth + 1 ≤ bound

namespace CallChainDepthBound

theorem mono {Frame : Type}
    {RootFrame₁ RootFrame₂ : Frame → Prop}
    {DirectCall₁ DirectCall₂ : Frame → Frame → Prop}
    {bound : Nat}
    (hBound : CallChainDepthBound RootFrame₂ DirectCall₂ bound)
    (hRoot : ∀ {frame}, RootFrame₁ frame → RootFrame₂ frame)
    (hDirect :
      ∀ {frame next}, DirectCall₁ frame next → DirectCall₂ frame next) :
    CallChainDepthBound RootFrame₁ DirectCall₁ bound := by
  intro frame depth hRoot₁ hChain₁
  exact hBound (hRoot hRoot₁) (hChain₁.mono hDirect)

end CallChainDepthBound

namespace SourceCallDepth

/--
Semantic source-call depth contract.

The root and direct-call predicates are parameters on purpose: executable
analyses must prove that their checker-shaped roots/edges cover the actual
source-semantics predicates before using a finite graph bound.
-/
abbrev Bound {Frame : Type}
    (RootFrame : Frame → Prop)
    (DirectCall : Frame → Frame → Prop)
    (bound : Nat) : Prop :=
  CallChainDepthBound RootFrame DirectCall bound

end SourceCallDepth

structure HeightBound {Frame : Type}
    (RootFrame : Frame → Prop)
    (DirectCall : Frame → Frame → Prop)
    (height : Frame → Nat)
    (bound : Nat) : Prop where
  root_height :
    ∀ {frame}, RootFrame frame → height frame + 1 ≤ bound
  step_decreases :
    ∀ {frame next}, DirectCall frame next → height next < height frame

namespace HeightBound

theorem chain_depth_le_height {Frame : Type}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    {height : Frame → Nat} {bound : Nat}
    (hBound : HeightBound RootFrame DirectCall height bound)
    {frame : Frame} {depth : Nat}
    (hChain : ConcreteCallChain DirectCall frame depth) :
    depth ≤ height frame := by
  induction hChain with
  | here =>
      exact Nat.zero_le _
  | step hCall _hTail ih =>
      have hDecrease := hBound.step_decreases hCall
      omega

theorem callChainDepthBound {Frame : Type}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    {height : Frame → Nat} {bound : Nat}
    (hBound : HeightBound RootFrame DirectCall height bound) :
    CallChainDepthBound RootFrame DirectCall bound := by
  intro frame depth hRoot hChain
  have hDepth := hBound.chain_depth_le_height hChain
  have hRootHeight := hBound.root_height hRoot
  omega

end HeightBound

/--
State-sensitive graph soundness interface.

This is the broad replacement target for raw all-syntactic call-graph
conformance: a checker supplies roots and edges together with a matching
relation from abstract graph nodes to concrete call frames.  Soundness says
root concrete frames are matched by graph roots, and every concrete direct
internal call from a matched frame is represented by a graph edge to a matched
callee frame.
-/
structure CallGraphSound {Frame : Type}
    (edges : List Edge) (roots : List Node)
    (Matches : Node → Frame → Prop)
    (RootFrame : Frame → Prop)
    (DirectCall : Frame → Frame → Prop) : Prop where
  root_sound :
    ∀ {frame},
      RootFrame frame →
        ∃ root, root ∈ roots ∧ Matches root frame
  step_sound :
    ∀ {node frame nextFrame},
      Matches node frame →
        DirectCall frame nextFrame →
          ∃ next,
            next ∈ Edge.successors edges node ∧
              Matches next nextFrame

namespace CallGraphSound

theorem path_from {Frame : Type}
    {edges : List Edge} {roots : List Node}
    {Matches : Node → Frame → Prop}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    (hSound : CallGraphSound edges roots Matches RootFrame DirectCall)
    {frame : Frame} {depth : Nat}
    (hChain : ConcreteCallChain DirectCall frame depth) :
    ∀ {node}, Matches node frame → Path edges node depth := by
  induction hChain with
  | here =>
      intro node _hMatch
      exact Path.here
  | step hCall _hTail ih =>
      intro node hMatch
      rcases hSound.step_sound hMatch hCall with
        ⟨next, hSucc, hNextMatch⟩
      exact Path.step hSucc (ih hNextMatch)

theorem chain_to_path {Frame : Type}
    {edges : List Edge} {roots : List Node}
    {Matches : Node → Frame → Prop}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    (hSound : CallGraphSound edges roots Matches RootFrame DirectCall)
    {frame : Frame} {depth : Nat}
    (hRoot : RootFrame frame)
    (hChain : ConcreteCallChain DirectCall frame depth) :
    ∃ root, root ∈ roots ∧ Path edges root depth := by
  rcases hSound.root_sound hRoot with ⟨root, hRootMem, hMatch⟩
  exact ⟨root, hRootMem, hSound.path_from hChain hMatch⟩

theorem graph_chain {Frame : Type}
    {edges : List Edge} {roots : List Node}
    {Matches : Node → Frame → Prop}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    (hSound : CallGraphSound edges roots Matches RootFrame DirectCall)
    {frame : Frame} {depth : Nat}
    (hChain : ConcreteCallChain DirectCall frame depth) :
    ∀ {node}, Matches node frame →
      ConcreteCallChain (GraphStep edges) node depth := by
  induction hChain with
  | here =>
      intro _node _hMatch
      exact ConcreteCallChain.here
  | step hCall _hTail ih =>
      intro node hMatch
      rcases hSound.step_sound hMatch hCall with
        ⟨next, hSucc, hNextMatch⟩
      exact ConcreteCallChain.step hSucc (ih hNextMatch)

theorem chain_bound_of_graph_bound {Frame : Type}
    {edges : List Edge} {roots : List Node} {bound : Nat}
    {Matches : Node → Frame → Prop}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    (hSound : CallGraphSound edges roots Matches RootFrame DirectCall)
    (hBound : RootedGraphDepthBound edges roots bound)
    {frame : Frame} {depth : Nat}
    (hRoot : RootFrame frame)
    (hChain : ConcreteCallChain DirectCall frame depth) :
    depth + 1 ≤ bound := by
  rcases hSound.root_sound hRoot with ⟨root, hRootMem, hMatch⟩
  exact hBound.chain_bound hRootMem (hSound.graph_chain hChain hMatch)

theorem callChainDepthBound_of_graph_bound {Frame : Type}
    {edges : List Edge} {roots : List Node} {bound : Nat}
    {Matches : Node → Frame → Prop}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    (hSound : CallGraphSound edges roots Matches RootFrame DirectCall)
    (hBound : RootedGraphDepthBound edges roots bound) :
    CallChainDepthBound RootFrame DirectCall bound :=
  fun hRoot hChain => hSound.chain_bound_of_graph_bound hBound hRoot hChain

end CallGraphSound

namespace Program

mutual
  def rankedMaxDepthFrom? (edges : List Edge) :
      Nat → List Node → Node → Option Nat
    | 0, _stack, _node => none
    | fuel + 1, stack, node =>
        if node ∈ stack then
          none
        else
          rankedMaxDepthCalls? edges fuel (node :: stack)
            (Edge.successors edges node)

  def rankedMaxDepthCalls? (edges : List Edge) :
      Nat → List Node → List Node → Option Nat
    | _fuel, _stack, [] => some 0
    | fuel, stack, node :: rest => do
        let headDepth ← rankedMaxDepthFrom? edges fuel stack node
        let tailDepth ← rankedMaxDepthCalls? edges fuel stack rest
        some (max (headDepth + 1) tailDepth)
end

def rankedMaxRootDepth? (edges : List Edge) (roots : List Node) :
    Option Nat :=
  rankedMaxDepthCalls? edges (edges.length + roots.length + 1) [] roots

mutual
  theorem rankedMaxDepthFrom?_sound (edges : List Edge) :
      ∀ {fuel : Nat} {stack : List Node} {node : Node}
        {depth pathLen : Nat},
        rankedMaxDepthFrom? edges fuel stack node = some depth →
        Path edges node pathLen →
          pathLen ≤ depth
    | 0, _stack, _node, _depth, _pathLen, hDepth, _hPath => by
        simp [rankedMaxDepthFrom?] at hDepth
    | fuel + 1, stack, node, depth, pathLen, hDepth, hPath => by
        unfold rankedMaxDepthFrom? at hDepth
        by_cases hCycle : node ∈ stack
        · simp [hCycle] at hDepth
        · simp [hCycle] at hDepth
          cases hPath with
          | here =>
              exact Nat.zero_le depth
          | step hEdge hTail =>
              exact
                rankedMaxDepthCalls?_sound edges hDepth hEdge hTail
  termination_by fuel _ _ _ _ => (fuel, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem rankedMaxDepthCalls?_sound (edges : List Edge) :
      ∀ {fuel : Nat} {stack calls : List Node} {depth : Nat}
        {node : Node} {pathLen : Nat},
        rankedMaxDepthCalls? edges fuel stack calls = some depth →
        node ∈ calls →
        Path edges node pathLen →
          pathLen + 1 ≤ depth
    | fuel, stack, [], _depth, _node, _pathLen, _hDepth, hMem, _hPath => by
        simp at hMem
    | fuel, stack, head :: rest, depth, node, pathLen, hDepth, hMem,
        hPath => by
        unfold rankedMaxDepthCalls? at hDepth
        cases hHead : rankedMaxDepthFrom? edges fuel stack head with
        | none =>
            simp [hHead] at hDepth
        | some headDepth =>
            cases hTail :
                rankedMaxDepthCalls? edges fuel stack rest with
            | none =>
                simp [hHead, hTail] at hDepth
            | some tailDepth =>
                simp [hHead, hTail] at hDepth
                cases hDepth
                have hMem' : node = head ∨ node ∈ rest := by
                  simpa using hMem
                rcases hMem' with hName | hRest
                · cases hName
                  have hBound :=
                    rankedMaxDepthFrom?_sound edges hHead hPath
                  omega
                · have hBound :=
                    rankedMaxDepthCalls?_sound edges hTail hRest hPath
                  omega
  termination_by fuel _ calls _ _ _ => (fuel, calls.length + 1)
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

theorem rankedMaxRootDepth?_sound
    {edges : List Edge} {roots : List Node} {depth : Nat}
    (hDepth : rankedMaxRootDepth? edges roots = some depth)
    {node : Node} {pathLen : Nat}
    (hRoot : node ∈ roots)
    (hPath : Path edges node pathLen) :
    pathLen + 1 ≤ depth :=
  rankedMaxDepthCalls?_sound edges hDepth hRoot hPath

def rankedStackBudgetOk? (depth : Nat) : Bool :=
  decide (16 + 17 * depth + 17 ≤ 1024)

structure RankedDepthCheckResult
    (edges : List Edge) (roots : List Node) : Type where
  depth : Nat
  checked : rankedMaxRootDepth? edges roots = some depth
  budget : 16 + 17 * depth + 17 ≤ 1024

def rankedDepthCheck? (edges : List Edge) (roots : List Node) :
    Option (RankedDepthCheckResult edges roots) :=
  match hDepth : rankedMaxRootDepth? edges roots with
  | none => none
  | some depth =>
      if hBudget : 16 + 17 * depth + 17 ≤ 1024 then
        some
          { depth := depth
            checked := hDepth
            budget := hBudget }
      else
        none

theorem rankedDepthCheck?_eq_some
    {edges : List Edge} {roots : List Node}
    {check : RankedDepthCheckResult edges roots}
    (_hCheck : rankedDepthCheck? edges roots = some check) :
    rankedMaxRootDepth? edges roots = some check.depth ∧
      16 + 17 * check.depth + 17 ≤ 1024 := by
  exact ⟨check.checked, check.budget⟩

def rankedDepth? (edges : List Edge) (roots : List Node) :
    Option Nat :=
  match rankedMaxRootDepth? edges roots with
  | none => none
  | some depth =>
      if 16 + 17 * depth ≤ 1007 then
        some depth
      else
        none

theorem rankedDepth?_sound
    {edges : List Edge} {roots : List Node} {depth : Nat}
    (hDepth : rankedDepth? edges roots = some depth) :
    ∃ check : RankedDepthCheckResult edges roots,
      check.depth = depth := by
  unfold rankedDepth? at hDepth
  cases hRanked : rankedMaxRootDepth? edges roots with
  | none =>
      simp [hRanked] at hDepth
  | some checkedDepth =>
      by_cases hBudget : 16 + 17 * checkedDepth ≤ 1007
      · have hDepthEq : checkedDepth = depth := by
          simpa [hRanked, hBudget] using hDepth
        let check : RankedDepthCheckResult edges roots :=
          { depth := checkedDepth
            checked := hRanked
            budget := by omega }
        refine ⟨check, ?_⟩
        simpa [check] using hDepthEq
      · simp [hRanked, hBudget] at hDepth

def RankedDepthCheckResult.toStackBudget
    {edges : List Edge} {roots : List Node}
    (check : RankedDepthCheckResult edges roots) :
    _root_.EvmCompiler.Functions.CallDepth.StackBudget where
  depth := check.depth
  budget := check.budget

theorem RankedDepthCheckResult.path_bound
    {edges : List Edge} {roots : List Node}
    (check : RankedDepthCheckResult edges roots)
    {node : Node} {pathLen : Nat}
    (hRoot : node ∈ roots)
    (hPath : Path edges node pathLen) :
    pathLen + 1 ≤ check.depth :=
  rankedMaxRootDepth?_sound check.checked hRoot hPath

theorem RankedDepthCheckResult.toRootedGraphDepthBound
    {edges : List Edge} {roots : List Node}
    (check : RankedDepthCheckResult edges roots) :
    RootedGraphDepthBound edges roots check.depth where
  chain_bound := by
    intro root depth hRoot hChain
    exact check.path_bound hRoot (graphStepChain_to_path hChain)

end Program

namespace CallGraphSound

theorem chain_frame_count_bound {Frame : Type}
    {edges : List Edge} {roots : List Node}
    {Matches : Node → Frame → Prop}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    (hSound : CallGraphSound edges roots Matches RootFrame DirectCall)
    (check : Program.RankedDepthCheckResult edges roots)
    {frame : Frame} {depth : Nat}
    (hRoot : RootFrame frame)
    (hChain : ConcreteCallChain DirectCall frame depth) :
    depth + 1 ≤ check.depth :=
  hSound.chain_bound_of_graph_bound check.toRootedGraphDepthBound hRoot hChain

theorem callChainDepthBound_of_ranked {Frame : Type}
    {edges : List Edge} {roots : List Node}
    {Matches : Node → Frame → Prop}
    {RootFrame : Frame → Prop}
    {DirectCall : Frame → Frame → Prop}
    (hSound : CallGraphSound edges roots Matches RootFrame DirectCall)
    (check : Program.RankedDepthCheckResult edges roots) :
    CallChainDepthBound RootFrame DirectCall check.depth :=
  hSound.callChainDepthBound_of_graph_bound check.toRootedGraphDepthBound

end CallGraphSound

def edgeNodes : List Edge → List Node
  | [] => []
  | edge :: rest => edge.src :: edge.dst :: edgeNodes rest

def graphNodes (edges : List Edge) (roots : List Node) : List Node :=
  roots ++ edgeNodes edges

def hasSuccessorNamed? (edges : List Edge) (node : Node)
    (callee : Name) : Bool :=
  decide (∃ next,
    next ∈ Edge.successors edges node ∧ next.functionName = callee)

def rootsCover? (program : Functions.Program) (roots : List Node) :
    Bool :=
  (_root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls program).all
    (fun callee =>
      decide (∃ root, root ∈ roots ∧ root.functionName = callee))

def nodeCovers? (program : Functions.Program) (edges : List Edge)
    (node : Node) : Bool :=
  match FunList.find? node.functionName program.functions with
  | none => false
  | some fn =>
      (FunDef.internalCalls fn).all
        (fun callee => hasSuccessorNamed? edges node callee)

def graphConforms? (program : Functions.Program) (edges : List Edge)
    (roots : List Node) : Bool :=
  rootsCover? program roots &&
    (graphNodes edges roots).all (nodeCovers? program edges)

theorem list_all_eq_true_of_mem {α : Type} (p : α → Bool) :
    ∀ {values : List α} {value : α},
      values.all p = true →
      value ∈ values →
        p value = true
  | [], _value, hAll, hMem => by
      simp at hMem
  | head :: rest, value, hAll, hMem => by
      simp only [List.all_cons] at hAll
      simp at hAll
      have hHead : p head = true := by
        exact hAll.1
      have hMem' : value = head ∨ value ∈ rest := by
        simpa using hMem
      rcases hMem' with hEq | hRest
      · cases hEq
        exact hHead
      · exact hAll.2 value hRest

namespace GraphHeight

def lookupNodeHeight? : List (Node × Nat) → Node → Option Nat
  | [], _node => none
  | (candidate, height) :: rest, node =>
      if candidate = node then
        some height
      else
        lookupNodeHeight? rest node

def nodeHeight (heights : List (Node × Nat)) (node : Node) : Nat :=
  (lookupNodeHeight? heights node).getD 0

def rootHeightOk? (heights : List (Node × Nat)) (bound : Nat)
    (root : Node) : Bool :=
  match lookupNodeHeight? heights root with
  | none => false
  | some height => decide (height + 1 ≤ bound)

def edgeHeightOk? (heights : List (Node × Nat)) (edge : Edge) : Bool :=
  match lookupNodeHeight? heights edge.src,
      lookupNodeHeight? heights edge.dst with
  | some srcHeight, some dstHeight => decide (dstHeight < srcHeight)
  | _, _ => false

def graphHeightBound? (edges : List Edge) (roots : List Node)
    (heights : List (Node × Nat)) (bound : Nat) : Bool :=
  roots.all (rootHeightOk? heights bound) &&
    edges.all (edgeHeightOk? heights)

theorem lookupNodeHeight?_nodeHeight
    {heights : List (Node × Nat)} {node : Node} {height : Nat}
    (hLookup : lookupNodeHeight? heights node = some height) :
    nodeHeight heights node = height := by
  simp [nodeHeight, hLookup]

theorem rootHeightOk?_sound
    {heights : List (Node × Nat)} {bound : Nat} {root : Node}
    (hCheck : rootHeightOk? heights bound root = true) :
    nodeHeight heights root + 1 ≤ bound := by
  unfold rootHeightOk? at hCheck
  cases hLookup : lookupNodeHeight? heights root with
  | none =>
      simp [hLookup] at hCheck
  | some height =>
      simp [hLookup] at hCheck
      simpa [lookupNodeHeight?_nodeHeight hLookup] using hCheck

theorem edgeHeightOk?_sound
    {heights : List (Node × Nat)} {edge : Edge}
    (hCheck : edgeHeightOk? heights edge = true) :
    nodeHeight heights edge.dst < nodeHeight heights edge.src := by
  unfold edgeHeightOk? at hCheck
  cases hSrc : lookupNodeHeight? heights edge.src with
  | none =>
      simp [hSrc] at hCheck
  | some srcHeight =>
      cases hDst : lookupNodeHeight? heights edge.dst with
      | none =>
          simp [hSrc, hDst] at hCheck
      | some dstHeight =>
          simp [hSrc, hDst] at hCheck
          simpa [lookupNodeHeight?_nodeHeight hSrc,
            lookupNodeHeight?_nodeHeight hDst] using hCheck

theorem graphHeightBound?_heightBound
    {edges : List Edge} {roots : List Node}
    {heights : List (Node × Nat)} {bound : Nat}
    (hCheck : graphHeightBound? edges roots heights bound = true) :
    HeightBound (fun node => node ∈ roots) (GraphStep edges)
      (nodeHeight heights) bound := by
  unfold graphHeightBound? at hCheck
  simp at hCheck
  rcases hCheck with ⟨hRoots, hEdges⟩
  refine
    { root_height := ?_
      step_decreases := ?_ }
  · intro root hRoot
    have hRootCheck := hRoots root hRoot
    exact rootHeightOk?_sound hRootCheck
  · intro node next hStep
    unfold GraphStep at hStep
    rcases Edge.mem_successors_exists_mem hStep with
      ⟨edge, hEdgeMem, hSrc, hDst⟩
    have hEdgeCheck := hEdges edge hEdgeMem
    have hDecrease := edgeHeightOk?_sound hEdgeCheck
    rw [hSrc, hDst] at hDecrease
    exact hDecrease

theorem graphHeightBound?_chainBound
    {edges : List Edge} {roots : List Node}
    {heights : List (Node × Nat)} {bound : Nat}
    (hCheck : graphHeightBound? edges roots heights bound = true) :
    CallChainDepthBound (fun node => node ∈ roots) (GraphStep edges)
      bound :=
  (graphHeightBound?_heightBound hCheck).callChainDepthBound

theorem graphHeightBound?_rootedGraphDepthBound
    {edges : List Edge} {roots : List Node}
    {heights : List (Node × Nat)} {bound : Nat}
    (hCheck : graphHeightBound? edges roots heights bound = true) :
    RootedGraphDepthBound edges roots bound where
  chain_bound := by
    intro root depth hRoot hChain
    exact graphHeightBound?_chainBound hCheck hRoot hChain

end GraphHeight

theorem hasSuccessorNamed?_sound
    {edges : List Edge} {node : Node} {callee : Name}
    (hCheck : hasSuccessorNamed? edges node callee = true) :
    ∃ next,
      next ∈ Edge.successors edges node ∧ next.functionName = callee := by
  exact of_decide_eq_true hCheck

theorem rootsCover?_sound
    {program : Functions.Program} {roots : List Node}
    (hCheck : rootsCover? program roots = true)
    {callee : Name}
    (hRoot :
      callee ∈
        _root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls
          program) :
    ∃ root, root ∈ roots ∧ root.functionName = callee := by
  unfold rootsCover? at hCheck
  have hCallee :=
    list_all_eq_true_of_mem
      (fun callee =>
        decide (∃ root, root ∈ roots ∧ root.functionName = callee))
      hCheck hRoot
  exact of_decide_eq_true hCallee

theorem nodeCovers?_sound
    {program : Functions.Program} {edges : List Edge} {node : Node}
    (hCheck : nodeCovers? program edges node = true)
    {fn : FunDef} {callee : Name}
    (hFind : FunList.find? node.functionName program.functions = some fn)
    (hCall : callee ∈ FunDef.internalCalls fn) :
    ∃ next,
      next ∈ Edge.successors edges node ∧ next.functionName = callee := by
  unfold nodeCovers? at hCheck
  rw [hFind] at hCheck
  have hCallee :=
    list_all_eq_true_of_mem
      (fun callee => hasSuccessorNamed? edges node callee)
      hCheck hCall
  exact hasSuccessorNamed?_sound hCallee

structure ProgramConformance (program : Functions.Program)
    (edges : List Edge) (roots : List Node) : Prop where
  root :
    ∀ {callee : Name},
      callee ∈
        _root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls
          program →
        ∃ root, root ∈ roots ∧ root.functionName = callee
  call :
    ∀ {node : Node},
      node ∈ graphNodes edges roots →
      ∀ {fn : FunDef} {callee : Name},
        FunList.find? node.functionName program.functions = some fn →
        callee ∈ FunDef.internalCalls fn →
          ∃ next,
            next ∈ Edge.successors edges node ∧
              next.functionName = callee

theorem graphConforms?_sound
    {program : Functions.Program} {edges : List Edge} {roots : List Node}
    (hCheck : graphConforms? program edges roots = true) :
    ProgramConformance program edges roots := by
  unfold graphConforms? at hCheck
  have hRoots : rootsCover? program roots = true :=
    (by
      simp at hCheck
      exact hCheck.1)
  have hNodes :
      ∀ node, node ∈ graphNodes edges roots →
        nodeCovers? program edges node = true :=
    (by
      simp at hCheck
      exact hCheck.2)
  refine
    { root := ?_
      call := ?_ }
  · intro callee hRoot
    exact rootsCover?_sound hRoots hRoot
  · intro node hNode fn callee hFind hCall
    have hNodeCheck := hNodes node hNode
    exact nodeCovers?_sound hNodeCheck hFind hCall

structure CheckedProgramCheckResult
    (program : Functions.Program) : Type where
  edges : List Edge
  roots : List Node
  depthCheck : Program.RankedDepthCheckResult edges roots
  conforms : graphConforms? program edges roots = true

structure CheckedProgramRecurrenceCheckResult
    (program : Functions.Program) : Type where
  edges : List Edge
  roots : List Node
  depth : Nat
  checked : Program.rankedMaxRootDepth? edges roots = some depth
  conforms : graphConforms? program edges roots = true

def checkedProgramCheck? (program : Functions.Program)
    (edges : List Edge) (roots : List Node) :
    Option (CheckedProgramCheckResult program) :=
  match Program.rankedDepthCheck? edges roots with
  | none => none
  | some depthCheck =>
      if hConforms : graphConforms? program edges roots = true then
        some
          { edges := edges
            roots := roots
            depthCheck := depthCheck
            conforms := hConforms }
      else
        none

def checkedProgramRecurrenceDepth? (program : Functions.Program)
    (edges : List Edge) (roots : List Node) : Option Nat :=
  match Program.rankedMaxRootDepth? edges roots with
  | none => none
  | some depth =>
      if graphConforms? program edges roots = true then
        some depth
      else
        none

def checkedProgramDepth? (program : Functions.Program)
    (edges : List Edge) (roots : List Node) : Option Nat :=
  match Program.rankedDepth? edges roots with
  | none => none
  | some depth =>
      if graphConforms? program edges roots = true then
        some depth
      else
        none

theorem checkedProgramRecurrenceDepth?_sound
    {program : Functions.Program} {edges : List Edge} {roots : List Node}
    {depth : Nat}
    (hDepth :
      checkedProgramRecurrenceDepth? program edges roots = some depth) :
    ∃ check : CheckedProgramRecurrenceCheckResult program,
      check.depth = depth := by
  unfold checkedProgramRecurrenceDepth? at hDepth
  cases hRanked : Program.rankedMaxRootDepth? edges roots with
  | none =>
      simp [hRanked] at hDepth
  | some checkedDepth =>
      by_cases hConforms : graphConforms? program edges roots = true
      · have hDepthEq : checkedDepth = depth := by
          simpa [hRanked, hConforms] using hDepth
        let check : CheckedProgramRecurrenceCheckResult program :=
          { edges := edges
            roots := roots
            depth := checkedDepth
            checked := hRanked
            conforms := hConforms }
        refine ⟨check, ?_⟩
        simpa [check] using hDepthEq
      · simp [hRanked, hConforms] at hDepth

theorem checkedProgramDepth?_sound
    {program : Functions.Program} {edges : List Edge} {roots : List Node}
    {depth : Nat}
    (hDepth : checkedProgramDepth? program edges roots = some depth) :
    ∃ check : CheckedProgramCheckResult program,
      check.depthCheck.depth = depth := by
  unfold checkedProgramDepth? at hDepth
  cases hRanked : Program.rankedDepth? edges roots with
  | none =>
      simp [hRanked] at hDepth
  | some checkedDepth =>
      by_cases hConforms : graphConforms? program edges roots = true
      · simp [hRanked, hConforms] at hDepth
        cases hDepth
        rcases Program.rankedDepth?_sound hRanked with
          ⟨depthCheck, hDepthEq⟩
        cases hDepthEq
        let check : CheckedProgramCheckResult program :=
          { edges := edges
            roots := roots
            depthCheck := depthCheck
            conforms := hConforms }
        exact ⟨check, rfl⟩
      · simp [hRanked, hConforms] at hDepth

/--
Small executable sidecar format for stack-recursion checking.

Inference may synthesize one of these, or callers may provide one explicitly,
but soundness always goes through `checkStackRecurrenceCandidate?`.
-/
structure StackRecurrenceCandidate where
  edges : List Edge
  roots : List Node
  deriving DecidableEq, Repr

def rankZeroNode (name : Name) : Node :=
  { functionName := name, rank := 0 }

def inferredRoots (program : Functions.Program) : List Node :=
  (_root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls program).map
    rankZeroNode

def inferredEdgesForFunction (fn : FunDef) : List Edge :=
  (FunDef.internalCalls fn).map
    (fun callee => { src := rankZeroNode fn.name, dst := rankZeroNode callee })

def inferredEdgesForFunctions : List FunDef → List Edge
  | [] => []
  | fn :: rest => inferredEdgesForFunction fn ++ inferredEdgesForFunctions rest

def inferredEdges (program : Functions.Program) : List Edge :=
  inferredEdgesForFunctions program.functions

def inferredAcyclicCandidate
    (program : Functions.Program) : StackRecurrenceCandidate where
  edges := inferredEdges program
  roots := inferredRoots program

def checkStackRecurrenceCandidate? (program : Functions.Program)
    (check : StackRecurrenceCandidate) :
    Option (CheckedProgramCheckResult program) :=
  checkedProgramCheck? program check.edges check.roots

/--
Conservative built-in analyzer for the ranked checker.

It assigns every function to rank zero and emits one edge for each syntactic
internal call.  Therefore it accepts exactly the acyclic call-graph cases the
ranked checker can verify without path/ranking information.  Recursive cycles
remain rejected until a stronger source-state analysis can justify why the
ranked base cases do not execute the recursive calls.
-/
def inferAcyclicCheck? (program : Functions.Program) :
    Option (CheckedProgramCheckResult program) :=
  checkStackRecurrenceCandidate? program
    (inferredAcyclicCandidate program)

def inferStackRecurrenceCandidate?
    (program : Functions.Program) :
    Option StackRecurrenceCandidate :=
  some (inferredAcyclicCandidate program)

def inferStackRecurrences? (program : Functions.Program) :
    Option (CheckedProgramCheckResult program) :=
  match inferStackRecurrenceCandidate? program with
  | none => none
  | some check => checkStackRecurrenceCandidate? program check

def inferAcyclicDepth? (program : Functions.Program) : Option Nat :=
  checkedProgramDepth? program (inferredEdges program) (inferredRoots program)

def inferAcyclicRecurrenceDepth? (program : Functions.Program) : Option Nat :=
  checkedProgramRecurrenceDepth? program (inferredEdges program)
    (inferredRoots program)

theorem inferAcyclicDepth?_sound
    {program : Functions.Program} {depth : Nat}
    (hDepth : inferAcyclicDepth? program = some depth) :
    ∃ check : CheckedProgramCheckResult program,
      check.depthCheck.depth = depth := by
  unfold inferAcyclicDepth? at hDepth
  exact checkedProgramDepth?_sound hDepth

theorem inferAcyclicRecurrenceDepth?_sound
    {program : Functions.Program} {depth : Nat}
    (hDepth : inferAcyclicRecurrenceDepth? program = some depth) :
    ∃ check : CheckedProgramRecurrenceCheckResult program,
      check.depth = depth := by
  unfold inferAcyclicRecurrenceDepth? at hDepth
  exact checkedProgramRecurrenceDepth?_sound hDepth

namespace CheckedProgramCheckResult

def toStackBudget {program : Functions.Program}
    (check : CheckedProgramCheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.StackBudget :=
  check.depthCheck.toStackBudget

theorem conformance {program : Functions.Program}
    (check : CheckedProgramCheckResult program) :
    ProgramConformance program check.edges check.roots :=
  graphConforms?_sound check.conforms

def toStackResourceCheckResult {program : Functions.Program}
    (check : CheckedProgramCheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceCheckResult
      program where
  budget := check.toStackBudget
  baseSafe :=
    _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafeFromBase_of_budget
      program check.toStackBudget
  safe :=
    _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafe_of_budget
      program check.toStackBudget

theorem stackResourceSafe {program : Functions.Program}
    (check : CheckedProgramCheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceSafe program
      check.toStackBudget :=
  (toStackResourceCheckResult check).safe

end CheckedProgramCheckResult

namespace CheckedProgramRecurrenceCheckResult

theorem conformance {program : Functions.Program}
    (check : CheckedProgramRecurrenceCheckResult program) :
    ProgramConformance program check.edges check.roots :=
  graphConforms?_sound check.conforms

theorem rootedGraphDepthBound {program : Functions.Program}
    (check : CheckedProgramRecurrenceCheckResult program) :
    RootedGraphDepthBound check.edges check.roots check.depth where
  chain_bound := by
    intro root depth hRoot hChain
    exact
      Program.rankedMaxRootDepth?_sound check.checked hRoot
        (graphStepChain_to_path hChain)

end CheckedProgramRecurrenceCheckResult

namespace SelfGuardedOnce

def zero : Word :=
  EvmYul.UInt256.ofNat 0

def node (name : Name) (rank : Nat) : Node :=
  { functionName := name, rank := rank }

def edgesUpTo (name : Name) : Nat → List Edge
  | 0 => []
  | rank + 1 =>
      { src := node name (rank + 1), dst := node name rank } ::
        edgesUpTo name rank

def maxRank : List Node → Nat
  | [] => 0
  | root :: rest => max root.rank (maxRank rest)

def varName? {results : Nat} : Expr results → Option Name
  | .var name => some name
  | _ => none

def litValue? {results : Nat} : Expr results → Option Word
  | .lit value => some value
  | _ => none

def functionShape? (fn : FunDef) : Option Name :=
  match fn.params, fn.returns, fn.body.stmts with
  | [counter], [], [.if_ cond { stmts := [.call [] callee [arg]] }] =>
      if varName? cond == some counter && callee == fn.name &&
          litValue? arg == some zero then
        some fn.name
      else
        none
  | _, _, _ => none

def rootFromStmt? (functionName : Name) : Stmt → Option Node
  | .call [] callee [arg] =>
      match litValue? arg with
      | none => none
      | some rank =>
          if callee == functionName then
            some (node functionName (if rank == zero then 0 else 1))
          else
            none
  | _ => none

def rootsFromStmts? (functionName : Name) : List Stmt → Option (List Node)
  | [] => some []
  | stmt :: rest => do
      let root ← rootFromStmt? functionName stmt
      let roots ← rootsFromStmts? functionName rest
      some (root :: roots)

def programShape? (program : Functions.Program) :
    Option (Name × List Node) :=
  match program.functions with
  | [fn] => do
      let functionName ← functionShape? fn
      let roots ← rootsFromStmts? functionName program.body.stmts
      some (functionName, roots)
  | _ => none

/--
Checked executable check result for the first genuinely recursive source pattern
we can recognize without a proof-carrying user witness.

The accepted shape is intentionally tiny: a single non-returning function
`f(counter)` whose body is exactly `if counter { f(0) }`, and a main body made
only of calls to `f` with literal arguments.  Zero-valued root calls receive
rank zero; nonzero literal roots receive rank one.  The checker builds the
finite one-step self-recursive graph and rechecks the generic ranked depth and
budget check result.

This is not yet the general public theorem boundary for recursive source
programs.  It is the executable Rung-B seed: it proves that a recursive internal
call cycle can be accepted only through a checker-owned finite ranked graph.
-/
structure CheckResult (program : Functions.Program) : Type where
  functionName : Name
  roots : List Node
  edges : List Edge
  shape : programShape? program = some (functionName, roots)
  edges_eq : edges = edgesUpTo functionName (maxRank roots)
  depthCheck : Program.RankedDepthCheckResult edges roots

def checkResult? (program : Functions.Program) :
    Option (CheckResult program) :=
  match hShape : programShape? program with
  | none => none
  | some (functionName, roots) =>
      let maxRoot := maxRank roots
      let edges := edgesUpTo functionName maxRoot
      match Program.rankedDepthCheck? edges roots with
      | none => none
      | some depthCheck =>
          some
            { functionName := functionName
              roots := roots
              edges := edges
              shape := hShape
              edges_eq := rfl
              depthCheck := depthCheck }

theorem checkResult?_eq_some
    {program : Functions.Program}
    {check : CheckResult program}
    (_hCheck : checkResult? program = some check) :
    programShape? program = some (check.functionName, check.roots) ∧
      check.edges = edgesUpTo check.functionName (maxRank check.roots) ∧
      Program.rankedMaxRootDepth? check.edges check.roots =
        some check.depthCheck.depth ∧
      16 + 17 * check.depthCheck.depth + 17 ≤ 1024 :=
  ⟨check.shape, check.edges_eq, check.depthCheck.checked,
    check.depthCheck.budget⟩

def checkedDepth? (program : Functions.Program) : Option Nat :=
  match programShape? program with
  | none => none
  | some (functionName, roots) =>
      Program.rankedDepth? (edgesUpTo functionName (maxRank roots)) roots

theorem checkedDepth?_sound
    {program : Functions.Program} {depth : Nat}
    (hDepth : checkedDepth? program = some depth) :
    ∃ check : CheckResult program,
      check.depthCheck.depth = depth := by
  unfold checkedDepth? at hDepth
  cases hShape : programShape? program with
  | none =>
      simp [hShape] at hDepth
  | some shape =>
      rcases shape with ⟨functionName, roots⟩
      simp [hShape] at hDepth
      rcases Program.rankedDepth?_sound hDepth with
        ⟨depthCheck, hDepthEq⟩
      cases hDepthEq
      let check : CheckResult program :=
        { functionName := functionName
          roots := roots
          edges := edgesUpTo functionName (maxRank roots)
          shape := hShape
          edges_eq := rfl
          depthCheck := depthCheck }
      exact ⟨check, rfl⟩

theorem functionShape_name
    {fn : FunDef} {name : Name}
    (hShape : functionShape? fn = some name) :
    fn.name = name := by
  unfold functionShape? at hShape
  split at hShape <;> simp at hShape
  exact hShape.2

theorem functionShape_internalCalls
    {fn : FunDef} {name : Name}
    (hShape : functionShape? fn = some name) :
    FunDef.internalCalls fn = [name] := by
  unfold functionShape? at hShape
  split at hShape <;> simp at hShape
  rename_i counter cond callee arg hParams hReturns hBody
  have hCallee : callee = name := by
    rw [hShape.1.1.2, hShape.2]
  cases hBodyObj : fn.body with
  | mk stmts =>
      rw [hBodyObj] at hBody
      simp at hBody
      simp [FunDef.internalCalls, blockInternalCalls, hBodyObj]
      rw [hBody]
      change blockInternalCalls { stmts := [Stmt.call [] callee [arg]] } =
        [name]
      simp [blockInternalCalls, stmtListInternalCalls, stmtInternalCalls,
        hCallee]

theorem functionShape_bodyFacts
    {fn : FunDef} {name : Name}
    (hShape : functionShape? fn = some name) :
    ∃ counter cond arg,
      fn.name = name ∧
        fn.params = [counter] ∧
        fn.returns = [] ∧
        fn.body.stmts =
          [.if_ cond { stmts := [.call [] name [arg]] }] ∧
        varName? cond = some counter ∧
        (litValue? arg == some zero) = true := by
  unfold functionShape? at hShape
  split at hShape <;> simp at hShape
  rename_i counter cond callee arg hParams hReturns hBody
  have hCallee : callee = name := by
    rw [hShape.1.1.2, hShape.2]
  refine
    ⟨counter, cond, arg, hShape.2, hParams, hReturns, ?_, ?_, ?_⟩
  · simpa [hCallee] using hBody
  · exact hShape.1.1.1
  · exact hShape.1.2

theorem programShape_find_function_shape
    {program : Functions.Program} {name : Name} {roots : List Node}
    (hShape : programShape? program = some (name, roots)) :
    ∃ fn,
      FunList.find? name program.functions = some fn ∧
        functionShape? fn = some name ∧
        rootsFromStmts? name program.body.stmts = some roots := by
  unfold programShape? at hShape
  cases hFns : program.functions with
  | nil =>
      simp [hFns] at hShape
  | cons fn rest =>
      cases rest with
      | nil =>
          simp [hFns] at hShape
          cases hFunShape : functionShape? fn with
          | none =>
              simp [hFunShape] at hShape
          | some functionName =>
              simp [hFunShape] at hShape
              cases hRoots :
                  rootsFromStmts? functionName program.body.stmts with
              | none =>
                  simp [hRoots] at hShape
              | some roots' =>
                  simp [hRoots] at hShape
                  rcases hShape with ⟨rfl, rfl⟩
                  refine ⟨fn, ?_, hFunShape, hRoots⟩
                  simp [FunList.find?, functionShape_name hFunShape]
      | cons _fn2 _rest2 =>
          simp [hFns] at hShape

theorem programShape_find_function
    {program : Functions.Program} {name : Name} {roots : List Node}
    (hShape : programShape? program = some (name, roots)) :
    ∃ fn,
      FunList.find? name program.functions = some fn ∧
        FunDef.internalCalls fn = [name] := by
  unfold programShape? at hShape
  cases hFns : program.functions with
  | nil =>
      simp [hFns] at hShape
  | cons fn rest =>
      cases rest with
      | nil =>
          simp [hFns] at hShape
          cases hFunShape : functionShape? fn with
          | none =>
              simp [hFunShape] at hShape
          | some functionName =>
              simp [hFunShape] at hShape
              cases hRoots :
                  rootsFromStmts? functionName program.body.stmts with
              | none =>
                  simp [hRoots] at hShape
              | some roots' =>
                  simp [hRoots] at hShape
                  rcases hShape with ⟨rfl, rfl⟩
                  refine ⟨fn, ?_, ?_⟩
                  · simp [FunList.find?, functionShape_name hFunShape]
                  · exact functionShape_internalCalls hFunShape
      | cons _fn2 _rest2 =>
          simp [hFns] at hShape

theorem CheckResult.find_function
    {program : Functions.Program}
    (check : CheckResult program) :
    ∃ fn,
      FunList.find? check.functionName program.functions = some fn ∧
        FunDef.internalCalls fn = [check.functionName] :=
  programShape_find_function check.shape

theorem CheckResult.find_function_shape
    {program : Functions.Program}
    (check : CheckResult program) :
    ∃ fn,
      FunList.find? check.functionName program.functions = some fn ∧
        functionShape? fn = some check.functionName ∧
        rootsFromStmts? check.functionName program.body.stmts =
          some check.roots :=
  programShape_find_function_shape check.shape

theorem CheckResult.function_bodyFacts
    {program : Functions.Program}
    (check : CheckResult program) :
    ∃ fn counter cond arg,
      FunList.find? check.functionName program.functions = some fn ∧
        fn.name = check.functionName ∧
        fn.params = [counter] ∧
        fn.returns = [] ∧
        fn.body.stmts =
          [.if_ cond
            { stmts := [.call [] check.functionName [arg]] }] ∧
        varName? cond = some counter ∧
        (litValue? arg == some zero) = true := by
  rcases check.find_function_shape with
    ⟨fn, hFind, hShape, _hRoots⟩
  rcases functionShape_bodyFacts hShape with
    ⟨counter, cond, arg, hName, hParams, hReturns, hBody, hCond,
      hArg⟩
  exact
    ⟨fn, counter, cond, arg, hFind, hName, hParams, hReturns, hBody,
      hCond, hArg⟩

theorem rootFromStmt?_eq_some_facts
    {name : Name} {stmt : Stmt} {root : Node}
    (hRoot : rootFromStmt? name stmt = some root) :
    root.functionName = name ∧ root.rank ≤ 1 ∧
      name ∈ stmtInternalCalls stmt := by
  cases stmt with
  | call targets callee args =>
      cases targets with
      | nil =>
          cases args with
          | nil =>
              simp [rootFromStmt?] at hRoot
          | cons arg rest =>
              cases rest with
              | nil =>
                  cases hLit : litValue? arg with
                  | none =>
                      simp [rootFromStmt?, hLit] at hRoot
                  | some value =>
                      by_cases hCallee : callee = name
                      · simp [rootFromStmt?, hLit, hCallee] at hRoot
                        cases hRoot
                        constructor
                        · simp [node]
                        constructor
                        · simp [node]
                          split <;> omega
                        · simp [stmtInternalCalls, hCallee]
                      · simp [rootFromStmt?, hLit, hCallee] at hRoot
              | cons _arg2 _rest2 =>
                  simp [rootFromStmt?] at hRoot
      | cons _target _restTargets =>
          cases args <;> simp [rootFromStmt?] at hRoot
  | expr _ =>
      simp [rootFromStmt?] at hRoot
  | let_ _ _ =>
      simp [rootFromStmt?] at hRoot
  | assign _ _ =>
      simp [rootFromStmt?] at hRoot
  | block _ =>
      simp [rootFromStmt?] at hRoot
  | if_ _ _ =>
      simp [rootFromStmt?] at hRoot
  | switch _ _ _ =>
      simp [rootFromStmt?] at hRoot
  | for_ _ _ _ _ =>
      simp [rootFromStmt?] at hRoot
  | brk =>
      simp [rootFromStmt?] at hRoot
  | cont =>
      simp [rootFromStmt?] at hRoot
  | leave =>
      simp [rootFromStmt?] at hRoot
  | terminal _ =>
      simp [rootFromStmt?] at hRoot
  | terminalArgs _ _ =>
      simp [rootFromStmt?] at hRoot

theorem rootsFromStmts?_mem_facts
    {name : Name} :
    ∀ {stmts : List Stmt} {roots : List Node} {root : Node},
      rootsFromStmts? name stmts = some roots →
        root ∈ roots →
          root.functionName = name ∧ root.rank ≤ 1 ∧
            name ∈ stmtListInternalCalls stmts
  | [], roots, root, hRoots, hMem => by
      simp [rootsFromStmts?] at hRoots
      cases hRoots
      simp at hMem
  | stmt :: rest, roots, root, hRoots, hMem => by
      unfold rootsFromStmts? at hRoots
      cases hHead : rootFromStmt? name stmt with
      | none =>
          simp [hHead] at hRoots
      | some headRoot =>
          simp [hHead] at hRoots
          cases hTail : rootsFromStmts? name rest with
          | none =>
              simp [hTail] at hRoots
          | some tailRoots =>
              simp [hTail] at hRoots
              cases hRoots
              simp at hMem
              rcases hMem with hEq | hRest
              · subst root
                rcases rootFromStmt?_eq_some_facts hHead with
                  ⟨hName, hRank, hCall⟩
                exact ⟨hName, hRank,
                  by simp [stmtListInternalCalls, hCall]⟩
              · rcases rootsFromStmts?_mem_facts hTail hRest with
                  ⟨hName, hRank, hCall⟩
                exact ⟨hName, hRank,
                  by simp [stmtListInternalCalls, hCall]⟩

theorem programShape_root_mem_facts
    {program : Functions.Program} {name : Name} {roots : List Node}
    (hShape : programShape? program = some (name, roots))
    {root : Node} (hRoot : root ∈ roots) :
    root.functionName = name ∧ root.rank ≤ 1 ∧
      name ∈ stmtListInternalCalls program.body.stmts := by
  unfold programShape? at hShape
  cases hFns : program.functions with
  | nil =>
      simp [hFns] at hShape
  | cons fn rest =>
      cases rest with
      | nil =>
          simp [hFns] at hShape
          cases hFunShape : functionShape? fn with
          | none =>
              simp [hFunShape] at hShape
          | some functionName =>
              simp [hFunShape] at hShape
              cases hRoots :
                  rootsFromStmts? functionName program.body.stmts with
              | none =>
                  simp [hRoots] at hShape
              | some roots' =>
                  simp [hRoots] at hShape
                  rcases hShape with ⟨rfl, rfl⟩
                  rcases rootsFromStmts?_mem_facts hRoots hRoot with
                    ⟨hName, hRank, hCall⟩
                  exact ⟨hName, hRank, hCall⟩
      | cons _fn2 _rest2 =>
          simp [hFns] at hShape

theorem CheckResult.root_mem_facts
    {program : Functions.Program}
    (check : CheckResult program)
    {root : Node} (hRoot : root ∈ check.roots) :
    root.functionName = check.functionName ∧ root.rank ≤ 1 ∧
      check.functionName ∈
        _root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls
          program :=
  by
    rcases programShape_root_mem_facts check.shape hRoot with
      ⟨hName, hRank, hCall⟩
    refine ⟨hName, hRank, ?_⟩
    cases hBody : program.body with
    | mk stmts =>
        rw [hBody] at hCall
        simpa
          [_root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls,
            blockInternalCalls, hBody]
          using hCall

theorem maxRank_le_one_of_all_roots_le_one :
    ∀ {roots : List Node},
      (∀ root, root ∈ roots → root.rank ≤ 1) →
        maxRank roots ≤ 1
  | [], _hRoots => by
      simp [maxRank]
  | head :: rest, hRoots => by
      have hHead : head.rank ≤ 1 := hRoots head (by simp)
      have hRest :
          maxRank rest ≤ 1 :=
        maxRank_le_one_of_all_roots_le_one
          (fun root hRoot => hRoots root (by simp [hRoot]))
      simp [maxRank]
      omega

theorem CheckResult.maxRank_le_one
    {program : Functions.Program}
    (check : CheckResult program) :
    maxRank check.roots ≤ 1 := by
  exact
    maxRank_le_one_of_all_roots_le_one
      (fun root hRoot => (check.root_mem_facts hRoot).2.1)

theorem CheckResult.edges_empty_or_one
    {program : Functions.Program}
    (check : CheckResult program) :
    check.edges = [] ∨
      check.edges =
        [{ src := node check.functionName 1
           dst := node check.functionName 0 }] := by
  have hMax := check.maxRank_le_one
  rw [check.edges_eq]
  cases hRank : maxRank check.roots with
  | zero =>
      left
      simp [edgesUpTo]
  | succ rank =>
      cases rank with
      | zero =>
          right
          simp [edgesUpTo, node]
      | succ rank =>
          have hTooLarge : 2 ≤ maxRank check.roots := by
            rw [hRank]
            omega
          omega

theorem rank_le_maxRank_of_mem :
    ∀ {roots : List Node} {root : Node},
      root ∈ roots → root.rank ≤ maxRank roots
  | [], _root, hMem => by
      simp at hMem
  | head :: rest, root, hMem => by
      have hMem' : root = head ∨ root ∈ rest := by
        simpa using hMem
      rcases hMem' with hEq | hRest
      · subst root
        simp [maxRank]
      · have hTail := rank_le_maxRank_of_mem hRest
        simp [maxRank]
        omega

theorem zero_successor_one_edgesUpTo (name : Name) :
    ∀ {rank : Nat},
      1 ≤ rank →
        node name 0 ∈ Edge.successors (edgesUpTo name rank) (node name 1)
  | 0, hRank => by
      omega
  | rank + 1, hRank => by
      cases rank with
      | zero =>
          simp [edgesUpTo, Edge.successors, node]
      | succ rank =>
          have hTail :
              node name 0 ∈
                Edge.successors (edgesUpTo name (rank + 1)) (node name 1) :=
            zero_successor_one_edgesUpTo name (by omega)
          have hSrc :
              (node name (rank + 1 + 1)) ≠ node name 1 := by
            simp [node]
          unfold edgesUpTo Edge.successors
          simp [hSrc]
          simpa [Edge.successors] using hTail

theorem CheckResult.edge_one_zero_of_root
    {program : Functions.Program}
    (check : CheckResult program)
    (hRoot : node check.functionName 1 ∈ check.roots) :
    node check.functionName 0 ∈
      Edge.successors check.edges (node check.functionName 1) := by
  have hRank :
      1 ≤ maxRank check.roots := by
    have hLe :=
      rank_le_maxRank_of_mem (roots := check.roots)
        (root := node check.functionName 1) hRoot
    simpa [node] using hLe
  rw [check.edges_eq]
  exact zero_successor_one_edgesUpTo check.functionName hRank

def CheckResult.toStackBudget
    {program : Functions.Program}
    (check : CheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.StackBudget :=
  check.depthCheck.toStackBudget

def CheckResult.toStackResourceCheckResult
    {program : Functions.Program}
    (check : CheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceCheckResult
      program where
  budget := check.toStackBudget
  baseSafe :=
    _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafeFromBase_of_budget
      program check.toStackBudget
  safe :=
    _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafe_of_budget
      program check.toStackBudget

theorem CheckResult.stackResourceSafe
    {program : Functions.Program}
    (check : CheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceSafe program
      check.toStackBudget :=
  check.toStackResourceCheckResult.safe

end SelfGuardedOnce

namespace MutualGuardedOnce

abbrev zero : Word :=
  SelfGuardedOnce.zero

abbrev node (name : Name) (rank : Nat) : Node :=
  SelfGuardedOnce.node name rank

abbrev maxRank (roots : List Node) : Nat :=
  SelfGuardedOnce.maxRank roots

def edgesUpTo (left right : Name) : Nat → List Edge
  | 0 => []
  | rank + 1 =>
      { src := node left (rank + 1), dst := node right rank } ::
      { src := node right (rank + 1), dst := node left rank } ::
      edgesUpTo left right rank

def functionShape? (fn : FunDef) : Option (Name × Name) :=
  match fn.params, fn.returns, fn.body.stmts with
  | [counter], [], [.if_ cond { stmts := [.call [] callee [arg]] }] =>
      if SelfGuardedOnce.varName? cond == some counter &&
          SelfGuardedOnce.litValue? arg == some zero then
        some (fn.name, callee)
      else
        none
  | _, _, _ => none

def rootFromStmt? (left right : Name) : Stmt → Option Node
  | .call [] callee [arg] =>
      match SelfGuardedOnce.litValue? arg with
      | none => none
      | some rank =>
          if callee == left then
            some (node left (if rank == zero then 0 else 1))
          else if callee == right then
            some (node right (if rank == zero then 0 else 1))
          else
            none
  | _ => none

def rootsFromStmts? (left right : Name) : List Stmt → Option (List Node)
  | [] => some []
  | stmt :: rest => do
      let root ← rootFromStmt? left right stmt
      let roots ← rootsFromStmts? left right rest
      some (root :: roots)

def programShape? (program : Functions.Program) :
    Option (Name × Name × List Node) :=
  match program.functions with
  | [leftFn, rightFn] => do
      let (leftName, leftCallee) ← functionShape? leftFn
      let (rightName, rightCallee) ← functionShape? rightFn
      if leftName == rightName then
        none
      else if leftCallee == rightName && rightCallee == leftName then
        let roots ← rootsFromStmts? leftName rightName program.body.stmts
        some (leftName, rightName, roots)
      else
        none
  | _ => none

/--
Executable checker for the first bounded two-function recursive cycle.

The accepted shape is deliberately small: exactly two non-returning functions
`left(counter)` and `right(counter)`, where each body is `if counter` followed
by a call to the other function with literal zero.  Main may call either
function with a literal.  Literal zero roots are rank zero; nonzero literal
roots are rank one.  The checker then builds and checks the finite mutual
rank graph `left(1) -> right(0)` and `right(1) -> left(0)`.
-/
structure CheckResult (program : Functions.Program) : Type where
  leftName : Name
  rightName : Name
  roots : List Node
  edges : List Edge
  shape : programShape? program = some (leftName, rightName, roots)
  edges_eq : edges = edgesUpTo leftName rightName (maxRank roots)
  depthCheck : Program.RankedDepthCheckResult edges roots

def checkResult? (program : Functions.Program) :
    Option (CheckResult program) :=
  match hShape : programShape? program with
  | none => none
  | some (leftName, rightName, roots) =>
      let maxRoot := maxRank roots
      let edges := edgesUpTo leftName rightName maxRoot
      match Program.rankedDepthCheck? edges roots with
      | none => none
      | some depthCheck =>
          some
            { leftName := leftName
              rightName := rightName
              roots := roots
              edges := edges
              shape := hShape
              edges_eq := rfl
              depthCheck := depthCheck }

theorem checkResult?_eq_some
    {program : Functions.Program}
    {check : CheckResult program}
    (_hCheck : checkResult? program = some check) :
    programShape? program =
        some (check.leftName, check.rightName, check.roots) ∧
      check.edges = edgesUpTo check.leftName check.rightName
        (maxRank check.roots) ∧
      Program.rankedMaxRootDepth? check.edges check.roots =
        some check.depthCheck.depth ∧
      16 + 17 * check.depthCheck.depth + 17 ≤ 1024 :=
  ⟨check.shape, check.edges_eq, check.depthCheck.checked,
    check.depthCheck.budget⟩

def checkedDepth? (program : Functions.Program) : Option Nat :=
  match programShape? program with
  | none => none
  | some (leftName, rightName, roots) =>
      Program.rankedDepth? (edgesUpTo leftName rightName (maxRank roots))
        roots

theorem checkedDepth?_sound
    {program : Functions.Program} {depth : Nat}
    (hDepth : checkedDepth? program = some depth) :
    ∃ check : CheckResult program,
      check.depthCheck.depth = depth := by
  unfold checkedDepth? at hDepth
  cases hShape : programShape? program with
  | none =>
      simp [hShape] at hDepth
  | some shape =>
      rcases shape with ⟨leftName, rightName, roots⟩
      simp [hShape] at hDepth
      rcases Program.rankedDepth?_sound hDepth with
        ⟨depthCheck, hDepthEq⟩
      cases hDepthEq
      let check : CheckResult program :=
        { leftName := leftName
          rightName := rightName
          roots := roots
          edges := edgesUpTo leftName rightName (maxRank roots)
          shape := hShape
          edges_eq := rfl
          depthCheck := depthCheck }
      exact ⟨check, rfl⟩

theorem rootFromStmt?_eq_some_rank_le_one
    {left right : Name} {stmt : Stmt} {root : Node}
    (hRoot : rootFromStmt? left right stmt = some root) :
    root.rank ≤ 1 := by
  cases stmt with
  | call targets callee args =>
      cases targets with
      | nil =>
          cases args with
          | nil =>
              simp [rootFromStmt?] at hRoot
          | cons arg rest =>
              cases rest with
              | nil =>
                  cases hLit : SelfGuardedOnce.litValue? arg with
                  | none =>
                      simp [rootFromStmt?, hLit] at hRoot
                  | some value =>
                      simp [rootFromStmt?, hLit] at hRoot
                      split at hRoot
                      · cases hRoot
                        simp [node, SelfGuardedOnce.node]
                        split <;> omega
                      · split at hRoot
                        · cases hRoot
                          simp [node, SelfGuardedOnce.node]
                          split <;> omega
                        · simp at hRoot
              | cons _arg2 _rest2 =>
                  simp [rootFromStmt?] at hRoot
      | cons _target _restTargets =>
          cases args <;> simp [rootFromStmt?] at hRoot
  | expr _ =>
      simp [rootFromStmt?] at hRoot
  | let_ _ _ =>
      simp [rootFromStmt?] at hRoot
  | assign _ _ =>
      simp [rootFromStmt?] at hRoot
  | block _ =>
      simp [rootFromStmt?] at hRoot
  | if_ _ _ =>
      simp [rootFromStmt?] at hRoot
  | switch _ _ _ =>
      simp [rootFromStmt?] at hRoot
  | for_ _ _ _ _ =>
      simp [rootFromStmt?] at hRoot
  | brk =>
      simp [rootFromStmt?] at hRoot
  | cont =>
      simp [rootFromStmt?] at hRoot
  | leave =>
      simp [rootFromStmt?] at hRoot
  | terminal _ =>
      simp [rootFromStmt?] at hRoot
  | terminalArgs _ _ =>
      simp [rootFromStmt?] at hRoot

theorem rootsFromStmts?_mem_rank_le_one
    {left right : Name} :
    ∀ {stmts : List Stmt} {roots : List Node} {root : Node},
      rootsFromStmts? left right stmts = some roots →
        root ∈ roots →
          root.rank ≤ 1
  | [], roots, root, hRoots, hMem => by
      simp [rootsFromStmts?] at hRoots
      cases hRoots
      simp at hMem
  | stmt :: rest, roots, root, hRoots, hMem => by
      unfold rootsFromStmts? at hRoots
      cases hHead : rootFromStmt? left right stmt with
      | none =>
          simp [hHead] at hRoots
      | some headRoot =>
          simp [hHead] at hRoots
          cases hTail : rootsFromStmts? left right rest with
          | none =>
              simp [hTail] at hRoots
          | some tailRoots =>
              simp [hTail] at hRoots
              cases hRoots
              simp at hMem
              rcases hMem with hEq | hRest
              · subst root
                exact rootFromStmt?_eq_some_rank_le_one hHead
              · exact rootsFromStmts?_mem_rank_le_one hTail hRest

theorem programShape_root_rank_le_one
    {program : Functions.Program} {left right : Name} {roots : List Node}
    (hShape : programShape? program = some (left, right, roots))
    {root : Node} (hRoot : root ∈ roots) :
    root.rank ≤ 1 := by
  unfold programShape? at hShape
  cases hFns : program.functions with
  | nil =>
      simp [hFns] at hShape
  | cons leftFn rest =>
      cases rest with
      | nil =>
          simp [hFns] at hShape
      | cons rightFn rest2 =>
          cases rest2 with
          | nil =>
              simp [hFns] at hShape
              cases hLeft : functionShape? leftFn with
              | none =>
                  simp [hLeft] at hShape
              | some leftShape =>
                  rcases leftShape with ⟨leftName, leftCallee⟩
                  simp [hLeft] at hShape
                  cases hRight : functionShape? rightFn with
                  | none =>
                      simp [hRight] at hShape
                  | some rightShape =>
                      rcases rightShape with ⟨rightName, rightCallee⟩
                      simp [hRight] at hShape
                      rcases hShape with ⟨_hNe, _hCalls, hBind⟩
                      cases hRoots :
                          rootsFromStmts? leftName rightName
                            program.body.stmts with
                      | none =>
                          simp [hRoots] at hBind
                      | some roots' =>
                          simp [hRoots] at hBind
                          rcases hBind with ⟨rfl, rfl, rfl⟩
                          exact rootsFromStmts?_mem_rank_le_one hRoots hRoot
          | cons _third _more =>
              simp [hFns] at hShape

theorem CheckResult.maxRank_le_one
    {program : Functions.Program}
    (check : CheckResult program) :
    maxRank check.roots ≤ 1 :=
  SelfGuardedOnce.maxRank_le_one_of_all_roots_le_one
    (fun _root hRoot => programShape_root_rank_le_one check.shape hRoot)

theorem CheckResult.edges_empty_or_pair
    {program : Functions.Program}
    (check : CheckResult program) :
    check.edges = [] ∨
      check.edges =
        [{ src := node check.leftName 1
           dst := node check.rightName 0 },
         { src := node check.rightName 1
           dst := node check.leftName 0 }] := by
  have hMax := check.maxRank_le_one
  rw [check.edges_eq]
  cases hRank : maxRank check.roots with
  | zero =>
      left
      simp [edgesUpTo]
  | succ rank =>
      cases rank with
      | zero =>
          right
          simp [edgesUpTo, node]
      | succ rank =>
          have hTooLarge : 2 ≤ maxRank check.roots := by
            rw [hRank]
            omega
          omega

def CheckResult.toStackBudget
    {program : Functions.Program}
    (check : CheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.StackBudget :=
  check.depthCheck.toStackBudget

def CheckResult.toStackResourceCheckResult
    {program : Functions.Program}
    (check : CheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceCheckResult
      program where
  budget := check.toStackBudget
  baseSafe :=
    _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafeFromBase_of_budget
      program check.toStackBudget
  safe :=
    _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafe_of_budget
      program check.toStackBudget

theorem CheckResult.stackResourceSafe
    {program : Functions.Program}
    (check : CheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceSafe program
      check.toStackBudget :=
  check.toStackResourceCheckResult.safe

end MutualGuardedOnce

namespace GuardedZeroCalls

abbrev zero : Word :=
  SelfGuardedOnce.zero

abbrev node (name : Name) (rank : Nat) : Node :=
  SelfGuardedOnce.node name rank

abbrev maxRank (roots : List Node) : Nat :=
  SelfGuardedOnce.maxRank roots

mutual
  def zeroCallFromStmt? : Stmt → Option Name
    | .call [] callee [arg] =>
        if SelfGuardedOnce.litValue? arg == some zero then
          some callee
        else
          none
    | .block body =>
        zeroCallFromBlock? body
    | _ => none

  def zeroCallFromBlock? : Block → Option Name
    | ⟨stmts⟩ => zeroCallFromStmts? stmts

  def zeroCallFromStmts? : List Stmt → Option Name
    | [stmt] => zeroCallFromStmt? stmt
    | _ => none
end

mutual
  def guardedZeroCallFromStmt? (counter : Name) : Stmt → Option Name
    | .if_ cond body =>
        if SelfGuardedOnce.varName? cond == some counter then
          zeroCallFromBlock? body
        else
          none
    | .block body =>
        guardedZeroCallFromBlock? counter body
    | _ => none

  def guardedZeroCallFromBlock? (counter : Name) : Block → Option Name
    | ⟨stmts⟩ => guardedZeroCallFromStmts? counter stmts

  def guardedZeroCallFromStmts? (counter : Name) :
      List Stmt → Option Name
    | [stmt] => guardedZeroCallFromStmt? counter stmt
    | _ => none
end

def functionShape? (fn : FunDef) : Option (Name × Name) :=
  match fn.params, fn.returns with
  | [counter], [] => do
      let callee ← guardedZeroCallFromBlock? counter fn.body
      some (fn.name, callee)
  | _, _ => none

mutual
theorem zeroCallFromStmt?_mem_internalCalls :
    ∀ {stmt : Stmt} {callee : Name},
      zeroCallFromStmt? stmt = some callee →
        callee ∈ stmtInternalCalls stmt
  | .call targets callName args, callee, hCall => by
      cases targets with
      | nil =>
          cases args with
          | nil =>
              simp [zeroCallFromStmt?] at hCall
          | cons arg rest =>
              cases rest with
              | nil =>
                  by_cases hZero :
                      SelfGuardedOnce.litValue? arg == some zero
                  · simp [zeroCallFromStmt?, hZero] at hCall
                    cases hCall
                    simp [stmtInternalCalls]
                  · simp [zeroCallFromStmt?, hZero] at hCall
              | cons _arg2 _rest2 =>
                  simp [zeroCallFromStmt?] at hCall
      | cons _target _restTargets =>
          cases args <;> simp [zeroCallFromStmt?] at hCall
  | .expr _, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall
  | .let_ _ _, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall
  | .assign _ _, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall
  | .block body, callee, hCall => by
      unfold zeroCallFromStmt? at hCall
      exact by
        simpa [stmtInternalCalls] using
          zeroCallFromBlock?_mem_internalCalls hCall
  | .if_ _ _, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall
  | .switch _ _ _, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall
  | .for_ _ _ _ _, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall
  | .brk, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall
  | .cont, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall
  | .leave, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall
  | .terminal _, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall
  | .terminalArgs _ _, _callee, hCall => by
      simp [zeroCallFromStmt?] at hCall

theorem zeroCallFromBlock?_mem_internalCalls :
    ∀ {body : Block} {callee : Name},
      zeroCallFromBlock? body = some callee →
        callee ∈ blockInternalCalls body
  | ⟨stmts⟩, callee, hCall => by
      unfold zeroCallFromBlock? at hCall
      exact by
        simpa [blockInternalCalls] using
          zeroCallFromStmts?_mem_internalCalls hCall

theorem zeroCallFromStmts?_mem_internalCalls :
    ∀ {stmts : List Stmt} {callee : Name},
      zeroCallFromStmts? stmts = some callee →
        callee ∈ stmtListInternalCalls stmts
  | [], _callee, hCall => by
      simp [zeroCallFromStmts?] at hCall
  | stmt :: rest, callee, hCall => by
      cases rest with
      | nil =>
          unfold zeroCallFromStmts? at hCall
          exact by
            simpa [stmtListInternalCalls] using
              zeroCallFromStmt?_mem_internalCalls hCall
      | cons _stmt2 _rest2 =>
          simp [zeroCallFromStmts?] at hCall
end

mutual
theorem guardedZeroCallFromStmt?_mem_internalCalls
    {counter : Name} :
    ∀ {stmt : Stmt} {callee : Name},
      guardedZeroCallFromStmt? counter stmt = some callee →
        callee ∈ stmtInternalCalls stmt
  | .if_ cond body, callee, hCall => by
      unfold guardedZeroCallFromStmt? at hCall
      by_cases hCond : SelfGuardedOnce.varName? cond == some counter
      · simp [hCond] at hCall
        exact by
          simpa [stmtInternalCalls] using
            zeroCallFromBlock?_mem_internalCalls hCall
      · simp [hCond] at hCall
  | .block body, callee, hCall => by
      unfold guardedZeroCallFromStmt? at hCall
      exact by
        simpa [stmtInternalCalls] using
          guardedZeroCallFromBlock?_mem_internalCalls hCall
  | .call _ _ _, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall
  | .expr _, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall
  | .let_ _ _, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall
  | .assign _ _, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall
  | .switch _ _ _, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall
  | .for_ _ _ _ _, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall
  | .brk, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall
  | .cont, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall
  | .leave, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall
  | .terminal _, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall
  | .terminalArgs _ _, _callee, hCall => by
      simp [guardedZeroCallFromStmt?] at hCall

theorem guardedZeroCallFromBlock?_mem_internalCalls
    {counter : Name} :
    ∀ {body : Block} {callee : Name},
      guardedZeroCallFromBlock? counter body = some callee →
        callee ∈ blockInternalCalls body
  | ⟨stmts⟩, callee, hCall => by
      unfold guardedZeroCallFromBlock? at hCall
      exact by
        simpa [blockInternalCalls] using
          guardedZeroCallFromStmts?_mem_internalCalls hCall

theorem guardedZeroCallFromStmts?_mem_internalCalls
    {counter : Name} :
    ∀ {stmts : List Stmt} {callee : Name},
      guardedZeroCallFromStmts? counter stmts = some callee →
        callee ∈ stmtListInternalCalls stmts
  | [], _callee, hCall => by
      simp [guardedZeroCallFromStmts?] at hCall
  | stmt :: rest, callee, hCall => by
      cases rest with
      | nil =>
          unfold guardedZeroCallFromStmts? at hCall
          exact by
            simpa [stmtListInternalCalls] using
              guardedZeroCallFromStmt?_mem_internalCalls hCall
      | cons _stmt2 _rest2 =>
          simp [guardedZeroCallFromStmts?] at hCall
end

theorem functionShape?_eq_some_facts
    {fn : FunDef} {name callee : Name}
    (hShape : functionShape? fn = some (name, callee)) :
    name = fn.name ∧ fn.returns = [] ∧
      callee ∈ FunDef.internalCalls fn := by
  cases fn with
  | mk fnName params returns body =>
      unfold functionShape? at hShape
      cases params with
      | nil =>
          cases returns <;> simp at hShape
      | cons counter rest =>
          cases rest with
          | nil =>
              cases returns with
              | nil =>
                  simp at hShape
                  cases hGuard :
                      guardedZeroCallFromBlock? counter body with
                  | none =>
                      simp [hGuard] at hShape
                  | some bodyCallee =>
                      simp [hGuard] at hShape
                      rcases hShape with ⟨rfl, rfl⟩
                      exact
                        ⟨rfl, rfl,
                          by
                            simpa [FunDef.internalCalls] using
                              guardedZeroCallFromBlock?_mem_internalCalls
                                hGuard⟩
              | cons _ret _rets =>
                  simp at hShape
          | cons _param _params =>
              cases returns <;> simp at hShape

theorem functionShape?_eq_some_shape
    {fn : FunDef} {name callee : Name}
    (hShape : functionShape? fn = some (name, callee)) :
    ∃ counter,
      name = fn.name ∧ fn.params = [counter] ∧ fn.returns = [] ∧
        guardedZeroCallFromBlock? counter fn.body = some callee := by
  cases fn with
  | mk fnName params returns body =>
      unfold functionShape? at hShape
      cases params with
      | nil =>
          cases returns <;> simp at hShape
      | cons counter rest =>
          cases rest with
          | nil =>
              cases returns with
              | nil =>
                  simp at hShape
                  cases hGuard :
                      guardedZeroCallFromBlock? counter body with
                  | none =>
                      simp [hGuard] at hShape
                  | some bodyCallee =>
                      simp [hGuard] at hShape
                      rcases hShape with ⟨rfl, rfl⟩
                      exact ⟨counter, rfl, rfl, rfl, hGuard⟩
              | cons _ret _rets =>
                  simp at hShape
          | cons _param _params =>
              cases returns <;> simp at hShape

def functionShapes? : List FunDef → Option (List (Name × Name))
  | [] => some []
  | fn :: rest => do
      let shape ← functionShape? fn
      let shapes ← functionShapes? rest
      some (shape :: shapes)

theorem functionShapes?_mem_facts :
    ∀ {functions : List FunDef} {shapes : List (Name × Name)}
      {shape : Name × Name},
      functionShapes? functions = some shapes →
        shape ∈ shapes →
          ∃ fn,
            fn ∈ functions ∧ functionShape? fn = some shape ∧
              shape.2 ∈ FunDef.internalCalls fn
  | [], shapes, shape, hShapes, hMem => by
      simp [functionShapes?] at hShapes
      cases hShapes
      simp at hMem
  | fn :: rest, shapes, shape, hShapes, hMem => by
      unfold functionShapes? at hShapes
      cases hHead : functionShape? fn with
      | none =>
          simp [hHead] at hShapes
      | some headShape =>
          simp [hHead] at hShapes
          cases hTail : functionShapes? rest with
          | none =>
              simp [hTail] at hShapes
          | some tailShapes =>
              simp [hTail] at hShapes
              cases hShapes
              simp at hMem
              rcases hMem with hEq | hRest
              · subst shape
                exact
                  ⟨fn, by simp, hHead,
                    (functionShape?_eq_some_facts hHead).2.2⟩
              · rcases functionShapes?_mem_facts hTail hRest with
                  ⟨fn', hFnMem, hFnShape, hCall⟩
                exact
                  ⟨fn', by simp [hFnMem], hFnShape, hCall⟩

theorem functionShapes?_mem_of_find_shape :
    ∀ {functions : List FunDef} {shapes : List (Name × Name)}
      {caller callee : Name} {fn : FunDef},
      functionShapes? functions = some shapes →
        FunList.find? caller functions = some fn →
          functionShape? fn = some (caller, callee) →
            (caller, callee) ∈ shapes
  | [], _shapes, _caller, _callee, _fn, hShapes, hFind, _hShape => by
      simp [functionShapes?, FunList.find?] at hShapes hFind
  | head :: rest, shapes, caller, callee, fn, hShapes, hFind,
      hShape => by
      unfold functionShapes? at hShapes
      cases hHead : functionShape? head with
      | none =>
          simp [hHead] at hShapes
      | some headShape =>
          simp [hHead] at hShapes
          cases hTail : functionShapes? rest with
          | none =>
              simp [hTail] at hShapes
          | some tailShapes =>
              simp [hTail] at hShapes
              cases hShapes
              by_cases hName : head.name = caller
              · simp [FunList.find?, hName] at hFind
                cases hFind
                rw [hHead] at hShape
                cases hShape
                simp
              · simp [FunList.find?, hName] at hFind
                have hTailMem :=
                  functionShapes?_mem_of_find_shape hTail hFind hShape
                simp [hTailMem]

def shapeNames (shapes : List (Name × Name)) : List Name :=
  shapes.map (fun shape => shape.1)

def calleesInShapeNames? (shapes : List (Name × Name)) : Bool :=
  shapes.all (fun shape => decide (shape.2 ∈ shapeNames shapes))

theorem calleesInShapeNames?_sound
    {shapes : List (Name × Name)}
    (hCheck : calleesInShapeNames? shapes = true)
    {shape : Name × Name} (hShape : shape ∈ shapes) :
    shape.2 ∈ shapeNames shapes := by
  unfold calleesInShapeNames? at hCheck
  have hShapeCheck :=
    list_all_eq_true_of_mem
      (fun shape => decide (shape.2 ∈ shapeNames shapes))
      hCheck hShape
  exact of_decide_eq_true hShapeCheck

def rootFromCall? (names : List Name) (callee : Name) :
    List (Expr 1) → Option Node
  | [arg] =>
      match SelfGuardedOnce.litValue? arg with
      | none => none
      | some rank =>
          if callee ∈ names then
            some (node callee (if rank == zero then 0 else 1))
          else
            none
  | _ => none

mutual
  def rootsFromStmt? (names : List Name) : Stmt → Option (List Node)
    | .call [] callee args => do
        let root ← rootFromCall? names callee args
        some [root]
    | .block body =>
        rootsFromBlock? names body
    | .if_ _ body =>
        rootsFromBlock? names body
    | _ => none

  def rootsFromBlock? (names : List Name) : Block → Option (List Node)
    | ⟨stmts⟩ => rootsFromStmts? names stmts

  def rootsFromStmts? (names : List Name) : List Stmt → Option (List Node)
    | [] => some []
    | stmt :: rest => do
        let roots ← rootsFromStmt? names stmt
        let restRoots ← rootsFromStmts? names rest
        some (roots ++ restRoots)
end

def edgeForShape (shape : Name × Name) : Edge :=
  { src := node shape.1 1, dst := node shape.2 0 }

def edgesForShapes (shapes : List (Name × Name)) : List Edge :=
  shapes.map edgeForShape

theorem edgeForShape_successor :
    ∀ {shapes : List (Name × Name)} {shape : Name × Name},
      shape ∈ shapes →
        node shape.2 0 ∈
          Edge.successors (edgesForShapes shapes) (node shape.1 1)
  | shapes, shape, hShape => by
      have hEdge :
          edgeForShape shape ∈ edgesForShapes shapes := by
        simpa [edgesForShapes] using List.mem_map_of_mem hShape
      have hSucc :=
        Edge.dst_mem_successors_of_mem
          (edges := edgesForShapes shapes)
          (edge := edgeForShape shape)
          (node := node shape.1 1)
          hEdge rfl
      simpa [edgeForShape] using hSucc

structure AbstractFrame where
  functionName : Name
  rank : Nat
  deriving DecidableEq, Repr

namespace AbstractFrame

def toNode (frame : AbstractFrame) : Node :=
  node frame.functionName frame.rank

end AbstractFrame

def AbstractMatches (node : Node) (frame : AbstractFrame) : Prop :=
  node = frame.toNode

def AbstractRootFrame (roots : List Node) (frame : AbstractFrame) : Prop :=
  frame.toNode ∈ roots

def AbstractDirectCall (shapes : List (Name × Name))
    (frame next : AbstractFrame) : Prop :=
  frame.rank = 1 ∧ next.rank = 0 ∧
    (frame.functionName, next.functionName) ∈ shapes

structure SourceCallFrame where
  functionName : Name
  args : List Word
  deriving DecidableEq, Repr

namespace SourceCallFrame

def rank? (frame : SourceCallFrame) : Option Nat :=
  match frame.args with
  | [arg] => some (if arg == zero then 0 else 1)
  | _ => none

def toNode? (frame : SourceCallFrame) : Option Node := do
  let rank ← frame.rank?
  some (node frame.functionName rank)

theorem toNode?_eq_one_of_singleton_nonzero
    {frame : SourceCallFrame} {arg : Word}
    (hArgs : frame.args = [arg])
    (hArgNonzero : (arg == zero) = false) :
    frame.toNode? = some (node frame.functionName 1) := by
  cases frame with
  | mk functionName args =>
      simp at hArgs
      subst args
      simp [toNode?, rank?, hArgNonzero]

theorem toNode?_eq_zero_of_singleton_zero
    {frame : SourceCallFrame}
    (hArgs : frame.args = [zero]) :
    frame.toNode? = some (node frame.functionName 0) := by
  cases frame with
  | mk functionName args =>
      simp at hArgs
      subst args
      have hZero : (zero == zero) = true := by native_decide
      simp [toNode?, rank?, hZero]

end SourceCallFrame

def SourceMatches (node : Node) (frame : SourceCallFrame) : Prop :=
  frame.toNode? = some node

theorem SourceMatches.functionName_eq
    {node : Node} {frame : SourceCallFrame}
    (hMatch : SourceMatches node frame) :
    node.functionName = frame.functionName := by
  unfold SourceMatches SourceCallFrame.toNode? at hMatch
  cases hRank : frame.rank? with
  | none =>
      simp [hRank] at hMatch
  | some rank =>
      simp [hRank] at hMatch
      cases hMatch
      simp [node, SelfGuardedOnce.node]

def SourceRootFrame (roots : List Node) (frame : SourceCallFrame) : Prop :=
  ∃ root, root ∈ roots ∧ SourceMatches root frame

def SourceDirectCall (shapes : List (Name × Name))
    (frame next : SourceCallFrame) : Prop :=
  ∃ arg,
    frame.args = [arg] ∧ (arg == zero) = false ∧ next.args = [zero] ∧
      (frame.functionName, next.functionName) ∈ shapes

mutual
  def GuardedSemanticRootStmt (names : List Name) :
      Stmt → SourceCallFrame → Prop
    | .call [] callee args, frame =>
        ∃ arg,
          args = [.lit arg] ∧
            callee ∈ names ∧
              frame = { functionName := callee, args := [arg] }
    | .block body, frame =>
        GuardedSemanticRootBlock names body frame
    | .if_ _ body, frame =>
        GuardedSemanticRootBlock names body frame
    | _, _ => False

  def GuardedSemanticRootBlock (names : List Name) :
      Block → SourceCallFrame → Prop
    | ⟨stmts⟩, frame =>
        GuardedSemanticRootStmts names stmts frame

  def GuardedSemanticRootStmts (names : List Name) :
      List Stmt → SourceCallFrame → Prop
    | [], _frame => False
    | stmt :: rest, frame =>
        GuardedSemanticRootStmt names stmt frame ∨
          GuardedSemanticRootStmts names rest frame
end

def GuardedSemanticRootFrame (program : Functions.Program)
    (frame : SourceCallFrame) : Prop :=
  ∃ shapes,
    functionShapes? program.functions = some shapes ∧
      (shapeNames shapes).Nodup ∧
        calleesInShapeNames? shapes = true ∧
          GuardedSemanticRootBlock (shapeNames shapes) program.body frame

def GuardedSemanticDirectCall (program : Functions.Program)
    (frame next : SourceCallFrame) : Prop :=
  ∃ arg fn callee,
    frame.args = [arg] ∧
      (arg == zero) = false ∧
      next.functionName = callee ∧
      next.args = [zero] ∧
      FunList.find? frame.functionName program.functions = some fn ∧
      functionShape? fn = some (frame.functionName, callee)

def SourceCallRunParts
    (prim : Source.PrimitiveSemantics) (program : Functions.Program)
    (_ctx : Source.Ctx) (stmtFuel : Nat)
    (targets : List Name) (functionName : Name) (args : List (Expr 1))
    (source : Source.State) (outcome : Source.Outcome) : Prop :=
  ∃ bodyFuel,
    stmtFuel = bodyFuel + 1 ∧
      ∃ stateAfterArgs argValues fn callResult,
        targets.Nodup ∧
          Source.ArgList.eval prim args source =
            .ok (stateAfterArgs, argValues) ∧
          Source.FunList.find? functionName program.functions = some fn ∧
          Source.FunDef.runBody prim program fn argValues bodyFuel
              stateAfterArgs.shared =
            .ok callResult ∧
          ((∃ sharedAfterCall returnValues returnStore,
            callResult =
                Source.CallResult.returned sharedAfterCall returnValues ∧
              Source.Store.assignMany targets returnValues
                  stateAfterArgs.vars =
                some returnStore ∧
              outcome =
                Source.Outcome.regular
                  { shared := sharedAfterCall, vars := returnStore }) ∨
            ∃ kind haltedState,
              callResult = Source.CallResult.halted kind haltedState ∧
                outcome = Source.Outcome.halt kind haltedState)

def SourceRunBodyParts
    (prim : Source.PrimitiveSemantics) (program : Functions.Program)
    (caller : Name) (fn : FunDef) (args : List Word) (fuel : Nat)
    (shared : EvmYul.SharedState .EVM)
    (result : Source.CallResult) : Prop :=
  FunList.find? caller program.functions = some fn ∧
    ∃ bodyFuel,
      fuel = bodyFuel + 1 ∧
        match result with
        | .returned sharedAfterCall returnValues =>
            ∃ paramStore bodyOutcome bodyCtx',
              Source.Store.insertMany fn.params args
                  Locals.Source.Store.empty =
                some paramStore ∧
              Source.Block.runOpen prim program (Source.FunDef.bodyCtx fn)
                  bodyFuel fn.body
                  { shared := shared,
                    vars := Source.Store.initReturns fn.returns paramStore } =
                .ok (bodyOutcome, bodyCtx') ∧
              (bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave) ∧
              Source.Store.lookupMany fn.returns bodyOutcome.state.vars =
                some returnValues ∧
              bodyOutcome.state.shared = sharedAfterCall
        | .halted kind haltedState =>
            ∃ paramStore bodyCtx',
              Source.Store.insertMany fn.params args
                  Locals.Source.Store.empty =
                some paramStore ∧
              Source.Block.runOpen prim program (Source.FunDef.bodyCtx fn)
                  bodyFuel fn.body
                  { shared := shared,
                    vars := Source.Store.initReturns fn.returns paramStore } =
                .ok (Source.Outcome.halt kind haltedState, bodyCtx')

theorem SourceDirectCall.not_from_rank_zero
    {shapes : List (Name × Name)}
    {frame next : SourceCallFrame}
    (hMatch : SourceMatches (node frame.functionName 0) frame)
    (hCall : SourceDirectCall shapes frame next) :
    False := by
  rcases hCall with ⟨arg, hArgs, hArgNonzero, _hNextArgs, _hShape⟩
  have hOne :=
    SourceCallFrame.toNode?_eq_one_of_singleton_nonzero
      (frame := frame) hArgs hArgNonzero
  unfold SourceMatches at hMatch
  rw [hOne] at hMatch
  simp [node, SelfGuardedOnce.node] at hMatch

theorem SourceDirectCall.of_shape_nonzero
    {shapes : List (Name × Name)}
    {caller callee : Name} {arg : Word}
    (hArgNonzero : (arg == zero) = false)
    (hShape : (caller, callee) ∈ shapes) :
    SourceDirectCall shapes
      { functionName := caller, args := [arg] }
      { functionName := callee, args := [zero] } :=
  ⟨arg, rfl, hArgNonzero, rfl, hShape⟩

theorem sourceRootFrame_of_rootFromCall?_mem
    {roots : List Node} {names : List Name}
    {callee : Name} {arg : Word} {root : Node}
    (hRootCall : rootFromCall? names callee [.lit arg] = some root)
    (hRootMem : root ∈ roots) :
    SourceRootFrame roots { functionName := callee, args := [arg] } := by
  unfold rootFromCall? at hRootCall
  by_cases hCallee : callee ∈ names
  · cases hArgZero : arg == zero
    · simp [SelfGuardedOnce.litValue?, hCallee, hArgZero] at hRootCall
      cases hRootCall
      refine ⟨node callee 1, hRootMem, ?_⟩
      unfold SourceMatches SourceCallFrame.toNode? SourceCallFrame.rank?
      simp [hArgZero]
    · simp [SelfGuardedOnce.litValue?, hCallee, hArgZero] at hRootCall
      cases hRootCall
      refine ⟨node callee 0, hRootMem, ?_⟩
      unfold SourceMatches SourceCallFrame.toNode? SourceCallFrame.rank?
      simp [hArgZero]
  · simp [SelfGuardedOnce.litValue?, hCallee] at hRootCall

def programShape? (program : Functions.Program) :
    Option (List (Name × Name) × List Node) := do
  let shapes ← functionShapes? program.functions
  if (shapeNames shapes).Nodup then
    if calleesInShapeNames? shapes then
      let roots ← rootsFromStmts? (shapeNames shapes) program.body.stmts
      some (shapes, roots)
    else
      none
  else
    none

theorem programShape_shape_call_facts
    {program : Functions.Program} {shapes : List (Name × Name)}
    {roots : List Node}
    (hShape : programShape? program = some (shapes, roots))
    {shape : Name × Name} (hShapeMem : shape ∈ shapes) :
    ∃ fn,
      fn ∈ program.functions ∧ functionShape? fn = some shape ∧
        shape.2 ∈ FunDef.internalCalls fn := by
  unfold programShape? at hShape
  cases hShapes : functionShapes? program.functions with
  | none =>
      simp [hShapes] at hShape
  | some checkedShapes =>
      simp [hShapes] at hShape
      by_cases hNodup : (shapeNames checkedShapes).Nodup
      · simp [hNodup] at hShape
        cases hCallees : calleesInShapeNames? checkedShapes with
        | false =>
            simp [hCallees] at hShape
        | true =>
            simp [hCallees] at hShape
            cases hRoots :
                rootsFromStmts? (shapeNames checkedShapes)
                  program.body.stmts with
            | none =>
                simp [hRoots] at hShape
            | some checkedRoots =>
                simp [hRoots] at hShape
                rcases hShape with ⟨rfl, rfl⟩
                exact functionShapes?_mem_facts hShapes hShapeMem
      · simp [hNodup] at hShape

/--
Executable checker for any finite set of one-step guarded zero-call functions.

Every accepted function has exactly one parameter, no returns, and body
`if counter { callee(0) }`, where `callee` is another accepted function name
or the same name. Main may call any accepted function with a literal argument.
Zero roots receive rank zero, nonzero roots receive rank one, and every guarded
body contributes only a rank-one-to-rank-zero edge. That is enough to accept
finite self, mutual, and larger recursive cycles without trusting a caller
supplied proof.
-/
structure CheckResult (program : Functions.Program) : Type where
  shapes : List (Name × Name)
  roots : List Node
  edges : List Edge
  shape : programShape? program = some (shapes, roots)
  edges_eq : edges = edgesForShapes shapes
  depthCheck : Program.RankedDepthCheckResult edges roots

def checkResult? (program : Functions.Program) :
    Option (CheckResult program) :=
  match hShape : programShape? program with
  | none => none
  | some (shapes, roots) =>
      let edges := edgesForShapes shapes
      match Program.rankedDepthCheck? edges roots with
      | none => none
      | some depthCheck =>
          some
            { shapes := shapes
              roots := roots
              edges := edges
              shape := hShape
              edges_eq := rfl
              depthCheck := depthCheck }

theorem checkResult?_eq_some
    {program : Functions.Program}
    {check : CheckResult program}
    (_hCheck : checkResult? program = some check) :
    programShape? program = some (check.shapes, check.roots) ∧
      check.edges = edgesForShapes check.shapes ∧
      Program.rankedMaxRootDepth? check.edges check.roots =
        some check.depthCheck.depth ∧
      16 + 17 * check.depthCheck.depth + 17 ≤ 1024 :=
  ⟨check.shape, check.edges_eq, check.depthCheck.checked,
    check.depthCheck.budget⟩

def checkedDepth? (program : Functions.Program) : Option Nat :=
  match programShape? program with
  | none => none
  | some (shapes, roots) =>
      Program.rankedDepth? (edgesForShapes shapes) roots

theorem checkedDepth?_sound
    {program : Functions.Program} {depth : Nat}
    (hDepth : checkedDepth? program = some depth) :
    ∃ check : CheckResult program,
      check.depthCheck.depth = depth := by
  unfold checkedDepth? at hDepth
  cases hShape : programShape? program with
  | none =>
      simp [hShape] at hDepth
  | some shape =>
      rcases shape with ⟨shapes, roots⟩
      simp [hShape] at hDepth
      rcases Program.rankedDepth?_sound hDepth with
        ⟨depthCheck, hDepthEq⟩
      cases hDepthEq
      let check : CheckResult program :=
        { shapes := shapes
          roots := roots
          edges := edgesForShapes shapes
          shape := hShape
          edges_eq := rfl
          depthCheck := depthCheck }
      exact ⟨check, rfl⟩

theorem rootFromCall?_eq_some_facts
    {names : List Name} {callee : Name} {args : List (Expr 1)}
    {root : Node}
    (hCallRoot : rootFromCall? names callee args = some root) :
    root.functionName ∈ names ∧ root.rank ≤ 1 ∧
      root.functionName = callee := by
  cases args with
  | nil =>
      simp [rootFromCall?] at hCallRoot
  | cons arg rest =>
      cases rest with
      | nil =>
          cases hLit : SelfGuardedOnce.litValue? arg with
          | none =>
              simp [rootFromCall?, hLit] at hCallRoot
          | some value =>
              by_cases hCallee : callee ∈ names
              · simp [rootFromCall?, hLit, hCallee] at hCallRoot
                cases hCallRoot
                constructor
                · change callee ∈ names
                  exact hCallee
                constructor
                · simp [node, SelfGuardedOnce.node]
                  split <;> omega
                · simp [node, SelfGuardedOnce.node]
              · simp [rootFromCall?, hLit, hCallee] at hCallRoot
      | cons _arg2 _rest2 =>
          simp [rootFromCall?] at hCallRoot

theorem rootFromCall?_some_of_mem
    {names : List Name} {callee : Name} {arg : Word}
    (hCallee : callee ∈ names) :
    ∃ root,
      rootFromCall? names callee [.lit arg] = some root ∧
        SourceMatches root { functionName := callee, args := [arg] } := by
  let root := node callee (if arg == zero then 0 else 1)
  refine ⟨root, ?_, ?_⟩
  · unfold rootFromCall?
    simp [SelfGuardedOnce.litValue?, hCallee, root]
  · unfold SourceMatches SourceCallFrame.toNode? SourceCallFrame.rank?
    simp [root]

mutual
theorem rootsFromStmt?_mem_facts
    {names : List Name} :
    ∀ {stmt : Stmt} {roots : List Node} {root : Node},
      rootsFromStmt? names stmt = some roots →
        root ∈ roots →
          root.functionName ∈ names ∧ root.rank ≤ 1 ∧
            root.functionName ∈ stmtInternalCalls stmt
  | stmt, roots, root, hRoots, hMem => by
      cases stmt with
      | call targets callee args =>
          cases targets with
          | nil =>
              unfold rootsFromStmt? at hRoots
              cases hCall : rootFromCall? names callee args with
              | none =>
                  simp [hCall] at hRoots
              | some callRoot =>
                  simp [hCall] at hRoots
                  cases hRoots
                  simp at hMem
                  subst root
                  rcases rootFromCall?_eq_some_facts hCall with
                    ⟨hName, hRank, hCallee⟩
                  exact
                    ⟨hName, hRank, by simp [stmtInternalCalls, hCallee]⟩
          | cons _target _restTargets =>
              cases args <;> simp [rootsFromStmt?] at hRoots
      | expr _ =>
          simp [rootsFromStmt?] at hRoots
      | let_ _ _ =>
          simp [rootsFromStmt?] at hRoots
      | assign _ _ =>
          simp [rootsFromStmt?] at hRoots
      | block body =>
          unfold rootsFromStmt? at hRoots
          rcases rootsFromBlock?_mem_facts hRoots hMem with
            ⟨hName, hRank, hCall⟩
          exact
            ⟨hName, hRank, by simpa [stmtInternalCalls] using hCall⟩
      | if_ _ body =>
          unfold rootsFromStmt? at hRoots
          rcases rootsFromBlock?_mem_facts hRoots hMem with
            ⟨hName, hRank, hCall⟩
          exact
            ⟨hName, hRank, by simpa [stmtInternalCalls] using hCall⟩
      | switch _ _ _ =>
          simp [rootsFromStmt?] at hRoots
      | for_ _ _ _ _ =>
          simp [rootsFromStmt?] at hRoots
      | brk =>
          simp [rootsFromStmt?] at hRoots
      | cont =>
          simp [rootsFromStmt?] at hRoots
      | leave =>
          simp [rootsFromStmt?] at hRoots
      | terminal _ =>
          simp [rootsFromStmt?] at hRoots
      | terminalArgs _ _ =>
          simp [rootsFromStmt?] at hRoots

theorem rootsFromBlock?_mem_facts
    {names : List Name} :
    ∀ {body : Block} {roots : List Node} {root : Node},
      rootsFromBlock? names body = some roots →
        root ∈ roots →
          root.functionName ∈ names ∧ root.rank ≤ 1 ∧
            root.functionName ∈ blockInternalCalls body
  | ⟨stmts⟩, roots, root, hRoots, hMem => by
      unfold rootsFromBlock? at hRoots
      rcases rootsFromStmts?_mem_facts hRoots hMem with
        ⟨hName, hRank, hCall⟩
      exact
        ⟨hName, hRank, by simpa [blockInternalCalls] using hCall⟩

theorem rootsFromStmts?_mem_facts
    {names : List Name} :
    ∀ {stmts : List Stmt} {roots : List Node} {root : Node},
      rootsFromStmts? names stmts = some roots →
        root ∈ roots →
          root.functionName ∈ names ∧ root.rank ≤ 1 ∧
            root.functionName ∈ stmtListInternalCalls stmts
  | [], roots, root, hRoots, hMem => by
      simp [rootsFromStmts?] at hRoots
      cases hRoots
      simp at hMem
  | stmt :: rest, roots, root, hRoots, hMem => by
      unfold rootsFromStmts? at hRoots
      cases hHead : rootsFromStmt? names stmt with
      | none =>
          simp [hHead] at hRoots
      | some stmtRoots =>
          simp [hHead] at hRoots
          cases hTail : rootsFromStmts? names rest with
          | none =>
              simp [hTail] at hRoots
          | some restRoots =>
              simp [hTail] at hRoots
              cases hRoots
              simp at hMem
              rcases hMem with hStmt | hRest
              · rcases rootsFromStmt?_mem_facts hHead hStmt with
                  ⟨hName, hRank, hCall⟩
                exact
                  ⟨hName, hRank,
                    by simp [stmtListInternalCalls, hCall]⟩
              · rcases rootsFromStmts?_mem_facts hTail hRest with
                  ⟨hName, hRank, hCall⟩
                exact
                  ⟨hName, hRank,
                    by simp [stmtListInternalCalls, hCall]⟩
end

mutual
theorem rootsFromStmt?_covers_guardedSemanticRoot
    {names : List Name} :
    ∀ {stmt : Stmt} {roots : List Node} {frame : SourceCallFrame},
      rootsFromStmt? names stmt = some roots →
        GuardedSemanticRootStmt names stmt frame →
          SourceRootFrame roots frame
  | stmt, roots, frame, hRoots, hSemantic => by
      cases stmt with
      | call targets callee args =>
          cases targets with
          | nil =>
              rcases hSemantic with
                ⟨arg, hArgs, hCallee, hFrame⟩
              subst args
              subst frame
              unfold rootsFromStmt? at hRoots
              rcases rootFromCall?_some_of_mem
                  (names := names) (callee := callee)
                  (arg := arg) hCallee with
                ⟨root, hRootCall, hMatch⟩
              simp [hRootCall] at hRoots
              cases hRoots
              exact ⟨root, by simp, hMatch⟩
          | cons _target _restTargets =>
              simp [GuardedSemanticRootStmt] at hSemantic
      | expr _ =>
          simp [GuardedSemanticRootStmt] at hSemantic
      | let_ _ _ =>
          simp [GuardedSemanticRootStmt] at hSemantic
      | assign _ _ =>
          simp [GuardedSemanticRootStmt] at hSemantic
      | block body =>
          have hBlock :
              GuardedSemanticRootBlock names body frame := by
            simpa [GuardedSemanticRootStmt] using hSemantic
          exact
            rootsFromBlock?_covers_guardedSemanticRoot hRoots hBlock
      | if_ _ body =>
          have hBlock :
              GuardedSemanticRootBlock names body frame := by
            simpa [GuardedSemanticRootStmt] using hSemantic
          exact
            rootsFromBlock?_covers_guardedSemanticRoot hRoots hBlock
      | switch _ _ _ =>
          simp [GuardedSemanticRootStmt] at hSemantic
      | for_ _ _ _ _ =>
          simp [GuardedSemanticRootStmt] at hSemantic
      | brk =>
          simp [GuardedSemanticRootStmt] at hSemantic
      | cont =>
          simp [GuardedSemanticRootStmt] at hSemantic
      | leave =>
          simp [GuardedSemanticRootStmt] at hSemantic
      | terminal _ =>
          simp [GuardedSemanticRootStmt] at hSemantic
      | terminalArgs _ _ =>
          simp [GuardedSemanticRootStmt] at hSemantic

theorem rootsFromBlock?_covers_guardedSemanticRoot
    {names : List Name} :
    ∀ {body : Block} {roots : List Node} {frame : SourceCallFrame},
      rootsFromBlock? names body = some roots →
        GuardedSemanticRootBlock names body frame →
          SourceRootFrame roots frame
  | ⟨stmts⟩, roots, frame, hRoots, hSemantic => by
      exact
        rootsFromStmts?_covers_guardedSemanticRoot hRoots hSemantic

theorem rootsFromStmts?_covers_guardedSemanticRoot
    {names : List Name} :
    ∀ {stmts : List Stmt} {roots : List Node} {frame : SourceCallFrame},
      rootsFromStmts? names stmts = some roots →
        GuardedSemanticRootStmts names stmts frame →
          SourceRootFrame roots frame
  | [], roots, frame, hRoots, hSemantic => by
      simp [GuardedSemanticRootStmts] at hSemantic
  | stmt :: rest, roots, frame, hRoots, hSemantic => by
      unfold rootsFromStmts? at hRoots
      cases hHead : rootsFromStmt? names stmt with
      | none =>
          simp [hHead] at hRoots
      | some stmtRoots =>
          simp [hHead] at hRoots
          cases hTail : rootsFromStmts? names rest with
          | none =>
              simp [hTail] at hRoots
          | some restRoots =>
              simp [hTail] at hRoots
              cases hRoots
              rcases hSemantic with hStmt | hRest
              · rcases
                  rootsFromStmt?_covers_guardedSemanticRoot hHead hStmt with
                    ⟨root, hRootMem, hMatch⟩
                exact ⟨root, by simp [hRootMem], hMatch⟩
              · rcases
                  rootsFromStmts?_covers_guardedSemanticRoot hTail hRest with
                    ⟨root, hRootMem, hMatch⟩
                exact ⟨root, by simp [hRootMem], hMatch⟩
end

theorem programShape_root_mem_facts
    {program : Functions.Program} {shapes : List (Name × Name)}
    {roots : List Node}
    (hShape : programShape? program = some (shapes, roots))
    {root : Node} (hRoot : root ∈ roots) :
    root.functionName ∈ shapeNames shapes ∧ root.rank ≤ 1 ∧
      root.functionName ∈ stmtListInternalCalls program.body.stmts := by
  unfold programShape? at hShape
  cases hShapes : functionShapes? program.functions with
  | none =>
      simp [hShapes] at hShape
  | some checkedShapes =>
      simp [hShapes] at hShape
      by_cases hNodup : (shapeNames checkedShapes).Nodup
      · simp [hNodup] at hShape
        cases hCallees : calleesInShapeNames? checkedShapes with
        | false =>
            simp [hCallees] at hShape
        | true =>
            simp [hCallees] at hShape
            cases hRoots :
                rootsFromStmts? (shapeNames checkedShapes)
                  program.body.stmts with
            | none =>
                simp [hRoots] at hShape
            | some checkedRoots =>
                simp [hRoots] at hShape
                rcases hShape with ⟨rfl, rfl⟩
                exact rootsFromStmts?_mem_facts hRoots hRoot
      · simp [hNodup] at hShape

theorem programShape_shape_facts
    {program : Functions.Program} {shapes : List (Name × Name)}
    {roots : List Node}
    (hShape : programShape? program = some (shapes, roots)) :
    (shapeNames shapes).Nodup ∧
      ∀ shape, shape ∈ shapes → shape.2 ∈ shapeNames shapes := by
  unfold programShape? at hShape
  cases hShapes : functionShapes? program.functions with
  | none =>
      simp [hShapes] at hShape
  | some checkedShapes =>
      simp [hShapes] at hShape
      by_cases hNodup : (shapeNames checkedShapes).Nodup
      · simp [hNodup] at hShape
        cases hCallees : calleesInShapeNames? checkedShapes with
        | false =>
            simp [hCallees] at hShape
        | true =>
            simp [hCallees] at hShape
            cases hRoots :
                rootsFromStmts? (shapeNames checkedShapes)
                  program.body.stmts with
            | none =>
                simp [hRoots] at hShape
            | some checkedRoots =>
                simp [hRoots] at hShape
                rcases hShape with ⟨rfl, rfl⟩
                exact
                  ⟨hNodup,
                    fun shape hShapeMem =>
                      calleesInShapeNames?_sound hCallees hShapeMem⟩
      · simp [hNodup] at hShape

theorem CheckResult.shapeNames_nodup
    {program : Functions.Program}
    (check : CheckResult program) :
    (shapeNames check.shapes).Nodup :=
  (programShape_shape_facts check.shape).1

theorem CheckResult.callee_mem_shapeNames
    {program : Functions.Program}
    (check : CheckResult program)
    {shape : Name × Name} (hShape : shape ∈ check.shapes) :
    shape.2 ∈ shapeNames check.shapes :=
  (programShape_shape_facts check.shape).2 shape hShape

theorem CheckResult.shape_call_facts
    {program : Functions.Program}
    (check : CheckResult program)
    {shape : Name × Name} (hShape : shape ∈ check.shapes) :
    ∃ fn,
      fn ∈ program.functions ∧ functionShape? fn = some shape ∧
        shape.2 ∈ FunDef.internalCalls fn :=
  programShape_shape_call_facts check.shape hShape

theorem CheckResult.shape_body_facts
    {program : Functions.Program}
    (check : CheckResult program)
    {shape : Name × Name} (hShape : shape ∈ check.shapes) :
    ∃ fn counter,
      fn ∈ program.functions ∧ functionShape? fn = some shape ∧
        shape.1 = fn.name ∧ fn.params = [counter] ∧ fn.returns = [] ∧
          guardedZeroCallFromBlock? counter fn.body = some shape.2 := by
  rcases check.shape_call_facts hShape with
    ⟨fn, hFnMem, hFnShape, _hCall⟩
  rcases functionShape?_eq_some_shape hFnShape with
    ⟨counter, hName, hParams, hReturns, hBody⟩
  exact
    ⟨fn, counter, hFnMem, hFnShape, hName, hParams, hReturns,
      hBody⟩

theorem CheckResult.root_mem_facts
    {program : Functions.Program}
    (check : CheckResult program)
    {root : Node} (hRoot : root ∈ check.roots) :
    root.functionName ∈ shapeNames check.shapes ∧ root.rank ≤ 1 ∧
      root.functionName ∈
        _root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls
          program :=
  by
    rcases programShape_root_mem_facts check.shape hRoot with
      ⟨hName, hRank, hCall⟩
    refine ⟨hName, hRank, ?_⟩
    cases hBody : program.body with
    | mk stmts =>
        rw [hBody] at hCall
        simpa
          [_root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls,
            blockInternalCalls, hBody]
          using hCall

theorem CheckResult.sourceRootFrame_of_rootFromCall?
    {program : Functions.Program}
    (check : CheckResult program)
    {callee : Name} {arg : Word} {root : Node}
    (hRootCall :
      rootFromCall? (shapeNames check.shapes) callee [.lit arg] =
        some root)
    (hRootMem : root ∈ check.roots) :
    SourceRootFrame check.roots { functionName := callee, args := [arg] } :=
  sourceRootFrame_of_rootFromCall?_mem hRootCall hRootMem

theorem CheckResult.sourceRootFrame_of_call_run_rootFromCall?_parts
    {program : Functions.Program}
    (check : CheckResult program)
    {prim : Source.PrimitiveSemantics} {ctx : Source.Ctx} {fuel : Nat}
    {callee : Name} {arg : Word} {root : Node}
    {source : Source.State} {outcome : Source.Outcome}
    (hRun :
      Source.Stmt.run prim program ctx fuel
          (.call [] callee [.lit arg]) source =
        .ok (outcome, ctx))
    (hRootCall :
      rootFromCall? (shapeNames check.shapes) callee [.lit arg] =
        some root)
    (hRootMem : root ∈ check.roots) :
    SourceRootFrame check.roots { functionName := callee, args := [arg] } ∧
      SourceCallRunParts prim program ctx fuel [] callee [.lit arg] source
        outcome := by
  refine ⟨check.sourceRootFrame_of_rootFromCall? hRootCall hRootMem, ?_⟩
  unfold SourceCallRunParts
  cases fuel with
  | zero =>
      simp [Source.Stmt.run, Source.invalid, Structured.invalid] at hRun
  | succ bodyFuel =>
      exact ⟨bodyFuel, rfl, Source.Stmt.call_ok_parts hRun⟩

theorem CheckResult.sourceRootFrame_of_call_run_rootFromCall?
    {program : Functions.Program}
    (check : CheckResult program)
    {prim : Source.PrimitiveSemantics} {ctx : Source.Ctx} {fuel : Nat}
    {callee : Name} {arg : Word} {root : Node}
    {source : Source.State} {outcome : Source.Outcome}
    (hRun :
      Source.Stmt.run prim program ctx fuel
          (.call [] callee [.lit arg]) source =
        .ok (outcome, ctx))
    (hRootCall :
      rootFromCall? (shapeNames check.shapes) callee [.lit arg] =
        some root)
    (hRootMem : root ∈ check.roots) :
    SourceRootFrame check.roots { functionName := callee, args := [arg] } :=
  (check.sourceRootFrame_of_call_run_rootFromCall?_parts hRun hRootCall
    hRootMem).1

theorem CheckResult.sourceRootFrame_of_guardedSemanticRootFrame
    {program : Functions.Program}
    (check : CheckResult program)
    {frame : SourceCallFrame}
    (hRoot : GuardedSemanticRootFrame program frame) :
    SourceRootFrame check.roots frame := by
  rcases hRoot with
    ⟨semanticShapes, hSemanticShapes, _hSemanticNodup,
      _hSemanticCallees, hSemanticRoot⟩
  have hCheckShape := check.shape
  unfold programShape? at hCheckShape
  cases hShapes : functionShapes? program.functions with
  | none =>
      simp [hShapes] at hCheckShape
  | some checkedShapes =>
      simp [hShapes] at hCheckShape
      rw [hShapes] at hSemanticShapes
      cases hSemanticShapes
      by_cases hNodup : (shapeNames semanticShapes).Nodup
      · simp [hNodup] at hCheckShape
        cases hCallees : calleesInShapeNames? semanticShapes with
        | false =>
            simp [hCallees] at hCheckShape
        | true =>
            simp [hCallees] at hCheckShape
            cases hRoots :
                rootsFromStmts? (shapeNames semanticShapes)
                  program.body.stmts with
            | none =>
                simp [hRoots] at hCheckShape
            | some checkedRoots =>
                simp [hRoots] at hCheckShape
                rcases hCheckShape with ⟨_hShapesEq, hRootsEq⟩
                subst checkedRoots
                cases hBody : program.body with
                | mk stmts =>
                    rw [hBody] at hRoots hSemanticRoot
                    exact
                      rootsFromBlock?_covers_guardedSemanticRoot
                        (names := shapeNames semanticShapes)
                        (body := { stmts := stmts })
                        hRoots hSemanticRoot
      · simp [hNodup] at hCheckShape

theorem CheckResult.sourceDirectCall_of_shape_nonzero
    {program : Functions.Program}
    (check : CheckResult program)
    {caller callee : Name} {arg : Word}
    (hArgNonzero : (arg == zero) = false)
    (hShape : (caller, callee) ∈ check.shapes) :
    SourceDirectCall check.shapes
      { functionName := caller, args := [arg] }
      { functionName := callee, args := [zero] } :=
  SourceDirectCall.of_shape_nonzero hArgNonzero hShape

theorem CheckResult.sourceDirectCall_of_guardedSemanticDirectCall
    {program : Functions.Program}
    (check : CheckResult program)
    {frame next : SourceCallFrame}
    (hCall : GuardedSemanticDirectCall program frame next) :
    SourceDirectCall check.shapes frame next := by
  rcases hCall with
    ⟨arg, fn, callee, hArgs, hArgNonzero, hNextName, hNextArgs,
      hFind, hFnShape⟩
  have hShapeMem :
      (frame.functionName, callee) ∈ check.shapes := by
    have hCheckShape := check.shape
    unfold programShape? at hCheckShape
    cases hShapes : functionShapes? program.functions with
    | none =>
        simp [hShapes] at hCheckShape
    | some checkedShapes =>
        simp [hShapes] at hCheckShape
        by_cases hNodup : (shapeNames checkedShapes).Nodup
        · simp [hNodup] at hCheckShape
          cases hCallees : calleesInShapeNames? checkedShapes with
          | false =>
              simp [hCallees] at hCheckShape
          | true =>
              simp [hCallees] at hCheckShape
              cases hRoots :
                  rootsFromStmts? (shapeNames checkedShapes)
                    program.body.stmts with
              | none =>
                  simp [hRoots] at hCheckShape
              | some checkedRoots =>
                  simp [hRoots] at hCheckShape
                  rcases hCheckShape with ⟨rfl, _hRootsEq⟩
                  exact
                    functionShapes?_mem_of_find_shape hShapes hFind
                      hFnShape
        · simp [hNodup] at hCheckShape
  rcases frame with ⟨frameName, frameArgs⟩
  simp at hArgs
  subst frameArgs
  rcases next with ⟨nextName, nextArgs⟩
  simp at hNextName hNextArgs
  subst nextName
  subst nextArgs
  exact
    SourceDirectCall.of_shape_nonzero
      (shapes := check.shapes)
      (caller := frameName)
      (callee := callee)
      (arg := arg)
      hArgNonzero hShapeMem

theorem CheckResult.sourceDirectCall_of_runBody_nonzero_parts
    {program : Functions.Program}
    (check : CheckResult program)
    {prim : Source.PrimitiveSemantics} {caller callee : Name}
    {arg : Word} {fn : FunDef} {fuel : Nat}
    {shared : EvmYul.SharedState .EVM} {result : Source.CallResult}
    (hFind : FunList.find? caller program.functions = some fn)
    (hRun :
      Source.FunDef.runBody prim program fn [arg] fuel shared =
        .ok result)
    (hArgNonzero : (arg == zero) = false)
    (hShape : (caller, callee) ∈ check.shapes) :
    SourceDirectCall check.shapes
      { functionName := caller, args := [arg] }
      { functionName := callee, args := [zero] } ∧
      SourceRunBodyParts prim program caller fn [arg] fuel shared result := by
  refine
    ⟨check.sourceDirectCall_of_shape_nonzero hArgNonzero hShape, ?_⟩
  unfold SourceRunBodyParts
  refine ⟨hFind, ?_⟩
  cases fuel with
  | zero =>
      simp [Source.FunDef.runBody, Source.invalid, Structured.invalid] at hRun
  | succ bodyFuel =>
      refine ⟨bodyFuel, rfl, ?_⟩
      cases result with
      | returned sharedAfterCall returnValues =>
          exact Source.FunDef.runBody_returned_parts hRun
      | halted kind haltedState =>
          exact Source.FunDef.runBody_halted_parts hRun

theorem CheckResult.sourceDirectCall_of_runBody_nonzero
    {program : Functions.Program}
    (check : CheckResult program)
    {prim : Source.PrimitiveSemantics} {caller callee : Name}
    {arg : Word} {fn : FunDef} {fuel : Nat}
    {shared : EvmYul.SharedState .EVM} {result : Source.CallResult}
    (hFind : FunList.find? caller program.functions = some fn)
    (hRun :
      Source.FunDef.runBody prim program fn [arg] fuel shared =
        .ok result)
    (hArgNonzero : (arg == zero) = false)
    (hShape : (caller, callee) ∈ check.shapes) :
    SourceDirectCall check.shapes
      { functionName := caller, args := [arg] }
      { functionName := callee, args := [zero] } :=
  (check.sourceDirectCall_of_runBody_nonzero_parts hFind hRun hArgNonzero
    hShape).1

theorem CheckResult.maxRank_le_one
    {program : Functions.Program}
    (check : CheckResult program) :
    maxRank check.roots ≤ 1 :=
  SelfGuardedOnce.maxRank_le_one_of_all_roots_le_one
    (fun _root hRoot => (check.root_mem_facts hRoot).2.1)

theorem edgesForShapes_mem_rank_one_to_zero :
    ∀ {shapes : List (Name × Name)} {edge : Edge},
      edge ∈ edgesForShapes shapes →
        edge.src.rank = 1 ∧ edge.dst.rank = 0
  | [], edge, hEdge => by
      simp [edgesForShapes] at hEdge
  | shape :: rest, edge, hEdge => by
      simp [edgesForShapes] at hEdge
      rcases hEdge with hHead | hTail
      · cases hHead
        simp [edgeForShape, node, SelfGuardedOnce.node]
      · rcases hTail with ⟨srcName, dstName, hMem, hEq⟩
        have hMapped : edge ∈ edgesForShapes rest :=
          List.mem_map.mpr ⟨(srcName, dstName), hMem, hEq⟩
        exact edgesForShapes_mem_rank_one_to_zero hMapped

theorem CheckResult.edge_rank_one_to_zero
    {program : Functions.Program}
    (check : CheckResult program)
    {edge : Edge} (hEdge : edge ∈ check.edges) :
    edge.src.rank = 1 ∧ edge.dst.rank = 0 := by
  rw [check.edges_eq] at hEdge
  exact edgesForShapes_mem_rank_one_to_zero hEdge

theorem CheckResult.callGraphSound
    {program : Functions.Program}
    (check : CheckResult program) :
    CallGraphSound check.edges check.roots
      AbstractMatches
      (AbstractRootFrame check.roots)
      (AbstractDirectCall check.shapes) := by
  refine
    { root_sound := ?_
      step_sound := ?_ }
  · intro frame hRoot
    exact ⟨frame.toNode, hRoot, rfl⟩
  · intro node frame nextFrame hMatch hCall
    rcases hCall with ⟨hRank, hNextRank, hShape⟩
    cases hMatch
    refine ⟨nextFrame.toNode, ?_, rfl⟩
    rw [check.edges_eq]
    unfold AbstractFrame.toNode
    rw [hRank, hNextRank]
    exact edgeForShape_successor hShape

theorem CheckResult.abstractCallChain_frame_count_bound
    {program : Functions.Program}
    (check : CheckResult program)
    {frame : AbstractFrame} {depth : Nat}
    (hRoot : AbstractRootFrame check.roots frame)
    (hChain :
      ConcreteCallChain (AbstractDirectCall check.shapes) frame depth) :
    depth + 1 ≤ check.depthCheck.depth :=
  check.callGraphSound.chain_frame_count_bound check.depthCheck hRoot hChain

theorem CheckResult.sourceCallGraphSound
    {program : Functions.Program}
    (check : CheckResult program) :
    CallGraphSound check.edges check.roots
      SourceMatches
      (SourceRootFrame check.roots)
      (SourceDirectCall check.shapes) := by
  refine
    { root_sound := ?_
      step_sound := ?_ }
  · intro frame hRoot
    exact hRoot
  · intro current frame nextFrame hMatch hCall
    rcases hCall with
      ⟨arg, hArgs, hArgNonzero, hNextArgs, hShape⟩
    have hFrameNode :
        frame.toNode? = some (node frame.functionName 1) :=
      SourceCallFrame.toNode?_eq_one_of_singleton_nonzero
        (frame := frame) hArgs hArgNonzero
    unfold SourceMatches at hMatch
    rw [hFrameNode] at hMatch
    cases hMatch
    refine ⟨node nextFrame.functionName 0, ?_, ?_⟩
    · rw [check.edges_eq]
      exact edgeForShape_successor hShape
    · exact SourceCallFrame.toNode?_eq_zero_of_singleton_zero
        (frame := nextFrame) hNextArgs

theorem CheckResult.sourceCallChain_frame_count_bound
    {program : Functions.Program}
    (check : CheckResult program)
    {frame : SourceCallFrame} {depth : Nat}
    (hRoot : SourceRootFrame check.roots frame)
    (hChain :
      ConcreteCallChain (SourceDirectCall check.shapes) frame depth) :
    depth + 1 ≤ check.depthCheck.depth :=
  check.sourceCallGraphSound.chain_frame_count_bound check.depthCheck hRoot
    hChain

theorem CheckResult.sourceCallDepthBound
    {program : Functions.Program}
    (check : CheckResult program) :
    CallChainDepthBound
      (SourceRootFrame check.roots)
      (SourceDirectCall check.shapes)
      check.depthCheck.depth :=
  check.sourceCallGraphSound.callChainDepthBound_of_ranked check.depthCheck

theorem CheckResult.sourceCallDepthBound_of_covered
    {program : Functions.Program}
    (check : CheckResult program)
    {RootFrame : SourceCallFrame → Prop}
    {DirectCall : SourceCallFrame → SourceCallFrame → Prop}
    (hRoot :
      ∀ {frame}, RootFrame frame → SourceRootFrame check.roots frame)
    (hDirect :
      ∀ {frame next}, DirectCall frame next →
        SourceDirectCall check.shapes frame next) :
    SourceCallDepth.Bound RootFrame DirectCall check.depthCheck.depth :=
  CallChainDepthBound.mono check.sourceCallDepthBound hRoot hDirect

theorem CheckResult.sourceCallDepthBound_of_guardedSemanticDirect
    {program : Functions.Program}
    (check : CheckResult program)
    {RootFrame : SourceCallFrame → Prop}
    (hRoot :
      ∀ {frame}, RootFrame frame → SourceRootFrame check.roots frame) :
    SourceCallDepth.Bound RootFrame
      (GuardedSemanticDirectCall program) check.depthCheck.depth :=
  check.sourceCallDepthBound_of_covered hRoot
    (fun hCall => check.sourceDirectCall_of_guardedSemanticDirectCall hCall)

theorem CheckResult.sourceCallDepthBound_of_guardedSemantic
    {program : Functions.Program}
    (check : CheckResult program) :
    SourceCallDepth.Bound
      (GuardedSemanticRootFrame program)
      (GuardedSemanticDirectCall program)
      check.depthCheck.depth :=
  check.sourceCallDepthBound_of_guardedSemanticDirect
    (fun hRoot => check.sourceRootFrame_of_guardedSemanticRootFrame hRoot)

def CheckResult.toStackBudget
    {program : Functions.Program}
    (check : CheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.StackBudget :=
  check.depthCheck.toStackBudget

def CheckResult.toStackResourceCheckResult
    {program : Functions.Program}
    (check : CheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceCheckResult
      program where
  budget := check.toStackBudget
  baseSafe :=
    _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafeFromBase_of_budget
      program check.toStackBudget
  safe :=
    _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafe_of_budget
      program check.toStackBudget

theorem CheckResult.stackResourceSafe
    {program : Functions.Program}
    (check : CheckResult program) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceSafe program
      check.toStackBudget :=
  check.toStackResourceCheckResult.safe

end GuardedZeroCalls

theorem successor_mem_edgeNodes
    {edges : List Edge} {node next : Node}
    (hSucc : next ∈ Edge.successors edges node) :
    next ∈ edgeNodes edges := by
  induction edges with
  | nil =>
      simp [Edge.successors] at hSucc
  | cons edge rest ih =>
      unfold Edge.successors at hSucc
      by_cases hSrc : edge.src = node
      · simp [hSrc] at hSucc
        rcases hSucc with hHead | hTail
        · cases hHead
          simp [edgeNodes]
        · have hRest := ih hTail
          simp [edgeNodes, hRest]
      · simp [hSrc] at hSucc
        have hRest := ih hSucc
        simp [edgeNodes, hRest]

theorem pathTo_target_eq_start_or_mem_edgeNodes
    {edges : List Edge} {start target : Node} {depth : Nat}
    (hPath : PathTo edges start target depth) :
    target = start ∨ target ∈ edgeNodes edges := by
  induction hPath with
  | here =>
      exact Or.inl rfl
  | step hEdge _hTail ih =>
      rcases ih with hEq | hMem
      · subst hEq
        exact Or.inr (successor_mem_edgeNodes hEdge)
      · exact Or.inr hMem

theorem pathTo_target_mem_graphNodes
    {edges : List Edge} {roots : List Node}
    {root target : Node} {depth : Nat}
    (hRoot : root ∈ roots)
    (hPath : PathTo edges root target depth) :
    target ∈ graphNodes edges roots := by
  rcases pathTo_target_eq_start_or_mem_edgeNodes hPath with hEq | hEdgeMem
  · subst hEq
    simp [graphNodes, hRoot]
  · simp [graphNodes, hEdgeMem]

namespace ProgramConformance

def NameFrameMatches (edges : List Edge) (roots : List Node)
    (node : Node) (functionName : Name) : Prop :=
  node ∈ graphNodes edges roots ∧ node.functionName = functionName

def RootNameFrame (program : Functions.Program) (functionName : Name) :
    Prop :=
  functionName ∈
    _root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls
      program

def DirectNameCall (program : Functions.Program)
    (caller callee : Name) : Prop :=
  ∃ fn,
    FunList.find? caller program.functions = some fn ∧
      callee ∈ FunDef.internalCalls fn

theorem toCallGraphSound
    {program : Functions.Program} {edges : List Edge} {roots : List Node}
    (hConforms : ProgramConformance program edges roots) :
    CallGraphSound edges roots
      (NameFrameMatches edges roots)
      (RootNameFrame program)
      (DirectNameCall program) := by
  refine
    { root_sound := ?_
      step_sound := ?_ }
  · intro functionName hRoot
    rcases hConforms.root hRoot with ⟨root, hRootMem, hName⟩
    exact
      ⟨root, hRootMem,
        ⟨by simp [graphNodes, hRootMem], hName⟩⟩
  · intro node caller callee hMatch hCall
    rcases hMatch with ⟨hNodeMem, hNodeName⟩
    rcases hCall with ⟨fn, hFind, hInternalCall⟩
    have hFindNode :
        FunList.find? node.functionName program.functions = some fn := by
      rw [hNodeName]
      exact hFind
    rcases hConforms.call hNodeMem hFindNode hInternalCall with
      ⟨next, hSucc, hNextName⟩
    have hNextMem : next ∈ graphNodes edges roots := by
      simp [graphNodes, successor_mem_edgeNodes hSucc]
    exact ⟨next, hSucc, ⟨hNextMem, hNextName⟩⟩

end ProgramConformance

namespace CheckedProgramCheckResult

theorem callGraphSound {program : Functions.Program}
    (check : CheckedProgramCheckResult program) :
    CallGraphSound check.edges check.roots
      (ProgramConformance.NameFrameMatches check.edges check.roots)
      (ProgramConformance.RootNameFrame program)
      (ProgramConformance.DirectNameCall program) :=
  check.conformance.toCallGraphSound

theorem directNameCallChain_frame_count_bound
    {program : Functions.Program}
    (check : CheckedProgramCheckResult program)
    {functionName : Name} {depth : Nat}
    (hRoot :
      ProgramConformance.RootNameFrame program functionName)
    (hChain :
      ConcreteCallChain
        (ProgramConformance.DirectNameCall program)
        functionName depth) :
    depth + 1 ≤ check.depthCheck.depth :=
  check.callGraphSound.chain_frame_count_bound check.depthCheck hRoot hChain

theorem directNameCallDepthBound
    {program : Functions.Program}
    (check : CheckedProgramCheckResult program) :
    CallChainDepthBound
      (ProgramConformance.RootNameFrame program)
      (ProgramConformance.DirectNameCall program)
      check.depthCheck.depth :=
  check.callGraphSound.callChainDepthBound_of_ranked check.depthCheck

end CheckedProgramCheckResult

namespace CheckedProgramRecurrenceCheckResult

theorem callGraphSound {program : Functions.Program}
    (check : CheckedProgramRecurrenceCheckResult program) :
    CallGraphSound check.edges check.roots
      (ProgramConformance.NameFrameMatches check.edges check.roots)
      (ProgramConformance.RootNameFrame program)
      (ProgramConformance.DirectNameCall program) :=
  check.conformance.toCallGraphSound

theorem directNameCallDepthBound
    {program : Functions.Program}
    (check : CheckedProgramRecurrenceCheckResult program) :
    CallChainDepthBound
      (ProgramConformance.RootNameFrame program)
      (ProgramConformance.DirectNameCall program)
      check.depth :=
  check.callGraphSound.callChainDepthBound_of_graph_bound
    check.rootedGraphDepthBound

end CheckedProgramRecurrenceCheckResult

/--
Branch-free semantic source recurrence bound.

This is the theorem-facing contract for executable recurrence checking.  The
constructors still distinguish the two semantic abstractions we currently know
how to prove: ordinary function-name call chains for acyclic graphs, and
argument-sensitive guarded-zero source frames for bounded recursive cycles.
The public checker soundness theorem below exposes this predicate rather than
the recognizer-specific check result that happened to prove it.
-/
inductive SourceRecurrenceBound
    (program : Functions.Program) (maxFrames : Nat) : Prop where
  | byName
      (bound :
        CallChainDepthBound
          (ProgramConformance.RootNameFrame program)
          (ProgramConformance.DirectNameCall program)
          maxFrames) :
      SourceRecurrenceBound program maxFrames
  | guardedZero
      (bound :
        SourceCallDepth.Bound
          (GuardedZeroCalls.GuardedSemanticRootFrame program)
          (GuardedZeroCalls.GuardedSemanticDirectCall program)
          maxFrames) :
      SourceRecurrenceBound program maxFrames

namespace CheckedProgramCheckResult

theorem sourceRecurrenceBound
    {program : Functions.Program}
    (check : CheckedProgramCheckResult program) :
    SourceRecurrenceBound program check.depthCheck.depth :=
  SourceRecurrenceBound.byName check.directNameCallDepthBound

end CheckedProgramCheckResult

namespace CheckedProgramRecurrenceCheckResult

theorem sourceRecurrenceBound
    {program : Functions.Program}
    (check : CheckedProgramRecurrenceCheckResult program) :
    SourceRecurrenceBound program check.depth :=
  SourceRecurrenceBound.byName check.directNameCallDepthBound

end CheckedProgramRecurrenceCheckResult

namespace GuardedZeroCalls

theorem CheckResult.sourceRecurrenceBound
    {program : Functions.Program}
    (check : CheckResult program) :
    SourceRecurrenceBound program check.depthCheck.depth :=
  SourceRecurrenceBound.guardedZero check.sourceCallDepthBound_of_guardedSemantic

end GuardedZeroCalls

/--
Executable SCC recurrence check result.

This is the small theorem-facing `Type` wrapper for the bounded-recursive
checker we currently support.  The semantic proof comes from the checked
guarded-zero backend, but the public resource path can talk about SCC entries,
procedures, ranked edges, and the maximum frame count without exposing the
backend recognizer as an arbitrary proof-carrying input.
-/
structure SCCRecurrenceCheckResult (program : Functions.Program) : Type where
  procedures : List Name
  entryNodes : List Node
  edges : List Edge
  maxFrames : Nat
  checked : GuardedZeroCalls.CheckResult program
  procedures_eq : procedures = GuardedZeroCalls.shapeNames checked.shapes
  entryNodes_eq : entryNodes = checked.roots
  edges_eq : edges = checked.edges
  maxFrames_eq : maxFrames = checked.depthCheck.depth

namespace SCCRecurrenceCheckResult

def ofGuardedZero {program : Functions.Program}
    (checked : GuardedZeroCalls.CheckResult program) :
    SCCRecurrenceCheckResult program where
  procedures := GuardedZeroCalls.shapeNames checked.shapes
  entryNodes := checked.roots
  edges := checked.edges
  maxFrames := checked.depthCheck.depth
  checked := checked
  procedures_eq := rfl
  entryNodes_eq := rfl
  edges_eq := rfl
  maxFrames_eq := rfl

theorem sourceRecurrenceBound
    {program : Functions.Program}
    (check : SCCRecurrenceCheckResult program) :
    SourceRecurrenceBound program check.maxFrames := by
  rw [check.maxFrames_eq]
  exact check.checked.sourceRecurrenceBound

theorem guardedSemanticCallDepthBound
    {program : Functions.Program}
    (check : SCCRecurrenceCheckResult program) :
    SourceCallDepth.Bound
      (GuardedZeroCalls.GuardedSemanticRootFrame program)
      (GuardedZeroCalls.GuardedSemanticDirectCall program)
      check.maxFrames := by
  rw [check.maxFrames_eq]
  exact check.checked.sourceCallDepthBound_of_guardedSemantic

theorem guardedSemanticRootChain_frame_count_bound
    {program : Functions.Program}
    (check : SCCRecurrenceCheckResult program)
    {frame : GuardedZeroCalls.SourceCallFrame} {depth : Nat}
    (hRoot :
      GuardedZeroCalls.GuardedSemanticRootFrame program frame)
    (hChain :
      ConcreteCallChain
        (GuardedZeroCalls.GuardedSemanticDirectCall program)
        frame depth) :
    depth + 1 ≤ check.maxFrames :=
  check.guardedSemanticCallDepthBound hRoot hChain

theorem guardedSemanticFrameStack_length_le
    {program : Functions.Program}
    (check : SCCRecurrenceCheckResult program)
    {frames : List GuardedZeroCalls.SourceCallFrame}
    (hStack :
      ConcreteFrameStack
        (GuardedZeroCalls.GuardedSemanticRootFrame program)
        (GuardedZeroCalls.GuardedSemanticDirectCall program)
        frames) :
    frames.length ≤ check.maxFrames :=
  ConcreteFrameStack.length_le_depth hStack
    check.guardedSemanticCallDepthBound

end SCCRecurrenceCheckResult

def checkSCCRecurrence?
    (program : Functions.Program) :
    Option (SCCRecurrenceCheckResult program) :=
  match GuardedZeroCalls.checkResult? program with
  | none => none
  | some checked => some (SCCRecurrenceCheckResult.ofGuardedZero checked)

theorem checkSCCRecurrence?_sound
    {program : Functions.Program}
    {check : SCCRecurrenceCheckResult program}
    (hCheck : checkSCCRecurrence? program = some check) :
    GuardedZeroCalls.checkResult? program = some check.checked ∧
      SourceRecurrenceBound program check.maxFrames := by
  unfold checkSCCRecurrence? at hCheck
  cases hChecked : GuardedZeroCalls.checkResult? program with
  | none =>
      simp [hChecked] at hCheck
  | some checked =>
      simp [hChecked] at hCheck
      cases hCheck
      exact
        ⟨rfl,
          by simpa using checked.sourceRecurrenceBound⟩

def sccRecurrenceDepth? (program : Functions.Program) : Option Nat :=
  match checkSCCRecurrence? program with
  | none => none
  | some check => some check.maxFrames

theorem sccRecurrenceDepth?_none_of_check_none
    {program : Functions.Program}
    (hCheck : checkSCCRecurrence? program = none) :
    sccRecurrenceDepth? program = none := by
  unfold sccRecurrenceDepth?
  simp [hCheck]

theorem sccRecurrenceDepth?_sourceRecurrenceBound
    {program : Functions.Program} {depth : Nat}
    (hDepth : sccRecurrenceDepth? program = some depth) :
    ∃ check : SCCRecurrenceCheckResult program,
      checkSCCRecurrence? program = some check ∧
        check.maxFrames = depth ∧
          SourceRecurrenceBound program depth := by
  unfold sccRecurrenceDepth? at hDepth
  cases hCheck : checkSCCRecurrence? program with
  | none =>
      simp [hCheck] at hDepth
  | some check =>
      simp [hCheck] at hDepth
      cases hDepth
      exact
        ⟨check, by simp, rfl,
          (checkSCCRecurrence?_sound hCheck).2⟩

namespace SourceCallDepth

/--
A semantic source call-depth contract.

The frame type is part of the contract because different analyses may need
different semantic call frames.  The current name-based checker uses only
function names, while the guarded-zero checker uses argument-carrying source
frames.  The trusted resource predicate below accepts only contracts marked
`Valid`; analyzer-specific check results are merely ways to prove a valid
contract has a finite depth.
-/
structure Contract (program : Functions.Program) : Type 1 where
  Frame : Type
  frameName : Frame → Name
  RootFrame : Frame → Prop
  DirectCall : Frame → Frame → Prop

namespace Contract

def byName (program : Functions.Program) : Contract program where
  Frame := Name
  frameName := id
  RootFrame := ProgramConformance.RootNameFrame program
  DirectCall := ProgramConformance.DirectNameCall program

def guardedZero (program : Functions.Program) : Contract program where
  Frame := GuardedZeroCalls.SourceCallFrame
  frameName := fun frame => frame.functionName
  RootFrame := GuardedZeroCalls.GuardedSemanticRootFrame program
  DirectCall := GuardedZeroCalls.GuardedSemanticDirectCall program

def depthBound {program : Functions.Program}
    (contract : Contract program) (bound : Nat) : Prop :=
  SourceCallDepth.Bound contract.RootFrame contract.DirectCall bound

/--
The registry of semantic call-depth contracts that preservation is allowed to
consume.  Adding analyzer power should mean adding a checked way to prove one
of these contracts, or adding a new contract here with a semantic coverage
theorem; the public resource layer should not inspect analyzer branches.
-/
inductive Valid {program : Functions.Program} :
    Contract program → Prop where
  | byName : Valid (byName program)
  | guardedZero : Valid (guardedZero program)

end Contract

def ActiveDepthBound (program : Functions.Program)
    (maxFrames : Nat) : Prop :=
  ∃ contract : Contract program,
    contract.Valid ∧ contract.depthBound maxFrames

structure ActiveStack {program : Functions.Program}
    (contract : Contract program) (active : List Name) : Type 1 where
  frames : List contract.Frame
  names : frames.map contract.frameName = active
  chain :
    ConcreteFrameStack contract.RootFrame contract.DirectCall frames

namespace ActiveStack

theorem length_le_depth
    {program : Functions.Program}
    {contract : Contract program}
    {active : List Name}
    {maxFrames : Nat}
    (hStack : ActiveStack contract active)
    (hBound : contract.depthBound maxFrames) :
    active.length ≤ maxFrames := by
  rw [← hStack.names]
  simp only [List.length_map]
  exact hStack.chain.length_le_depth hBound

end ActiveStack

def ActiveStackWitness (program : Functions.Program)
    (maxFrames : Nat) (active : List Name) : Prop :=
  ∃ contract : Contract program,
    contract.Valid ∧
      contract.depthBound maxFrames ∧
        Nonempty (ActiveStack contract active)

namespace ActiveStackWitness

theorem of_activeStack
    {program : Functions.Program} {maxFrames : Nat} {active : List Name}
    {contract : SourceCallDepth.Contract program}
    (hValid : contract.Valid)
    (hBound : contract.depthBound maxFrames)
    (hStack : SourceCallDepth.ActiveStack contract active) :
    ActiveStackWitness program maxFrames active :=
  ⟨contract, hValid, hBound, ⟨hStack⟩⟩

theorem empty_of_activeDepthBound
    {program : Functions.Program} {maxFrames : Nat}
    (hDepth : ActiveDepthBound program maxFrames) :
    ActiveStackWitness program maxFrames [] := by
  rcases hDepth with ⟨contract, hValid, hBound⟩
  exact
    of_activeStack hValid hBound
      { frames := []
        names := rfl
        chain := ConcreteFrameStack.empty }

theorem functionPathTo_nameChain
    {program : Functions.Program}
    {root current : Name} {depth : Nat}
    (hPath :
      _root_.EvmCompiler.Functions.CallDepth.FunctionPathTo
        program.functions root current depth) :
    ConcreteCallChain
      (ProgramConformance.DirectNameCall program) root depth := by
  induction hPath with
  | here _hFind =>
      exact ConcreteCallChain.here
  | call hFind hCall _hTail ih =>
      exact ConcreteCallChain.step ⟨_, hFind, hCall⟩ ih

theorem activeCallChain_to_concreteFrameStack
    {program : Functions.Program} {active : List Name}
    (hChain :
      _root_.EvmCompiler.Functions.CallDepth.Program.ActiveCallChain
        program active) :
    ConcreteFrameStack
      (ProgramConformance.RootNameFrame program)
      (ProgramConformance.DirectNameCall program) active := by
  induction hChain with
  | main =>
      exact ConcreteFrameStack.empty
  | root hRoot _hFind =>
      exact ConcreteFrameStack.root hRoot
  | push hActive hCaller hCallerFind hCall _hCalleeFind ih =>
      exact
        ConcreteFrameStack.snoc ih hCaller
          ⟨_, hCallerFind, hCall⟩

theorem byName_of_programActive
    {program : Functions.Program} {maxFrames : Nat} {active : List Name}
    (hBound :
      SourceCallDepth.Contract.depthBound
        (SourceCallDepth.Contract.byName program) maxFrames)
    (hActive :
      _root_.EvmCompiler.Functions.CallDepth.Program.ActiveCallStack
        program active) :
    ActiveStackWitness program maxFrames active := by
  refine
    ⟨SourceCallDepth.Contract.byName program,
      SourceCallDepth.Contract.Valid.byName, hBound, ?_⟩
  refine ⟨?_⟩
  refine
    { frames := active
      names := by simp [SourceCallDepth.Contract.byName]
      chain := activeCallChain_to_concreteFrameStack hActive.chain }

theorem guardedZero_empty
    {program : Functions.Program} {maxFrames : Nat}
    (hBound :
      SourceCallDepth.Contract.depthBound
        (SourceCallDepth.Contract.guardedZero program) maxFrames) :
    ActiveStackWitness program maxFrames [] :=
  of_activeStack
    SourceCallDepth.Contract.Valid.guardedZero hBound
    { frames := []
      names := rfl
      chain := ConcreteFrameStack.empty }

theorem guardedZero_root
    {program : Functions.Program} {maxFrames : Nat}
    {frame : GuardedZeroCalls.SourceCallFrame}
    (hBound :
      SourceCallDepth.Contract.depthBound
        (SourceCallDepth.Contract.guardedZero program) maxFrames)
    (hRoot :
      GuardedZeroCalls.GuardedSemanticRootFrame program frame) :
    ActiveStackWitness program maxFrames [frame.functionName] :=
  of_activeStack
    SourceCallDepth.Contract.Valid.guardedZero hBound
    { frames := [frame]
      names := by simp [SourceCallDepth.Contract.guardedZero]
      chain := ConcreteFrameStack.root hRoot }

theorem guardedZero_direct
    {program : Functions.Program} {maxFrames : Nat}
    {frame next : GuardedZeroCalls.SourceCallFrame}
    (hBound :
      SourceCallDepth.Contract.depthBound
        (SourceCallDepth.Contract.guardedZero program) maxFrames)
    (hRoot :
      GuardedZeroCalls.GuardedSemanticRootFrame program frame)
    (hCall :
      GuardedZeroCalls.GuardedSemanticDirectCall program frame next) :
    ActiveStackWitness program maxFrames
      [frame.functionName, next.functionName] :=
  of_activeStack
    SourceCallDepth.Contract.Valid.guardedZero hBound
    { frames := [frame, next]
      names := by simp [SourceCallDepth.Contract.guardedZero]
      chain := by
        simpa using
          ConcreteFrameStack.snoc
            (ConcreteFrameStack.root hRoot)
            (by simp : [frame].getLast? = some frame)
            hCall }

theorem guardedZero_of_frameStack
    {program : Functions.Program} {maxFrames : Nat}
    {frames : List GuardedZeroCalls.SourceCallFrame}
    {active : List Name}
    (hBound :
      SourceCallDepth.Contract.depthBound
        (SourceCallDepth.Contract.guardedZero program) maxFrames)
    (hNames : frames.map (fun frame => frame.functionName) = active)
    (hStack :
      ConcreteFrameStack
        (GuardedZeroCalls.GuardedSemanticRootFrame program)
        (GuardedZeroCalls.GuardedSemanticDirectCall program)
        frames) :
    ActiveStackWitness program maxFrames active := by
  subst active
  exact
    of_activeStack
      SourceCallDepth.Contract.Valid.guardedZero hBound
      { frames := frames
        names := rfl
        chain := hStack }

theorem length_le_depth
    {program : Functions.Program} {maxFrames : Nat} {active : List Name}
    (hWitness : ActiveStackWitness program maxFrames active) :
    active.length ≤ maxFrames := by
  rcases hWitness with
    ⟨contract, _hValid, hBound, ⟨hStack⟩⟩
  exact hStack.length_le_depth hBound

end ActiveStackWitness

end SourceCallDepth

namespace SourceRecurrenceBound

theorem activeDepthBound
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceRecurrenceBound program maxFrames) :
    SourceCallDepth.ActiveDepthBound program maxFrames := by
  cases bound with
  | byName hBound =>
      exact
        ⟨SourceCallDepth.Contract.byName program,
          SourceCallDepth.Contract.Valid.byName, hBound⟩
  | guardedZero hBound =>
      exact
        ⟨SourceCallDepth.Contract.guardedZero program,
          SourceCallDepth.Contract.Valid.guardedZero, hBound⟩

theorem activeStackWitness_empty
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceRecurrenceBound program maxFrames) :
    SourceCallDepth.ActiveStackWitness program maxFrames [] :=
  SourceCallDepth.ActiveStackWitness.empty_of_activeDepthBound
    bound.activeDepthBound

theorem activeStackWitness_of_programActive_byName
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceRecurrenceBound program maxFrames)
    {active : List Name}
    (hByName :
      ∃ hDepth :
        SourceCallDepth.Contract.depthBound
          (SourceCallDepth.Contract.byName program) maxFrames,
        bound =
          SourceRecurrenceBound.byName
            (program := program) (maxFrames := maxFrames) hDepth)
    (hActive :
      _root_.EvmCompiler.Functions.CallDepth.Program.ActiveCallStack
        program active) :
    SourceCallDepth.ActiveStackWitness program maxFrames active := by
  rcases hByName with ⟨hDepth, _hEq⟩
  exact
    SourceCallDepth.ActiveStackWitness.byName_of_programActive
      hDepth hActive

theorem activeStackWitness_of_guardedZero_frameStack
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceRecurrenceBound program maxFrames)
    {frames : List GuardedZeroCalls.SourceCallFrame}
    {active : List Name}
    (hGuarded :
      ∃ hDepth :
        SourceCallDepth.Contract.depthBound
          (SourceCallDepth.Contract.guardedZero program) maxFrames,
        bound =
          SourceRecurrenceBound.guardedZero
            (program := program) (maxFrames := maxFrames) hDepth)
    (hNames : frames.map (fun frame => frame.functionName) = active)
    (hStack :
      ConcreteFrameStack
        (GuardedZeroCalls.GuardedSemanticRootFrame program)
        (GuardedZeroCalls.GuardedSemanticDirectCall program)
        frames) :
    SourceCallDepth.ActiveStackWitness program maxFrames active := by
  rcases hGuarded with ⟨hDepth, _hEq⟩
  exact
    SourceCallDepth.ActiveStackWitness.guardedZero_of_frameStack
      hDepth hNames hStack

end SourceRecurrenceBound

def sourceStackWordsForMaxFramesWithFrameWords
    (frameWords maxFrames : Nat) : Nat :=
  16 + frameWords * maxFrames + 17

def sourceStackFitsEVMWithFrameWords
    (frameWords maxFrames : Nat) : Prop :=
  sourceStackWordsForMaxFramesWithFrameWords frameWords maxFrames ≤ 1024

def sourceStackFitsEVMWithFrameWords?
    (frameWords maxFrames : Nat) : Bool :=
  Nat.ble
    (sourceStackWordsForMaxFramesWithFrameWords frameWords maxFrames) 1024

theorem sourceStackFitsEVMWithFrameWords?_eq_true
    {frameWords maxFrames : Nat} :
    sourceStackFitsEVMWithFrameWords? frameWords maxFrames = true ↔
      sourceStackFitsEVMWithFrameWords frameWords maxFrames := by
  unfold sourceStackFitsEVMWithFrameWords?
  unfold sourceStackFitsEVMWithFrameWords
  rw [Nat.ble_eq]

theorem sourceStackFitsEVMWithFrameWords?_sound
    {frameWords maxFrames : Nat}
    (hFits :
      sourceStackFitsEVMWithFrameWords? frameWords maxFrames = true) :
    sourceStackFitsEVMWithFrameWords frameWords maxFrames :=
  sourceStackFitsEVMWithFrameWords?_eq_true.mp hFits

theorem sourceStackFitsEVMWithFrameWords?_complete
    {frameWords maxFrames : Nat}
    (hFits : sourceStackFitsEVMWithFrameWords frameWords maxFrames) :
    sourceStackFitsEVMWithFrameWords? frameWords maxFrames = true :=
  sourceStackFitsEVMWithFrameWords?_eq_true.mpr hFits

def sourceStackWordsForProgram
    (program : Functions.Program) (maxFrames : Nat) : Nat :=
  sourceStackWordsForMaxFramesWithFrameWords
    (_root_.EvmCompiler.Functions.CallDepth.Program.maxSourceReturnFrameWords
      program)
    maxFrames

def sourceStackFitsEVMForProgram
    (program : Functions.Program) (maxFrames : Nat) : Prop :=
  sourceStackWordsForProgram program maxFrames ≤ 1024

def sourceStackFitsEVMForProgram?
    (program : Functions.Program) (maxFrames : Nat) : Bool :=
  Nat.ble (sourceStackWordsForProgram program maxFrames) 1024

theorem sourceStackFitsEVMForProgram?_eq_true
    {program : Functions.Program} {maxFrames : Nat} :
    sourceStackFitsEVMForProgram? program maxFrames = true ↔
      sourceStackFitsEVMForProgram program maxFrames := by
  unfold sourceStackFitsEVMForProgram? sourceStackFitsEVMForProgram
  rw [Nat.ble_eq]

theorem sourceStackFitsEVMForProgram?_sound
    {program : Functions.Program} {maxFrames : Nat}
    (hFits : sourceStackFitsEVMForProgram? program maxFrames = true) :
    sourceStackFitsEVMForProgram program maxFrames :=
  sourceStackFitsEVMForProgram?_eq_true.mp hFits

theorem sourceStackFitsEVMForProgram?_complete
    {program : Functions.Program} {maxFrames : Nat}
    (hFits : sourceStackFitsEVMForProgram program maxFrames) :
    sourceStackFitsEVMForProgram? program maxFrames = true :=
  sourceStackFitsEVMForProgram?_eq_true.mpr hFits

def sourceStackWordsForMaxFrames (maxFrames : Nat) : Nat :=
  sourceStackWordsForMaxFramesWithFrameWords 17 maxFrames

def sourceStackFitsEVM (maxFrames : Nat) : Prop :=
  sourceStackFitsEVMWithFrameWords 17 maxFrames

def sourceMaxFramesForEVM : Nat := 58

theorem sourceStackFitsEVM_iff_le_sourceMaxFramesForEVM
    {maxFrames : Nat} :
    sourceStackFitsEVM maxFrames ↔ maxFrames ≤ sourceMaxFramesForEVM := by
  unfold sourceStackFitsEVM sourceStackFitsEVMWithFrameWords
    sourceStackWordsForMaxFramesWithFrameWords
    sourceMaxFramesForEVM
  omega

def sourceStackFitsEVM? (maxFrames : Nat) : Bool :=
  Nat.ble maxFrames sourceMaxFramesForEVM

theorem sourceStackFitsEVM?_eq_true
    {maxFrames : Nat} :
    sourceStackFitsEVM? maxFrames = true ↔
      sourceStackFitsEVM maxFrames := by
  unfold sourceStackFitsEVM?
  rw [Nat.ble_eq]
  exact sourceStackFitsEVM_iff_le_sourceMaxFramesForEVM.symm

theorem sourceStackFitsEVM?_sound
    {maxFrames : Nat}
    (hFits : sourceStackFitsEVM? maxFrames = true) :
    sourceStackFitsEVM maxFrames := by
  exact sourceStackFitsEVM?_eq_true.mp hFits

theorem sourceStackFitsEVM?_complete
    {maxFrames : Nat}
    (hFits : sourceStackFitsEVM maxFrames) :
    sourceStackFitsEVM? maxFrames = true :=
  sourceStackFitsEVM?_eq_true.mpr hFits

theorem sourceStackFitsEVM_58 : sourceStackFitsEVM 58 := by
  rw [sourceStackFitsEVM_iff_le_sourceMaxFramesForEVM]
  simp [sourceMaxFramesForEVM]

theorem not_sourceStackFitsEVM_59 : ¬ sourceStackFitsEVM 59 := by
  rw [sourceStackFitsEVM_iff_le_sourceMaxFramesForEVM]
  simp [sourceMaxFramesForEVM]

example : sourceStackFitsEVM? 58 = true := by
  native_decide

example : sourceStackFitsEVM? 59 = false := by
  native_decide

structure SourceResourceBound
    (program : Functions.Program) (maxFrames : Nat) : Prop where
  recurrence : SourceRecurrenceBound program maxFrames
  stackFits : sourceStackFitsEVM maxFrames

structure SourceFrameWordsResourceBound
    (program : Functions.Program) (maxFrames : Nat) : Prop where
  recurrence : SourceRecurrenceBound program maxFrames
  stackFits : sourceStackFitsEVMForProgram program maxFrames

namespace SourceFrameWordsResourceBound

theorem activeDepthBound
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceFrameWordsResourceBound program maxFrames) :
    SourceCallDepth.ActiveDepthBound program maxFrames :=
  bound.recurrence.activeDepthBound

theorem activeStackWitness_empty
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceFrameWordsResourceBound program maxFrames) :
    SourceCallDepth.ActiveStackWitness program maxFrames [] :=
  SourceCallDepth.ActiveStackWitness.empty_of_activeDepthBound
    bound.activeDepthBound

def toFrameWordStackBudget
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceFrameWordsResourceBound program maxFrames) :
    _root_.EvmCompiler.Functions.CallDepth.FrameWordStackBudget where
  depth := maxFrames
  frameWords :=
    _root_.EvmCompiler.Functions.CallDepth.Program.maxSourceReturnFrameWords
      program
  budget := by
    simpa [sourceStackFitsEVMForProgram, sourceStackWordsForProgram,
      sourceStackWordsForMaxFramesWithFrameWords]
      using bound.stackFits

theorem sourceStackHeadroom_of_frameWordsContext
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceFrameWordsResourceBound program maxFrames)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      _root_.EvmCompiler.Functions.CallDepth.SourceDirectFrameWordsContext
        program
        (_root_.EvmCompiler.Functions.CallDepth.Program.maxSourceReturnFrameWords
          program)
        active layout hiddenReturns source target)
    (hActiveLength : active.length ≤ maxFrames) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  context.sourceStackHeadroomWithBound
    (budget := bound.toFrameWordStackBudget)
    (by
      simpa [toFrameWordStackBudget] using hActiveLength)

theorem sourceStackHeadroom_of_activeStackWitness
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceFrameWordsResourceBound program maxFrames)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      _root_.EvmCompiler.Functions.CallDepth.SourceDirectFrameWordsContext
        program
        (_root_.EvmCompiler.Functions.CallDepth.Program.maxSourceReturnFrameWords
          program)
        active layout hiddenReturns source target)
    (hActive :
      SourceCallDepth.ActiveStackWitness program maxFrames active) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  bound.sourceStackHeadroom_of_frameWordsContext context
    (SourceCallDepth.ActiveStackWitness.length_le_depth hActive)

end SourceFrameWordsResourceBound

namespace SourceResourceBound

theorem activeDepthBound
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames) :
    SourceCallDepth.ActiveDepthBound program maxFrames :=
  bound.recurrence.activeDepthBound

theorem activeStackWitness_empty
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames) :
    SourceCallDepth.ActiveStackWitness program maxFrames [] :=
  SourceCallDepth.ActiveStackWitness.empty_of_activeDepthBound
    bound.activeDepthBound

theorem activeStackWitness_of_programActive_byName
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames)
    {active : List Name}
    (hByName :
      ∃ hDepth :
        SourceCallDepth.Contract.depthBound
          (SourceCallDepth.Contract.byName program) maxFrames,
        bound.recurrence =
          SourceRecurrenceBound.byName
            (program := program) (maxFrames := maxFrames) hDepth)
    (hActive :
      _root_.EvmCompiler.Functions.CallDepth.Program.ActiveCallStack
        program active) :
    SourceCallDepth.ActiveStackWitness program maxFrames active :=
  bound.recurrence.activeStackWitness_of_programActive_byName
    hByName hActive

theorem activeStackWitness_of_guardedZero_frameStack
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames)
    {frames : List GuardedZeroCalls.SourceCallFrame}
    {active : List Name}
    (hGuarded :
      ∃ hDepth :
        SourceCallDepth.Contract.depthBound
          (SourceCallDepth.Contract.guardedZero program) maxFrames,
        bound.recurrence =
          SourceRecurrenceBound.guardedZero
            (program := program) (maxFrames := maxFrames) hDepth)
    (hNames : frames.map (fun frame => frame.functionName) = active)
    (hStack :
      ConcreteFrameStack
        (GuardedZeroCalls.GuardedSemanticRootFrame program)
        (GuardedZeroCalls.GuardedSemanticDirectCall program)
        frames) :
    SourceCallDepth.ActiveStackWitness program maxFrames active :=
  bound.recurrence.activeStackWitness_of_guardedZero_frameStack
    hGuarded hNames hStack

def toStackBudget
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames) :
    _root_.EvmCompiler.Functions.CallDepth.StackBudget where
  depth := maxFrames
  budget := by
    simpa [sourceStackFitsEVM, sourceStackFitsEVMWithFrameWords,
      sourceStackWordsForMaxFramesWithFrameWords]
      using bound.stackFits

def toStackResourceCheckResult
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceCheckResult program where
  budget := bound.toStackBudget
  baseSafe := _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafeFromBase_of_budget program
    bound.toStackBudget
  safe := _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafe_of_budget program
    bound.toStackBudget

theorem stackResourceSafeFromBase
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceSafeFromBase program bound.toStackBudget :=
  _root_.EvmCompiler.Functions.CallDepth.Program.stackResourceSafeFromBase_of_budget program
    bound.toStackBudget

theorem sourceStackHeadroom_of_base
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectBaseContext program active layout hiddenReturns source
        target)
    (hActiveLength : active.length ≤ maxFrames) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  bound.stackResourceSafeFromBase context (by
    simpa [toStackBudget] using hActiveLength)

theorem sourceStackHeadroom_of_activeStackWitness
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectBaseContext program active layout hiddenReturns source
        target)
    (hActive :
      SourceCallDepth.ActiveStackWitness program maxFrames active) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  bound.sourceStackHeadroom_of_base context
    (SourceCallDepth.ActiveStackWitness.length_le_depth hActive)

theorem sourceStackHeadroom_empty
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames)
    {layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectBaseContext program [] layout hiddenReturns source
        target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  bound.sourceStackHeadroom_of_activeStackWitness context
    bound.activeStackWitness_empty

def toResourceContext
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectBaseContext program active layout hiddenReturns source
        target)
    (hActiveLength : active.length ≤ maxFrames) :
    SourceDirectResourceContext program bound.toStackBudget active
      layout hiddenReturns source target :=
  context.toResourceContext (by
    simpa [toStackBudget] using hActiveLength)

def toResourceContext_empty
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames)
    {layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectBaseContext program [] layout hiddenReturns source
        target) :
    SourceDirectResourceContext program bound.toStackBudget []
      layout hiddenReturns source target :=
  bound.toResourceContext context
    (SourceCallDepth.ActiveStackWitness.length_le_depth
      bound.activeStackWitness_empty)

def toResourceContext_of_activeStackWitness
    {program : Functions.Program} {maxFrames : Nat}
    (bound : SourceResourceBound program maxFrames)
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (context :
      SourceDirectBaseContext program active layout hiddenReturns source
        target)
    (hActive :
      SourceCallDepth.ActiveStackWitness program maxFrames active) :
    SourceDirectResourceContext program bound.toStackBudget active
      layout hiddenReturns source target :=
  bound.toResourceContext context
    (SourceCallDepth.ActiveStackWitness.length_le_depth hActive)

end SourceResourceBound

structure ActiveCallStack (edges : List Edge) (roots : List Node)
    (active : List Name) (nodes : List Node) : Prop where
  names : nodes.map Node.functionName = active
  path :
    nodes = [] ∨
      ∃ root current pathLen,
        root ∈ roots ∧
          nodes.getLast? = some current ∧
          nodes.length = pathLen + 1 ∧
          PathTo edges root current pathLen

namespace ActiveCallStack

theorem getLast?_map_eq_some {α β : Type} (f : α → β) :
    ∀ {values : List α} {value : α},
      values.getLast? = some value →
        (values.map f).getLast? = some (f value)
  | [], _value, hLast => by
      simp at hLast
  | head :: tail, value, hLast => by
      cases tail with
      | nil =>
          simp at hLast ⊢
          cases hLast
          rfl
      | cons next rest =>
          simp at hLast ⊢
          exact getLast?_map_eq_some f hLast

theorem main {edges : List Edge} {roots : List Node} :
    ActiveCallStack edges roots [] [] where
  names := rfl
  path := Or.inl rfl

theorem root {edges : List Edge} {roots : List Node}
    {rootNode : Node}
    (hRoot : rootNode ∈ roots) :
    ActiveCallStack edges roots [rootNode.functionName] [rootNode] where
  names := by simp
  path := by
    right
    refine ⟨rootNode, rootNode, 0, hRoot, ?_, ?_, ?_⟩
    · simp
    · simp
    · exact PathTo.here

theorem push {edges : List Edge} {roots : List Node}
    {active : List Name} {nodes : List Node}
    {current next : Node}
    (hActive : ActiveCallStack edges roots active nodes)
    (hCurrent : nodes.getLast? = some current)
    (hEdge : next ∈ Edge.successors edges current) :
    ActiveCallStack edges roots (active ++ [next.functionName])
      (nodes ++ [next]) where
  names := by
    rw [List.map_append, hActive.names]
    simp
  path := by
    rcases hActive.path with hEmpty | hPath
    · cases hEmpty
      simp at hCurrent
    · rcases hPath with
        ⟨rootNode, currentNode, pathLen, hRoot, hLast, hLength,
          hPathTo⟩
      have hCurrentEq : currentNode = current := by
        rw [hLast] at hCurrent
        cases hCurrent
        rfl
      subst currentNode
      right
      refine
        ⟨rootNode, next, pathLen + 1, hRoot, ?_, ?_, ?_⟩
      · simp
      · simp [hLength]
      · exact PathTo.snoc hPathTo hEdge

theorem length_le_depth {edges : List Edge} {roots : List Node}
    (check : Program.RankedDepthCheckResult edges roots)
    {active : List Name} {nodes : List Node}
    (hActive : ActiveCallStack edges roots active nodes) :
    active.length ≤ check.depth := by
  have hNamesLen : active.length = nodes.length := by
    rw [← hActive.names]
    simp
  rcases hActive.path with hEmpty | hPath
  · cases hEmpty
    simp [hNamesLen]
  · rcases hPath with
      ⟨rootNode, currentNode, pathLen, hRoot, _hLast, hLength,
        hPathTo⟩
    have hBound := check.path_bound hRoot hPathTo.toPath
    omega

theorem length_le_checked_depth {program : Functions.Program}
    (check : CheckedProgramCheckResult program)
    {active : List Name} {nodes : List Node}
    (hActive :
      ActiveCallStack check.edges check.roots active nodes) :
    active.length ≤ check.depthCheck.depth :=
  length_le_depth check.depthCheck hActive

theorem current_mem_graphNodes {edges : List Edge} {roots : List Node}
    {active : List Name} {nodes : List Node} {current : Node}
    (hActive : ActiveCallStack edges roots active nodes)
    (hCurrent : nodes.getLast? = some current) :
    current ∈ graphNodes edges roots := by
  rcases hActive.path with hEmpty | hPath
  · cases hEmpty
    simp at hCurrent
  · rcases hPath with
      ⟨rootNode, currentNode, pathLen, hRoot, hLast, _hLength,
        hPathTo⟩
    have hCurrentEq : currentNode = current := by
      rw [hLast] at hCurrent
      cases hCurrent
      rfl
    subst currentNode
    exact pathTo_target_mem_graphNodes hRoot hPathTo

theorem successor_of_conformance
    {program : Functions.Program}
    {edges : List Edge} {roots : List Node}
    (hConformance : ProgramConformance program edges roots)
    {active : List Name} {nodes : List Node}
    {current : Node} {caller callee : Name} {callerFn : FunDef}
    (hActive : ActiveCallStack edges roots active nodes)
    (hCurrent : nodes.getLast? = some current)
    (hCurrentName : current.functionName = caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn) :
    ∃ next,
      next ∈ Edge.successors edges current ∧
        next.functionName = callee := by
  have hCurrentMem := current_mem_graphNodes hActive hCurrent
  have hFind :
      FunList.find? current.functionName program.functions =
        some callerFn := by
    rw [hCurrentName]
    exact hCallerFind
  exact hConformance.call hCurrentMem hFind hCall

theorem active_getLast?_of_current
    {edges : List Edge} {roots : List Node}
    {active : List Name} {nodes : List Node}
    {current : Node} {caller : Name}
    (hActive : ActiveCallStack edges roots active nodes)
    (hCurrent : nodes.getLast? = some current)
    (hCurrentName : current.functionName = caller) :
    active.getLast? = some caller := by
  have hMap :=
    getLast?_map_eq_some Node.functionName hCurrent
  rw [hActive.names] at hMap
  rw [hCurrentName] at hMap
  exact hMap

end ActiveCallStack

theorem runtimeCallStackShape_of_sourceDirectStateRel
    {program : Functions.Program}
    {edges : List Edge} {roots rankedNodes : List Node}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (check : Program.RankedDepthCheckResult edges roots)
    (hProgramActive : CallDepth.Program.ActiveCallStack program active)
    (hRankedActive : ActiveCallStack edges roots active rankedNodes)
    (hLayout : layout.length ≤ 16)
    (hReturnsLength : hiddenReturns.length = active.length)
    (hCallers :
      ∀ frame, frame ∈ hiddenReturns →
        frame.callerStack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    RuntimeCallStackShape program check.toStackBudget active
      target :=
  RuntimeCallStackShape.of_sourceDirectStateRelWithBound
    hProgramActive (ActiveCallStack.length_le_depth check hRankedActive)
    hLayout hReturnsLength hCallers hRel

theorem sourceDirectResourceContext_of_ranked
    {program : Functions.Program}
    {edges : List Edge} {roots rankedNodes : List Node}
    {active layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (check : Program.RankedDepthCheckResult edges roots)
    (hProgramActive : CallDepth.Program.ActiveCallStack program active)
    (hRankedActive : ActiveCallStack edges roots active rankedNodes)
    (hLayout : layout.length ≤ 16)
    (hReturnsLength : hiddenReturns.length = active.length)
    (hCallers :
      ∀ frame, frame ∈ hiddenReturns →
        frame.callerStack.length ≤ 16)
    (hRel :
      SourceDirect.StateRel layout hiddenReturns source target) :
    SourceDirectResourceContext program check.toStackBudget active
      layout hiddenReturns source target :=
  SourceDirectResourceContext.of_sourceDirectStateRelWithBound
    hProgramActive (ActiveCallStack.length_le_depth check hRankedActive)
    hLayout hReturnsLength hCallers hRel

/--
Ranked stack-resource context: the ordinary source/direct resource invariant
plus the ranked active-node path that justifies the generic stack budget.

This is the handoff point for bounded recursive analyses.  The CALL refactor can
thread the ordinary `SourceDirectResourceContext`; once it has a ranked
successor node for each internal call, this package supplies the active-frame
bound without falling back to the acyclic checker.
-/
structure RankedResourceContext (program : Functions.Program)
    {edges : List Edge} {roots : List Node}
    (check : Program.RankedDepthCheckResult edges roots)
    (active : List Name) (nodes : List Node)
    (layout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (source : Source.State) (target : Structured.RunState) : Prop where
  context :
    _root_.EvmCompiler.Functions.CallDepth.SourceDirectResourceContext
      program check.toStackBudget active layout hiddenReturns
      source target
  rankedActive : ActiveCallStack edges roots active nodes

namespace RankedResourceContext

theorem sourceStackHeadroom
    {program : Functions.Program}
    {edges : List Edge} {roots : List Node}
    {check : Program.RankedDepthCheckResult edges roots}
    {active : List Name} {nodes : List Node}
    {layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Structured.RunState}
    (hContext :
      RankedResourceContext program check active nodes layout hiddenReturns
        source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  hContext.context.sourceStackHeadroom

theorem main
    {program : Functions.Program}
    {edges : List Edge} {roots : List Node}
    {check : Program.RankedDepthCheckResult edges roots}
    {layout : List Name}
    {source : Source.State} {target : Structured.RunState}
    (hLayout : layout.length ≤ 16)
    (hRel : SourceDirect.StateRel layout [] source target) :
    RankedResourceContext program check [] [] layout [] source target where
  context :=
    _root_.EvmCompiler.Functions.CallDepth.SourceDirectResourceContext.main
      (program := program) (budget := check.toStackBudget)
      hLayout hRel
  rankedActive := ActiveCallStack.main

theorem rootCallBodyWithNode
    {program : Functions.Program}
    {edges : List Edge} {roots : List Node}
    {check : Program.RankedDepthCheckResult edges roots}
    {callerLayout calleeLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    {rootNode : Node}
    (hCaller :
      RankedResourceContext program check [] [] callerLayout []
        callerSource callerTarget)
    (hRoot : callee ∈
      _root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls
        program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hRootNode : rootNode ∈ roots)
    (hRootName : rootNode.functionName = callee)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    RankedResourceContext program check [callee] [rootNode] calleeLayout
      [{ callerStack := callerTarget.evm.stack, retc := retc }]
      calleeSource calleeTarget := by
  subst callee
  have hRankedActive :
      ActiveCallStack edges roots [rootNode.functionName] [rootNode] :=
    ActiveCallStack.root hRootNode
  refine
    { context := ?_
      rankedActive := hRankedActive }
  exact
    _root_.EvmCompiler.Functions.CallDepth.SourceDirectResourceContext.rootCallBody
        (program := program)
        (budget := check.toStackBudget)
        hCaller.context hRoot hCalleeFind
        (ActiveCallStack.length_le_depth check hRankedActive)
        hCalleeLayout hRel

theorem rootCallBody
    {program : Functions.Program}
    {edges : List Edge} {roots : List Node}
    {check : Program.RankedDepthCheckResult edges roots}
    (hConformance : ProgramConformance program edges roots)
    {callerLayout calleeLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    (hCaller :
      RankedResourceContext program check [] [] callerLayout []
        callerSource callerTarget)
    (hRoot : callee ∈
      _root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls
        program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    ∃ rootNode,
      RankedResourceContext program check [callee] [rootNode] calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget := by
  rcases hConformance.root hRoot with ⟨rootNode, hRootNode, hRootName⟩
  exact
    ⟨rootNode,
      rootCallBodyWithNode hCaller hRoot hCalleeFind hRootNode hRootName
        hCalleeLayout hRel⟩

theorem rootCallBodyChecked
    {program : Functions.Program}
    (checked : CheckedProgramCheckResult program)
    {callerLayout calleeLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callee : Name} {calleeFn : FunDef} {retc : Nat}
    (hCaller :
      RankedResourceContext program checked.depthCheck [] [] callerLayout []
        callerSource callerTarget)
    (hRoot : callee ∈
      _root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls
        program)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    ∃ rootNode,
      RankedResourceContext program checked.depthCheck [callee] [rootNode]
        calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget :=
  rootCallBody checked.conformance hCaller hRoot hCalleeFind
    hCalleeLayout hRel

theorem callBodyWithNode
    {program : Functions.Program}
    {edges : List Edge} {roots : List Node}
    {check : Program.RankedDepthCheckResult edges roots}
    {active callerLayout calleeLayout : List Name}
    {nodes : List Node}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    {current next : Node}
    (hCallerContext :
      RankedResourceContext program check active nodes callerLayout
        hiddenReturns callerSource callerTarget)
    (hCurrent : nodes.getLast? = some current)
    (hCurrentName : current.functionName = caller)
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hEdge : next ∈ Edge.successors edges current)
    (hNextName : next.functionName = callee)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    RankedResourceContext program check (active ++ [callee])
      (nodes ++ [next])
      calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget := by
  subst callee
  have hRankedActive :
      ActiveCallStack edges roots
        (active ++ [next.functionName]) (nodes ++ [next]) :=
    ActiveCallStack.push hCallerContext.rankedActive hCurrent hEdge
  have hCallerLast : active.getLast? = some caller :=
    ActiveCallStack.active_getLast?_of_current
      hCallerContext.rankedActive hCurrent hCurrentName
  refine
    { context := ?_
      rankedActive := hRankedActive }
  exact
    _root_.EvmCompiler.Functions.CallDepth.SourceDirectResourceContext.callBodyWithBound
        (program := program)
        (budget := check.toStackBudget)
        hCallerContext.context hCallerLast hCallerFind hCall hCalleeFind
        (ActiveCallStack.length_le_depth check hRankedActive)
        hCalleeLayout hRel

theorem callBody
    {program : Functions.Program}
    {edges : List Edge} {roots : List Node}
    {check : Program.RankedDepthCheckResult edges roots}
    (hConformance : ProgramConformance program edges roots)
    {active callerLayout calleeLayout : List Name}
    {nodes : List Node}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    {current : Node}
    (hCallerContext :
      RankedResourceContext program check active nodes callerLayout
        hiddenReturns callerSource callerTarget)
    (hCurrent : nodes.getLast? = some current)
    (hCurrentName : current.functionName = caller)
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
    ∃ next,
      RankedResourceContext program check (active ++ [callee])
        (nodes ++ [next])
        calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget := by
  rcases
      ActiveCallStack.successor_of_conformance hConformance
        hCallerContext.rankedActive hCurrent hCurrentName
        hCallerFind hCall with
    ⟨next, hEdge, hNextName⟩
  exact
    ⟨next,
      callBodyWithNode hCallerContext hCurrent hCurrentName hCallerFind
        hCall hCalleeFind hEdge hNextName hCalleeLayout hRel⟩

theorem callBodyChecked
    {program : Functions.Program}
    (checked : CheckedProgramCheckResult program)
    {active callerLayout calleeLayout : List Name}
    {nodes : List Node}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    {current : Node}
    (hCallerContext :
      RankedResourceContext program checked.depthCheck active nodes
        callerLayout hiddenReturns callerSource callerTarget)
    (hCurrent : nodes.getLast? = some current)
    (hCurrentName : current.functionName = caller)
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
    ∃ next,
      RankedResourceContext program checked.depthCheck (active ++ [callee])
        (nodes ++ [next])
        calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget :=
  callBody checked.conformance hCallerContext hCurrent hCurrentName
    hCallerFind hCall hCalleeFind hCalleeLayout hRel

theorem afterAttachReturnsWithCaller?
    {program : Functions.Program}
    {edges : List Edge} {roots : List Node}
    {check : Program.RankedDepthCheckResult edges roots}
    {active : List Name} {callerNodes : List Node} {callee : Name}
    {calleeNodes : List Node}
    {calleeLayout callerLayout : List Name}
    {calleeHidden callerHidden : List Structured.ReturnDest}
    {calleeSource callerSource : Source.State}
    {state returned callerTarget : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Word}
    {callerProofSource : Source.State}
    {callerProofTarget : Structured.RunState}
    (hCalleeContext :
      RankedResourceContext program check (active ++ [callee])
        calleeNodes calleeLayout calleeHidden calleeSource state)
    (hCallerContext :
      RankedResourceContext program check active callerNodes callerLayout
        callerHidden callerProofSource callerProofTarget)
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
    RankedResourceContext program check active callerNodes callerLayout
      callerHidden callerSource callerTarget := by
  refine
    { context := ?_
      rankedActive := hCallerContext.rankedActive }
  exact
    _root_.EvmCompiler.Functions.CallDepth.SourceDirectResourceContext.afterAttachReturnsWithBound?
        (program := program)
        (budget := check.toStackBudget)
        hCalleeContext.context
        hCallerContext.context.runtime.activeStack
        (ActiveCallStack.length_le_depth check hCallerContext.rankedActive)
        hPop hAttach hReturnFrameVisible hCallerTarget hRel

end RankedResourceContext

namespace GuardedZeroCalls

theorem CheckResult.rootCallBody_of_sourceRootFrame
    {program : Functions.Program}
    (check : CheckResult program)
    {callerLayout calleeLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {retc : Nat} {rootFrame : SourceCallFrame}
    {calleeFn : FunDef}
    (hCaller :
      RankedResourceContext program check.depthCheck [] [] callerLayout []
        callerSource callerTarget)
    (hRoot : SourceRootFrame check.roots rootFrame)
    (hCalleeFind :
      FunList.find? rootFrame.functionName program.functions =
        some calleeFn)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    ∃ rootNode,
      RankedResourceContext program check.depthCheck
        [rootFrame.functionName] [rootNode] calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget := by
  rcases hRoot with ⟨rootNode, hRootMem, hMatch⟩
  have hRootName : rootNode.functionName = rootFrame.functionName :=
    SourceMatches.functionName_eq hMatch
  have hMainCall :
      rootFrame.functionName ∈
        _root_.EvmCompiler.Functions.CallDepth.Program.mainInternalCalls
          program := by
    rw [← hRootName]
    exact (check.root_mem_facts hRootMem).2.2
  exact
    ⟨rootNode,
      RankedResourceContext.rootCallBodyWithNode
        (program := program)
        (check := check.depthCheck)
        (callee := rootFrame.functionName)
        (calleeFn := calleeFn)
        (rootNode := rootNode)
        hCaller hMainCall hCalleeFind hRootMem hRootName hCalleeLayout
        hRel⟩

theorem CheckResult.callBodyOneToZero
    {program : Functions.Program}
    (check : CheckResult program)
    {active callerLayout calleeLayout : List Name}
    {nodes : List Node}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Name} {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      RankedResourceContext program check.depthCheck active nodes callerLayout
        hiddenReturns callerSource callerTarget)
    (hCurrent : nodes.getLast? = some (node caller 1))
    (hCallerFind :
      FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? callee program.functions = some calleeFn)
    (hShape : (caller, callee) ∈ check.shapes)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    RankedResourceContext program check.depthCheck
      (active ++ [callee])
      (nodes ++ [node callee 0])
      calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget := by
  exact
    RankedResourceContext.callBodyWithNode
      (program := program)
      (check := check.depthCheck)
      (caller := caller)
      (callee := callee)
      (current := node caller 1)
      (next := node callee 0)
      hCallerContext hCurrent rfl hCallerFind hCall hCalleeFind
      (by
        rw [check.edges_eq]
        exact edgeForShape_successor hShape)
      rfl hCalleeLayout hRel

theorem CheckResult.callBody_of_sourceDirectCall
    {program : Functions.Program}
    (check : CheckResult program)
    {active callerLayout calleeLayout : List Name}
    {nodes : List Node}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callerFrame nextFrame : SourceCallFrame}
    {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      RankedResourceContext program check.depthCheck active nodes callerLayout
        hiddenReturns callerSource callerTarget)
    (hCurrent :
      nodes.getLast? = some (node callerFrame.functionName 1))
    (hDirect :
      SourceDirectCall check.shapes callerFrame nextFrame)
    (hCallerFind :
      FunList.find? callerFrame.functionName program.functions =
        some callerFn)
    (hCall : nextFrame.functionName ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? nextFrame.functionName program.functions =
        some calleeFn)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    RankedResourceContext program check.depthCheck
      (active ++ [nextFrame.functionName])
      (nodes ++ [node nextFrame.functionName 0])
      calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget := by
  rcases hDirect with
    ⟨arg, _hArgs, _hArgNonzero, _hNextArgs, hShape⟩
  exact
    check.callBodyOneToZero hCallerContext hCurrent hCallerFind hCall
      hCalleeFind hShape hCalleeLayout hRel

end GuardedZeroCalls

namespace SelfGuardedOnce

theorem CheckResult.rootCallBodyDerived
    {program : Functions.Program}
    (check : CheckResult program)
    {callerLayout calleeLayout : List Name}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {retc : Nat} {rootNode : Node}
    (hCaller :
      RankedResourceContext program check.depthCheck [] [] callerLayout []
        callerSource callerTarget)
    (hRootNode : rootNode ∈ check.roots)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget) :
    RankedResourceContext program check.depthCheck [check.functionName]
      [rootNode] calleeLayout
      [{ callerStack := callerTarget.evm.stack, retc := retc }]
      calleeSource calleeTarget := by
  rcases check.find_function with ⟨fn, hFind, _hCalls⟩
  rcases check.root_mem_facts hRootNode with
    ⟨hRootName, _hRootRank, hMainCall⟩
  exact
    RankedResourceContext.rootCallBodyWithNode
      (program := program)
      (check := check.depthCheck)
      (callee := check.functionName)
      (calleeFn := fn)
      (rootNode := rootNode)
      hCaller hMainCall hFind hRootNode hRootName hCalleeLayout hRel

theorem CheckResult.callBodyOneToZero
    {program : Functions.Program}
    (check : CheckResult program)
    {active callerLayout calleeLayout : List Name}
    {nodes : List Node}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {callerFn calleeFn : FunDef} {retc : Nat}
    (hCallerContext :
      RankedResourceContext program check.depthCheck active nodes callerLayout
        hiddenReturns callerSource callerTarget)
    (hCurrent : nodes.getLast? = some (node check.functionName 1))
    (hCallerFind :
      FunList.find? check.functionName program.functions = some callerFn)
    (hCall : check.functionName ∈ FunDef.internalCalls callerFn)
    (hCalleeFind :
      FunList.find? check.functionName program.functions = some calleeFn)
    (hRankOneRoot : node check.functionName 1 ∈ check.roots)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    RankedResourceContext program check.depthCheck
      (active ++ [check.functionName])
      (nodes ++ [node check.functionName 0])
      calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget :=
  RankedResourceContext.callBodyWithNode
    (program := program)
    (check := check.depthCheck)
    (caller := check.functionName)
    (callee := check.functionName)
    (current := node check.functionName 1)
    (next := node check.functionName 0)
    hCallerContext hCurrent rfl hCallerFind hCall hCalleeFind
    (check.edge_one_zero_of_root hRankOneRoot) rfl hCalleeLayout hRel

theorem CheckResult.callBodyOneToZeroDerived
    {program : Functions.Program}
    (check : CheckResult program)
    {active callerLayout calleeLayout : List Name}
    {nodes : List Node}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {retc : Nat}
    (hCallerContext :
      RankedResourceContext program check.depthCheck active nodes callerLayout
        hiddenReturns callerSource callerTarget)
    (hCurrent : nodes.getLast? = some (node check.functionName 1))
    (hRankOneRoot : node check.functionName 1 ∈ check.roots)
    (hCalleeLayout : calleeLayout.length ≤ 16)
    (hRel :
      SourceDirect.StateRel calleeLayout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    RankedResourceContext program check.depthCheck
      (active ++ [check.functionName])
      (nodes ++ [node check.functionName 0])
      calleeLayout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget := by
  rcases check.find_function with ⟨fn, hFind, hCalls⟩
  have hCall : check.functionName ∈ FunDef.internalCalls fn := by
    rw [hCalls]
    simp
  exact
    check.callBodyOneToZero hCallerContext hCurrent hFind hCall hFind
      hRankOneRoot hCalleeLayout hRel

end SelfGuardedOnce

inductive SourceRecurrenceAnalyzer where
  | acyclic
  | guardedZeroCalls
  deriving DecidableEq, Repr

namespace SourceRecurrenceAnalyzer

def run : SourceRecurrenceAnalyzer → Functions.Program → Option Nat
  | .acyclic, program => inferAcyclicRecurrenceDepth? program
  | .guardedZeroCalls, program => sccRecurrenceDepth? program

theorem run_sourceRecurrenceBound
    {analyzer : SourceRecurrenceAnalyzer}
    {program : Functions.Program} {depth : Nat}
    (hRun : analyzer.run program = some depth) :
    SourceRecurrenceBound program depth := by
  cases analyzer with
  | acyclic =>
      rcases inferAcyclicRecurrenceDepth?_sound hRun with ⟨check, hDepth⟩
      cases hDepth
      exact check.sourceRecurrenceBound
  | guardedZeroCalls =>
      rcases sccRecurrenceDepth?_sourceRecurrenceBound hRun with
        ⟨_check, _hCheck, hDepth, hBound⟩
      cases hDepth
      exact hBound

theorem run_sourceResourceBound
    {analyzer : SourceRecurrenceAnalyzer}
    {program : Functions.Program} {depth : Nat}
    (hRun : analyzer.run program = some depth)
    (hFits : sourceStackFitsEVM? depth = true) :
    SourceResourceBound program depth := by
  let recurrence := run_sourceRecurrenceBound hRun
  exact
    { recurrence := recurrence
      stackFits := sourceStackFitsEVM?_sound hFits }

theorem run_sourceFrameWordsResourceBound
    {analyzer : SourceRecurrenceAnalyzer}
    {program : Functions.Program} {depth : Nat}
    (hRun : analyzer.run program = some depth)
    (hFits : sourceStackFitsEVMForProgram? program depth = true) :
    SourceFrameWordsResourceBound program depth := by
  let recurrence := run_sourceRecurrenceBound hRun
  exact
    { recurrence := recurrence
      stackFits := sourceStackFitsEVMForProgram?_sound hFits }

def resourceDepth? (analyzer : SourceRecurrenceAnalyzer)
    (program : Functions.Program) : Option Nat :=
  match analyzer.run program with
  | none => none
  | some depth =>
      if sourceStackFitsEVM? depth then
        some depth
      else
        none

def frameWordsResourceDepth? (analyzer : SourceRecurrenceAnalyzer)
    (program : Functions.Program) : Option Nat :=
  match analyzer.run program with
  | none => none
  | some depth =>
      if sourceStackFitsEVMForProgram? program depth then
        some depth
      else
        none

theorem resourceDepth?_sound
    {analyzer : SourceRecurrenceAnalyzer}
    {program : Functions.Program} {depth : Nat}
    (hDepth : analyzer.resourceDepth? program = some depth) :
    SourceResourceBound program depth := by
  unfold resourceDepth? at hDepth
  cases hRun : analyzer.run program with
  | none =>
      simp [hRun] at hDepth
  | some checkedDepth =>
      cases hFits : sourceStackFitsEVM? checkedDepth
      · simp [hRun, hFits] at hDepth
      · simp [hRun, hFits] at hDepth
        cases hDepth
        exact run_sourceResourceBound hRun hFits

theorem frameWordsResourceDepth?_sound
    {analyzer : SourceRecurrenceAnalyzer}
    {program : Functions.Program} {depth : Nat}
    (hDepth : analyzer.frameWordsResourceDepth? program = some depth) :
    SourceFrameWordsResourceBound program depth := by
  unfold frameWordsResourceDepth? at hDepth
  cases hRun : analyzer.run program with
  | none =>
      simp [hRun] at hDepth
  | some checkedDepth =>
      cases hFits : sourceStackFitsEVMForProgram? program checkedDepth
      · simp [hRun, hFits] at hDepth
      · simp [hRun, hFits] at hDepth
        cases hDepth
        exact run_sourceFrameWordsResourceBound hRun hFits

end SourceRecurrenceAnalyzer

def defaultSourceRecurrenceAnalyzers : List SourceRecurrenceAnalyzer :=
  [.acyclic, .guardedZeroCalls]

def firstSome? {α β : Type} : List α → (α → Option β) → Option β
  | [], _f => none
  | value :: rest, f =>
      match f value with
      | some result => some result
      | none => firstSome? rest f

theorem firstSome?_sound {α β : Type}
    {values : List α} {f : α → Option β} {P : β → Prop} {result : β}
    (hEach :
      ∀ value, value ∈ values → ∀ result, f value = some result → P result)
    (hResult : firstSome? values f = some result) :
    P result := by
  induction values with
  | nil =>
      simp [firstSome?] at hResult
  | cons value rest ih =>
      unfold firstSome? at hResult
      cases hValue : f value with
      | none =>
          simp [hValue] at hResult
          exact ih
            (by
              intro next hNext found hFound
              exact hEach next (by simp [hNext]) found hFound)
            hResult
      | some found =>
          simp [hValue] at hResult
          have hEq : found = result := by
            simpa using hResult
          have hFound : P found := hEach value (by simp) found hValue
          simpa [hEq] using hFound

def firstSourceRecurrenceDepth? :
    List SourceRecurrenceAnalyzer → Functions.Program → Option Nat
  | [], _program => none
  | analyzer :: rest, program =>
      match analyzer.run program with
      | some depth => some depth
      | none => firstSourceRecurrenceDepth? rest program

theorem firstSourceRecurrenceDepth?_sourceRecurrenceBound
    {analyzers : List SourceRecurrenceAnalyzer}
    {program : Functions.Program} {depth : Nat}
    (hDepth :
      firstSourceRecurrenceDepth? analyzers program = some depth) :
    SourceRecurrenceBound program depth := by
  induction analyzers with
  | nil =>
      simp [firstSourceRecurrenceDepth?] at hDepth
  | cons analyzer rest ih =>
      unfold firstSourceRecurrenceDepth? at hDepth
      cases hRun : analyzer.run program with
      | none =>
          simp [hRun] at hDepth
          exact ih hDepth
      | some checkedDepth =>
          simp [hRun] at hDepth
          cases hDepth
          exact SourceRecurrenceAnalyzer.run_sourceRecurrenceBound hRun

def firstSourceResourceDepth? :
    List SourceRecurrenceAnalyzer → Functions.Program → Option Nat
  | analyzers, program =>
      firstSome? analyzers (fun analyzer => analyzer.resourceDepth? program)

def firstSourceFrameWordsResourceDepth? :
    List SourceRecurrenceAnalyzer → Functions.Program → Option Nat
  | analyzers, program =>
      firstSome? analyzers
        (fun analyzer => analyzer.frameWordsResourceDepth? program)

theorem firstSourceResourceDepth?_sound
    {analyzers : List SourceRecurrenceAnalyzer}
    {program : Functions.Program} {depth : Nat}
    (hDepth : firstSourceResourceDepth? analyzers program = some depth) :
    SourceResourceBound program depth := by
  unfold firstSourceResourceDepth? at hDepth
  exact
    firstSome?_sound
      (values := analyzers)
      (f := fun analyzer : SourceRecurrenceAnalyzer =>
        analyzer.resourceDepth? program)
      (P := fun depth => SourceResourceBound program depth)
      (by
        intro analyzer _hAnalyzer checkedDepth hChecked
        exact SourceRecurrenceAnalyzer.resourceDepth?_sound hChecked)
      hDepth

theorem firstSourceFrameWordsResourceDepth?_sound
    {analyzers : List SourceRecurrenceAnalyzer}
    {program : Functions.Program} {depth : Nat}
    (hDepth :
      firstSourceFrameWordsResourceDepth? analyzers program = some depth) :
    SourceFrameWordsResourceBound program depth := by
  unfold firstSourceFrameWordsResourceDepth? at hDepth
  exact
    firstSome?_sound
      (values := analyzers)
      (f := fun analyzer : SourceRecurrenceAnalyzer =>
        analyzer.frameWordsResourceDepth? program)
      (P := fun depth => SourceFrameWordsResourceBound program depth)
      (by
        intro analyzer _hAnalyzer checkedDepth hChecked
        exact SourceRecurrenceAnalyzer.frameWordsResourceDepth?_sound
          hChecked)
      hDepth

def sourceRecurrenceDepth? (program : Functions.Program) : Option Nat :=
  firstSourceRecurrenceDepth? defaultSourceRecurrenceAnalyzers program

theorem sourceRecurrenceDepth?_eq_some_cases
    {program : Functions.Program} {depth : Nat}
    (hDepth : sourceRecurrenceDepth? program = some depth) :
    (∃ check : CheckedProgramRecurrenceCheckResult program,
      check.depth = depth) ∨
      (inferAcyclicRecurrenceDepth? program = none ∧
        ∃ check : SCCRecurrenceCheckResult program,
          checkSCCRecurrence? program = some check ∧
            check.maxFrames = depth) := by
  unfold sourceRecurrenceDepth? defaultSourceRecurrenceAnalyzers
    firstSourceRecurrenceDepth? SourceRecurrenceAnalyzer.run at hDepth
  cases hInferred : inferAcyclicRecurrenceDepth? program with
  | some inferredDepth =>
      simp [hInferred] at hDepth
      cases hDepth
      exact Or.inl (inferAcyclicRecurrenceDepth?_sound hInferred)
  | none =>
      simp [hInferred, firstSourceRecurrenceDepth?,
        SourceRecurrenceAnalyzer.run] at hDepth
      cases hGuarded : sccRecurrenceDepth? program with
      | none =>
          simp [hGuarded] at hDepth
      | some guardedDepth =>
          simp [hGuarded] at hDepth
          cases hDepth
          rcases sccRecurrenceDepth?_sourceRecurrenceBound hGuarded with
            ⟨check, hCheck, hDepth, _hBound⟩
          exact Or.inr ⟨rfl, ⟨check, hCheck, hDepth⟩⟩

theorem sourceRecurrenceDepth?_sourceRecurrenceBound
    {program : Functions.Program} {depth : Nat}
    (hDepth : sourceRecurrenceDepth? program = some depth) :
    SourceRecurrenceBound program depth :=
  firstSourceRecurrenceDepth?_sourceRecurrenceBound hDepth

theorem sourceRecurrenceDepth?_none_of_default_branches_none
    {program : Functions.Program}
    (hAcyclic : inferAcyclicRecurrenceDepth? program = none)
    (hSCC : checkSCCRecurrence? program = none) :
    sourceRecurrenceDepth? program = none := by
  have hSCCDepth := sccRecurrenceDepth?_none_of_check_none hSCC
  simp [sourceRecurrenceDepth?, defaultSourceRecurrenceAnalyzers,
    firstSourceRecurrenceDepth?, SourceRecurrenceAnalyzer.run, hAcyclic,
    hSCCDepth]

def sourceResourceDepth? (program : Functions.Program) : Option Nat :=
  firstSourceResourceDepth? defaultSourceRecurrenceAnalyzers program

def sourceFrameWordsResourceDepth? (program : Functions.Program) :
    Option Nat :=
  firstSourceFrameWordsResourceDepth? defaultSourceRecurrenceAnalyzers program

theorem sourceResourceDepth?_none_of_default_branches_none
    {program : Functions.Program}
    (hAcyclic : inferAcyclicRecurrenceDepth? program = none)
    (hSCC : checkSCCRecurrence? program = none) :
    sourceResourceDepth? program = none := by
  have hSCCDepth := sccRecurrenceDepth?_none_of_check_none hSCC
  simp [sourceResourceDepth?, firstSourceResourceDepth?,
    defaultSourceRecurrenceAnalyzers, firstSome?,
    SourceRecurrenceAnalyzer.resourceDepth?, SourceRecurrenceAnalyzer.run,
    hAcyclic, hSCCDepth]

theorem sourceResourceDepth?_eq_some_cases
    {program : Functions.Program} {depth : Nat}
    (hDepth : sourceResourceDepth? program = some depth) :
    (inferAcyclicRecurrenceDepth? program = some depth ∧
        sourceStackFitsEVM? depth = true ∧
        ∃ check : CheckedProgramRecurrenceCheckResult program,
          check.depth = depth) ∨
      (((inferAcyclicRecurrenceDepth? program = none) ∨
          ∃ acyclicDepth,
            inferAcyclicRecurrenceDepth? program = some acyclicDepth ∧
              sourceStackFitsEVM? acyclicDepth = false) ∧
        ∃ check : SCCRecurrenceCheckResult program,
          checkSCCRecurrence? program = some check ∧
            check.maxFrames = depth ∧
              sourceStackFitsEVM? depth = true) := by
  unfold sourceResourceDepth? firstSourceResourceDepth?
    defaultSourceRecurrenceAnalyzers firstSome?
    SourceRecurrenceAnalyzer.resourceDepth? SourceRecurrenceAnalyzer.run
    at hDepth
  cases hAcyclic : inferAcyclicRecurrenceDepth? program with
  | none =>
      simp [hAcyclic] at hDepth
      cases hSCC : sccRecurrenceDepth? program with
      | none =>
          simp [firstSome?, hSCC] at hDepth
      | some sccDepth =>
          cases hFits : sourceStackFitsEVM? sccDepth
          · simp [firstSome?, hSCC, hFits] at hDepth
          · simp [firstSome?, hSCC, hFits] at hDepth
            cases hDepth
            rcases sccRecurrenceDepth?_sourceRecurrenceBound hSCC with
              ⟨check, hCheck, hCheckDepth, _hBound⟩
            exact Or.inr
              ⟨Or.inl rfl, ⟨check, hCheck, hCheckDepth, hFits⟩⟩
  | some acyclicDepth =>
      cases hAcyclicFits : sourceStackFitsEVM? acyclicDepth
      · simp [hAcyclic, hAcyclicFits] at hDepth
        cases hSCC : sccRecurrenceDepth? program with
        | none =>
            simp [firstSome?, hSCC] at hDepth
        | some sccDepth =>
            cases hFits : sourceStackFitsEVM? sccDepth
            · simp [firstSome?, hSCC, hFits] at hDepth
            · simp [firstSome?, hSCC, hFits] at hDepth
              cases hDepth
              rcases sccRecurrenceDepth?_sourceRecurrenceBound hSCC with
                ⟨check, hCheck, hCheckDepth, _hBound⟩
              exact Or.inr
                ⟨Or.inr ⟨acyclicDepth, rfl, hAcyclicFits⟩,
                  ⟨check, hCheck, hCheckDepth, hFits⟩⟩
      · simp [hAcyclic, hAcyclicFits] at hDepth
        cases hDepth
        exact Or.inl
          ⟨rfl, hAcyclicFits,
            inferAcyclicRecurrenceDepth?_sound hAcyclic⟩

theorem sourceResourceDepth?_eq_some
    {program : Functions.Program} {depth : Nat}
    (hDepth : sourceResourceDepth? program = some depth) :
    SourceResourceBound program depth :=
  firstSourceResourceDepth?_sound hDepth

theorem sourceResourceDepth?_sound
    {program : Functions.Program} {depth : Nat}
    (hDepth : sourceResourceDepth? program = some depth) :
    SourceResourceBound program depth :=
  sourceResourceDepth?_eq_some hDepth

theorem sourceFrameWordsResourceDepth?_sound
    {program : Functions.Program} {depth : Nat}
    (hDepth : sourceFrameWordsResourceDepth? program = some depth) :
    SourceFrameWordsResourceBound program depth :=
  firstSourceFrameWordsResourceDepth?_sound hDepth

namespace Examples

def emptyBlock : Block :=
  { stmts := [] }

def leafFunction : FunDef :=
  { name := "leaf"
    params := []
    returns := []
    body := emptyBlock }

def rootFunction : FunDef :=
  { name := "root"
    params := []
    returns := []
    body := { stmts := [.call [] "leaf" []] } }

def simpleProgram : Functions.Program :=
  { functions := [rootFunction, leafFunction]
    body := { stmts := [.call [] "root" []] } }

def countdownNode (name : Name) (rank : Nat) : Node :=
  { functionName := name, rank := rank }

def simpleRoot : Node :=
  countdownNode "root" 0

def simpleLeaf : Node :=
  countdownNode "leaf" 0

def simpleEdges : List Edge :=
  [{ src := simpleRoot, dst := simpleLeaf }]

def simpleRoots : List Node :=
  [simpleRoot]

example :
    graphConforms? simpleProgram simpleEdges simpleRoots = true := by
  native_decide

example :
    Program.rankedMaxRootDepth? simpleEdges simpleRoots = some 2 := by
  native_decide

example :
    (Program.rankedDepthCheck? simpleEdges simpleRoots).isSome =
      true := by
  native_decide

example :
    (checkedProgramCheck? simpleProgram simpleEdges simpleRoots).isSome =
      true := by
  native_decide

example :
    (checkStackRecurrenceCandidate? simpleProgram
      { edges := simpleEdges, roots := simpleRoots }).isSome = true := by
  native_decide

example :
    (inferAcyclicCheck? simpleProgram).isSome = true := by
  native_decide

example :
    (inferStackRecurrences? simpleProgram).isSome = true := by
  native_decide

example :
    graphConforms? simpleProgram [] simpleRoots = false := by
  native_decide

example :
    (checkedProgramCheck? simpleProgram [] simpleRoots).isNone =
      true := by
  native_decide

def selfFunction : FunDef :=
  { name := "loop"
    params := []
    returns := []
    body := { stmts := [.call [] "loop" []] } }

def selfProgram : Functions.Program :=
  { functions := [selfFunction]
    body := { stmts := [.call [] "loop" []] } }

example :
    (inferAcyclicCheck? selfProgram).isNone = true := by
  native_decide

example :
    (inferStackRecurrences? selfProgram).isNone = true := by
  native_decide

def countdownEdges (name : Name) : Nat → List Edge
  | 0 => []
  | rank + 1 =>
      { src := countdownNode name (rank + 1)
        dst := countdownNode name rank } :: countdownEdges name rank

def countdownRoots (name : Name) (rank : Nat) : List Node :=
  [countdownNode name rank]

example :
    Program.rankedMaxRootDepth? (countdownEdges "loop" 3)
      (countdownRoots "loop" 3) = some 4 := by
  native_decide

example :
    (Program.rankedDepthCheck? (countdownEdges "loop" 3)
      (countdownRoots "loop" 3)).isSome = true := by
  native_decide

example :
    graphConforms? selfProgram (countdownEdges "loop" 3)
      (countdownRoots "loop" 3) = false := by
  native_decide

example :
    (checkedProgramCheck? selfProgram (countdownEdges "loop" 3)
      (countdownRoots "loop" 3)).isNone = true := by
  native_decide

def guardedOnceFunction : FunDef :=
  { name := "loop"
    params := ["n"]
    returns := []
    body :=
      { stmts :=
          [.if_ (.var "n")
            { stmts := [.call [] "loop" [.lit (EvmYul.UInt256.ofNat 0)]] }] } }

def guardedOnceProgram : Functions.Program :=
  { functions := [guardedOnceFunction]
    body :=
      { stmts :=
          [.call [] "loop" [.lit (EvmYul.UInt256.ofNat 7)]] } }

example :
    SelfGuardedOnce.programShape? guardedOnceProgram =
      some ("loop", [SelfGuardedOnce.node "loop" 1]) := by
  native_decide

example :
    (SelfGuardedOnce.checkResult? guardedOnceProgram).isSome =
      true := by
  native_decide

example :
    (sourceRecurrenceDepth? guardedOnceProgram).isSome = true := by
  native_decide

example :
    sourceRecurrenceDepth? guardedOnceProgram = some 2 := by
  native_decide

example :
    (sourceResourceDepth? guardedOnceProgram).isSome = true := by
  native_decide

example :
    sourceResourceDepth? guardedOnceProgram = some 2 := by
  native_decide

example :
    (inferStackRecurrences? guardedOnceProgram).isNone = true := by
  native_decide

example :
    Program.rankedMaxRootDepth? (SelfGuardedOnce.edgesUpTo "loop" 1)
      [SelfGuardedOnce.node "loop" 1] = some 2 := by
  native_decide

example :
    (checkedProgramCheck? guardedOnceProgram
      (SelfGuardedOnce.edgesUpTo "loop" 1)
      [SelfGuardedOnce.node "loop" 1]).isNone = true := by
  native_decide

example :
    (SelfGuardedOnce.checkResult? selfProgram).isNone = true := by
  native_decide

def unboundedGuardFunction : FunDef :=
  { name := "loop"
    params := ["n"]
    returns := []
    body :=
      { stmts :=
          [.if_ (.var "n")
            { stmts := [.call [] "loop" [.var "n"]] }] } }

def unboundedGuardProgram : Functions.Program :=
  { functions := [unboundedGuardFunction]
    body :=
      { stmts :=
          [.call [] "loop" [.lit (EvmYul.UInt256.ofNat 7)]] } }

example :
    (SelfGuardedOnce.checkResult? unboundedGuardProgram).isNone =
      true := by
  native_decide

example :
    sourceRecurrenceDepth? unboundedGuardProgram = none := by
  native_decide

example :
    sourceResourceDepth? unboundedGuardProgram = none := by
  native_decide

def guardedMutualLeft : FunDef :=
  { name := "left"
    params := ["n"]
    returns := []
    body :=
      { stmts :=
          [.if_ (.var "n")
            { stmts := [.call [] "right" [.lit (EvmYul.UInt256.ofNat 0)]] }] } }

def guardedMutualRight : FunDef :=
  { name := "right"
    params := ["n"]
    returns := []
    body :=
      { stmts :=
          [.if_ (.var "n")
            { stmts := [.call [] "left" [.lit (EvmYul.UInt256.ofNat 0)]] }] } }

def guardedMutualProgram : Functions.Program :=
  { functions := [guardedMutualLeft, guardedMutualRight]
    body :=
      { stmts :=
          [.call [] "left" [.lit (EvmYul.UInt256.ofNat 7)]] } }

example :
    (SelfGuardedOnce.checkResult? guardedMutualProgram).isNone =
      true := by
  native_decide

example :
    MutualGuardedOnce.programShape? guardedMutualProgram =
      some ("left", "right", [MutualGuardedOnce.node "left" 1]) := by
  native_decide

example :
    (MutualGuardedOnce.checkResult? guardedMutualProgram).isSome =
      true := by
  native_decide

example :
    (sourceRecurrenceDepth? guardedMutualProgram).isSome = true := by
  native_decide

example :
    sourceRecurrenceDepth? guardedMutualProgram = some 2 := by
  native_decide

example :
    (sourceResourceDepth? guardedMutualProgram).isSome = true := by
  native_decide

example :
    sourceResourceDepth? guardedMutualProgram = some 2 := by
  native_decide

example :
    Program.rankedMaxRootDepth?
        (MutualGuardedOnce.edgesUpTo "left" "right" 1)
        [MutualGuardedOnce.node "left" 1] =
      some 2 := by
  native_decide

example :
    (checkedProgramCheck? guardedMutualProgram
      (MutualGuardedOnce.edgesUpTo "left" "right" 1)
      [MutualGuardedOnce.node "left" 1]).isNone = true := by
  native_decide

example :
    (MutualGuardedOnce.checkResult? selfProgram).isNone = true := by
  native_decide

def guardedTripleA : FunDef :=
  { name := "a"
    params := ["n"]
    returns := []
    body :=
      { stmts :=
          [.if_ (.var "n")
            { stmts := [.call [] "b" [.lit (EvmYul.UInt256.ofNat 0)]] }] } }

def guardedTripleB : FunDef :=
  { name := "b"
    params := ["n"]
    returns := []
    body :=
      { stmts :=
          [.if_ (.var "n")
            { stmts := [.call [] "c" [.lit (EvmYul.UInt256.ofNat 0)]] }] } }

def guardedTripleC : FunDef :=
  { name := "c"
    params := ["n"]
    returns := []
    body :=
      { stmts :=
          [.if_ (.var "n")
            { stmts := [.call [] "a" [.lit (EvmYul.UInt256.ofNat 0)]] }] } }

def guardedTripleWrappedA : FunDef :=
  { name := "a"
    params := ["n"]
    returns := []
    body :=
      { stmts :=
          [.block
            { stmts :=
                [.if_ (.var "n")
                  { stmts :=
                      [.block
                        { stmts :=
                            [.call [] "b"
                              [.lit (EvmYul.UInt256.ofNat 0)]] }] }] }] } }

def guardedTripleProgram : Functions.Program :=
  { functions := [guardedTripleA, guardedTripleB, guardedTripleC]
    body :=
      { stmts :=
          [.call [] "a" [.lit (EvmYul.UInt256.ofNat 7)]] } }

def guardedTripleWrappedBodyProgram : Functions.Program :=
  { functions := [guardedTripleWrappedA, guardedTripleB, guardedTripleC]
    body :=
      { stmts :=
          [.call [] "a" [.lit (EvmYul.UInt256.ofNat 7)]] } }

example :
    (SelfGuardedOnce.checkResult? guardedTripleProgram).isNone =
      true := by
  native_decide

example :
    (MutualGuardedOnce.checkResult? guardedTripleProgram).isNone =
      true := by
  native_decide

example :
    GuardedZeroCalls.programShape? guardedTripleProgram =
      some
        ([("a", "b"), ("b", "c"), ("c", "a")],
          [GuardedZeroCalls.node "a" 1]) := by
  native_decide

example :
    (GuardedZeroCalls.checkResult? guardedTripleProgram).isSome =
      true := by
  native_decide

example :
    (sourceRecurrenceDepth? guardedTripleProgram).isSome = true := by
  native_decide

example :
    sourceRecurrenceDepth? guardedTripleProgram = some 2 := by
  native_decide

example :
    (sourceResourceDepth? guardedTripleProgram).isSome = true := by
  native_decide

example :
    sourceResourceDepth? guardedTripleProgram = some 2 := by
  native_decide

example :
    GuardedZeroCalls.programShape? guardedTripleWrappedBodyProgram =
      some
        ([("a", "b"), ("b", "c"), ("c", "a")],
          [GuardedZeroCalls.node "a" 1]) := by
  native_decide

example :
    (GuardedZeroCalls.checkResult?
      guardedTripleWrappedBodyProgram).isSome = true := by
  native_decide

def guardedTripleNestedRootProgram : Functions.Program :=
  { functions := [guardedTripleA, guardedTripleB, guardedTripleC]
    body :=
      { stmts :=
          [.block
            { stmts :=
                [.call [] "a" [.lit (EvmYul.UInt256.ofNat 7)]] },
           .if_ (.lit (EvmYul.UInt256.ofNat 1))
            { stmts :=
                [.call [] "b" [.lit (EvmYul.UInt256.ofNat 0)]] }] } }

example :
    GuardedZeroCalls.programShape? guardedTripleNestedRootProgram =
      some
        ([("a", "b"), ("b", "c"), ("c", "a")],
          [GuardedZeroCalls.node "a" 1,
           GuardedZeroCalls.node "b" 0]) := by
  native_decide

example :
    (GuardedZeroCalls.checkResult?
      guardedTripleNestedRootProgram).isSome = true := by
  native_decide

example :
    sourceResourceDepth? guardedTripleNestedRootProgram = some 2 := by
  native_decide

def guardedTripleCompositeRootProgram : Functions.Program :=
  { functions := [guardedTripleA, guardedTripleB, guardedTripleC]
    body :=
      { stmts :=
          [.block
            { stmts :=
                [.call [] "a" [.lit (EvmYul.UInt256.ofNat 7)],
                 .if_ (.lit (EvmYul.UInt256.ofNat 1))
                  { stmts :=
                      [.call [] "b"
                        [.lit (EvmYul.UInt256.ofNat 0)]] }] }] } }

example :
    GuardedZeroCalls.programShape? guardedTripleCompositeRootProgram =
      some
        ([("a", "b"), ("b", "c"), ("c", "a")],
          [GuardedZeroCalls.node "a" 1,
           GuardedZeroCalls.node "b" 0]) := by
  native_decide

example :
    (GuardedZeroCalls.checkResult?
      guardedTripleCompositeRootProgram).isSome = true := by
  native_decide

example :
    sourceResourceDepth? guardedTripleCompositeRootProgram = some 2 := by
  native_decide

example :
    Program.rankedMaxRootDepth?
        (GuardedZeroCalls.edgesForShapes
          [("a", "b"), ("b", "c"), ("c", "a")])
        [GuardedZeroCalls.node "a" 1] =
      some 2 := by
  native_decide

example :
    (GuardedZeroCalls.checkResult? selfProgram).isNone = true := by
  native_decide

example :
    sourceRecurrenceDepth? selfProgram = none := by
  native_decide

example :
    sourceResourceDepth? selfProgram = none := by
  native_decide

def unrankedSelfLoop : List Edge :=
  [{ src := countdownNode "loop" 0, dst := countdownNode "loop" 0 }]

example :
    Program.rankedMaxRootDepth? unrankedSelfLoop
      (countdownRoots "loop" 0) = none := by
  native_decide

def mutualCountdownEdges (left right : Name) : Nat → List Edge
  | 0 => []
  | rank + 1 =>
      { src := countdownNode left (rank + 1)
        dst := countdownNode right (rank + 1) } ::
      { src := countdownNode right (rank + 1)
        dst := countdownNode left rank } ::
      mutualCountdownEdges left right rank

example :
    Program.rankedMaxRootDepth? (mutualCountdownEdges "even" "odd" 3)
      (countdownRoots "even" 3) = some 7 := by
  native_decide

example :
    (Program.rankedDepthCheck? (mutualCountdownEdges "even" "odd" 3)
      (countdownRoots "even" 3)).isSome = true := by
  native_decide

def rankedChainName (index : Nat) : Name :=
  s!"ranked_chain_{index}"

def rankedChainFunctionsFrom : Nat → Nat → List FunDef
  | 0, _index => []
  | count + 1, index =>
      { name := rankedChainName index
        params := []
        returns := []
        body :=
          if count = 0 then
            emptyBlock
          else
            { stmts := [.call [] (rankedChainName (index + 1)) []] } } ::
        rankedChainFunctionsFrom count (index + 1)

def rankedChainProgram (count : Nat) : Functions.Program :=
  { functions := rankedChainFunctionsFrom count 0
    body :=
      if count = 0 then
        emptyBlock
      else
        { stmts := [.call [] (rankedChainName 0) []] } }

example :
    inferAcyclicDepth? (rankedChainProgram 58) = some 58 := by
  native_decide

example :
    inferAcyclicRecurrenceDepth? (rankedChainProgram 58) = some 58 := by
  native_decide

example :
    sourceRecurrenceDepth? (rankedChainProgram 58) = some 58 := by
  native_decide

example :
    sourceResourceDepth? (rankedChainProgram 58) = some 58 := by
  native_decide

example :
    inferAcyclicRecurrenceDepth? (rankedChainProgram 59) = some 59 := by
  native_decide

example :
    sourceRecurrenceDepth? (rankedChainProgram 59) = some 59 := by
  native_decide

example :
    inferAcyclicDepth? (rankedChainProgram 59) = none := by
  native_decide

example :
    sourceResourceDepth? (rankedChainProgram 59) = none := by
  native_decide

end Examples

end Ranked
end CallDepth
end Functions
end EvmCompiler
