import EvmCompiler.TypedCfg.Syntax

namespace EvmCompiler
namespace TypedCfg

namespace Instr

def type? (instr : Instr) (shape : Shape) : Option Shape :=
  match instr with
  | .push value => some (.literal value :: shape)
  | .prim op =>
      match op.continuingStep? with
      | none =>
          if op.haltKind?.isSome then
            none
          else
            match op.stackEffect? with
            | some (inputArity, outputArity) =>
                if inputArity ≤ shape.length then
                  some
                    (Shape.pushWords outputArity
                      (Shape.pop inputArity shape))
                else
                  none
            | none => none
      | some step =>
          if step.inputArity ≤ shape.length then
            some (Shape.pushWords step.outputArity (Shape.pop step.inputArity shape))
          else
            none
  | .pop =>
      match shape with
      | [] => none
      | _ :: rest => some rest
  | .dup depth =>
      if depth < 16 then
        match shape[depth]? with
        | some slot => some (slot :: shape)
        | none => none
      else
        none
  | .swap depth =>
      if depth < 16 then
        match shape, shape[depth]? with
        | top :: rest, some slot =>
            some (slot :: (rest.set (depth - 1) top))
        | _, none => none
        | [], _ => none
      else
        none
  | .unwind target =>
      Shape.unwindTo target shape

end Instr

namespace Block

def bodyType? : List Instr → Shape → Option Shape
  | [], shape => some shape
  | instr :: rest, shape => do
      let shape' ← instr.type? shape
      bodyType? rest shape'

end Block

namespace Terminator

def targets : Terminator → List Label
  | .fallthrough => []
  | .jump target => [target]
  | .jumpi target next => [target, next]
  | .returnDispatch _ => []
  | .halt _ => []
  | .invalid => []

def type? (program : Program) (shape : Shape) : Terminator → Option Unit
  | .fallthrough => some ()
  | .jump target => do
      let targetShape ← program.labelShape? target
      if shape = targetShape then some () else none
  | .jumpi target next => do
      let targetShape ← program.labelShape? target
      let fallthroughShape ← program.labelShape? next
      match shape with
      | _cond :: rest =>
          if rest = targetShape ∧ rest = fallthroughShape then some () else none
      | _ => none
  | .returnDispatch siteShape =>
      if shape = siteShape then some () else none
  | .halt kind =>
      if kind.argCount ≤ shape.length then some () else none
  | .invalid => some ()

end Terminator

namespace Block

def type? (program : Program) (block : Block) : Option Unit := do
  let output ← bodyType? block.body block.input
  block.term.type? program output

def WellTyped (program : Program) (block : Block) : Prop :=
  ∃ output, bodyType? block.body block.input = some output ∧
    block.term.type? program output = some ()

end Block

namespace Program

def LabelsUnique (program : Program) : Prop :=
  program.blocks.Pairwise (fun left right => left.label ≠ right.label)

def AllBlocksTyped (program : Program) : Prop :=
  ∀ block, block ∈ program.blocks → block.WellTyped program

def WellTyped (program : Program) : Prop :=
  program.LabelsUnique ∧ program.AllBlocksTyped ∧ program.findBlock? program.entry ≠ none

def labelsUnique? : List Block → Bool
  | [] => true
  | block :: rest =>
      rest.all (fun other => decide (block.label ≠ other.label)) &&
        labelsUnique? rest

def allBlocksTyped? (program : Program) : Bool :=
  program.blocks.all (fun block => (block.type? program).isSome)

def typeCheck? (program : Program) : Option Unit :=
  if labelsUnique? program.blocks &&
      allBlocksTyped? program &&
      (program.findBlock? program.entry).isSome then
    some ()
  else
    none

end Program

structure CheckedProgram where
  program : Program
  checked : program.typeCheck? = some ()
  deriving Repr

namespace Program

def check? (program : Program) : Option CheckedProgram :=
  if h : program.typeCheck? = some () then
    some { program := program, checked := h }
  else
    none

theorem wellTyped_allBlocksTyped {program : Program}
    (h : program.WellTyped) :
    program.AllBlocksTyped :=
  h.2.1

end Program

end TypedCfg
end EvmCompiler
