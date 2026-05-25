import EvmCompiler.TypedCfg.Syntax

namespace EvmCompiler
namespace TypedCfg

namespace Instr

def type? (instr : Instr) (shape : Shape) : Option Shape :=
  match instr with
  | .push value => some (.literal value :: shape)
  | .prim op =>
      match op.continuingStep? with
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
      match shape[depth]? with
      | some slot => some (slot :: shape)
      | none => none
  | .swap depth =>
      match shape, shape[depth]? with
      | top :: rest, some slot =>
          some (slot :: (rest.set (depth - 1) top))
      | _, none => none
      | [], _ => none
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
      | .word :: rest =>
          if rest = targetShape ∧ rest = fallthroughShape then some () else none
      | _ => none
  | .returnDispatch siteShape =>
      if shape = siteShape then some () else none
  | .halt _ => some ()
  | .invalid => some ()

end Terminator

namespace Block

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

theorem wellTyped_allBlocksTyped {program : Program}
    (h : program.WellTyped) :
    program.AllBlocksTyped :=
  h.2.1

end Program

end TypedCfg
end EvmCompiler
