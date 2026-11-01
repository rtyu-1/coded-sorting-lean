import CodedSorting
import Lean.Util.FoldConsts
import Lean.Elab.Command

/-! Stable elaborated types and selected model definitions. The checked-in
baseline is updated only after an explicit correspondence review. Proof terms
are excluded; constructors of selected structures are included. -/
open CodedSorting Construction Construction.Sorting
open GeneralWordSorting NetworkCodingResult

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``Sorting.Theorem31.theorem_3_1,
    ``NormalGuarantee,
    ``SmallGuarantee,
    ``WordControl.Word,
    ``WordConvention.Covers,
    ``CommonIntegerPhysical.InputFile,
    ``CommonIntegerPhysical.inputWord,
    ``TwoWordBlockFormat.File,
    ``TwoWordBlockFormat.wordAt,
    ``TwoWordBlockFormat.cell,
    ``CommonNormalizationController.Program,
    ``CommonNormalizationController.State,
    ``CommonNormalizationController.step,
    ``CommonNormalizationController.run,
    ``CommonNormalizationController.outputWord,
    ``TwoWordSmallMemorySorting.Stage,
    ``TwoWordSmallMemorySorting.Executes,
    ``TwoWordBlockLift.State,
    ``TwoWordBlockLift.Command,
    ``TwoWordBlockLift.step,
    ``TwoWordBlockLift.cost,
    ``CommonSortingNormalization.ResidentIndex,
    ``CommonNormalizationController.Address,
    ``TwoWordSmallMemoryFootprint.BoundedCode,
    ``GeneralWordSorting.coefficient,
    ``GeneralWordSorting.factor,
    ``GeneralWordNormalSorting.factor,
    ``GeneralWordSorting.smallSpaceBound,
    ``GeneralWordSorting.factor_eq,
    ``GeneralWordSorting.coefficient_positive,
    ``NetworkCoding.Theorem32.theorem_3_2,
    ``network,
    ``source,
    ``sink,
    ``TensorNetwork.Session,
    ``TensorNetwork.OriginalActive,
    ``TensorNetwork.session_count,
    ``physicalEdgeEquiv,
    ``NetworkProtocol.Correct,
    ``NetworkCut.Protocol,
    ``NetworkCut.message,
    ``NetworkCut.step,
    ``NetworkCut.run,
    ``NetworkRates.BlockCode,
    ``BinaryLinearPipeline.BinaryLinearBlock,
    ``NetworkRates.Achievable,
    ``NetworkRates.capacity,
    ``GraphRouting.Walk,
    ``GraphRouting.Walk.edges,
    ``NetworkRates.Routable,
    ``NetworkRates.routingCapacity,
    ``SSAFunctionCertificate.trace_sound,
    ``FiniteProjectionInterpretation.checked_frame_inclusion,
    ``TensorFrameNetwork.actualLabel_endpoint_rank,
    ``TensorFrameNetwork.actualRank_eq_budget,
    ``finite_binary_linear_strict_block]
  let mut pending := targets.toList
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let info ← getConstInfo name
    let pretty ← liftTermElabM do Lean.Meta.ppExpr info.type
    let mut fields := [("name", toJson name.toString),
      ("type", toJson (reprStr info.type)), ("readable_type", toJson pretty.pretty)]
    match info with
    | .defnInfo d => fields := fields ++ [("value", toJson (reprStr d.value))]
    | .inductInfo d => pending := d.ctors ++ pending
    | _ => pure ()
    logInfo m!"CS_MODEL {(Json.mkObj fields).compress}"
