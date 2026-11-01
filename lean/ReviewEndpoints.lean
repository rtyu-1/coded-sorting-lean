import CodedSorting

/-! Main theorem statements and the definitions used to express them.
`scripts/verify.py` groups this Lean output into English and Chinese
references covering inputs, execution, resources, communication, and rates.
The markers identify the sections used by the report generator. -/
open CodedSorting Construction Construction.Sorting
open GeneralWordSorting NetworkCodingResult

#eval IO.println "CS_REVIEW sorting.statement"
#check Sorting.Theorem31.theorem_3_1

#eval IO.println "CS_REVIEW sorting.guarantees"
#print NormalGuarantee
#print SmallGuarantee

#eval IO.println "CS_REVIEW sorting.inputs"
#print WordControl.Word
#print WordConvention.Covers
#print CommonIntegerPhysical.InputFile
#print CommonIntegerPhysical.inputWord
#print TwoWordBlockFormat.File
#print TwoWordBlockFormat.wordAt
#print TwoWordBlockFormat.cell

#eval IO.println "CS_REVIEW sorting.execution"
#print CommonNormalizationController.Program
#print CommonNormalizationController.State
#print CommonNormalizationController.step
#print CommonNormalizationController.run
#print CommonNormalizationController.outputWord
#print TwoWordSmallMemorySorting.Stage
#print TwoWordSmallMemorySorting.Executes
#print TwoWordBlockLift.State
#print TwoWordBlockLift.Command
#print TwoWordBlockLift.step
#print TwoWordBlockLift.cost

#eval IO.println "CS_REVIEW sorting.resources"
#print CommonSortingNormalization.ResidentIndex
#print CommonNormalizationController.Address
#print TwoWordSmallMemoryFootprint.BoundedCode
#print GeneralWordSorting.coefficient
#print GeneralWordSorting.factor
#print GeneralWordNormalSorting.factor
#print GeneralWordSorting.smallSpaceBound
#check GeneralWordSorting.factor_eq
#check GeneralWordSorting.coefficient_positive

#eval IO.println "CS_REVIEW network.statement"
#check NetworkCoding.Theorem32.theorem_3_2

#eval IO.println "CS_REVIEW network.sessions"
#print network
#print source
#print sink
#print TensorNetwork.Session
#print TensorNetwork.OriginalActive
#check TensorNetwork.session_count
#check physicalEdgeEquiv

#eval IO.println "CS_REVIEW network.protocol"
#print NetworkProtocol.Correct
#print NetworkCut.Protocol
#print NetworkCut.message
#print NetworkCut.step
#print NetworkCut.run
#print NetworkRates.BlockCode
#print BinaryLinearPipeline.BinaryLinearBlock

#eval IO.println "CS_REVIEW network.rates"
#print NetworkRates.Achievable
#print NetworkRates.capacity
#print GraphRouting.Walk
#print GraphRouting.Walk.edges
#print NetworkRates.Routable
#print NetworkRates.routingCapacity

#eval IO.println "CS_REVIEW bridges"
#check SSAFunctionCertificate.trace_sound
#check FiniteProjectionInterpretation.checked_frame_inclusion
#check TensorFrameNetwork.actualLabel_endpoint_rank
#check TensorFrameNetwork.actualRank_eq_budget
#check finite_binary_linear_strict_block
#check paperPackets_eq_integer
#check paper_finite_block

#eval IO.println "CS_REVIEW axioms"
#print axioms Sorting.Theorem31.theorem_3_1
#print axioms NetworkCoding.Theorem32.theorem_3_2
