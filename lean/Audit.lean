import CodedSorting
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let targets : Array (Name × Name) := #[
    (``CodedSorting.Sorting.Theorem31.theorem_3_1,
      ``CodedSorting.Construction.Sorting.GeneralWordSorting.complete),
    (``CodedSorting.NetworkCoding.Theorem32.theorem_3_2,
      ``CodedSorting.Construction.NetworkCodingResult.network_coding_result)]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, implementation) in targets do
    let publicInfo ← getConstInfo name
    let implementationInfo ← getConstInfo implementation
    unless publicInfo.type == implementationInfo.type do
      throwError "public statement differs from its implementation: {name}"
    logInfo m!"CS_STATEMENT {(Json.mkObj [
      ("theorem", toJson name.toString),
      ("implementation", toJson implementation.toString),
      ("exact_type_equal", toJson true)]).compress}"
    let axioms ← collectAxioms name
    let forbidden := axioms.filter (fun a => !allowed.contains a)
    unless forbidden.isEmpty do
      throwError "unexpected axioms for {name}: {forbidden.toList}"
    logInfo m!"CS_ENDPOINT {(Json.mkObj [
      ("theorem", toJson name.toString),
      ("axioms", toJson (axioms.toList.map Name.toString))]).compress}"

open Lean Elab Command in
run_cmd do
  let name := ``CodedSorting.Construction.NetworkCodingResult.paper_finite_block
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms name
  unless (axioms.filter (fun a => !allowed.contains a)).isEmpty do
    throwError "unexpected axioms for Appendix B.2: {axioms.toList}"
  logInfo m!"CS_AUXILIARY {(Json.mkObj [
    ("theorem", toJson name.toString),
    ("axioms", toJson (axioms.toList.map Name.toString))]).compress}"
