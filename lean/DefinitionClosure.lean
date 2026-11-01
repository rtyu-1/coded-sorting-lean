import CodedSorting
import Lean.Elab.Command
import Lean.DeclarationRange

/-! Expand the sorting statement through project definitions. Proof declarations
are recorded as checked lemmas; their proof terms are not executable definitions. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean

private def projectName (n : Name) : Bool :=
  (n.toString.splitOn "CodedSorting").length > 1

private partial def constants (e : Expr) (out : NameSet := {}) : NameSet :=
  match e with
  | .const n _ => out.insert n
  | .app f a => constants a (constants f out)
  | .lam _ t b _ => constants b (constants t out)
  | .forallE _ t b _ => constants b (constants t out)
  | .letE _ t v b _ => constants b (constants v (constants t out))
  | .mdata _ b => constants b out
  | .proj n _ b => constants b (out.insert n)
  | _ => out

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := ``CodedSorting.Sorting.Theorem31.theorem_3_1
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut count := 0
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let info ← getConstInfo name
    let mut dependencies := constants info.type
    let mut kind := "type"
    let mut valueText := ""
    match info with
    | .defnInfo d =>
        kind := "definition"
        dependencies := constants d.value dependencies
        valueText ← liftTermElabM do return (← Lean.Meta.ppExpr d.value).pretty
    | .inductInfo d =>
        kind := "inductive"
        for ctor in d.ctors do dependencies := dependencies.insert ctor
    | .ctorInfo _ => kind := "constructor"
    | .recInfo _ => kind := "recursor"
    | .thmInfo _ =>
        kind := if name == root then "root_theorem" else "checked_lemma"
    | .axiomInfo _ => kind := "axiom"
    | .opaqueInfo _ => kind := "opaque"
    | .quotInfo _ => kind := "quotient"
    let names := dependencies.toList.filter (fun n => n != name)
    let inProject := fun n => match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]!).toString.startsWith "CodedSorting"
      | none => projectName n
    let project := names.filter inProject
    let external := names.filter (fun n => !inProject n)
    pending := project ++ pending
    let sourceModule := match env.getModuleIdxFor? name with
      | some i => (env.header.moduleNames[i.toNat]!).toString
      | none => ""
    let ranges ← findDeclarationRanges? name
    let sourceLine := match ranges with
      | some r => r.range.pos.line
      | none => 0
    let sourceEndLine := match ranges with
      | some r => r.range.endPos.line
      | none => 0
    let typeText ← liftTermElabM do return (← Lean.Meta.ppExpr info.type).pretty
    logInfo m!"CS_DEFINITION {(Json.mkObj [
      ("name",toJson name.toString),("kind",toJson kind),
      ("type",toJson typeText),("value",toJson valueText),
      ("module",toJson sourceModule),("source_line",toJson sourceLine),
      ("source_end_line",toJson sourceEndLine),
      ("project_dependencies",toJson (project.map Name.toString)),
      ("foundation_dependencies",toJson (external.map Name.toString))]).compress}"
    count := count+1
  logInfo m!"CS_DEFINITION_TOTAL {count}"
