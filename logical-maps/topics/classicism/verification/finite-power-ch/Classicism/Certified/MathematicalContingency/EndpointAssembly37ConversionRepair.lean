import Classicism.Certified.MathematicalContingency.EndpointAssembly37Segment12

/- Recompose saved conversion bridges directly, without regenerating the endpoint.
Every declaration is checked by the Lean kernel and the existing pure-axiom audit. -/
open Lean Meta Elab
set_option maxHeartbeats 0
set_option maxRecDepth 20000
run_cmd Lean.Elab.Command.liftTermElabM do
  let cachePrefix := `Classicism.MathematicalContingency.FinitePower.negative_possible_not_cardinalCH.conversionCache
  let bridge := Name.num cachePrefix 4265374060
  let left := Name.num cachePrefix 1984103607
  let bi ← getConstInfo bridge
  let ba := bi.type.getAppArgs
  unless bi.type.getAppFn.isConstOf ``Classicism.Meta.Conv && ba.size == 5 do
    throwError "Expected closed conversion bridge"
  let symmType := mkAppN (mkConst ``Classicism.Meta.Conv) #[ba[0]!, ba[1]!, ba[2]!, ba[4]!, ba[3]!]
  let symmName := Name.num cachePrefix (hash symmType).toNat
  unless symmName == Name.num cachePrefix 4243062644 do
    throwError "Unexpected symmetry type hash: {symmName}"
  let symmValue := mkAppN (mkConst ``Classicism.Meta.Conv.symm) (ba.push (mkConst bridge))
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl {name := symmName, levelParams := [], type := symmType, value := symmValue})
  Classicism.Meta.ConversionCache.requirePure symmName
  logInfo m!"'{symmName}' depends on axioms: {← collectAxioms symmName}"
  let li ← getConstInfo left
  let la := li.type.getAppArgs
  unless li.type.getAppFn.isConstOf ``Classicism.Meta.Conv && la.size == 5 do
    throwError "Expected closed left conversion"
  let finalType := mkAppN (mkConst ``Classicism.Meta.Conv) #[la[0]!, la[1]!, la[2]!, la[3]!, ba[3]!]
  let finalName := Name.num cachePrefix (hash finalType).toNat
  unless finalName == Name.num cachePrefix 931400403 do
    throwError "Unexpected final conversion type hash: {finalName}"
  let finalValue := mkAppN (mkConst ``Classicism.Meta.Conv.trans) #[la[0]!,la[1]!,la[2]!,la[3]!,la[4]!,ba[3]!,mkConst left,mkConst symmName]
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl {name := finalName, levelParams := [], type := finalType, value := finalValue})
  Classicism.Meta.ConversionCache.requirePure finalName
  logInfo m!"'{finalName}' depends on axioms: {← collectAxioms finalName}"
  logInfo "formerly blocked conversion931400403 repaired and kernel checked"
