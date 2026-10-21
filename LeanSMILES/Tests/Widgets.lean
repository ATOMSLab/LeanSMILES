import LeanSMILES.MetaPrograms.Show
import LeanSMILES.MetaPrograms.Test

/-! Tests for the widgets: charts, molecule drawings, tables and SVG export. -/

open Widgets MetaPrograms

def fig := histogram #[1.0, 2.0, 2.5, 3.0, 4.0] 4 "test"

#show fig
#show Chem.Exec.molFromSmiles "c1ccccc1O"

#test (toMarkup fig).startsWith "<svg"
#test ((toMarkup fig).splitOn "<rect").length - 1 ≥ 4 + 1
#test ((toMarkup (scatter #[(1.0, 1.0), (2.0, 2.5)])).splitOn "<circle").length - 1 == 2
-- phenol: 7 atoms, one labelled (OH)
#test ((toMarkup (smilesSvg "c1ccccc1O")).splitOn ">OH<").length == 2
#test (toMarkup (smilesSvg "C1CC")).contains "invalid SMILES"
#test svgAttrName "strokeWidth" == "stroke-width" && svgAttrName "viewBox" == "viewBox"
#test niceTicks 0 10 == #[0, 2, 4, 6, 8, 10]
#test ((toMarkup (table #["a", "b"] #[#["1", "2"], #["3", "4"]])).splitOn "<td").length - 1 == 4
