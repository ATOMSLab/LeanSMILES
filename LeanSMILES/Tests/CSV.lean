import LeanSMILES.API.CSV
import LeanSMILES.MetaPrograms.Test

/-! Tests for `CSV.parse` and the column helpers. -/

open API

def csv! (s : String) : CSV := (CSV.parse s).toOption.getD default

def text :=
  "name,value,smiles\n\"2,2'-PCB\",1.5,c1ccccc1\nplain,\"-2\",CCO \r\n\"say \"\"hi\"\"\",,C\n"

#test (csv! text).header == #["name", "value", "smiles"]
#test (csv! text).rows.size == 3
-- quoted field with a comma
#test ((csv! text).rows[0]!)[0]! == "2,2'-PCB"
-- `""` inside quotes is an escaped quote; `\r\n` is a line ending
#test ((csv! text).rows[2]!)[0]! == "say \"hi\""
#test ((csv! text).rows[1]!)[2]! == "CCO "
#test ((csv! text).column "value").toOption == some #["1.5", "-2", ""]
#test (csv! text).missingCounts == #[("name", 0), ("value", 1), ("smiles", 0)]
#test ((csv! text).columnIndex "nope").toOption == none
-- no trailing newline, blank lines ignored
#test (csv! "a,b\n1,2\n\n3,4").rows == #[#["1", "2"], #["3", "4"]]
-- ragged rows are rejected
#test (CSV.parse "a,b\n1,2,3\n").toOption.isNone
#test (CSV.parse "").toOption.isNone
