module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # The uniform 1D random walk

Specified in `TotalEris/Examples/RandomWalk`, whose docstring explains why
`rand 1` makes this walk degenerate. -/

namespace ProbLang
namespace TotalEris
namespace Examples

variable {rT : Type _}

/-- The recursive body of the 1D random walk: from position `n`, stop once
`n < 1`, otherwise flip `rand 1` and step down or up. -/
def unifRw1dRec : Exp rT :=
  pl% rec f n α :=
        if n < #1 then #.unit
        else
          let x := rand(#1, α);
          if x < #1
            then f (n - #1) α
            else f (n + #1) α

/-- Top-level program: `let α = alloc 1 in unifRw1dRec 1 α`. -/
def unifRw1d : Exp rT :=
  pl% let α := alloc(#1); &unifRw1dRec #1 α

end Examples
end TotalEris
end ProbLang
