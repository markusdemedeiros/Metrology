module

public import MicroCircuit

@[expose] public section

/-- Emit a Graphviz DOT representation of a circuit to stdout. -/
def Circuit.toDot (c : Circuit) (numInputs : Nat) (name : String := "circuit") : String := Id.run do
  let mut lines : Array String := #[]
  lines := lines.push s!"digraph {name} \{"
  lines := lines.push "  overlap=false;"
  lines := lines.push "  node [shape=point, width=0.05, height=0.05];"
  -- Input nodes
  for i in [:numInputs] do
    lines := lines.push s!"  w{i} [color=lightblue];"
  -- Gate nodes
  for g in c do
    let color := match g.prim with
      | .And _ _ => "goldenrod"
      | .Xor _ _ => "green"
      | .Not _   => "red"
      | .Id _    => "red"
      | .Const0  => "gray"
      | .Const1  => "gray"
    lines := lines.push s!"  w{g.id} [color={color}];"
  -- Edges
  for g in c do
    match g.prim with
    | .And wA wB =>
      lines := lines.push s!"  w{wA} -> w{g.id};"
      lines := lines.push s!"  w{wB} -> w{g.id};"
    | .Xor wA wB =>
      lines := lines.push s!"  w{wA} -> w{g.id};"
      lines := lines.push s!"  w{wB} -> w{g.id};"
    | .Not wA =>
      lines := lines.push s!"  w{wA} -> w{g.id};"
    | .Id wA =>
      lines := lines.push s!"  w{wA} -> w{g.id};"
    | .Const0 => pure ()
    | .Const1 => pure ()
  lines := lines.push "}"
  "\n".intercalate lines.toList

def CircuitSpec.toDot (spec : CircuitSpec) (name : String := "circuit") : String := Id.run do
  let base := spec.gates.toDot spec.numInputs name
  -- Highlight outputs: strip closing brace, add output nodes, re-close
  let mut lines := base.splitOn "\n" |>.toArray
  -- Remove last "}"
  if lines.size > 0 then
    lines := lines.pop
  -- Output nodes
  for i in [:spec.outputs.length] do
    let w := spec.outputs[i]!
    lines := lines.push s!"  out{i} [color=purple];"
    lines := lines.push s!"  w{w} -> out{i};"
  lines := lines.push "}"
  "\n".intercalate lines.toList

def main (args : List String) : IO Unit := do
  let some path := args.head? | do
    IO.eprintln "Usage: MicroCircuitViz <output.dot>"
    IO.Process.exit 1
  let spec := buildSpec do
    let mut msgWords : Array (Bundle 32) := #[]
    for _ in [:16] do
      msgWords := msgWords.push (← inputN 32)
    let hashWords ← sha256_block msgWords
    let mut outs : List Wire := []
    for w in hashWords do
      outs := outs ++ w.toList
    return outs
  let dot := spec.toDot "sha256"
  IO.FS.writeFile path dot
  IO.println s!"Wrote {spec.gates.size} gates to {path}"
