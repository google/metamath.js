
axiom wctr
  let ts: term S
  let tt: term T
  assume wctl.1: |- ( S , T ) : bool
  assert |- T : bool
end
