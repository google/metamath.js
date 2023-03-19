

axiom wctr
  param ts: term S
  param tt: term T
  assume wctl.1: |- ( S , T ) : bool
  assert |- T : bool
end
