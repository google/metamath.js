

axiom wctl
  param ts: term S
  param tt: term T
  assume wctl.1: |- ( S , T ) : bool
  assert |- S : bool
end
