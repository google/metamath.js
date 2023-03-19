
axiom wct
  param ts: term S
  param tt: term T
  assume wct.1: |- S : bool
  assume wct.2: |- T : bool
  assert |- ( S , T ) : bool
end
