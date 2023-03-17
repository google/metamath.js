

axiom wctl
  let ts: term S
  let tt: term T
  assume wctl.1: |- ( S , T ) : bool
  assert |- S : bool
end
