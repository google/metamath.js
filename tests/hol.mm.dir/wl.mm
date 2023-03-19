

axiom wl
  param hal: type al
  param hbe: type be
  param vx: var x
  param tt: term T
  assume wl.1: |- T : be
  assert |- \ x : al . T : ( al -> be )
end
