
axiom wl
  let hal: type al
  let hbe: type be
  let vx: var x
  let tt: term T
  assume wl.1: |- T : be
  assert |- \ x : al . T : ( al -> be )
end
