
axiom df-irred
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vb: setvar b
  assert |- Irred = ( w e. _V |-> [_ ( ( Base ` w ) \ ( Unit ` w ) ) / b ]_ { z e. b | A. x e. b A. y e. b ( x ( .r ` w ) y ) =/= z } )
end
