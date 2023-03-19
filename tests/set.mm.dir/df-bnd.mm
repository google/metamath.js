
axiom df-bnd
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vr: setvar r
  assert |- Bnd = ( x e. _V |-> { m e. ( Met ` x ) | A. y e. x E. r e. RR+ x = ( y ( ball ` m ) r ) } )
end
