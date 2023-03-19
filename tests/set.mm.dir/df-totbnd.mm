
axiom df-totbnd
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vm: setvar m
  let vb: setvar b
  let vd: setvar d
  assert |- TotBnd = ( x e. _V |-> { m e. ( Met ` x ) | A. d e. RR+ E. v e. Fin ( U. v = x /\ A. b e. v E. y e. x b = ( y ( ball ` m ) d ) ) } )
end
