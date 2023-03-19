
axiom df-submnd
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let vs: setvar s
  assert |- SubMnd = ( s e. Mnd |-> { t e. ~P ( Base ` s ) | ( ( 0g ` s ) e. t /\ A. x e. t A. y e. t ( x ( +g ` s ) y ) e. t ) } )
end
