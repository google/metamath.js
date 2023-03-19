
axiom df-xmet
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vd: setvar d
  assert |- *Met = ( x e. _V |-> { d e. ( RR* ^m ( x X. x ) ) | A. y e. x A. z e. x ( ( ( y d z ) = 0 <-> y = z ) /\ A. w e. x ( y d z ) <_ ( ( w d y ) +e ( w d z ) ) ) } )
end
