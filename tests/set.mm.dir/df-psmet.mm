
axiom df-psmet
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vd: setvar d
  assert |- PsMet = ( x e. _V |-> { d e. ( RR* ^m ( x X. x ) ) | A. y e. x ( ( y d y ) = 0 /\ A. z e. x A. w e. x ( y d z ) <_ ( ( w d y ) +e ( w d z ) ) ) } )
end
