
axiom df-mon
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vb: setvar b
  let vc: setvar c
  assert |- Mono = ( c e. Cat |-> [_ ( Base ` c ) / b ]_ [_ ( Hom ` c ) / h ]_ ( x e. b , y e. b |-> { f e. ( x h y ) | A. z e. b Fun `' ( g e. ( z h x ) |-> ( f ( <. z , x >. ( comp ` c ) y ) g ) ) } ) )
end
