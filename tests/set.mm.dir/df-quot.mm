
axiom df-quot
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vq: setvar q
  assert |- quot = ( f e. ( Poly ` CC ) , g e. ( ( Poly ` CC ) \ { 0p } ) |-> ( iota_ q e. ( Poly ` CC ) [. ( f oF - ( g oF x. q ) ) / r ]. ( r = 0p \/ ( deg ` r ) < ( deg ` g ) ) ) )
end
