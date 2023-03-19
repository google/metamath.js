
axiom df-eupth
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assert |- EulerPaths = ( g e. _V |-> { <. f , p >. | ( f ( Trails ` g ) p /\ f : ( 0 ..^ ( # ` f ) ) -onto-> dom ( iEdg ` g ) ) } )
end
