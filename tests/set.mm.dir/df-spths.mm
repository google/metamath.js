
axiom df-spths
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assert |- SPaths = ( g e. _V |-> { <. f , p >. | ( f ( Trails ` g ) p /\ Fun `' p ) } )
end
