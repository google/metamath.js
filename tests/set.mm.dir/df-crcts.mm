
axiom df-crcts
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assert |- Circuits = ( g e. _V |-> { <. f , p >. | ( f ( Trails ` g ) p /\ ( p ` 0 ) = ( p ` ( # ` f ) ) ) } )
end
