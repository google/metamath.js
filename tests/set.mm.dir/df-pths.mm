
axiom df-pths
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assert |- Paths = ( g e. _V |-> { <. f , p >. | ( f ( Trails ` g ) p /\ Fun `' ( p |` ( 1 ..^ ( # ` f ) ) ) /\ ( ( p " { 0 , ( # ` f ) } ) i^i ( p " ( 1 ..^ ( # ` f ) ) ) ) = (/) ) } )
end
