
axiom df-clwlks
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assert |- ClWalks = ( g e. _V |-> { <. f , p >. | ( f ( Walks ` g ) p /\ ( p ` 0 ) = ( p ` ( # ` f ) ) ) } )
end
