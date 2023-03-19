
axiom df-cycls
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assert |- Cycles = ( g e. _V |-> { <. f , p >. | ( f ( Paths ` g ) p /\ ( p ` 0 ) = ( p ` ( # ` f ) ) ) } )
end
