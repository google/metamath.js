
axiom df-wlkson
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assert |- WalksOn = ( g e. _V |-> ( a e. ( Vtx ` g ) , b e. ( Vtx ` g ) |-> { <. f , p >. | ( f ( Walks ` g ) p /\ ( p ` 0 ) = a /\ ( p ` ( # ` f ) ) = b ) } ) )
end
