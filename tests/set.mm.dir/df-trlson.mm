
axiom df-trlson
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assert |- TrailsOn = ( g e. _V |-> ( a e. ( Vtx ` g ) , b e. ( Vtx ` g ) |-> { <. f , p >. | ( f ( a ( WalksOn ` g ) b ) p /\ f ( Trails ` g ) p ) } ) )
end
