
axiom df-spthson
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assert |- SPathsOn = ( g e. _V |-> ( a e. ( Vtx ` g ) , b e. ( Vtx ` g ) |-> { <. f , p >. | ( f ( a ( TrailsOn ` g ) b ) p /\ f ( SPaths ` g ) p ) } ) )
end
