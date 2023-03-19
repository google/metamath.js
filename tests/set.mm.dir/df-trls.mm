
axiom df-trls
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assert |- Trails = ( g e. _V |-> { <. f , p >. | ( f ( Walks ` g ) p /\ Fun `' f ) } )
end
