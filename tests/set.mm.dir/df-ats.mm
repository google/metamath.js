
axiom df-ats
  let vp: setvar p
  let va: setvar a
  assert |- Atoms = ( p e. _V |-> { a e. ( Base ` p ) | ( 0. ` p ) ( <o ` p ) a } )
end
