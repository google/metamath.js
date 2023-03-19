
axiom df-lmi
  let vg: setvar g
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  assert |- lInvG = ( g e. _V |-> ( m e. ran ( LineG ` g ) |-> ( a e. ( Base ` g ) |-> ( iota_ b e. ( Base ` g ) ( ( a ( midG ` g ) b ) e. m /\ ( m ( perpG ` g ) ( a ( LineG ` g ) b ) \/ a = b ) ) ) ) ) )
end
