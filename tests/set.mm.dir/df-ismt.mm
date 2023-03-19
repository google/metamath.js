
axiom df-ismt
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let va: setvar a
  let vb: setvar b
  assert |- Ismt = ( g e. _V , h e. _V |-> { f | ( f : ( Base ` g ) -1-1-onto-> ( Base ` h ) /\ A. a e. ( Base ` g ) A. b e. ( Base ` g ) ( ( f ` a ) ( dist ` h ) ( f ` b ) ) = ( a ( dist ` g ) b ) ) } )
end
