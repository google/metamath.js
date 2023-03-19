
axiom df-hlg
  let vg: setvar g
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assert |- hlG = ( g e. _V |-> ( c e. ( Base ` g ) |-> { <. a , b >. | ( ( a e. ( Base ` g ) /\ b e. ( Base ` g ) ) /\ ( a =/= c /\ b =/= c /\ ( a e. ( c ( Itv ` g ) b ) \/ b e. ( c ( Itv ` g ) a ) ) ) ) } ) )
end
