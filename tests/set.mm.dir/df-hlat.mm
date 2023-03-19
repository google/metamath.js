
axiom df-hlat
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vl: setvar l
  assert |- HL = { l e. ( ( OML i^i CLat ) i^i CvLat ) | ( A. a e. ( Atoms ` l ) A. b e. ( Atoms ` l ) ( a =/= b -> E. c e. ( Atoms ` l ) ( c =/= a /\ c =/= b /\ c ( le ` l ) ( a ( join ` l ) b ) ) ) /\ E. a e. ( Base ` l ) E. b e. ( Base ` l ) E. c e. ( Base ` l ) ( ( ( 0. ` l ) ( lt ` l ) a /\ a ( lt ` l ) b ) /\ ( b ( lt ` l ) c /\ c ( lt ` l ) ( 1. ` l ) ) ) ) }
end
