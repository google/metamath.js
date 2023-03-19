
axiom df-plig
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vl: setvar l
  assert |- Plig = { x | ( A. a e. U. x A. b e. U. x ( a =/= b -> E! l e. x ( a e. l /\ b e. l ) ) /\ A. l e. x E. a e. U. x E. b e. U. x ( a =/= b /\ a e. l /\ b e. l ) /\ E. a e. U. x E. b e. U. x E. c e. U. x A. l e. x -. ( a e. l /\ b e. l /\ c e. l ) ) }
end
