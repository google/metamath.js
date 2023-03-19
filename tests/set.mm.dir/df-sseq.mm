
axiom df-sseq
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vm: setvar m
  assert |- seqstr = ( m e. _V , f e. _V |-> ( m u. ( lastS o. seq ( # ` m ) ( ( x e. _V , y e. _V |-> ( x ++ <" ( f ` x ) "> ) ) , ( NN0 X. { ( m ++ <" ( f ` m ) "> ) } ) ) ) ) )
end
