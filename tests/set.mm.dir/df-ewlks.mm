
axiom df-ewlks
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vk: setvar k
  let vs: setvar s
  assert |- EdgWalks = ( g e. _V , s e. NN0* |-> { f | [. ( iEdg ` g ) / i ]. ( f e. Word dom i /\ A. k e. ( 1 ..^ ( # ` f ) ) s <_ ( # ` ( ( i ` ( f ` ( k - 1 ) ) ) i^i ( i ` ( f ` k ) ) ) ) ) } )
end
