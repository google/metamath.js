
axiom df-mre
  let vx: setvar x
  let vs: setvar s
  let vc: setvar c
  assert |- Moore = ( x e. _V |-> { c e. ~P ~P x | ( x e. c /\ A. s e. ~P c ( s =/= (/) -> |^| s e. c ) ) } )
end
