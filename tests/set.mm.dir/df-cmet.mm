
axiom df-cmet
  let vx: setvar x
  let vf: setvar f
  let vd: setvar d
  assert |- CMet = ( x e. _V |-> { d e. ( Met ` x ) | A. f e. ( CauFil ` d ) ( ( MetOpen ` d ) fLim f ) =/= (/) } )
end
