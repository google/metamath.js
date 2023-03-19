
axiom df-ida
  let vx: setvar x
  let vc: setvar c
  assert |- IdA = ( c e. Cat |-> ( x e. ( Base ` c ) |-> <. x , x , ( ( Id ` c ) ` x ) >. ) )
end
