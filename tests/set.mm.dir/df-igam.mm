
axiom df-igam
  let vx: setvar x
  assert |- 1/_G = ( x e. CC |-> if ( x e. ( ZZ \ NN ) , 0 , ( 1 / ( _G ` x ) ) ) )
end
