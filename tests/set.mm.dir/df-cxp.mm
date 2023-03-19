
axiom df-cxp
  let vx: setvar x
  let vy: setvar y
  assert |- ^c = ( x e. CC , y e. CC |-> if ( x = 0 , if ( y = 0 , 1 , 0 ) , ( exp ` ( y x. ( log ` x ) ) ) ) )
end
