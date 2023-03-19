
axiom df-bj-prcpal
  let vx: setvar x
  assert |- prcpal = ( x e. RR |-> ( ( x mod ( 2 x. _pi ) ) - if ( ( x mod ( 2 x. _pi ) ) <_ _pi , 0 , ( 2 x. _pi ) ) ) )
end
