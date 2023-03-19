
axiom df-qqh
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  assert |- QQHom = ( r e. _V |-> ran ( x e. ZZ , y e. ( `' ( ZRHom ` r ) " ( Unit ` r ) ) |-> <. ( x / y ) , ( ( ( ZRHom ` r ) ` x ) ( /r ` r ) ( ( ZRHom ` r ) ` y ) ) >. ) )
end
