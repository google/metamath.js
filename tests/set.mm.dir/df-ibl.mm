
axiom df-ibl
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vk: setvar k
  assert |- L^1 = { f e. MblFn | A. k e. ( 0 ... 3 ) ( S.2 ` ( x e. RR |-> [_ ( Re ` ( ( f ` x ) / ( _i ^ k ) ) ) / y ]_ if ( ( x e. dom f /\ 0 <_ y ) , y , 0 ) ) ) e. RR }
end
