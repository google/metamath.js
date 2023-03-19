
axiom df-itg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  assert |- S. A B _d x = sum_ k e. ( 0 ... 3 ) ( ( _i ^ k ) x. ( S.2 ` ( x e. RR |-> [_ ( Re ` ( B / ( _i ^ k ) ) ) / y ]_ if ( ( x e. A /\ 0 <_ y ) , y , 0 ) ) ) )
end
