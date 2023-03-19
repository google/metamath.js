
axiom df-ex
  let hal: type al
  let vx: var x
  let vp: var p
  let vq: var q
  assert |- T. |= [ ? = \ p : ( al -> bool ) . ( ! \ q : bool . [ ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) ==> q : bool ] ) ==> q : bool ] ) ]
end
