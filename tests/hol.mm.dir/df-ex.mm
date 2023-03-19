
axiom df-ex
  param hal: type al
  param vx: var x
  param vp: var p
  param vq: var q
  assert |- T. |= [ ? = \ p : ( al -> bool ) . ( ! \ q : bool . [ ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) ==> q : bool ] ) ==> q : bool ] ) ]
end
