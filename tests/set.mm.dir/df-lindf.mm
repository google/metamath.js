
axiom df-lindf
  let vx: setvar x
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  let vs: setvar s
  assert |- LIndF = { <. f , w >. | ( f : dom f --> ( Base ` w ) /\ [. ( Scalar ` w ) / s ]. A. x e. dom f A. k e. ( ( Base ` s ) \ { ( 0g ` s ) } ) -. ( k ( .s ` w ) ( f ` x ) ) e. ( ( LSpan ` w ) ` ( f " ( dom f \ { x } ) ) ) ) }
end
