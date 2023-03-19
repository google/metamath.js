
axiom df-xps
  let vx: setvar x
  let vy: setvar y
  let vs: setvar s
  let vr: setvar r
  assert |- Xs. = ( r e. _V , s e. _V |-> ( `' ( x e. ( Base ` r ) , y e. ( Base ` s ) |-> `' ( { x } +c { y } ) ) "s ( ( Scalar ` r ) Xs_ `' ( { r } +c { s } ) ) ) )
end
