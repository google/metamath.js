
axiom df-cofu
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  assert |- o.func = ( g e. _V , f e. _V |-> <. ( ( 1st ` g ) o. ( 1st ` f ) ) , ( x e. dom dom ( 2nd ` f ) , y e. dom dom ( 2nd ` f ) |-> ( ( ( ( 1st ` f ) ` x ) ( 2nd ` g ) ( ( 1st ` f ) ` y ) ) o. ( x ( 2nd ` f ) y ) ) ) >. )
end
