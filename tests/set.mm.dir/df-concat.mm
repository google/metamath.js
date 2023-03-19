
axiom df-concat
  let vx: setvar x
  let vt: setvar t
  let vs: setvar s
  assert |- ++ = ( s e. _V , t e. _V |-> ( x e. ( 0 ..^ ( ( # ` s ) + ( # ` t ) ) ) |-> if ( x e. ( 0 ..^ ( # ` s ) ) , ( s ` x ) , ( t ` ( x - ( # ` s ) ) ) ) ) )
end
