
axiom df-reverse
  let vx: setvar x
  let vs: setvar s
  assert |- reverse = ( s e. _V |-> ( x e. ( 0 ..^ ( # ` s ) ) |-> ( s ` ( ( ( # ` s ) - 1 ) - x ) ) ) )
end
