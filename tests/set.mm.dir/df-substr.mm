
axiom df-substr
  let vx: setvar x
  let vs: setvar s
  let vb: setvar b
  assert |- substr = ( s e. _V , b e. ( ZZ X. ZZ ) |-> if ( ( ( 1st ` b ) ..^ ( 2nd ` b ) ) C_ dom s , ( x e. ( 0 ..^ ( ( 2nd ` b ) - ( 1st ` b ) ) ) |-> ( s ` ( x + ( 1st ` b ) ) ) ) , (/) ) )
end
