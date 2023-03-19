
axiom df-mulg
  let vx: setvar x
  let vg: setvar g
  let vn: setvar n
  let vs: setvar s
  assert |- .g = ( g e. _V |-> ( n e. ZZ , x e. ( Base ` g ) |-> if ( n = 0 , ( 0g ` g ) , [_ seq 1 ( ( +g ` g ) , ( NN X. { x } ) ) / s ]_ if ( 0 < n , ( s ` n ) , ( ( invg ` g ) ` ( s ` -u n ) ) ) ) ) )
end
