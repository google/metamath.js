
axiom df-pco
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  assert |- *p = ( j e. Top |-> ( f e. ( II Cn j ) , g e. ( II Cn j ) |-> ( x e. ( 0 [,] 1 ) |-> if ( x <_ ( 1 / 2 ) , ( f ` ( 2 x. x ) ) , ( g ` ( ( 2 x. x ) - 1 ) ) ) ) ) )
end
