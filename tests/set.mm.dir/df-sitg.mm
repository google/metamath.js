
axiom df-sitg
  let vx: setvar x
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  assert |- sitg = ( w e. _V , m e. U. ran measures |-> ( f e. { g e. ( dom m MblFnM ( sigaGen ` ( TopOpen ` w ) ) ) | ( ran g e. Fin /\ A. x e. ( ran g \ { ( 0g ` w ) } ) ( m ` ( `' g " { x } ) ) e. ( 0 [,) +oo ) ) } |-> ( w gsum ( x e. ( ran f \ { ( 0g ` w ) } ) |-> ( ( ( RRHom ` ( Scalar ` w ) ) ` ( m ` ( `' f " { x } ) ) ) ( .s ` w ) x ) ) ) ) )
end
