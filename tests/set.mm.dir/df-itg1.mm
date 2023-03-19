
axiom df-itg1
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assert |- S.1 = ( f e. { g e. MblFn | ( g : RR --> RR /\ ran g e. Fin /\ ( vol ` ( `' g " ( RR \ { 0 } ) ) ) e. RR ) } |-> sum_ x e. ( ran f \ { 0 } ) ( x x. ( vol ` ( `' f " { x } ) ) ) )
end
