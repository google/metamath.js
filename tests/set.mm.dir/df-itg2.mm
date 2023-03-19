
axiom df-itg2
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assert |- S.2 = ( f e. ( ( 0 [,] +oo ) ^m RR ) |-> sup ( { x | E. g e. dom S.1 ( g oR <_ f /\ x = ( S.1 ` g ) ) } , RR* , < ) )
end
