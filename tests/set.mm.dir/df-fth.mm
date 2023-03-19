
axiom df-fth
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vc: setvar c
  let vd: setvar d
  assert |- Faith = ( c e. Cat , d e. Cat |-> { <. f , g >. | ( f ( c Func d ) g /\ A. x e. ( Base ` c ) A. y e. ( Base ` c ) Fun `' ( x g y ) ) } )
end
