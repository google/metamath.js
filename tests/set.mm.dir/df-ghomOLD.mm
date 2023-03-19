
axiom df-ghomOLD
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  assert |- GrpOpHom = ( g e. GrpOp , h e. GrpOp |-> { f | ( f : ran g --> ran h /\ A. x e. ran g A. y e. ran g ( ( f ` x ) h ( f ` y ) ) = ( f ` ( x g y ) ) ) } )
end
