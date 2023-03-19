
axiom df-slt
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  assert |- <s = { <. f , g >. | ( ( f e. No /\ g e. No ) /\ E. x e. On ( A. y e. x ( f ` y ) = ( g ` y ) /\ ( f ` x ) { <. 1o , (/) >. , <. 1o , 2o >. , <. (/) , 2o >. } ( g ` x ) ) ) }
end
