
axiom df-bj-finsum
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  assert |- FinSum = ( x e. { <. y , z >. | ( y e. CMnd /\ E. t e. Fin z : t --> ( Base ` y ) ) } |-> ( iota s E. m e. NN0 E. f ( f : ( 1 ... m ) -1-1-onto-> dom ( 2nd ` x ) /\ s = ( seq 1 ( ( +g ` ( 1st ` x ) ) , ( n e. NN |-> ( ( 2nd ` x ) ` ( f ` n ) ) ) ) ` m ) ) ) )
end
