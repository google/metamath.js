
axiom df-nv
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vn: setvar n
  let vs: setvar s
  assert |- NrmCVec = { <. <. g , s >. , n >. | ( <. g , s >. e. CVecOLD /\ n : ran g --> RR /\ A. x e. ran g ( ( ( n ` x ) = 0 -> x = ( GId ` g ) ) /\ A. y e. CC ( n ` ( y s x ) ) = ( ( abs ` y ) x. ( n ` x ) ) /\ A. y e. ran g ( n ` ( x g y ) ) <_ ( ( n ` x ) + ( n ` y ) ) ) ) }
end
