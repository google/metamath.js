
axiom df-ismty
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  assert |- Ismty = ( m e. U. ran *Met , n e. U. ran *Met |-> { f | ( f : dom dom m -1-1-onto-> dom dom n /\ A. x e. dom dom m A. y e. dom dom m ( x m y ) = ( ( f ` x ) n ( f ` y ) ) ) } )
end
