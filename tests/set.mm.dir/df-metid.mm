
axiom df-metid
  let vx: setvar x
  let vy: setvar y
  let vd: setvar d
  assert |- ~Met = ( d e. U. ran PsMet |-> { <. x , y >. | ( ( x e. dom dom d /\ y e. dom dom d ) /\ ( x d y ) = 0 ) } )
end
