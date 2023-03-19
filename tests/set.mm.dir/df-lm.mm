
axiom df-lm
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vf: setvar f
  let vj: setvar j
  assert |- ~~>t = ( j e. Top |-> { <. f , x >. | ( f e. ( U. j ^pm CC ) /\ x e. U. j /\ A. u e. j ( x e. u -> E. y e. ran ZZ>= ( f |` y ) : y --> u ) ) } )
end
