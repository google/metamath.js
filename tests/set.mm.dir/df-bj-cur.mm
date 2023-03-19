
axiom df-bj-cur
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  assert |- curry_ = ( x e. _V , y e. _V , z e. _V |-> ( f e. ( ( x X. y ) -Set-> z ) |-> ( a e. x |-> ( b e. y |-> ( f ` <. a , b >. ) ) ) ) )
end
