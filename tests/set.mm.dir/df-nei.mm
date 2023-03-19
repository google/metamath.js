
axiom df-nei
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vj: setvar j
  assert |- nei = ( j e. Top |-> ( x e. ~P U. j |-> { y e. ~P U. j | E. g e. j ( x C_ g /\ g C_ y ) } ) )
end
