
axiom df-of
  let vx: setvar x
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  assert |- oF R = ( f e. _V , g e. _V |-> ( x e. ( dom f i^i dom g ) |-> ( ( f ` x ) R ( g ` x ) ) ) )
end
