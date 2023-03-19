
axiom df-ufil
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assert |- UFil = ( g e. _V |-> { f e. ( Fil ` g ) | A. x e. ~P g ( x e. f \/ ( g \ x ) e. f ) } )
end
