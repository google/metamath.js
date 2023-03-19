
axiom df-ofr
  let vx: setvar x
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  assert |- oR R = { <. f , g >. | A. x e. ( dom f i^i dom g ) ( f ` x ) R ( g ` x ) }
end
