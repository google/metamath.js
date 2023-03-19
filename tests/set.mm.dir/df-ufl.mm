
axiom df-ufl
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assert |- UFL = { x | A. f e. ( Fil ` x ) E. g e. ( UFil ` x ) f C_ g }
end
