
axiom df-conngr
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  assert |- ConnGraph = { g | [. ( Vtx ` g ) / v ]. A. k e. v A. n e. v E. f E. p f ( k ( PathsOn ` g ) n ) p }
end
