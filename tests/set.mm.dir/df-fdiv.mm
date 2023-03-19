
axiom df-fdiv
  let vf: setvar f
  let vg: setvar g
  assert |- /_f = ( f e. _V , g e. _V |-> ( ( f oF / g ) |` ( g supp 0 ) ) )
end
