
axiom df-fusgr
  let vg: setvar g
  assert |- FinUSGraph = { g e. USGraph | ( Vtx ` g ) e. Fin }
end
