
axiom df-rusgr
  let vg: setvar g
  let vk: setvar k
  assert |- RegUSGraph = { <. g , k >. | ( g e. USGraph /\ g RegGraph k ) }
end
