
axiom df-pcmp
  let vj: setvar j
  assert |- Paracomp = { j | j e. CovHasRef ( LocFin ` j ) }
end
