
axiom df-perf
  let vj: setvar j
  assert |- Perf = { j e. Top | ( ( limPt ` j ) ` U. j ) = U. j }
end
