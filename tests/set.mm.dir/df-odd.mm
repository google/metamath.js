
axiom df-odd
  let vz: setvar z
  assert |- Odd = { z e. ZZ | ( ( z + 1 ) / 2 ) e. ZZ }
end
