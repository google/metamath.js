
axiom df-mgmOLD
  let vt: setvar t
  let vg: setvar g
  assert |- Magma = { g | E. t g : ( t X. t ) --> t }
end
