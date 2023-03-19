
axiom df-bdop
  let vt: setvar t
  assert |- BndLinOp = { t e. LinOp | ( normop ` t ) < +oo }
end
