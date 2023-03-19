
axiom df-cnrm
  let vx: setvar x
  let vj: setvar j
  assert |- CNrm = { j e. Top | A. x e. ~P U. j ( j |`t x ) e. Nrm }
end
