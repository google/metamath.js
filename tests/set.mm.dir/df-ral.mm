

axiom df-ral
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  assert |- ( A. x e. A ph <-> A. x ( x e. A -> ph ) )
end
