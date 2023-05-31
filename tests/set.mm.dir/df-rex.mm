

axiom df-rex
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  assert |- ( E. x e. A ph <-> E. x ( x e. A /\ ph ) )
end
