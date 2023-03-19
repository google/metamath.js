
axiom df-bj-rnf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assert |- ( F/ x e. A ph <-> ( E. x e. A ph -> A. x e. A ph ) )
end
