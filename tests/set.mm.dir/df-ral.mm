
axiom df-ral
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assert |- ( A. x e. A ph <-> A. x ( x e. A -> ph ) )
end
