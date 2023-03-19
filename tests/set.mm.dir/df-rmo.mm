
axiom df-rmo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assert |- ( E* x e. A ph <-> E* x ( x e. A /\ ph ) )
end
