
axiom df-alsc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assert |- ( A! x e. A ph <-> ( A. x e. A ph /\ E. x x e. A ) )
end
