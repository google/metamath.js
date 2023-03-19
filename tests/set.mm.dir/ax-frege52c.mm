
axiom ax-frege52c
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assert |- ( A = B -> ( [. A / x ]. ph -> [. B / x ]. ph ) )
end
