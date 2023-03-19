
axiom df-riota
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assert |- ( iota_ x e. A ph ) = ( iota x ( x e. A /\ ph ) )
end
