
axiom ax-riotaBAD
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assert |- ( iota_ x e. A ph ) = if ( E! x e. A ph , ( iota x ( x e. A /\ ph ) ) , ( Undef ` { x | x e. A } ) )
end
