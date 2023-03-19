
axiom df-ptdf
  let vx: setvar x
  let cA: class A
  let cB: class B
  assert |- PtDf ( A , B ) = ( x e. RR |-> ( ( ( x .v ( B -r A ) ) +v A ) " { 1 , 2 , 3 } ) )
end
