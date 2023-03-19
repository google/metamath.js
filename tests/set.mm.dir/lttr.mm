include "axlttrn.mm"

theorem lttr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A < B /\ B < C ) -> A < C ) )

  proof
    cA
    cB
    cC
    axlttrn
end
