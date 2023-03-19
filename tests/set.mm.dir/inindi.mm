include "cin.mm"
include "inidm.mm"
include "ineq1i.mm"
include "in4.mm"
include "eqtr3i.mm"

theorem inindi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A i^i ( B i^i C ) ) = ( ( A i^i B ) i^i ( A i^i C ) )

  proof
    cA
    cA
    cin
    #
    cB
    cC
    cin
    #
    cin
    cA
    @1
    cin
    cA
    cB
    cin
    cA
    cC
    cin
    cin
    @0
    cA
    @1
    cA
    inidm
    ineq1i
    cA
    cA
    cB
    cC
    in4
    eqtr3i
end
