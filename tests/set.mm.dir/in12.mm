include "cin.mm"
include "incom.mm"
include "ineq1i.mm"
include "inass.mm"
include "3eqtr3i.mm"

theorem in12
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A i^i ( B i^i C ) ) = ( B i^i ( A i^i C ) )

  proof
    cA
    cB
    cin
    #
    cC
    cin
    cB
    cA
    cin
    #
    cC
    cin
    cA
    cB
    cC
    cin
    cin
    cB
    cA
    cC
    cin
    cin
    @0
    @1
    cC
    cA
    cB
    incom
    ineq1i
    cA
    cB
    cC
    inass
    cB
    cA
    cC
    inass
    3eqtr3i
end
