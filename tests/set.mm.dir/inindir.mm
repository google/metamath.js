include "cin.mm"
include "inidm.mm"
include "ineq2i.mm"
include "in4.mm"
include "eqtr3i.mm"

theorem inindir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i B ) i^i C ) = ( ( A i^i C ) i^i ( B i^i C ) )

  proof
    cA
    cB
    cin
    #
    cC
    cC
    cin
    #
    cin
    @0
    cC
    cin
    cA
    cC
    cin
    cB
    cC
    cin
    cin
    @1
    cC
    @0
    cC
    inidm
    ineq2i
    cA
    cB
    cC
    cC
    in4
    eqtr3i
end
