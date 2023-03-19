include "cin.mm"
include "cdif.mm"
include "incom.mm"
include "difeq1i.mm"
include "indif2.mm"
include "3eqtr4i.mm"

theorem indifcom
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A i^i ( B \ C ) ) = ( B i^i ( A \ C ) )

  proof
    cA
    cB
    cin
    #
    cC
    cdif
    cB
    cA
    cin
    #
    cC
    cdif
    cA
    cB
    cC
    cdif
    cin
    cB
    cA
    cC
    cdif
    cin
    @0
    @1
    cC
    cA
    cB
    incom
    difeq1i
    cA
    cB
    cC
    indif2
    cB
    cA
    cC
    indif2
    3eqtr4i
end
