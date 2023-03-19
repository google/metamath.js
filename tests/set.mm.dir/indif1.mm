include "cdif.mm"
include "cin.mm"
include "indif2.mm"
include "incom.mm"
include "difeq1i.mm"
include "3eqtr3i.mm"

theorem indif1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A \ C ) i^i B ) = ( ( A i^i B ) \ C )

  proof
    cB
    cA
    cC
    cdif
    #
    cin
    cB
    cA
    cin
    #
    cC
    cdif
    @0
    cB
    cin
    cA
    cB
    cin
    #
    cC
    cdif
    cB
    cA
    cC
    indif2
    cB
    @0
    incom
    @1
    @2
    cC
    cB
    cA
    incom
    difeq1i
    3eqtr3i
end
