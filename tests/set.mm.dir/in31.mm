include "cin.mm"
include "in12.mm"
include "incom.mm"
include "3eqtr4i.mm"

theorem in31
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i B ) i^i C ) = ( ( C i^i B ) i^i A )

  proof
    cC
    cA
    cB
    cin
    #
    cin
    cA
    cC
    cB
    cin
    #
    cin
    @0
    cC
    cin
    @1
    cA
    cin
    cC
    cA
    cB
    in12
    @0
    cC
    incom
    @1
    cA
    incom
    3eqtr4i
end
