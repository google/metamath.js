include "cin.mm"
include "in32.mm"
include "incom.mm"
include "3eqtr4i.mm"

theorem in13
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A i^i ( B i^i C ) ) = ( C i^i ( B i^i A ) )

  proof
    cB
    cC
    cin
    #
    cA
    cin
    cB
    cA
    cin
    #
    cC
    cin
    cA
    @0
    cin
    cC
    @1
    cin
    cB
    cC
    cA
    in32
    cA
    @0
    incom
    cC
    @1
    incom
    3eqtr4i
end
