include "cin.mm"
include "inass.mm"
include "in12.mm"
include "incom.mm"
include "3eqtri.mm"

theorem in32
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i B ) i^i C ) = ( ( A i^i C ) i^i B )

  proof
    cA
    cB
    cin
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
    #
    cin
    @0
    cB
    cin
    cA
    cB
    cC
    inass
    cA
    cB
    cC
    in12
    cB
    @0
    incom
    3eqtri
end
