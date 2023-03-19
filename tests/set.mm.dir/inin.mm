include "cin.mm"
include "in13.mm"
include "inidm.mm"
include "ineq2i.mm"
include "incom.mm"
include "3eqtri.mm"

theorem inin
  let cA: class A
  let cB: class B


  assert |- ( A i^i ( A i^i B ) ) = ( A i^i B )

  proof
    cA
    cA
    cB
    cin
    #
    cin
    cB
    cA
    cA
    cin
    #
    cin
    cB
    cA
    cin
    @0
    cA
    cA
    cB
    in13
    @1
    cA
    cB
    cA
    inidm
    ineq2i
    cB
    cA
    incom
    3eqtri
end
