include "cdif.mm"
include "cin.mm"
include "dfin4.mm"
include "difeq2i.mm"
include "difin.mm"
include "3eqtr2i.mm"

theorem indif
  let cA: class A
  let cB: class B


  assert |- ( A i^i ( A \ B ) ) = ( A \ B )

  proof
    cA
    cA
    cB
    cdif
    #
    cin
    cA
    cA
    @0
    cdif
    #
    cdif
    cA
    cA
    cB
    cin
    #
    cdif
    @0
    cA
    @0
    dfin4
    @2
    @1
    cA
    cA
    cB
    dfin4
    difeq2i
    cA
    cB
    difin
    3eqtr2i
end
