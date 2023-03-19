include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cdif.mm"
include "difeq2.mm"
include "difin.mm"
include "dif0.mm"
include "3eqtr3g.mm"

theorem disjdif2
  let cA: class A
  let cB: class B


  assert |- ( ( A i^i B ) = (/) -> ( A \ B ) = A )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    cA
    @0
    cdif
    cA
    c0
    cdif
    cA
    cB
    cdif
    cA
    @0
    c0
    cA
    difeq2
    cA
    cB
    difin
    cA
    dif0
    3eqtr3g
end
