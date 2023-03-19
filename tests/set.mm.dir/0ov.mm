include "c0.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "df-ov.mm"
include "0fv.mm"
include "eqtri.mm"

theorem 0ov
  let cA: class A
  let cB: class B


  assert |- ( A (/) B ) = (/)

  proof
    cA
    cB
    c0
    co
    cA
    cB
    cop
    #
    c0
    cfv
    c0
    cA
    cB
    c0
    df-ov
    @0
    0fv
    eqtri
end
