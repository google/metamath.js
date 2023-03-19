include "co.mm"
include "cop.mm"
include "cfv.mm"
include "cvv.mm"
include "df-ov.mm"
include "fvex.mm"
include "eqeltri.mm"

theorem ovex
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( A F B ) e. _V

  proof
    cA
    cB
    cF
    co
    cA
    cB
    cop
    #
    cF
    cfv
    cvv
    cA
    cB
    cF
    df-ov
    @0
    cF
    fvex
    eqeltri
end
