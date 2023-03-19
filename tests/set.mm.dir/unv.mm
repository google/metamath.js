include "cvv.mm"
include "cun.mm"
include "ssv.mm"
include "ssun2.mm"
include "eqssi.mm"

theorem unv
  let cA: class A


  assert |- ( A u. _V ) = _V

  proof
    cA
    cvv
    cun
    #
    cvv
    @0
    ssv
    cvv
    cA
    ssun2
    eqssi
end
