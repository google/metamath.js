include "cpw.mm"
include "wcel.mm"
include "cuni.mm"
include "cvv.mm"
include "unipw.mm"
include "uniexg.mm"
include "syl5eqelr.mm"

theorem pwexr
  let cA: class A
  let cV: class V


  assert |- ( ~P A e. V -> A e. _V )

  proof
    cA
    cpw
    #
    cV
    wcel
    cA
    @0
    cuni
    cvv
    cA
    unipw
    @0
    cV
    uniexg
    syl5eqelr
end
