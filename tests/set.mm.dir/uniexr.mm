include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "cvv.mm"
include "pwuni.mm"
include "pwexg.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem uniexr
  let cA: class A
  let cV: class V


  assert |- ( U. A e. V -> A e. _V )

  proof
    cA
    cuni
    #
    cV
    wcel
    cA
    @0
    cpw
    #
    wss
    @1
    cvv
    wcel
    cA
    cvv
    wcel
    cA
    pwuni
    @0
    cV
    pwexg
    cA
    @1
    cvv
    ssexg
    sylancr
end
