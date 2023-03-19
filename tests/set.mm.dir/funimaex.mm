include "wfun.mm"
include "cvv.mm"
include "wcel.mm"
include "cima.mm"
include "funimaexg.mm"
include "mpan2.mm"

theorem funimaex
  let cA: class A
  let cB: class B
  assume zfrep5.1: |- B e. _V


  assert |- ( Fun A -> ( A " B ) e. _V )

  proof
    cA
    wfun
    cB
    cvv
    wcel
    cA
    cB
    cima
    cvv
    wcel
    zfrep5.1
    cA
    cB
    cvv
    funimaexg
    mpan2
end
