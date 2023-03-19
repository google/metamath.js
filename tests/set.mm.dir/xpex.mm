include "cvv.mm"
include "wcel.mm"
include "cxp.mm"
include "xpexg.mm"
include "mp2an.mm"

theorem xpex
  let cA: class A
  let cB: class B
  assume xpex.1: |- A e. _V
  assume xpex.2: |- B e. _V


  assert |- ( A X. B ) e. _V

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cxp
    cvv
    wcel
    xpex.1
    xpex.2
    cA
    cB
    cvv
    cvv
    xpexg
    mp2an
end
