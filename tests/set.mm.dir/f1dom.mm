include "cvv.mm"
include "wcel.mm"
include "wf1.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "f1domg.mm"
include "ax-mp.mm"

theorem f1dom
  let cA: class A
  let cB: class B
  let cF: class F
  assume f1dom.1: |- B e. _V


  assert |- ( F : A -1-1-> B -> A ~<_ B )

  proof
    cB
    cvv
    wcel
    cA
    cB
    cF
    wf1
    cA
    cB
    cdom
    wbr
    wi
    f1dom.1
    cA
    cB
    cvv
    cF
    f1domg
    ax-mp
end
