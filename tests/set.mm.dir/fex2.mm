include "wf.mm"
include "wcel.mm"
include "w3a.mm"
include "cxp.mm"
include "cvv.mm"
include "xpexg.mm"
include "3adant1.mm"
include "wss.mm"
include "fssxp.mm"
include "3ad2ant1.mm"
include "ssexd.mm"

theorem fex2
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( F : A --> B /\ A e. V /\ B e. W ) -> F e. _V )

  proof
    cA
    cB
    cF
    wf
    #
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    w3a
    cF
    cA
    cB
    cxp
    #
    cvv
    @1
    @2
    @3
    cvv
    wcel
    @0
    cA
    cB
    cV
    cW
    xpexg
    3adant1
    @0
    @1
    cF
    @3
    wss
    @2
    cA
    cB
    cF
    fssxp
    3ad2ant1
    ssexd
end
