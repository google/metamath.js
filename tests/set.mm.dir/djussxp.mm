include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cvv.mm"
include "wss.mm"
include "iunss.mm"
include "wcel.mm"
include "snssi.mm"
include "ssv.mm"
include "xpss12.mm"
include "sylancl.mm"
include "mprgbir.mm"

theorem djussxp
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- U_ x e. A ( { x } X. B ) C_ ( A X. _V )

  proof
    vx
    cA
    vx
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    cA
    cvv
    cxp
    #
    wss
    @2
    @3
    wss
    #
    vx
    cA
    vx
    cA
    @2
    @3
    iunss
    @0
    cA
    wcel
    @1
    cA
    wss
    cB
    cvv
    wss
    @4
    @0
    cA
    snssi
    cB
    ssv
    @1
    cA
    cB
    cvv
    xpss12
    sylancl
    mprgbir
end
