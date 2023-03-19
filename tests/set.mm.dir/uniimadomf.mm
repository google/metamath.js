include "cv.mm"
include "cfv.mm"
include "cdom.mm"
include "wbr.mm"
include "wral.mm"
include "wfun.mm"
include "cima.mm"
include "cuni.mm"
include "cxp.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvral.mm"
include "uniimadom.mm"
include "sylan2b.mm"

theorem uniimadomf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z
  assume uniimadomf.1: |- F/_ x F
  assume uniimadomf.2: |- A e. _V
  assume uniimadomf.3: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint x z
  disjoint A z
  disjoint B z
  disjoint F z
  assert |- ( ( Fun F /\ A. x e. A ( F ` x ) ~<_ B ) -> U. ( F " A ) ~<_ ( A X. B ) )

  proof
    vx
    cv
    #
    cF
    cfv
    #
    cB
    cdom
    wbr
    #
    vx
    cA
    wral
    cF
    wfun
    vz
    cv
    #
    cF
    cfv
    #
    cB
    cdom
    wbr
    #
    vz
    cA
    wral
    cF
    cA
    cima
    cuni
    cA
    cB
    cxp
    cdom
    wbr
    @2
    @5
    vx
    vz
    cA
    @2
    vz
    nfv
    vx
    @4
    cB
    cdom
    vx
    @3
    cF
    uniimadomf.1
    vx
    @3
    nfcv
    nffv
    vx
    cdom
    nfcv
    vx
    cB
    nfcv
    nfbr
    vx
    vz
    weq
    @1
    @4
    cB
    cdom
    @0
    @3
    cF
    fveq2
    breq1d
    cbvral
    vz
    cA
    cB
    cF
    uniimadomf.2
    uniimadomf.3
    uniimadom
    sylan2b
end
