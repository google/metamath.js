include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfilu.mm"
include "w3a.mm"
include "cv.mm"
include "cxp.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cfbas.mm"
include "iscfilu.mm"
include "simplbda.mm"
include "3adant3.mm"
include "wi.mm"
include "wceq.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "3ad2ant3.mm"
include "mpd.mm"

theorem cfiluexsm
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let va: setvar a
  let vv: setvar v

  disjoint F a
  disjoint V a
  disjoint a v
  disjoint F v
  disjoint V v
  disjoint U v
  assert |- ( ( U e. ( UnifOn ` X ) /\ F e. ( CauFilU ` U ) /\ V e. U ) -> E. a e. F ( a X. a ) C_ V )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cF
    cU
    ccfilu
    cfv
    wcel
    #
    cV
    cU
    wcel
    #
    w3a
    va
    cv
    #
    @3
    cxp
    #
    vv
    cv
    #
    wss
    #
    va
    cF
    wrex
    #
    vv
    cU
    wral
    #
    @4
    cV
    wss
    #
    va
    cF
    wrex
    #
    @0
    @1
    @8
    @2
    @0
    @1
    cF
    cX
    cfbas
    cfv
    wcel
    @8
    vv
    cU
    cF
    cX
    va
    iscfilu
    simplbda
    3adant3
    @2
    @0
    @8
    @10
    wi
    @1
    @7
    @10
    vv
    cV
    cU
    @5
    cV
    wceq
    @6
    @9
    va
    cF
    @5
    cV
    @4
    sseq2
    rexbidv
    rspcv
    3ad2ant3
    mpd
end
