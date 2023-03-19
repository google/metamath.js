include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfilu.mm"
include "cfbas.mm"
include "cv.mm"
include "cxp.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "iscfilu.mm"
include "simprbda.mm"

theorem cfilufbas
  let cU: class U
  let cF: class F
  let cX: class X
  let va: setvar a
  let vv: setvar v


  assert |- ( ( U e. ( UnifOn ` X ) /\ F e. ( CauFilU ` U ) ) -> F e. ( fBas ` X ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    cF
    cU
    ccfilu
    cfv
    wcel
    cF
    cX
    cfbas
    cfv
    wcel
    va
    cv
    #
    @0
    cxp
    vv
    cv
    wss
    va
    cF
    wrex
    vv
    cU
    wral
    vv
    cU
    cF
    cX
    va
    iscfilu
    simprbda
end
