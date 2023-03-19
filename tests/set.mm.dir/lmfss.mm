include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "clm.mm"
include "wbr.mm"
include "wa.mm"
include "wfun.mm"
include "cc.mm"
include "cxp.mm"
include "wss.mm"
include "cpm.mm"
include "co.mm"
include "lmfpm.mm"
include "wb.mm"
include "cvv.mm"
include "toponmax.mm"
include "cnex.mm"
include "elpmg.mm"
include "sylancl.mm"
include "adantr.mm"
include "mpbid.mm"
include "simprd.mm"

theorem lmfss
  let cP: class P
  let cF: class F
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vy: setvar y


  assert |- ( ( J e. ( TopOn ` X ) /\ F ( ~~>t ` J ) P ) -> F C_ ( CC X. X ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cP
    cJ
    clm
    cfv
    wbr
    #
    wa
    #
    cF
    wfun
    #
    cF
    cc
    cX
    cxp
    wss
    #
    @2
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    @3
    @4
    wa
    #
    cP
    cF
    cJ
    cX
    lmfpm
    @0
    @5
    @6
    wb
    #
    @1
    @0
    cX
    cJ
    wcel
    cc
    cvv
    wcel
    @7
    cX
    cJ
    toponmax
    cnex
    cX
    cc
    cF
    cJ
    cvv
    elpmg
    sylancl
    adantr
    mpbid
    simprd
end
