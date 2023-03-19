include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfilu.mm"
include "wa.mm"
include "cfg.mm"
include "co.mm"
include "cfbas.mm"
include "cv.mm"
include "cxp.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cfil.mm"
include "cfilufbas.mm"
include "fgcl.mm"
include "filfbas.mm"
include "3syl.mm"
include "ad3antrrr.mm"
include "ssfg.mm"
include "syl.mm"
include "simplr.mm"
include "sseldd.mm"
include "weq.mm"
include "id.mm"
include "sqxpeqd.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "sylancom.mm"
include "iscfilu.mm"
include "simplbda.mm"
include "r19.21bi.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "wb.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem cfilufg
  let cU: class U
  let cF: class F
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vv: setvar v


  assert |- ( ( U e. ( UnifOn ` X ) /\ F e. ( CauFilU ` U ) ) -> ( X filGen F ) e. ( CauFilU ` U ) )

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
    #
    wcel
    #
    wa
    #
    cX
    cF
    cfg
    co
    #
    @1
    wcel
    #
    @4
    cX
    cfbas
    cfv
    #
    wcel
    #
    va
    cv
    #
    @8
    cxp
    #
    vv
    cv
    #
    wss
    #
    va
    @4
    wrex
    #
    vv
    cU
    wral
    #
    @3
    cF
    @6
    wcel
    #
    @4
    cX
    cfil
    cfv
    wcel
    @7
    cU
    cF
    cX
    cfilufbas
    #
    cF
    cX
    fgcl
    @4
    cX
    filfbas
    3syl
    @3
    @12
    vv
    cU
    @3
    @10
    cU
    wcel
    #
    wa
    #
    vb
    cv
    #
    @18
    cxp
    #
    @10
    wss
    #
    @12
    vb
    cF
    @17
    @18
    cF
    wcel
    #
    wa
    #
    @20
    @18
    @4
    wcel
    @12
    @22
    @20
    wa
    #
    cF
    @4
    @18
    @23
    @14
    cF
    @4
    wss
    @3
    @14
    @16
    @21
    @20
    @15
    ad3antrrr
    cF
    cX
    ssfg
    syl
    @17
    @21
    @20
    simplr
    sseldd
    @11
    @20
    va
    @18
    @4
    va
    vb
    weq
    #
    @9
    @19
    @10
    @24
    @8
    @18
    @24
    id
    sqxpeqd
    sseq1d
    rspcev
    sylancom
    @3
    @20
    vb
    cF
    wrex
    #
    vv
    cU
    @0
    @2
    @14
    @25
    vv
    cU
    wral
    vv
    cU
    cF
    cX
    vb
    iscfilu
    simplbda
    r19.21bi
    r19.29a
    ralrimiva
    @0
    @5
    @7
    @13
    wa
    wb
    @2
    vv
    cU
    @4
    cX
    va
    iscfilu
    adantr
    mpbir2and
end
