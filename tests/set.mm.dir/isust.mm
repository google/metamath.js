include "wcel.mm"
include "cust.mm"
include "cfv.mm"
include "cv.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
include "cid.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "wrex.mm"
include "w3a.mm"
include "cab.mm"
include "ustval.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wb.mm"
include "simp1.mm"
include "wa.mm"
include "sqxpexg.mm"
include "pwexg.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "ssexd.mm"
include "ex.mm"
include "syl5.mm"
include "wceq.mm"
include "sseq1.mm"
include "eleq2.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "raleqbi1dv.mm"
include "rexeq.mm"
include "3anbi23d.mm"
include "3anbi123d.mm"
include "elab3g.mm"
include "bitrd.mm"

theorem isust
  let vw: setvar w
  let vv: setvar v
  let cU: class U
  let cV: class V
  let cX: class X
  let vu: setvar u

  disjoint v w
  disjoint U v
  disjoint U w
  disjoint X v
  disjoint X w
  disjoint u v
  disjoint u w
  disjoint U u
  disjoint X u
  assert |- ( X e. V -> ( U e. ( UnifOn ` X ) <-> ( U C_ ~P ( X X. X ) /\ ( X X. X ) e. U /\ A. v e. U ( A. w e. ~P ( X X. X ) ( v C_ w -> w e. U ) /\ A. w e. U ( v i^i w ) e. U /\ ( ( _I |` X ) C_ v /\ `' v e. U /\ E. w e. U ( w o. w ) C_ v ) ) ) ) )

  proof
    cX
    cV
    wcel
    #
    cU
    cX
    cust
    cfv
    #
    wcel
    cU
    vu
    cv
    #
    cX
    cX
    cxp
    #
    cpw
    #
    wss
    #
    @3
    @2
    wcel
    #
    vv
    cv
    #
    vw
    cv
    #
    wss
    #
    vw
    vu
    wel
    #
    wi
    #
    vw
    @4
    wral
    #
    @7
    @8
    cin
    #
    @2
    wcel
    #
    vw
    @2
    wral
    #
    cid
    cX
    cres
    @7
    wss
    #
    @7
    ccnv
    #
    @2
    wcel
    #
    @8
    @8
    ccom
    @7
    wss
    #
    vw
    @2
    wrex
    #
    w3a
    #
    w3a
    #
    vv
    @2
    wral
    #
    w3a
    #
    vu
    cab
    #
    wcel
    #
    cU
    @4
    wss
    #
    @3
    cU
    wcel
    #
    @9
    @8
    cU
    wcel
    #
    wi
    #
    vw
    @4
    wral
    #
    @13
    cU
    wcel
    #
    vw
    cU
    wral
    #
    @16
    @17
    cU
    wcel
    #
    @19
    vw
    cU
    wrex
    #
    w3a
    #
    w3a
    #
    vv
    cU
    wral
    #
    w3a
    #
    @0
    @1
    @25
    cU
    vw
    vv
    vu
    cV
    cX
    ustval
    eleq2d
    @0
    @39
    cU
    cvv
    wcel
    #
    wi
    @26
    @39
    wb
    @39
    @27
    @0
    @40
    @27
    @28
    @38
    simp1
    @0
    @27
    @40
    @0
    @27
    wa
    cU
    @4
    cvv
    @0
    @4
    cvv
    wcel
    #
    @27
    @0
    @3
    cvv
    wcel
    @41
    cX
    cV
    sqxpexg
    @3
    cvv
    pwexg
    syl
    adantr
    @0
    @27
    simpr
    ssexd
    ex
    syl5
    @24
    @39
    vu
    cU
    cvv
    @2
    cU
    wceq
    #
    @5
    @27
    @6
    @28
    @23
    @38
    @2
    cU
    @4
    sseq1
    @2
    cU
    @3
    eleq2
    @22
    @37
    vv
    @2
    cU
    @42
    @12
    @31
    @15
    @33
    @21
    @36
    @42
    @11
    @30
    vw
    @4
    @42
    @10
    @29
    @9
    @2
    cU
    @8
    eleq2
    imbi2d
    ralbidv
    @14
    @32
    vw
    @2
    cU
    @2
    cU
    @13
    eleq2
    raleqbi1dv
    @42
    @18
    @34
    @20
    @35
    @16
    @2
    cU
    @17
    eleq2
    @19
    vw
    @2
    cU
    rexeq
    3anbi23d
    3anbi123d
    raleqbi1dv
    3anbi123d
    elab3g
    syl
    bitrd
end
