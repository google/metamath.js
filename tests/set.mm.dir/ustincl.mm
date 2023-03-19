include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cin.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "wss.mm"
include "wi.mm"
include "cxp.mm"
include "cpw.mm"
include "cid.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "wrex.mm"
include "w3a.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "isust.mm"
include "syl.mm"
include "ibi.mm"
include "simp3d.mm"
include "wceq.mm"
include "sseq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "sseq2.mm"
include "cnveq.mm"
include "rexbidv.mm"
include "3anbi123d.mm"
include "rspcv.mm"
include "mpan9.mm"
include "simp2d.mm"
include "ineq2.mm"
include "3impa.mm"

theorem ustincl
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w


  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U /\ W e. U ) -> ( V i^i W ) e. U )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cV
    cU
    wcel
    #
    cW
    cU
    wcel
    #
    cV
    cW
    cin
    #
    cU
    wcel
    #
    @0
    @1
    wa
    #
    cV
    vw
    cv
    #
    cin
    #
    cU
    wcel
    #
    vw
    cU
    wral
    #
    @2
    @4
    @5
    cV
    @6
    wss
    #
    @6
    cU
    wcel
    #
    wi
    #
    vw
    cX
    cX
    cxp
    #
    cpw
    #
    wral
    #
    @9
    cid
    cX
    cres
    #
    cV
    wss
    #
    cV
    ccnv
    #
    cU
    wcel
    #
    @6
    @6
    ccom
    #
    cV
    wss
    #
    vw
    cU
    wrex
    #
    w3a
    #
    @0
    vv
    cv
    #
    @6
    wss
    #
    @11
    wi
    #
    vw
    @14
    wral
    #
    @24
    @6
    cin
    #
    cU
    wcel
    #
    vw
    cU
    wral
    #
    @16
    @24
    wss
    #
    @24
    ccnv
    #
    cU
    wcel
    #
    @20
    @24
    wss
    #
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
    @1
    @15
    @9
    @23
    w3a
    #
    @0
    cU
    @14
    wss
    #
    @13
    cU
    wcel
    #
    @38
    @0
    @40
    @41
    @38
    w3a
    #
    @0
    cX
    cvv
    wcel
    @0
    @42
    wb
    cU
    cX
    cust
    elfvex
    vw
    vv
    cU
    cvv
    cX
    isust
    syl
    ibi
    simp3d
    @37
    @39
    vv
    cV
    cU
    @24
    cV
    wceq
    #
    @27
    @15
    @30
    @9
    @36
    @23
    @43
    @26
    @12
    vw
    @14
    @43
    @25
    @10
    @11
    @24
    cV
    @6
    sseq1
    imbi1d
    ralbidv
    @43
    @29
    @8
    vw
    cU
    @43
    @28
    @7
    cU
    @24
    cV
    @6
    ineq1
    eleq1d
    ralbidv
    @43
    @31
    @17
    @33
    @19
    @35
    @22
    @24
    cV
    @16
    sseq2
    @43
    @32
    @18
    cU
    @24
    cV
    cnveq
    eleq1d
    @43
    @34
    @21
    vw
    cU
    @24
    cV
    @20
    sseq2
    rexbidv
    3anbi123d
    3anbi123d
    rspcv
    mpan9
    simp2d
    @8
    @4
    vw
    cW
    cU
    @6
    cW
    wceq
    @7
    @3
    cU
    @6
    cW
    cV
    ineq2
    eleq1d
    rspcv
    mpan9
    3impa
end
