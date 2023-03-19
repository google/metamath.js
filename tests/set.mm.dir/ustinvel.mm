include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wss.mm"
include "ccnv.mm"
include "cv.mm"
include "ccom.mm"
include "wrex.mm"
include "wi.mm"
include "cxp.mm"
include "cpw.mm"
include "wral.mm"
include "cin.mm"
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

theorem ustinvel
  let cU: class U
  let cV: class V
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cW: class W


  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U ) -> `' V e. U )

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
    wa
    #
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
    vw
    cv
    #
    @7
    ccom
    #
    cV
    wss
    #
    vw
    cU
    wrex
    #
    @2
    cV
    @7
    wss
    #
    @7
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
    cV
    @7
    cin
    #
    cU
    wcel
    #
    vw
    cU
    wral
    #
    @4
    @6
    @10
    w3a
    #
    @0
    vv
    cv
    #
    @7
    wss
    #
    @12
    wi
    #
    vw
    @15
    wral
    #
    @21
    @7
    cin
    #
    cU
    wcel
    #
    vw
    cU
    wral
    #
    @3
    @21
    wss
    #
    @21
    ccnv
    #
    cU
    wcel
    #
    @8
    @21
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
    @16
    @19
    @20
    w3a
    #
    @0
    cU
    @15
    wss
    #
    @14
    cU
    wcel
    #
    @35
    @0
    @37
    @38
    @35
    w3a
    #
    @0
    cX
    cvv
    wcel
    @0
    @39
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
    @34
    @36
    vv
    cV
    cU
    @21
    cV
    wceq
    #
    @24
    @16
    @27
    @19
    @33
    @20
    @40
    @23
    @13
    vw
    @15
    @40
    @22
    @11
    @12
    @21
    cV
    @7
    sseq1
    imbi1d
    ralbidv
    @40
    @26
    @18
    vw
    cU
    @40
    @25
    @17
    cU
    @21
    cV
    @7
    ineq1
    eleq1d
    ralbidv
    @40
    @28
    @4
    @30
    @6
    @32
    @10
    @21
    cV
    @3
    sseq2
    @40
    @29
    @5
    cU
    @21
    cV
    cnveq
    eleq1d
    @40
    @31
    @9
    vw
    cU
    @21
    cV
    @8
    sseq2
    rexbidv
    3anbi123d
    3anbi123d
    rspcv
    mpan9
    simp3d
    simp2d
end
