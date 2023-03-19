include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cin.mm"
include "cid.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "wrex.mm"
include "simp1.mm"
include "cvv.mm"
include "wb.mm"
include "elfvexd.mm"
include "isust.mm"
include "syl.mm"
include "mpbid.mm"
include "simp3d.mm"
include "ralimi.mm"
include "simp2.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "simp3.mm"
include "sselpwd.mm"
include "wceq.mm"
include "sseq1.mm"
include "imbi1d.mm"
include "sseq2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspc2v.mm"
include "mpd.mm"

theorem ustssel
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w


  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U /\ W C_ ( X X. X ) ) -> ( V C_ W -> W e. U ) )

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
    cX
    cX
    cxp
    #
    wss
    #
    w3a
    #
    vv
    cv
    #
    vw
    cv
    #
    wss
    #
    @6
    cU
    wcel
    #
    wi
    #
    vw
    @2
    cpw
    #
    wral
    #
    vv
    cU
    wral
    #
    cV
    cW
    wss
    #
    cW
    cU
    wcel
    #
    wi
    #
    @4
    @11
    @5
    @6
    cin
    cU
    wcel
    vw
    cU
    wral
    #
    cid
    cX
    cres
    @5
    wss
    @5
    ccnv
    cU
    wcel
    @6
    @6
    ccom
    @5
    wss
    vw
    cU
    wrex
    w3a
    #
    w3a
    #
    vv
    cU
    wral
    #
    @12
    @4
    cU
    @10
    wss
    #
    @2
    cU
    wcel
    #
    @19
    @4
    @0
    @20
    @21
    @19
    w3a
    #
    @0
    @1
    @3
    simp1
    #
    @4
    cX
    cvv
    wcel
    #
    @0
    @22
    wb
    @4
    cU
    cust
    cX
    @23
    elfvexd
    #
    vw
    vv
    cU
    cvv
    cX
    isust
    syl
    mpbid
    simp3d
    @18
    @11
    vv
    cU
    @11
    @16
    @17
    simp1
    ralimi
    syl
    @4
    @1
    cW
    @10
    wcel
    @12
    @15
    wi
    @0
    @1
    @3
    simp2
    @4
    cW
    @2
    cvv
    @4
    @24
    @24
    @2
    cvv
    wcel
    @25
    @25
    cX
    cX
    cvv
    cvv
    xpexg
    syl2anc
    @0
    @1
    @3
    simp3
    sselpwd
    @9
    @15
    cV
    @6
    wss
    #
    @8
    wi
    vv
    vw
    cV
    cW
    cU
    @10
    @5
    cV
    wceq
    @7
    @26
    @8
    @5
    cV
    @6
    sseq1
    imbi1d
    @6
    cW
    wceq
    @26
    @13
    @8
    @14
    @6
    cW
    cV
    sseq2
    @6
    cW
    cU
    eleq1
    imbi12d
    rspc2v
    syl2anc
    mpd
end
