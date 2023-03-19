include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
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
include "simp1d.mm"
include "sselda.mm"
include "elpwid.mm"

theorem ustssxp
  let cU: class U
  let cV: class V
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w


  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U ) -> V C_ ( X X. X ) )

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
    wa
    cV
    cX
    cX
    cxp
    #
    @0
    cU
    @1
    cpw
    #
    cV
    @0
    cU
    @2
    wss
    #
    @1
    cU
    wcel
    #
    vv
    cv
    #
    vw
    cv
    #
    wss
    @6
    cU
    wcel
    wi
    vw
    @2
    wral
    @5
    @6
    cin
    cU
    wcel
    vw
    cU
    wral
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
    w3a
    vv
    cU
    wral
    #
    @0
    @3
    @4
    @7
    w3a
    #
    @0
    cX
    cvv
    wcel
    @0
    @8
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
    simp1d
    sselda
    elpwid
end
