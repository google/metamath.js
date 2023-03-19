include "cust.mm"
include "cfv.mm"
include "wcel.mm"
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
include "simp2d.mm"

theorem ustbasel
  let cU: class U
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cV: class V
  let cW: class W


  assert |- ( U e. ( UnifOn ` X ) -> ( X X. X ) e. U )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cU
    cX
    cX
    cxp
    #
    cpw
    #
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
    simp2d
end
