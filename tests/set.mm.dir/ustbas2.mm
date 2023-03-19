include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cdm.mm"
include "cuni.mm"
include "dmxpid.mm"
include "wss.mm"
include "ustbasel.mm"
include "elssuni.mm"
include "syl.mm"
include "cpw.mm"
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
include "ibi.mm"
include "simp1d.mm"
include "unissd.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "eqssd.mm"
include "dmeqd.mm"
include "syl5eqr.mm"

theorem ustbas2
  let cU: class U
  let cX: class X
  let vv: setvar v
  let vw: setvar w


  assert |- ( U e. ( UnifOn ` X ) -> X = dom U. U )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cX
    cX
    cX
    cxp
    #
    cdm
    cU
    cuni
    #
    cdm
    cX
    dmxpid
    @0
    @1
    @2
    @0
    @1
    @2
    @0
    @1
    cU
    wcel
    #
    @1
    @2
    wss
    cU
    cX
    ustbasel
    @1
    cU
    elssuni
    syl
    @0
    @2
    @1
    cpw
    #
    cuni
    @1
    @0
    cU
    @4
    @0
    cU
    @4
    wss
    #
    @3
    vv
    cv
    #
    vw
    cv
    #
    wss
    @7
    cU
    wcel
    wi
    vw
    @4
    wral
    @6
    @7
    cin
    cU
    wcel
    vw
    cU
    wral
    cid
    cX
    cres
    @6
    wss
    @6
    ccnv
    cU
    wcel
    @7
    @7
    ccom
    @6
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
    @5
    @3
    @8
    w3a
    #
    @0
    cX
    cvv
    wcel
    @0
    @9
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
    unissd
    @1
    unipw
    syl6sseq
    eqssd
    dmeqd
    syl5eqr
end
