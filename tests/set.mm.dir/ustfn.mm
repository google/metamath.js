include "cvv.mm"
include "cv.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "wcel.mm"
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
include "cust.mm"
include "selpw.mm"
include "abbii.mm"
include "abid2.mm"
include "vex.mm"
include "xpex.mm"
include "pwex.mm"
include "eqeltri.mm"
include "eqeltrri.mm"
include "simp1.mm"
include "ss2abi.mm"
include "ssexi.mm"
include "df-ust.mm"
include "fnmpti.mm"

theorem ustfn
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x


  assert |- UnifOn Fn _V

  proof
    vx
    cvv
    vu
    cv
    #
    vx
    cv
    #
    @1
    cxp
    #
    cpw
    #
    wss
    #
    @2
    @0
    wcel
    #
    vv
    cv
    #
    vw
    cv
    #
    wss
    @7
    @0
    wcel
    wi
    vw
    @3
    wral
    @6
    @7
    cin
    @0
    wcel
    vw
    @0
    wral
    cid
    @1
    cres
    @6
    wss
    @6
    ccnv
    @0
    wcel
    @7
    @7
    ccom
    @6
    wss
    vw
    @0
    wrex
    w3a
    w3a
    vv
    @0
    wral
    #
    w3a
    #
    vu
    cab
    #
    cust
    @10
    @4
    vu
    cab
    #
    @0
    @3
    cpw
    #
    wcel
    #
    vu
    cab
    #
    @11
    cvv
    @13
    @4
    vu
    vu
    @3
    selpw
    abbii
    @14
    @12
    cvv
    vu
    @12
    abid2
    @3
    @2
    @1
    @1
    vx
    vex
    #
    @15
    xpex
    pwex
    pwex
    eqeltri
    eqeltrri
    @9
    @4
    vu
    @4
    @5
    @8
    simp1
    ss2abi
    ssexi
    vx
    vw
    vv
    vu
    df-ust
    fnmpti
end
