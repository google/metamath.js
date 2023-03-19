include "cxp.mm"
include "cun.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "cen.mm"
include "wss.mm"
include "wa.mm"
include "cwdom.mm"
include "wo.mm"
include "wex.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "domeng.mm"
include "syl.mm"
include "ibi.mm"
include "cin.mm"
include "simprl.mm"
include "indi.mm"
include "wceq.mm"
include "simprr.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eqr.mm"
include "breqtrrd.mm"
include "unxpwdom2.mm"
include "wi.mm"
include "ssun1.mm"
include "adantr.mm"
include "ssexg.mm"
include "sylancr.mm"
include "inss2.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domwdom.mm"
include "wdomtr.mm"
include "expcom.mm"
include "ssun2.mm"
include "domtr.mm"
include "orim12d.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem unxpwdom
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A X. A ) ~<_ ( B u. C ) -> ( A ~<_* B \/ A ~<_ C ) )

  proof
    cA
    cA
    cxp
    #
    cB
    cC
    cun
    #
    cdom
    wbr
    #
    @0
    vx
    cv
    #
    cen
    wbr
    #
    @3
    @1
    wss
    #
    wa
    #
    cA
    cB
    cwdom
    wbr
    #
    cA
    cC
    cdom
    wbr
    #
    wo
    #
    vx
    @2
    @6
    vx
    wex
    #
    @2
    @1
    cvv
    wcel
    #
    @2
    @10
    wb
    @0
    @1
    cdom
    reldom
    brrelex2i
    #
    vx
    @0
    @1
    cvv
    domeng
    syl
    ibi
    @2
    @6
    wa
    #
    cA
    @3
    cB
    cin
    #
    cwdom
    wbr
    #
    cA
    @3
    cC
    cin
    #
    cdom
    wbr
    #
    wo
    #
    @9
    @13
    @0
    @14
    @16
    cun
    #
    cen
    wbr
    @18
    @13
    @0
    @3
    @19
    cen
    @2
    @4
    @5
    simprl
    @13
    @19
    @3
    @1
    cin
    #
    @3
    @3
    cB
    cC
    indi
    @13
    @5
    @20
    @3
    wceq
    @2
    @4
    @5
    simprr
    @3
    @1
    df-ss
    sylib
    syl5eqr
    breqtrrd
    cA
    @14
    @16
    unxpwdom2
    syl
    @13
    @15
    @7
    @17
    @8
    @13
    @14
    cB
    cwdom
    wbr
    #
    @15
    @7
    wi
    @13
    @14
    cB
    cdom
    wbr
    #
    @21
    @13
    cB
    cvv
    wcel
    #
    @14
    cB
    wss
    @22
    @13
    cB
    @1
    wss
    @11
    @23
    cB
    cC
    ssun1
    @2
    @11
    @6
    @12
    adantr
    #
    cB
    @1
    cvv
    ssexg
    sylancr
    @3
    cB
    inss2
    @14
    cB
    cvv
    ssdomg
    mpisyl
    @14
    cB
    domwdom
    syl
    @15
    @21
    @7
    cA
    @14
    cB
    wdomtr
    expcom
    syl
    @13
    @16
    cC
    cdom
    wbr
    #
    @17
    @8
    wi
    @13
    cC
    cvv
    wcel
    #
    @16
    cC
    wss
    @25
    @13
    cC
    @1
    wss
    @11
    @26
    cC
    cB
    ssun2
    @24
    cC
    @1
    cvv
    ssexg
    sylancr
    @3
    cC
    inss2
    @16
    cC
    cvv
    ssdomg
    mpisyl
    @17
    @25
    @8
    cA
    @16
    cC
    domtr
    expcom
    syl
    orim12d
    mpd
    exlimddv
end
