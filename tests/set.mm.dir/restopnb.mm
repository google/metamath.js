include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "crest.mm"
include "co.mm"
include "wi.mm"
include "simpr3.mm"
include "simpr2.mm"
include "sstrd.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqcomd.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "expcom.mm"
include "syl.mm"
include "inass.mm"
include "simprr.mm"
include "ineq1d.mm"
include "simplr3.mm"
include "adantrr.mm"
include "eqtr3d.mm"
include "simplr2.mm"
include "sseqin2.mm"
include "ineq2d.mm"
include "3eqtr3a.mm"
include "simplll.mm"
include "simprl.mm"
include "simplr1.mm"
include "inopn.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "rexlimdvaa.mm"
include "impbid.mm"
include "wb.mm"
include "elrest.mm"
include "adantr.mm"
include "bitr4d.mm"

theorem restopnb
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let cV: class V
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cK: class K


  assert |- ( ( ( J e. Top /\ A e. V ) /\ ( B e. J /\ B C_ A /\ C C_ B ) ) -> ( C e. J <-> C e. ( J |`t A ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cB
    cJ
    wcel
    #
    cB
    cA
    wss
    #
    cC
    cB
    wss
    #
    w3a
    #
    wa
    #
    cC
    cJ
    wcel
    #
    cC
    vv
    cv
    #
    cA
    cin
    #
    wceq
    #
    vv
    cJ
    wrex
    #
    cC
    cJ
    cA
    crest
    co
    wcel
    #
    @7
    @8
    @12
    @7
    cC
    cC
    cA
    cin
    #
    wceq
    #
    @8
    @12
    wi
    @7
    @14
    cC
    @7
    cC
    cA
    wss
    @14
    cC
    wceq
    @7
    cC
    cB
    cA
    @2
    @3
    @4
    @5
    simpr3
    @2
    @3
    @4
    @5
    simpr2
    sstrd
    cC
    cA
    df-ss
    sylib
    eqcomd
    @8
    @15
    @12
    @11
    @15
    vv
    cC
    cJ
    @9
    cC
    wceq
    @10
    @14
    cC
    @9
    cC
    cA
    ineq1
    eqeq2d
    rspcev
    expcom
    syl
    @7
    @11
    @8
    vv
    cJ
    @7
    @9
    cJ
    wcel
    #
    @11
    wa
    #
    wa
    #
    cC
    @9
    cB
    cin
    #
    cJ
    @18
    @10
    cB
    cin
    #
    @9
    cA
    cB
    cin
    #
    cin
    #
    cC
    @19
    @9
    cA
    cB
    inass
    @18
    cC
    cB
    cin
    #
    @20
    cC
    @18
    cC
    @10
    cB
    @7
    @16
    @11
    simprr
    ineq1d
    @7
    @16
    @23
    cC
    wceq
    #
    @11
    @7
    @16
    wa
    #
    @5
    @24
    @3
    @4
    @5
    @2
    @16
    simplr3
    cC
    cB
    df-ss
    sylib
    adantrr
    eqtr3d
    @7
    @16
    @22
    @19
    wceq
    @11
    @25
    @21
    cB
    @9
    @25
    @4
    @21
    cB
    wceq
    @3
    @4
    @5
    @2
    @16
    simplr2
    cB
    cA
    sseqin2
    sylib
    ineq2d
    adantrr
    3eqtr3a
    @18
    @0
    @16
    @3
    @19
    cJ
    wcel
    @0
    @1
    @6
    @17
    simplll
    @7
    @16
    @11
    simprl
    @3
    @4
    @5
    @2
    @17
    simplr1
    @9
    cB
    cJ
    inopn
    syl3anc
    eqeltrd
    rexlimdvaa
    impbid
    @2
    @13
    @12
    wb
    @6
    vv
    cC
    cA
    cJ
    ctop
    cV
    elrest
    adantr
    bitr4d
end
