include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "wa.mm"
include "cflim.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "csn.mm"
include "cnei.mm"
include "fbflim.mm"
include "cuni.mm"
include "ctop.mm"
include "wb.mm"
include "topontop.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "wceq.mm"
include "toponuni.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "isneip.mm"
include "syl2anc.mm"
include "syl6bi.mm"
include "r19.29.mm"
include "pm3.45.mm"
include "imp.mm"
include "sstr2.mm"
include "com12.mm"
include "reximdv.mm"
include "impcom.mm"
include "syl.mm"
include "rexlimivw.mm"
include "ex.mm"
include "syl9.mm"
include "ralrimdv.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "opnneip.mm"
include "syl3anc.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "expr.mm"
include "com23.mm"
include "ralrimdva.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem fbflim2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cX: class X
  let vy: setvar y
  assume fbflim.3: |- F = ( X filGen B )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint B n
  disjoint B x
  disjoint J n
  disjoint J x
  disjoint X n
  disjoint X x
  disjoint F x
  disjoint n y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint J y
  disjoint X y
  disjoint F y
  assert |- ( ( J e. ( TopOn ` X ) /\ B e. ( fBas ` X ) ) -> ( A e. ( J fLim F ) <-> ( A e. X /\ A. n e. ( ( nei ` J ) ` { A } ) E. x e. B x C_ n ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cB
    cX
    cfbas
    cfv
    wcel
    #
    wa
    #
    cA
    cJ
    cF
    cflim
    co
    wcel
    cA
    cX
    wcel
    #
    cA
    vy
    cv
    #
    wcel
    #
    vx
    cv
    #
    @4
    wss
    #
    vx
    cB
    wrex
    #
    wi
    #
    vy
    cJ
    wral
    #
    wa
    @3
    @6
    vn
    cv
    #
    wss
    #
    vx
    cB
    wrex
    #
    vn
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    #
    wral
    #
    wa
    vy
    vx
    cA
    cB
    cF
    cJ
    cX
    fbflim.3
    fbflim
    @2
    @3
    @10
    @15
    @2
    @3
    wa
    #
    @10
    @15
    @16
    @10
    @13
    vn
    @14
    @16
    @11
    @14
    wcel
    #
    @5
    @4
    @11
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    @10
    @13
    @16
    @17
    @11
    cJ
    cuni
    #
    wss
    #
    @20
    wa
    #
    @20
    @16
    cJ
    ctop
    wcel
    #
    cA
    @21
    wcel
    @17
    @23
    wb
    @0
    @24
    @1
    @3
    cX
    cJ
    topontop
    ad2antrr
    #
    @16
    cA
    cX
    @21
    @2
    @3
    simpr
    @0
    cX
    @21
    wceq
    @1
    @3
    cX
    cJ
    toponuni
    ad2antrr
    eleqtrd
    cA
    vy
    cJ
    @11
    @21
    @21
    eqid
    isneip
    syl2anc
    @22
    @20
    simpr
    syl6bi
    @10
    @20
    @13
    @10
    @20
    wa
    @9
    @19
    wa
    #
    vy
    cJ
    wrex
    @13
    @9
    @19
    vy
    cJ
    r19.29
    @26
    @13
    vy
    cJ
    @26
    @8
    @18
    wa
    #
    @13
    @9
    @19
    @27
    @5
    @8
    @18
    pm3.45
    imp
    @18
    @8
    @13
    @18
    @7
    @12
    vx
    cB
    @7
    @18
    @12
    @6
    @4
    @11
    sstr2
    com12
    reximdv
    impcom
    syl
    rexlimivw
    syl
    ex
    syl9
    ralrimdv
    @16
    @15
    @9
    vy
    cJ
    @16
    @4
    cJ
    wcel
    #
    wa
    @5
    @15
    @8
    @16
    @28
    @5
    @15
    @8
    wi
    #
    @16
    @28
    @5
    wa
    #
    wa
    #
    @4
    @14
    wcel
    #
    @29
    @31
    @24
    @28
    @5
    @32
    @16
    @24
    @30
    @25
    adantr
    @16
    @28
    @5
    simprl
    @16
    @28
    @5
    simprr
    cA
    cJ
    @4
    opnneip
    syl3anc
    @13
    @8
    vn
    @4
    @14
    @11
    @4
    wceq
    @12
    @7
    vx
    cB
    @11
    @4
    @6
    sseq2
    rexbidv
    rspcv
    syl
    expr
    com23
    ralrimdva
    impbid
    pm5.32da
    bitrd
end
