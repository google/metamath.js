include "cxp.mm"
include "cun.mm"
include "cpw.mm"
include "relxp.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "opelxp.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "snssi.mm"
include "ssun3.mm"
include "syl.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"
include "adantr.mm"
include "df-pr.mm"
include "ssun4.mm"
include "anim12i.mm"
include "unss.mm"
include "sylib.mm"
include "syl5eqss.mm"
include "zfpair2.mm"
include "jca.mm"
include "prex.mm"
include "vex.mm"
include "dfop.mm"
include "eleq1i.mm"
include "prss.mm"
include "3bitr4ri.mm"
include "sylbi.mm"
include "relssi.mm"

theorem xpsspw
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A X. B ) C_ ~P ~P ( A u. B )

  proof
    vx
    vy
    cA
    cB
    cxp
    #
    cA
    cB
    cun
    #
    cpw
    #
    cpw
    #
    cA
    cB
    relxp
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @0
    wcel
    @4
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    #
    @6
    @3
    wcel
    #
    @4
    @5
    cA
    cB
    opelxp
    @9
    @4
    csn
    #
    @2
    wcel
    #
    @4
    @5
    cpr
    #
    @2
    wcel
    #
    wa
    #
    @10
    @9
    @12
    @14
    @7
    @12
    @8
    @7
    @11
    @1
    wss
    #
    @12
    @7
    @11
    cA
    wss
    @16
    @4
    cA
    snssi
    @11
    cA
    cB
    ssun3
    syl
    #
    @11
    @1
    @4
    snex
    #
    elpw
    sylibr
    adantr
    @9
    @13
    @1
    wss
    @14
    @9
    @13
    @11
    @5
    csn
    #
    cun
    #
    @1
    @4
    @5
    df-pr
    @9
    @16
    @19
    @1
    wss
    #
    wa
    @20
    @1
    wss
    @7
    @16
    @8
    @21
    @17
    @8
    @19
    cB
    wss
    @21
    @5
    cB
    snssi
    @19
    cB
    cA
    ssun4
    syl
    anim12i
    @11
    @19
    @1
    unss
    sylib
    syl5eqss
    @13
    @1
    vx
    vy
    zfpair2
    #
    elpw
    sylibr
    jca
    @11
    @13
    cpr
    #
    @3
    wcel
    @23
    @2
    wss
    @10
    @15
    @23
    @2
    @11
    @13
    prex
    elpw
    @6
    @23
    @3
    @4
    @5
    vx
    vex
    vy
    vex
    dfop
    eleq1i
    @11
    @13
    @2
    @18
    @22
    prss
    3bitr4ri
    sylib
    sylbi
    relssi
end
