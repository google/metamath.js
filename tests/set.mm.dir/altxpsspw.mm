include "caltxp.mm"
include "cpw.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "caltop.mm"
include "wceq.mm"
include "wrex.mm"
include "elaltxp.mm"
include "wa.mm"
include "wi.mm"
include "csn.mm"
include "cpr.mm"
include "df-altop.mm"
include "wss.mm"
include "snssi.mm"
include "ssun3.mm"
include "syl.mm"
include "adantr.mm"
include "elun1.mm"
include "snex.mm"
include "elpw.mm"
include "elun2.mm"
include "sylbir.mm"
include "anim12i.mm"
include "vex.mm"
include "prss.mm"
include "sylib.mm"
include "prex.mm"
include "prsspw.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "syl5eqel.mm"
include "eleq1a.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "ssriv.mm"

theorem altxpsspw
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A XX. B ) C_ ~P ~P ( A u. ~P B )

  proof
    vz
    cA
    cB
    caltxp
    #
    cA
    cB
    cpw
    #
    cun
    #
    cpw
    #
    cpw
    #
    vz
    cv
    #
    @0
    wcel
    @5
    vx
    cv
    #
    vy
    cv
    #
    caltop
    #
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    @5
    @4
    wcel
    #
    vx
    vy
    cA
    cB
    @5
    elaltxp
    @9
    @10
    vx
    vy
    cA
    cB
    @6
    cA
    wcel
    #
    @7
    cB
    wcel
    #
    wa
    #
    @8
    @4
    wcel
    @9
    @10
    wi
    @13
    @8
    @6
    csn
    #
    @6
    @7
    csn
    #
    cpr
    #
    cpr
    #
    @4
    @6
    @7
    df-altop
    @13
    @14
    @2
    wss
    #
    @16
    @2
    wss
    #
    @17
    @4
    wcel
    #
    @11
    @18
    @12
    @11
    @14
    cA
    wss
    @18
    @6
    cA
    snssi
    @14
    cA
    @1
    ssun3
    syl
    adantr
    @13
    @6
    @2
    wcel
    #
    @15
    @2
    wcel
    #
    wa
    @19
    @11
    @21
    @12
    @22
    @6
    cA
    @1
    elun1
    @12
    @15
    cB
    wss
    #
    @22
    @7
    cB
    snssi
    @23
    @15
    @1
    wcel
    @22
    @15
    cB
    @7
    snex
    #
    elpw
    @15
    @1
    cA
    elun2
    sylbir
    syl
    anim12i
    @6
    @15
    @2
    vx
    vex
    @24
    prss
    sylib
    @20
    @17
    @3
    wss
    @18
    @19
    wa
    @17
    @3
    @14
    @16
    prex
    elpw
    @14
    @16
    @2
    @6
    snex
    @6
    @15
    prex
    prsspw
    bitri
    sylanbrc
    syl5eqel
    @8
    @4
    @5
    eleq1a
    syl
    rexlimivv
    sylbi
    ssriv
end
