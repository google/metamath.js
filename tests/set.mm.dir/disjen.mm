include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "csn.mm"
include "cxp.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "cop.mm"
include "1st2nd2.mm"
include "ad2antll.mm"
include "simprl.mm"
include "eqeltrrd.mm"
include "fvex.mm"
include "opelrn.mm"
include "syl.mm"
include "pwuninel.mm"
include "xp2nd.mm"
include "elsni.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "pm2.65da.mm"
include "elin.mm"
include "sylnibr.mm"
include "eq0rdv.mm"
include "cvv.mm"
include "simpr.mm"
include "rnexg.mm"
include "adantr.mm"
include "uniexg.mm"
include "pwexg.mm"
include "3syl.mm"
include "xpsneng.mm"
include "syl2anc.mm"
include "jca.mm"

theorem disjen
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x


  assert |- ( ( A e. V /\ B e. W ) -> ( ( A i^i ( B X. { ~P U. ran A } ) ) = (/) /\ ( B X. { ~P U. ran A } ) ~~ B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    cB
    cA
    crn
    #
    cuni
    #
    cpw
    #
    csn
    #
    cxp
    #
    cin
    #
    c0
    wceq
    @7
    cB
    cen
    wbr
    #
    @2
    vx
    @8
    @2
    vx
    cv
    #
    cA
    wcel
    #
    @10
    @7
    wcel
    #
    wa
    #
    @10
    @8
    wcel
    @2
    @13
    @10
    c2nd
    cfv
    #
    @3
    wcel
    #
    @2
    @13
    wa
    #
    @10
    c1st
    cfv
    #
    @14
    cop
    #
    cA
    wcel
    @15
    @16
    @10
    @18
    cA
    @12
    @10
    @18
    wceq
    @2
    @11
    @10
    cB
    @6
    1st2nd2
    ad2antll
    @2
    @11
    @12
    simprl
    eqeltrrd
    @17
    @14
    cA
    @10
    c1st
    fvex
    @10
    c2nd
    fvex
    opelrn
    syl
    @16
    @15
    @5
    @3
    wcel
    @3
    pwuninel
    @16
    @14
    @5
    @3
    @16
    @14
    @6
    wcel
    #
    @14
    @5
    wceq
    @12
    @19
    @2
    @11
    @10
    cB
    @6
    xp2nd
    ad2antll
    @14
    @5
    elsni
    syl
    eleq1d
    mtbiri
    pm2.65da
    @10
    cA
    @7
    elin
    sylnibr
    eq0rdv
    @2
    @1
    @5
    cvv
    wcel
    #
    @9
    @0
    @1
    simpr
    @2
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @20
    @0
    @21
    @1
    cA
    cV
    rnexg
    adantr
    @3
    cvv
    uniexg
    @4
    cvv
    pwexg
    3syl
    cB
    @5
    cW
    cvv
    xpsneng
    syl2anc
    jca
end
