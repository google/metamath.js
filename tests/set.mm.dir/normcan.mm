include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wne.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "csm.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cc.mm"
include "wrex.mm"
include "wb.mm"
include "elspansn.mm"
include "adantr.mm"
include "cmul.mm"
include "oveq1.mm"
include "simpr.mm"
include "simpl.mm"
include "ax-his3.mm"
include "syl3anc.mm"
include "sylan9eqr.mm"
include "normsq.mm"
include "ad2antrr.mm"
include "oveq12d.mm"
include "adantllr.mm"
include "hicl.mm"
include "anidms.mm"
include "cc0.mm"
include "his6.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "divcan4d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "sylbid.mm"
include "3impia.mm"

theorem normcan
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( B e. ~H /\ B =/= 0h /\ A e. ( span ` { B } ) ) -> ( ( ( A .ih B ) / ( ( normh ` B ) ^ 2 ) ) .h B ) = A )

  proof
    cB
    chil
    wcel
    #
    cB
    c0v
    wne
    #
    cA
    cB
    csn
    cspn
    cfv
    wcel
    #
    cA
    cB
    csp
    co
    #
    cB
    cno
    cfv
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cB
    csm
    co
    #
    cA
    wceq
    #
    @0
    @1
    wa
    #
    @2
    cA
    vx
    cv
    #
    cB
    csm
    co
    #
    wceq
    #
    vx
    cc
    wrex
    #
    @7
    @0
    @2
    @12
    wb
    @1
    vx
    cB
    cA
    elspansn
    adantr
    @8
    @11
    @7
    vx
    cc
    @8
    @9
    cc
    wcel
    #
    @11
    @7
    @8
    @13
    wa
    #
    @11
    wa
    #
    @6
    @10
    cA
    @15
    @5
    @9
    cB
    csm
    @15
    @5
    @9
    cB
    cB
    csp
    co
    #
    cmul
    co
    #
    @16
    cdiv
    co
    #
    @9
    @0
    @13
    @11
    @5
    @18
    wceq
    @1
    @0
    @13
    wa
    #
    @11
    wa
    @3
    @17
    @4
    @16
    cdiv
    @11
    @19
    @3
    @10
    cB
    csp
    co
    #
    @17
    cA
    @10
    cB
    csp
    oveq1
    @19
    @13
    @0
    @0
    @20
    @17
    wceq
    @0
    @13
    simpr
    @0
    @13
    simpl
    #
    @21
    @9
    cB
    cB
    ax-his3
    syl3anc
    sylan9eqr
    @0
    @4
    @16
    wceq
    @13
    @11
    cB
    normsq
    ad2antrr
    oveq12d
    adantllr
    @14
    @18
    @9
    wceq
    @11
    @14
    @9
    @16
    @8
    @13
    simpr
    @0
    @16
    cc
    wcel
    #
    @1
    @13
    @0
    @22
    cB
    cB
    hicl
    anidms
    ad2antrr
    @8
    @16
    cc0
    wne
    #
    @13
    @0
    @23
    @1
    @0
    @16
    cc0
    cB
    c0v
    cB
    his6
    necon3bid
    biimpar
    adantr
    divcan4d
    adantr
    eqtrd
    oveq1d
    @14
    @11
    simpr
    eqtr4d
    exp31
    rexlimdv
    sylbid
    3impia
end
