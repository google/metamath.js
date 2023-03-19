include "cflim.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "ccl.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "cuni.mm"
include "wi.mm"
include "wral.mm"
include "ctop.mm"
include "wss.mm"
include "flimtop.mm"
include "eqid.mm"
include "flimelbas.mm"
include "snssd.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "sselda.mm"
include "cnei.mm"
include "simpll.mm"
include "syl.mm"
include "simprl.mm"
include "w3a.mm"
include "adantr.mm"
include "simpr.mm"
include "3jca.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "clsndisj.mm"
include "disjsn.mm"
include "necon2abii.mm"
include "sylibr.mm"
include "sylan.mm"
include "opnneip.mm"
include "syl3anc.mm"
include "flimnei.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "cfil.mm"
include "wb.mm"
include "toptopon.mm"
include "sylib.mm"
include "flimfil.mm"
include "flimopn.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"

theorem flimsncls
  let cA: class A
  let cF: class F
  let cJ: class J
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. ( J fLim F ) -> ( ( cls ` J ) ` { A } ) C_ ( J fLim F ) )

  proof
    cA
    cJ
    cF
    cflim
    co
    #
    wcel
    #
    vx
    cA
    csn
    #
    cJ
    ccl
    cfv
    cfv
    #
    @0
    @1
    vx
    cv
    #
    @3
    wcel
    #
    @4
    @0
    wcel
    #
    @1
    @5
    wa
    #
    @6
    @4
    cJ
    cuni
    #
    wcel
    #
    @4
    vy
    cv
    #
    wcel
    #
    @10
    cF
    wcel
    #
    wi
    #
    vy
    cJ
    wral
    #
    @1
    @3
    @8
    @4
    @1
    cJ
    ctop
    wcel
    #
    @2
    @8
    wss
    #
    @3
    @8
    wss
    cA
    cF
    cJ
    flimtop
    #
    @1
    cA
    @8
    cA
    cF
    cJ
    @8
    @8
    eqid
    #
    flimelbas
    snssd
    #
    @2
    cJ
    @8
    @18
    clsss3
    syl2anc
    sselda
    @7
    @13
    vy
    cJ
    @7
    @10
    cJ
    wcel
    #
    @11
    @12
    @7
    @20
    @11
    wa
    #
    wa
    #
    @1
    @10
    @2
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    @12
    @1
    @5
    @21
    simpll
    #
    @22
    @15
    @20
    cA
    @10
    wcel
    #
    @23
    @22
    @1
    @15
    @24
    @17
    syl
    @7
    @20
    @11
    simprl
    @7
    @15
    @16
    @5
    w3a
    #
    @21
    @25
    @7
    @15
    @16
    @5
    @1
    @15
    @5
    @17
    adantr
    #
    @1
    @16
    @5
    @19
    adantr
    @1
    @5
    simpr
    3jca
    @26
    @21
    wa
    @10
    @2
    cin
    #
    c0
    wne
    @25
    @4
    @2
    @10
    cJ
    @8
    @18
    clsndisj
    @25
    @28
    c0
    @10
    cA
    disjsn
    necon2abii
    sylibr
    sylan
    cA
    cJ
    @10
    opnneip
    syl3anc
    cA
    cF
    cJ
    @10
    flimnei
    syl2anc
    expr
    ralrimiva
    @7
    cJ
    @8
    ctopon
    cfv
    wcel
    #
    cF
    @8
    cfil
    cfv
    wcel
    #
    @6
    @9
    @14
    wa
    wb
    @7
    @15
    @29
    @27
    cJ
    @8
    @18
    toptopon
    sylib
    @1
    @30
    @5
    cA
    cF
    cJ
    @8
    @18
    flimfil
    adantr
    vy
    @4
    cF
    cJ
    @8
    flimopn
    syl2anc
    mpbir2and
    ex
    ssrdv
end
