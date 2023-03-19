include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cres.mm"
include "crest.mm"
include "cuni.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "eqid.mm"
include "cnf.mm"
include "adantr.mm"
include "simpr.mm"
include "fssresd.mm"
include "cin.mm"
include "cnvresima.mm"
include "ctop.mm"
include "cvv.mm"
include "cntop1.mm"
include "topopn.mm"
include "ssexg.mm"
include "ancoms.mm"
include "sylan.mm"
include "cnima.mm"
include "adantlr.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "cfv.mm"
include "wb.mm"
include "toptopon.mm"
include "sylib.mm"
include "resttopon.mm"
include "cntop2.mm"
include "iscn.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem cnrest
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vo: setvar o
  assume cnrest.1: |- X = U. J


  assert |- ( ( F e. ( J Cn K ) /\ A C_ X ) -> ( F |` A ) e. ( ( J |`t A ) Cn K ) )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cF
    cA
    cres
    #
    cJ
    cA
    crest
    co
    #
    cK
    ccn
    co
    wcel
    #
    cA
    cK
    cuni
    #
    @3
    wf
    #
    @3
    ccnv
    vo
    cv
    #
    cima
    #
    @4
    wcel
    #
    vo
    cK
    wral
    #
    @2
    cX
    @6
    cA
    cF
    @0
    cX
    @6
    cF
    wf
    @1
    cF
    cJ
    cK
    cX
    @6
    cnrest.1
    @6
    eqid
    #
    cnf
    adantr
    @0
    @1
    simpr
    fssresd
    @2
    @10
    vo
    cK
    @2
    @8
    cK
    wcel
    #
    wa
    #
    @9
    cF
    ccnv
    @8
    cima
    #
    cA
    cin
    #
    @4
    cA
    @8
    cF
    cnvresima
    @14
    cJ
    ctop
    wcel
    #
    cA
    cvv
    wcel
    #
    @15
    cJ
    wcel
    #
    @16
    @4
    wcel
    @2
    @17
    @13
    @0
    @17
    @1
    cF
    cJ
    cK
    cntop1
    #
    adantr
    adantr
    @2
    @18
    @13
    @0
    @17
    @1
    @18
    @20
    @17
    cX
    cJ
    wcel
    #
    @1
    @18
    cJ
    cX
    cnrest.1
    topopn
    @1
    @21
    @18
    cA
    cX
    cJ
    ssexg
    ancoms
    sylan
    sylan
    adantr
    @0
    @13
    @19
    @1
    @8
    cF
    cJ
    cK
    cnima
    adantlr
    @15
    cA
    cJ
    ctop
    cvv
    elrestr
    syl3anc
    syl5eqel
    ralrimiva
    @2
    @4
    cA
    ctopon
    cfv
    wcel
    #
    cK
    @6
    ctopon
    cfv
    wcel
    #
    @5
    @7
    @11
    wa
    wb
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @1
    @22
    @0
    @17
    @24
    @20
    cJ
    cX
    cnrest.1
    toptopon
    sylib
    cA
    cJ
    cX
    resttopon
    sylan
    @2
    cK
    ctop
    wcel
    #
    @23
    @0
    @25
    @1
    cF
    cJ
    cK
    cntop2
    adantr
    cK
    @6
    @12
    toptopon
    sylib
    vo
    @3
    @4
    cK
    cA
    @6
    iscn
    syl2anc
    mpbir2and
end
