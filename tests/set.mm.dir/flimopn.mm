include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wa.mm"
include "cflim.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "elflim.mm"
include "dfss3.mm"
include "ctop.mm"
include "topontop.mm"
include "ad2antrr.mm"
include "opnneip.mm"
include "3expb.mm"
include "sylan.mm"
include "eleq1.mm"
include "rspcv.mm"
include "syl.mm"
include "expr.mm"
include "com23.mm"
include "ralrimdva.mm"
include "cnt.mm"
include "simpr.mm"
include "cuni.mm"
include "wb.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "wceq.mm"
include "toponuni.mm"
include "eleqtrd.mm"
include "snssd.mm"
include "eqid.mm"
include "neii1.mm"
include "neiint.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "snssg.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "ntropn.mm"
include "syl2anc.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "mpid.mm"
include "simpllr.mm"
include "ntrss2.mm"
include "sseqtr4d.mm"
include "filss.mm"
include "3exp2.mm"
include "com24.mm"
include "syl3c.mm"
include "syld.mm"
include "impbid.mm"
include "syl5bb.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem flimopn
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let cG: class G
  let cK: class K

  disjoint A x
  disjoint F x
  disjoint J x
  disjoint X x
  disjoint x y
  disjoint A y
  disjoint F y
  disjoint G x
  disjoint J y
  disjoint K x
  disjoint X y
  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) ) -> ( A e. ( J fLim F ) <-> ( A e. X /\ A. x e. J ( A e. x -> x e. F ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cX
    cfil
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
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    cF
    wss
    #
    wa
    @3
    cA
    vx
    cv
    #
    wcel
    #
    @7
    cF
    wcel
    #
    wi
    #
    vx
    cJ
    wral
    #
    wa
    cA
    cF
    cJ
    cX
    elflim
    @2
    @3
    @6
    @11
    @6
    vy
    cv
    #
    cF
    wcel
    #
    vy
    @5
    wral
    #
    @2
    @3
    wa
    #
    @11
    vy
    @5
    cF
    dfss3
    @15
    @14
    @11
    @15
    @14
    @10
    vx
    cJ
    @15
    @7
    cJ
    wcel
    #
    wa
    @8
    @14
    @9
    @15
    @16
    @8
    @14
    @9
    wi
    #
    @15
    @16
    @8
    wa
    #
    wa
    @7
    @5
    wcel
    #
    @17
    @15
    cJ
    ctop
    wcel
    #
    @18
    @19
    @0
    @20
    @1
    @3
    cX
    cJ
    topontop
    #
    ad2antrr
    #
    @20
    @16
    @8
    @19
    cA
    cJ
    @7
    opnneip
    3expb
    sylan
    @13
    @9
    vy
    @7
    @5
    @12
    @7
    cF
    eleq1
    rspcv
    syl
    expr
    com23
    ralrimdva
    @15
    @11
    @13
    vy
    @5
    @15
    @12
    @5
    wcel
    #
    wa
    #
    @11
    @12
    cJ
    cnt
    cfv
    cfv
    #
    cF
    wcel
    #
    @13
    @24
    @11
    cA
    @25
    wcel
    #
    @26
    @24
    @27
    @4
    @25
    wss
    #
    @24
    @23
    @28
    @15
    @23
    simpr
    @24
    @20
    @4
    cJ
    cuni
    #
    wss
    @12
    @29
    wss
    #
    @23
    @28
    wb
    @0
    @20
    @1
    @3
    @23
    @21
    ad3antrrr
    #
    @24
    cA
    @29
    @24
    cA
    cX
    @29
    @2
    @3
    @23
    simplr
    @0
    cX
    @29
    wceq
    @1
    @3
    @23
    cX
    cJ
    toponuni
    ad3antrrr
    #
    eleqtrd
    snssd
    @15
    @20
    @23
    @30
    @22
    @4
    cJ
    @12
    @29
    @29
    eqid
    #
    neii1
    sylan
    #
    @4
    cJ
    @12
    @29
    @33
    neiint
    syl3anc
    mpbid
    @3
    @27
    @28
    wb
    @2
    @23
    cA
    @25
    cX
    snssg
    ad2antlr
    mpbird
    @24
    @25
    cJ
    wcel
    #
    @11
    @27
    @26
    wi
    #
    wi
    @24
    @20
    @30
    @35
    @31
    @34
    @12
    cJ
    @29
    @33
    ntropn
    syl2anc
    @10
    @36
    vx
    @25
    cJ
    @7
    @25
    wceq
    @8
    @27
    @9
    @26
    @7
    @25
    cA
    eleq2
    @7
    @25
    cF
    eleq1
    imbi12d
    rspcv
    syl
    mpid
    @24
    @1
    @25
    @12
    wss
    #
    @12
    cX
    wss
    #
    @26
    @13
    wi
    @0
    @1
    @3
    @23
    simpllr
    @24
    @20
    @30
    @37
    @31
    @34
    @12
    cJ
    @29
    @33
    ntrss2
    syl2anc
    @24
    @12
    @29
    cX
    @34
    @32
    sseqtr4d
    @1
    @26
    @38
    @37
    @13
    @1
    @26
    @38
    @37
    @13
    @25
    @12
    cF
    cX
    filss
    3exp2
    com24
    syl3c
    syld
    ralrimdva
    impbid
    syl5bb
    pm5.32da
    bitrd
end
