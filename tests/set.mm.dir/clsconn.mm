include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "w3a.mm"
include "ccl.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cdif.mm"
include "cun.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "simpll3.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simplrl.mm"
include "simplrr.mm"
include "wex.mm"
include "simprl1.mm"
include "n0.mm"
include "sylib.mm"
include "ctop.mm"
include "cuni.mm"
include "adantr.mm"
include "topontop.mm"
include "syl.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "inss1.mm"
include "eqid.mm"
include "clsndisj.mm"
include "syl32anc.mm"
include "exlimddv.mm"
include "simprl2.mm"
include "cvv.mm"
include "simprl3.mm"
include "sscls.mm"
include "syl2anc.mm"
include "sscond.mm"
include "sstrd.mm"
include "ssv.mm"
include "ssdif.mm"
include "ax-mp.mm"
include "syl6ss.mm"
include "disj2.mm"
include "sylibr.mm"
include "simprr.mm"
include "nconnsubb.mm"
include "expr.mm"
include "mt2d.mm"
include "ex.mm"
include "ralrimivva.mm"
include "wb.mm"
include "simp1.mm"
include "sseq2d.mm"
include "biimpa.mm"
include "clsss3.mm"
include "sylan.mm"
include "syldan.mm"
include "sseqtr4d.mm"
include "3adant3.mm"
include "connsub.mm"
include "mpbird.mm"

theorem clsconn
  let cA: class A
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cT: class T


  assert |- ( ( J e. ( TopOn ` X ) /\ A C_ X /\ ( J |`t A ) e. Conn ) -> ( J |`t ( ( cls ` J ) ` A ) ) e. Conn )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wss
    #
    cJ
    cA
    crest
    co
    cconn
    wcel
    #
    w3a
    #
    cJ
    cA
    cJ
    ccl
    cfv
    cfv
    #
    crest
    co
    cconn
    wcel
    #
    vx
    cv
    #
    @4
    cin
    #
    c0
    wne
    #
    vy
    cv
    #
    @4
    cin
    #
    c0
    wne
    #
    @6
    @9
    cin
    #
    cX
    @4
    cdif
    #
    wss
    #
    w3a
    #
    @4
    @6
    @9
    cun
    #
    wss
    #
    wn
    #
    wi
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    #
    @3
    @19
    vx
    vy
    cJ
    cJ
    @3
    @6
    cJ
    wcel
    #
    @9
    cJ
    wcel
    #
    wa
    #
    wa
    #
    @15
    @18
    @24
    @15
    wa
    @17
    @2
    @0
    @1
    @2
    @23
    @15
    simpll3
    @24
    @15
    @17
    @2
    wn
    @24
    @15
    @17
    wa
    #
    wa
    #
    cA
    @6
    cJ
    @9
    cX
    @0
    @1
    @2
    @23
    @25
    simpll1
    #
    @0
    @1
    @2
    @23
    @25
    simpll2
    #
    @3
    @21
    @22
    @25
    simplrl
    #
    @3
    @21
    @22
    @25
    simplrr
    #
    @26
    vz
    cv
    #
    @7
    wcel
    #
    @6
    cA
    cin
    c0
    wne
    #
    vz
    @26
    @8
    @32
    vz
    wex
    @8
    @11
    @14
    @17
    @24
    simprl1
    vz
    @7
    n0
    sylib
    @26
    @32
    wa
    #
    cJ
    ctop
    wcel
    #
    cA
    cJ
    cuni
    #
    wss
    #
    @31
    @4
    wcel
    #
    @21
    @31
    @6
    wcel
    @33
    @34
    @0
    @35
    @26
    @0
    @32
    @27
    adantr
    #
    cX
    cJ
    topontop
    #
    syl
    @34
    cA
    cX
    @36
    @26
    @1
    @32
    @28
    adantr
    @34
    @0
    cX
    @36
    wceq
    #
    @39
    cX
    cJ
    toponuni
    #
    syl
    sseqtrd
    @34
    @7
    @4
    @31
    @6
    @4
    inss2
    @26
    @32
    simpr
    #
    sseldi
    @26
    @21
    @32
    @29
    adantr
    @34
    @7
    @6
    @31
    @6
    @4
    inss1
    @43
    sseldi
    @31
    cA
    @6
    cJ
    @36
    @36
    eqid
    #
    clsndisj
    syl32anc
    exlimddv
    @26
    @31
    @10
    wcel
    #
    @9
    cA
    cin
    c0
    wne
    #
    vz
    @26
    @11
    @45
    vz
    wex
    @8
    @11
    @14
    @17
    @24
    simprl2
    vz
    @10
    n0
    sylib
    @26
    @45
    wa
    #
    @35
    @37
    @38
    @22
    @31
    @9
    wcel
    @46
    @47
    @0
    @35
    @26
    @0
    @45
    @27
    adantr
    #
    @40
    syl
    @47
    cA
    cX
    @36
    @26
    @1
    @45
    @28
    adantr
    @47
    @0
    @41
    @48
    @42
    syl
    sseqtrd
    @47
    @10
    @4
    @31
    @9
    @4
    inss2
    @26
    @45
    simpr
    #
    sseldi
    @26
    @22
    @45
    @30
    adantr
    @47
    @10
    @9
    @31
    @9
    @4
    inss1
    @49
    sseldi
    @31
    cA
    @9
    cJ
    @36
    @44
    clsndisj
    syl32anc
    exlimddv
    @26
    @12
    cvv
    cA
    cdif
    #
    wss
    @12
    cA
    cin
    c0
    wceq
    @26
    @12
    cX
    cA
    cdif
    #
    @50
    @26
    @12
    @13
    @51
    @8
    @11
    @14
    @17
    @24
    simprl3
    @26
    cA
    @4
    cX
    @26
    @35
    @37
    cA
    @4
    wss
    @26
    @0
    @35
    @27
    @40
    syl
    @26
    cA
    cX
    @36
    @28
    @26
    @0
    @41
    @27
    @42
    syl
    sseqtrd
    cA
    cJ
    @36
    @44
    sscls
    syl2anc
    #
    sscond
    sstrd
    cX
    cvv
    wss
    @51
    @50
    wss
    cX
    ssv
    cX
    cvv
    cA
    ssdif
    ax-mp
    syl6ss
    @12
    cA
    disj2
    sylibr
    @26
    cA
    @4
    @16
    @52
    @24
    @15
    @17
    simprr
    sstrd
    nconnsubb
    expr
    mt2d
    ex
    ralrimivva
    @3
    @0
    @4
    cX
    wss
    #
    @5
    @20
    wb
    @0
    @1
    @2
    simp1
    @0
    @1
    @53
    @2
    @0
    @1
    wa
    @4
    @36
    cX
    @0
    @1
    @37
    @4
    @36
    wss
    #
    @0
    @1
    @37
    @0
    cX
    @36
    cA
    @42
    sseq2d
    biimpa
    @0
    @35
    @37
    @54
    @40
    cA
    cJ
    @36
    @44
    clsss3
    sylan
    syldan
    @0
    @41
    @1
    @42
    adantr
    sseqtr4d
    3adant3
    vx
    vy
    @4
    cJ
    cX
    connsub
    syl2anc
    mpbird
end
