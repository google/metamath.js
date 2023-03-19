include "cn0.mm"
include "wcel.mm"
include "crelexp.mm"
include "co.mm"
include "cc0.mm"
include "wss.mm"
include "cn.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elnn0.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "relexp1g.mm"
include "ssid.mm"
include "syl6eqss.mm"
include "w3a.mm"
include "ccom.mm"
include "simp2.mm"
include "simp1.mm"
include "wa.mm"
include "relexpsucnnr.mm"
include "syl2anc.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "cvv.mm"
include "ovex.mm"
include "coexg.mm"
include "mpan.mm"
include "relexp0g.mm"
include "syl.mm"
include "dmcoss.mm"
include "rncoss.mm"
include "unss12.mm"
include "mp2an.mm"
include "ssres2.mm"
include "ax-mp.mm"
include "resundi.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "adantr.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "simpr.mm"
include "syl5ss.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "3adant1.mm"
include "sstrd.mm"
include "eqsstrd.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"
include "relexp0idm.mm"
include "sylan9eq.mm"
include "eqimss.mm"
include "ex.mm"
include "jaoi.mm"
include "sylbi.mm"
include "impcom.mm"

theorem relexp0a
  let cA: class A
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ N e. NN0 ) -> ( ( A ^r N ) ^r 0 ) C_ ( A ^r 0 ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cV
    wcel
    #
    cA
    cN
    crelexp
    co
    #
    cc0
    crelexp
    co
    #
    cA
    cc0
    crelexp
    co
    #
    wss
    #
    @0
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @1
    @5
    wi
    #
    cN
    elnn0
    @6
    @8
    @7
    @1
    cA
    vx
    cv
    #
    crelexp
    co
    #
    cc0
    crelexp
    co
    #
    @4
    wss
    #
    wi
    @1
    cA
    c1
    crelexp
    co
    #
    cc0
    crelexp
    co
    #
    @4
    wss
    #
    wi
    @1
    cA
    vy
    cv
    #
    crelexp
    co
    #
    cc0
    crelexp
    co
    #
    @4
    wss
    #
    wi
    @1
    cA
    @16
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cc0
    crelexp
    co
    #
    @4
    wss
    #
    wi
    @8
    vx
    vy
    cN
    @9
    c1
    wceq
    #
    @12
    @15
    @1
    @24
    @11
    @14
    @4
    @24
    @10
    @13
    cc0
    crelexp
    @9
    c1
    cA
    crelexp
    oveq2
    oveq1d
    sseq1d
    imbi2d
    vx
    vy
    weq
    #
    @12
    @19
    @1
    @25
    @11
    @18
    @4
    @25
    @10
    @17
    cc0
    crelexp
    @9
    @16
    cA
    crelexp
    oveq2
    oveq1d
    sseq1d
    imbi2d
    @9
    @20
    wceq
    #
    @12
    @23
    @1
    @26
    @11
    @22
    @4
    @26
    @10
    @21
    cc0
    crelexp
    @9
    @20
    cA
    crelexp
    oveq2
    oveq1d
    sseq1d
    imbi2d
    @9
    cN
    wceq
    #
    @12
    @5
    @1
    @27
    @11
    @3
    @4
    @27
    @10
    @2
    cc0
    crelexp
    @9
    cN
    cA
    crelexp
    oveq2
    oveq1d
    sseq1d
    imbi2d
    @1
    @14
    @4
    @4
    @1
    @13
    cA
    cc0
    crelexp
    cA
    cV
    relexp1g
    oveq1d
    @4
    ssid
    syl6eqss
    @16
    cn
    wcel
    #
    @1
    @19
    @23
    @28
    @1
    @19
    @23
    @28
    @1
    @19
    w3a
    #
    @22
    @17
    cA
    ccom
    #
    cc0
    crelexp
    co
    #
    @4
    @29
    @1
    @28
    @22
    @31
    wceq
    @28
    @1
    @19
    simp2
    #
    @28
    @1
    @19
    simp1
    @1
    @28
    wa
    @21
    @30
    cc0
    crelexp
    cA
    @16
    cV
    relexpsucnnr
    oveq1d
    syl2anc
    @29
    @31
    cid
    cA
    cdm
    #
    @17
    crn
    #
    cun
    #
    cres
    #
    @4
    @29
    @1
    @31
    @36
    wss
    @32
    @1
    @31
    cid
    @30
    cdm
    #
    @30
    crn
    #
    cun
    #
    cres
    #
    @36
    @1
    @30
    cvv
    wcel
    #
    @31
    @40
    wceq
    @17
    cvv
    wcel
    #
    @1
    @41
    cA
    @16
    crelexp
    ovex
    #
    @17
    cA
    cvv
    cV
    coexg
    mpan
    @30
    cvv
    relexp0g
    syl
    @39
    @35
    wss
    #
    @40
    @36
    wss
    @37
    @33
    wss
    @38
    @34
    wss
    @44
    @17
    cA
    dmcoss
    @17
    cA
    rncoss
    @37
    @33
    @38
    @34
    unss12
    mp2an
    @39
    @35
    cid
    ssres2
    ax-mp
    syl6eqss
    syl
    @1
    @19
    @36
    @4
    wss
    @28
    @1
    @19
    wa
    #
    @36
    cid
    @33
    cres
    #
    cid
    @34
    cres
    #
    cun
    @4
    cid
    @33
    @34
    resundi
    @45
    @46
    @47
    @4
    @1
    @46
    @4
    wss
    @19
    @1
    cid
    @33
    cA
    crn
    #
    cun
    #
    cres
    #
    @46
    @4
    @33
    @49
    wss
    @46
    @50
    wss
    @33
    @48
    ssun1
    @33
    @49
    cid
    ssres2
    ax-mp
    cA
    cV
    relexp0g
    syl5sseqr
    adantr
    @45
    @47
    @18
    @4
    @47
    cid
    @17
    cdm
    #
    @34
    cun
    #
    cres
    #
    @18
    @34
    @52
    wss
    @47
    @53
    wss
    @34
    @51
    ssun2
    @34
    @52
    cid
    ssres2
    ax-mp
    @42
    @18
    @53
    wceq
    @43
    @17
    cvv
    relexp0g
    ax-mp
    sseqtr4i
    @1
    @19
    simpr
    syl5ss
    unssd
    syl5eqss
    3adant1
    sstrd
    eqsstrd
    3exp
    a2d
    nnind
    @7
    @1
    @5
    @7
    @1
    wa
    @3
    @4
    wceq
    @5
    @7
    @1
    @3
    @4
    cc0
    crelexp
    co
    @4
    @7
    @2
    @4
    cc0
    crelexp
    cN
    cc0
    cA
    crelexp
    oveq2
    oveq1d
    cA
    cV
    relexp0idm
    sylan9eq
    @3
    @4
    eqimss
    syl
    ex
    jaoi
    sylbi
    impcom
end
