include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "wss.mm"
include "w3a.mm"
include "ctop.mm"
include "cuni.mm"
include "wf.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "crest.mm"
include "wi.mm"
include "cntop1.mm"
include "a1i.mm"
include "wfn.mm"
include "eqid.mm"
include "cnf.mm"
include "ffn.mm"
include "syl.mm"
include "simp2.mm"
include "jctird.mm"
include "df-f.mm"
include "syl6ibr.mm"
include "jcad.mm"
include "adantl.mm"
include "toptopon.mm"
include "sylib.mm"
include "resttopon.mm"
include "3adant2.mm"
include "adantr.mm"
include "simpr.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "jca.mm"
include "ex.mm"
include "wb.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "cin.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl1.mm"
include "toponmax.mm"
include "simpl3.mm"
include "ssexd.mm"
include "elrest.mm"
include "syl2anc.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "ralxfr2d.mm"
include "wfun.mm"
include "simplrr.mm"
include "ffun.mm"
include "inpreima.mm"
include "3syl.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cnvimarndm.mm"
include "sseqtr4i.mm"
include "simpll2.mm"
include "imass2.mm"
include "syl5ss.mm"
include "df-ss.mm"
include "eqtrd.mm"
include "ralbidva.mm"
include "simprr.mm"
include "fssd.mm"
include "biantrurd.mm"
include "3bitrrd.mm"
include "bitrd.mm"
include "simprl.mm"
include "iscn.mm"
include "3bitr4d.mm"
include "pm5.21ndd.mm"

theorem cnrest2
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cY: class Y
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( K e. ( TopOn ` Y ) /\ ran F C_ B /\ B C_ Y ) -> ( F e. ( J Cn K ) <-> F e. ( J Cn ( K |`t B ) ) ) )

  proof
    cK
    cY
    ctopon
    cfv
    #
    wcel
    #
    cF
    crn
    #
    cB
    wss
    #
    cB
    cY
    wss
    #
    w3a
    #
    cJ
    ctop
    wcel
    #
    cJ
    cuni
    #
    cB
    cF
    wf
    #
    wa
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cF
    cJ
    cK
    cB
    crest
    co
    #
    ccn
    co
    wcel
    #
    @5
    @10
    @6
    @8
    @10
    @6
    wi
    @5
    cF
    cJ
    cK
    cntop1
    a1i
    @5
    @10
    cF
    @7
    wfn
    #
    @3
    wa
    @8
    @5
    @10
    @13
    @3
    @10
    @13
    wi
    @5
    @10
    @7
    cK
    cuni
    #
    cF
    wf
    @13
    cF
    cJ
    cK
    @7
    @14
    @7
    eqid
    #
    @14
    eqid
    cnf
    @7
    @14
    cF
    ffn
    syl
    a1i
    @1
    @3
    @4
    simp2
    jctird
    @7
    cB
    cF
    df-f
    syl6ibr
    jcad
    @5
    @12
    @9
    @5
    @12
    wa
    #
    @6
    @8
    @12
    @6
    @5
    cF
    cJ
    @11
    cntop1
    adantl
    #
    @16
    cJ
    @7
    ctopon
    cfv
    wcel
    #
    @11
    cB
    ctopon
    cfv
    wcel
    #
    @12
    @8
    @16
    @6
    @18
    @17
    cJ
    @7
    @15
    toptopon
    #
    sylib
    @5
    @19
    @12
    @1
    @4
    @19
    @3
    cB
    cK
    cY
    resttopon
    3adant2
    #
    adantr
    @5
    @12
    simpr
    cF
    cJ
    @11
    @7
    cB
    cnf2
    syl3anc
    jca
    ex
    @5
    @9
    @10
    @12
    wb
    @5
    @9
    wa
    #
    @7
    cY
    cF
    wf
    #
    cF
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vx
    cK
    wral
    #
    wa
    #
    @8
    @24
    vy
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vy
    @11
    wral
    #
    wa
    #
    @10
    @12
    @22
    @29
    @33
    @34
    @22
    @33
    @24
    @25
    cB
    cin
    #
    cima
    #
    cJ
    wcel
    #
    vx
    cK
    wral
    @28
    @29
    @22
    @32
    @37
    vy
    vx
    @35
    @11
    cK
    cvv
    @35
    cvv
    wcel
    @22
    @25
    cK
    wcel
    #
    wa
    #
    @25
    cB
    vx
    vex
    inex1
    a1i
    @22
    @1
    cB
    cvv
    wcel
    @30
    @11
    wcel
    @30
    @35
    wceq
    #
    vx
    cK
    wrex
    wb
    @1
    @3
    @4
    @9
    simpl1
    #
    @22
    cB
    cY
    cK
    @22
    @1
    cY
    cK
    wcel
    @41
    cY
    cK
    toponmax
    syl
    @1
    @3
    @4
    @9
    simpl3
    #
    ssexd
    vx
    @30
    cB
    cK
    @0
    cvv
    elrest
    syl2anc
    @40
    @32
    @37
    wb
    @22
    @40
    @31
    @36
    cJ
    @30
    @35
    @24
    imaeq2
    eleq1d
    adantl
    ralxfr2d
    @22
    @37
    @27
    vx
    cK
    @39
    @36
    @26
    cJ
    @39
    @36
    @26
    @24
    cB
    cima
    #
    cin
    #
    @26
    @39
    @8
    cF
    wfun
    @36
    @44
    wceq
    @5
    @6
    @8
    @38
    simplrr
    @7
    cB
    cF
    ffun
    @25
    cB
    cF
    inpreima
    3syl
    @39
    @26
    @43
    wss
    @44
    @26
    wceq
    @39
    @26
    @24
    @2
    cima
    #
    @43
    @26
    cF
    cdm
    @45
    cF
    @25
    cnvimass
    cF
    cnvimarndm
    sseqtr4i
    @39
    @3
    @45
    @43
    wss
    @1
    @3
    @4
    @9
    @38
    simpll2
    @2
    cB
    @24
    imass2
    syl
    syl5ss
    @26
    @43
    df-ss
    sylib
    eqtrd
    eleq1d
    ralbidva
    @22
    @23
    @28
    @22
    @7
    cB
    cY
    cF
    @5
    @6
    @8
    simprr
    #
    @42
    fssd
    biantrurd
    3bitrrd
    @22
    @8
    @33
    @46
    biantrurd
    bitrd
    @22
    @18
    @1
    @10
    @29
    wb
    @22
    @6
    @18
    @5
    @6
    @8
    simprl
    @20
    sylib
    #
    @41
    vx
    cF
    cJ
    cK
    @7
    cY
    iscn
    syl2anc
    @22
    @18
    @19
    @12
    @34
    wb
    @47
    @5
    @19
    @9
    @21
    adantr
    vy
    cF
    cJ
    @11
    @7
    cB
    iscn
    syl2anc
    3bitr4d
    ex
    pm5.21ndd
end
