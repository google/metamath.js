include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cxp.mm"
include "ctx.mm"
include "co.mm"
include "ccl.mm"
include "ccld.mm"
include "ctop.mm"
include "cuni.mm"
include "topontop.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "clscld.mm"
include "syl2anc.mm"
include "ad2antlr.mm"
include "simprr.mm"
include "txcld.mm"
include "sscls.mm"
include "xpss12.mm"
include "clsss2.mm"
include "wrel.mm"
include "relxp.mm"
include "a1i.mm"
include "cv.mm"
include "cop.mm"
include "opelxp.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wb.mm"
include "eltx.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "rspccva.mm"
include "wex.mm"
include "simplrl.mm"
include "simprll.mm"
include "simprrl.mm"
include "sylib.mm"
include "simpld.mm"
include "clsndisj.mm"
include "syl32anc.mm"
include "n0.mm"
include "simplrr.mm"
include "simprlr.mm"
include "simprd.mm"
include "eeanv.mm"
include "inss1.mm"
include "opelxpi.mm"
include "inxp.mm"
include "syl6eleqr.mm"
include "sseldi.mm"
include "simprrr.mm"
include "sselda.mm"
include "sylan2.mm"
include "inss2.mm"
include "adantl.mm"
include "inelcm.mm"
include "ex.mm"
include "exlimdvv.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "syl5.mm"
include "expd.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "txtopon.mm"
include "syl.mm"
include "clsss3.mm"
include "sseqtr4d.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eleqtrd.mm"
include "elcls.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "syl5bi.mm"
include "relssdv.mm"
include "eqssd.mm"

theorem txcls
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( R e. ( TopOn ` X ) /\ S e. ( TopOn ` Y ) ) /\ ( A C_ X /\ B C_ Y ) ) -> ( ( cls ` ( R tX S ) ) ` ( A X. B ) ) = ( ( ( cls ` R ) ` A ) X. ( ( cls ` S ) ` B ) ) )

  proof
    cR
    cX
    ctopon
    cfv
    #
    wcel
    #
    cS
    cY
    ctopon
    cfv
    #
    wcel
    #
    wa
    #
    cA
    cX
    wss
    #
    cB
    cY
    wss
    #
    wa
    #
    wa
    #
    cA
    cB
    cxp
    #
    cR
    cS
    ctx
    co
    #
    ccl
    cfv
    cfv
    #
    cA
    cR
    ccl
    cfv
    cfv
    #
    cB
    cS
    ccl
    cfv
    cfv
    #
    cxp
    #
    @8
    @14
    @10
    ccld
    cfv
    wcel
    #
    @9
    @14
    wss
    #
    @11
    @14
    wss
    @8
    @12
    cR
    ccld
    cfv
    wcel
    #
    @13
    cS
    ccld
    cfv
    wcel
    #
    @15
    @8
    cR
    ctop
    wcel
    #
    cA
    cR
    cuni
    #
    wss
    #
    @17
    @1
    @19
    @3
    @7
    cX
    cR
    topontop
    ad2antrr
    #
    @8
    cA
    cX
    @20
    @4
    @5
    @6
    simprl
    @1
    cX
    @20
    wceq
    @3
    @7
    cX
    cR
    toponuni
    ad2antrr
    #
    sseqtrd
    #
    cA
    cR
    @20
    @20
    eqid
    #
    clscld
    syl2anc
    @8
    cS
    ctop
    wcel
    #
    cB
    cS
    cuni
    #
    wss
    #
    @18
    @3
    @26
    @1
    @7
    cY
    cS
    topontop
    ad2antlr
    #
    @8
    cB
    cY
    @27
    @4
    @5
    @6
    simprr
    @3
    cY
    @27
    wceq
    @1
    @7
    cY
    cS
    toponuni
    ad2antlr
    #
    sseqtrd
    #
    cB
    cS
    @27
    @27
    eqid
    #
    clscld
    syl2anc
    @12
    @13
    cR
    cS
    txcld
    syl2anc
    @8
    cA
    @12
    wss
    #
    cB
    @13
    wss
    #
    @16
    @8
    @19
    @21
    @33
    @22
    @24
    cA
    cR
    @20
    @25
    sscls
    syl2anc
    @8
    @26
    @28
    @34
    @29
    @31
    cB
    cS
    @27
    @32
    sscls
    syl2anc
    cA
    @12
    cB
    @13
    xpss12
    syl2anc
    @14
    @9
    @10
    @10
    cuni
    #
    @35
    eqid
    #
    clsss2
    syl2anc
    @8
    vx
    vy
    @14
    @11
    @14
    wrel
    @8
    @12
    @13
    relxp
    a1i
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @14
    wcel
    @37
    @12
    wcel
    #
    @38
    @13
    wcel
    #
    wa
    #
    @8
    @39
    @11
    wcel
    #
    @37
    @38
    @12
    @13
    opelxp
    @8
    @42
    @43
    @8
    @42
    wa
    #
    @43
    @39
    vu
    cv
    #
    wcel
    #
    @45
    @9
    cin
    c0
    wne
    #
    wi
    #
    vu
    @10
    wral
    #
    @44
    @48
    vu
    @10
    @44
    @45
    @10
    wcel
    #
    vz
    cv
    #
    vr
    cv
    #
    vs
    cv
    #
    cxp
    #
    wcel
    #
    @54
    @45
    wss
    #
    wa
    #
    vs
    cS
    wrex
    vr
    cR
    wrex
    #
    vz
    @45
    wral
    #
    @48
    @4
    @50
    @59
    wb
    @7
    @42
    vr
    vs
    @45
    cR
    cS
    @0
    @2
    vz
    eltx
    ad2antrr
    @44
    @59
    @46
    @47
    @59
    @46
    wa
    @39
    @54
    wcel
    #
    @56
    wa
    #
    vs
    cS
    wrex
    vr
    cR
    wrex
    #
    @44
    @47
    @58
    @62
    vz
    @39
    @45
    @51
    @39
    wceq
    #
    @57
    @61
    vr
    vs
    cR
    cS
    @63
    @55
    @60
    @56
    @51
    @39
    @54
    eleq1
    anbi1d
    2rexbidv
    rspccva
    @44
    @61
    @47
    vr
    vs
    cR
    cS
    @44
    @52
    cR
    wcel
    #
    @53
    cS
    wcel
    #
    wa
    #
    @61
    @47
    @44
    @66
    @61
    wa
    #
    wa
    #
    @51
    @52
    cA
    cin
    #
    wcel
    #
    vz
    wex
    #
    vw
    cv
    #
    @53
    cB
    cin
    #
    wcel
    #
    vw
    wex
    #
    @47
    @68
    @69
    c0
    wne
    #
    @71
    @68
    @19
    @21
    @40
    @64
    @37
    @52
    wcel
    #
    @76
    @8
    @19
    @42
    @67
    @22
    ad2antrr
    @8
    @21
    @42
    @67
    @24
    ad2antrr
    @8
    @40
    @41
    @67
    simplrl
    @44
    @64
    @65
    @61
    simprll
    @68
    @77
    @38
    @53
    wcel
    #
    @68
    @60
    @77
    @78
    wa
    @44
    @66
    @60
    @56
    simprrl
    @37
    @38
    @52
    @53
    opelxp
    sylib
    #
    simpld
    @37
    cA
    @52
    cR
    @20
    @25
    clsndisj
    syl32anc
    vz
    @69
    n0
    sylib
    @68
    @73
    c0
    wne
    #
    @75
    @68
    @26
    @28
    @41
    @65
    @78
    @80
    @8
    @26
    @42
    @67
    @29
    ad2antrr
    @8
    @28
    @42
    @67
    @31
    ad2antrr
    @8
    @40
    @41
    @67
    simplrr
    @44
    @64
    @65
    @61
    simprlr
    @68
    @77
    @78
    @79
    simprd
    @38
    cB
    @53
    cS
    @27
    @32
    clsndisj
    syl32anc
    vw
    @73
    n0
    sylib
    @71
    @75
    wa
    @70
    @74
    wa
    #
    vw
    wex
    vz
    wex
    @68
    @47
    @70
    @74
    vz
    vw
    eeanv
    @68
    @81
    @47
    vz
    vw
    @68
    @81
    @47
    @68
    @81
    wa
    @51
    @72
    cop
    #
    @45
    wcel
    #
    @82
    @9
    wcel
    #
    @47
    @81
    @68
    @82
    @54
    wcel
    @83
    @81
    @54
    @9
    cin
    #
    @54
    @82
    @54
    @9
    inss1
    @81
    @82
    @69
    @73
    cxp
    @85
    @51
    @72
    @69
    @73
    opelxpi
    @52
    @53
    cA
    cB
    inxp
    syl6eleqr
    #
    sseldi
    @68
    @54
    @45
    @82
    @44
    @66
    @60
    @56
    simprrr
    sselda
    sylan2
    @81
    @84
    @68
    @81
    @85
    @9
    @82
    @54
    @9
    inss2
    @86
    sseldi
    adantl
    @82
    @45
    @9
    inelcm
    syl2anc
    ex
    exlimdvv
    syl5bir
    mp2and
    expr
    rexlimdvva
    syl5
    expd
    sylbid
    ralrimiv
    @44
    @10
    ctop
    wcel
    #
    @9
    @35
    wss
    @39
    @35
    wcel
    @43
    @49
    wb
    @44
    @10
    cX
    cY
    cxp
    #
    ctopon
    cfv
    wcel
    #
    @87
    @4
    @89
    @7
    @42
    cR
    cS
    cX
    cY
    txtopon
    ad2antrr
    #
    @88
    @10
    topontop
    syl
    @44
    @9
    @88
    @35
    @7
    @9
    @88
    wss
    @4
    @42
    cA
    cX
    cB
    cY
    xpss12
    ad2antlr
    @44
    @89
    @88
    @35
    wceq
    @90
    @88
    @10
    toponuni
    syl
    #
    sseqtrd
    @44
    @39
    @88
    @35
    @44
    @37
    cX
    wcel
    #
    @38
    cY
    wcel
    #
    @39
    @88
    wcel
    @8
    @40
    @92
    @41
    @8
    @12
    cX
    @37
    @8
    @12
    @20
    cX
    @8
    @19
    @21
    @12
    @20
    wss
    @22
    @24
    cA
    cR
    @20
    @25
    clsss3
    syl2anc
    @23
    sseqtr4d
    sselda
    adantrr
    @8
    @41
    @93
    @40
    @8
    @13
    cY
    @38
    @8
    @13
    @27
    cY
    @8
    @26
    @28
    @13
    @27
    wss
    @29
    @31
    cB
    cS
    @27
    @32
    clsss3
    syl2anc
    @30
    sseqtr4d
    sselda
    adantrl
    @37
    @38
    cX
    cY
    opelxpi
    syl2anc
    @91
    eleqtrd
    vu
    @39
    @9
    @10
    @35
    @36
    elcls
    syl3anc
    mpbird
    ex
    syl5bi
    relssdv
    eqssd
end
