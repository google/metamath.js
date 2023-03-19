include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "ccnv.mm"
include "wceq.mm"
include "ctx.mm"
include "co.mm"
include "ccl.mm"
include "ccom.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wrel.mm"
include "relxp.mm"
include "cuni.mm"
include "ctop.mm"
include "cutop.mm"
include "utoptop.mm"
include "syl5eqel.mm"
include "txtop.mm"
include "syl2anc.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "ctopon.mm"
include "utoptopon.mm"
include "toponuni.mm"
include "syl.mm"
include "sqxpeqd.mm"
include "eqid.mm"
include "txuni.mm"
include "eqtrd.mm"
include "sseqtrd.mm"
include "clsss3.mm"
include "sseqtr4d.mm"
include "simpr.mm"
include "sseldd.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "wbr.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "wral.mm"
include "simp-4l.mm"
include "simpr1l.mm"
include "3anassrs.mm"
include "ustrel.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "xp1st.mm"
include "elrelimasn.mm"
include "biimpa.mm"
include "cvv.mm"
include "simp-4r.mm"
include "xpss.mm"
include "syl6ss.mm"
include "df-rel.mm"
include "sylibr.mm"
include "simprd.mm"
include "1st2ndbr.mm"
include "xp2nd.mm"
include "wb.mm"
include "simpr1r.mm"
include "fvex.mm"
include "brcnv.mm"
include "breq.mm"
include "syl5rbbr.mm"
include "mpbird.mm"
include "wi.mm"
include "w3a.mm"
include "brcogw.mm"
include "ex.mm"
include "mp3an.mm"
include "sylan.mm"
include "syl21anc.mm"
include "ralrimiva.mm"
include "c0.mm"
include "wne.mm"
include "cnei.mm"
include "simplll.mm"
include "simplrl.mm"
include "3ad2ant1.mm"
include "utopsnnei.mm"
include "syl3an3.mm"
include "neitx.mm"
include "syl22anc.mm"
include "1st2nd2.mm"
include "sneqd.mm"
include "xpsn.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "3ad2ant3.mm"
include "eleqtrrd.mm"
include "syl3anc.mm"
include "neindisj.mm"
include "r19.3rzv.mm"
include "df-br.mm"
include "eqeltrd.mm"
include "ssrdv.mm"

theorem utop3cls
  let cU: class U
  let cJ: class J
  let cM: class M
  let cV: class V
  let cX: class X
  let vp: setvar p
  let vv: setvar v
  let cP: class P
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let vr: setvar r
  let vz: setvar z
  assume utoptop.1: |- J = ( unifTop ` U )


  assert |- ( ( ( U e. ( UnifOn ` X ) /\ M C_ ( X X. X ) ) /\ ( V e. U /\ `' V = V ) ) -> ( ( cls ` ( J tX J ) ) ` M ) C_ ( V o. ( M o. V ) ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cM
    cX
    cX
    cxp
    #
    wss
    #
    wa
    #
    cV
    cU
    wcel
    #
    cV
    ccnv
    #
    cV
    wceq
    #
    wa
    #
    wa
    #
    vz
    cM
    cJ
    cJ
    ctx
    co
    #
    ccl
    cfv
    cfv
    #
    cV
    cM
    cV
    ccom
    #
    ccom
    #
    @8
    vz
    cv
    #
    @10
    wcel
    #
    @13
    @12
    wcel
    @8
    @14
    wa
    #
    @13
    @13
    c1st
    cfv
    #
    @13
    c2nd
    cfv
    #
    cop
    #
    @12
    @15
    @1
    wrel
    @13
    @1
    wcel
    #
    @13
    @18
    wceq
    cX
    cX
    relxp
    @15
    @10
    @1
    @13
    @15
    @10
    @9
    cuni
    #
    @1
    @15
    @9
    ctop
    wcel
    #
    cM
    @20
    wss
    #
    @10
    @20
    wss
    @0
    @21
    @2
    @7
    @14
    @0
    cJ
    ctop
    wcel
    #
    @23
    @21
    @0
    cJ
    cU
    cutop
    cfv
    #
    ctop
    utoptop.1
    cU
    cX
    utoptop
    syl5eqel
    #
    @25
    cJ
    cJ
    txtop
    syl2anc
    ad3antrrr
    #
    @15
    cM
    @1
    @20
    @0
    @2
    @7
    @14
    simpllr
    @0
    @1
    @20
    wceq
    @2
    @7
    @14
    @0
    @1
    cJ
    cuni
    #
    @27
    cxp
    #
    @20
    @0
    cX
    @27
    @0
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    cX
    @27
    wceq
    @0
    cJ
    @24
    @29
    utoptop.1
    cU
    cX
    utoptopon
    syl5eqel
    cX
    cJ
    toponuni
    syl
    sqxpeqd
    @0
    @23
    @23
    @28
    @20
    wceq
    @25
    @25
    cJ
    cJ
    @27
    @27
    @27
    eqid
    #
    @30
    txuni
    syl2anc
    eqtrd
    ad3antrrr
    #
    sseqtrd
    #
    cM
    @9
    @20
    @20
    eqid
    #
    clsss3
    syl2anc
    @31
    sseqtr4d
    @8
    @14
    simpr
    #
    sseldd
    #
    @13
    @1
    1st2nd
    sylancr
    @15
    @16
    @17
    @12
    wbr
    #
    @18
    @12
    wcel
    @15
    @36
    @36
    vr
    cV
    @16
    csn
    #
    cima
    #
    cV
    @17
    csn
    #
    cima
    #
    cxp
    #
    cM
    cin
    #
    wral
    #
    @15
    @36
    vr
    @42
    @15
    vr
    cv
    #
    @42
    wcel
    #
    wa
    #
    @16
    @44
    c1st
    cfv
    #
    cV
    wbr
    #
    @47
    @44
    c2nd
    cfv
    #
    cM
    wbr
    #
    @49
    @17
    cV
    wbr
    #
    @36
    @46
    cV
    wrel
    #
    @47
    @38
    wcel
    #
    @48
    @46
    @0
    @4
    @52
    @0
    @2
    @7
    @14
    @45
    simp-4l
    @3
    @7
    @14
    @45
    @4
    @4
    @6
    @14
    @45
    @3
    simpr1l
    3anassrs
    cU
    cV
    cX
    ustrel
    syl2anc
    #
    @46
    @44
    @41
    wcel
    #
    @53
    @46
    @55
    @44
    cM
    wcel
    #
    @46
    @45
    @55
    @56
    wa
    @15
    @45
    simpr
    @44
    @41
    cM
    elin
    sylib
    #
    simpld
    #
    @44
    @38
    @40
    xp1st
    syl
    @52
    @53
    @48
    @16
    @47
    cV
    elrelimasn
    biimpa
    syl2anc
    @46
    cM
    wrel
    #
    @56
    @50
    @46
    cM
    cvv
    cvv
    cxp
    #
    wss
    @59
    @46
    cM
    @1
    @60
    @0
    @2
    @7
    @14
    @45
    simp-4r
    cX
    cX
    xpss
    syl6ss
    cM
    df-rel
    sylibr
    @46
    @55
    @56
    @57
    simprd
    @44
    cM
    1st2ndbr
    syl2anc
    @46
    @51
    @17
    @49
    cV
    wbr
    #
    @46
    @52
    @49
    @40
    wcel
    #
    @61
    @54
    @46
    @55
    @62
    @58
    @44
    @38
    @40
    xp2nd
    syl
    @52
    @62
    @61
    @17
    @49
    cV
    elrelimasn
    biimpa
    syl2anc
    @46
    @6
    @51
    @61
    wb
    @3
    @7
    @14
    @45
    @6
    @4
    @6
    @14
    @45
    @3
    simpr1r
    3anassrs
    @61
    @49
    @17
    @5
    wbr
    @6
    @51
    @49
    @17
    cV
    @44
    c2nd
    fvex
    #
    @13
    c2nd
    fvex
    #
    brcnv
    @49
    @17
    @5
    cV
    breq
    syl5rbbr
    syl
    mpbird
    @48
    @50
    wa
    #
    @16
    @49
    @11
    wbr
    #
    @51
    @36
    @16
    cvv
    wcel
    #
    @49
    cvv
    wcel
    #
    @47
    cvv
    wcel
    #
    @65
    @66
    wi
    @13
    c1st
    fvex
    #
    @63
    @44
    c1st
    fvex
    @67
    @68
    @69
    w3a
    @65
    @66
    @16
    @49
    cM
    cV
    cvv
    cvv
    @47
    cvv
    brcogw
    ex
    mp3an
    @67
    @17
    cvv
    wcel
    #
    @68
    @66
    @51
    wa
    #
    @36
    wi
    @70
    @64
    @63
    @67
    @71
    @68
    w3a
    @72
    @36
    @16
    @17
    cV
    @11
    cvv
    cvv
    @49
    cvv
    brcogw
    ex
    mp3an
    sylan
    syl21anc
    ralrimiva
    @15
    @42
    c0
    wne
    #
    @36
    @43
    wb
    @15
    @21
    @22
    @14
    @41
    @13
    csn
    #
    @9
    cnei
    cfv
    #
    cfv
    #
    wcel
    #
    @73
    @26
    @32
    @34
    @15
    @0
    @4
    @19
    @77
    @0
    @2
    @7
    @14
    simplll
    @3
    @4
    @6
    @14
    simplrl
    @35
    @0
    @4
    @19
    w3a
    #
    @41
    @37
    @39
    cxp
    #
    @75
    cfv
    #
    @76
    @78
    @23
    @23
    @38
    @37
    cJ
    cnei
    cfv
    #
    cfv
    wcel
    #
    @40
    @39
    @81
    cfv
    wcel
    #
    @41
    @80
    wcel
    @0
    @4
    @23
    @19
    @25
    3ad2ant1
    #
    @84
    @19
    @0
    @4
    @16
    cX
    wcel
    @82
    @13
    cX
    cX
    xp1st
    @16
    cU
    cJ
    cV
    cX
    utoptop.1
    utopsnnei
    syl3an3
    @19
    @0
    @4
    @17
    cX
    wcel
    @83
    @13
    cX
    cX
    xp2nd
    @17
    cU
    cJ
    cV
    cX
    utoptop.1
    utopsnnei
    syl3an3
    @38
    @40
    @37
    @39
    cJ
    cJ
    @27
    @27
    @30
    @30
    neitx
    syl22anc
    @19
    @0
    @76
    @80
    wceq
    @4
    @19
    @74
    @79
    @75
    @19
    @74
    @18
    csn
    @79
    @19
    @13
    @18
    @13
    cX
    cX
    1st2nd2
    sneqd
    @16
    @17
    @70
    @64
    xpsn
    syl6eqr
    fveq2d
    3ad2ant3
    eleqtrrd
    syl3anc
    @13
    cM
    @9
    @41
    @20
    @33
    neindisj
    syl22anc
    @36
    vr
    @42
    r19.3rzv
    syl
    mpbird
    @16
    @17
    @12
    df-br
    sylib
    eqeltrd
    ex
    ssrdv
end
