include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "ccnv.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "wss.mm"
include "w3a.mm"
include "ccom.mm"
include "ctx.mm"
include "co.mm"
include "cnei.mm"
include "c0.mm"
include "ctop.mm"
include "cutop.mm"
include "utoptop.mm"
include "syl5eqel.mm"
include "txtop.mm"
include "syl2anc.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "0nei.mm"
include "syl.mm"
include "coeq1.mm"
include "co01.mm"
include "syl6eq.mm"
include "coeq2d.mm"
include "co02.mm"
include "adantl.mm"
include "simpr.mm"
include "fveq2d.mm"
include "3eltr4d.mm"
include "wne.mm"
include "cv.mm"
include "csn.mm"
include "wral.mm"
include "c1st.mm"
include "cima.mm"
include "c2nd.mm"
include "cuni.mm"
include "cop.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simp3.mm"
include "sselda.mm"
include "xp1st.mm"
include "utopsnnei.mm"
include "syl3anc.mm"
include "xp2nd.mm"
include "eqid.mm"
include "neitx.mm"
include "syl22anc.mm"
include "fvex.mm"
include "xpsn.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "wrel.mm"
include "cvv.mm"
include "xpss.mm"
include "sstr.mm"
include "mpan2.mm"
include "df-rel.mm"
include "sylibr.mm"
include "1st2nd.mm"
include "sylancom.mm"
include "sneqd.mm"
include "eleqtrrd.mm"
include "relxp.mm"
include "a1i.mm"
include "wbr.mm"
include "simpll2.mm"
include "simprd.mm"
include "simpll1.mm"
include "simpld.mm"
include "ustrel.mm"
include "elrelimasn.mm"
include "biimpa.mm"
include "brcnv.mm"
include "breq.mm"
include "syl5bbr.mm"
include "biimpar.mm"
include "simpll3.mm"
include "simplr.mm"
include "1st2ndbr.mm"
include "sylan.mm"
include "3pm3.2i.mm"
include "brcogw.mm"
include "mpan.mm"
include "syl21anc.mm"
include "df-br.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "ex.mm"
include "ssrdv.mm"
include "simp1.mm"
include "simp2l.mm"
include "ustssxp.mm"
include "coss1.mm"
include "coss2.mm"
include "xpcoid.mm"
include "syl6sseq.mm"
include "sstrd.mm"
include "utopbas.mm"
include "unieqi.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "txuni.mm"
include "eqtrd.mm"
include "sseqtrd.mm"
include "ssnei2.mm"
include "ralrimiva.mm"
include "wb.mm"
include "neips.mm"
include "mpbird.mm"
include "pm2.61dane.mm"

theorem utop2nei
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


  assert |- ( ( U e. ( UnifOn ` X ) /\ ( V e. U /\ `' V = V ) /\ M C_ ( X X. X ) ) -> ( V o. ( M o. V ) ) e. ( ( nei ` ( J tX J ) ) ` M ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
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
    cM
    cX
    cX
    cxp
    #
    wss
    #
    w3a
    #
    cV
    cM
    cV
    ccom
    #
    ccom
    #
    cM
    cJ
    cJ
    ctx
    co
    #
    cnei
    cfv
    #
    cfv
    #
    wcel
    #
    cM
    c0
    @7
    cM
    c0
    wceq
    #
    wa
    #
    c0
    c0
    @11
    cfv
    #
    @9
    @12
    @15
    @10
    ctop
    wcel
    #
    c0
    @16
    wcel
    @7
    @17
    @14
    @0
    @4
    @17
    @6
    @0
    cJ
    ctop
    wcel
    #
    @18
    @17
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
    @20
    cJ
    cJ
    txtop
    syl2anc
    3ad2ant1
    #
    adantr
    @10
    0nei
    syl
    @14
    @9
    c0
    wceq
    @7
    @14
    @9
    cV
    c0
    ccom
    c0
    @14
    @8
    c0
    cV
    @14
    @8
    c0
    cV
    ccom
    c0
    cM
    c0
    cV
    coeq1
    cV
    co01
    syl6eq
    coeq2d
    cV
    co02
    syl6eq
    adantl
    @15
    cM
    c0
    @11
    @7
    @14
    simpr
    fveq2d
    3eltr4d
    @7
    cM
    c0
    wne
    #
    wa
    #
    @13
    @9
    vr
    cv
    #
    csn
    #
    @11
    cfv
    #
    wcel
    #
    vr
    cM
    wral
    #
    @7
    @28
    @22
    @7
    @27
    vr
    cM
    @7
    @24
    cM
    wcel
    #
    wa
    #
    @17
    cV
    @24
    c1st
    cfv
    #
    csn
    #
    cima
    #
    cV
    @24
    c2nd
    cfv
    #
    csn
    #
    cima
    #
    cxp
    #
    @26
    wcel
    @37
    @9
    wss
    @9
    @10
    cuni
    #
    wss
    #
    @27
    @7
    @17
    @29
    @21
    adantr
    @30
    @37
    @31
    @34
    cop
    #
    csn
    #
    @11
    cfv
    #
    @26
    @30
    @37
    @32
    @35
    cxp
    #
    @11
    cfv
    #
    @42
    @30
    @18
    @18
    @33
    @32
    cJ
    cnei
    cfv
    #
    cfv
    wcel
    #
    @36
    @35
    @45
    cfv
    wcel
    #
    @37
    @44
    wcel
    @30
    @0
    @18
    @0
    @4
    @6
    @29
    simpl1
    #
    @20
    syl
    #
    @49
    @30
    @0
    @1
    @31
    cX
    wcel
    #
    @46
    @48
    @1
    @3
    @0
    @6
    @29
    simpl2l
    #
    @30
    @24
    @5
    wcel
    #
    @50
    @7
    cM
    @5
    @24
    @0
    @4
    @6
    simp3
    #
    sselda
    #
    @24
    cX
    cX
    xp1st
    syl
    @31
    cU
    cJ
    cV
    cX
    utoptop.1
    utopsnnei
    syl3anc
    @30
    @0
    @1
    @34
    cX
    wcel
    #
    @47
    @48
    @51
    @30
    @52
    @55
    @54
    @24
    cX
    cX
    xp2nd
    syl
    @34
    cU
    cJ
    cV
    cX
    utoptop.1
    utopsnnei
    syl3anc
    @33
    @36
    @32
    @35
    cJ
    cJ
    cJ
    cuni
    #
    @56
    @56
    eqid
    #
    @57
    neitx
    syl22anc
    @43
    @41
    @11
    @31
    @34
    @24
    c1st
    fvex
    #
    @24
    c2nd
    fvex
    #
    xpsn
    fveq2i
    syl6eleq
    @30
    @25
    @41
    @11
    @30
    @24
    @40
    @7
    @29
    cM
    wrel
    #
    @24
    @40
    wceq
    @30
    @6
    @60
    @7
    @6
    @29
    @53
    adantr
    @6
    cM
    cvv
    cvv
    cxp
    #
    wss
    #
    @60
    @6
    @5
    @61
    wss
    @62
    cX
    cX
    xpss
    cM
    @5
    @61
    sstr
    mpan2
    cM
    df-rel
    sylibr
    #
    syl
    @24
    cM
    1st2nd
    sylancom
    sneqd
    fveq2d
    eleqtrrd
    @30
    vz
    @37
    @9
    @30
    vz
    cv
    #
    @37
    wcel
    #
    @64
    @9
    wcel
    @30
    @65
    wa
    #
    @64
    @64
    c1st
    cfv
    #
    @64
    c2nd
    cfv
    #
    cop
    #
    @9
    @30
    @65
    @37
    wrel
    #
    @64
    @69
    wceq
    @70
    @66
    @33
    @36
    relxp
    a1i
    @64
    @37
    1st2nd
    sylancom
    @66
    @67
    @68
    @9
    wbr
    #
    @69
    @9
    wcel
    @66
    @67
    @31
    cV
    wbr
    #
    @31
    @34
    cM
    wbr
    #
    @34
    @68
    cV
    wbr
    #
    @71
    @66
    @3
    @31
    @67
    cV
    wbr
    #
    @72
    @66
    @1
    @3
    @0
    @4
    @6
    @29
    @65
    simpll2
    #
    simprd
    @66
    cV
    wrel
    #
    @67
    @33
    wcel
    #
    @75
    @66
    @0
    @1
    @77
    @0
    @4
    @6
    @29
    @65
    simpll1
    @66
    @1
    @3
    @76
    simpld
    cU
    cV
    cX
    ustrel
    syl2anc
    #
    @65
    @78
    @30
    @64
    @33
    @36
    xp1st
    adantl
    @77
    @78
    @75
    @31
    @67
    cV
    elrelimasn
    biimpa
    syl2anc
    @3
    @72
    @75
    @72
    @31
    @67
    @2
    wbr
    @3
    @75
    @31
    @67
    cV
    @58
    @64
    c1st
    fvex
    #
    brcnv
    @31
    @67
    @2
    cV
    breq
    syl5bbr
    biimpar
    syl2anc
    @66
    @6
    @29
    @73
    @0
    @4
    @6
    @29
    @65
    simpll3
    @7
    @29
    @65
    simplr
    @6
    @60
    @29
    @73
    @63
    @24
    cM
    1st2ndbr
    sylan
    syl2anc
    @66
    @77
    @68
    @36
    wcel
    #
    @74
    @79
    @65
    @81
    @30
    @64
    @33
    @36
    xp2nd
    adantl
    @77
    @81
    @74
    @34
    @68
    cV
    elrelimasn
    biimpa
    syl2anc
    @72
    @73
    wa
    #
    @67
    @34
    @8
    wbr
    #
    @74
    @71
    @67
    cvv
    wcel
    #
    @34
    cvv
    wcel
    #
    @31
    cvv
    wcel
    #
    w3a
    @82
    @83
    @84
    @85
    @86
    @80
    @59
    @58
    3pm3.2i
    @67
    @34
    cM
    cV
    cvv
    cvv
    @31
    cvv
    brcogw
    mpan
    @84
    @68
    cvv
    wcel
    #
    @85
    w3a
    @83
    @74
    wa
    @71
    @84
    @87
    @85
    @80
    @64
    c2nd
    fvex
    @59
    3pm3.2i
    @67
    @68
    cV
    @8
    cvv
    cvv
    @34
    cvv
    brcogw
    mpan
    sylan
    syl21anc
    @67
    @68
    @9
    df-br
    sylib
    eqeltrd
    ex
    ssrdv
    @7
    @39
    @29
    @7
    @9
    @5
    @38
    @7
    @9
    @5
    @8
    ccom
    #
    @5
    @7
    cV
    @5
    wss
    #
    @9
    @88
    wss
    @7
    @0
    @1
    @89
    @0
    @4
    @6
    simp1
    @0
    @1
    @3
    @6
    simp2l
    cU
    cV
    cX
    ustssxp
    syl2anc
    #
    cV
    @5
    @8
    coss1
    syl
    @7
    @8
    @5
    wss
    #
    @88
    @5
    wss
    @7
    @8
    @5
    cV
    ccom
    #
    @5
    @7
    @6
    @8
    @92
    wss
    @53
    cM
    @5
    cV
    coss1
    syl
    @7
    @89
    @92
    @5
    wss
    @90
    @89
    @92
    @5
    @5
    ccom
    #
    @5
    cV
    @5
    @5
    coss2
    cX
    xpcoid
    #
    syl6sseq
    syl
    sstrd
    @91
    @88
    @93
    @5
    @8
    @5
    @5
    coss2
    @94
    syl6sseq
    syl
    sstrd
    @0
    @4
    @5
    @38
    wceq
    @6
    @0
    @5
    @56
    @56
    cxp
    #
    @38
    @0
    cX
    @56
    @0
    cX
    @19
    cuni
    @56
    cU
    cX
    utopbas
    cJ
    @19
    utoptop.1
    unieqi
    syl6eqr
    sqxpeqd
    @0
    @18
    @18
    @95
    @38
    wceq
    @20
    @20
    cJ
    cJ
    @56
    @56
    @57
    @57
    txuni
    syl2anc
    eqtrd
    3ad2ant1
    #
    sseqtrd
    adantr
    @25
    @10
    @9
    @37
    @38
    @38
    eqid
    #
    ssnei2
    syl22anc
    ralrimiva
    adantr
    @23
    @17
    cM
    @38
    wss
    #
    @22
    @13
    @28
    wb
    @7
    @17
    @22
    @21
    adantr
    @7
    @98
    @22
    @7
    cM
    @5
    @38
    @53
    @96
    sseqtrd
    adantr
    @7
    @22
    simpr
    cM
    @10
    @9
    @38
    vr
    @97
    neips
    syl3anc
    mpbird
    pm2.61dane
end
