include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cima.mm"
include "cres.mm"
include "wf1o.mm"
include "wf1.mm"
include "wss.mm"
include "cvv.mm"
include "eqid.mm"
include "ovexd.mm"
include "cn.mm"
include "wcel.mm"
include "nnex.mm"
include "a1i.mm"
include "ssexd.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "pmtridf1o.mm"
include "fmptco1f1o.mm"
include "f1of1.mm"
include "syl.mm"
include "wa.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "crab.mm"
include "ssrab2.mm"
include "crepr.mm"
include "wn.mm"
include "ssrab3.mm"
include "nnnn0d.mm"
include "reprval.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "sseldi.mm"
include "ex.mm"
include "ssrdv.mm"
include "f1ores.mm"
include "syl2anc.mm"
include "resmpt.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "wrex.mm"
include "vex.mm"
include "elimampt.mm"
include "simpr.mm"
include "wral.mm"
include "wf.mm"
include "f1of.mm"
include "ad2antrr.mm"
include "fmpt.mm"
include "adantr.mm"
include "rspa.mm"
include "eqeltrd.mm"
include "fveq1d.mm"
include "wfun.mm"
include "cdm.mm"
include "f1ofun.mm"
include "f1odm.mm"
include "eleqtrrd.mm"
include "fvco.mm"
include "adantlr.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "fveq2.mm"
include "cfn.mm"
include "fzofi.mm"
include "cz.mm"
include "cn0.mm"
include "reprf.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "nncnd.mm"
include "fsumf1o.mm"
include "reprsum.mm"
include "3eqtr2d.mm"
include "fveq1.mm"
include "sumeq2sdv.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "pmtridfv2.mm"
include "fveq2d.mm"
include "syl6eleq.mm"
include "rabid.mm"
include "sylib.mm"
include "simprd.mm"
include "eqneltrd.mm"
include "jca.mm"
include "r19.29an.mm"
include "ccnv.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "fco.mm"
include "wb.mm"
include "elmapg.mm"
include "mpbird.mm"
include "f1ocnvfv.mm"
include "imp.mm"
include "syl21anc.mm"
include "eleq1d.mm"
include "notbid.mm"
include "syl6eleqr.mm"
include "anasss.mm"
include "coeq1d.mm"
include "eqeq2d.mm"
include "cid.mm"
include "f1ococnv1.mm"
include "coeq2d.mm"
include "adantrr.mm"
include "fcoi1.mm"
include "eqtr2d.mm"
include "coass.mm"
include "rspcedvd.mm"
include "impbida.mm"
include "bitrd.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "f1oeq123d.mm"
include "mpbid.mm"

theorem reprpmtf1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cT: class T
  let cF: class F
  let cM: class M
  let cO: class O
  let cX: class X
  let vc: setvar c
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  assume reprpmtf1o.s: |- ( ph -> S e. NN )
  assume reprpmtf1o.m: |- ( ph -> M e. ZZ )
  assume reprpmtf1o.a: |- ( ph -> A C_ NN )
  assume reprpmtf1o.x: |- ( ph -> X e. ( 0 ..^ S ) )
  assume reprpmtf1o.o: |- O = { c e. ( A ( repr ` S ) M ) | -. ( c ` 0 ) e. B }
  assume reprpmtf1o.p: |- P = { c e. ( A ( repr ` S ) M ) | -. ( c ` X ) e. B }
  assume reprpmtf1o.t: |- T = if ( X = 0 , ( _I |` ( 0 ..^ S ) ) , ( ( pmTrsp ` ( 0 ..^ S ) ) ` { X , 0 } ) )
  assume reprpmtf1o.f: |- F = ( c e. P |-> ( c o. T ) )

  disjoint A c
  disjoint B c
  disjoint M c
  disjoint P c
  disjoint S c
  disjoint T c
  disjoint X c
  disjoint c ph
  disjoint A a
  disjoint A b
  disjoint A d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint B d
  disjoint M a
  disjoint M b
  disjoint M d
  disjoint P a
  disjoint P b
  disjoint P d
  disjoint S a
  disjoint S b
  disjoint S d
  disjoint T a
  disjoint T b
  disjoint T d
  disjoint a ph
  disjoint b ph
  disjoint d ph
  assert |- ( ph -> F : P -1-1-onto-> O )

  proof
    wph
    cP
    vc
    cA
    cc0
    cS
    cfzo
    co
    #
    cmap
    co
    #
    vc
    cv
    #
    cT
    ccom
    #
    cmpt
    #
    cP
    cima
    #
    @4
    cP
    cres
    #
    wf1o
    #
    cP
    cO
    cF
    wf1o
    wph
    @1
    @1
    @4
    wf1
    #
    cP
    @1
    wss
    #
    @7
    wph
    @1
    @1
    @4
    wf1o
    #
    @8
    wph
    @1
    @1
    @0
    cA
    cT
    vc
    @0
    @4
    cvv
    cvv
    cvv
    @1
    eqid
    #
    @11
    @4
    eqid
    #
    wph
    cc0
    cS
    cfzo
    ovexd
    #
    @13
    wph
    cA
    cn
    cvv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    reprpmtf1o.a
    ssexd
    #
    wph
    @0
    cT
    cvv
    cX
    cc0
    @13
    reprpmtf1o.x
    wph
    cS
    cn
    wcel
    cc0
    @0
    wcel
    #
    reprpmtf1o.s
    cS
    lbfzo0
    sylibr
    #
    reprpmtf1o.t
    pmtridf1o
    #
    fmptco1f1o
    #
    @1
    @1
    @4
    f1of1
    syl
    wph
    vc
    cP
    @1
    wph
    @2
    cP
    wcel
    #
    @2
    @1
    wcel
    #
    wph
    @19
    wa
    #
    @0
    va
    cv
    #
    @2
    cfv
    #
    va
    csu
    #
    cM
    wceq
    #
    vc
    @1
    crab
    #
    @1
    @2
    @25
    vc
    @1
    ssrab2
    wph
    cP
    @26
    @2
    wph
    cP
    cA
    cM
    cS
    crepr
    cfv
    co
    #
    @26
    cP
    @27
    wss
    wph
    cX
    @2
    cfv
    #
    cB
    wcel
    #
    wn
    #
    vc
    @27
    cP
    reprpmtf1o.p
    ssrab3
    a1i
    #
    wph
    cA
    cS
    cM
    va
    vc
    reprpmtf1o.a
    reprpmtf1o.m
    wph
    cS
    reprpmtf1o.s
    nnnn0d
    #
    reprval
    #
    sseqtrd
    sselda
    sseldi
    #
    ex
    ssrdv
    #
    @1
    @1
    cP
    @4
    f1ores
    syl2anc
    wph
    cP
    cP
    @5
    cO
    @6
    cF
    wph
    @6
    vc
    cP
    @3
    cmpt
    #
    cF
    wph
    @9
    @6
    @36
    wceq
    @35
    vc
    @1
    cP
    @3
    resmpt
    syl
    reprpmtf1o.f
    syl6eqr
    wph
    cP
    eqidd
    wph
    @5
    cc0
    @2
    cfv
    #
    cB
    wcel
    #
    wn
    #
    vc
    @27
    crab
    #
    cO
    wph
    vd
    @5
    @40
    wph
    vd
    cv
    #
    @5
    wcel
    #
    @41
    @27
    wcel
    #
    cc0
    @41
    cfv
    #
    cB
    wcel
    #
    wn
    #
    wa
    #
    @41
    @40
    wcel
    wph
    @42
    @41
    @3
    wceq
    #
    vc
    cP
    wrex
    #
    @47
    wph
    vc
    @1
    @3
    @41
    cP
    @4
    cvv
    @12
    @41
    cvv
    wcel
    wph
    vd
    vex
    a1i
    @35
    elimampt
    wph
    @49
    @47
    wph
    @48
    @47
    vc
    cP
    @21
    @48
    wa
    #
    @43
    @46
    @50
    @41
    @26
    @27
    @50
    @41
    @1
    wcel
    @0
    @22
    @41
    cfv
    #
    va
    csu
    #
    cM
    wceq
    #
    @41
    @26
    wcel
    @50
    @41
    @3
    @1
    @21
    @48
    simpr
    #
    @50
    @3
    @1
    wcel
    #
    vc
    @1
    wral
    #
    @20
    @55
    @50
    @1
    @1
    @4
    wf
    #
    @56
    wph
    @57
    @19
    @48
    wph
    @10
    @57
    @18
    @1
    @1
    @4
    f1of
    syl
    ad2antrr
    vc
    @1
    @1
    @3
    @4
    @12
    fmpt
    sylibr
    @21
    @20
    @48
    @34
    adantr
    @55
    vc
    @1
    rspa
    syl2anc
    eqeltrd
    @50
    @52
    @0
    @22
    cT
    cfv
    #
    @2
    cfv
    #
    va
    csu
    #
    @0
    vb
    cv
    #
    @2
    cfv
    #
    vb
    csu
    #
    cM
    @50
    @0
    @51
    @59
    va
    @50
    @22
    @0
    wcel
    #
    wa
    #
    @51
    @22
    @3
    cfv
    #
    @59
    @65
    @22
    @41
    @3
    @50
    @48
    @64
    @54
    adantr
    fveq1d
    @21
    @64
    @66
    @59
    wceq
    #
    @48
    @21
    @64
    wa
    #
    cT
    wfun
    #
    @22
    cT
    cdm
    #
    wcel
    @67
    wph
    @69
    @19
    @64
    wph
    @0
    @0
    cT
    wf1o
    #
    @69
    @17
    @0
    @0
    cT
    f1ofun
    syl
    #
    ad2antrr
    @68
    @22
    @0
    @70
    @21
    @64
    simpr
    wph
    @70
    @0
    wceq
    #
    @19
    @64
    wph
    @71
    @73
    @17
    @0
    @0
    cT
    f1odm
    syl
    #
    ad2antrr
    eleqtrrd
    @22
    @2
    cT
    fvco
    syl2anc
    adantlr
    eqtrd
    sumeq2dv
    @21
    @63
    @60
    wceq
    @48
    @21
    @0
    @62
    @0
    @59
    vb
    va
    cT
    @58
    @61
    @58
    @2
    fveq2
    @0
    cfn
    wcel
    #
    @21
    cc0
    cS
    fzofi
    #
    a1i
    wph
    @71
    @19
    @17
    adantr
    @68
    @58
    eqidd
    @21
    @61
    @0
    wcel
    #
    wa
    #
    @62
    @78
    cA
    cn
    @62
    wph
    cA
    cn
    wss
    #
    @19
    @77
    reprpmtf1o.a
    ad2antrr
    @21
    @0
    cA
    @61
    @2
    @21
    cA
    @2
    cS
    cM
    wph
    @79
    @19
    reprpmtf1o.a
    adantr
    #
    wph
    cM
    cz
    wcel
    #
    @19
    reprpmtf1o.m
    adantr
    #
    wph
    cS
    cn0
    wcel
    #
    @19
    @32
    adantr
    #
    wph
    cP
    @27
    @2
    @31
    sselda
    #
    reprf
    ffvelrnda
    sseldd
    nncnd
    fsumf1o
    adantr
    @21
    @63
    cM
    wceq
    @48
    @21
    cA
    @2
    cS
    cM
    vb
    @80
    @82
    @84
    @85
    reprsum
    adantr
    3eqtr2d
    @25
    @53
    vc
    @41
    @1
    @2
    @41
    wceq
    #
    @24
    @52
    cM
    @86
    @0
    @23
    @51
    va
    @22
    @2
    @41
    fveq1
    sumeq2sdv
    eqeq1d
    elrab
    sylanbrc
    wph
    @27
    @26
    wceq
    #
    @19
    @48
    @33
    ad2antrr
    eleqtrrd
    @50
    @44
    cc0
    @3
    cfv
    #
    cB
    @50
    cc0
    @41
    @3
    @54
    fveq1d
    @50
    @88
    cc0
    cT
    cfv
    #
    @2
    cfv
    #
    cB
    @50
    @69
    cc0
    @70
    wcel
    #
    @88
    @90
    wceq
    wph
    @69
    @19
    @48
    @72
    ad2antrr
    wph
    @91
    @19
    @48
    wph
    cc0
    @0
    @70
    @16
    @74
    eleqtrrd
    ad2antrr
    cc0
    @2
    cT
    fvco
    syl2anc
    @50
    @90
    @28
    cB
    @50
    @89
    cX
    @2
    wph
    @89
    cX
    wceq
    #
    @19
    @48
    wph
    @0
    cT
    cvv
    cX
    cc0
    @13
    reprpmtf1o.x
    @16
    reprpmtf1o.t
    pmtridfv2
    #
    ad2antrr
    fveq2d
    @21
    @30
    @48
    @21
    @2
    @27
    wcel
    #
    @30
    @21
    @2
    @30
    vc
    @27
    crab
    #
    wcel
    @94
    @30
    wa
    @21
    @2
    cP
    @95
    wph
    @19
    simpr
    reprpmtf1o.p
    syl6eleq
    @30
    vc
    @27
    rabid
    sylib
    simprd
    adantr
    eqneltrd
    eqneltrd
    eqneltrd
    jca
    r19.29an
    wph
    @47
    wa
    #
    @48
    @41
    @41
    cT
    ccnv
    #
    ccom
    #
    cT
    ccom
    #
    wceq
    vc
    @98
    cP
    wph
    @43
    @46
    @98
    cP
    wcel
    wph
    @43
    wa
    #
    @46
    wa
    #
    @98
    @95
    cP
    @101
    @98
    @27
    wcel
    cX
    @98
    cfv
    #
    cB
    wcel
    #
    wn
    #
    @98
    @95
    wcel
    @101
    @98
    @26
    @27
    @101
    @98
    @1
    wcel
    #
    @0
    @22
    @98
    cfv
    #
    va
    csu
    #
    cM
    wceq
    #
    @98
    @26
    wcel
    @100
    @105
    @46
    @100
    @105
    @0
    cA
    @98
    wf
    #
    @100
    @0
    cA
    @41
    wf
    #
    @0
    @0
    @97
    wf
    #
    @109
    @100
    cA
    @41
    cS
    cM
    wph
    @79
    @43
    reprpmtf1o.a
    adantr
    #
    wph
    @81
    @43
    reprpmtf1o.m
    adantr
    #
    wph
    @83
    @43
    @32
    adantr
    #
    wph
    @43
    simpr
    #
    reprf
    #
    wph
    @111
    @43
    wph
    @71
    @0
    @0
    @97
    wf1o
    #
    @111
    @17
    @0
    @0
    cT
    f1ocnv
    #
    @0
    @0
    @97
    f1of
    3syl
    adantr
    @0
    @0
    cA
    @41
    @97
    fco
    syl2anc
    wph
    @105
    @109
    wb
    #
    @43
    wph
    cA
    cvv
    wcel
    @0
    cvv
    wcel
    @119
    @14
    @13
    cA
    @0
    @98
    cvv
    cvv
    elmapg
    syl2anc
    adantr
    mpbird
    adantr
    @100
    @108
    @46
    @100
    @107
    @0
    @22
    @97
    cfv
    #
    @41
    cfv
    #
    va
    csu
    @0
    @61
    @41
    cfv
    #
    vb
    csu
    cM
    @100
    @0
    @106
    @121
    va
    @100
    @64
    wa
    #
    @97
    wfun
    #
    @22
    @97
    cdm
    #
    wcel
    #
    @106
    @121
    wceq
    wph
    @124
    @43
    @64
    wph
    @71
    @117
    @124
    @17
    @118
    @0
    @0
    @97
    f1ofun
    3syl
    #
    ad2antrr
    wph
    @64
    @126
    @43
    wph
    @64
    wa
    @22
    @0
    @125
    wph
    @64
    simpr
    wph
    @125
    @0
    wceq
    #
    @64
    wph
    @71
    @117
    @128
    @17
    @118
    @0
    @0
    @97
    f1odm
    3syl
    #
    adantr
    eleqtrrd
    adantlr
    @22
    @41
    @97
    fvco
    syl2anc
    sumeq2dv
    @100
    @0
    @122
    @0
    @121
    vb
    va
    @97
    @120
    @61
    @120
    @41
    fveq2
    @75
    @100
    @76
    a1i
    wph
    @117
    @43
    wph
    @71
    @117
    @17
    @118
    syl
    adantr
    @123
    @120
    eqidd
    @100
    @77
    wa
    #
    @122
    @130
    cA
    cn
    @122
    @100
    @79
    @77
    @112
    adantr
    @100
    @0
    cA
    @61
    @41
    @116
    ffvelrnda
    sseldd
    nncnd
    fsumf1o
    @100
    cA
    @41
    cS
    cM
    vb
    @112
    @113
    @114
    @115
    reprsum
    3eqtr2d
    adantr
    @25
    @108
    vc
    @98
    @1
    @2
    @98
    wceq
    #
    @24
    @107
    cM
    @131
    @0
    @23
    @106
    va
    @22
    @2
    @98
    fveq1
    sumeq2sdv
    eqeq1d
    elrab
    sylanbrc
    wph
    @87
    @43
    @46
    @33
    ad2antrr
    eleqtrrd
    @101
    @102
    cX
    @97
    cfv
    #
    @41
    cfv
    #
    cB
    @101
    @124
    cX
    @125
    wcel
    #
    @102
    @133
    wceq
    wph
    @124
    @43
    @46
    @127
    ad2antrr
    wph
    @134
    @43
    @46
    wph
    cX
    @0
    @125
    reprpmtf1o.x
    @129
    eleqtrrd
    ad2antrr
    cX
    @41
    @97
    fvco
    syl2anc
    @101
    @133
    @44
    cB
    @101
    @132
    cc0
    @41
    wph
    @132
    cc0
    wceq
    #
    @43
    @46
    wph
    @71
    @15
    @92
    @135
    @17
    @16
    @93
    @71
    @15
    wa
    @92
    @135
    @0
    @0
    cc0
    cX
    cT
    f1ocnvfv
    imp
    syl21anc
    ad2antrr
    fveq2d
    @100
    @46
    simpr
    eqneltrd
    eqneltrd
    @30
    @104
    vc
    @98
    @27
    @131
    @29
    @103
    @131
    @28
    @102
    cB
    cX
    @2
    @98
    fveq1
    eleq1d
    notbid
    elrab
    sylanbrc
    reprpmtf1o.p
    syl6eleqr
    anasss
    @96
    @131
    wa
    #
    @3
    @99
    @41
    @136
    @2
    @98
    cT
    @96
    @131
    simpr
    coeq1d
    eqeq2d
    @96
    @41
    @41
    @97
    cT
    ccom
    #
    ccom
    #
    @99
    @96
    @138
    @41
    cid
    @0
    cres
    #
    ccom
    #
    @41
    @96
    @137
    @139
    @41
    wph
    @137
    @139
    wceq
    #
    @47
    wph
    @71
    @141
    @17
    @0
    @0
    cT
    f1ococnv1
    syl
    adantr
    coeq2d
    @96
    @110
    @140
    @41
    wceq
    wph
    @43
    @110
    @46
    @116
    adantrr
    @0
    cA
    @41
    fcoi1
    syl
    eqtr2d
    @41
    @97
    cT
    coass
    syl6eqr
    rspcedvd
    impbida
    bitrd
    @39
    @46
    vc
    @41
    @27
    @86
    @38
    @45
    @86
    @37
    @44
    cB
    cc0
    @2
    @41
    fveq1
    eleq1d
    notbid
    elrab
    syl6bbr
    eqrdv
    reprpmtf1o.o
    syl6eqr
    f1oeq123d
    mpbid
end
