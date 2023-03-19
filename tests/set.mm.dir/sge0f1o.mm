include "cpnf.mm"
include "cmpt.mm"
include "crn.mm"
include "wcel.mm"
include "csumge0.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "wfo.mm"
include "wf1o.mm"
include "f1ofo.mm"
include "syl.mm"
include "fornex.mm"
include "sylc.mm"
include "adantr.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "eqid.mm"
include "fmptdf.mm"
include "wrex.mm"
include "wb.mm"
include "pnfex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "wi.mm"
include "nfv.mm"
include "cv.mm"
include "w3a.mm"
include "csb.mm"
include "simp3.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "nfcv.mm"
include "nfcsb1.mm"
include "nfeq.mm"
include "nfim.mm"
include "eqeq1.mm"
include "csbeq1a.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "simpl.mm"
include "jca.mm"
include "nfan.mm"
include "nfel1.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "elrnmpt1sf.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "sge0pnfval.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "wn.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "csu.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "sumex.mm"
include "a1i.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "sseqtrd.mm"
include "fex.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "elpwg.mm"
include "mpbird.mm"
include "wfun.mm"
include "f1ocnv.mm"
include "f1ofun.mm"
include "elinel2.mm"
include "imafi.mm"
include "elind.mm"
include "adantlr.mm"
include "cres.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfn.mm"
include "wf1.mm"
include "f1of1.mm"
include "mpbid.mm"
include "f1ores.mm"
include "elpwinss.mm"
include "foimacnv.mm"
include "f1oeq3d.mm"
include "ad2antrr.mm"
include "simpll.mm"
include "jca31.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "reseq2.mm"
include "fveq1d.mm"
include "fvres.mm"
include "sselda.mm"
include "vtoclg.mm"
include "adantllr.mm"
include "cc.mm"
include "ad3antrrr.mm"
include "eleqtrd.mm"
include "imaeq2.mm"
include "eleq2d.mm"
include "imbi1d.mm"
include "cico.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "simplll.mm"
include "simpllr.mm"
include "fimass.mm"
include "sseldd.mm"
include "foelrni.mm"
include "sylan.mm"
include "csbid.mm"
include "eqcomi.mm"
include "id.mm"
include "csbeq1d.mm"
include "3ad2ant3.mm"
include "idi.mm"
include "3eqtrd.mm"
include "3adant1r.mm"
include "0xr.mm"
include "pnfxr.mm"
include "eliccnelico.mm"
include "elrnmpt1.mm"
include "condan.mm"
include "syl21anc.mm"
include "sseldi.mm"
include "fsumf1of.mm"
include "sumeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "rnmptssrn.mm"
include "ssexd.mm"
include "ffun.mm"
include "eqssd.mm"
include "supeq1d.mm"
include "sge0revalmpt.mm"
include "3eqtr4d.mm"
include "pm2.61dan.mm"

theorem sge0f1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume sge0f1o.1: |- F/ k ph
  assume sge0f1o.2: |- F/ n ph
  assume sge0f1o.3: |- ( k = G -> B = D )
  assume sge0f1o.4: |- ( ph -> C e. V )
  assume sge0f1o.5: |- ( ph -> F : C -1-1-onto-> A )
  assume sge0f1o.6: |- ( ( ph /\ n e. C ) -> ( F ` n ) = G )
  assume sge0f1o.7: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )

  disjoint A k
  disjoint A n
  disjoint k n
  disjoint B n
  disjoint C k
  disjoint C n
  disjoint D k
  disjoint F k
  disjoint F n
  disjoint G k
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. A |-> B ) ) = ( sum^ ` ( n e. C |-> D ) ) )

  proof
    wph
    cpnf
    vn
    cC
    cD
    cmpt
    #
    crn
    #
    wcel
    #
    vk
    cA
    cB
    cmpt
    #
    csumge0
    cfv
    #
    @0
    csumge0
    cfv
    #
    wceq
    wph
    @2
    wa
    #
    @4
    cpnf
    @5
    @6
    @3
    cvv
    cA
    wph
    cA
    cvv
    wcel
    #
    @2
    wph
    cC
    cV
    wcel
    #
    cC
    cA
    cF
    wfo
    #
    @7
    sge0f1o.4
    wph
    cC
    cA
    cF
    wf1o
    #
    @9
    sge0f1o.5
    cC
    cA
    cF
    f1ofo
    syl
    #
    cC
    cA
    cV
    cF
    fornex
    sylc
    #
    adantr
    wph
    cA
    cc0
    cpnf
    cicc
    co
    #
    @3
    wf
    @2
    wph
    vk
    cA
    cB
    @13
    @3
    sge0f1o.1
    sge0f1o.7
    @3
    eqid
    #
    fmptdf
    adantr
    @6
    cpnf
    cD
    wceq
    #
    vn
    cC
    wrex
    #
    cpnf
    @3
    crn
    #
    wcel
    #
    @2
    @16
    wph
    @2
    @16
    cpnf
    cvv
    wcel
    @2
    @16
    wb
    pnfex
    vn
    cC
    cD
    cpnf
    @0
    cvv
    @0
    eqid
    #
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @16
    @18
    wi
    @2
    wph
    @15
    @18
    vn
    cC
    sge0f1o.2
    @18
    vn
    nfv
    wph
    vn
    cv
    #
    cC
    wcel
    #
    @15
    @18
    wph
    @21
    @15
    w3a
    #
    cpnf
    vk
    @20
    cF
    cfv
    #
    cB
    csb
    #
    @17
    @22
    cpnf
    cD
    @24
    wph
    @21
    @15
    simp3
    wph
    @21
    cD
    @24
    wceq
    @15
    wph
    @21
    wa
    #
    @24
    cD
    @25
    @23
    cA
    wcel
    #
    @23
    cG
    wceq
    #
    @24
    cD
    wceq
    #
    wph
    cC
    cA
    @20
    cF
    wph
    @10
    cC
    cA
    cF
    wf
    #
    sge0f1o.5
    cC
    cA
    cF
    f1of
    syl
    #
    ffvelrnda
    #
    sge0f1o.6
    vk
    cv
    #
    cG
    wceq
    #
    cB
    cD
    wceq
    #
    wi
    @27
    @28
    wi
    vk
    @23
    cA
    vk
    @23
    nfcv
    #
    @27
    @28
    vk
    @27
    vk
    nfv
    vk
    @24
    cD
    vk
    @23
    cB
    @35
    nfcsb1
    #
    vk
    cD
    nfcv
    nfeq
    nfim
    @32
    @23
    wceq
    #
    @33
    @27
    @34
    @28
    @32
    @23
    cG
    eqeq1
    @37
    cB
    @24
    cD
    vk
    @23
    cB
    csbeq1a
    #
    eqeq1d
    imbi12d
    sge0f1o.3
    vtoclgf
    sylc
    #
    eqcomd
    #
    3adant3
    eqtrd
    wph
    @21
    @24
    @17
    wcel
    #
    @15
    @25
    @26
    @24
    @13
    wcel
    #
    @41
    @31
    @25
    @26
    wph
    @26
    wa
    #
    @42
    @31
    @25
    wph
    @26
    wph
    @21
    simpl
    @31
    jca
    wph
    @32
    cA
    wcel
    #
    wa
    #
    cB
    @13
    wcel
    #
    wi
    @43
    @42
    wi
    vk
    @23
    cA
    @35
    @43
    @42
    vk
    wph
    @26
    vk
    sge0f1o.1
    @26
    vk
    nfv
    nfan
    vk
    @24
    @13
    @36
    nfel1
    nfim
    @37
    @45
    @43
    @46
    @42
    @37
    @44
    @26
    wph
    @32
    @23
    cA
    eleq1
    anbi2d
    @37
    cB
    @24
    @13
    @38
    eleq1d
    imbi12d
    sge0f1o.7
    vtoclgf
    sylc
    #
    vk
    cA
    cB
    @24
    @23
    @3
    @13
    @36
    @14
    @38
    elrnmpt1sf
    syl2anc
    3adant3
    eqeltrd
    3exp
    rexlimd
    adantr
    mpd
    sge0pnfval
    @6
    @0
    cV
    cC
    wph
    @8
    @2
    sge0f1o.4
    adantr
    wph
    cC
    @13
    @0
    wf
    @2
    wph
    vn
    cC
    cD
    @13
    @0
    sge0f1o.2
    @25
    cD
    @24
    @13
    @40
    @47
    eqeltrd
    #
    @19
    fmptdf
    adantr
    wph
    @2
    simpr
    sge0pnfval
    eqtr4d
    wph
    @2
    wn
    #
    wa
    #
    vy
    cA
    cpw
    #
    cfn
    cin
    #
    vy
    cv
    #
    cB
    vk
    csu
    #
    cmpt
    crn
    #
    cxr
    clt
    csup
    vx
    cC
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    cD
    vn
    csu
    #
    cmpt
    crn
    #
    cxr
    clt
    csup
    @4
    @5
    @50
    cxr
    @55
    @60
    clt
    @50
    @55
    @60
    @50
    vy
    vx
    @52
    @54
    @57
    @59
    cvv
    @54
    cvv
    wcel
    @50
    @53
    @52
    wcel
    #
    wa
    #
    @53
    cB
    vk
    sumex
    a1i
    @62
    cF
    ccnv
    #
    @53
    cima
    #
    @57
    wcel
    #
    @54
    @64
    cD
    vn
    csu
    #
    wceq
    #
    @54
    @59
    wceq
    #
    vx
    @57
    wrex
    wph
    @61
    @65
    @49
    wph
    @61
    wa
    #
    @56
    cfn
    @64
    wph
    @64
    @56
    wcel
    #
    @61
    wph
    @70
    @64
    cC
    wss
    #
    wph
    @64
    cF
    cdm
    #
    cC
    @64
    @72
    wss
    wph
    cF
    @53
    cnvimass
    a1i
    wph
    @29
    @72
    cC
    wceq
    @30
    cC
    cA
    cF
    fdm
    syl
    sseqtrd
    wph
    @64
    cvv
    wcel
    #
    @70
    @71
    wb
    #
    wph
    @63
    cvv
    wcel
    #
    @73
    wph
    cF
    cvv
    wcel
    #
    @75
    wph
    @29
    @8
    @76
    @30
    sge0f1o.4
    cC
    cA
    cV
    cF
    fex
    syl2anc
    cF
    cvv
    cnvexg
    syl
    @63
    @53
    cvv
    imaexg
    syl
    #
    @64
    cC
    cvv
    elpwg
    syl
    #
    mpbird
    #
    adantr
    #
    @69
    @63
    wfun
    #
    @53
    cfn
    wcel
    #
    @64
    cfn
    wcel
    #
    wph
    @81
    @61
    wph
    cA
    cC
    @63
    wf1o
    #
    @81
    wph
    @10
    @84
    sge0f1o.5
    cC
    cA
    cF
    f1ocnv
    syl
    cA
    cC
    @63
    f1ofun
    syl
    adantr
    @61
    @82
    wph
    @53
    @51
    cfn
    elinel2
    adantl
    @63
    @53
    imafi
    syl2anc
    #
    elind
    #
    adantlr
    @62
    @53
    cB
    @64
    cD
    vk
    vn
    cF
    @64
    cres
    #
    cG
    @50
    @61
    vk
    wph
    @49
    vk
    sge0f1o.1
    @49
    vk
    nfv
    nfan
    #
    @61
    vk
    nfv
    nfan
    @50
    @61
    vn
    wph
    @49
    vn
    sge0f1o.2
    @2
    vn
    vn
    cpnf
    @1
    vn
    cpnf
    nfcv
    vn
    @0
    vn
    cC
    cD
    nfmpt1
    nfrn
    nfel
    nfn
    nfan
    #
    @61
    vn
    nfv
    nfan
    sge0f1o.3
    wph
    @61
    @83
    @49
    @85
    adantlr
    #
    wph
    @61
    @64
    @53
    @87
    wf1o
    #
    @49
    @69
    @64
    cF
    @64
    cima
    #
    @87
    wf1o
    #
    @91
    @69
    cC
    cA
    cF
    wf1
    #
    @71
    @93
    wph
    @94
    @61
    wph
    @10
    @94
    sge0f1o.5
    cC
    cA
    cF
    f1of1
    syl
    #
    adantr
    @69
    @70
    @71
    @80
    wph
    @74
    @61
    @78
    adantr
    mpbid
    cC
    cA
    @64
    cF
    f1ores
    syl2anc
    @69
    @92
    @53
    @64
    @87
    @69
    @9
    @53
    cA
    wss
    #
    @92
    @53
    wceq
    wph
    @9
    @61
    @11
    adantr
    @61
    @96
    wph
    @53
    cA
    cfn
    elpwinss
    adantl
    cC
    cA
    @53
    cF
    foimacnv
    syl2anc
    #
    f1oeq3d
    mpbid
    adantlr
    wph
    @61
    @20
    @64
    wcel
    #
    @20
    @87
    cfv
    #
    cG
    wceq
    #
    @49
    @69
    @98
    wa
    #
    @73
    wph
    @65
    wa
    #
    @98
    wa
    #
    @100
    wph
    @73
    @61
    @98
    @77
    ad2antrr
    @101
    wph
    @65
    @98
    wph
    @61
    @98
    simpll
    @69
    @65
    @98
    @86
    adantr
    @69
    @98
    simpr
    jca31
    wph
    @58
    @57
    wcel
    #
    wa
    #
    @20
    @58
    wcel
    #
    wa
    #
    @20
    cF
    @58
    cres
    #
    cfv
    #
    cG
    wceq
    #
    wi
    @103
    @100
    wi
    vx
    @64
    cvv
    @58
    @64
    wceq
    #
    @107
    @103
    @110
    @100
    @111
    @105
    @102
    @106
    @98
    @111
    @104
    @65
    wph
    @58
    @64
    @57
    eleq1
    #
    anbi2d
    @58
    @64
    @20
    eleq2
    anbi12d
    @111
    @109
    @99
    cG
    @111
    @20
    @108
    @87
    @58
    @64
    cF
    reseq2
    fveq1d
    eqeq1d
    imbi12d
    @107
    @109
    @23
    cG
    @106
    @109
    @23
    wceq
    @105
    @20
    @58
    cF
    fvres
    adantl
    @107
    wph
    @21
    @27
    wph
    @104
    @106
    simpll
    @105
    @58
    cC
    @20
    @104
    @58
    cC
    wss
    #
    wph
    @58
    cC
    cfn
    elpwinss
    adantl
    #
    sselda
    sge0f1o.6
    syl2anc
    eqtrd
    #
    vtoclg
    sylc
    adantllr
    @62
    @32
    @53
    wcel
    #
    wa
    #
    @73
    @50
    @65
    wa
    #
    @32
    @92
    wcel
    #
    wa
    #
    cB
    cc
    wcel
    #
    wph
    @73
    @49
    @61
    @116
    @77
    ad3antrrr
    @117
    @50
    @65
    @119
    @50
    @61
    @116
    simpll
    @117
    @56
    cfn
    @64
    wph
    @70
    @49
    @61
    @116
    @79
    ad3antrrr
    @62
    @83
    @116
    @90
    adantr
    elind
    wph
    @61
    @116
    @119
    @49
    @69
    @116
    wa
    @32
    @53
    @92
    @69
    @116
    simpr
    @69
    @53
    @92
    wceq
    @116
    @69
    @92
    @53
    @97
    eqcomd
    adantr
    eleqtrd
    adantllr
    jca31
    @50
    @104
    wa
    #
    @32
    cF
    @58
    cima
    #
    wcel
    #
    wa
    #
    @121
    wi
    #
    @120
    @121
    wi
    vx
    @64
    cvv
    @111
    @125
    @120
    @121
    @111
    @122
    @118
    @124
    @119
    @111
    @104
    @65
    @50
    @112
    anbi2d
    @111
    @123
    @92
    @32
    @58
    @64
    cF
    imaeq2
    eleq2d
    anbi12d
    imbi1d
    @126
    @125
    cc0
    cpnf
    cico
    co
    #
    cc
    cB
    @127
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    @125
    wph
    @49
    @44
    cB
    @127
    wcel
    #
    wph
    @49
    @104
    @124
    simplll
    wph
    @49
    @104
    @124
    simpllr
    wph
    @104
    @124
    @44
    @49
    @105
    @124
    wa
    @123
    cA
    @32
    wph
    @123
    cA
    wss
    #
    @104
    @124
    wph
    @29
    @129
    @30
    cC
    cA
    cF
    @58
    fimass
    syl
    #
    ad2antrr
    @105
    @124
    simpr
    sseldd
    adantllr
    @50
    @44
    wa
    #
    @23
    @32
    wceq
    #
    vn
    cC
    wrex
    #
    @128
    wph
    @44
    @133
    @49
    wph
    @9
    @44
    @133
    @11
    vn
    cC
    cA
    cF
    @32
    foelrni
    sylan
    adantlr
    @131
    @132
    @128
    vn
    cC
    @50
    @44
    vn
    @89
    @44
    vn
    nfv
    nfan
    @128
    vn
    nfv
    @50
    @21
    @132
    @128
    wi
    wi
    @44
    @50
    @21
    @132
    @128
    @50
    @21
    @132
    w3a
    cB
    cD
    @127
    wph
    @21
    @132
    @34
    @49
    wph
    @21
    @132
    w3a
    #
    cB
    vk
    @32
    cB
    csb
    #
    @24
    cD
    cB
    @135
    wceq
    @134
    @135
    cB
    vk
    cB
    csbid
    eqcomi
    a1i
    @132
    wph
    @135
    @24
    wceq
    @21
    @132
    vk
    @32
    @23
    cB
    @132
    @23
    @32
    @132
    id
    eqcomd
    csbeq1d
    3ad2ant3
    wph
    @21
    @28
    @132
    @25
    @28
    wi
    @39
    idi
    3adant3
    3eqtrd
    3adant1r
    @50
    @21
    cD
    @127
    wcel
    #
    @132
    @50
    @21
    wa
    @136
    @2
    wph
    @21
    @136
    wn
    #
    @2
    @49
    @25
    @137
    wa
    #
    cpnf
    cD
    @1
    @138
    cD
    cpnf
    @138
    cc0
    cpnf
    cD
    cc0
    cxr
    wcel
    @138
    0xr
    a1i
    cpnf
    cxr
    wcel
    @138
    pnfxr
    a1i
    @25
    cD
    @13
    wcel
    #
    @137
    @48
    adantr
    @25
    @137
    simpr
    eliccnelico
    eqcomd
    @25
    cD
    @1
    wcel
    #
    @137
    @25
    @21
    @139
    @140
    wph
    @21
    simpr
    @25
    @139
    wi
    @48
    idi
    vn
    cC
    cD
    @0
    @13
    @19
    elrnmpt1
    syl2anc
    adantr
    eqeltrd
    adantllr
    wph
    @49
    @21
    @137
    simpllr
    condan
    #
    3adant3
    eqeltrd
    3exp
    adantr
    rexlimd
    mpd
    #
    syl21anc
    sseldi
    #
    idi
    vtoclg
    sylc
    fsumf1of
    @68
    @67
    vx
    @64
    @57
    @111
    @59
    @66
    @54
    @58
    @64
    cD
    vn
    sumeq1
    eqeq2d
    rspcev
    syl2anc
    rnmptssrn
    @50
    vx
    vy
    @57
    @59
    @52
    @54
    cvv
    @59
    cvv
    wcel
    @122
    @58
    cD
    vn
    sumex
    a1i
    @122
    @123
    @52
    wcel
    #
    @59
    @123
    cB
    vk
    csu
    #
    wceq
    #
    @59
    @54
    wceq
    #
    vy
    @52
    wrex
    wph
    @104
    @144
    @49
    @105
    @51
    cfn
    @123
    wph
    @123
    @51
    wcel
    #
    @104
    wph
    @148
    @129
    @130
    wph
    @123
    cvv
    wcel
    @148
    @129
    wb
    wph
    @123
    cA
    cvv
    @12
    @130
    ssexd
    @123
    cA
    cvv
    elpwg
    syl
    mpbird
    adantr
    @105
    cF
    wfun
    #
    @58
    cfn
    wcel
    #
    @123
    cfn
    wcel
    wph
    @149
    @104
    wph
    @29
    @149
    @30
    cC
    cA
    cF
    ffun
    syl
    adantr
    @104
    @150
    wph
    @58
    @56
    cfn
    elinel2
    #
    adantl
    cF
    @58
    imafi
    syl2anc
    elind
    adantlr
    @122
    @145
    @59
    @122
    @123
    cB
    @58
    cD
    vk
    vn
    @108
    cG
    @50
    @104
    vk
    @88
    @104
    vk
    nfv
    nfan
    @50
    @104
    vn
    @89
    @104
    vn
    nfv
    nfan
    sge0f1o.3
    @104
    @150
    @50
    @151
    adantl
    wph
    @104
    @58
    @123
    @108
    wf1o
    #
    @49
    @105
    @94
    @113
    @152
    wph
    @94
    @104
    @95
    adantr
    @114
    cC
    cA
    @58
    cF
    f1ores
    syl2anc
    adantlr
    wph
    @104
    @106
    @110
    @49
    @115
    adantllr
    @143
    fsumf1of
    eqcomd
    @147
    @146
    vy
    @123
    @52
    @53
    @123
    wceq
    @54
    @145
    @59
    @53
    @123
    cB
    vk
    sumeq1
    eqeq2d
    rspcev
    syl2anc
    rnmptssrn
    eqssd
    supeq1d
    @50
    vk
    vy
    cA
    cB
    cvv
    @88
    wph
    @7
    @49
    @12
    adantr
    @142
    sge0revalmpt
    @50
    vn
    vx
    cC
    cD
    cV
    @89
    wph
    @8
    @49
    sge0f1o.4
    adantr
    @141
    sge0revalmpt
    3eqtr4d
    pm2.61dan
end
