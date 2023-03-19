include "csumge0.mm"
include "cfv.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cvv.mm"
include "wcel.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cicc.mm"
include "wss.mm"
include "icossicc.mm"
include "fssd.mm"
include "sge0xrcl.mm"
include "cv.mm"
include "wa.mm"
include "eqidd.mm"
include "rge0ssre.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "cabs.mm"
include "wral.mm"
include "wrex.mm"
include "cz.mm"
include "cli.mm"
include "cdm.mm"
include "cc.mm"
include "caddc.mm"
include "cseq.mm"
include "seqex.mm"
include "climcl.mm"
include "syl.mm"
include "breldmg.mm"
include "wceq.mm"
include "fveq1d.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "cfz.mm"
include "simpll.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "syl2anc.mm"
include "readdcl.mm"
include "seqcl.mm"
include "eqeltrd.mm"
include "recnd.mm"
include "ralrimiva.mm"
include "climbdd.mm"
include "ad4ant13.mm"
include "abscld.mm"
include "simpllr.mm"
include "leabsd.mm"
include "simpr.mm"
include "letrd.mm"
include "ex.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "isumsup2.mm"
include "climrecl.mm"
include "rexrd.mm"
include "cmpt.mm"
include "feqmptd.mm"
include "fveq2d.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "mpteq1.mm"
include "mpt0.mm"
include "fveq2i.mm"
include "sge00.mm"
include "eqtri.mm"
include "eqtrd.mm"
include "0red.mm"
include "wf.mm"
include "seqf.mm"
include "feq1d.mm"
include "mpbird.mm"
include "frn.mm"
include "wfun.mm"
include "ffun.mm"
include "uzid.mm"
include "eqcomi.mm"
include "syl6eleq.mm"
include "fdm.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvelrn.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "fveq1i.mm"
include "seq1.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "wne.mm"
include "ne0i.mm"
include "wb.mm"
include "wfn.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "adantr.mm"
include "mpbid.mm"
include "adantlr.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "wi.mm"
include "w3a.mm"
include "rspa.mm"
include "3adant3.mm"
include "simp3.mm"
include "id.mm"
include "simpl.mm"
include "eqbrtrd.mm"
include "3exp.mm"
include "ad2antlr.mm"
include "rexlimd.mm"
include "reximdv.mm"
include "suprub.mm"
include "syl31anc.mm"
include "ad2antrr.mm"
include "wn.mm"
include "elpwinss.mm"
include "sselda.mm"
include "adantll.mm"
include "eqid.mm"
include "fmptd.mm"
include "fzfid.mm"
include "sylan2.mm"
include "elinel2.mm"
include "ssuzfz.mm"
include "sge0lessmpt.mm"
include "csu.mm"
include "sge0fsummpt.mm"
include "syl6sseq.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "neqne.mm"
include "suprfinzcl.mm"
include "fsumser.mm"
include "3eqtrd.mm"
include "xrletrd.mm"
include "pm2.61dan.mm"
include "sge0lefimpt.mm"
include "ssriv.mm"
include "3ad2ant1.mm"
include "3eqtrrd.mm"
include "breq12d.mm"
include "rexlimdv.mm"
include "sge0cl.mm"
include "ltpnfd.mm"
include "xrlelttrd.mm"
include "xrgtned.mm"
include "necomd.mm"
include "ge0xrre.mm"
include "suprleub.mm"
include "xrletrid.mm"
include "climuni.mm"
include "eqtr4d.mm"

theorem sge0isum
  let wph: wff ph
  let cB: class B
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sge0isum.m: |- ( ph -> M e. ZZ )
  assume sge0isum.z: |- Z = ( ZZ>= ` M )
  assume sge0isum.f: |- ( ph -> F : Z --> ( 0 [,) +oo ) )
  assume sge0isum.g: |- G = seq M ( + , F )
  assume sge0isum.gcnv: |- ( ph -> G ~~> B )


  assert |- ( ph -> ( sum^ ` F ) = B )

  proof
    wph
    cF
    csumge0
    cfv
    #
    cG
    crn
    #
    cr
    clt
    csup
    #
    cB
    wph
    @0
    @2
    wph
    cF
    cvv
    cZ
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    cfv
    #
    cvv
    sge0isum.z
    cM
    cuz
    fvex
    eqeltri
    a1i
    #
    wph
    cZ
    cc0
    cpnf
    cico
    co
    #
    cc0
    cpnf
    cicc
    co
    #
    cF
    sge0isum.f
    @5
    @6
    wss
    wph
    cc0
    cpnf
    icossicc
    #
    a1i
    fssd
    #
    sge0xrcl
    #
    wph
    @2
    wph
    @2
    vj
    cG
    cM
    cZ
    sge0isum.z
    sge0isum.m
    wph
    vx
    vk
    cv
    #
    cF
    cfv
    #
    vj
    vk
    cF
    cG
    cM
    cZ
    sge0isum.z
    sge0isum.g
    sge0isum.m
    wph
    @10
    cZ
    wcel
    #
    wa
    #
    @11
    eqidd
    #
    @13
    @5
    cr
    @11
    rge0ssre
    wph
    cZ
    @5
    @10
    cF
    sge0isum.f
    ffvelrnda
    #
    sseldi
    #
    @13
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @11
    @5
    wcel
    #
    cc0
    @11
    cle
    wbr
    @17
    @13
    0xr
    a1i
    @18
    @13
    pnfxr
    a1i
    @15
    cc0
    cpnf
    @11
    icogelb
    syl3anc
    wph
    vj
    cv
    #
    cG
    cfv
    #
    cabs
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @21
    @23
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    wph
    cM
    cz
    wcel
    #
    cG
    cli
    cdm
    wcel
    #
    @21
    cc
    wcel
    #
    vj
    cZ
    wral
    @26
    sge0isum.m
    wph
    cG
    cvv
    wcel
    #
    cB
    cc
    wcel
    #
    cG
    cB
    cli
    wbr
    #
    @31
    @33
    wph
    cG
    caddc
    cF
    cM
    cseq
    #
    cvv
    sge0isum.g
    caddc
    cF
    cM
    seqex
    eqeltri
    a1i
    wph
    @35
    @34
    sge0isum.gcnv
    cB
    cG
    climcl
    syl
    sge0isum.gcnv
    cG
    cB
    cvv
    cc
    cli
    breldmg
    syl3anc
    wph
    @32
    vj
    cZ
    wph
    @20
    cZ
    wcel
    #
    wa
    #
    @21
    @38
    @21
    @20
    @36
    cfv
    #
    cr
    @38
    @20
    cG
    @36
    cG
    @36
    wceq
    #
    @38
    sge0isum.g
    a1i
    fveq1d
    @38
    vk
    vi
    caddc
    cr
    cF
    cM
    @20
    @37
    @20
    @3
    wcel
    #
    wph
    @37
    @41
    cZ
    @3
    @20
    sge0isum.z
    eleq2i
    biimpi
    adantl
    #
    @38
    @10
    cM
    @20
    cfz
    co
    #
    wcel
    #
    wa
    #
    wph
    @12
    @11
    cr
    wcel
    wph
    @37
    @44
    simpll
    #
    @44
    @12
    @38
    @44
    @10
    @3
    cZ
    @10
    cM
    @20
    elfzuz
    sge0isum.z
    syl6eleqr
    #
    adantl
    #
    @16
    syl2anc
    @10
    cr
    wcel
    vi
    cv
    #
    cr
    wcel
    wa
    #
    @10
    @49
    caddc
    co
    cr
    wcel
    #
    @38
    @10
    @49
    readdcl
    #
    adantl
    seqcl
    eqeltrd
    #
    recnd
    #
    ralrimiva
    vx
    vj
    cG
    cM
    cZ
    sge0isum.z
    climbdd
    syl3anc
    wph
    @25
    @28
    vx
    cr
    wph
    @23
    cr
    wcel
    #
    wa
    #
    @24
    @27
    vj
    cZ
    @56
    @37
    wa
    #
    @24
    @27
    @57
    @24
    wa
    #
    @21
    @22
    @23
    wph
    @37
    @21
    cr
    wcel
    @55
    @24
    @53
    ad4ant13
    #
    @58
    @21
    wph
    @37
    @32
    @55
    @24
    @54
    ad4ant13
    abscld
    wph
    @55
    @37
    @24
    simpllr
    @58
    @21
    @59
    leabsd
    @57
    @24
    simpr
    letrd
    ex
    ralimdva
    reximdva
    mpd
    #
    isumsup2
    #
    @53
    climrecl
    #
    rexrd
    #
    wph
    @0
    vk
    cZ
    @11
    cmpt
    #
    csumge0
    cfv
    #
    @2
    cle
    wph
    cF
    @64
    csumge0
    wph
    vk
    cZ
    @5
    cF
    sge0isum.f
    feqmptd
    fveq2d
    #
    wph
    @65
    @2
    cle
    wbr
    vk
    vy
    cv
    #
    @11
    cmpt
    #
    csumge0
    cfv
    #
    @2
    cle
    wbr
    #
    vy
    cZ
    cpw
    #
    cfn
    cin
    #
    wral
    wph
    @70
    vy
    @72
    wph
    @67
    @72
    wcel
    #
    wa
    #
    @67
    c0
    wceq
    #
    @70
    @74
    @75
    wa
    @69
    cc0
    @2
    cle
    @75
    @69
    cc0
    wceq
    @74
    @75
    @69
    vk
    c0
    @11
    cmpt
    #
    csumge0
    cfv
    #
    cc0
    @75
    @68
    @76
    csumge0
    vk
    @67
    c0
    @11
    mpteq1
    fveq2d
    @77
    cc0
    wceq
    @75
    @77
    c0
    csumge0
    cfv
    cc0
    @76
    c0
    csumge0
    vk
    @11
    mpt0
    fveq2i
    sge00
    eqtri
    a1i
    eqtrd
    adantl
    wph
    cc0
    @2
    cle
    wbr
    @73
    @75
    wph
    cc0
    cM
    cG
    cfv
    #
    @2
    wph
    0red
    wph
    @1
    cr
    @78
    wph
    cZ
    cr
    cG
    wf
    #
    @1
    cr
    wss
    #
    wph
    @79
    cZ
    cr
    @36
    wf
    wph
    vk
    vi
    caddc
    cr
    cF
    cM
    cZ
    sge0isum.z
    sge0isum.m
    @16
    @50
    @51
    wph
    @52
    adantl
    seqf
    wph
    cZ
    cr
    cG
    @36
    @40
    wph
    sge0isum.g
    a1i
    feq1d
    mpbird
    #
    cZ
    cr
    cG
    frn
    syl
    #
    wph
    cG
    wfun
    #
    cM
    cG
    cdm
    #
    wcel
    @78
    @1
    wcel
    #
    wph
    @79
    @83
    @81
    cZ
    cr
    cG
    ffun
    syl
    #
    wph
    cM
    cZ
    @84
    wph
    cM
    @3
    cZ
    wph
    @30
    cM
    @3
    wcel
    sge0isum.m
    cM
    uzid
    syl
    cZ
    @3
    sge0isum.z
    eqcomi
    #
    syl6eleq
    #
    wph
    @84
    cZ
    wph
    @79
    @84
    cZ
    wceq
    @81
    cZ
    cr
    cG
    fdm
    syl
    eqcomd
    #
    eleqtrd
    cM
    cG
    fvelrn
    syl2anc
    #
    sseldd
    @62
    wph
    cc0
    cM
    cF
    cfv
    #
    @78
    cle
    wph
    @17
    @18
    @91
    @5
    wcel
    cc0
    @91
    cle
    wbr
    @17
    wph
    0xr
    a1i
    @18
    wph
    pnfxr
    a1i
    #
    wph
    cZ
    @5
    cM
    cF
    sge0isum.f
    @88
    ffvelrnd
    cc0
    cpnf
    @91
    icogelb
    syl3anc
    wph
    @78
    cM
    @36
    cfv
    #
    @91
    @78
    @93
    wceq
    wph
    cM
    cG
    @36
    sge0isum.g
    fveq1i
    a1i
    wph
    @30
    @93
    @91
    wceq
    sge0isum.m
    caddc
    cF
    cM
    seq1
    syl
    eqtr2d
    breqtrd
    wph
    @80
    @1
    c0
    wne
    #
    vz
    cv
    #
    @23
    cle
    wbr
    #
    vz
    @1
    wral
    #
    vx
    cr
    wrex
    #
    @85
    @78
    @2
    cle
    wbr
    @82
    wph
    @85
    @94
    @90
    @1
    @78
    ne0i
    syl
    #
    wph
    @29
    @98
    @60
    wph
    @28
    @97
    vx
    cr
    wph
    @28
    @97
    wph
    @28
    wa
    #
    @96
    vz
    @1
    @100
    @95
    @1
    wcel
    #
    wa
    #
    @21
    @95
    wceq
    #
    vj
    cZ
    wrex
    #
    @96
    wph
    @101
    @104
    @28
    wph
    @101
    wa
    #
    @101
    @104
    wph
    @101
    simpr
    wph
    @101
    @104
    wb
    #
    @101
    wph
    cG
    cZ
    wfn
    #
    @106
    wph
    @79
    @107
    @81
    cZ
    cr
    cG
    ffn
    syl
    vj
    cZ
    @95
    cG
    fvelrnb
    syl
    adantr
    mpbid
    #
    adantlr
    @102
    @103
    @96
    vj
    cZ
    @100
    @101
    vj
    wph
    @28
    vj
    wph
    vj
    nfv
    @27
    vj
    cZ
    nfra1
    nfan
    @101
    vj
    nfv
    nfan
    @96
    vj
    nfv
    @28
    @37
    @103
    @96
    wi
    wi
    wph
    @101
    @28
    @37
    @103
    @96
    @28
    @37
    @103
    w3a
    @27
    @103
    @96
    @28
    @37
    @27
    @103
    @27
    vj
    cZ
    rspa
    3adant3
    @28
    @37
    @103
    simp3
    @27
    @103
    wa
    @95
    @21
    @23
    cle
    @103
    @95
    @21
    wceq
    @27
    @103
    @21
    @95
    @103
    id
    eqcomd
    adantl
    @27
    @103
    simpl
    eqbrtrd
    syl2anc
    3exp
    ad2antlr
    rexlimd
    mpd
    ralrimiva
    ex
    reximdv
    mpd
    #
    @90
    vx
    vz
    @1
    @78
    suprub
    syl31anc
    letrd
    ad2antrr
    eqbrtrd
    @74
    @75
    wn
    #
    wa
    #
    @69
    vk
    cM
    @67
    cr
    clt
    csup
    #
    cfz
    co
    #
    @11
    cmpt
    #
    csumge0
    cfv
    #
    @2
    @74
    @69
    cxr
    wcel
    @110
    @74
    @68
    @72
    @67
    wph
    @73
    simpr
    @74
    vk
    @67
    @11
    @6
    @68
    @74
    @10
    @67
    wcel
    #
    wa
    wph
    @12
    @11
    @6
    wcel
    #
    wph
    @73
    @116
    simpll
    @73
    @116
    @12
    wph
    @73
    @67
    cZ
    @10
    @67
    cZ
    cfn
    elpwinss
    #
    sselda
    adantll
    @13
    @5
    @6
    @11
    @7
    @15
    sseldi
    #
    syl2anc
    @68
    eqid
    fmptd
    sge0xrcl
    adantr
    @74
    @115
    cxr
    wcel
    @110
    @74
    @114
    cfn
    @113
    @74
    cM
    @112
    fzfid
    #
    wph
    @113
    @6
    @114
    wf
    @73
    wph
    vk
    @113
    @11
    @6
    @114
    @10
    @113
    wcel
    #
    wph
    @12
    @117
    @121
    @10
    @3
    cZ
    @10
    cM
    @112
    elfzuz
    @87
    syl6eleq
    #
    @119
    sylan2
    @114
    eqid
    fmptd
    adantr
    sge0xrcl
    adantr
    @74
    @2
    cxr
    wcel
    #
    @110
    wph
    @123
    @73
    @63
    adantr
    adantr
    @74
    @69
    @115
    cle
    wbr
    @110
    @74
    vk
    @113
    @11
    @67
    cfn
    @120
    @74
    @121
    wa
    #
    wph
    @12
    @117
    wph
    @73
    @121
    simpll
    #
    @121
    @12
    @74
    @122
    adantl
    #
    @119
    syl2anc
    @73
    @67
    @113
    wss
    wph
    @73
    @67
    cM
    cZ
    sge0isum.z
    @118
    @67
    @71
    cfn
    elinel2
    #
    ssuzfz
    adantl
    sge0lessmpt
    adantr
    @111
    @80
    @94
    @98
    @115
    @1
    wcel
    @115
    @2
    cle
    wbr
    @74
    @80
    @110
    wph
    @80
    @73
    @82
    adantr
    adantr
    @74
    @94
    @110
    wph
    @94
    @73
    @99
    adantr
    adantr
    @74
    @98
    @110
    wph
    @98
    @73
    @109
    adantr
    adantr
    @111
    @115
    @112
    cG
    cfv
    #
    @1
    @111
    @115
    @113
    @11
    vk
    csu
    #
    @112
    @36
    cfv
    #
    @128
    @74
    @115
    @129
    wceq
    @110
    @74
    @113
    @11
    vk
    @120
    @124
    wph
    @12
    @19
    @125
    @126
    @15
    syl2anc
    sge0fsummpt
    adantr
    @111
    @11
    vk
    cF
    cM
    @112
    @111
    @121
    wa
    @11
    eqidd
    @73
    @110
    @112
    @3
    wcel
    wph
    @73
    @110
    wa
    #
    @67
    @3
    @112
    @73
    @67
    @3
    wss
    @110
    @73
    @67
    cZ
    @3
    @118
    sge0isum.z
    syl6sseq
    adantr
    @131
    @67
    cz
    wss
    #
    @67
    c0
    wne
    #
    @67
    cfn
    wcel
    #
    @112
    @67
    wcel
    @73
    @132
    @110
    @73
    @67
    cZ
    cz
    @118
    cZ
    @3
    cz
    sge0isum.z
    cM
    uzssz
    eqsstri
    syl6ss
    adantr
    @110
    @133
    @73
    @67
    c0
    neqne
    adantl
    @73
    @134
    @110
    @127
    adantr
    @67
    suprfinzcl
    syl3anc
    sseldd
    adantll
    #
    @74
    @121
    @11
    cc
    wcel
    #
    @110
    @124
    wph
    @12
    @136
    @125
    @126
    @13
    @11
    @16
    recnd
    #
    syl2anc
    adantlr
    fsumser
    @130
    @128
    wceq
    @111
    @112
    @36
    cG
    cG
    @36
    sge0isum.g
    eqcomi
    #
    fveq1i
    a1i
    3eqtrd
    @111
    @83
    @112
    @84
    wcel
    @128
    @1
    wcel
    @74
    @83
    @110
    wph
    @83
    @73
    @86
    adantr
    adantr
    @111
    @112
    cZ
    @84
    @111
    @112
    @3
    cZ
    @135
    @87
    syl6eleq
    wph
    cZ
    @84
    wceq
    @73
    @110
    @89
    ad2antrr
    eleqtrd
    @112
    cG
    fvelrn
    syl2anc
    eqeltrd
    vx
    vz
    @1
    @115
    suprub
    syl31anc
    xrletrd
    pm2.61dan
    ralrimiva
    wph
    vk
    vy
    cZ
    @11
    @2
    cvv
    wph
    vk
    nfv
    @4
    @119
    @63
    sge0lefimpt
    mpbird
    eqbrtrd
    #
    wph
    @2
    @0
    cle
    wbr
    #
    @95
    @0
    cle
    wbr
    #
    vz
    @1
    wral
    #
    wph
    @141
    vz
    @1
    @105
    @104
    @141
    @108
    @105
    @103
    @141
    vj
    cZ
    wph
    @37
    @103
    @141
    wi
    wi
    @101
    wph
    @37
    @103
    @141
    wph
    @37
    @103
    w3a
    #
    @141
    vk
    @43
    @11
    cmpt
    csumge0
    cfv
    #
    @65
    cle
    wbr
    #
    wph
    @37
    @145
    @103
    wph
    vk
    cZ
    @11
    @43
    cvv
    @4
    @119
    @43
    cZ
    wss
    wph
    vk
    @43
    cZ
    @47
    ssriv
    a1i
    sge0lessmpt
    3ad2ant1
    @143
    @95
    @144
    @0
    @65
    cle
    @143
    @144
    @39
    @21
    @95
    @143
    @144
    @43
    @11
    vk
    csu
    #
    @39
    wph
    @37
    @144
    @146
    wceq
    @103
    wph
    @43
    @11
    vk
    wph
    cM
    @20
    fzfid
    @44
    wph
    @12
    @19
    @47
    @15
    sylan2
    sge0fsummpt
    3ad2ant1
    wph
    @37
    @146
    @39
    wceq
    @103
    @38
    @11
    vk
    cF
    cM
    @20
    @45
    wph
    @12
    @11
    @11
    wceq
    @46
    @48
    @14
    syl2anc
    @42
    @45
    wph
    @12
    @136
    @46
    @48
    @137
    syl2anc
    fsumser
    3adant3
    eqtrd
    @39
    @21
    wceq
    @143
    @20
    @36
    cG
    @138
    fveq1i
    a1i
    wph
    @37
    @103
    simp3
    3eqtrrd
    wph
    @37
    @0
    @65
    wceq
    @103
    @66
    3ad2ant1
    breq12d
    mpbird
    3exp
    adantr
    rexlimdv
    mpd
    ralrimiva
    wph
    @80
    @94
    @98
    @0
    cr
    wcel
    #
    @140
    @142
    wb
    @82
    @99
    @109
    wph
    @0
    @6
    wcel
    @0
    cpnf
    wne
    @147
    wph
    cF
    cvv
    cZ
    @4
    @8
    sge0cl
    wph
    cpnf
    @0
    wph
    @0
    cpnf
    @9
    @92
    wph
    @0
    @2
    cpnf
    @9
    @63
    @92
    @139
    wph
    @2
    @62
    ltpnfd
    xrlelttrd
    xrgtned
    necomd
    @0
    ge0xrre
    syl2anc
    vx
    vz
    vz
    @1
    @0
    suprleub
    syl31anc
    mpbird
    xrletrid
    wph
    @35
    cG
    @2
    cli
    wbr
    cB
    @2
    wceq
    sge0isum.gcnv
    @61
    cB
    @2
    cG
    climuni
    syl2anc
    eqtr4d
end
