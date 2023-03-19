include "c0.mm"
include "wceq.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cn.mm"
include "cv.mm"
include "cico.mm"
include "cfv.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "csn.mm"
include "cvv.mm"
include "wcel.mm"
include "reex.mm"
include "mapdm0.mm"
include "ax-mp.mm"
include "a1i.mm"
include "oveq2.mm"
include "ixpeq1.mm"
include "iuneq2d.mm"
include "ixp0x.mm"
include "iuneq2i.mm"
include "wne.mm"
include "c1.mm"
include "1nn.mm"
include "ne0ii.mm"
include "iunconst.mm"
include "eqtri.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "eqimss.mm"
include "syl.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "cabs.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wbr.mm"
include "rncoss.mm"
include "cc.mm"
include "wf.mm"
include "absf.mm"
include "frn.mm"
include "sstri.mm"
include "wor.mm"
include "cfn.mm"
include "ltso.mm"
include "elmapi.mm"
include "ax-resscn.mm"
include "fssd.mm"
include "fco.mm"
include "syl2anc.mm"
include "adantr.mm"
include "rnffi.mm"
include "cdm.mm"
include "fdmi.mm"
include "eqcomi.mm"
include "sseqtri.mm"
include "sstrd.mm"
include "dmcosseq.mm"
include "fdm.mm"
include "neqne.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "dm0rn0.mm"
include "sylnib.mm"
include "neqned.mm"
include "adantll.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldd.mm"
include "arch.mm"
include "wfn.mm"
include "ffnd.mm"
include "ad2antrr.mm"
include "adantlr.mm"
include "c1st.mm"
include "c2nd.mm"
include "cneg.mm"
include "simplll.mm"
include "id.mm"
include "ad3antlr.mm"
include "w3a.mm"
include "cxr.mm"
include "simp2.mm"
include "cz.mm"
include "zssre.mm"
include "ressxr.mm"
include "nnnegz.mm"
include "sseldi.mm"
include "sylan.mm"
include "nnxrd.mm"
include "3ad2ant1.mm"
include "3adant1l.mm"
include "ffvelrnda.mm"
include "nnre.mm"
include "3ad2antl2.mm"
include "renegcld.mm"
include "3ad2antl1.mm"
include "n0i.mm"
include "syl21anc.mm"
include "abscld.mm"
include "cle.mm"
include "leabsd.mm"
include "absnegd.mm"
include "breqtrd.mm"
include "syldan.mm"
include "fimaxre2.mm"
include "sylancr.mm"
include "wfun.mm"
include "elmapfun.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvco.mm"
include "absfun.mm"
include "funco.mm"
include "syl6eleq.mm"
include "wb.mm"
include "dmfco.mm"
include "mpbird.mm"
include "fvelrn.mm"
include "eqeltrd.mm"
include "suprub.mm"
include "syl31anc.mm"
include "letrd.mm"
include "simpl3.mm"
include "lelttrd.mm"
include "ltnegd.mm"
include "mpbid.mm"
include "negnegd.mm"
include "ltled.mm"
include "elicod.mm"
include "adantlllr.mm"
include "cop.mm"
include "cmpt.mm"
include "mptexg.mm"
include "fvmpt2.mm"
include "fveq1d.mm"
include "3adant3.mm"
include "eqidd.mm"
include "eqid.mm"
include "opex.mm"
include "fvmptd.mm"
include "3ad2ant3.mm"
include "fveq2d.mm"
include "negex.mm"
include "vex.mm"
include "op1st.mm"
include "op2nd.mm"
include "oveq12d.mm"
include "3adant1r.mm"
include "ad5ant135.mm"
include "cxp.mm"
include "opelxpi.mm"
include "ad2antlr.mm"
include "fmptd.mm"
include "feq1d.mm"
include "ad4ant14.mm"
include "fvovco.mm"
include "ralrimiva.mm"
include "jca.mm"
include "elixp.mm"
include "sylibr.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "eliun.mm"
include "dfss3.mm"
include "pm2.61dan.mm"

theorem hoicvr
  let wph: wff ph
  let vx: setvar x
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cX: class X
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume hoicvr.2: |- I = ( j e. NN |-> ( x e. X |-> <. -u j , j >. ) )
  assume hoicvr.3: |- ( ph -> X e. Fin )

  disjoint X i
  disjoint X j
  disjoint i j
  disjoint X x
  disjoint i x
  disjoint j x
  disjoint i ph
  disjoint j ph
  disjoint ph x
  disjoint I f
  disjoint X f
  disjoint f i
  disjoint f j
  disjoint f ph
  disjoint f y
  disjoint f z
  disjoint y z
  disjoint k x
  assert |- ( ph -> ( RR ^m X ) C_ U_ j e. NN X_ i e. X ( ( [,) o. ( I ` j ) ) ` i ) )

  proof
    wph
    cX
    c0
    wceq
    #
    cr
    cX
    cmap
    co
    #
    vj
    cn
    vi
    cX
    vi
    cv
    #
    cico
    vj
    cv
    #
    cI
    cfv
    #
    ccom
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    @0
    @8
    wph
    @0
    @1
    @7
    wceq
    @8
    @0
    cr
    c0
    cmap
    co
    #
    c0
    csn
    #
    @1
    @7
    @9
    @10
    wceq
    #
    @0
    cr
    cvv
    wcel
    @11
    reex
    cr
    cvv
    mapdm0
    ax-mp
    a1i
    cX
    c0
    cr
    cmap
    oveq2
    @0
    @7
    vj
    cn
    vi
    c0
    @5
    cixp
    #
    ciun
    #
    @10
    @0
    vj
    cn
    @6
    @12
    vi
    cX
    c0
    @5
    ixpeq1
    iuneq2d
    @13
    @10
    wceq
    @0
    @13
    vj
    cn
    @10
    ciun
    #
    @10
    vj
    cn
    @12
    @10
    @12
    @10
    wceq
    @3
    cn
    wcel
    #
    vi
    @5
    ixp0x
    a1i
    iuneq2i
    cn
    c0
    wne
    @14
    @10
    wceq
    c1
    cn
    1nn
    ne0ii
    vj
    cn
    @10
    iunconst
    ax-mp
    eqtri
    a1i
    eqtrd
    3eqtr4d
    @1
    @7
    eqimss
    syl
    adantl
    wph
    @0
    wn
    #
    wa
    #
    vf
    cv
    #
    @7
    wcel
    #
    vf
    @1
    wral
    @8
    @17
    @19
    vf
    @1
    @17
    @18
    @1
    wcel
    #
    wa
    #
    @18
    @6
    wcel
    #
    vj
    cn
    wrex
    #
    @19
    @21
    wph
    @20
    @16
    @23
    wph
    @16
    @20
    simpll
    @17
    @20
    simpr
    wph
    @16
    @20
    simplr
    wph
    @20
    wa
    #
    @16
    wa
    #
    cabs
    @18
    ccom
    #
    crn
    #
    cr
    clt
    csup
    #
    @3
    clt
    wbr
    #
    vj
    cn
    wrex
    #
    @23
    @25
    @28
    cr
    wcel
    #
    @30
    @25
    @27
    cr
    @28
    @27
    cr
    wss
    #
    @25
    @27
    cabs
    crn
    #
    cr
    cabs
    @18
    rncoss
    cc
    cr
    cabs
    wf
    #
    @33
    cr
    wss
    absf
    cc
    cr
    cabs
    frn
    ax-mp
    sstri
    #
    a1i
    #
    @25
    cr
    clt
    wor
    #
    @27
    cfn
    wcel
    #
    @27
    c0
    wne
    #
    @32
    @28
    @27
    wcel
    @37
    @25
    ltso
    a1i
    @24
    @38
    @16
    @24
    cX
    cr
    @26
    wf
    #
    cX
    cfn
    wcel
    #
    @38
    @24
    @34
    cX
    cc
    @18
    wf
    @40
    @34
    @24
    absf
    a1i
    @24
    cX
    cr
    cc
    @18
    @20
    cX
    cr
    @18
    wf
    #
    wph
    @18
    cr
    cX
    elmapi
    #
    adantl
    #
    cr
    cc
    wss
    @24
    ax-resscn
    a1i
    fssd
    cX
    cc
    cr
    cabs
    @18
    fco
    syl2anc
    wph
    @41
    @20
    hoicvr.3
    adantr
    cX
    cr
    @26
    rnffi
    syl2anc
    #
    adantr
    @20
    @16
    @39
    wph
    @20
    @16
    wa
    #
    @27
    c0
    @46
    @26
    cdm
    #
    c0
    wceq
    @27
    c0
    wceq
    @46
    @47
    c0
    @46
    @47
    cX
    c0
    @20
    @47
    cX
    wceq
    @16
    @20
    @47
    @18
    cdm
    #
    cX
    @20
    @18
    crn
    #
    cabs
    cdm
    #
    wss
    @47
    @48
    wceq
    @20
    @49
    cr
    @50
    @20
    @42
    @49
    cr
    wss
    @43
    cX
    cr
    @18
    frn
    syl
    cr
    @50
    wss
    @20
    cr
    cc
    @50
    ax-resscn
    @50
    cc
    cc
    cr
    cabs
    absf
    fdmi
    eqcomi
    #
    sseqtri
    a1i
    sstrd
    cabs
    @18
    dmcosseq
    syl
    @20
    @42
    @48
    cX
    wceq
    @43
    cX
    cr
    @18
    fdm
    syl
    #
    eqtrd
    adantr
    @16
    cX
    c0
    wne
    @20
    cX
    c0
    neqne
    adantl
    eqnetrd
    neneqd
    @26
    dm0rn0
    sylnib
    neqned
    adantll
    #
    @36
    cr
    @27
    clt
    fisupcl
    syl13anc
    sseldd
    #
    @28
    vj
    arch
    syl
    @25
    @29
    @22
    vj
    cn
    @25
    @15
    wa
    #
    @29
    @22
    @55
    @29
    wa
    #
    @18
    cX
    wfn
    #
    @2
    @18
    cfv
    #
    @5
    wcel
    #
    vi
    cX
    wral
    #
    wa
    @22
    @56
    @57
    @60
    @25
    @29
    @57
    @15
    @24
    @57
    @16
    @29
    @24
    cX
    cr
    @18
    @44
    ffnd
    ad2antrr
    adantlr
    @56
    @59
    vi
    cX
    @56
    @2
    cX
    wcel
    #
    wa
    #
    @58
    @2
    @4
    cfv
    #
    c1st
    cfv
    #
    @63
    c2nd
    cfv
    #
    cico
    co
    #
    @5
    @62
    @58
    @3
    cneg
    #
    @3
    cico
    co
    #
    @66
    @24
    @15
    @29
    @61
    @58
    @68
    wcel
    #
    @16
    @24
    @15
    wa
    #
    @29
    wa
    #
    @61
    wa
    @24
    @15
    @29
    @61
    @69
    @24
    @15
    @29
    @61
    simplll
    @15
    @15
    @24
    @29
    @61
    @15
    id
    #
    ad3antlr
    @70
    @29
    @61
    simplr
    @71
    @61
    simpr
    @24
    @15
    @29
    w3a
    #
    @61
    wa
    #
    @67
    @3
    @58
    @73
    @15
    @61
    @67
    cxr
    wcel
    #
    @24
    @15
    @29
    simp2
    #
    @15
    @75
    @61
    @15
    cz
    cxr
    @67
    cz
    cr
    cxr
    zssre
    ressxr
    sstri
    @3
    nnnegz
    #
    sseldi
    adantr
    sylan
    @73
    @15
    @61
    @3
    cxr
    wcel
    #
    @76
    @15
    @78
    @61
    @15
    @3
    @72
    nnxrd
    adantr
    sylan
    @73
    cX
    cxr
    @2
    @18
    @20
    @15
    @29
    cX
    cxr
    @18
    wf
    wph
    @20
    @15
    @29
    w3a
    #
    cX
    cr
    cxr
    @18
    @20
    @15
    @42
    @29
    @43
    3ad2ant1
    cr
    cxr
    wss
    @79
    ressxr
    a1i
    fssd
    3adant1l
    ffvelrnda
    @74
    @67
    @58
    @74
    @3
    @15
    @24
    @61
    @3
    cr
    wcel
    #
    @29
    @15
    @80
    @61
    @3
    nnre
    #
    adantr
    3ad2antl2
    #
    renegcld
    @24
    @15
    @61
    @58
    cr
    wcel
    @29
    @24
    cX
    cr
    @2
    @18
    @44
    ffvelrnda
    3ad2antl1
    #
    @74
    @67
    @58
    cneg
    #
    cneg
    #
    @58
    clt
    @74
    @84
    @3
    clt
    wbr
    @67
    @85
    clt
    wbr
    @74
    @84
    @28
    @3
    @74
    @58
    @83
    renegcld
    #
    @24
    @15
    @61
    @31
    @29
    @24
    @61
    wa
    wph
    @20
    @16
    @31
    wph
    @20
    @61
    simpll
    wph
    @20
    @61
    simplr
    @61
    @16
    @24
    cX
    @2
    n0i
    adantl
    #
    @54
    syl21anc
    3ad2antl1
    #
    @82
    @74
    @84
    @58
    cabs
    cfv
    #
    @28
    @86
    @24
    @15
    @61
    @89
    cr
    wcel
    #
    @29
    @20
    @61
    @90
    wph
    @20
    @61
    wa
    #
    @58
    @91
    cr
    cc
    @58
    ax-resscn
    @20
    cX
    cr
    @2
    @18
    @43
    ffvelrnda
    #
    sseldi
    #
    abscld
    adantll
    3ad2antl1
    #
    @88
    @24
    @15
    @61
    @84
    @89
    cle
    wbr
    #
    @29
    @20
    @61
    @95
    wph
    @91
    @84
    @84
    cabs
    cfv
    @89
    cle
    @91
    @84
    @91
    @58
    @92
    renegcld
    leabsd
    @91
    @58
    @93
    absnegd
    breqtrd
    adantll
    3ad2antl1
    @74
    @32
    @39
    vz
    cv
    vy
    cv
    cle
    wbr
    vz
    @27
    wral
    vy
    cr
    wrex
    #
    @89
    @27
    wcel
    #
    @89
    @28
    cle
    wbr
    @32
    @74
    @35
    a1i
    @24
    @15
    @61
    @39
    @29
    @24
    @61
    @16
    @39
    @87
    @53
    syldan
    3ad2antl1
    @24
    @15
    @61
    @96
    @29
    @24
    @96
    @61
    @24
    @32
    @38
    @96
    @35
    @45
    vy
    vz
    @27
    fimaxre2
    sylancr
    adantr
    3ad2antl1
    @24
    @15
    @61
    @97
    @29
    @20
    @61
    @97
    wph
    @91
    @89
    @2
    @26
    cfv
    #
    @27
    @91
    @98
    @89
    @91
    @18
    wfun
    #
    @2
    @48
    wcel
    #
    @98
    @89
    wceq
    @20
    @99
    @61
    @18
    cr
    cX
    elmapfun
    #
    adantr
    #
    @91
    @2
    cX
    @48
    @20
    @61
    simpr
    @20
    cX
    @48
    wceq
    @61
    @20
    @48
    cX
    @52
    eqcomd
    adantr
    eleqtrd
    #
    @2
    cabs
    @18
    fvco
    syl2anc
    eqcomd
    @91
    @26
    wfun
    #
    @2
    @47
    wcel
    #
    @98
    @27
    wcel
    @20
    @104
    @61
    @20
    cabs
    wfun
    #
    @99
    @104
    @106
    @20
    absfun
    a1i
    @101
    cabs
    @18
    funco
    syl2anc
    adantr
    @91
    @105
    @58
    @50
    wcel
    #
    @91
    @58
    cc
    @50
    @93
    @51
    syl6eleq
    @91
    @99
    @100
    @105
    @107
    wb
    @102
    @103
    @2
    cabs
    @18
    dmfco
    syl2anc
    mpbird
    @2
    @26
    fvelrn
    syl2anc
    eqeltrd
    adantll
    3ad2antl1
    vy
    vz
    @27
    @89
    suprub
    syl31anc
    #
    letrd
    @24
    @15
    @29
    @61
    simpl3
    #
    lelttrd
    @74
    @84
    @3
    @86
    @82
    ltnegd
    mpbid
    @74
    @58
    @74
    cr
    cc
    @58
    ax-resscn
    @83
    sseldi
    negnegd
    breqtrd
    ltled
    @74
    @58
    @28
    @3
    @83
    @88
    @82
    @74
    @58
    @89
    @28
    @83
    @94
    @88
    @74
    @58
    @83
    leabsd
    @108
    letrd
    @109
    lelttrd
    elicod
    syl31anc
    adantlllr
    @24
    @15
    @61
    @68
    @66
    wceq
    #
    @16
    @29
    wph
    @15
    @61
    @110
    @20
    wph
    @15
    @61
    w3a
    #
    @66
    @68
    @111
    @64
    @67
    @65
    @3
    cico
    @111
    @64
    @67
    @3
    cop
    #
    c1st
    cfv
    #
    @67
    @111
    @63
    @112
    c1st
    @111
    @63
    @2
    vx
    cX
    @112
    cmpt
    #
    cfv
    #
    @112
    wph
    @15
    @63
    @115
    wceq
    @61
    wph
    @15
    wa
    #
    @2
    @4
    @114
    @116
    @15
    @114
    cvv
    wcel
    #
    @4
    @114
    wceq
    wph
    @15
    simpr
    wph
    @117
    @15
    wph
    @41
    @117
    hoicvr.3
    vx
    cX
    @112
    cfn
    mptexg
    syl
    adantr
    vj
    cn
    @114
    cvv
    cI
    hoicvr.2
    fvmpt2
    syl2anc
    #
    fveq1d
    3adant3
    @61
    wph
    @115
    @112
    wceq
    @15
    @61
    vx
    @2
    @112
    @112
    cX
    @114
    cvv
    @61
    @114
    eqidd
    @112
    @112
    wceq
    @61
    vx
    cv
    #
    @2
    wceq
    wa
    @112
    eqid
    a1i
    @61
    id
    @112
    cvv
    wcel
    @61
    @67
    @3
    opex
    a1i
    fvmptd
    3ad2ant3
    eqtrd
    #
    fveq2d
    @113
    @67
    wceq
    @111
    @67
    @3
    @3
    negex
    #
    vj
    vex
    #
    op1st
    a1i
    eqtrd
    @111
    @65
    @112
    c2nd
    cfv
    #
    @3
    @111
    @63
    @112
    c2nd
    @120
    fveq2d
    @123
    @3
    wceq
    @111
    @67
    @3
    @121
    @122
    op2nd
    a1i
    eqtrd
    oveq12d
    eqcomd
    3adant1r
    ad5ant135
    eleqtrd
    @62
    @5
    @66
    @62
    @4
    cico
    cr
    cr
    cX
    @2
    @55
    cX
    cr
    cr
    cxp
    #
    @4
    wf
    #
    @29
    @61
    wph
    @15
    @125
    @20
    @16
    @116
    @125
    cX
    @124
    @114
    wf
    @116
    vx
    cX
    @112
    @124
    @114
    @15
    @112
    @124
    wcel
    #
    wph
    @119
    cX
    wcel
    @15
    @67
    cr
    wcel
    @80
    @126
    @15
    cz
    cr
    @67
    zssre
    @77
    sseldi
    @81
    @67
    @3
    cr
    cr
    opelxpi
    syl2anc
    ad2antlr
    @114
    eqid
    fmptd
    @116
    cX
    @124
    @4
    @114
    @118
    feq1d
    mpbird
    ad4ant14
    ad2antrr
    @56
    @61
    simpr
    fvovco
    eqcomd
    eleqtrd
    ralrimiva
    jca
    vi
    cX
    @5
    @18
    vf
    vex
    elixp
    sylibr
    ex
    reximdva
    mpd
    syl21anc
    vj
    @18
    cn
    @6
    eliun
    sylibr
    ralrimiva
    vf
    @1
    @7
    dfss3
    sylibr
    pm2.61dan
end
