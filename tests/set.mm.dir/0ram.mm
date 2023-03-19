include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cn0.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crn.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "wa.mm"
include "cc0.mm"
include "cram.mm"
include "co.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "cvv.mm"
include "chash.mm"
include "cfv.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt2.mm"
include "eqid.mm"
include "0nn0.mm"
include "a1i.mm"
include "simpl1.mm"
include "simpl3.mm"
include "wss.mm"
include "frn.mm"
include "syl.mm"
include "nn0ssz.mm"
include "syl6ss.mm"
include "cdm.mm"
include "fdm.mm"
include "simpl2.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "simpr.mm"
include "suprzcl2.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "csn.mm"
include "ccnv.mm"
include "cima.mm"
include "vex.mm"
include "hashbc0.mm"
include "ax-mp.mm"
include "feq2i.mm"
include "biimpi.mm"
include "simprr.mm"
include "0ex.mm"
include "snid.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "pwid.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "nn0red.mm"
include "rexrd.mm"
include "cxr.mm"
include "hashxrcl.mm"
include "mp1i.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "suprzub.mm"
include "simprl.mm"
include "xrletrd.mm"
include "fvex.mm"
include "wb.mm"
include "elpreima.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "fveq2.mm"
include "breq1d.mm"
include "sseq1i.mm"
include "snss.mm"
include "bitr4i.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "eleq2d.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "breq2d.mm"
include "anbi1d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "sylanr2.mm"
include "ramub.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "cn.mm"
include "c1.mm"
include "cmin.mm"
include "cop.mm"
include "simpll1.mm"
include "simpll3.mm"
include "nnm1nn0.mm"
include "ad2antll.mm"
include "cfz.mm"
include "wf1o.mm"
include "f1osn.mm"
include "f1of.mm"
include "snssd.mm"
include "fss.mm"
include "sylancr.mm"
include "ovex.mm"
include "sylibr.mm"
include "cdom.mm"
include "cfn.mm"
include "fzfid.mm"
include "ssdomg.mm"
include "sylc.mm"
include "ssfi.mm"
include "hashdom.mm"
include "mpbird.mm"
include "hashfz1.mm"
include "breqtrd.mm"
include "hashcl.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "nn0ltlem1.mm"
include "fvsn.mm"
include "f1ofn.mm"
include "mp2b.mm"
include "simprbi.mm"
include "syl5eqelr.mm"
include "elsni.mm"
include "fveq2d.mm"
include "syl5ibcom.mm"
include "syl5bi.mm"
include "ramlb.mm"
include "ramubcl.mm"
include "syl32anc.mm"
include "nn0lem1lt.mm"
include "expr.mm"
include "nn0ge0d.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "wo.mm"
include "elnn0.mm"
include "mpjaod.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "letri3d.mm"

theorem 0ram
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cF: class F
  let cV: class V
  let vb: setvar b
  let vd: setvar d
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vs: setvar s
  let cC: class C
  let va: setvar a
  let vi: setvar i
  let cM: class M

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint F x
  disjoint F y
  disjoint V x
  disjoint b d
  disjoint b z
  disjoint d z
  disjoint c f
  disjoint c s
  disjoint c x
  disjoint C c
  disjoint f s
  disjoint f x
  disjoint C f
  disjoint s x
  disjoint C s
  disjoint C x
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a i
  disjoint a s
  disjoint a x
  disjoint M a
  disjoint b c
  disjoint b f
  disjoint b i
  disjoint b s
  disjoint b x
  disjoint M b
  disjoint c i
  disjoint M c
  disjoint f i
  disjoint M f
  disjoint i s
  disjoint i x
  disjoint M i
  disjoint M s
  disjoint M x
  disjoint c d
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint d f
  disjoint d s
  disjoint d x
  disjoint d y
  disjoint R d
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint s y
  disjoint s z
  disjoint R s
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint a d
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint F c
  disjoint d i
  disjoint F d
  disjoint F f
  disjoint i y
  disjoint i z
  disjoint F i
  disjoint F s
  disjoint F z
  disjoint V c
  disjoint V d
  disjoint V f
  disjoint V s
  disjoint V z
  assert |- ( ( ( R e. V /\ R =/= (/) /\ F : R --> NN0 ) /\ E. x e. ZZ A. y e. ran F y <_ x ) -> ( 0 Ramsey F ) = sup ( ran F , RR , < ) )

  proof
    cR
    cV
    wcel
    #
    cR
    c0
    wne
    #
    cR
    cn0
    cF
    wf
    #
    w3a
    #
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cF
    crn
    #
    wral
    vx
    cz
    wrex
    #
    wa
    #
    cc0
    cF
    cram
    co
    #
    @4
    cr
    clt
    csup
    #
    wceq
    @7
    @8
    cle
    wbr
    #
    @8
    @7
    cle
    wbr
    #
    @6
    vz
    va
    vi
    cvv
    cn0
    vb
    cv
    chash
    cfv
    vi
    cv
    wceq
    vb
    va
    cv
    cpw
    crab
    cmpt2
    #
    cR
    vf
    vi
    cF
    cc0
    @8
    cV
    vs
    va
    vb
    vc
    @11
    eqid
    #
    cc0
    cn0
    wcel
    #
    @6
    0nn0
    a1i
    #
    @0
    @1
    @2
    @5
    simpl1
    #
    @0
    @1
    @2
    @5
    simpl3
    #
    @6
    @4
    cn0
    @8
    @6
    @2
    @4
    cn0
    wss
    @16
    cR
    cn0
    cF
    frn
    syl
    #
    @6
    @4
    cz
    wss
    #
    @4
    c0
    wne
    #
    @5
    @8
    @4
    wcel
    #
    @6
    @4
    cn0
    cz
    @17
    nn0ssz
    syl6ss
    #
    @6
    cF
    cdm
    #
    c0
    wne
    @19
    @6
    @22
    cR
    c0
    @6
    @2
    @22
    cR
    wceq
    @16
    cR
    cn0
    cF
    fdm
    syl
    @0
    @1
    @2
    @5
    simpl2
    eqnetrd
    @22
    c0
    @4
    c0
    cF
    dm0rn0
    necon3bii
    sylib
    @3
    @5
    simpr
    #
    vx
    vy
    @4
    suprzcl2
    syl3anc
    #
    sseldd
    #
    vs
    cv
    #
    cc0
    @11
    co
    #
    cR
    vf
    cv
    #
    wf
    #
    @6
    @8
    @26
    chash
    cfv
    #
    cle
    wbr
    #
    c0
    csn
    #
    cR
    @28
    wf
    #
    vc
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @36
    cc0
    @11
    co
    #
    @28
    ccnv
    #
    @34
    csn
    #
    cima
    #
    wss
    #
    wa
    #
    vz
    @26
    cpw
    #
    wrex
    vc
    cR
    wrex
    #
    @29
    @33
    @27
    @32
    cR
    @28
    @26
    cvv
    wcel
    #
    @27
    @32
    wceq
    vs
    vex
    #
    @26
    @11
    vi
    cvv
    va
    vb
    @12
    hashbc0
    ax-mp
    feq2i
    biimpi
    @6
    @31
    @33
    wa
    #
    wa
    #
    c0
    @28
    cfv
    #
    cR
    wcel
    #
    @26
    @45
    wcel
    #
    @51
    cF
    cfv
    #
    @30
    cle
    wbr
    #
    c0
    @40
    @51
    csn
    #
    cima
    #
    wcel
    #
    @46
    @50
    @33
    c0
    @32
    wcel
    #
    @52
    @6
    @31
    @33
    simprr
    #
    c0
    0ex
    snid
    #
    @32
    cR
    c0
    @28
    ffvelrn
    sylancl
    #
    @53
    @50
    @26
    @48
    pwid
    a1i
    @50
    @54
    @8
    @30
    @50
    @54
    @50
    @54
    @50
    cR
    cn0
    @51
    cF
    @6
    @2
    @49
    @16
    adantr
    #
    @62
    ffvelrnd
    nn0red
    rexrd
    @6
    @8
    cxr
    wcel
    @49
    @6
    @8
    @6
    @8
    @25
    nn0red
    #
    rexrd
    adantr
    @47
    @30
    cxr
    wcel
    @50
    @48
    @26
    cvv
    hashxrcl
    mp1i
    @50
    @18
    @5
    @54
    @4
    wcel
    #
    @54
    @8
    cle
    wbr
    @6
    @18
    @49
    @21
    adantr
    @6
    @5
    @49
    @23
    adantr
    @50
    cF
    cR
    wfn
    #
    @52
    @65
    @50
    @2
    @66
    @63
    cR
    cn0
    cF
    ffn
    #
    syl
    @62
    cR
    @51
    cF
    fnfvelrn
    syl2anc
    vx
    vy
    @4
    @54
    suprzub
    syl3anc
    @6
    @31
    @33
    simprl
    xrletrd
    @50
    @58
    @59
    @51
    @56
    wcel
    #
    @59
    @50
    @61
    a1i
    @68
    @50
    @51
    c0
    @28
    fvex
    snid
    a1i
    @50
    @33
    @28
    @32
    wfn
    @58
    @59
    @68
    wa
    wb
    @60
    @32
    cR
    @28
    ffn
    @32
    c0
    @56
    @28
    elpreima
    3syl
    mpbir2and
    @44
    @55
    @58
    wa
    @54
    @37
    cle
    wbr
    #
    @58
    wa
    vc
    vz
    @51
    @26
    cR
    @45
    @34
    @51
    wceq
    #
    @38
    @69
    @43
    @58
    @70
    @35
    @54
    @37
    cle
    @34
    @51
    cF
    fveq2
    breq1d
    @43
    c0
    @42
    wcel
    #
    @70
    @58
    @43
    @32
    @42
    wss
    @71
    @39
    @32
    @42
    @36
    cvv
    wcel
    @39
    @32
    wceq
    vz
    vex
    @36
    @11
    vi
    cvv
    va
    vb
    @12
    hashbc0
    ax-mp
    #
    sseq1i
    c0
    @42
    0ex
    snss
    bitr4i
    @70
    @42
    @57
    c0
    @70
    @41
    @56
    @40
    @34
    @51
    sneq
    imaeq2d
    eleq2d
    syl5bb
    anbi12d
    @36
    @26
    wceq
    #
    @69
    @55
    @58
    @73
    @37
    @30
    @54
    cle
    @36
    @26
    chash
    fveq2
    breq2d
    anbi1d
    rspc2ev
    syl112anc
    sylanr2
    ramub
    #
    @6
    @35
    @8
    wceq
    #
    vc
    cR
    wrex
    #
    @10
    @6
    @20
    @76
    @24
    @6
    @2
    @66
    @20
    @76
    wb
    @16
    @67
    vc
    cR
    @8
    cF
    fvelrnb
    3syl
    mpbid
    @6
    @75
    @10
    vc
    cR
    @6
    @34
    cR
    wcel
    #
    wa
    #
    @35
    @7
    cle
    wbr
    #
    @75
    @10
    @78
    @35
    cn
    wcel
    #
    @79
    @35
    cc0
    wceq
    #
    @6
    @77
    @80
    @79
    @6
    @77
    @80
    wa
    #
    wa
    #
    @79
    @35
    c1
    cmin
    co
    #
    @7
    clt
    wbr
    #
    @83
    vz
    @11
    cR
    vi
    cF
    c0
    @34
    cop
    csn
    #
    cc0
    @84
    cV
    va
    vb
    vd
    @12
    @13
    @83
    0nn0
    a1i
    @0
    @1
    @2
    @5
    @82
    simpll1
    @0
    @1
    @2
    @5
    @82
    simpll3
    @80
    @84
    cn0
    wcel
    #
    @6
    @77
    @35
    nnm1nn0
    ad2antll
    #
    @83
    @32
    cR
    @86
    wf
    #
    c1
    @84
    cfz
    co
    #
    cc0
    @11
    co
    #
    cR
    @86
    wf
    @83
    @32
    @41
    @86
    wf
    #
    @41
    cR
    wss
    @89
    @32
    @41
    @86
    wf1o
    #
    @92
    c0
    @34
    0ex
    vc
    vex
    #
    f1osn
    #
    @32
    @41
    @86
    f1of
    ax-mp
    @83
    @34
    cR
    @6
    @77
    @80
    simprl
    snssd
    @32
    @41
    cR
    @86
    fss
    sylancr
    @91
    @32
    cR
    @86
    @90
    cvv
    wcel
    @91
    @32
    wceq
    c1
    @84
    cfz
    ovex
    @90
    @11
    vi
    cvv
    va
    vb
    @12
    hashbc0
    ax-mp
    feq2i
    sylibr
    @39
    @86
    ccnv
    vd
    cv
    #
    csn
    #
    cima
    #
    wss
    #
    c0
    @98
    wcel
    #
    @83
    @96
    cR
    wcel
    #
    @36
    @90
    wss
    #
    wa
    #
    wa
    #
    @37
    @96
    cF
    cfv
    #
    clt
    wbr
    #
    @99
    @32
    @98
    wss
    @100
    @39
    @32
    @98
    @72
    sseq1i
    c0
    @98
    0ex
    snss
    bitr4i
    @104
    @37
    @35
    clt
    wbr
    #
    @100
    @106
    @104
    @107
    @37
    @84
    cle
    wbr
    #
    @104
    @37
    @90
    chash
    cfv
    #
    @84
    cle
    @104
    @37
    @109
    cle
    wbr
    #
    @36
    @90
    cdom
    wbr
    #
    @104
    @90
    cfn
    wcel
    #
    @102
    @111
    @104
    c1
    @84
    fzfid
    #
    @83
    @101
    @102
    simprr
    #
    @36
    @90
    cfn
    ssdomg
    sylc
    @104
    @36
    cfn
    wcel
    #
    @112
    @110
    @111
    wb
    @104
    @112
    @102
    @115
    @113
    @114
    @90
    @36
    ssfi
    syl2anc
    #
    @113
    @36
    @90
    cfn
    hashdom
    syl2anc
    mpbird
    @104
    @87
    @109
    @84
    wceq
    @83
    @87
    @103
    @88
    adantr
    @84
    hashfz1
    syl
    breqtrd
    @104
    @37
    cn0
    wcel
    #
    @35
    cn0
    wcel
    #
    @107
    @108
    wb
    @104
    @115
    @117
    @116
    @36
    hashcl
    syl
    @83
    @118
    @103
    @6
    @77
    @118
    @80
    @6
    cR
    cn0
    @34
    cF
    @16
    ffvelrnda
    #
    adantrr
    #
    adantr
    @37
    @35
    nn0ltlem1
    syl2anc
    mpbird
    @100
    @35
    @105
    @37
    clt
    @100
    @34
    @96
    cF
    @100
    @34
    @97
    wcel
    @34
    @96
    wceq
    @100
    @34
    c0
    @86
    cfv
    #
    @97
    c0
    @34
    0ex
    @94
    fvsn
    @100
    @59
    @121
    @97
    wcel
    #
    @93
    @86
    @32
    wfn
    @100
    @59
    @122
    wa
    wb
    @95
    @32
    @41
    @86
    f1ofn
    @32
    c0
    @97
    @86
    elpreima
    mp2b
    simprbi
    syl5eqelr
    @34
    @96
    elsni
    syl
    fveq2d
    breq2d
    syl5ibcom
    syl5bi
    ramlb
    @83
    @118
    @7
    cn0
    wcel
    #
    @79
    @85
    wb
    @120
    @6
    @123
    @82
    @6
    @13
    @0
    @2
    @8
    cn0
    wcel
    @9
    @123
    @14
    @15
    @16
    @25
    @74
    @8
    cR
    cF
    cc0
    cV
    ramubcl
    syl32anc
    #
    adantr
    @35
    @7
    nn0lem1lt
    syl2anc
    mpbird
    expr
    @78
    @79
    @81
    cc0
    @7
    cle
    wbr
    @78
    @7
    @6
    @123
    @77
    @124
    adantr
    nn0ge0d
    @35
    cc0
    @7
    cle
    breq1
    syl5ibrcom
    @78
    @118
    @80
    @81
    wo
    @119
    @35
    elnn0
    sylib
    mpjaod
    @35
    @8
    @7
    cle
    breq1
    syl5ibcom
    rexlimdva
    mpd
    @6
    @7
    @8
    @6
    @7
    @124
    nn0red
    @64
    letri3d
    mpbir2and
end
