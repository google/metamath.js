include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cli.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "cdm.mm"
include "cmea.mm"
include "adantr.mm"
include "eqid.mm"
include "ffvelrnda.mm"
include "meaxrcl.mm"
include "meage0.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "simprd.mm"
include "rspa.mm"
include "syl2anc.mm"
include "3ad2ant1.mm"
include "rexr.mm"
include "3ad2ant2.mm"
include "ltpnf.mm"
include "xrlelttrd.mm"
include "syl3anc.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "elicod.mm"
include "fmptd.mm"
include "wss.mm"
include "rge0ssre.mm"
include "fssd.mm"
include "c1.mm"
include "caddc.mm"
include "peano2uzs.mm"
include "adantl.mm"
include "syldan.mm"
include "meassle.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "fvexd.mm"
include "fvmpt2d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fvmptd.mm"
include "breq12d.mm"
include "mpbird.mm"
include "wi.mm"
include "eqcomd.mm"
include "breq1d.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "reximdva.mm"
include "climsup.mm"
include "csumge0.mm"
include "cfz.mm"
include "csu.mm"
include "nfv.mm"
include "cfzo.mm"
include "cdif.mm"
include "id.mm"
include "fvex.mm"
include "difexi.mm"
include "fvmpt2.mm"
include "csalg.mm"
include "dmmeasal.mm"
include "com.mm"
include "cdom.mm"
include "fzoct.mm"
include "wf.mm"
include "cuz.mm"
include "fzossuz.mm"
include "eqcomi.mm"
include "sseqtri.mm"
include "sseli.mm"
include "ffvelrnd.mm"
include "adantlr.mm"
include "saliuncl.mm"
include "saldifcl2.mm"
include "eqeltrd.mm"
include "difssd.mm"
include "eqsstrd.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "iuneq1d.mm"
include "cbviunv.mm"
include "wdisj.mm"
include "iundjiun.mm"
include "simplld.mm"
include "simpr.mm"
include "3eqtrd.mm"
include "chvarv.mm"
include "syl6eleq.mm"
include "oveq1.mm"
include "sseq12d.mm"
include "iunincfi.mm"
include "eqtr2d.mm"
include "elfzuz.mm"
include "eleq1d.mm"
include "fzct.mm"
include "ssd.mm"
include "cbvdisjv.mm"
include "sylib.mm"
include "disjss1.mm"
include "sylc.mm"
include "meadjiun.mm"
include "fzfid.mm"
include "sge0fsummpt.mm"
include "cbvsumv.mm"
include "eqtrd.mm"
include "imp.mm"
include "ex.mm"
include "reximdv.mm"
include "sge0reuzb.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "eqtr4d.mm"
include "uzct.mm"
include "simplrd.mm"
include "breqtrd.mm"

theorem meaiuninclem
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vm: setvar m
  let vk: setvar k
  assume meaiuninclem.m: |- ( ph -> M e. Meas )
  assume meaiuninclem.n: |- ( ph -> N e. ZZ )
  assume meaiuninclem.z: |- Z = ( ZZ>= ` N )
  assume meaiuninclem.e: |- ( ph -> E : Z --> dom M )
  assume meaiuninclem.i: |- ( ( ph /\ n e. Z ) -> ( E ` n ) C_ ( E ` ( n + 1 ) ) )
  assume meaiuninclem.b: |- ( ph -> E. x e. RR A. n e. Z ( M ` ( E ` n ) ) <_ x )
  assume meaiuninclem.s: |- S = ( n e. Z |-> ( M ` ( E ` n ) ) )
  assume meaiuninclem.f: |- F = ( n e. Z |-> ( ( E ` n ) \ U_ i e. ( N ..^ n ) ( E ` i ) ) )

  disjoint E i
  disjoint E n
  disjoint i n
  disjoint E x
  disjoint i x
  disjoint n x
  disjoint F i
  disjoint F n
  disjoint F x
  disjoint M i
  disjoint M n
  disjoint M x
  disjoint N i
  disjoint N n
  disjoint N x
  disjoint S n
  disjoint S x
  disjoint Z i
  disjoint Z n
  disjoint Z x
  disjoint i ph
  disjoint n ph
  disjoint ph x
  disjoint E m
  disjoint i m
  disjoint m n
  disjoint F m
  disjoint M m
  disjoint N m
  disjoint Z m
  disjoint m ph
  disjoint k x
  assert |- ( ph -> S ~~> ( M ` U_ n e. Z ( E ` n ) ) )

  proof
    wph
    cS
    cS
    crn
    #
    cr
    clt
    csup
    #
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cM
    cfv
    #
    cli
    wph
    vx
    vn
    cS
    cN
    cZ
    meaiuninclem.z
    meaiuninclem.n
    wph
    cZ
    cc0
    cpnf
    cico
    co
    #
    cr
    cS
    wph
    vn
    cZ
    @3
    cM
    cfv
    #
    @6
    cS
    wph
    @2
    cZ
    wcel
    #
    wa
    #
    cc0
    cpnf
    @7
    cc0
    cxr
    wcel
    @9
    0xr
    a1i
    #
    cpnf
    cxr
    wcel
    #
    @9
    pnfxr
    a1i
    #
    @9
    @3
    cM
    cdm
    #
    cM
    wph
    cM
    cmea
    wcel
    @8
    meaiuninclem.m
    adantr
    #
    @13
    eqid
    #
    wph
    cZ
    @13
    @2
    cE
    meaiuninclem.e
    ffvelrnda
    #
    meaxrcl
    #
    @9
    @3
    cM
    @14
    @16
    meage0
    @9
    @7
    vx
    cv
    #
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @7
    cpnf
    clt
    wbr
    #
    wph
    @21
    @8
    meaiuninclem.b
    adantr
    @9
    @20
    @22
    vx
    cr
    @9
    @18
    cr
    wcel
    #
    @20
    @22
    @9
    @23
    @20
    w3a
    #
    @9
    @23
    @19
    @22
    @9
    @23
    @20
    simp1
    #
    @9
    @23
    @20
    simp2
    @24
    @20
    @8
    @19
    @9
    @23
    @20
    simp3
    @24
    wph
    @8
    @25
    simprd
    @19
    vn
    cZ
    rspa
    syl2anc
    @9
    @23
    @19
    w3a
    #
    @7
    @18
    cpnf
    @9
    @23
    @7
    cxr
    wcel
    @19
    @17
    3ad2ant1
    @23
    @9
    @18
    cxr
    wcel
    @19
    @18
    rexr
    3ad2ant2
    @11
    @26
    pnfxr
    a1i
    @9
    @23
    @19
    simp3
    @23
    @9
    @18
    cpnf
    clt
    wbr
    @19
    @18
    ltpnf
    3ad2ant2
    xrlelttrd
    syl3anc
    3exp
    rexlimdv
    mpd
    #
    elicod
    meaiuninclem.s
    fmptd
    @6
    cr
    wss
    wph
    rge0ssre
    a1i
    fssd
    @9
    @2
    cS
    cfv
    #
    @2
    c1
    caddc
    co
    #
    cS
    cfv
    #
    cle
    wbr
    @7
    @29
    cE
    cfv
    #
    cM
    cfv
    #
    cle
    wbr
    @9
    @3
    @31
    @13
    cM
    @14
    @15
    @16
    wph
    @8
    @29
    cZ
    wcel
    #
    @31
    @13
    wcel
    @8
    @33
    wph
    cN
    @2
    cZ
    meaiuninclem.z
    peano2uzs
    adantl
    #
    wph
    cZ
    @13
    @29
    cE
    meaiuninclem.e
    ffvelrnda
    syldan
    meaiuninclem.i
    meassle
    @9
    @28
    @7
    @30
    @32
    cle
    wph
    vn
    cZ
    @7
    cS
    cvv
    cS
    vn
    cZ
    @7
    cmpt
    #
    wceq
    wph
    meaiuninclem.s
    a1i
    @9
    @3
    cM
    fvexd
    fvmpt2d
    #
    @9
    vm
    @29
    vm
    cv
    #
    cE
    cfv
    #
    cM
    cfv
    #
    @32
    cZ
    cS
    cvv
    cS
    vm
    cZ
    @39
    cmpt
    #
    wceq
    @9
    cS
    @35
    @40
    meaiuninclem.s
    vn
    vm
    cZ
    @7
    @39
    @2
    @37
    wceq
    @3
    @38
    cM
    @2
    @37
    cE
    fveq2
    fveq2d
    cbvmptv
    eqtri
    a1i
    @37
    @29
    wceq
    #
    @39
    @32
    wceq
    @9
    @41
    @38
    @31
    cM
    @37
    @29
    cE
    fveq2
    fveq2d
    adantl
    @34
    @9
    @31
    cM
    fvexd
    fvmptd
    breq12d
    mpbird
    wph
    @21
    @28
    @18
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vx
    cr
    wrex
    meaiuninclem.b
    wph
    @20
    @43
    vx
    cr
    wph
    @20
    @43
    wi
    @23
    wph
    @20
    @43
    wph
    @19
    @42
    vn
    cZ
    @9
    @7
    @28
    @18
    cle
    @9
    @28
    @7
    @36
    eqcomd
    breq1d
    ralbidva
    biimpd
    adantr
    reximdva
    mpd
    climsup
    wph
    @1
    vn
    cZ
    @2
    cF
    cfv
    #
    cM
    cfv
    #
    cmpt
    csumge0
    cfv
    #
    vn
    cZ
    @44
    ciun
    #
    cM
    cfv
    #
    @5
    wph
    @46
    @1
    wph
    @46
    vi
    cZ
    cN
    vi
    cv
    #
    cfz
    co
    #
    @45
    vn
    csu
    #
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    @1
    wph
    vx
    @45
    vn
    vi
    cN
    cZ
    wph
    vn
    nfv
    #
    wph
    vx
    nfv
    meaiuninclem.n
    meaiuninclem.z
    @9
    cc0
    cpnf
    @45
    @10
    @12
    @9
    @44
    @13
    cM
    @14
    @15
    @9
    @44
    @3
    vi
    cN
    @2
    cfzo
    co
    #
    @49
    cE
    cfv
    #
    ciun
    #
    cdif
    #
    @13
    @8
    @44
    @58
    wceq
    #
    wph
    @8
    @8
    @58
    cvv
    wcel
    #
    @59
    @8
    id
    #
    @60
    @8
    @3
    @57
    @2
    cE
    fvex
    difexi
    a1i
    vn
    cZ
    @58
    cvv
    cF
    meaiuninclem.f
    fvmpt2
    syl2anc
    adantl
    #
    @9
    @13
    csalg
    wcel
    #
    @3
    @13
    wcel
    @57
    @13
    wcel
    @58
    @13
    wcel
    wph
    @63
    @8
    wph
    @13
    cM
    meaiuninclem.m
    @15
    dmmeasal
    adantr
    #
    @16
    @9
    @13
    vi
    @56
    @55
    @64
    @55
    com
    cdom
    wbr
    @9
    @2
    cN
    fzoct
    a1i
    wph
    @49
    @55
    wcel
    #
    @56
    @13
    wcel
    @8
    wph
    @65
    wa
    cZ
    @13
    @49
    cE
    wph
    cZ
    @13
    cE
    wf
    @65
    meaiuninclem.e
    adantr
    @65
    @49
    cZ
    wcel
    #
    wph
    @55
    cZ
    @49
    @55
    cN
    cuz
    cfv
    #
    cZ
    cN
    @2
    fzossuz
    cZ
    @67
    meaiuninclem.z
    eqcomi
    #
    sseqtri
    sseli
    adantl
    #
    ffvelrnd
    adantlr
    saliuncl
    @13
    @3
    @57
    saldifcl2
    syl3anc
    eqeltrd
    #
    meaxrcl
    #
    @9
    @44
    cM
    @14
    @70
    meage0
    @9
    @45
    @7
    cpnf
    @71
    @17
    @12
    @9
    @44
    @3
    @13
    cM
    @14
    @15
    @70
    @16
    @9
    @44
    @58
    @3
    @62
    @9
    @3
    @57
    difssd
    eqsstrd
    meassle
    @27
    xrlelttrd
    elicod
    #
    wph
    @21
    @51
    @18
    cle
    wbr
    #
    vi
    cZ
    wral
    #
    vx
    cr
    wrex
    meaiuninclem.b
    wph
    @20
    @74
    vx
    cr
    wph
    @20
    @74
    wph
    @20
    @56
    cM
    cfv
    #
    @18
    cle
    wbr
    #
    vi
    cZ
    wral
    #
    @74
    @20
    @77
    wph
    @20
    @77
    @19
    @76
    vn
    vi
    cZ
    @2
    @49
    wceq
    #
    @7
    @75
    @18
    cle
    @78
    @3
    @56
    cM
    @2
    @49
    cE
    fveq2
    #
    fveq2d
    #
    breq1d
    cbvralv
    biimpi
    adantl
    wph
    @77
    @74
    wph
    @77
    @74
    wph
    @76
    @73
    vi
    cZ
    wph
    @66
    wa
    #
    @75
    @51
    @18
    cle
    @81
    @75
    @50
    @37
    cF
    cfv
    #
    cM
    cfv
    #
    vm
    csu
    #
    @51
    @9
    @7
    cN
    @2
    cfz
    co
    #
    @83
    vm
    csu
    #
    wceq
    #
    wi
    @81
    @75
    @84
    wceq
    #
    wi
    vn
    vi
    @78
    @9
    @81
    @87
    @88
    @78
    @8
    @66
    wph
    @2
    @49
    cZ
    eleq1
    anbi2d
    #
    @78
    @7
    @75
    @86
    @84
    @80
    @78
    @85
    @50
    @83
    vm
    @2
    @49
    cN
    cfz
    oveq2
    sumeq1d
    eqeq12d
    imbi12d
    @9
    @7
    vi
    @85
    @49
    cF
    cfv
    #
    ciun
    #
    cM
    cfv
    vi
    @85
    @90
    cM
    cfv
    #
    cmpt
    csumge0
    cfv
    #
    @86
    @9
    @3
    @91
    cM
    @9
    @91
    vi
    @85
    @56
    ciun
    #
    @3
    wph
    @37
    cZ
    wcel
    #
    wa
    #
    vi
    cN
    @37
    cfz
    co
    #
    @90
    ciun
    #
    vi
    @97
    @56
    ciun
    #
    wceq
    #
    wi
    @9
    @91
    @94
    wceq
    #
    wi
    vm
    vn
    @37
    @2
    wceq
    #
    @96
    @9
    @100
    @101
    @102
    @95
    @8
    wph
    @37
    @2
    cZ
    eleq1
    anbi2d
    @102
    @98
    @91
    @99
    @94
    @102
    vi
    @97
    @85
    @90
    @37
    @2
    cN
    cfz
    oveq2
    #
    iuneq1d
    @102
    vi
    @97
    @85
    @56
    @103
    iuneq1d
    eqeq12d
    imbi12d
    @96
    @98
    vn
    @97
    @44
    ciun
    #
    vn
    @97
    @3
    ciun
    #
    @99
    @98
    @104
    wceq
    @96
    vi
    vn
    @97
    @90
    @44
    @49
    @2
    cF
    fveq2
    cbviunv
    a1i
    @96
    @104
    @105
    wceq
    #
    vm
    cZ
    wral
    #
    @95
    @106
    wph
    @107
    @95
    wph
    @107
    @47
    @4
    wceq
    #
    vn
    cZ
    @44
    wdisj
    #
    wph
    vi
    vm
    vn
    cE
    cF
    cN
    @13
    cZ
    @54
    meaiuninclem.z
    meaiuninclem.e
    meaiuninclem.f
    iundjiun
    #
    simplld
    adantr
    wph
    @95
    simpr
    @106
    vm
    cZ
    rspa
    syl2anc
    @105
    @99
    wceq
    @96
    vn
    vi
    @97
    @3
    @56
    @79
    cbviunv
    a1i
    3eqtrd
    chvarv
    @9
    vi
    cE
    cN
    @2
    @8
    @2
    @67
    wcel
    wph
    @8
    @2
    cZ
    @67
    @61
    meaiuninclem.z
    syl6eleq
    adantl
    wph
    @65
    @56
    @49
    c1
    caddc
    co
    #
    cE
    cfv
    #
    wss
    #
    @8
    wph
    @65
    @66
    @113
    @69
    @9
    @3
    @31
    wss
    #
    wi
    @81
    @113
    wi
    vn
    vi
    @78
    @9
    @81
    @114
    @113
    @89
    @78
    @3
    @56
    @31
    @112
    @79
    @78
    @29
    @111
    cE
    @2
    @49
    c1
    caddc
    oveq1
    fveq2d
    sseq12d
    imbi12d
    meaiuninclem.i
    chvarv
    syldan
    adantlr
    iunincfi
    eqtr2d
    fveq2d
    @9
    @85
    @90
    @13
    vi
    cM
    @9
    vi
    nfv
    @14
    @15
    wph
    @49
    @85
    wcel
    #
    @90
    @13
    wcel
    #
    @8
    wph
    @115
    @66
    @116
    @115
    @66
    wph
    @115
    @49
    @67
    cZ
    @49
    cN
    @2
    elfzuz
    @68
    syl6eleq
    adantl
    #
    @9
    @44
    @13
    wcel
    #
    wi
    @81
    @116
    wi
    vn
    vi
    @78
    @9
    @81
    @118
    @116
    @89
    @78
    @44
    @90
    @13
    @2
    @49
    cF
    fveq2
    #
    eleq1d
    imbi12d
    @70
    chvarv
    syldan
    adantlr
    @85
    com
    cdom
    wbr
    @9
    @2
    cN
    fzct
    a1i
    wph
    vi
    @85
    @90
    wdisj
    #
    @8
    wph
    @85
    cZ
    wss
    vi
    cZ
    @90
    wdisj
    #
    @120
    wph
    vi
    @85
    cZ
    @117
    ssd
    wph
    @109
    @121
    wph
    @107
    @108
    wa
    @109
    @110
    simprd
    #
    vn
    vi
    cZ
    @44
    @90
    @119
    cbvdisjv
    sylib
    vi
    @85
    cZ
    @90
    disjss1
    sylc
    adantr
    meadjiun
    @9
    @93
    @85
    @92
    vi
    csu
    #
    @86
    @9
    @85
    @92
    vi
    @9
    cN
    @2
    fzfid
    wph
    @115
    @92
    @6
    wcel
    #
    @8
    wph
    @115
    @66
    @124
    @117
    @9
    @45
    @6
    wcel
    #
    wi
    @81
    @124
    wi
    vn
    vi
    @78
    @9
    @81
    @125
    @124
    @89
    @78
    @45
    @92
    @6
    @78
    @44
    @90
    cM
    @119
    fveq2d
    eleq1d
    imbi12d
    @72
    chvarv
    syldan
    adantlr
    sge0fsummpt
    @123
    @86
    wceq
    @9
    @85
    @92
    @83
    vi
    vm
    @49
    @37
    wceq
    @90
    @82
    cM
    @49
    @37
    cF
    fveq2
    fveq2d
    cbvsumv
    a1i
    eqtrd
    3eqtrd
    chvarv
    @84
    @51
    wceq
    @81
    @50
    @83
    @45
    vm
    vn
    @102
    @82
    @44
    cM
    @37
    @2
    cF
    fveq2
    fveq2d
    cbvsumv
    a1i
    eqtrd
    #
    breq1d
    ralbidva
    biimpd
    imp
    syldan
    ex
    reximdv
    mpd
    sge0reuzb
    wph
    cr
    @0
    @53
    clt
    wph
    cS
    @52
    wph
    cS
    vi
    cZ
    @75
    cmpt
    #
    @52
    cS
    @127
    wceq
    wph
    cS
    @35
    @127
    meaiuninclem.s
    vn
    vi
    cZ
    @7
    @75
    @80
    cbvmptv
    eqtri
    a1i
    wph
    vi
    cZ
    @75
    @51
    @126
    mpteq2dva
    eqtrd
    rneqd
    supeq1d
    eqtr4d
    eqcomd
    wph
    @48
    @46
    wph
    cZ
    @44
    @13
    vn
    cM
    @54
    meaiuninclem.m
    @15
    @70
    cZ
    com
    cdom
    wbr
    wph
    cN
    cZ
    meaiuninclem.z
    uzct
    a1i
    @122
    meadjiun
    eqcomd
    wph
    @47
    @4
    cM
    wph
    @107
    @108
    @109
    @110
    simplrd
    fveq2d
    3eqtrd
    breqtrd
end
