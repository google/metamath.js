include "caddc.mm"
include "cof.mm"
include "cseq.mm"
include "culm.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "cz.mm"
include "cli.mm"
include "climcau.mm"
include "syl2anc.mm"
include "wa.mm"
include "wi.mm"
include "cle.mm"
include "c1.mm"
include "cfz.mm"
include "csu.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "wfn.mm"
include "seqfn.mm"
include "syl.mm"
include "fneq2i.mm"
include "sylibr.mm"
include "cmpt.mm"
include "cvv.mm"
include "elex.mm"
include "adantr.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "elmapi.mm"
include "feqmptd.mm"
include "wceq.mm"
include "adantl.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "mpteq2dv.mm"
include "eqtr4d.mm"
include "seqof.mm"
include "ffvelrnda.mm"
include "an32s.mm"
include "fmptd.mm"
include "serf.mm"
include "wb.mm"
include "cnex.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "ad2antrr.mm"
include "uztrn2.mm"
include "ffvelrnd.mm"
include "simprl.mm"
include "subcld.mm"
include "abscld.mm"
include "fzfid.mm"
include "cun.mm"
include "ssun2.mm"
include "simprr.mm"
include "elfzuzb.mm"
include "fzsplit.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "fsumrecl.mm"
include "cr.mm"
include "serfre.mm"
include "resubcld.mm"
include "recnd.mm"
include "sylan2.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "sylan9eq.mm"
include "eqeq12d.mm"
include "rspccv.mm"
include "sylc.mm"
include "oveq12d.mm"
include "fsumser.mm"
include "cin.mm"
include "c0.mm"
include "eluzelre.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "fsumsplit.mm"
include "eqcomd.mm"
include "fsumcl.mm"
include "subaddd.mm"
include "3eqtr2d.mm"
include "fveq2d.mm"
include "fsumabs.mm"
include "eqbrtrd.mm"
include "simpll.mm"
include "anass1rs.mm"
include "fsumle.mm"
include "eqidd.mm"
include "eqtr3d.mm"
include "eqeltrrd.mm"
include "cc0.mm"
include "0red.mm"
include "absge0d.mm"
include "letrd.mm"
include "fsumge0.mm"
include "absidd.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "simpllr.mm"
include "rpred.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "ralrimdva.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "ulmcau.mm"

theorem mtest
  let wph: wff ph
  let vz: setvar z
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vm: setvar m
  let vy: setvar y
  let cT: class T
  assume mtest.z: |- Z = ( ZZ>= ` N )
  assume mtest.n: |- ( ph -> N e. ZZ )
  assume mtest.s: |- ( ph -> S e. V )
  assume mtest.f: |- ( ph -> F : Z --> ( CC ^m S ) )
  assume mtest.m: |- ( ph -> M e. W )
  assume mtest.c: |- ( ( ph /\ k e. Z ) -> ( M ` k ) e. RR )
  assume mtest.l: |- ( ( ph /\ ( k e. Z /\ z e. S ) ) -> ( abs ` ( ( F ` k ) ` z ) ) <_ ( M ` k ) )
  assume mtest.d: |- ( ph -> seq N ( + , M ) e. dom ~~> )

  disjoint k z
  disjoint F k
  disjoint F z
  disjoint M k
  disjoint M z
  disjoint N k
  disjoint N z
  disjoint k ph
  disjoint ph z
  disjoint Z k
  disjoint Z z
  disjoint S k
  disjoint S z
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i x
  disjoint i z
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint F n
  disjoint r x
  disjoint r z
  disjoint F r
  disjoint x z
  disjoint F x
  disjoint i m
  disjoint i y
  disjoint M i
  disjoint j m
  disjoint j y
  disjoint M j
  disjoint k m
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint n y
  disjoint M n
  disjoint r y
  disjoint M r
  disjoint x y
  disjoint M x
  disjoint y z
  disjoint M y
  disjoint N i
  disjoint N j
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint N x
  disjoint N y
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint Z i
  disjoint Z j
  disjoint Z m
  disjoint Z n
  disjoint Z r
  disjoint Z x
  disjoint Z y
  disjoint S i
  disjoint S j
  disjoint S n
  disjoint S r
  disjoint S x
  disjoint S y
  assert |- ( ph -> seq N ( oF + , F ) e. dom ( ~~>u ` S ) )

  proof
    wph
    caddc
    cof
    #
    cF
    cN
    cseq
    #
    cS
    culm
    cfv
    cdm
    wcel
    vz
    cv
    #
    vi
    cv
    #
    @1
    cfv
    #
    cfv
    #
    @2
    vj
    cv
    #
    @1
    cfv
    #
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vr
    cv
    #
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vi
    @6
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vr
    crp
    wral
    #
    wph
    @3
    caddc
    cM
    cN
    cseq
    #
    cfv
    #
    @6
    @18
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    vi
    @14
    wral
    #
    vj
    cZ
    wrex
    #
    vr
    crp
    wral
    #
    @17
    wph
    cN
    cz
    wcel
    #
    @18
    cli
    cdm
    wcel
    @26
    mtest.n
    mtest.d
    vr
    vj
    vi
    @18
    cN
    cZ
    mtest.z
    climcau
    syl2anc
    wph
    @25
    @16
    vr
    crp
    wph
    @11
    crp
    wcel
    #
    wa
    #
    @24
    @15
    vj
    cZ
    @29
    @6
    cZ
    wcel
    #
    wa
    @23
    @13
    vi
    @14
    @29
    @30
    @3
    @14
    wcel
    #
    @23
    @13
    wi
    @29
    @30
    @31
    wa
    #
    wa
    #
    @23
    @12
    vz
    cS
    @33
    @2
    cS
    wcel
    #
    wa
    #
    @10
    @22
    cle
    wbr
    #
    @23
    @12
    @35
    @10
    @6
    c1
    caddc
    co
    #
    @3
    cfz
    co
    #
    @2
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cabs
    cfv
    #
    vk
    csu
    #
    @22
    @35
    @9
    @35
    @5
    @8
    @33
    cS
    cc
    @2
    @4
    @33
    @4
    cc
    cS
    cmap
    co
    #
    wcel
    #
    cS
    cc
    @4
    wf
    @33
    cZ
    @44
    @3
    @1
    wph
    cZ
    @44
    @1
    wf
    #
    @28
    @32
    wph
    @1
    cZ
    wfn
    #
    @45
    vi
    cZ
    wral
    @46
    wph
    @1
    cN
    cuz
    cfv
    #
    wfn
    #
    @47
    wph
    @27
    @49
    mtest.n
    @0
    cF
    cN
    seqfn
    syl
    cZ
    @48
    @1
    mtest.z
    fneq2i
    sylibr
    wph
    @45
    vi
    cZ
    wph
    @3
    cZ
    wcel
    #
    wa
    #
    @4
    vz
    cS
    @3
    caddc
    vn
    cZ
    @2
    vn
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    cN
    cseq
    #
    cfv
    #
    cmpt
    #
    @44
    @51
    vk
    vz
    cS
    caddc
    cF
    @55
    cN
    @3
    cvv
    wph
    cS
    cvv
    wcel
    #
    @50
    wph
    cS
    cV
    wcel
    @59
    mtest.s
    cS
    cV
    elex
    syl
    adantr
    #
    @51
    @3
    cZ
    @48
    wph
    @50
    simpr
    mtest.z
    syl6eleq
    @51
    @39
    cN
    @3
    cfz
    co
    #
    wcel
    #
    wa
    #
    @40
    vz
    cS
    @41
    cmpt
    vz
    cS
    @39
    @55
    cfv
    #
    cmpt
    @63
    vz
    cS
    cc
    @40
    @63
    @40
    @44
    wcel
    #
    cS
    cc
    @40
    wf
    #
    @51
    cZ
    @44
    cF
    wf
    #
    @39
    cZ
    wcel
    #
    @65
    @62
    wph
    @67
    @50
    mtest.f
    adantr
    @62
    @39
    @48
    cZ
    @39
    cN
    @3
    elfzuz
    mtest.z
    syl6eleqr
    #
    cZ
    @44
    @39
    cF
    ffvelrn
    #
    syl2an
    @40
    cc
    cS
    elmapi
    #
    syl
    feqmptd
    @63
    vz
    cS
    @64
    @41
    @63
    @68
    @64
    @41
    wceq
    #
    @62
    @68
    @51
    @69
    adantl
    vn
    @39
    @54
    @41
    cZ
    @55
    vn
    vk
    weq
    @2
    @53
    @40
    @52
    @39
    cF
    fveq2
    fveq1d
    @55
    eqid
    #
    @2
    @40
    fvex
    fvmpt
    #
    syl
    mpteq2dv
    eqtr4d
    seqof
    #
    @51
    @58
    @44
    wcel
    #
    cS
    cc
    @58
    wf
    #
    @51
    vz
    cS
    @57
    cc
    @58
    wph
    @34
    @50
    @57
    cc
    wcel
    wph
    @34
    wa
    #
    cZ
    cc
    @3
    @56
    @78
    vi
    @55
    cN
    cZ
    mtest.z
    wph
    @27
    @34
    mtest.n
    adantr
    @78
    cZ
    cc
    @3
    @55
    @78
    vn
    cZ
    @54
    cc
    @55
    wph
    @52
    cZ
    wcel
    #
    @34
    @54
    cc
    wcel
    wph
    @79
    wa
    #
    cS
    cc
    @2
    @53
    @80
    @53
    @44
    wcel
    cS
    cc
    @53
    wf
    wph
    cZ
    @44
    @52
    cF
    mtest.f
    ffvelrnda
    @53
    cc
    cS
    elmapi
    syl
    ffvelrnda
    an32s
    @73
    fmptd
    ffvelrnda
    serf
    ffvelrnda
    an32s
    @58
    eqid
    #
    fmptd
    @51
    cc
    cvv
    wcel
    @59
    @76
    @77
    wb
    cnex
    @60
    cc
    cS
    @58
    cvv
    cvv
    elmapg
    sylancr
    mpbird
    eqeltrd
    ralrimiva
    vi
    cZ
    @44
    @1
    ffnfv
    sylanbrc
    #
    ad2antrr
    #
    @32
    @50
    @29
    cN
    @3
    @6
    cZ
    mtest.z
    uztrn2
    #
    adantl
    #
    ffvelrnd
    @4
    cc
    cS
    elmapi
    syl
    ffvelrnda
    @33
    cS
    cc
    @2
    @7
    @33
    @7
    @44
    wcel
    cS
    cc
    @7
    wf
    @33
    cZ
    @44
    @6
    @1
    @83
    @29
    @30
    @31
    simprl
    #
    ffvelrnd
    @7
    cc
    cS
    elmapi
    syl
    ffvelrnda
    subcld
    abscld
    #
    @35
    @38
    @42
    vk
    @35
    @37
    @3
    fzfid
    #
    @35
    @39
    @38
    wcel
    #
    wa
    #
    @41
    @35
    @89
    @62
    @41
    cc
    wcel
    #
    @33
    @89
    @62
    @34
    @33
    @38
    @61
    @39
    @33
    cN
    @6
    cfz
    co
    #
    @38
    cun
    #
    @38
    @61
    @38
    @92
    ssun2
    @33
    @6
    @61
    wcel
    #
    @61
    @93
    wceq
    #
    @33
    @6
    @48
    wcel
    #
    @31
    @94
    @33
    @6
    cZ
    @48
    @86
    mtest.z
    syl6eleq
    #
    @29
    @30
    @31
    simprr
    @6
    cN
    @3
    elfzuzb
    sylanbrc
    @6
    cN
    @3
    fzsplit
    syl
    #
    syl5sseqr
    sselda
    #
    adantlr
    #
    @33
    @62
    @34
    @91
    @33
    @62
    wa
    #
    cS
    cc
    @2
    @40
    @101
    @65
    @66
    @33
    @67
    @68
    @65
    @62
    wph
    @67
    @28
    @32
    mtest.f
    ad2antrr
    #
    @69
    @70
    syl2an
    @71
    syl
    ffvelrnda
    an32s
    #
    syldan
    #
    abscld
    #
    fsumrecl
    @33
    @22
    cr
    wcel
    #
    @34
    @33
    @21
    @33
    @21
    @33
    @19
    @20
    @33
    cZ
    cr
    @3
    @18
    wph
    cZ
    cr
    @18
    wf
    @28
    @32
    wph
    vk
    cM
    cN
    cZ
    mtest.z
    mtest.n
    mtest.c
    serfre
    ad2antrr
    #
    @85
    ffvelrnd
    @33
    cZ
    cr
    @6
    @18
    @107
    @86
    ffvelrnd
    resubcld
    #
    recnd
    abscld
    adantr
    #
    @35
    @10
    @38
    @41
    vk
    csu
    #
    cabs
    cfv
    @43
    cle
    @35
    @9
    @110
    cabs
    @35
    @9
    @57
    @6
    @56
    cfv
    #
    cmin
    co
    @61
    @41
    vk
    csu
    #
    @92
    @41
    vk
    csu
    #
    cmin
    co
    #
    @110
    @35
    @5
    @57
    @8
    @111
    cmin
    @33
    @34
    @5
    @2
    @58
    cfv
    #
    @57
    @33
    @2
    @4
    @58
    wph
    @32
    @4
    @58
    wceq
    #
    @28
    @32
    wph
    @50
    @116
    @84
    @75
    sylan2
    adantlr
    fveq1d
    @34
    @57
    cvv
    wcel
    @115
    @57
    wceq
    @3
    @56
    fvex
    vz
    cS
    @57
    cvv
    @58
    @81
    fvmpt2
    mpan2
    sylan9eq
    @33
    @34
    @8
    @2
    vz
    cS
    @111
    cmpt
    #
    cfv
    #
    @111
    @33
    @2
    @7
    @117
    @33
    @116
    vi
    cZ
    wral
    #
    @30
    @7
    @117
    wceq
    #
    wph
    @119
    @28
    @32
    wph
    @116
    vi
    cZ
    @75
    ralrimiva
    ad2antrr
    @86
    @116
    @120
    vi
    @6
    cZ
    vi
    vj
    weq
    #
    @4
    @7
    @58
    @117
    @3
    @6
    @1
    fveq2
    @121
    vz
    cS
    @57
    @111
    @3
    @6
    @56
    fveq2
    mpteq2dv
    eqeq12d
    rspccv
    sylc
    fveq1d
    @34
    @111
    cvv
    wcel
    @118
    @111
    wceq
    @6
    @56
    fvex
    vz
    cS
    @111
    cvv
    @117
    @117
    eqid
    fvmpt2
    mpan2
    sylan9eq
    oveq12d
    @35
    @112
    @57
    @113
    @111
    cmin
    @35
    @41
    vk
    @55
    cN
    @3
    @35
    @62
    wa
    @68
    @72
    @62
    @68
    @35
    @69
    adantl
    @74
    syl
    @35
    @3
    cZ
    @48
    @33
    @50
    @34
    @85
    adantr
    mtest.z
    syl6eleq
    @103
    fsumser
    @35
    @41
    vk
    @55
    cN
    @6
    @35
    @39
    @92
    wcel
    #
    wa
    @68
    @72
    @122
    @68
    @35
    @122
    @39
    @48
    cZ
    @39
    cN
    @6
    elfzuz
    mtest.z
    syl6eleqr
    #
    adantl
    @74
    syl
    @35
    @6
    cZ
    @48
    @33
    @30
    @34
    @86
    adantr
    mtest.z
    syl6eleq
    @33
    @122
    @34
    @91
    @33
    @122
    wa
    #
    cS
    cc
    @2
    @40
    @124
    @65
    @66
    @33
    @67
    @68
    @65
    @122
    @102
    @123
    @70
    syl2an
    @71
    syl
    ffvelrnda
    an32s
    #
    fsumser
    oveq12d
    @35
    @114
    @110
    wceq
    @113
    @110
    caddc
    co
    #
    @112
    wceq
    @35
    @112
    @126
    @35
    @92
    @38
    @41
    @61
    vk
    @33
    @92
    @38
    cin
    c0
    wceq
    #
    @34
    @33
    @6
    @37
    clt
    wbr
    @127
    @33
    @6
    @33
    @96
    @6
    cr
    wcel
    @97
    cN
    @6
    eluzelre
    syl
    ltp1d
    cN
    @6
    @37
    @3
    fzdisj
    syl
    #
    adantr
    @33
    @95
    @34
    @98
    adantr
    @35
    cN
    @3
    fzfid
    #
    @103
    fsumsplit
    eqcomd
    @35
    @112
    @113
    @110
    @35
    @61
    @41
    vk
    @129
    @103
    fsumcl
    @35
    @92
    @41
    vk
    @35
    cN
    @6
    fzfid
    @125
    fsumcl
    @35
    @38
    @41
    vk
    @88
    @104
    fsumcl
    subaddd
    mpbird
    3eqtr2d
    fveq2d
    @35
    @38
    @41
    vk
    @88
    @104
    fsumabs
    eqbrtrd
    @35
    @43
    @38
    @39
    cM
    cfv
    #
    vk
    csu
    #
    @22
    cle
    @35
    @38
    @42
    @130
    vk
    @88
    @105
    @33
    @89
    @130
    cr
    wcel
    #
    @34
    @33
    @89
    @62
    @132
    @99
    @33
    wph
    @68
    @132
    @62
    wph
    @28
    @32
    simpll
    #
    @69
    mtest.c
    syl2an
    #
    syldan
    adantlr
    #
    @35
    @89
    @68
    @42
    @130
    cle
    wbr
    #
    @90
    @62
    @68
    @100
    @69
    syl
    @33
    @68
    @34
    @136
    @29
    @68
    @34
    wa
    #
    @136
    @32
    wph
    @137
    @136
    @28
    mtest.l
    adantlr
    adantlr
    anass1rs
    syldan
    #
    fsumle
    @35
    @22
    @131
    cabs
    cfv
    #
    @131
    @33
    @22
    @139
    wceq
    @34
    @33
    @21
    @131
    cabs
    @33
    @61
    @130
    vk
    csu
    #
    @92
    @130
    vk
    csu
    #
    cmin
    co
    #
    @21
    @131
    @33
    @140
    @19
    @141
    @20
    cmin
    @33
    @130
    vk
    cM
    cN
    @3
    @101
    @130
    eqidd
    @33
    @3
    cZ
    @48
    @85
    mtest.z
    syl6eleq
    @101
    @130
    @134
    recnd
    #
    fsumser
    @33
    @130
    vk
    cM
    cN
    @6
    @124
    @130
    eqidd
    @97
    @124
    @130
    @33
    wph
    @68
    @132
    @122
    @133
    @123
    mtest.c
    syl2an
    recnd
    #
    fsumser
    oveq12d
    @33
    @142
    @131
    wceq
    @141
    @131
    caddc
    co
    #
    @140
    wceq
    @33
    @140
    @145
    @33
    @92
    @38
    @130
    @61
    vk
    @128
    @98
    @33
    cN
    @3
    fzfid
    #
    @143
    fsumsplit
    eqcomd
    @33
    @140
    @141
    @131
    @33
    @61
    @130
    vk
    @146
    @143
    fsumcl
    @33
    @92
    @130
    vk
    @33
    cN
    @6
    fzfid
    @144
    fsumcl
    @33
    @38
    @130
    vk
    @33
    @37
    @3
    fzfid
    @33
    @89
    @62
    @130
    cc
    wcel
    @99
    @143
    syldan
    fsumcl
    subaddd
    mpbird
    eqtr3d
    #
    fveq2d
    adantr
    @35
    @131
    @33
    @131
    cr
    wcel
    @34
    @33
    @21
    @131
    cr
    @147
    @108
    eqeltrrd
    adantr
    @35
    @38
    @130
    vk
    @88
    @135
    @90
    cc0
    @42
    @130
    @90
    0red
    @105
    @135
    @90
    @41
    @104
    absge0d
    @138
    letrd
    fsumge0
    absidd
    eqtrd
    breqtrrd
    letrd
    @35
    @10
    cr
    wcel
    @106
    @11
    cr
    wcel
    @36
    @23
    wa
    @12
    wi
    @87
    @109
    @35
    @11
    wph
    @28
    @32
    @34
    simpllr
    rpred
    @10
    @22
    @11
    lelttr
    syl3anc
    mpand
    ralrimdva
    anassrs
    ralimdva
    reximdva
    ralimdva
    mpd
    wph
    vr
    vz
    cS
    vj
    vi
    @1
    cN
    cV
    cZ
    mtest.z
    mtest.n
    mtest.s
    @82
    ulmcau
    mpbird
end
