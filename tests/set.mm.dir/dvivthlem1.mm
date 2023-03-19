include "cv.mm"
include "cicc.mm"
include "co.mm"
include "cres.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "cdv.mm"
include "wceq.mm"
include "cioo.mm"
include "ioossre.mm"
include "sseldi.mm"
include "ltled.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cmul.mm"
include "cmin.mm"
include "wa.mm"
include "cncff.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "wss.mm"
include "cdm.mm"
include "dvfre.mm"
include "sylancl.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "adantr.mm"
include "a1i.mm"
include "sselda.mm"
include "remulcld.mm"
include "resubcld.mm"
include "fmptd.mm"
include "iccssioo2.mm"
include "fssresd.mm"
include "cc.mm"
include "wb.mm"
include "ax-resscn.mm"
include "fss.mm"
include "cmpt.mm"
include "oveq2i.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "recnd.mm"
include "feq2d.mm"
include "mpbid.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "remulcl.mm"
include "sylan.mm"
include "c1.mm"
include "1cnd.mm"
include "dvmptid.mm"
include "dvmptcmul.mm"
include "mulid1d.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "eqid.mm"
include "tgioo2.mm"
include "iooretop.mm"
include "dvmptres.mm"
include "dvmptsub.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "cvv.mm"
include "dmmptg.mm"
include "ovex.mm"
include "mprg.mm"
include "syl6eq.mm"
include "dvcn.mm"
include "syl31anc.mm"
include "rescncf.mm"
include "sylc.mm"
include "cncffvrn.mm"
include "sylancr.mm"
include "mpbird.mm"
include "evthicc.mm"
include "simpld.mm"
include "fvres.mm"
include "breqan12rd.mm"
include "ralbidva.mm"
include "adantl.mm"
include "wi.mm"
include "ioossicc.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "syldan.mm"
include "ad2antrr.mm"
include "cc0.mm"
include "fveq1d.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fvmpt.mm"
include "simprl.mm"
include "syl5ss.mm"
include "simprr.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "dvferm.mm"
include "subeq0d.mm"
include "exp32.mm"
include "wo.mm"
include "vex.mm"
include "elpr.mm"
include "clt.mm"
include "eliooord.mm"
include "cxr.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "ndmioo.mm"
include "necon1ai.mm"
include "3syl.mm"
include "rexrd.mm"
include "elioo2.mm"
include "mpbir3and.mm"
include "eqeltrd.mm"
include "simprd.mm"
include "xrltle.mm"
include "mpd.mm"
include "iooss2.mm"
include "raleqdv.mm"
include "dvferm1.mm"
include "eqbrtrrd.mm"
include "suble0d.mm"
include "elicc2.mm"
include "simp3d.mm"
include "fveq2d.mm"
include "breqtrrd.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "simp2d.mm"
include "eqbrtrd.mm"
include "iooss1.mm"
include "dvferm2.mm"
include "breqtrd.mm"
include "subge0d.mm"
include "jaod.mm"
include "syl5bi.mm"
include "cun.mm"
include "elun.mm"
include "prunioo.mm"
include "syl3anc.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "biimpar.mm"
include "mpjaod.mm"
include "syld.mm"
include "reximdva.mm"

theorem dvivthlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vw: setvar w
  let vz: setvar z
  assume dvivth.1: |- ( ph -> M e. ( A (,) B ) )
  assume dvivth.2: |- ( ph -> N e. ( A (,) B ) )
  assume dvivth.3: |- ( ph -> F e. ( ( A (,) B ) -cn-> RR ) )
  assume dvivth.4: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume dvivth.5: |- ( ph -> M < N )
  assume dvivth.6: |- ( ph -> C e. ( ( ( RR _D F ) ` N ) [,] ( ( RR _D F ) ` M ) ) )
  assume dvivth.7: |- G = ( y e. ( A (,) B ) |-> ( ( F ` y ) - ( C x. y ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint M x
  disjoint M y
  disjoint C x
  disjoint C y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint B w
  disjoint F w
  disjoint w z
  disjoint G w
  disjoint x z
  disjoint G z
  disjoint M w
  disjoint y z
  disjoint M z
  disjoint N w
  disjoint N z
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> E. x e. ( M [,] N ) ( ( RR _D F ) ` x ) = C )

  proof
    wph
    vz
    cv
    #
    cG
    cM
    cN
    cicc
    co
    #
    cres
    #
    cfv
    #
    vx
    cv
    #
    @2
    cfv
    #
    cle
    wbr
    #
    vz
    @1
    wral
    #
    vx
    @1
    wrex
    #
    @4
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cC
    wceq
    #
    vx
    @1
    wrex
    wph
    @8
    @5
    @3
    cle
    wbr
    vz
    @1
    wral
    vx
    @1
    wrex
    wph
    vx
    vz
    vx
    vz
    cM
    cN
    @2
    wph
    cA
    cB
    cioo
    co
    #
    cr
    cM
    cA
    cB
    ioossre
    #
    dvivth.1
    sseldi
    #
    wph
    @12
    cr
    cN
    @13
    dvivth.2
    sseldi
    #
    wph
    cM
    cN
    @14
    @15
    dvivth.5
    ltled
    #
    wph
    @2
    @1
    cr
    ccncf
    co
    wcel
    #
    @1
    cr
    @2
    wf
    #
    wph
    @12
    cr
    @1
    cG
    wph
    vy
    @12
    vy
    cv
    #
    cF
    cfv
    #
    cC
    @19
    cmul
    co
    #
    cmin
    co
    #
    cr
    cG
    wph
    @19
    @12
    wcel
    #
    wa
    #
    @20
    @21
    wph
    @12
    cr
    @19
    cF
    wph
    cF
    @12
    cr
    ccncf
    co
    wcel
    @12
    cr
    cF
    wf
    #
    dvivth.3
    @12
    cr
    cF
    cncff
    syl
    #
    ffvelrnda
    #
    @24
    cC
    @19
    wph
    cC
    cr
    wcel
    #
    @23
    wph
    cN
    @9
    cfv
    #
    cM
    @9
    cfv
    #
    cicc
    co
    #
    cr
    cC
    wph
    @29
    cr
    wcel
    #
    @30
    cr
    wcel
    #
    @31
    cr
    wss
    wph
    @9
    cdm
    #
    cr
    cN
    @9
    wph
    @25
    @12
    cr
    wss
    #
    @34
    cr
    @9
    wf
    #
    @26
    @13
    @12
    cF
    dvfre
    sylancl
    #
    wph
    cN
    @12
    @34
    dvivth.2
    dvivth.4
    eleqtrrd
    ffvelrnd
    #
    wph
    @34
    cr
    cM
    @9
    @37
    wph
    cM
    @12
    @34
    dvivth.1
    dvivth.4
    eleqtrrd
    ffvelrnd
    #
    @29
    @30
    iccssre
    syl2anc
    dvivth.6
    sseldd
    #
    adantr
    #
    wph
    @12
    cr
    @19
    @35
    wph
    @13
    a1i
    #
    sselda
    remulcld
    #
    resubcld
    dvivth.7
    fmptd
    #
    wph
    cM
    @12
    wcel
    #
    cN
    @12
    wcel
    #
    @1
    @12
    wss
    #
    dvivth.1
    dvivth.2
    cA
    cB
    cM
    cN
    iccssioo2
    syl2anc
    #
    fssresd
    wph
    cr
    cc
    wss
    #
    @2
    @1
    cc
    ccncf
    co
    wcel
    #
    @17
    @18
    wb
    ax-resscn
    wph
    @47
    cG
    @12
    cc
    ccncf
    co
    wcel
    #
    @50
    @48
    wph
    @49
    @12
    cc
    cG
    wf
    #
    @35
    cr
    cG
    cdv
    co
    #
    cdm
    #
    @12
    wceq
    #
    @51
    @49
    wph
    ax-resscn
    a1i
    #
    wph
    @12
    cr
    cG
    wf
    #
    @49
    @52
    @44
    ax-resscn
    @12
    cr
    cc
    cG
    fss
    sylancl
    @42
    wph
    @54
    vy
    @12
    @19
    @9
    cfv
    #
    cC
    cmin
    co
    #
    cmpt
    #
    cdm
    #
    @12
    wph
    @53
    @60
    wph
    @53
    cr
    vy
    @12
    @22
    cmpt
    #
    cdv
    co
    @60
    cG
    @62
    cr
    cdv
    dvivth.7
    oveq2i
    wph
    vy
    @20
    @58
    @21
    cC
    cr
    cr
    cr
    @12
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    @24
    @20
    @27
    recnd
    wph
    @12
    cr
    @19
    @9
    wph
    @36
    @12
    cr
    @9
    wf
    @37
    wph
    @34
    @12
    cr
    @9
    dvivth.4
    feq2d
    mpbid
    #
    ffvelrnda
    wph
    @9
    cr
    vy
    @12
    @20
    cmpt
    #
    cdv
    co
    vy
    @12
    @58
    cmpt
    wph
    cF
    @65
    cr
    cdv
    wph
    vy
    @12
    cr
    cF
    @26
    feqmptd
    oveq2d
    wph
    vy
    @12
    cr
    @9
    @64
    feqmptd
    eqtr3d
    @24
    @21
    @43
    recnd
    @41
    wph
    vy
    @21
    cC
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    cr
    cr
    @12
    @63
    wph
    @19
    cr
    wcel
    #
    wa
    #
    @21
    wph
    @28
    @68
    @21
    cr
    wcel
    @40
    cC
    @19
    remulcl
    sylan
    recnd
    wph
    @28
    @68
    @40
    adantr
    wph
    cr
    vy
    cr
    @21
    cmpt
    cdv
    co
    vy
    cr
    cC
    c1
    cmul
    co
    #
    cmpt
    vy
    cr
    cC
    cmpt
    wph
    vy
    @19
    c1
    cC
    cr
    cc
    cr
    @63
    wph
    cr
    cc
    @19
    @56
    sselda
    @69
    1cnd
    wph
    vy
    cr
    @63
    dvmptid
    wph
    cC
    @40
    recnd
    #
    dvmptcmul
    wph
    vy
    cr
    @70
    cC
    wph
    cC
    @71
    mulid1d
    mpteq2dv
    eqtrd
    @42
    @67
    @67
    eqid
    #
    tgioo2
    @72
    @12
    @66
    wcel
    wph
    cA
    cB
    iooretop
    a1i
    dvmptres
    dvmptsub
    syl5eq
    #
    dmeqd
    @59
    cvv
    wcel
    #
    @61
    @12
    wceq
    vy
    @12
    vy
    @12
    @59
    cvv
    dmmptg
    @74
    @23
    @58
    cC
    cmin
    ovex
    a1i
    mprg
    syl6eq
    #
    @12
    cr
    cG
    dvcn
    syl31anc
    @12
    cc
    @1
    cG
    rescncf
    sylc
    @1
    cc
    cr
    @2
    cncffvrn
    sylancr
    mpbird
    evthicc
    simpld
    wph
    @7
    @11
    vx
    @1
    wph
    @4
    @1
    wcel
    #
    wa
    #
    @7
    @0
    cG
    cfv
    #
    @4
    cG
    cfv
    #
    cle
    wbr
    #
    vz
    cM
    cN
    cioo
    co
    #
    wral
    #
    @11
    @77
    @7
    @80
    vz
    @1
    wral
    #
    @82
    @76
    @7
    @83
    wb
    wph
    @76
    @6
    @80
    vz
    @1
    @0
    @1
    wcel
    @76
    @3
    @78
    @5
    @79
    cle
    @0
    @1
    cG
    fvres
    @4
    @1
    cG
    fvres
    breqan12rd
    ralbidva
    adantl
    @81
    @1
    wss
    @83
    @82
    wi
    cM
    cN
    ioossicc
    #
    @80
    vz
    @81
    @1
    ssralv
    ax-mp
    syl6bi
    @77
    @4
    @81
    wcel
    #
    @82
    @11
    wi
    #
    @4
    cM
    cN
    cpr
    #
    wcel
    #
    @77
    @85
    @82
    @11
    @77
    @85
    @82
    wa
    #
    wa
    #
    @10
    cC
    @77
    @10
    cc
    wcel
    @89
    @77
    @10
    wph
    @76
    @4
    @12
    wcel
    #
    @10
    cr
    wcel
    #
    wph
    @1
    @12
    @4
    @48
    sselda
    #
    wph
    @12
    cr
    @4
    @9
    @64
    ffvelrnda
    syldan
    #
    recnd
    adantr
    wph
    cC
    cc
    wcel
    @76
    @89
    @71
    ad2antrr
    @90
    @4
    @53
    cfv
    #
    @10
    cC
    cmin
    co
    #
    cc0
    @77
    @95
    @96
    wceq
    #
    @89
    @77
    @95
    @4
    @60
    cfv
    #
    @96
    wph
    @95
    @98
    wceq
    @76
    wph
    @4
    @53
    @60
    @73
    fveq1d
    adantr
    @77
    @91
    @98
    @96
    wceq
    @93
    vy
    @4
    @59
    @96
    @12
    @60
    vy
    vx
    weq
    @58
    @10
    cC
    cmin
    @19
    @4
    @9
    fveq2
    oveq1d
    @60
    eqid
    @10
    cC
    cmin
    ovex
    fvmpt
    syl
    eqtrd
    #
    adantr
    @90
    vw
    cM
    cN
    @4
    cG
    @12
    wph
    @57
    @76
    @89
    @44
    ad2antrr
    @35
    @90
    @13
    a1i
    @77
    @85
    @82
    simprl
    wph
    @81
    @12
    wss
    @76
    @89
    wph
    @81
    @1
    @12
    @84
    @48
    syl5ss
    ad2antrr
    @90
    @4
    @12
    @54
    @77
    @91
    @89
    @93
    adantr
    wph
    @55
    @76
    @89
    @75
    ad2antrr
    eleqtrrd
    @90
    @82
    vw
    cv
    #
    cG
    cfv
    #
    @79
    cle
    wbr
    #
    vw
    @81
    wral
    #
    @77
    @85
    @82
    simprr
    @80
    @102
    vz
    vw
    @81
    vz
    vw
    weq
    @78
    @101
    @79
    cle
    @0
    @100
    cG
    fveq2
    breq1d
    cbvralv
    #
    sylib
    dvferm
    eqtr3d
    subeq0d
    exp32
    @88
    @4
    cM
    wceq
    #
    @4
    cN
    wceq
    #
    wo
    @77
    @86
    @4
    cM
    cN
    vx
    vex
    elpr
    @77
    @105
    @86
    @106
    @77
    @105
    @82
    @11
    @77
    @105
    @82
    wa
    #
    wa
    #
    @11
    @10
    cC
    cle
    wbr
    #
    cC
    @10
    cle
    wbr
    #
    @108
    @96
    cc0
    cle
    wbr
    @109
    @108
    @95
    @96
    cc0
    cle
    @77
    @97
    @107
    @99
    adantr
    @108
    vw
    cA
    cN
    @4
    cG
    @12
    wph
    @57
    @76
    @107
    @44
    ad2antrr
    @35
    @108
    @13
    a1i
    @108
    @4
    cM
    cA
    cN
    cioo
    co
    #
    @77
    @105
    @82
    simprl
    #
    wph
    cM
    @111
    wcel
    #
    @76
    @107
    wph
    @113
    cM
    cr
    wcel
    #
    cA
    cM
    clt
    wbr
    #
    cM
    cN
    clt
    wbr
    #
    @14
    wph
    @115
    cM
    cB
    clt
    wbr
    #
    wph
    @45
    @115
    @117
    wa
    dvivth.1
    cM
    cA
    cB
    eliooord
    syl
    simpld
    #
    dvivth.5
    wph
    cA
    cxr
    wcel
    #
    cN
    cxr
    wcel
    #
    @113
    @114
    @115
    @116
    w3a
    wb
    wph
    @119
    cB
    cxr
    wcel
    #
    wph
    @45
    @12
    c0
    wne
    @119
    @121
    wa
    #
    dvivth.1
    @12
    cM
    ne0i
    @122
    @12
    c0
    cA
    cB
    ndmioo
    necon1ai
    3syl
    #
    simpld
    #
    wph
    cN
    @15
    rexrd
    #
    cA
    cN
    cM
    elioo2
    syl2anc
    mpbir3and
    ad2antrr
    eqeltrd
    wph
    @111
    @12
    wss
    #
    @76
    @107
    wph
    @121
    cN
    cB
    cle
    wbr
    #
    @126
    wph
    @119
    @121
    @123
    simprd
    #
    wph
    cN
    cB
    clt
    wbr
    #
    @127
    wph
    cA
    cN
    clt
    wbr
    #
    @129
    wph
    @46
    @130
    @129
    wa
    dvivth.2
    cN
    cA
    cB
    eliooord
    syl
    simprd
    #
    wph
    @120
    @121
    @129
    @127
    wi
    @125
    @128
    cN
    cB
    xrltle
    syl2anc
    mpd
    cA
    cN
    cB
    iooss2
    syl2anc
    ad2antrr
    @108
    @4
    @12
    @54
    @77
    @91
    @107
    @93
    adantr
    wph
    @55
    @76
    @107
    @75
    ad2antrr
    eleqtrrd
    @108
    @102
    vw
    @4
    cN
    cioo
    co
    #
    wral
    @103
    @108
    @82
    @103
    @77
    @105
    @82
    simprr
    @104
    sylib
    @108
    @102
    vw
    @132
    @81
    @108
    @4
    cM
    cN
    cioo
    @112
    oveq1d
    raleqdv
    mpbird
    dvferm1
    eqbrtrrd
    @108
    @10
    cC
    @77
    @92
    @107
    @94
    adantr
    #
    wph
    @28
    @76
    @107
    @40
    ad2antrr
    #
    suble0d
    mpbid
    @108
    cC
    @30
    @10
    cle
    wph
    cC
    @30
    cle
    wbr
    #
    @76
    @107
    wph
    @28
    @29
    cC
    cle
    wbr
    #
    @135
    wph
    cC
    @31
    wcel
    #
    @28
    @136
    @135
    w3a
    #
    dvivth.6
    wph
    @32
    @33
    @137
    @138
    wb
    @38
    @39
    @29
    @30
    cC
    elicc2
    syl2anc
    mpbid
    #
    simp3d
    ad2antrr
    @108
    @4
    cM
    @9
    @112
    fveq2d
    breqtrrd
    @108
    @10
    cC
    @133
    @134
    letri3d
    mpbir2and
    exp32
    @77
    @106
    @82
    @11
    @77
    @106
    @82
    wa
    #
    wa
    #
    @11
    @109
    @110
    @141
    @10
    @29
    cC
    cle
    @141
    @4
    cN
    @9
    @77
    @106
    @82
    simprl
    #
    fveq2d
    wph
    @136
    @76
    @140
    wph
    @28
    @136
    @135
    @139
    simp2d
    ad2antrr
    eqbrtrd
    @141
    cc0
    @96
    cle
    wbr
    @110
    @141
    cc0
    @95
    @96
    cle
    @141
    vw
    cM
    cB
    @4
    cG
    @12
    wph
    @57
    @76
    @140
    @44
    ad2antrr
    @35
    @141
    @13
    a1i
    @141
    @4
    cN
    cM
    cB
    cioo
    co
    #
    @142
    wph
    cN
    @143
    wcel
    #
    @76
    @140
    wph
    @144
    cN
    cr
    wcel
    #
    @116
    @129
    @15
    dvivth.5
    @131
    wph
    cM
    cxr
    wcel
    #
    @121
    @144
    @145
    @116
    @129
    w3a
    wb
    wph
    cM
    @14
    rexrd
    #
    @128
    cM
    cB
    cN
    elioo2
    syl2anc
    mpbir3and
    ad2antrr
    eqeltrd
    wph
    @143
    @12
    wss
    #
    @76
    @140
    wph
    @119
    cA
    cM
    cle
    wbr
    #
    @148
    @124
    wph
    @115
    @149
    @118
    wph
    @119
    @146
    @115
    @149
    wi
    @124
    @147
    cA
    cM
    xrltle
    syl2anc
    mpd
    cA
    cM
    cB
    iooss1
    syl2anc
    ad2antrr
    @141
    @4
    @12
    @54
    @77
    @91
    @140
    @93
    adantr
    wph
    @55
    @76
    @140
    @75
    ad2antrr
    eleqtrrd
    @141
    @102
    vw
    cM
    @4
    cioo
    co
    #
    wral
    @103
    @141
    @82
    @103
    @77
    @106
    @82
    simprr
    @104
    sylib
    @141
    @102
    vw
    @150
    @81
    @141
    @4
    cN
    cM
    cioo
    @142
    oveq2d
    raleqdv
    mpbird
    dvferm2
    @77
    @97
    @140
    @99
    adantr
    breqtrd
    @141
    @10
    cC
    @77
    @92
    @140
    @94
    adantr
    #
    wph
    @28
    @76
    @140
    @40
    ad2antrr
    #
    subge0d
    mpbid
    @141
    @10
    cC
    @151
    @152
    letri3d
    mpbir2and
    exp32
    jaod
    syl5bi
    wph
    @85
    @88
    wo
    #
    @76
    @153
    @4
    @81
    @87
    cun
    #
    wcel
    wph
    @76
    @4
    @81
    @87
    elun
    wph
    @154
    @1
    @4
    wph
    @146
    @120
    cM
    cN
    cle
    wbr
    @154
    @1
    wceq
    @147
    @125
    @16
    cM
    cN
    prunioo
    syl3anc
    eleq2d
    syl5bbr
    biimpar
    mpjaod
    syld
    reximdva
    mpd
end
