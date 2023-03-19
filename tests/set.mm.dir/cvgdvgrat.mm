include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "wral.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "cle.mm"
include "cuz.mm"
include "eqid.mm"
include "cr.mm"
include "elioore.mm"
include "ad3antlr.mm"
include "w3a.mm"
include "cxr.mm"
include "wb.mm"
include "cz.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "syl.mm"
include "cdiv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "cc.mm"
include "peano2uzs.mm"
include "wi.mm"
include "ovex.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "eleq2i.mm"
include "uztrn2.mm"
include "sylan.mm"
include "sylan2b.mm"
include "syldan.mm"
include "chvarv.mm"
include "vtocl.mm"
include "sylan2.mm"
include "divcld.mm"
include "abscld.mm"
include "fvmpt2d.mm"
include "eqeltrd.mm"
include "climrecl.mm"
include "rexrd.mm"
include "1re.mm"
include "rexri.mm"
include "elioo2.mm"
include "sylancl.mm"
include "biimpa.mm"
include "simp3d.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "ex.mm"
include "ad3antrrr.mm"
include "imp.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "rspccva.mm"
include "adantll.mm"
include "cvgrat.mm"
include "cmin.mm"
include "wrex.mm"
include "adantr.mm"
include "crp.mm"
include "simp2d.mm"
include "difrp.mm"
include "syl2an.mm"
include "mpbid.mm"
include "adantlr.mm"
include "climi2.mm"
include "anassrs.mm"
include "adantllr.mm"
include "ad4antlr.mm"
include "remulcld.mm"
include "cc0.mm"
include "wne.mm"
include "absdivd.mm"
include "cneg.mm"
include "resubcld.mm"
include "absltd.mm"
include "simplbda.mm"
include "ad4antr.mm"
include "ltsub1d.mm"
include "mpbird.mm"
include "eqbrtrrd.mm"
include "absrpcld.mm"
include "ltdivmuld.mm"
include "rpcnd.mm"
include "recnd.mm"
include "mulcomd.mm"
include "breqtrd.mm"
include "ltled.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "c0.mm"
include "ioon0.mm"
include "biimpar.mm"
include "r19.3rzv.mm"
include "iserex.mm"
include "wn.mm"
include "wo.mm"
include "1red.mm"
include "lttri2d.mm"
include "orcanai.mm"
include "wnel.mm"
include "neeq1d.mm"
include "dvgrat.mm"
include "sylancr.mm"
include "mulid2d.mm"
include "1cnd.mm"
include "negsubdi2d.mm"
include "simprbda.mm"
include "ltmuldivd.mm"
include "df-nel.mm"
include "sylib.mm"
include "mtbird.mm"
include "impcon4bid.mm"

theorem cvgdvgrat
  let wph: wff ph
  let cR: class R
  let vk: setvar k
  let cF: class F
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vi: setvar i
  let vn: setvar n
  let vr: setvar r
  assume cvgdvgrat.z: |- Z = ( ZZ>= ` M )
  assume cvgdvgrat.w: |- W = ( ZZ>= ` N )
  assume cvgdvgrat.n: |- ( ph -> N e. Z )
  assume cvgdvgrat.f: |- ( ph -> F e. V )
  assume cvgdvgrat.c: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume cvgdvgrat.n0: |- ( ( ph /\ k e. W ) -> ( F ` k ) =/= 0 )
  assume cvgdvgrat.r: |- R = ( k e. W |-> ( abs ` ( ( F ` ( k + 1 ) ) / ( F ` k ) ) ) )
  assume cvgdvgrat.cvg: |- ( ph -> R ~~> L )
  assume cvgdvgrat.n1: |- ( ph -> L =/= 1 )

  disjoint k ph
  disjoint F k
  disjoint L k
  disjoint N k
  disjoint W k
  disjoint R k
  disjoint M k
  disjoint Z k
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i ph
  disjoint k n
  disjoint k r
  disjoint n r
  disjoint n ph
  disjoint ph r
  disjoint F i
  disjoint F n
  disjoint F r
  disjoint L i
  disjoint L n
  disjoint L r
  disjoint N i
  disjoint N n
  disjoint N r
  disjoint W i
  disjoint W n
  disjoint R n
  disjoint V i
  assert |- ( ph -> ( L < 1 <-> seq M ( + , F ) e. dom ~~> ) )

  proof
    wph
    cL
    c1
    clt
    wbr
    #
    caddc
    cF
    cM
    cseq
    cli
    cdm
    #
    wcel
    #
    wph
    @0
    @2
    wph
    @0
    wa
    #
    @2
    caddc
    cF
    cN
    cseq
    #
    @1
    wcel
    #
    @3
    @5
    @5
    vr
    cL
    c1
    cioo
    co
    #
    wral
    #
    wph
    @7
    @0
    wph
    @5
    vr
    @6
    wph
    vr
    cv
    #
    @6
    wcel
    #
    wa
    #
    vk
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    @8
    @11
    cF
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vk
    vn
    cv
    #
    cuz
    cfv
    #
    wral
    #
    @5
    vn
    cW
    @10
    @19
    cW
    wcel
    #
    wa
    #
    @21
    wa
    #
    @8
    vi
    cF
    cN
    @19
    @20
    cW
    cvgdvgrat.w
    @20
    eqid
    #
    @9
    @8
    cr
    wcel
    #
    wph
    @22
    @21
    @8
    cL
    c1
    elioore
    #
    ad3antlr
    @10
    @8
    c1
    clt
    wbr
    #
    @22
    @21
    @10
    @26
    cL
    @8
    clt
    wbr
    #
    @28
    wph
    @9
    @26
    @29
    @28
    w3a
    #
    wph
    cL
    cxr
    wcel
    #
    c1
    cxr
    wcel
    #
    @9
    @30
    wb
    wph
    cL
    wph
    cL
    vk
    cR
    cN
    cW
    cvgdvgrat.w
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    cN
    cz
    wcel
    #
    wph
    cN
    cZ
    @33
    cvgdvgrat.n
    cvgdvgrat.z
    syl6eleq
    cM
    cN
    eluzelz
    syl
    #
    cvgdvgrat.cvg
    wph
    @11
    cW
    wcel
    #
    wa
    #
    @11
    cR
    cfv
    #
    @13
    @15
    cdiv
    co
    #
    cabs
    cfv
    #
    cr
    wph
    vk
    cW
    @40
    cR
    cr
    cR
    vk
    cW
    @40
    cmpt
    wceq
    wph
    cvgdvgrat.r
    a1i
    @37
    @39
    @37
    @13
    @15
    @36
    wph
    @12
    cW
    wcel
    #
    @13
    cc
    wcel
    #
    cN
    @11
    cW
    cvgdvgrat.w
    peano2uzs
    wph
    vi
    cv
    #
    cW
    wcel
    #
    wa
    #
    @43
    cF
    cfv
    #
    cc
    wcel
    #
    wi
    #
    wph
    @41
    wa
    #
    @42
    wi
    vi
    @12
    @11
    c1
    caddc
    ovex
    @43
    @12
    wceq
    #
    @45
    @49
    @47
    @42
    @50
    @44
    @41
    wph
    @43
    @12
    cW
    eleq1
    anbi2d
    @50
    @46
    @13
    cc
    @43
    @12
    cF
    fveq2
    eleq1d
    imbi12d
    @37
    @15
    cc
    wcel
    #
    wi
    @48
    vk
    vi
    @11
    @43
    wceq
    #
    @37
    @45
    @51
    @47
    @52
    @36
    @44
    wph
    @11
    @43
    cW
    eleq1
    anbi2d
    #
    @52
    @15
    @46
    cc
    @11
    @43
    cF
    fveq2
    #
    eleq1d
    imbi12d
    wph
    @36
    @11
    cZ
    wcel
    #
    @51
    @36
    wph
    @11
    cN
    cuz
    cfv
    #
    wcel
    #
    @55
    cW
    @56
    @11
    cvgdvgrat.w
    eleq2i
    wph
    cN
    cZ
    wcel
    @57
    @55
    cvgdvgrat.n
    cM
    @11
    cN
    cZ
    cvgdvgrat.z
    uztrn2
    sylan
    sylan2b
    cvgdvgrat.c
    syldan
    #
    chvarv
    #
    vtocl
    sylan2
    #
    @58
    cvgdvgrat.n0
    divcld
    abscld
    #
    fvmpt2d
    #
    @61
    eqeltrd
    climrecl
    #
    rexrd
    #
    c1
    1re
    rexri
    #
    cL
    c1
    @8
    elioo2
    sylancl
    biimpa
    #
    simp3d
    ad2antrr
    @10
    @22
    @21
    simplr
    @24
    @44
    @47
    wph
    @44
    @47
    wi
    #
    @9
    @22
    @21
    wph
    @44
    @47
    @59
    ex
    #
    ad3antrrr
    imp
    @21
    @43
    @20
    wcel
    #
    @43
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    @8
    @46
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @23
    @18
    @75
    vk
    @43
    @20
    @52
    @14
    @72
    @17
    @74
    cle
    @52
    @13
    @71
    cabs
    @52
    @12
    @70
    cF
    @11
    @43
    c1
    caddc
    oveq1
    fveq2d
    fveq2d
    #
    @52
    @16
    @73
    @8
    cmul
    @52
    @15
    @46
    cabs
    @54
    fveq2d
    #
    oveq2d
    breq12d
    rspccva
    adantll
    cvgrat
    @10
    @40
    cL
    cmin
    co
    #
    cabs
    cfv
    #
    @8
    cL
    cmin
    co
    #
    clt
    wbr
    #
    vk
    @20
    wral
    #
    vn
    cW
    wrex
    @21
    vn
    cW
    wrex
    @10
    cL
    @40
    @80
    vn
    vk
    cR
    cN
    cW
    cvgdvgrat.w
    wph
    @34
    @9
    @35
    adantr
    @10
    @29
    @80
    crp
    wcel
    #
    @10
    @26
    @29
    @28
    @66
    simp2d
    wph
    cL
    cr
    wcel
    #
    @26
    @29
    @83
    wb
    @9
    @63
    @27
    cL
    @8
    difrp
    syl2an
    mpbid
    wph
    @36
    @38
    @40
    wceq
    #
    @9
    @62
    adantlr
    wph
    cR
    cL
    cli
    wbr
    #
    @9
    cvgdvgrat.cvg
    adantr
    climi2
    @10
    @82
    @21
    vn
    cW
    @23
    @81
    @18
    vk
    @20
    @23
    @11
    @20
    wcel
    #
    wa
    #
    @81
    @18
    @88
    @81
    wa
    #
    @14
    @17
    @89
    @13
    @88
    @42
    @81
    wph
    @22
    @87
    @42
    @9
    wph
    @22
    @87
    @42
    @22
    @87
    wa
    #
    wph
    @36
    @42
    cN
    @11
    @19
    cW
    cvgdvgrat.w
    uztrn2
    #
    @60
    sylan2
    anassrs
    #
    adantllr
    #
    adantr
    #
    abscld
    #
    @89
    @8
    @16
    @9
    @26
    wph
    @22
    @87
    @81
    @27
    ad4antlr
    #
    @89
    @15
    @88
    @51
    @81
    wph
    @22
    @87
    @51
    @9
    wph
    @22
    @87
    @51
    @90
    wph
    @36
    @51
    @91
    @58
    sylan2
    anassrs
    #
    adantllr
    #
    adantr
    #
    abscld
    remulcld
    @89
    @14
    @16
    @8
    cmul
    co
    #
    @17
    clt
    @89
    @14
    @16
    cdiv
    co
    #
    @8
    clt
    wbr
    @14
    @100
    clt
    wbr
    @89
    @40
    @101
    @8
    clt
    @89
    @13
    @15
    @94
    @99
    @88
    @15
    cc0
    wne
    #
    @81
    wph
    @22
    @87
    @102
    @9
    wph
    @22
    @87
    @102
    @90
    wph
    @36
    @102
    @91
    cvgdvgrat.n0
    sylan2
    anassrs
    #
    adantllr
    #
    adantr
    #
    absdivd
    @89
    @40
    @8
    clt
    wbr
    @78
    @80
    clt
    wbr
    #
    @88
    @81
    @80
    cneg
    @78
    clt
    wbr
    @106
    @88
    @78
    @80
    @88
    @40
    cL
    @88
    @39
    @88
    @13
    @15
    @93
    @98
    @104
    divcld
    abscld
    wph
    @84
    @9
    @22
    @87
    @63
    ad3antrrr
    #
    resubcld
    @88
    @8
    cL
    @9
    @26
    wph
    @22
    @87
    @27
    ad3antlr
    @107
    resubcld
    absltd
    simplbda
    @89
    @40
    @8
    cL
    @89
    @39
    @89
    @13
    @15
    @94
    @99
    @105
    divcld
    abscld
    @96
    wph
    @84
    @9
    @22
    @87
    @81
    @63
    ad4antr
    ltsub1d
    mpbird
    eqbrtrrd
    @89
    @14
    @8
    @16
    @95
    @96
    @89
    @15
    @99
    @105
    absrpcld
    #
    ltdivmuld
    mpbid
    @89
    @16
    @8
    @89
    @16
    @108
    rpcnd
    @89
    @8
    @96
    recnd
    mulcomd
    breqtrd
    ltled
    ex
    ralimdva
    reximdva
    mpd
    r19.29a
    ralrimiva
    adantr
    @3
    @6
    c0
    wne
    #
    @5
    @7
    wb
    wph
    @109
    @0
    wph
    @31
    @32
    @109
    @0
    wb
    @64
    @65
    cL
    c1
    ioon0
    sylancl
    biimpar
    @5
    vr
    @6
    r19.3rzv
    syl
    mpbird
    wph
    @2
    @5
    wb
    #
    @0
    wph
    vk
    cF
    cM
    cN
    cZ
    cvgdvgrat.z
    cvgdvgrat.n
    cvgdvgrat.c
    iserex
    #
    adantr
    mpbird
    ex
    wph
    @0
    wn
    #
    @2
    wn
    #
    wph
    @112
    c1
    cL
    clt
    wbr
    #
    @113
    wph
    @0
    @114
    wph
    cL
    c1
    wne
    @0
    @114
    wo
    cvgdvgrat.n1
    wph
    cL
    c1
    @63
    wph
    1red
    lttri2d
    mpbid
    orcanai
    wph
    @114
    wa
    #
    @2
    @5
    @115
    @4
    @1
    wnel
    #
    @5
    wn
    @115
    @16
    @14
    cle
    wbr
    #
    vk
    @20
    wral
    #
    @116
    vn
    cW
    @115
    @22
    wa
    #
    @118
    wa
    #
    vi
    cF
    cN
    @19
    cV
    @20
    cW
    cvgdvgrat.w
    @25
    @115
    @22
    @118
    simplr
    wph
    cF
    cV
    wcel
    @114
    @22
    @118
    cvgdvgrat.f
    ad3antrrr
    @120
    @44
    @47
    wph
    @67
    @114
    @22
    @118
    @68
    ad3antrrr
    imp
    @119
    @69
    @46
    cc0
    wne
    #
    @118
    wph
    @22
    @69
    @121
    @114
    wph
    @22
    @69
    @121
    @22
    @69
    wa
    wph
    @44
    @121
    cN
    @43
    @19
    cW
    cvgdvgrat.w
    uztrn2
    @37
    @102
    wi
    @45
    @121
    wi
    vk
    vi
    @52
    @37
    @45
    @102
    @121
    @53
    @52
    @15
    @46
    cc0
    @54
    neeq1d
    imbi12d
    cvgdvgrat.n0
    chvarv
    sylan2
    anassrs
    adantllr
    adantlr
    @118
    @69
    @73
    @72
    cle
    wbr
    #
    @119
    @117
    @122
    vk
    @43
    @20
    @52
    @16
    @73
    @14
    @72
    cle
    @77
    @76
    breq12d
    rspccva
    adantll
    dvgrat
    @115
    @79
    cL
    c1
    cmin
    co
    #
    clt
    wbr
    #
    vk
    @20
    wral
    #
    vn
    cW
    wrex
    @118
    vn
    cW
    wrex
    @115
    cL
    @40
    @123
    vn
    vk
    cR
    cN
    cW
    cvgdvgrat.w
    wph
    @34
    @114
    @35
    adantr
    wph
    @114
    @123
    crp
    wcel
    #
    wph
    c1
    cr
    wcel
    @84
    @114
    @126
    wb
    1re
    @63
    c1
    cL
    difrp
    sylancr
    biimpa
    wph
    @36
    @85
    @114
    @62
    adantlr
    wph
    @86
    @114
    cvgdvgrat.cvg
    adantr
    climi2
    @115
    @125
    @118
    vn
    cW
    @119
    @124
    @117
    vk
    @20
    @119
    @87
    wa
    #
    @124
    @117
    @127
    @124
    wa
    #
    @16
    @14
    @128
    @15
    @127
    @51
    @124
    wph
    @22
    @87
    @51
    @114
    @97
    adantllr
    #
    adantr
    #
    abscld
    @128
    @13
    @127
    @42
    @124
    wph
    @22
    @87
    @42
    @114
    @92
    adantllr
    #
    adantr
    #
    abscld
    #
    @128
    c1
    @16
    cmul
    co
    #
    @16
    @14
    clt
    @128
    @16
    @128
    @16
    @128
    @15
    @130
    @127
    @102
    @124
    wph
    @22
    @87
    @102
    @114
    @103
    adantllr
    #
    adantr
    #
    absrpcld
    #
    rpcnd
    mulid2d
    @128
    @134
    @14
    clt
    wbr
    c1
    @101
    clt
    wbr
    @128
    c1
    @40
    @101
    clt
    @128
    c1
    @40
    clt
    wbr
    c1
    cL
    cmin
    co
    #
    @78
    clt
    wbr
    @128
    @123
    cneg
    #
    @138
    @78
    clt
    @128
    cL
    c1
    @128
    cL
    wph
    @84
    @114
    @22
    @87
    @124
    @63
    ad4antr
    #
    recnd
    @128
    1cnd
    negsubdi2d
    @127
    @124
    @139
    @78
    clt
    wbr
    @78
    @123
    clt
    wbr
    @127
    @78
    @123
    @127
    @40
    cL
    @127
    @39
    @127
    @13
    @15
    @131
    @129
    @135
    divcld
    abscld
    wph
    @84
    @114
    @22
    @87
    @63
    ad3antrrr
    #
    resubcld
    @127
    cL
    c1
    @141
    @127
    1red
    resubcld
    absltd
    simprbda
    eqbrtrrd
    @128
    c1
    @40
    cL
    @128
    1red
    #
    @128
    @39
    @128
    @13
    @15
    @132
    @130
    @136
    divcld
    abscld
    @140
    ltsub1d
    mpbird
    @128
    @13
    @15
    @132
    @130
    @136
    absdivd
    breqtrd
    @128
    c1
    @14
    @16
    @142
    @133
    @137
    ltmuldivd
    mpbird
    eqbrtrrd
    ltled
    ex
    ralimdva
    reximdva
    mpd
    r19.29a
    @4
    @1
    df-nel
    sylib
    wph
    @110
    @114
    @111
    adantr
    mtbird
    syldan
    ex
    impcon4bid
end
