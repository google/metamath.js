include "csn.mm"
include "cun.mm"
include "cprod.mm"
include "cmpt.mm"
include "cdv.mm"
include "co.mm"
include "cmul.mm"
include "cv.mm"
include "cdif.mm"
include "csu.mm"
include "caddc.mm"
include "wcel.mm"
include "wa.mm"
include "nfcv.mm"
include "nfel.mm"
include "nfan.mm"
include "wnfc.mm"
include "a1i.mm"
include "cfn.mm"
include "snfi.mm"
include "unfi.mm"
include "syl2anc.mm"
include "adantr.mm"
include "cc.mm"
include "simpll.mm"
include "sselda.mm"
include "adantlr.mm"
include "simplr.mm"
include "syl3anc.mm"
include "cvv.mm"
include "snidg.mm"
include "syl.mm"
include "elun2.mm"
include "wceq.mm"
include "adantl.mm"
include "fprodsplit1f.mm"
include "c0.mm"
include "difundir.mm"
include "wn.mm"
include "difsn.mm"
include "difid.mm"
include "uneq12d.mm"
include "un0.mm"
include "3eqtrd.mm"
include "prodeq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "mpteq2da.mm"
include "w3a.mm"
include "sseldd.mm"
include "simpl.mm"
include "simpr.mm"
include "3jca.mm"
include "wi.mm"
include "nfv.mm"
include "nf3an.mm"
include "nfim.mm"
include "ancom.mm"
include "imbi1i.mm"
include "eqcom.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "3adantr2.mm"
include "3adant2.mm"
include "simp3.mm"
include "eleq1.mm"
include "3anbi2d.mm"
include "imbi1d.mm"
include "biimpa.mm"
include "3adant3.mm"
include "mpd.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "2a1i.mm"
include "impbid.mm"
include "vtoclgf.mm"
include "sylc.mm"
include "wss.mm"
include "elun1.mm"
include "fprodclf.mm"
include "diffi.mm"
include "eldifi.mm"
include "syldan.mm"
include "mulcld.mm"
include "fsumclf.mm"
include "dvmptmulf.mm"
include "nfov.mm"
include "sneq.mm"
include "difeq2d.mm"
include "oveq12d.mm"
include "fsumsplitsn.mm"
include "cin.mm"
include "wral.mm"
include "elsni.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "adantll.mm"
include "simpllr.mm"
include "ad3antrrr.mm"
include "pm2.65da.mm"
include "velsn.mm"
include "sylnibr.mm"
include "ex.mm"
include "ralrimi.mm"
include "disj.mm"
include "sylibr.mm"
include "disjdif2.mm"
include "uneq2d.mm"
include "id.mm"
include "intnanrd.mm"
include "eldif.mm"
include "fprodsplitsn.mm"
include "mulassd.mm"
include "sumeq2d.mm"
include "fsummulc1f.mm"
include "addcomd.mm"
include "3eqtrrd.mm"

theorem dvmptfprodlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let vk: setvar k
  assume dvmptfprodlem.xph: |- F/ x ph
  assume dvmptfprodlem.iph: |- F/ i ph
  assume dvmptfprodlem.jph: |- F/ j ph
  assume dvmptfprodlem.if: |- F/_ i F
  assume dvmptfprodlem.jg: |- F/_ j G
  assume dvmptfprodlem.a: |- ( ( ph /\ i e. I /\ x e. X ) -> A e. CC )
  assume dvmptfprodlem.d: |- ( ph -> D e. Fin )
  assume dvmptfprodlem.e: |- ( ph -> E e. _V )
  assume dvmptfprodlem.db: |- ( ph -> -. E e. D )
  assume dvmptfprodlem.ss: |- ( ph -> ( D u. { E } ) C_ I )
  assume dvmptfprodlem.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptfprodlem.c: |- ( ( ( ph /\ x e. X ) /\ j e. D ) -> C e. CC )
  assume dvmptfprodlem.dvp: |- ( ph -> ( S _D ( x e. X |-> prod_ i e. D A ) ) = ( x e. X |-> sum_ j e. D ( C x. prod_ i e. ( D \ { j } ) A ) ) )
  assume dvmptfprodlem.14: |- ( ( ph /\ x e. X ) -> G e. CC )
  assume dvmptfprodlem.dvf: |- ( ph -> ( S _D ( x e. X |-> F ) ) = ( x e. X |-> G ) )
  assume dvmptfprodlem.f: |- ( i = E -> A = F )
  assume dvmptfprodlem.cg: |- ( j = E -> C = G )

  disjoint A j
  disjoint D i
  disjoint D j
  disjoint D x
  disjoint i j
  disjoint i x
  disjoint j x
  disjoint E i
  disjoint E j
  disjoint E x
  disjoint F j
  disjoint I i
  disjoint X i
  disjoint X j
  disjoint X x
  disjoint k x
  assert |- ( ph -> ( S _D ( x e. X |-> prod_ i e. ( D u. { E } ) A ) ) = ( x e. X |-> sum_ j e. ( D u. { E } ) ( C x. prod_ i e. ( ( D u. { E } ) \ { j } ) A ) ) )

  proof
    wph
    cS
    vx
    cX
    cD
    cE
    csn
    #
    cun
    #
    cA
    vi
    cprod
    #
    cmpt
    #
    cdv
    co
    cS
    vx
    cX
    cF
    cD
    cA
    vi
    cprod
    #
    cmul
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    cG
    @4
    cmul
    co
    #
    cD
    cC
    cD
    vj
    cv
    #
    csn
    #
    cdif
    #
    cA
    vi
    cprod
    #
    cmul
    co
    #
    vj
    csu
    #
    cF
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    vx
    cX
    @1
    cC
    @1
    @9
    cdif
    #
    cA
    vi
    cprod
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    wph
    @3
    @6
    cS
    cdv
    wph
    vx
    cX
    @2
    @5
    dvmptfprodlem.xph
    wph
    vx
    cv
    #
    cX
    wcel
    #
    wa
    #
    @2
    cF
    @1
    @0
    cdif
    #
    cA
    vi
    cprod
    #
    cmul
    co
    #
    @5
    @22
    @1
    cA
    cE
    cF
    vi
    wph
    @21
    vi
    dvmptfprodlem.iph
    vi
    @20
    cX
    vi
    @20
    nfcv
    vi
    cX
    nfcv
    nfel
    #
    nfan
    #
    vi
    cF
    wnfc
    @22
    dvmptfprodlem.if
    a1i
    wph
    @1
    cfn
    wcel
    #
    @21
    wph
    cD
    cfn
    wcel
    #
    @0
    cfn
    wcel
    #
    @28
    dvmptfprodlem.d
    @30
    wph
    cE
    snfi
    a1i
    cD
    @0
    unfi
    syl2anc
    #
    adantr
    @22
    vi
    cv
    #
    @1
    wcel
    #
    wa
    wph
    @32
    cI
    wcel
    #
    @21
    cA
    cc
    wcel
    #
    wph
    @21
    @33
    simpll
    wph
    @33
    @34
    @21
    wph
    @1
    cI
    @32
    dvmptfprodlem.ss
    sselda
    adantlr
    wph
    @21
    @33
    simplr
    dvmptfprodlem.a
    syl3anc
    #
    wph
    cE
    @1
    wcel
    #
    @21
    wph
    cE
    @0
    wcel
    #
    @37
    wph
    cE
    cvv
    wcel
    #
    @38
    dvmptfprodlem.e
    cE
    cvv
    snidg
    syl
    cE
    @0
    cD
    elun2
    syl
    #
    adantr
    @32
    cE
    wceq
    #
    cA
    cF
    wceq
    #
    @22
    dvmptfprodlem.f
    adantl
    #
    fprodsplit1f
    wph
    @25
    @5
    wceq
    @21
    wph
    @24
    @4
    cF
    cmul
    wph
    @23
    cD
    cA
    vi
    wph
    @23
    cD
    @0
    cdif
    #
    @0
    @0
    cdif
    #
    cun
    #
    cD
    c0
    cun
    #
    cD
    @23
    @46
    wceq
    wph
    cD
    @0
    @0
    difundir
    a1i
    wph
    @44
    cD
    @45
    c0
    wph
    cE
    cD
    wcel
    #
    wn
    #
    @44
    cD
    wceq
    dvmptfprodlem.db
    cE
    cD
    difsn
    syl
    @45
    c0
    wceq
    wph
    @0
    difid
    a1i
    uneq12d
    @47
    cD
    wceq
    wph
    cD
    un0
    a1i
    3eqtrd
    #
    prodeq1d
    #
    oveq2d
    adantr
    eqtrd
    mpteq2da
    oveq2d
    wph
    vx
    cF
    cG
    @4
    @13
    cS
    cc
    cc
    cX
    dvmptfprodlem.xph
    dvmptfprodlem.s
    @22
    cE
    cI
    wcel
    #
    wph
    @52
    @21
    w3a
    #
    cF
    cc
    wcel
    #
    wph
    @52
    @21
    wph
    @1
    cI
    cE
    dvmptfprodlem.ss
    @40
    sseldd
    adantr
    #
    @22
    wph
    @52
    @21
    wph
    @21
    simpl
    #
    @55
    wph
    @21
    simpr
    #
    3jca
    wph
    @34
    @21
    w3a
    #
    @35
    wi
    #
    @53
    @54
    wi
    #
    vi
    cE
    cI
    vi
    cE
    nfcv
    @53
    @54
    vi
    wph
    @52
    @21
    vi
    dvmptfprodlem.iph
    @52
    vi
    nfv
    @26
    nf3an
    vi
    cF
    cc
    dvmptfprodlem.if
    vi
    cc
    nfcv
    nfel
    nfim
    @41
    @59
    @60
    @41
    @59
    @53
    @54
    @41
    @59
    @53
    w3a
    #
    cF
    cA
    cc
    @41
    @53
    cF
    cA
    wceq
    #
    @59
    @41
    wph
    @21
    @62
    @52
    @22
    @41
    wa
    #
    @42
    wi
    #
    @41
    @22
    wa
    #
    @62
    wi
    #
    @43
    @64
    @65
    @42
    wi
    @66
    @63
    @65
    @42
    @22
    @41
    ancom
    imbi1i
    @42
    @62
    @65
    cA
    cF
    eqcom
    imbi2i
    bitri
    mpbi
    3adantr2
    3adant2
    @61
    @53
    @35
    @41
    @59
    @53
    simp3
    @41
    @59
    @53
    @35
    wi
    #
    @53
    @41
    @59
    @67
    @41
    @58
    @53
    @35
    @41
    @34
    @52
    wph
    @21
    @32
    cE
    cI
    eleq1
    3anbi2d
    imbi1d
    biimpa
    3adant3
    mpd
    eqeltrd
    3exp
    @59
    @41
    @60
    dvmptfprodlem.a
    2a1i
    impbid
    dvmptfprodlem.a
    vtoclgf
    sylc
    #
    dvmptfprodlem.14
    dvmptfprodlem.dvf
    @22
    cD
    cA
    vi
    @27
    @22
    wph
    @29
    @56
    dvmptfprodlem.d
    syl
    #
    @22
    @32
    cD
    wcel
    #
    wa
    wph
    @34
    @21
    @35
    @22
    wph
    @70
    @56
    adantr
    wph
    @70
    @34
    @21
    wph
    @70
    wa
    @1
    cI
    @32
    wph
    @1
    cI
    wss
    #
    @70
    dvmptfprodlem.ss
    adantr
    @70
    @33
    wph
    @32
    cD
    @0
    elun1
    adantl
    sseldd
    adantlr
    @22
    @21
    @70
    @57
    adantr
    dvmptfprodlem.a
    syl3anc
    #
    fprodclf
    @22
    cD
    @12
    vj
    wph
    @21
    vj
    dvmptfprodlem.jph
    @21
    vj
    nfv
    nfan
    #
    @69
    @22
    @8
    cD
    wcel
    #
    wa
    #
    cC
    @11
    dvmptfprodlem.c
    @22
    @11
    cc
    wcel
    @74
    @22
    @10
    cA
    vi
    @27
    wph
    @10
    cfn
    wcel
    #
    @21
    wph
    @29
    @76
    dvmptfprodlem.d
    cD
    @9
    diffi
    syl
    adantr
    #
    @22
    @32
    @10
    wcel
    #
    @70
    @35
    @78
    @70
    @22
    @32
    cD
    @9
    eldifi
    adantl
    @72
    syldan
    #
    fprodclf
    adantr
    #
    mulcld
    #
    fsumclf
    #
    dvmptfprodlem.dvp
    dvmptmulf
    wph
    vx
    cX
    @15
    @19
    dvmptfprodlem.xph
    @22
    @19
    cD
    @18
    vj
    csu
    #
    cG
    @24
    cmul
    co
    #
    caddc
    co
    @84
    @83
    caddc
    co
    @15
    @22
    cD
    cE
    @18
    @84
    vj
    cvv
    @73
    vj
    cG
    @24
    cmul
    dvmptfprodlem.jg
    vj
    cmul
    nfcv
    vj
    @24
    nfcv
    nfov
    @69
    @22
    wph
    @39
    @56
    dvmptfprodlem.e
    syl
    @22
    wph
    @49
    @56
    dvmptfprodlem.db
    syl
    @75
    cC
    @17
    dvmptfprodlem.c
    @22
    @17
    cc
    wcel
    @74
    @22
    @16
    cA
    vi
    @27
    wph
    @16
    cfn
    wcel
    #
    @21
    wph
    @28
    @85
    @31
    @1
    @9
    diffi
    syl
    adantr
    @22
    @32
    @16
    wcel
    #
    @33
    @35
    @86
    @33
    @22
    @32
    @1
    @9
    eldifi
    adantl
    @36
    syldan
    fprodclf
    adantr
    mulcld
    @8
    cE
    wceq
    #
    cC
    cG
    @17
    @24
    cmul
    dvmptfprodlem.cg
    @87
    @16
    @23
    cA
    vi
    @87
    @9
    @0
    @1
    @8
    cE
    sneq
    difeq2d
    prodeq1d
    oveq12d
    @22
    cG
    @24
    dvmptfprodlem.14
    @22
    @23
    cA
    vi
    @27
    wph
    @23
    cfn
    wcel
    @21
    wph
    @23
    cD
    cfn
    @50
    dvmptfprodlem.d
    eqeltrd
    adantr
    @22
    @32
    @23
    wcel
    #
    wa
    wph
    @34
    @21
    @35
    @22
    wph
    @88
    @56
    adantr
    wph
    @88
    @34
    @21
    wph
    @88
    wa
    @1
    cI
    @32
    wph
    @71
    @88
    dvmptfprodlem.ss
    adantr
    @88
    @33
    wph
    @32
    @1
    @0
    eldifi
    adantl
    sseldd
    adantlr
    @22
    @21
    @88
    @57
    adantr
    dvmptfprodlem.a
    syl3anc
    fprodclf
    mulcld
    #
    fsumsplitsn
    @22
    @83
    @84
    @22
    @83
    @14
    cc
    @22
    @83
    cD
    @12
    cF
    cmul
    co
    #
    vj
    csu
    #
    @14
    @14
    @22
    cD
    @18
    @90
    vj
    @22
    @18
    @90
    wceq
    #
    vj
    cD
    @73
    @22
    @74
    @92
    @75
    @18
    cC
    @11
    cF
    cmul
    co
    #
    cmul
    co
    #
    @90
    @75
    @17
    @93
    cC
    cmul
    @75
    @17
    @10
    @0
    cun
    #
    cA
    vi
    cprod
    #
    @93
    @93
    wph
    @74
    @17
    @96
    wceq
    @21
    wph
    @74
    wa
    #
    @16
    @95
    cA
    vi
    @97
    @16
    @10
    @0
    @9
    cdif
    #
    cun
    #
    @95
    @16
    @99
    wceq
    @97
    cD
    @0
    @9
    difundir
    a1i
    @97
    @98
    @0
    @10
    @97
    @0
    @9
    cin
    c0
    wceq
    #
    @98
    @0
    wceq
    @97
    @20
    @9
    wcel
    #
    wn
    #
    vx
    @0
    wral
    @100
    @97
    @102
    vx
    @0
    wph
    @74
    vx
    dvmptfprodlem.xph
    @74
    vx
    nfv
    nfan
    @97
    @20
    @0
    wcel
    #
    @102
    @97
    @103
    wa
    #
    @20
    @8
    wceq
    #
    @101
    @104
    @105
    @48
    @104
    @105
    wa
    cE
    @8
    cD
    @103
    @105
    cE
    @8
    wceq
    @97
    @103
    @105
    wa
    #
    cE
    @20
    @8
    @8
    @103
    cE
    @20
    wceq
    @105
    @103
    @20
    cE
    @20
    cE
    elsni
    eqcomd
    adantr
    @103
    @105
    simpr
    @106
    @8
    eqidd
    3eqtrd
    adantll
    wph
    @74
    @103
    @105
    simpllr
    eqeltrd
    wph
    @49
    @74
    @103
    @105
    dvmptfprodlem.db
    ad3antrrr
    pm2.65da
    vx
    @8
    velsn
    sylnibr
    ex
    ralrimi
    vx
    @0
    @9
    disj
    sylibr
    @0
    @9
    disjdif2
    syl
    uneq2d
    eqtrd
    prodeq1d
    adantlr
    @75
    @10
    cE
    cA
    cF
    vi
    cvv
    @22
    @74
    vi
    @27
    @74
    vi
    nfv
    nfan
    dvmptfprodlem.if
    @22
    @76
    @74
    @77
    adantr
    @75
    wph
    @39
    @22
    wph
    @74
    @56
    adantr
    #
    dvmptfprodlem.e
    syl
    @75
    wph
    cE
    @10
    wcel
    #
    wn
    #
    @107
    wph
    @49
    @109
    dvmptfprodlem.db
    @49
    @48
    cE
    @9
    wcel
    wn
    #
    wa
    #
    @108
    @49
    @49
    @111
    wn
    @49
    id
    #
    @49
    @48
    @110
    @112
    intnanrd
    syl
    cE
    cD
    @9
    eldif
    sylnibr
    syl
    syl
    @22
    @78
    @35
    @74
    @79
    adantlr
    dvmptfprodlem.f
    @22
    @54
    @74
    @68
    adantr
    #
    fprodsplitsn
    @75
    @93
    eqidd
    3eqtrd
    oveq2d
    @75
    @90
    @94
    @75
    cC
    @11
    cF
    dvmptfprodlem.c
    @80
    @113
    mulassd
    eqcomd
    eqtrd
    ex
    ralrimi
    sumeq2d
    @22
    @14
    @91
    @22
    cD
    @12
    cF
    vj
    @73
    @69
    @68
    @81
    fsummulc1f
    eqcomd
    @22
    @14
    eqidd
    3eqtrd
    #
    @22
    @13
    cF
    @82
    @68
    mulcld
    eqeltrd
    @89
    addcomd
    @22
    @84
    @7
    @83
    @14
    caddc
    wph
    @84
    @7
    wceq
    @21
    wph
    @24
    @4
    cG
    cmul
    @51
    oveq2d
    adantr
    @114
    oveq12d
    3eqtrrd
    mpteq2da
    3eqtrd
end
