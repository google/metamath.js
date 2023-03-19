include "cr.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "wne.mm"
include "wa.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "simpll.mm"
include "eldifad.mm"
include "eldifsni.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "jca.mm"
include "simpr.mm"
include "cv.mm"
include "wral.mm"
include "simprr.mm"
include "wi.mm"
include "cs1.mm"
include "cconcat.mm"
include "wceq.mm"
include "neeq1.mm"
include "fveq1.mm"
include "neeq1d.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "raleqbidv.mm"
include "imbi12d.mm"
include "neirr.mm"
include "intnanr.mm"
include "pm2.21i.mm"
include "cbvralv.mm"
include "imbi2i.mm"
include "anbi2i.mm"
include "wn.mm"
include "noel.mm"
include "hash0.mm"
include "syl6eq.mm"
include "fzo0.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "adantl.mm"
include "pm2.21dd.mm"
include "simp-6l.mm"
include "simp-6r.mm"
include "signstfvp.mm"
include "syl3anc.mm"
include "simplll.mm"
include "w3a.mm"
include "simplrr.mm"
include "3anassrs.mm"
include "s1cld.mm"
include "cn.mm"
include "c1.mm"
include "cmin.mm"
include "lennncl.mm"
include "adantlr.mm"
include "fzo0end.mm"
include "elfzolt3b.mm"
include "3syl.mm"
include "ccatval1.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "simp-5r.mm"
include "mp2and.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "eqnetrd.mm"
include "pm2.61dane.mm"
include "fveq2d.mm"
include "simp-4r.mm"
include "simplrl.mm"
include "simprd.mm"
include "csgn.mm"
include "oveq1.mm"
include "s1cl.mm"
include "ccatlid.mm"
include "syl.mm"
include "sylan9eq.mm"
include "adantr.mm"
include "signstf0.mm"
include "eqtrd.mm"
include "fveq12d.mm"
include "sgnclre.mm"
include "s1fv.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "sgn0bi.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "velsn.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "simpllr.mm"
include "signstfvn.mm"
include "adantllr.mm"
include "cneg.mm"
include "ctp.mm"
include "neqned.mm"
include "signstcl.mm"
include "rexrd.mm"
include "sgncl.mm"
include "signswn0.mm"
include "pm2.61dan.mm"
include "anassrs.mm"
include "cuz.mm"
include "caddc.mm"
include "wo.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "ad4antr.mm"
include "ccatws1len.mm"
include "fzosplitsni.mm"
include "mpjaodan.mm"
include "ralrimiva.mm"
include "sylanbr.mm"
include "exp31.mm"
include "wrdind.mm"
include "imp.mm"
include "adantrr.mm"
include "syl12anc.mm"

theorem signstfvneq0
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  let vk: setvar k
  let vm: setvar m
  let vg: setvar g
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

  disjoint i n
  disjoint N i
  disjoint N n
  disjoint f i
  disjoint f n
  disjoint a b
  disjoint a n
  disjoint T a
  disjoint b n
  disjoint T b
  disjoint T n
  disjoint a b
  disjoint .+^ a
  disjoint .+^ b
  disjoint f i
  disjoint f n
  disjoint F f
  disjoint i n
  disjoint F i
  disjoint F n
  disjoint W f
  disjoint W i
  disjoint W n
  disjoint e f
  disjoint e i
  disjoint e k
  disjoint e m
  disjoint e n
  disjoint f k
  disjoint f m
  disjoint i k
  disjoint i m
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint g m
  disjoint F g
  disjoint F m
  disjoint N m
  disjoint a e
  disjoint a g
  disjoint a k
  disjoint a m
  disjoint b e
  disjoint b g
  disjoint b k
  disjoint b m
  disjoint e g
  disjoint T e
  disjoint g k
  disjoint g n
  disjoint T g
  disjoint T k
  disjoint T m
  disjoint K f
  disjoint K i
  disjoint K n
  assert |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 ) /\ N e. ( 0 ..^ ( # ` F ) ) ) -> ( ( T ` F ) ` N ) =/= 0 )

  proof
    cF
    cr
    cword
    #
    c0
    csn
    #
    cdif
    #
    wcel
    #
    cc0
    cF
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cN
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    #
    wa
    #
    cF
    @0
    wcel
    #
    cF
    c0
    wne
    #
    @5
    wa
    #
    @9
    cN
    cF
    cT
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    @10
    cF
    @0
    @1
    @3
    @5
    @9
    simpll
    eldifad
    @10
    @12
    @5
    @3
    @12
    @5
    @9
    cF
    @0
    c0
    eldifsni
    ad2antrr
    @3
    @5
    @9
    simplr
    jca
    @6
    @9
    simpr
    @11
    @13
    @9
    wa
    wa
    @9
    vm
    cv
    #
    @14
    cfv
    #
    cc0
    wne
    #
    vm
    @8
    wral
    #
    @16
    @11
    @13
    @9
    simprr
    @11
    @13
    @20
    @9
    @11
    @13
    @20
    vg
    cv
    #
    c0
    wne
    #
    cc0
    @21
    cfv
    #
    cc0
    wne
    #
    wa
    #
    @17
    @21
    cT
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    vm
    cc0
    @21
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    wi
    c0
    c0
    wne
    #
    cc0
    c0
    cfv
    #
    cc0
    wne
    #
    wa
    #
    @17
    c0
    cT
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    vm
    cc0
    c0
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    wi
    ve
    cv
    #
    c0
    wne
    #
    cc0
    @42
    cfv
    #
    cc0
    wne
    #
    wa
    #
    @17
    @42
    cT
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    vm
    cc0
    @42
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    wi
    #
    @42
    vk
    cv
    #
    cs1
    #
    cconcat
    co
    #
    c0
    wne
    #
    cc0
    @56
    cfv
    #
    cc0
    wne
    #
    wa
    #
    @17
    @56
    cT
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    vm
    cc0
    @56
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    wi
    @13
    @20
    wi
    vg
    ve
    vk
    cF
    cr
    @21
    c0
    wceq
    #
    @25
    @35
    @31
    @41
    @67
    @22
    @32
    @24
    @34
    @21
    c0
    c0
    neeq1
    @67
    @23
    @33
    cc0
    cc0
    @21
    c0
    fveq1
    neeq1d
    anbi12d
    @67
    @28
    @38
    vm
    @30
    @40
    @67
    @29
    @39
    cc0
    cfzo
    @21
    c0
    chash
    fveq2
    oveq2d
    @67
    @27
    @37
    cc0
    @67
    @17
    @26
    @36
    @21
    c0
    cT
    fveq2
    fveq1d
    neeq1d
    raleqbidv
    imbi12d
    @21
    @42
    wceq
    #
    @25
    @46
    @31
    @52
    @68
    @22
    @43
    @24
    @45
    @21
    @42
    c0
    neeq1
    @68
    @23
    @44
    cc0
    cc0
    @21
    @42
    fveq1
    neeq1d
    anbi12d
    @68
    @28
    @49
    vm
    @30
    @51
    @68
    @29
    @50
    cc0
    cfzo
    @21
    @42
    chash
    fveq2
    oveq2d
    @68
    @27
    @48
    cc0
    @68
    @17
    @26
    @47
    @21
    @42
    cT
    fveq2
    fveq1d
    neeq1d
    raleqbidv
    imbi12d
    @21
    @56
    wceq
    #
    @25
    @60
    @31
    @66
    @69
    @22
    @57
    @24
    @59
    @21
    @56
    c0
    neeq1
    @69
    @23
    @58
    cc0
    cc0
    @21
    @56
    fveq1
    neeq1d
    anbi12d
    @69
    @28
    @63
    vm
    @30
    @65
    @69
    @29
    @64
    cc0
    cfzo
    @21
    @56
    chash
    fveq2
    oveq2d
    @69
    @27
    @62
    cc0
    @69
    @17
    @26
    @61
    @21
    @56
    cT
    fveq2
    fveq1d
    neeq1d
    raleqbidv
    imbi12d
    @21
    cF
    wceq
    #
    @25
    @13
    @31
    @20
    @70
    @22
    @12
    @24
    @5
    @21
    cF
    c0
    neeq1
    @70
    @23
    @4
    cc0
    cc0
    @21
    cF
    fveq1
    neeq1d
    anbi12d
    @70
    @28
    @19
    vm
    @30
    @8
    @70
    @29
    @7
    cc0
    cfzo
    @21
    cF
    chash
    fveq2
    oveq2d
    @70
    @27
    @18
    cc0
    @70
    @17
    @26
    @14
    @21
    cF
    cT
    fveq2
    fveq1d
    neeq1d
    raleqbidv
    imbi12d
    @35
    @41
    @32
    @34
    c0
    neirr
    intnanr
    pm2.21i
    @42
    @0
    wcel
    #
    @54
    cr
    wcel
    #
    wa
    #
    @53
    @60
    @66
    @73
    @53
    wa
    @73
    @46
    vn
    cv
    #
    @47
    cfv
    #
    cc0
    wne
    #
    vn
    @51
    wral
    #
    wi
    #
    wa
    #
    @60
    @66
    @78
    @53
    @73
    @77
    @52
    @46
    @76
    @49
    vn
    vm
    @51
    @74
    @17
    wceq
    @75
    @48
    cc0
    @74
    @17
    @47
    fveq2
    neeq1d
    #
    cbvralv
    imbi2i
    anbi2i
    @79
    @60
    wa
    #
    @63
    vm
    @65
    @81
    @17
    @65
    wcel
    #
    wa
    #
    @17
    @51
    wcel
    #
    @63
    @17
    @50
    wceq
    #
    @83
    @84
    wa
    #
    @63
    @42
    c0
    @86
    @42
    c0
    wceq
    #
    wa
    @84
    @63
    @83
    @84
    @87
    simplr
    @87
    @84
    wn
    @86
    @87
    @84
    @17
    c0
    wcel
    @17
    noel
    @87
    @51
    c0
    @17
    @87
    @51
    cc0
    cc0
    cfzo
    co
    c0
    @87
    @50
    cc0
    cc0
    cfzo
    @87
    @50
    @39
    cc0
    @42
    c0
    chash
    fveq2
    hash0
    syl6eq
    #
    oveq2d
    cc0
    fzo0
    syl6eq
    eleq2d
    mtbiri
    adantl
    pm2.21dd
    @86
    @43
    wa
    #
    @62
    @48
    cc0
    @89
    @71
    @72
    @84
    @62
    @48
    wceq
    @71
    @72
    @78
    @60
    @82
    @84
    @43
    simp-6l
    @71
    @72
    @78
    @60
    @82
    @84
    @43
    simp-6r
    @83
    @84
    @43
    simplr
    #
    c.pd
    cT
    vf
    vi
    vj
    vn
    @42
    @54
    @17
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstfvp
    syl3anc
    @89
    @84
    @77
    @49
    @90
    @89
    @43
    @45
    @77
    @86
    @43
    simpr
    #
    @89
    @73
    @43
    @59
    @45
    @83
    @73
    @84
    @43
    @73
    @78
    @60
    @82
    simplll
    #
    ad2antrr
    @91
    @81
    @82
    @84
    @43
    @59
    @79
    @57
    @59
    @82
    @84
    @43
    w3a
    simplrr
    3anassrs
    @73
    @43
    wa
    #
    @59
    @45
    @93
    @58
    @44
    cc0
    @93
    @71
    @55
    @0
    wcel
    #
    cc0
    @51
    wcel
    #
    @58
    @44
    wceq
    @71
    @72
    @43
    simpll
    @93
    @54
    cr
    @71
    @72
    @43
    simplr
    s1cld
    @93
    @50
    cn
    wcel
    #
    @50
    c1
    cmin
    co
    #
    @51
    wcel
    #
    @95
    @71
    @43
    @96
    @72
    cr
    @42
    lennncl
    #
    adantlr
    @50
    fzo0end
    #
    @97
    cc0
    @50
    elfzolt3b
    3syl
    cr
    @42
    @55
    cc0
    ccatval1
    syl3anc
    neeq1d
    biimpa
    #
    syl21anc
    @73
    @78
    @60
    @82
    @84
    @43
    simp-5r
    mp2and
    @76
    @49
    vn
    @17
    @51
    @80
    rspcva
    syl2anc
    eqnetrd
    pm2.61dane
    @83
    @85
    wa
    #
    @62
    @50
    @61
    cfv
    #
    cc0
    @102
    @17
    @50
    @61
    @83
    @85
    simpr
    fveq2d
    @83
    @103
    cc0
    wne
    #
    @85
    @79
    @60
    @82
    @104
    @79
    @60
    @82
    wa
    #
    wa
    #
    @87
    @104
    @106
    @87
    wa
    #
    @87
    @72
    @59
    @104
    @106
    @87
    simpr
    @71
    @72
    @78
    @105
    @87
    simp-4r
    @107
    @57
    @59
    @79
    @60
    @82
    @87
    simplrl
    simprd
    @87
    @72
    wa
    #
    @59
    wa
    #
    @103
    @54
    csgn
    cfv
    #
    cc0
    @109
    @103
    cc0
    @110
    cs1
    #
    cfv
    #
    @110
    @109
    @50
    cc0
    @61
    @111
    @109
    @61
    @55
    cT
    cfv
    #
    @111
    @108
    @61
    @113
    wceq
    @59
    @108
    @56
    @55
    cT
    @87
    @72
    @56
    c0
    @55
    cconcat
    co
    #
    @55
    @42
    c0
    @55
    cconcat
    oveq1
    @72
    @94
    @114
    @55
    wceq
    @54
    cr
    s1cl
    cr
    @55
    ccatlid
    syl
    sylan9eq
    #
    fveq2d
    adantr
    @109
    @72
    @113
    @111
    wceq
    @87
    @72
    @59
    simplr
    #
    c.pd
    cT
    vf
    vi
    vj
    vn
    @54
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstf0
    syl
    eqtrd
    @87
    @50
    cc0
    wceq
    @72
    @59
    @88
    ad2antrr
    fveq12d
    @109
    @72
    @110
    cr
    wcel
    @112
    @110
    wceq
    @116
    @54
    sgnclre
    @110
    cr
    s1fv
    3syl
    eqtrd
    @109
    @72
    @54
    cc0
    wne
    #
    @110
    cc0
    wne
    #
    @116
    @108
    @59
    @117
    @108
    @58
    @54
    cc0
    @108
    @58
    cc0
    @55
    cfv
    #
    @54
    @108
    cc0
    @56
    @55
    @115
    fveq1d
    @72
    @119
    @54
    wceq
    @87
    @54
    cr
    s1fv
    adantl
    eqtrd
    neeq1d
    biimpa
    @72
    @118
    @117
    @72
    @110
    cc0
    @54
    cc0
    @72
    @54
    cxr
    wcel
    #
    @110
    cc0
    wceq
    @54
    cc0
    wceq
    wb
    @54
    rexr
    @54
    sgn0bi
    syl
    necon3bid
    biimpar
    syl2anc
    eqnetrd
    syl21anc
    @106
    @87
    wn
    #
    wa
    #
    @103
    @97
    @47
    cfv
    #
    @110
    c.pd
    co
    #
    cc0
    @73
    @105
    @121
    @103
    @124
    wceq
    #
    @78
    @73
    @105
    wa
    #
    @121
    wa
    #
    @42
    @2
    wcel
    @72
    @125
    @127
    @42
    @0
    @1
    @71
    @72
    @105
    @121
    simplll
    #
    @127
    @87
    @42
    @1
    wcel
    @126
    @121
    simpr
    #
    ve
    c0
    velsn
    sylnibr
    eldifd
    @71
    @72
    @105
    @121
    simpllr
    #
    c.pd
    cT
    vf
    vi
    vj
    vn
    @42
    @54
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstfvn
    syl2anc
    adantllr
    @122
    @123
    c1
    cneg
    cc0
    c1
    ctp
    #
    wcel
    #
    @110
    @131
    wcel
    #
    @123
    cc0
    wne
    #
    @124
    cc0
    wne
    @73
    @105
    @121
    @132
    @78
    @127
    @71
    @98
    @132
    @128
    @127
    @96
    @98
    @127
    @71
    @43
    @96
    @128
    @127
    @42
    c0
    @129
    neqned
    #
    @99
    syl2anc
    @100
    syl
    #
    c.pd
    cT
    vf
    vi
    vj
    vn
    @42
    @97
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstcl
    syl2anc
    adantllr
    @73
    @105
    @121
    @133
    @78
    @127
    @120
    @133
    @127
    @54
    @130
    rexrd
    @54
    sgncl
    syl
    adantllr
    @122
    @98
    @77
    @134
    @73
    @105
    @121
    @98
    @78
    @136
    adantllr
    @122
    @43
    @45
    @77
    @73
    @105
    @121
    @43
    @78
    @135
    adantllr
    #
    @122
    @73
    @43
    @59
    @45
    @73
    @78
    @105
    @121
    simplll
    @137
    @122
    @57
    @59
    @79
    @60
    @82
    @121
    simplrl
    simprd
    @101
    syl21anc
    @73
    @78
    @105
    @121
    simpllr
    mp2and
    @76
    @134
    vn
    @97
    @51
    @74
    @97
    wceq
    @75
    @123
    cc0
    @74
    @97
    @47
    fveq2
    neeq1d
    rspcva
    syl2anc
    c.pd
    cW
    @123
    @110
    va
    vb
    signsv.p
    signsv.w
    signswn0
    syl21anc
    eqnetrd
    pm2.61dan
    anassrs
    adantr
    eqnetrd
    @83
    @50
    cc0
    cuz
    cfv
    #
    wcel
    #
    @17
    cc0
    @50
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @84
    @85
    wo
    #
    @71
    @139
    @72
    @78
    @60
    @82
    @71
    @50
    cn0
    @138
    cr
    @42
    lencl
    nn0uz
    syl6eleq
    ad4antr
    @83
    @73
    @82
    @142
    @92
    @81
    @82
    simpr
    @73
    @82
    @142
    @73
    @65
    @141
    @17
    @73
    @64
    @140
    cc0
    cfzo
    @71
    @64
    @140
    wceq
    @72
    cr
    @42
    @54
    ccatws1len
    adantr
    oveq2d
    eleq2d
    biimpa
    syl2anc
    @139
    @142
    @143
    cc0
    @50
    @17
    fzosplitsni
    biimpa
    syl2anc
    mpjaodan
    ralrimiva
    sylanbr
    exp31
    wrdind
    imp
    adantrr
    @19
    @16
    vm
    cN
    @8
    @17
    cN
    wceq
    @18
    @15
    cc0
    @17
    cN
    @14
    fveq2
    neeq1d
    rspcva
    syl2anc
    syl12anc
end
