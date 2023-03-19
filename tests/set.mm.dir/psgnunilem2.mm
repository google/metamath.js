include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cgsu.mm"
include "chash.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "wcel.mm"
include "cdif.mm"
include "cdm.mm"
include "wn.mm"
include "wral.mm"
include "w3a.mm"
include "cword.mm"
include "wrex.mm"
include "c2.mm"
include "cmin.mm"
include "c0.mm"
include "cotp.mm"
include "csplice.mm"
include "wrd0.mm"
include "splcl.mm"
include "sylancl.mm"
include "adantr.mm"
include "cneg.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "cfz.mm"
include "fzossfz.mm"
include "sseldi.mm"
include "elfznn0.mm"
include "syl.mm"
include "2nn0.mm"
include "nn0addcl.mm"
include "cr.mm"
include "nn0red.mm"
include "nn0addge1.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "psgnunilem5.mm"
include "fzofzp1.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "addassd.mm"
include "df-2.mm"
include "oveq2i.mm"
include "syl6reqr.mm"
include "oveq2d.mm"
include "3eltr4d.mm"
include "a1i.mm"
include "spllen.mm"
include "hash0.mm"
include "oveq1i.mm"
include "df-neg.mm"
include "eqtr4i.mm"
include "cc.mm"
include "2cn.mm"
include "pncan2.mm"
include "negeqd.mm"
include "syl5eq.mm"
include "oveq12d.mm"
include "cz.mm"
include "elfzel2.mm"
include "zcnd.mm"
include "negsub.mm"
include "3eqtrd.mm"
include "cop.mm"
include "csubstr.mm"
include "splid.mm"
include "syl12anc.mm"
include "cbs.mm"
include "eqid.mm"
include "cmnd.mm"
include "cgrp.mm"
include "symggrp.mm"
include "grpmnd.mm"
include "wss.mm"
include "symgtrf.mm"
include "sswrd.mm"
include "ax-mp.mm"
include "swrdcl.mm"
include "cs2.mm"
include "cplusg.mm"
include "eleqtrrd.mm"
include "swrds2.mm"
include "syl3anc.mm"
include "wf.mm"
include "wrdf.mm"
include "feq2d.mm"
include "mpbid.mm"
include "ffvelrnd.mm"
include "gsumws2.mm"
include "symgov.mm"
include "syl2anc.mm"
include "simpr.mm"
include "c0g.mm"
include "symgid.mm"
include "gsum0.mm"
include "syl6eqr.mm"
include "gsumspl.mm"
include "3eqtr3d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "pm2.21dd.mm"
include "ex.mm"
include "simprl.mm"
include "simprr.mm"
include "s2cld.mm"
include "adantrr.mm"
include "simprr1.mm"
include "sselda.mm"
include "adantrl.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "s2len.mm"
include "subidi.mm"
include "syl6eq.mm"
include "eqeltrd.mm"
include "addid1d.mm"
include "jca.mm"
include "simprr2.mm"
include "cn.mm"
include "clt.mm"
include "1nn0.mm"
include "2nn.mm"
include "1lt2.mm"
include "elfzo0.mm"
include "mpbir3an.mm"
include "eleqtrri.mm"
include "splfv2a.mm"
include "s2fv1.mm"
include "ad2antll.mm"
include "difeq1d.mm"
include "dmeqd.mm"
include "wo.mm"
include "wb.mm"
include "cuz.mm"
include "fzosplitsni.mm"
include "nn0uz.mm"
include "eleq2s.mm"
include "wi.mm"
include "eleq2d.mm"
include "notbid.mm"
include "rspccva.mm"
include "sylan.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "splfv1.mm"
include "neleqtrrd.mm"
include "simprr3.mm"
include "0nn0.mm"
include "2pos.mm"
include "fveq2d.mm"
include "s2fv0.mm"
include "ad2antrl.mm"
include "mtbird.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "3jca.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "3anbi23d.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "psgnunilem1.mm"
include "mpjaod.mm"

theorem psgnunilem2
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cD: class D
  let cT: class T
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cI: class I
  let cL: class L
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vs: setvar s
  assume psgnunilem2.g: |- G = ( SymGrp ` D )
  assume psgnunilem2.t: |- T = ran ( pmTrsp ` D )
  assume psgnunilem2.d: |- ( ph -> D e. V )
  assume psgnunilem2.w: |- ( ph -> W e. Word T )
  assume psgnunilem2.id: |- ( ph -> ( G gsum W ) = ( _I |` D ) )
  assume psgnunilem2.l: |- ( ph -> ( # ` W ) = L )
  assume psgnunilem2.ix: |- ( ph -> I e. ( 0 ..^ L ) )
  assume psgnunilem2.a: |- ( ph -> A e. dom ( ( W ` I ) \ _I ) )
  assume psgnunilem2.al: |- ( ph -> A. k e. ( 0 ..^ I ) -. A e. dom ( ( W ` k ) \ _I ) )
  assume psgnunilem2.in: |- ( ph -> -. E. x e. Word T ( ( # ` x ) = ( L - 2 ) /\ ( G gsum x ) = ( _I |` D ) ) )

  disjoint j k
  disjoint j w
  disjoint A j
  disjoint k w
  disjoint A k
  disjoint A w
  disjoint j x
  disjoint D j
  disjoint w x
  disjoint D w
  disjoint D x
  disjoint j ph
  disjoint G j
  disjoint k x
  disjoint G k
  disjoint G w
  disjoint G x
  disjoint I j
  disjoint I k
  disjoint I w
  disjoint I x
  disjoint T j
  disjoint T w
  disjoint T x
  disjoint W j
  disjoint W k
  disjoint W w
  disjoint W x
  disjoint L w
  disjoint L x
  disjoint j r
  disjoint j s
  disjoint k r
  disjoint k s
  disjoint r s
  disjoint r w
  disjoint A r
  disjoint s w
  disjoint A s
  disjoint r x
  disjoint D r
  disjoint s x
  disjoint D s
  disjoint ph r
  disjoint ph s
  disjoint G r
  disjoint G s
  disjoint I r
  disjoint I s
  disjoint T r
  disjoint T s
  disjoint W r
  disjoint W s
  disjoint L r
  disjoint L s
  assert |- ( ph -> E. w e. Word T ( ( ( G gsum w ) = ( _I |` D ) /\ ( # ` w ) = L ) /\ ( ( I + 1 ) e. ( 0 ..^ L ) /\ A e. dom ( ( w ` ( I + 1 ) ) \ _I ) /\ A. j e. ( 0 ..^ ( I + 1 ) ) -. A e. dom ( ( w ` j ) \ _I ) ) ) )

  proof
    wph
    cI
    cW
    cfv
    #
    cI
    c1
    caddc
    co
    #
    cW
    cfv
    #
    ccom
    #
    cid
    cD
    cres
    #
    wceq
    #
    cG
    vw
    cv
    #
    cgsu
    co
    #
    @4
    wceq
    #
    @6
    chash
    cfv
    #
    cL
    wceq
    #
    wa
    #
    @1
    cc0
    cL
    cfzo
    co
    #
    wcel
    #
    cA
    @1
    @6
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    cA
    vj
    cv
    #
    @6
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    vj
    cc0
    @1
    cfzo
    co
    #
    wral
    #
    w3a
    #
    wa
    #
    vw
    cT
    cword
    #
    wrex
    #
    @3
    vr
    cv
    #
    vs
    cv
    #
    ccom
    #
    wceq
    #
    cA
    @31
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    cA
    @30
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    w3a
    #
    vs
    cT
    wrex
    vr
    cT
    wrex
    wph
    @5
    @29
    wph
    @5
    wa
    #
    vx
    cv
    #
    chash
    cfv
    #
    cL
    c2
    cmin
    co
    #
    wceq
    #
    cG
    @43
    cgsu
    co
    #
    @4
    wceq
    #
    wa
    #
    vx
    @28
    wrex
    #
    @29
    @42
    cW
    cI
    cI
    c2
    caddc
    co
    #
    c0
    cotp
    csplice
    co
    #
    @28
    wcel
    #
    @52
    chash
    cfv
    #
    @45
    wceq
    #
    cG
    @52
    cgsu
    co
    #
    @4
    wceq
    #
    @50
    wph
    @53
    @5
    wph
    cW
    @28
    wcel
    #
    c0
    @28
    wcel
    #
    @53
    psgnunilem2.w
    cT
    wrd0
    #
    cT
    c0
    cW
    @51
    cI
    splcl
    sylancl
    adantr
    wph
    @55
    @5
    wph
    @54
    cW
    chash
    cfv
    #
    c0
    chash
    cfv
    #
    @51
    cI
    cmin
    co
    #
    cmin
    co
    #
    caddc
    co
    cL
    c2
    cneg
    #
    caddc
    co
    #
    @45
    wph
    cT
    c0
    cW
    @51
    cI
    psgnunilem2.w
    wph
    cI
    cn0
    wcel
    #
    @51
    cn0
    wcel
    #
    cI
    @51
    cle
    wbr
    #
    cI
    cc0
    @51
    cfz
    co
    wcel
    #
    wph
    cI
    cc0
    cL
    cfz
    co
    #
    wcel
    #
    @67
    wph
    @12
    @71
    cI
    cc0
    cL
    fzossfz
    psgnunilem2.ix
    sseldi
    #
    cI
    cL
    elfznn0
    syl
    #
    wph
    @67
    c2
    cn0
    wcel
    #
    @68
    @74
    2nn0
    cI
    c2
    nn0addcl
    sylancl
    wph
    cI
    cr
    wcel
    @75
    @69
    wph
    cI
    @74
    nn0red
    2nn0
    cI
    c2
    nn0addge1
    sylancl
    cI
    @51
    elfz2nn0
    syl3anbrc
    #
    wph
    @1
    c1
    caddc
    co
    #
    @71
    @51
    cc0
    @61
    cfz
    co
    #
    wph
    @13
    @77
    @71
    wcel
    wph
    cA
    cD
    cT
    vk
    cG
    cI
    cL
    cV
    cW
    psgnunilem2.g
    psgnunilem2.t
    psgnunilem2.d
    psgnunilem2.w
    psgnunilem2.id
    psgnunilem2.l
    psgnunilem2.ix
    psgnunilem2.a
    psgnunilem2.al
    psgnunilem5
    #
    cc0
    cL
    @1
    fzofzp1
    syl
    wph
    @77
    cI
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @51
    wph
    cI
    c1
    c1
    wph
    cI
    @74
    nn0cnd
    #
    wph
    1cnd
    #
    @82
    addassd
    c2
    @80
    cI
    caddc
    df-2
    oveq2i
    syl6reqr
    wph
    @61
    cL
    cc0
    cfz
    psgnunilem2.l
    oveq2d
    3eltr4d
    #
    @59
    wph
    @60
    a1i
    spllen
    wph
    @61
    cL
    @64
    @65
    caddc
    psgnunilem2.l
    wph
    @64
    @63
    cneg
    #
    @65
    @64
    cc0
    @63
    cmin
    co
    @84
    @62
    cc0
    @63
    cmin
    hash0
    oveq1i
    @63
    df-neg
    eqtr4i
    wph
    @63
    c2
    wph
    cI
    cc
    wcel
    c2
    cc
    wcel
    #
    @63
    c2
    wceq
    @81
    2cn
    cI
    c2
    pncan2
    sylancl
    #
    negeqd
    syl5eq
    oveq12d
    wph
    cL
    cc
    wcel
    @85
    @66
    @45
    wceq
    wph
    cL
    wph
    @72
    cL
    cz
    wcel
    @73
    cI
    cc0
    cL
    elfzel2
    syl
    zcnd
    #
    2cn
    cL
    c2
    negsub
    sylancl
    3eqtrd
    adantr
    @42
    cG
    cW
    cI
    @51
    cW
    cI
    @51
    cop
    csubstr
    co
    #
    cotp
    csplice
    co
    #
    cgsu
    co
    #
    cG
    cW
    cgsu
    co
    #
    @56
    @4
    wph
    @90
    @91
    wceq
    #
    @5
    wph
    @89
    cW
    cG
    cgsu
    wph
    @58
    @70
    @51
    @78
    wcel
    #
    @89
    cW
    wceq
    psgnunilem2.w
    @76
    @83
    cT
    cW
    cI
    @51
    splid
    syl12anc
    oveq2d
    #
    adantr
    @42
    cG
    cbs
    cfv
    #
    cW
    @51
    cI
    cG
    @88
    c0
    @95
    eqid
    #
    wph
    cG
    cmnd
    wcel
    #
    @5
    wph
    cG
    cgrp
    wcel
    #
    @97
    wph
    cD
    cV
    wcel
    #
    @98
    psgnunilem2.d
    cD
    cG
    cV
    psgnunilem2.g
    symggrp
    syl
    cG
    grpmnd
    syl
    #
    adantr
    wph
    cW
    @95
    cword
    #
    wcel
    #
    @5
    wph
    @28
    @101
    cW
    cT
    @95
    wss
    #
    @28
    @101
    wss
    @95
    cD
    cT
    cG
    psgnunilem2.t
    psgnunilem2.g
    @96
    symgtrf
    #
    cT
    @95
    sswrd
    ax-mp
    #
    psgnunilem2.w
    sseldi
    #
    adantr
    wph
    @70
    @5
    @76
    adantr
    wph
    @93
    @5
    @83
    adantr
    wph
    @88
    @101
    wcel
    #
    @5
    wph
    @102
    @107
    @106
    @95
    cW
    cI
    @51
    swrdcl
    syl
    #
    adantr
    c0
    @101
    wcel
    @42
    @95
    wrd0
    a1i
    @42
    cG
    @88
    cgsu
    co
    #
    @3
    @4
    cG
    c0
    cgsu
    co
    #
    wph
    @109
    @3
    wceq
    #
    @5
    wph
    @109
    cG
    @0
    @2
    cs2
    #
    cgsu
    co
    #
    @0
    @2
    cG
    cplusg
    cfv
    #
    co
    #
    @3
    wph
    @88
    @112
    cG
    cgsu
    wph
    @58
    @67
    @1
    cc0
    @61
    cfzo
    co
    #
    wcel
    @88
    @112
    wceq
    psgnunilem2.w
    @74
    wph
    @1
    @12
    @116
    @79
    wph
    @61
    cL
    cc0
    cfzo
    psgnunilem2.l
    oveq2d
    #
    eleqtrrd
    cT
    cI
    cW
    swrds2
    syl3anc
    oveq2d
    wph
    @97
    @0
    @95
    wcel
    #
    @2
    @95
    wcel
    #
    @113
    @115
    wceq
    @100
    wph
    cT
    @95
    @0
    @104
    wph
    @12
    cT
    cI
    cW
    wph
    @116
    cT
    cW
    wf
    #
    @12
    cT
    cW
    wf
    wph
    @58
    @120
    psgnunilem2.w
    cT
    cW
    wrdf
    syl
    wph
    @116
    @12
    cT
    cW
    @117
    feq2d
    mpbid
    #
    psgnunilem2.ix
    ffvelrnd
    #
    sseldi
    #
    wph
    cT
    @95
    @2
    @104
    wph
    @12
    cT
    @1
    cW
    @121
    @79
    ffvelrnd
    #
    sseldi
    #
    @95
    @114
    @0
    @2
    cG
    @96
    @114
    eqid
    #
    gsumws2
    syl3anc
    wph
    @118
    @119
    @115
    @3
    wceq
    @123
    @125
    cD
    @95
    @114
    cG
    @0
    @2
    psgnunilem2.g
    @96
    @126
    symgov
    syl2anc
    3eqtrd
    #
    adantr
    wph
    @5
    simpr
    wph
    @4
    @110
    wceq
    @5
    wph
    @4
    cG
    c0g
    cfv
    #
    @110
    wph
    @99
    @4
    @128
    wceq
    psgnunilem2.d
    cD
    cG
    cV
    psgnunilem2.g
    symgid
    syl
    cG
    @128
    @128
    eqid
    gsum0
    syl6eqr
    adantr
    3eqtrd
    gsumspl
    wph
    @91
    @4
    wceq
    #
    @5
    psgnunilem2.id
    adantr
    3eqtr3d
    @49
    @55
    @57
    wa
    vx
    @52
    @28
    @43
    @52
    wceq
    #
    @46
    @55
    @48
    @57
    @130
    @44
    @54
    @45
    @43
    @52
    chash
    fveq2
    eqeq1d
    @130
    @47
    @56
    @4
    @43
    @52
    cG
    cgsu
    oveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    wph
    @50
    wn
    @5
    psgnunilem2.in
    adantr
    pm2.21dd
    ex
    wph
    @41
    @29
    vr
    vs
    cT
    cT
    wph
    @30
    cT
    wcel
    #
    @31
    cT
    wcel
    #
    wa
    #
    @41
    @29
    wph
    @133
    @41
    wa
    #
    wa
    #
    cW
    cI
    @51
    @30
    @31
    cs2
    #
    cotp
    csplice
    co
    #
    @28
    wcel
    #
    cG
    @137
    cgsu
    co
    #
    @4
    wceq
    #
    @137
    chash
    cfv
    #
    cL
    wceq
    #
    wa
    #
    @13
    cA
    @1
    @137
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    cA
    @18
    @137
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    vj
    @24
    wral
    #
    w3a
    #
    @29
    wph
    @133
    @138
    @41
    wph
    @133
    wa
    #
    @58
    @136
    @28
    wcel
    #
    @138
    wph
    @58
    @133
    psgnunilem2.w
    adantr
    #
    @155
    @30
    @31
    cT
    wph
    @131
    @132
    simprl
    wph
    @131
    @132
    simprr
    s2cld
    #
    cT
    @136
    cW
    @51
    cI
    splcl
    syl2anc
    adantrr
    @135
    @140
    @142
    @135
    @139
    @90
    @91
    @4
    @135
    @95
    cW
    @51
    cI
    cG
    @136
    @88
    @96
    wph
    @97
    @134
    @100
    adantr
    wph
    @102
    @134
    @106
    adantr
    wph
    @70
    @134
    @76
    adantr
    wph
    @93
    @134
    @83
    adantr
    wph
    @133
    @136
    @101
    wcel
    @41
    @155
    @28
    @101
    @136
    @105
    @158
    sseldi
    adantrr
    wph
    @107
    @134
    @108
    adantr
    @135
    @3
    @32
    @109
    cG
    @136
    cgsu
    co
    #
    @33
    @36
    @40
    @133
    wph
    simprr1
    wph
    @111
    @134
    @127
    adantr
    wph
    @133
    @159
    @32
    wceq
    @41
    @155
    @159
    @30
    @31
    @114
    co
    #
    @32
    @155
    @97
    @30
    @95
    wcel
    #
    @31
    @95
    wcel
    #
    @159
    @160
    wceq
    wph
    @97
    @133
    @100
    adantr
    wph
    @131
    @161
    @132
    wph
    cT
    @95
    @30
    @103
    wph
    @104
    a1i
    #
    sselda
    adantrr
    #
    wph
    @132
    @162
    @131
    wph
    cT
    @95
    @31
    @163
    sselda
    adantrl
    #
    @95
    @114
    @30
    @31
    cG
    @96
    @126
    gsumws2
    syl3anc
    @155
    @161
    @162
    @160
    @32
    wceq
    @164
    @165
    cD
    @95
    @114
    cG
    @30
    @31
    psgnunilem2.g
    @96
    @126
    symgov
    syl2anc
    eqtrd
    adantrr
    3eqtr4rd
    gsumspl
    wph
    @92
    @134
    @94
    adantr
    wph
    @129
    @134
    psgnunilem2.id
    adantr
    3eqtrd
    wph
    @133
    @142
    @41
    @155
    @141
    @61
    @136
    chash
    cfv
    #
    @63
    cmin
    co
    #
    caddc
    co
    #
    cL
    @155
    cT
    @136
    cW
    @51
    cI
    @157
    wph
    @70
    @133
    @76
    adantr
    #
    wph
    @93
    @133
    @83
    adantr
    #
    @158
    spllen
    wph
    @168
    cL
    wceq
    @133
    wph
    @168
    @61
    cc0
    caddc
    co
    @61
    cL
    wph
    @167
    cc0
    @61
    caddc
    wph
    @167
    c2
    @63
    cmin
    co
    #
    cc0
    @166
    c2
    @63
    cmin
    @30
    @31
    s2len
    #
    oveq1i
    wph
    @171
    c2
    c2
    cmin
    co
    cc0
    wph
    @63
    c2
    c2
    cmin
    @86
    oveq2d
    c2
    2cn
    subidi
    syl6eq
    syl5eq
    oveq2d
    wph
    @61
    wph
    @61
    cL
    cc
    psgnunilem2.l
    @87
    eqeltrd
    addid1d
    psgnunilem2.l
    3eqtrd
    adantr
    eqtrd
    adantrr
    jca
    @135
    @13
    @147
    @153
    wph
    @13
    @134
    @79
    adantr
    @135
    cA
    @35
    @146
    @33
    @36
    @40
    @133
    wph
    simprr2
    @135
    @145
    @34
    @135
    @144
    @31
    cid
    wph
    @133
    @144
    @31
    wceq
    @41
    @155
    @144
    c1
    @136
    cfv
    #
    @31
    @155
    cT
    @136
    cW
    @51
    cI
    c1
    @157
    @169
    @170
    @158
    c1
    cc0
    @166
    cfzo
    co
    #
    wcel
    @155
    c1
    cc0
    c2
    cfzo
    co
    #
    @174
    c1
    @175
    wcel
    c1
    cn0
    wcel
    c2
    cn
    wcel
    #
    c1
    c2
    clt
    wbr
    1nn0
    2nn
    1lt2
    c1
    c2
    elfzo0
    mpbir3an
    @166
    c2
    cc0
    cfzo
    @172
    oveq2i
    #
    eleqtrri
    a1i
    splfv2a
    @132
    @173
    @31
    wceq
    wph
    @131
    @30
    @31
    cT
    s2fv1
    ad2antll
    eqtrd
    adantrr
    difeq1d
    dmeqd
    eleqtrrd
    @135
    @152
    vj
    @24
    @135
    @18
    @24
    wcel
    #
    @18
    cc0
    cI
    cfzo
    co
    #
    wcel
    #
    @18
    cI
    wceq
    #
    wo
    #
    @152
    wph
    @178
    @182
    wb
    #
    @134
    wph
    @67
    @183
    @74
    @183
    cI
    cc0
    cuz
    cfv
    cn0
    cc0
    cI
    @18
    fzosplitsni
    nn0uz
    eleq2s
    syl
    adantr
    @135
    @180
    @152
    @181
    wph
    @133
    @180
    @152
    wi
    @41
    @155
    @180
    @152
    @155
    @180
    wa
    #
    @150
    @18
    cW
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    cA
    wph
    @180
    cA
    @187
    wcel
    #
    wn
    #
    @133
    wph
    cA
    vk
    cv
    #
    cW
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    vk
    @179
    wral
    @180
    @189
    psgnunilem2.al
    @195
    @189
    vk
    @18
    @179
    @190
    @18
    wceq
    #
    @194
    @188
    @196
    @193
    @187
    cA
    @196
    @192
    @186
    @196
    @191
    @185
    cid
    @190
    @18
    cW
    fveq2
    difeq1d
    dmeqd
    eleq2d
    notbid
    rspccva
    sylan
    adantlr
    @184
    @149
    @186
    @184
    @148
    @185
    cid
    @184
    cT
    @136
    cW
    @51
    cI
    @18
    wph
    @58
    @133
    @180
    psgnunilem2.w
    ad2antrr
    wph
    @70
    @133
    @180
    @76
    ad2antrr
    wph
    @93
    @133
    @180
    @83
    ad2antrr
    @155
    @156
    @180
    @158
    adantr
    @155
    @180
    simpr
    splfv1
    difeq1d
    dmeqd
    neleqtrrd
    ex
    adantrr
    @135
    @152
    @181
    cA
    cI
    @137
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    @135
    @200
    @39
    @33
    @36
    @40
    @133
    wph
    simprr3
    wph
    @133
    @200
    @39
    wb
    @41
    @155
    @199
    @38
    cA
    @155
    @198
    @37
    @155
    @197
    @30
    cid
    @155
    cI
    cc0
    caddc
    co
    #
    @137
    cfv
    cc0
    @136
    cfv
    #
    @197
    @30
    @155
    cT
    @136
    cW
    @51
    cI
    cc0
    @157
    @169
    @170
    @158
    cc0
    @174
    wcel
    @155
    cc0
    @175
    @174
    cc0
    @175
    wcel
    cc0
    cn0
    wcel
    @176
    cc0
    c2
    clt
    wbr
    0nn0
    2nn
    2pos
    cc0
    c2
    elfzo0
    mpbir3an
    @177
    eleqtrri
    a1i
    splfv2a
    @155
    @201
    cI
    @137
    wph
    @201
    cI
    wceq
    @133
    wph
    cI
    @81
    addid1d
    adantr
    fveq2d
    @131
    @202
    @30
    wceq
    wph
    @132
    @30
    @31
    cT
    s2fv0
    ad2antrl
    3eqtr3d
    difeq1d
    dmeqd
    eleq2d
    adantrr
    mtbird
    @181
    @151
    @200
    @181
    @150
    @199
    cA
    @181
    @149
    @198
    @181
    @148
    @197
    cid
    @18
    cI
    @137
    fveq2
    difeq1d
    dmeqd
    eleq2d
    notbid
    syl5ibrcom
    jaod
    sylbid
    ralrimiv
    3jca
    @27
    @143
    @154
    wa
    vw
    @137
    @28
    @6
    @137
    wceq
    #
    @11
    @143
    @26
    @154
    @203
    @8
    @140
    @10
    @142
    @203
    @7
    @139
    @4
    @6
    @137
    cG
    cgsu
    oveq2
    eqeq1d
    @203
    @9
    @141
    cL
    @6
    @137
    chash
    fveq2
    eqeq1d
    anbi12d
    @203
    @17
    @147
    @25
    @153
    @13
    @203
    @16
    @146
    cA
    @203
    @15
    @145
    @203
    @14
    @144
    cid
    @1
    @6
    @137
    fveq1
    difeq1d
    dmeqd
    eleq2d
    @203
    @23
    @152
    vj
    @24
    @203
    @22
    @151
    @203
    @21
    @150
    cA
    @203
    @20
    @149
    @203
    @19
    @148
    cid
    @18
    @6
    @137
    fveq1
    difeq1d
    dmeqd
    eleq2d
    notbid
    ralbidv
    3anbi23d
    anbi12d
    rspcev
    syl12anc
    expr
    rexlimdvva
    wph
    cA
    cD
    @0
    @2
    cT
    cV
    vs
    vr
    psgnunilem2.t
    psgnunilem2.d
    @122
    @124
    psgnunilem2.a
    psgnunilem1
    mpjaod
end
