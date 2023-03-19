include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cn.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "cn0.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cplusg.mm"
include "eqid.mm"
include "chfacfpmmulgsum2.mm"
include "wceq.mm"
include "cc.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "pncan1.mm"
include "syl.mm"
include "eqcomd.mm"
include "adantl.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "adantr.mm"
include "cbs.mm"
include "cabl.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "3adant3.mm"
include "pmatring.mm"
include "ringabl.mm"
include "cuz.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "ad2antrl.mm"
include "cmgp.mm"
include "cmgm.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "mndmgm.mm"
include "elfznn.mm"
include "mat2pmatbas.mm"
include "syl3an2.mm"
include "mgpbas.mm"
include "mulgnncl.mm"
include "syl3anc.mm"
include "simpl1.mm"
include "3ad2ant2.mm"
include "wf.mm"
include "elmapi.mm"
include "wi.mm"
include "cz.mm"
include "wb.mm"
include "nnz.mm"
include "peano2nn.mm"
include "nnzd.mm"
include "elfzm1b.mm"
include "syl2an.mm"
include "nncn.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "sylbid.mm"
include "expcom.mm"
include "com13.mm"
include "mpd.mm"
include "com12.mm"
include "imp.mm"
include "ffvelrnd.mm"
include "ringcl.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "telgsumfz.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "mulg1.mm"
include "1cnd.mm"
include "subidd.mm"
include "pncand.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "nnnn0.mm"
include "0elfz.mm"
include "simprl.mm"
include "peano2nnd.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "grpnpncan0.mm"
include "syl12anc.mm"
include "3eqtrd.mm"

theorem cayhamlem1
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.xp: class .X.
  let vi: setvar i
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let cK: class K
  let vk: setvar k
  let vx: setvar x
  assume cayhamlem1.a: |- A = ( N Mat R )
  assume cayhamlem1.b: |- B = ( Base ` A )
  assume cayhamlem1.p: |- P = ( Poly1 ` R )
  assume cayhamlem1.y: |- Y = ( N Mat P )
  assume cayhamlem1.r: |- .X. = ( .r ` Y )
  assume cayhamlem1.s: |- .- = ( -g ` Y )
  assume cayhamlem1.0: |- .0. = ( 0g ` Y )
  assume cayhamlem1.t: |- T = ( N matToPolyMat R )
  assume cayhamlem1.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume cayhamlem1.e: |- .^ = ( .g ` ( mulGrp ` Y ) )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
  disjoint .0. n
  disjoint B i
  disjoint G i
  disjoint M i
  disjoint N i
  disjoint R i
  disjoint T i
  disjoint .X. i
  disjoint .^ i
  disjoint i s
  disjoint b i
  disjoint T n
  disjoint i n
  disjoint Y i
  disjoint .X. n
  disjoint .- n
  disjoint .- i
  disjoint K n
  disjoint B k
  disjoint B x
  disjoint i k
  disjoint i x
  disjoint k x
  disjoint G k
  disjoint G x
  disjoint M k
  disjoint M x
  disjoint N k
  disjoint N x
  disjoint R k
  disjoint R x
  disjoint T k
  disjoint T x
  disjoint .X. k
  disjoint .X. x
  disjoint .^ k
  disjoint .^ x
  disjoint .0. k
  disjoint .0. x
  disjoint k s
  disjoint s x
  disjoint b k
  disjoint b x
  disjoint k n
  disjoint Y k
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> ( Y gsum ( i e. NN0 |-> ( ( i .^ ( T ` M ) ) .X. ( G ` i ) ) ) ) = .0. )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vs
    cv
    #
    cn
    wcel
    #
    vb
    cv
    #
    cB
    cc0
    @4
    cfz
    co
    #
    cmap
    co
    wcel
    #
    wa
    #
    wa
    #
    cY
    vi
    cn0
    vi
    cv
    #
    cM
    cT
    cfv
    #
    c.ex
    co
    #
    @11
    cG
    cfv
    c.xp
    co
    cmpt
    cgsu
    co
    cY
    vi
    c1
    @4
    cfz
    co
    #
    @13
    @11
    c1
    cmin
    co
    #
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    @11
    c1
    caddc
    co
    #
    @12
    c.ex
    co
    #
    @11
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @4
    c1
    caddc
    co
    #
    @12
    c.ex
    co
    #
    @4
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    @12
    cc0
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    c.mi
    co
    #
    cY
    cplusg
    cfv
    #
    co
    c1
    @12
    c.ex
    co
    #
    c1
    c1
    cmin
    co
    #
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    @28
    @27
    c1
    cmin
    co
    #
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    c.mi
    co
    #
    @35
    @36
    co
    #
    c.0
    cA
    cB
    cP
    @36
    cR
    cT
    c.xp
    vi
    vn
    c.ex
    cG
    cM
    c.mi
    cN
    cY
    c.0
    vs
    vb
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    cayhamlem1.r
    cayhamlem1.s
    cayhamlem1.0
    cayhamlem1.t
    cayhamlem1.g
    cayhamlem1.e
    @36
    eqid
    #
    chfacfpmmulgsum2
    @10
    @26
    @46
    @35
    @36
    @10
    @26
    cY
    vi
    @14
    @18
    @20
    @19
    c1
    cmin
    co
    #
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @46
    @3
    @26
    @55
    wceq
    @9
    @3
    @25
    @54
    cY
    cgsu
    @3
    vi
    @14
    @24
    @53
    @3
    @11
    @14
    wcel
    #
    wa
    #
    @23
    @52
    @18
    c.mi
    @57
    @22
    @51
    @20
    c.xp
    @57
    @21
    @50
    cT
    @57
    @11
    @49
    @6
    @56
    @11
    @49
    wceq
    @3
    @56
    @49
    @11
    @56
    @11
    cc
    wcel
    @49
    @11
    wceq
    @56
    @11
    @11
    c1
    @4
    elfzelz
    zcnd
    @11
    pncan1
    syl
    eqcomd
    adantl
    fveq2d
    fveq2d
    oveq2d
    oveq2d
    mpteq2dva
    oveq2d
    adantr
    @10
    vk
    cv
    #
    @12
    c.ex
    co
    #
    @58
    c1
    cmin
    co
    #
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    cY
    cbs
    cfv
    #
    @52
    @41
    vi
    vk
    @45
    cY
    @18
    c1
    c.mi
    @4
    @64
    eqid
    #
    @3
    cY
    cabl
    wcel
    #
    @9
    @3
    cY
    crg
    wcel
    #
    @66
    @3
    @0
    cR
    crg
    wcel
    #
    wa
    #
    @67
    @0
    @1
    @69
    @2
    @1
    @68
    @0
    cR
    crngring
    #
    anim2i
    #
    3adant3
    cY
    cP
    cR
    cN
    cayhamlem1.p
    cayhamlem1.y
    pmatring
    #
    syl
    #
    cY
    ringabl
    syl
    adantr
    cayhamlem1.s
    @5
    @4
    c1
    cuz
    cfv
    wcel
    #
    @3
    @8
    @5
    @74
    @4
    elnnuz
    biimpi
    ad2antrl
    @10
    @63
    @64
    wcel
    #
    vk
    c1
    @27
    cfz
    co
    #
    @10
    @58
    @76
    wcel
    #
    wa
    #
    @67
    @59
    @64
    wcel
    #
    @62
    @64
    wcel
    #
    @75
    @10
    @67
    @77
    @3
    @67
    @9
    @73
    adantr
    #
    adantr
    @78
    cY
    cmgp
    cfv
    #
    cmgm
    wcel
    #
    @58
    cn
    wcel
    #
    @12
    @64
    wcel
    #
    @79
    @78
    @82
    cmnd
    wcel
    #
    @83
    @10
    @86
    @77
    @3
    @86
    @9
    @3
    @67
    @86
    @0
    @1
    @67
    @2
    @0
    @1
    wa
    @69
    @67
    @71
    @72
    syl
    3adant3
    cY
    @82
    @82
    eqid
    #
    ringmgp
    syl
    adantr
    #
    adantr
    @82
    mndmgm
    #
    syl
    @77
    @84
    @10
    @58
    @27
    elfznn
    #
    adantl
    @10
    @85
    @77
    @3
    @85
    @9
    @1
    @0
    @68
    @2
    @85
    @70
    cA
    cB
    cY
    cP
    cR
    cT
    cM
    cN
    cayhamlem1.t
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    mat2pmatbas
    syl3an2
    #
    adantr
    #
    adantr
    @64
    c.ex
    @82
    @58
    @12
    @64
    cY
    @82
    @87
    @65
    mgpbas
    #
    cayhamlem1.e
    mulgnncl
    syl3anc
    @78
    @0
    @68
    @61
    cB
    wcel
    @80
    @10
    @0
    @77
    @0
    @1
    @2
    @9
    simpl1
    #
    adantr
    @10
    @68
    @77
    @3
    @68
    @9
    @1
    @0
    @68
    @2
    @70
    3ad2ant2
    adantr
    #
    adantr
    @78
    @7
    cB
    @60
    @6
    @10
    @7
    cB
    @6
    wf
    #
    @77
    @9
    @96
    @3
    @8
    @96
    @5
    @6
    cB
    @7
    elmapi
    adantl
    adantl
    #
    adantr
    @10
    @77
    @60
    @7
    wcel
    #
    @5
    @77
    @98
    wi
    #
    @3
    @8
    @77
    @5
    @98
    @77
    @84
    @5
    @98
    wi
    @90
    @5
    @84
    @77
    @98
    @84
    @5
    @99
    @84
    @5
    wa
    #
    @77
    @60
    cc0
    @42
    cfz
    co
    #
    wcel
    #
    @98
    @84
    @58
    cz
    wcel
    @27
    cz
    wcel
    @77
    @102
    wb
    @5
    @58
    nnz
    @5
    @27
    @4
    peano2nn
    nnzd
    @58
    @27
    elfzm1b
    syl2an
    @100
    @102
    @98
    @100
    @101
    @7
    @60
    @100
    @42
    @4
    cc0
    cfz
    @5
    @42
    @4
    wceq
    #
    @84
    @5
    @4
    cc
    wcel
    #
    @103
    @4
    nncn
    #
    @4
    pncan1
    syl
    adantl
    oveq2d
    eleq2d
    biimpd
    sylbid
    expcom
    com13
    mpd
    com12
    ad2antrl
    imp
    ffvelrnd
    cA
    cB
    cY
    cP
    cR
    cT
    @61
    cN
    cayhamlem1.t
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    mat2pmatbas
    syl3anc
    @64
    cY
    c.xp
    @59
    @62
    @65
    cayhamlem1.r
    ringcl
    syl3anc
    ralrimiva
    @58
    @11
    wceq
    #
    @59
    @13
    @62
    @17
    c.xp
    @58
    @11
    @12
    c.ex
    oveq1
    @106
    @61
    @16
    cT
    @106
    @60
    @15
    @6
    @58
    @11
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    oveq12d
    @58
    @19
    wceq
    #
    @59
    @20
    @62
    @51
    c.xp
    @58
    @19
    @12
    c.ex
    oveq1
    @107
    @61
    @50
    cT
    @107
    @60
    @49
    @6
    @58
    @19
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    oveq12d
    @58
    c1
    wceq
    #
    @59
    @37
    @62
    @40
    c.xp
    @58
    c1
    @12
    c.ex
    oveq1
    @108
    @61
    @39
    cT
    @108
    @60
    @38
    @6
    @58
    c1
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    oveq12d
    @58
    @27
    wceq
    #
    @59
    @28
    @62
    @44
    c.xp
    @58
    @27
    @12
    c.ex
    oveq1
    @109
    @61
    @43
    cT
    @109
    @60
    @42
    @6
    @58
    @27
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    oveq12d
    telgsumfz
    eqtrd
    oveq1d
    @10
    @47
    @34
    @31
    c.mi
    co
    #
    @35
    @36
    co
    #
    c.0
    @10
    @46
    @110
    @35
    @36
    @10
    @41
    @34
    @45
    @31
    c.mi
    @10
    @37
    @12
    @40
    @33
    c.xp
    @3
    @37
    @12
    wceq
    #
    @9
    @3
    @85
    @112
    @91
    @64
    c.ex
    @82
    @12
    @93
    cayhamlem1.e
    mulg1
    syl
    adantr
    @10
    @39
    @32
    cT
    @10
    @38
    cc0
    @6
    @10
    c1
    @10
    1cnd
    #
    subidd
    fveq2d
    fveq2d
    oveq12d
    @10
    @44
    @30
    @28
    c.xp
    @10
    @43
    @29
    cT
    @10
    @42
    @4
    @6
    @10
    @4
    c1
    @5
    @104
    @3
    @8
    @105
    ad2antrl
    @113
    pncand
    fveq2d
    fveq2d
    oveq2d
    oveq12d
    oveq1d
    @10
    cY
    cgrp
    wcel
    #
    @34
    @64
    wcel
    #
    @31
    @64
    wcel
    #
    @111
    c.0
    wceq
    @3
    @114
    @9
    @3
    @67
    @114
    @73
    cY
    ringgrp
    syl
    adantr
    @10
    @67
    @85
    @33
    @64
    wcel
    #
    @115
    @81
    @92
    @10
    @0
    @68
    @32
    cB
    wcel
    @117
    @94
    @95
    @10
    @7
    cB
    cc0
    @6
    @97
    @5
    cc0
    @7
    wcel
    #
    @3
    @8
    @5
    @4
    cn0
    wcel
    #
    @118
    @4
    nnnn0
    #
    @4
    0elfz
    syl
    ad2antrl
    ffvelrnd
    cA
    cB
    cY
    cP
    cR
    cT
    @32
    cN
    cayhamlem1.t
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    mat2pmatbas
    syl3anc
    @64
    cY
    c.xp
    @12
    @33
    @65
    cayhamlem1.r
    ringcl
    syl3anc
    @10
    @67
    @28
    @64
    wcel
    #
    @30
    @64
    wcel
    #
    @116
    @81
    @10
    @83
    @27
    cn
    wcel
    @85
    @121
    @10
    @86
    @83
    @88
    @89
    syl
    @10
    @4
    @3
    @5
    @8
    simprl
    peano2nnd
    @92
    @64
    c.ex
    @82
    @27
    @12
    @93
    cayhamlem1.e
    mulgnncl
    syl3anc
    @10
    @0
    @68
    @29
    cB
    wcel
    @122
    @94
    @95
    @10
    @7
    cB
    @4
    @6
    @97
    @5
    @4
    @7
    wcel
    #
    @3
    @8
    @5
    @119
    @123
    @120
    @4
    nn0fz0
    sylib
    ad2antrl
    ffvelrnd
    cA
    cB
    cY
    cP
    cR
    cT
    @29
    cN
    cayhamlem1.t
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    mat2pmatbas
    syl3anc
    @64
    cY
    c.xp
    @28
    @30
    @65
    cayhamlem1.r
    ringcl
    syl3anc
    @64
    @36
    cY
    c.mi
    @34
    @31
    c.0
    @65
    @48
    cayhamlem1.s
    cayhamlem1.0
    grpnpncan0
    syl12anc
    eqtrd
    3eqtrd
end
