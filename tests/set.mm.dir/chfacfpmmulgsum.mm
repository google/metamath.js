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
include "caddc.mm"
include "cuz.mm"
include "cmin.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "ccmn.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "3adant3.mm"
include "pmatring.mm"
include "syl.mm"
include "ringcmn.mm"
include "adantr.mm"
include "nn0ex.mm"
include "a1i.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "3jca.mm"
include "chfacfpmmulcl.mm"
include "chfacfpmmulfsupp.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "nn0disj.mm"
include "cun.mm"
include "nnnn0.mm"
include "peano2nn0.mm"
include "nn0split.mm"
include "ad2antrl.mm"
include "gsumsplit2.mm"
include "c2.mm"
include "cc.mm"
include "nncn.mm"
include "add1p1.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "chfacfpmmul0.mm"
include "syl3anc.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "sylan2.mm"
include "ringmnd.mm"
include "fvex.mm"
include "jctir.mm"
include "gsumz.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "elfznn0.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "mndrid.mm"
include "syl2anc.mm"
include "csn.mm"
include "gsummptfzsplit.mm"
include "gsummptfzsplitl.mm"
include "0nn0.mm"
include "mpd3an3.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "gsumsn.mm"
include "ovexd.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "elfznn.mm"
include "nnnn0d.mm"
include "adantl.mm"
include "mndass.mm"
include "syl13anc.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "wne.mm"
include "nnne0d.mm"
include "ad2antlr.mm"
include "wb.mm"
include "neeq1.mm"
include "mpbird.mm"
include "eqneqall.mm"
include "mpan9.mm"
include "eqeq1.mm"
include "eqcoms.mm"
include "wn.mm"
include "cz.mm"
include "cle.mm"
include "elfz2.mm"
include "wo.mm"
include "wi.mm"
include "zleltp1.mm"
include "ancoms.mm"
include "3adant1.mm"
include "biimpcd.mm"
include "impcom.mm"
include "orcd.mm"
include "cr.mm"
include "zre.mm"
include "1red.mm"
include "readdcld.mm"
include "anim12ci.mm"
include "lttri2.mm"
include "sylbi.mm"
include "neneqd.mm"
include "pm2.21d.mm"
include "imp.mm"
include "nnred.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "nn0red.mm"
include "ad2antrr.mm"
include "breq1.mm"
include "ltnsymd.mm"
include "simp-4r.mm"
include "oveq1d.mm"
include "ifeqda.mm"
include "fvmptd.mm"
include "nn0p1gt0.mm"
include "0red.mm"
include "ltne.mm"
include "sylan.mm"
include "mpdan.mm"
include "iftrue.mm"
include "fvexd.mm"
include "cur.mm"
include "cmgp.mm"
include "c0g.mm"
include "mat2pmatbas.mm"
include "syl3an2.mm"
include "mgpbas.mm"
include "mulg0.mm"
include "ringidval.mm"
include "syl6eqr.mm"
include "wf.mm"
include "chfacfisf.mm"
include "syl3anl2.mm"
include "ffvelrnd.mm"
include "ringlidm.mm"
include "3eqtrd.mm"
include "cmncom.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "eqeltrrd.mm"
include "simpl1.mm"
include "3ad2ant2.mm"
include "elmapi.mm"
include "0elfz.mm"
include "ringcl.mm"
include "grpsubadd0sub.mm"
include "3eqtr4d.mm"

theorem chfacfpmmulgsum
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
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
  assume chfacfpmmulgsum.p: |- .+ = ( +g ` Y )

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
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> ( Y gsum ( i e. NN0 |-> ( ( i .^ ( T ` M ) ) .X. ( G ` i ) ) ) ) = ( ( Y gsum ( i e. ( 1 ... s ) |-> ( ( i .^ ( T ` M ) ) .X. ( ( T ` ( b ` ( i - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` i ) ) ) ) ) ) ) .+ ( ( ( ( s + 1 ) .^ ( T ` M ) ) .X. ( T ` ( b ` s ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) ) )

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
    #
    c.xp
    co
    #
    cmpt
    cgsu
    co
    cY
    vi
    cc0
    @4
    c1
    caddc
    co
    #
    cfz
    co
    #
    @15
    cmpt
    cgsu
    co
    #
    cY
    vi
    @16
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @15
    cmpt
    #
    cgsu
    co
    #
    c.pl
    co
    #
    @18
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
    @12
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
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @16
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
    c.pl
    co
    #
    @10
    cn0
    cY
    cbs
    cfv
    #
    @17
    @20
    c.pl
    vi
    cY
    cvv
    @15
    c.0
    @44
    eqid
    #
    cayhamlem1.0
    chfacfpmmulgsum.p
    @3
    cY
    ccmn
    wcel
    #
    @9
    @3
    cY
    crg
    wcel
    #
    @46
    @3
    @0
    cR
    crg
    wcel
    #
    wa
    #
    @47
    @0
    @1
    @49
    @2
    @1
    @48
    @0
    cR
    crngring
    #
    anim2i
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
    ringcmn
    syl
    adantr
    #
    cn0
    cvv
    wcel
    @10
    nn0ex
    a1i
    @10
    @11
    cn0
    wcel
    #
    wa
    #
    @3
    @9
    @54
    w3a
    #
    @15
    @44
    wcel
    #
    @55
    @3
    @9
    @54
    @3
    @9
    @54
    simpll
    @3
    @9
    @54
    simplr
    @10
    @54
    simpr
    3jca
    #
    cA
    cB
    cP
    cR
    cT
    c.xp
    vn
    c.ex
    cG
    @11
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
    chfacfpmmulcl
    #
    syl
    #
    cA
    cB
    cP
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
    chfacfpmmulfsupp
    @17
    @20
    cin
    c0
    wceq
    @10
    @16
    nn0disj
    a1i
    @5
    cn0
    @17
    @20
    cun
    wceq
    #
    @3
    @8
    @5
    @16
    cn0
    wcel
    #
    @61
    @5
    @4
    cn0
    wcel
    #
    @62
    @4
    nnnn0
    #
    @4
    peano2nn0
    #
    syl
    @16
    nn0split
    syl
    ad2antrl
    gsumsplit2
    @10
    @23
    @18
    c.0
    c.pl
    co
    #
    @18
    @10
    @22
    c.0
    @18
    c.pl
    @10
    @22
    cY
    vi
    @20
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @10
    @21
    @67
    cY
    cgsu
    @10
    vi
    @20
    @15
    c.0
    @10
    @11
    @20
    wcel
    #
    wa
    @3
    @9
    @11
    @4
    c2
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @15
    c.0
    wceq
    @3
    @9
    @69
    simpll
    @3
    @9
    @69
    simplr
    @10
    @69
    @72
    @10
    @20
    @71
    @11
    @10
    @19
    @70
    cuz
    @5
    @19
    @70
    wceq
    #
    @3
    @8
    @5
    @4
    cc
    wcel
    @73
    @4
    nncn
    @4
    add1p1
    syl
    ad2antrl
    fveq2d
    eleq2d
    biimpa
    cA
    cB
    cP
    cR
    cT
    c.xp
    vn
    c.ex
    cG
    @11
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
    chfacfpmmul0
    syl3anc
    mpteq2dva
    oveq2d
    @10
    cY
    cmnd
    wcel
    #
    @20
    cvv
    wcel
    #
    wa
    #
    @68
    c.0
    wceq
    @3
    @76
    @9
    @3
    @74
    @75
    @0
    @1
    @74
    @2
    @0
    @1
    wa
    @47
    @74
    @1
    @0
    @48
    @47
    @50
    @51
    sylan2
    #
    cY
    ringmnd
    syl
    3adant3
    #
    @19
    cuz
    fvex
    jctir
    adantr
    @20
    vi
    cY
    cvv
    c.0
    cayhamlem1.0
    gsumz
    syl
    eqtrd
    oveq2d
    @10
    @74
    @18
    @44
    wcel
    @66
    @18
    wceq
    @3
    @74
    @9
    @78
    adantr
    #
    @10
    @44
    vi
    cY
    @17
    @15
    @45
    @53
    @10
    cc0
    @16
    fzfid
    @10
    @57
    vi
    @17
    @10
    @11
    @17
    wcel
    #
    wa
    @56
    @57
    @80
    @10
    @54
    @56
    @11
    @16
    elfznn0
    @58
    sylan2
    @59
    syl
    #
    ralrimiva
    gsummptcl
    @44
    c.pl
    cY
    @18
    c.0
    @45
    chfacfpmmulgsum.p
    cayhamlem1.0
    mndrid
    syl2anc
    eqtrd
    @10
    @18
    cY
    vi
    @7
    @15
    cmpt
    cgsu
    co
    #
    cY
    vi
    @16
    csn
    @15
    cmpt
    cgsu
    co
    #
    c.pl
    co
    cY
    vi
    @24
    @15
    cmpt
    #
    cgsu
    co
    #
    cc0
    @12
    c.ex
    co
    #
    cc0
    cG
    cfv
    #
    c.xp
    co
    #
    c.pl
    co
    #
    @35
    @16
    cG
    cfv
    #
    c.xp
    co
    #
    c.pl
    co
    #
    @43
    @10
    @44
    c.pl
    vi
    cY
    @4
    @15
    @45
    chfacfpmmulgsum.p
    @53
    @5
    @63
    @3
    @8
    @64
    ad2antrl
    #
    @81
    gsummptfzsplit
    @10
    @82
    @89
    @83
    @91
    c.pl
    @10
    @82
    @85
    cY
    vi
    cc0
    csn
    @15
    cmpt
    cgsu
    co
    #
    c.pl
    co
    @89
    @10
    @44
    c.pl
    vi
    cY
    @4
    @15
    @45
    chfacfpmmulgsum.p
    @53
    @93
    @11
    @7
    wcel
    @10
    @54
    @57
    @11
    @4
    elfznn0
    @60
    sylan2
    gsummptfzsplitl
    @10
    @94
    @88
    @85
    c.pl
    @10
    @74
    cc0
    cn0
    wcel
    #
    @88
    @44
    wcel
    #
    @94
    @88
    wceq
    @79
    @95
    @10
    0nn0
    a1i
    #
    @3
    @9
    @95
    @96
    @97
    cA
    cB
    cP
    cR
    cT
    c.xp
    vn
    c.ex
    cG
    cc0
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
    chfacfpmmulcl
    mpd3an3
    #
    @15
    @44
    @88
    vi
    cY
    cc0
    cn0
    @45
    @11
    cc0
    wceq
    @13
    @86
    @14
    @87
    c.xp
    @11
    cc0
    @12
    c.ex
    oveq1
    @11
    cc0
    cG
    fveq2
    oveq12d
    gsumsn
    syl3anc
    oveq2d
    eqtrd
    @10
    @74
    @16
    cvv
    wcel
    @91
    @44
    wcel
    #
    @83
    @91
    wceq
    @79
    @10
    @4
    c1
    caddc
    ovexd
    @3
    @9
    @62
    @99
    @10
    @4
    c1
    @93
    c1
    cn0
    wcel
    @10
    1nn0
    a1i
    nn0addcld
    cA
    cB
    cP
    cR
    cT
    c.xp
    vn
    c.ex
    cG
    @16
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
    chfacfpmmulcl
    mpd3an3
    #
    @15
    @44
    @91
    vi
    cY
    @16
    cvv
    @45
    @11
    @16
    wceq
    @13
    @35
    @14
    @90
    c.xp
    @11
    @16
    @12
    c.ex
    oveq1
    @11
    @16
    cG
    fveq2
    oveq12d
    gsumsn
    syl3anc
    oveq12d
    @10
    @92
    @85
    @88
    @91
    c.pl
    co
    #
    c.pl
    co
    #
    @43
    @10
    @74
    @85
    @44
    wcel
    @96
    @99
    @92
    @102
    wceq
    @79
    @10
    @44
    vi
    cY
    @24
    @15
    @45
    @53
    @10
    c1
    @4
    fzfid
    @10
    @57
    vi
    @24
    @10
    @11
    @24
    wcel
    #
    wa
    #
    @3
    @9
    @54
    @57
    @3
    @9
    @103
    simpll
    @3
    @9
    @103
    simplr
    @103
    @54
    @10
    @103
    @11
    @11
    @4
    elfznn
    #
    nnnn0d
    adantl
    #
    @59
    syl3anc
    ralrimiva
    gsummptcl
    @98
    @100
    @44
    c.pl
    cY
    @85
    @88
    @91
    @45
    chfacfpmmulgsum.p
    mndass
    syl13anc
    @10
    @85
    @34
    @101
    @42
    c.pl
    @10
    @84
    @33
    cY
    cgsu
    @10
    vi
    @24
    @15
    @32
    @104
    @14
    @31
    @13
    c.xp
    @104
    vn
    @11
    vn
    cv
    #
    cc0
    wceq
    #
    c.0
    @41
    c.mi
    co
    #
    @107
    @16
    wceq
    #
    @37
    @16
    @107
    clt
    wbr
    #
    c.0
    @107
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
    @12
    @107
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
    cif
    #
    cif
    #
    cif
    #
    @31
    cn0
    cG
    cvv
    cG
    vn
    cn0
    @121
    cmpt
    wceq
    #
    @104
    cayhamlem1.g
    a1i
    @104
    @107
    @11
    wceq
    #
    wa
    #
    @108
    @109
    @120
    @31
    @124
    @108
    wa
    #
    c.0
    @27
    @41
    @30
    c.mi
    @124
    @107
    cc0
    wne
    #
    @108
    c.0
    @27
    wceq
    #
    @124
    @126
    @11
    cc0
    wne
    #
    @103
    @128
    @10
    @123
    @103
    @11
    @105
    nnne0d
    ad2antlr
    @123
    @126
    @128
    wb
    @104
    @107
    @11
    cc0
    neeq1
    adantl
    mpbird
    @127
    @107
    cc0
    eqneqall
    mpan9
    @125
    @40
    @29
    @12
    c.xp
    @125
    @39
    @28
    cT
    @125
    cc0
    @11
    @6
    @125
    cc0
    @11
    wceq
    #
    @123
    @104
    @123
    @108
    simplr
    @108
    @129
    @123
    wb
    #
    @124
    @130
    cc0
    @107
    cc0
    @107
    @11
    eqeq1
    eqcoms
    adantl
    mpbird
    fveq2d
    fveq2d
    oveq2d
    oveq12d
    @124
    @108
    wn
    #
    wa
    #
    @110
    @37
    @119
    @31
    @132
    @110
    @37
    @31
    wceq
    #
    @132
    @110
    @133
    @132
    @107
    @16
    @124
    @107
    @16
    wne
    #
    @131
    @124
    @134
    @11
    @16
    wne
    #
    @103
    @135
    @10
    @123
    @103
    c1
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    w3a
    #
    c1
    @11
    cle
    wbr
    #
    @11
    @4
    cle
    wbr
    #
    wa
    #
    wa
    #
    @135
    @11
    c1
    @4
    elfz2
    #
    @143
    @135
    @11
    @16
    clt
    wbr
    #
    @16
    @11
    clt
    wbr
    #
    wo
    #
    @143
    @145
    @146
    @142
    @139
    @145
    @141
    @139
    @145
    wi
    @140
    @139
    @141
    @145
    @137
    @138
    @141
    @145
    wb
    #
    @136
    @138
    @137
    @148
    @11
    @4
    zleltp1
    ancoms
    3adant1
    biimpcd
    adantl
    impcom
    #
    orcd
    @139
    @135
    @147
    wb
    #
    @142
    @139
    @11
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    wa
    #
    @150
    @137
    @138
    @153
    @136
    @137
    @152
    @138
    @151
    @137
    @4
    c1
    @4
    zre
    @137
    1red
    readdcld
    @11
    zre
    anim12ci
    3adant1
    @11
    @16
    lttri2
    syl
    adantr
    mpbird
    sylbi
    ad2antlr
    @123
    @134
    @135
    wb
    @104
    @107
    @11
    @16
    neeq1
    adantl
    mpbird
    adantr
    neneqd
    pm2.21d
    imp
    @132
    @110
    wn
    #
    wa
    #
    @111
    c.0
    @118
    @31
    @155
    @111
    c.0
    @31
    wceq
    #
    @124
    @111
    @156
    wi
    @131
    @154
    @124
    @111
    @156
    @124
    @107
    @16
    @104
    @123
    @107
    cr
    wcel
    #
    @103
    @123
    @157
    wi
    @10
    @103
    @157
    @123
    @151
    @103
    @11
    @105
    nnred
    @107
    @11
    cr
    eleq1
    syl5ibrcom
    adantl
    imp
    @124
    @4
    c1
    @10
    @4
    cr
    wcel
    @103
    @123
    @10
    @4
    @93
    nn0red
    ad2antrr
    @124
    1red
    readdcld
    @124
    @107
    @16
    clt
    wbr
    #
    @145
    @103
    @145
    @10
    @123
    @103
    @143
    @145
    @144
    @149
    sylbi
    ad2antlr
    @123
    @158
    @145
    wb
    @104
    @107
    @11
    @16
    clt
    breq1
    adantl
    mpbird
    ltnsymd
    pm2.21d
    ad2antrr
    imp
    @155
    @111
    wn
    #
    wa
    #
    @114
    @27
    @117
    @30
    c.mi
    @160
    @113
    @26
    cT
    @160
    @112
    @25
    @6
    @160
    @107
    @11
    c1
    cmin
    @104
    @123
    @131
    @154
    @159
    simp-4r
    #
    oveq1d
    fveq2d
    fveq2d
    @160
    @116
    @29
    @12
    c.xp
    @160
    @115
    @28
    cT
    @160
    @107
    @11
    @6
    @161
    fveq2d
    fveq2d
    oveq2d
    oveq12d
    ifeqda
    ifeqda
    ifeqda
    @106
    @104
    @27
    @30
    c.mi
    ovexd
    fvmptd
    oveq2d
    mpteq2dva
    oveq2d
    @10
    @91
    @88
    c.pl
    co
    #
    @38
    @109
    c.pl
    co
    #
    @101
    @42
    @10
    @91
    @38
    @88
    @109
    c.pl
    @10
    @90
    @37
    @35
    c.xp
    @10
    vn
    @16
    @121
    @37
    cn0
    cG
    cvv
    @122
    @10
    cayhamlem1.g
    a1i
    #
    @10
    @110
    wa
    #
    @108
    @109
    @120
    @37
    @165
    @126
    @108
    @109
    @37
    wceq
    #
    @10
    @110
    @126
    @5
    @110
    @126
    wi
    #
    @3
    @8
    @5
    @63
    @167
    @64
    @63
    cc0
    @16
    clt
    wbr
    #
    @167
    @4
    nn0p1gt0
    @63
    @168
    wa
    @126
    @110
    @16
    cc0
    wne
    #
    @63
    cc0
    cr
    wcel
    @168
    @169
    @63
    0red
    cc0
    @16
    ltne
    sylan
    @107
    @16
    cc0
    neeq1
    syl5ibrcom
    mpdan
    syl
    ad2antrl
    imp
    @166
    @107
    cc0
    eqneqall
    mpan9
    @110
    @120
    @37
    wceq
    @10
    @131
    @110
    @37
    @119
    iftrue
    ad2antlr
    ifeqda
    @10
    @63
    @62
    @93
    @65
    syl
    @10
    @36
    cT
    fvexd
    fvmptd
    oveq2d
    #
    @10
    @88
    cY
    cur
    cfv
    #
    @87
    c.xp
    co
    #
    @87
    @109
    @10
    @86
    @171
    @87
    c.xp
    @3
    @86
    @171
    wceq
    @9
    @3
    @86
    cY
    cmgp
    cfv
    #
    c0g
    cfv
    #
    @171
    @3
    @12
    @44
    wcel
    #
    @86
    @174
    wceq
    @1
    @0
    @48
    @2
    @175
    @50
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
    @44
    c.ex
    @173
    @12
    @174
    @44
    cY
    @173
    @173
    eqid
    #
    @45
    mgpbas
    @174
    eqid
    cayhamlem1.e
    mulg0
    syl
    cY
    @171
    @173
    @177
    @171
    eqid
    #
    ringidval
    syl6eqr
    adantr
    oveq1d
    @10
    @47
    @87
    @44
    wcel
    @172
    @87
    wceq
    @3
    @47
    @9
    @0
    @1
    @47
    @2
    @77
    3adant3
    adantr
    @10
    cn0
    @44
    cc0
    cG
    @1
    @0
    @48
    @2
    @9
    cn0
    @44
    cG
    wf
    @50
    cA
    cB
    cP
    cR
    cT
    c.xp
    vn
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
    chfacfisf
    syl3anl2
    @97
    ffvelrnd
    @44
    cY
    c.xp
    @171
    @87
    @45
    cayhamlem1.r
    @178
    ringlidm
    syl2anc
    @10
    vn
    cc0
    @121
    @109
    cn0
    cG
    cvv
    @164
    @108
    @121
    @109
    wceq
    @10
    @108
    @109
    @120
    iftrue
    adantl
    @97
    @10
    c.0
    @41
    c.mi
    ovexd
    fvmptd
    3eqtrd
    oveq12d
    @10
    @46
    @96
    @99
    @101
    @162
    wceq
    @53
    @98
    @100
    @44
    c.pl
    cY
    @88
    @91
    @45
    chfacfpmmulgsum.p
    cmncom
    syl3anc
    @10
    cY
    cgrp
    wcel
    #
    @38
    @44
    wcel
    @41
    @44
    wcel
    #
    @42
    @163
    wceq
    @3
    @179
    @9
    @3
    @47
    @179
    @52
    cY
    ringgrp
    syl
    adantr
    @10
    @91
    @38
    @44
    @170
    @100
    eqeltrrd
    @10
    @47
    @175
    @40
    @44
    wcel
    #
    @180
    @3
    @47
    @9
    @52
    adantr
    @3
    @175
    @9
    @176
    adantr
    @10
    @0
    @48
    @39
    cB
    wcel
    @181
    @0
    @1
    @2
    @9
    simpl1
    @3
    @48
    @9
    @1
    @0
    @48
    @2
    @50
    3ad2ant2
    adantr
    @10
    @7
    cB
    cc0
    @6
    @9
    @7
    cB
    @6
    wf
    #
    @3
    @8
    @182
    @5
    @6
    cB
    @7
    elmapi
    adantl
    adantl
    @5
    cc0
    @7
    wcel
    #
    @3
    @8
    @5
    @63
    @183
    @64
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
    @39
    cN
    cayhamlem1.t
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    mat2pmatbas
    syl3anc
    @44
    cY
    c.xp
    @12
    @40
    @45
    cayhamlem1.r
    ringcl
    syl3anc
    @44
    c.pl
    cY
    c.mi
    @38
    @41
    c.0
    @45
    cayhamlem1.0
    cayhamlem1.s
    chfacfpmmulgsum.p
    grpsubadd0sub
    syl3anc
    3eqtr4d
    oveq12d
    eqtrd
    3eqtrd
    3eqtrd
end
