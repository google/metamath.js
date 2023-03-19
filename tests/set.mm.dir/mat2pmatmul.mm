include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cascl.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cgsu.mm"
include "w3a.mm"
include "cvv.mm"
include "cotp.mm"
include "cmmul.mm"
include "eqid.mm"
include "matmulr.mm"
include "eqcomd.mm"
include "oveqdr.mm"
include "cbs.mm"
include "crg.mm"
include "crngring.mm"
include "ad2antlr.mm"
include "simpll.mm"
include "cxp.mm"
include "cmap.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantr.mm"
include "adantl.mm"
include "matbas2.mm"
include "eleqtrrd.mm"
include "ad2antll.mm"
include "wb.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "mamuval.mm"
include "eqtrd.mm"
include "3ad2ant1.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveqan12d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "simp2.mm"
include "simp3.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "fveq2d.mm"
include "c0g.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "syl.mm"
include "cmnd.mm"
include "ply1ring.mm"
include "ringmnd.mm"
include "cmhm.mm"
include "cghm.mm"
include "csca.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "asclghm.mm"
include "ply1sca.mm"
include "oveq1d.mm"
include "ghmmhm.mm"
include "simpr.mm"
include "sylibr.mm"
include "matecld.mm"
include "cmat.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "gsummptmhm.mm"
include "crh.mm"
include "casa.mm"
include "ply1assa.mm"
include "asclrhm.mm"
include "rhmmul.mm"
include "mpteq2dva.mm"
include "3eqtr2d.mm"
include "mpt2eq3dva.mm"
include "simp1rl.mm"
include "ply1sclcl.mm"
include "syl2anc.mm"
include "simp1rr.mm"
include "oveq12.mm"
include "mpt2matmul.mm"
include "eqtr4d.mm"
include "matring.mm"
include "sylan2.mm"
include "anim1i.mm"
include "3anass.mm"
include "mat2pmatval.mm"
include "simpl.mm"
include "anim2i.mm"
include "df-3an.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"

theorem mat2pmatmul
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let cH: class H
  let cN: class N
  let cM: class M
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume mat2pmatbas.t: |- T = ( N matToPolyMat R )
  assume mat2pmatbas.a: |- A = ( N Mat R )
  assume mat2pmatbas.b: |- B = ( Base ` A )
  assume mat2pmatbas.p: |- P = ( Poly1 ` R )
  assume mat2pmatbas.c: |- C = ( N Mat P )
  assume mat2pmatbas0.h: |- H = ( Base ` C )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint P x
  disjoint P y
  disjoint R x
  disjoint R y
  disjoint T x
  disjoint T y
  disjoint A x
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint H x
  disjoint H y
  disjoint M x
  disjoint M y
  disjoint B m
  disjoint m x
  disjoint m y
  disjoint H m
  disjoint N m
  disjoint R m
  disjoint T m
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint T i
  disjoint T j
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint A i
  disjoint A j
  disjoint P i
  disjoint P j
  disjoint A k
  disjoint A l
  disjoint k l
  disjoint B k
  disjoint B l
  disjoint N k
  disjoint N l
  disjoint P k
  disjoint P l
  disjoint P m
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint l m
  disjoint l x
  disjoint l y
  disjoint R k
  disjoint R l
  assert |- ( ( N e. Fin /\ R e. CRing ) -> A. x e. B A. y e. B ( T ` ( x ( .r ` A ) y ) ) = ( ( T ` x ) ( .r ` C ) ( T ` y ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    cmulr
    cfv
    #
    co
    #
    cT
    cfv
    #
    @3
    cT
    cfv
    #
    @4
    cT
    cfv
    #
    cC
    cmulr
    cfv
    #
    co
    #
    wceq
    vx
    vy
    cB
    cB
    @2
    @3
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    #
    wa
    #
    vk
    vl
    cN
    cN
    vk
    cv
    #
    vl
    cv
    #
    @6
    co
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    vi
    cv
    #
    vj
    cv
    #
    @3
    co
    #
    @19
    cfv
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    @22
    @23
    @4
    co
    #
    @19
    cfv
    #
    cmpt2
    #
    @10
    co
    #
    @7
    @11
    @15
    @21
    vk
    vl
    cN
    cN
    cP
    vm
    cN
    @16
    vm
    cv
    #
    @3
    co
    #
    @19
    cfv
    #
    @31
    @17
    @4
    co
    #
    @19
    cfv
    #
    cP
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    @30
    @15
    vk
    vl
    cN
    cN
    @20
    @39
    @15
    @16
    cN
    wcel
    #
    @17
    cN
    wcel
    #
    w3a
    #
    @20
    cR
    vm
    cN
    @32
    @34
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @19
    cfv
    cP
    vm
    cN
    @44
    @19
    cfv
    #
    cmpt
    #
    cgsu
    co
    @39
    @42
    @18
    @46
    @19
    @42
    vi
    vj
    @16
    @17
    cN
    cN
    cR
    vm
    cN
    @22
    @31
    @3
    co
    #
    @31
    @23
    @4
    co
    #
    @43
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @46
    @6
    cvv
    @15
    @40
    @6
    vi
    vj
    cN
    cN
    @53
    cmpt2
    #
    wceq
    @41
    @15
    @6
    @3
    @4
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    @54
    @2
    @14
    vx
    vy
    @5
    @55
    @2
    @55
    @5
    cA
    cR
    @55
    cN
    ccrg
    mat2pmatbas.a
    @55
    eqid
    #
    matmulr
    eqcomd
    oveqdr
    @15
    cR
    cbs
    cfv
    #
    cN
    cR
    @43
    vi
    vm
    vj
    @55
    cN
    cN
    crg
    @3
    @4
    @56
    @57
    eqid
    #
    @43
    eqid
    #
    @1
    cR
    crg
    wcel
    #
    @0
    @14
    cR
    crngring
    #
    ad2antlr
    #
    @0
    @1
    @14
    simpll
    #
    @63
    @63
    @15
    @3
    cA
    cbs
    cfv
    #
    @57
    cN
    cN
    cxp
    cmap
    co
    #
    @14
    @3
    @64
    wcel
    #
    @2
    @12
    @66
    @13
    @12
    @66
    cB
    @64
    @3
    mat2pmatbas.b
    eleq2i
    #
    biimpi
    adantr
    adantl
    #
    @2
    @65
    @64
    wceq
    @14
    cA
    cR
    @57
    cN
    ccrg
    mat2pmatbas.a
    @58
    matbas2
    #
    adantr
    eleqtrrd
    @15
    @4
    @65
    wcel
    #
    @4
    @64
    wcel
    #
    @13
    @71
    @2
    @12
    @13
    @71
    cB
    @64
    @4
    mat2pmatbas.b
    eleq2i
    #
    biimpi
    ad2antll
    #
    @2
    @70
    @71
    wb
    @14
    @2
    @65
    @64
    @4
    @69
    eleq2d
    adantr
    mpbird
    mamuval
    eqtrd
    3ad2ant1
    vi
    vk
    weq
    #
    vj
    vl
    weq
    #
    wa
    #
    @53
    @46
    wceq
    @42
    @76
    @52
    @45
    cR
    cgsu
    @76
    vm
    cN
    @51
    @44
    @74
    @75
    @49
    @32
    @50
    @34
    @43
    @22
    @16
    @31
    @3
    oveq1
    @23
    @17
    @31
    @4
    oveq2
    oveqan12d
    mpteq2dv
    oveq2d
    adantl
    @15
    @40
    @41
    simp2
    #
    @15
    @40
    @41
    simp3
    #
    @42
    cR
    @45
    cgsu
    ovexd
    ovmpt2d
    fveq2d
    @42
    vm
    cN
    @57
    @44
    cR
    cP
    @19
    cfn
    cR
    c0g
    cfv
    #
    @58
    @79
    eqid
    @15
    @40
    cR
    ccmn
    wcel
    #
    @41
    @1
    @80
    @0
    @14
    @1
    @60
    @80
    @61
    cR
    ringcmn
    syl
    ad2antlr
    3ad2ant1
    @15
    @40
    cP
    cmnd
    wcel
    #
    @41
    @1
    @81
    @0
    @14
    @1
    cP
    crg
    wcel
    #
    @81
    @1
    @60
    @82
    @61
    cP
    cR
    mat2pmatbas.p
    ply1ring
    syl
    #
    cP
    ringmnd
    syl
    ad2antlr
    3ad2ant1
    @15
    @40
    @0
    @41
    @63
    3ad2ant1
    #
    @15
    @40
    @19
    cR
    cP
    cmhm
    co
    wcel
    #
    @41
    @2
    @85
    @14
    @2
    @19
    cR
    cP
    cghm
    co
    #
    wcel
    @85
    @2
    @19
    cP
    csca
    cfv
    #
    cP
    cghm
    co
    @86
    @2
    @19
    @87
    cP
    @19
    eqid
    #
    @87
    eqid
    #
    @1
    @82
    @0
    @83
    adantl
    @1
    cP
    clmod
    wcel
    #
    @0
    @1
    @60
    @90
    @61
    cP
    cR
    mat2pmatbas.p
    ply1lmod
    syl
    adantl
    asclghm
    @2
    cR
    @87
    cP
    cghm
    @1
    cR
    @87
    wceq
    @0
    cP
    cR
    ccrg
    mat2pmatbas.p
    ply1sca
    adantl
    #
    oveq1d
    eleqtrrd
    cR
    cP
    @19
    ghmmhm
    syl
    adantr
    3ad2ant1
    @42
    @31
    cN
    wcel
    #
    wa
    #
    @60
    @32
    @57
    wcel
    #
    @34
    @57
    wcel
    #
    @44
    @57
    wcel
    @42
    @60
    @92
    @15
    @40
    @60
    @41
    @62
    3ad2ant1
    adantr
    @93
    cA
    cB
    cR
    @16
    @31
    @57
    @3
    cN
    mat2pmatbas.a
    @58
    mat2pmatbas.b
    @42
    @40
    @92
    @77
    adantr
    @42
    @92
    simpr
    #
    @93
    @66
    @12
    @42
    @66
    @92
    @15
    @40
    @66
    @41
    @68
    3ad2ant1
    adantr
    @67
    sylibr
    matecld
    #
    @93
    cA
    cB
    cR
    @31
    @17
    @57
    @4
    cN
    mat2pmatbas.a
    @58
    mat2pmatbas.b
    @96
    @42
    @41
    @92
    @78
    adantr
    #
    @93
    @4
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    @13
    @42
    @101
    @92
    @15
    @40
    @101
    @41
    @13
    @101
    @2
    @12
    @13
    @101
    cB
    @100
    @4
    cB
    @64
    @100
    mat2pmatbas.b
    cA
    @99
    cbs
    mat2pmatbas.a
    fveq2i
    eqtri
    eleq2i
    #
    biimpi
    ad2antll
    3ad2ant1
    adantr
    @102
    sylibr
    matecld
    @57
    cR
    @43
    @32
    @34
    @58
    @59
    ringcl
    syl3anc
    @42
    vm
    cN
    @45
    cvv
    cvv
    @44
    @79
    @45
    eqid
    @84
    @93
    @32
    @34
    @43
    ovexd
    @42
    cR
    c0g
    fvexd
    fsuppmptdm
    gsummptmhm
    @42
    @48
    @38
    cP
    cgsu
    @42
    vm
    cN
    @47
    @37
    @93
    @19
    cR
    cP
    crh
    co
    #
    wcel
    #
    @94
    @95
    @47
    @37
    wceq
    @42
    @104
    @92
    @15
    @40
    @104
    @41
    @2
    @104
    @14
    @2
    @19
    @87
    cP
    crh
    co
    #
    @103
    @2
    cP
    casa
    wcel
    #
    @19
    @105
    wcel
    @1
    @106
    @0
    cP
    cR
    mat2pmatbas.p
    ply1assa
    adantl
    @19
    @87
    cP
    @88
    @89
    asclrhm
    syl
    @2
    cR
    @87
    cP
    crh
    @91
    oveq1d
    eleqtrrd
    adantr
    3ad2ant1
    adantr
    @97
    @93
    cA
    cB
    cR
    @31
    @17
    @57
    @4
    cN
    mat2pmatbas.a
    @58
    mat2pmatbas.b
    @96
    @98
    @93
    @71
    @13
    @42
    @71
    @92
    @15
    @40
    @71
    @41
    @73
    3ad2ant1
    adantr
    @72
    sylibr
    matecld
    @32
    @34
    cR
    cP
    @43
    @36
    @19
    @57
    @58
    @59
    @36
    eqid
    #
    rhmmul
    syl3anc
    mpteq2dva
    oveq2d
    3eqtr2d
    mpt2eq3dva
    @15
    cC
    cP
    cbs
    cfv
    #
    @25
    @33
    cP
    @36
    @10
    cvv
    vi
    vj
    vk
    vm
    @28
    @35
    cN
    crg
    cvv
    @26
    @29
    vl
    mat2pmatbas.c
    @108
    eqid
    #
    @10
    eqid
    @107
    @1
    @82
    @0
    @14
    @83
    ad2antlr
    @63
    @26
    eqid
    @29
    eqid
    @15
    @22
    cN
    wcel
    #
    @23
    cN
    wcel
    #
    w3a
    #
    @60
    @24
    @57
    wcel
    @25
    @108
    wcel
    @15
    @110
    @60
    @111
    @62
    3ad2ant1
    #
    @112
    cA
    cB
    cR
    @22
    @23
    @57
    @3
    cN
    mat2pmatbas.a
    @58
    mat2pmatbas.b
    @15
    @110
    @111
    simp2
    #
    @15
    @110
    @111
    simp3
    #
    @12
    @13
    @2
    @110
    @111
    simp1rl
    matecld
    @19
    @108
    cP
    cR
    @24
    @57
    mat2pmatbas.p
    @88
    @58
    @109
    ply1sclcl
    syl2anc
    @112
    @60
    @27
    @57
    wcel
    @28
    @108
    wcel
    @113
    @112
    cA
    cB
    cR
    @22
    @23
    @57
    @4
    cN
    mat2pmatbas.a
    @58
    mat2pmatbas.b
    @114
    @115
    @12
    @13
    @2
    @110
    @111
    simp1rr
    matecld
    @19
    @108
    cP
    cR
    @27
    @57
    mat2pmatbas.p
    @88
    @58
    @109
    ply1sclcl
    syl2anc
    vk
    vi
    weq
    vm
    vj
    weq
    wa
    #
    @33
    @25
    wceq
    @15
    @116
    @32
    @24
    @19
    @16
    @22
    @31
    @23
    @3
    oveq12
    fveq2d
    adantl
    vm
    vi
    weq
    vl
    vj
    weq
    wa
    #
    @35
    @28
    wceq
    @15
    @117
    @34
    @27
    @19
    @31
    @22
    @17
    @23
    @4
    oveq12
    fveq2d
    adantl
    @15
    @40
    @92
    w3a
    @32
    @19
    fvexd
    @15
    @92
    @41
    w3a
    @34
    @19
    fvexd
    mpt2matmul
    eqtr4d
    @15
    @0
    @60
    @6
    cB
    wcel
    #
    @7
    @21
    wceq
    @63
    @62
    @15
    cA
    crg
    wcel
    #
    @12
    @13
    w3a
    #
    @118
    @15
    @119
    @14
    wa
    @120
    @2
    @119
    @14
    @1
    @0
    @60
    @119
    @61
    cA
    cR
    cN
    mat2pmatbas.a
    matring
    sylan2
    anim1i
    @119
    @12
    @13
    3anass
    sylibr
    cB
    cA
    @5
    @3
    @4
    mat2pmatbas.b
    @5
    eqid
    ringcl
    syl
    vk
    vl
    cA
    cB
    cP
    cR
    @19
    cT
    @6
    cN
    crg
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @88
    mat2pmatval
    syl3anc
    @15
    @8
    @26
    @9
    @29
    @10
    @15
    @0
    @1
    @12
    w3a
    #
    @8
    @26
    wceq
    @15
    @2
    @12
    wa
    @121
    @14
    @12
    @2
    @12
    @13
    simpl
    anim2i
    @0
    @1
    @12
    df-3an
    sylibr
    vi
    vj
    cA
    cB
    cP
    cR
    @19
    cT
    @3
    cN
    ccrg
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @88
    mat2pmatval
    syl
    @15
    @0
    @1
    @13
    w3a
    #
    @9
    @29
    wceq
    @15
    @2
    @13
    wa
    @122
    @14
    @13
    @2
    @12
    @13
    simpr
    anim2i
    @0
    @1
    @13
    df-3an
    sylibr
    vi
    vj
    cA
    cB
    cP
    cR
    @19
    cT
    @4
    cN
    ccrg
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @88
    mat2pmatval
    syl
    oveq12d
    3eqtr4d
    ralrimivva
end
