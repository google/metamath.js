include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "csn.mm"
include "cdif.mm"
include "cmpt2.mm"
include "wo.mm"
include "wel.mm"
include "c0.mm"
include "cun.mm"
include "eleq2.mm"
include "ifbid.mm"
include "ifeq2d.mm"
include "mpt2eq3dv.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "weq.mm"
include "maducoeval.mm"
include "3adant1l.mm"
include "wn.mm"
include "noel.mm"
include "iffalse.mm"
include "mp1i.mm"
include "mpt2eq3ia.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "wss.mm"
include "cmulr.mm"
include "cplusg.mm"
include "cbs.mm"
include "eqid.mm"
include "simpl1l.mm"
include "cfn.mm"
include "simp1r.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "syl.mm"
include "adantr.mm"
include "crg.mm"
include "simp1l.mm"
include "ad2antrr.mm"
include "crngring.mm"
include "ring0cl.mm"
include "cxp.mm"
include "wf.mm"
include "cmap.mm"
include "simpl1r.mm"
include "matbas2i.mm"
include "elmapi.mm"
include "3syl.mm"
include "eldifi.mm"
include "ad2antll.mm"
include "eldifad.mm"
include "simpr.mm"
include "fovrnd.mm"
include "ifcld.mm"
include "ringidcl.mm"
include "3adant2.mm"
include "fovrnda.mm"
include "3impb.mm"
include "simpl2.mm"
include "simpl3.mm"
include "wne.mm"
include "eldifsni.mm"
include "mdetero.mm"
include "ifnot.mm"
include "eqcomi.mm"
include "a1i.mm"
include "ovif2.mm"
include "ringridm.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "ifeq1da.mm"
include "ringrz.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "oveq12d.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "wi.mm"
include "id.mm"
include "imnan.mm"
include "mpbi.mm"
include "mndifsplit.mm"
include "syl3anc.mm"
include "pm2.1.mm"
include "iftrue.mm"
include "3eqtr2d.mm"
include "oveq1.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "neneqd.mm"
include "3ad2ant1.mm"
include "eqeq1.mm"
include "notbid.mm"
include "iffalsed.mm"
include "eldifn.mm"
include "eleq1.mm"
include "3eqtr4d.mm"
include "pm2.61dan.mm"
include "mpt2eq3dva.mm"
include "neeq2.mm"
include "biimparc.mm"
include "necomd.mm"
include "vsnid.mm"
include "elun2.mm"
include "ax-mp.mm"
include "mpbiri.mm"
include "iftrued.mm"
include "3eqtr4rd.mm"
include "orc.mm"
include "orel2.mm"
include "impbid2.mm"
include "elun.mm"
include "velsn.mm"
include "orbi2i.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "3eqtr3d.mm"
include "biimpd.mm"
include "difss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "findcard2d.mm"
include "iba.mm"
include "orcs.mm"
include "neqned.mm"
include "anim2i.mm"
include "adantlr.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "biorf.mm"
include "intnand.mm"
include "eqcomd.mm"
include "ifbieq1d.mm"
include "3eqtrd.mm"
include "syl6eq.mm"

theorem maducoeval2
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.1: class .1.
  let vk: setvar k
  let cH: class H
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vl: setvar l
  let vn: setvar n
  let vr: setvar r
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  assume madufval.a: |- A = ( N Mat R )
  assume madufval.d: |- D = ( N maDet R )
  assume madufval.j: |- J = ( N maAdju R )
  assume madufval.b: |- B = ( Base ` A )
  assume madufval.o: |- .1. = ( 1r ` R )
  assume madufval.z: |- .0. = ( 0g ` R )

  disjoint N k
  disjoint N l
  disjoint k l
  disjoint R k
  disjoint R l
  disjoint M k
  disjoint M l
  disjoint I k
  disjoint I l
  disjoint H k
  disjoint H l
  disjoint B k
  disjoint B l
  disjoint .0. k
  disjoint .1. k
  disjoint N n
  disjoint N r
  disjoint N m
  disjoint N i
  disjoint N j
  disjoint n r
  disjoint m n
  disjoint i n
  disjoint j n
  disjoint k n
  disjoint l n
  disjoint m r
  disjoint i r
  disjoint j r
  disjoint k r
  disjoint l r
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint l m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint R n
  disjoint R r
  disjoint R m
  disjoint R i
  disjoint R j
  disjoint B m
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint D m
  disjoint .1. m
  disjoint .0. m
  disjoint B i
  disjoint B j
  disjoint I i
  disjoint I j
  disjoint D i
  disjoint D j
  disjoint .1. i
  disjoint .1. j
  disjoint .0. i
  disjoint .0. j
  disjoint H i
  disjoint H j
  disjoint B n
  disjoint B r
  disjoint D n
  disjoint D r
  disjoint H m
  disjoint H n
  disjoint H r
  disjoint I m
  disjoint I n
  disjoint I r
  disjoint J m
  disjoint J n
  disjoint J r
  disjoint M n
  disjoint M r
  disjoint .0. n
  disjoint .0. r
  disjoint .1. n
  disjoint .1. r
  assert |- ( ( ( R e. CRing /\ M e. B ) /\ I e. N /\ H e. N ) -> ( I ( J ` M ) H ) = ( D ` ( k e. N , l e. N |-> if ( ( k = H \/ l = I ) , if ( ( l = I /\ k = H ) , .1. , .0. ) , ( k M l ) ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    cI
    cN
    wcel
    #
    cH
    cN
    wcel
    #
    w3a
    #
    cI
    cH
    cM
    cJ
    cfv
    co
    #
    vk
    vl
    cN
    cN
    vk
    cv
    #
    cH
    wceq
    #
    vl
    cv
    #
    cI
    wceq
    #
    c.1
    c.0
    cif
    #
    @7
    cN
    cH
    csn
    #
    cdif
    #
    wcel
    #
    @10
    c.0
    @7
    @9
    cM
    co
    #
    cif
    #
    @15
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    vk
    vl
    cN
    cN
    @8
    @10
    wo
    #
    @10
    @8
    wa
    #
    c.1
    c.0
    cif
    #
    @15
    cif
    #
    cmpt2
    #
    cD
    cfv
    @5
    @6
    vk
    vl
    cN
    cN
    @8
    @11
    vk
    vm
    wel
    #
    @16
    @15
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    wceq
    @6
    vk
    vl
    cN
    cN
    @8
    @11
    @7
    c0
    wcel
    #
    @16
    @15
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    wceq
    @6
    vk
    vl
    cN
    cN
    @8
    @11
    vk
    vn
    wel
    #
    @16
    @15
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    wceq
    #
    @6
    vk
    vl
    cN
    cN
    @8
    @11
    @7
    vn
    cv
    #
    vr
    cv
    #
    csn
    #
    cun
    #
    wcel
    #
    @16
    @15
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    wceq
    #
    @6
    @20
    wceq
    vm
    vn
    vr
    @13
    vm
    cv
    #
    c0
    wceq
    #
    @30
    @35
    @6
    @53
    @29
    @34
    cD
    @53
    vk
    vl
    cN
    cN
    @28
    @33
    @53
    @8
    @27
    @32
    @11
    @53
    @26
    @31
    @16
    @15
    @52
    c0
    @7
    eleq2
    ifbid
    ifeq2d
    mpt2eq3dv
    fveq2d
    eqeq2d
    vm
    vn
    weq
    #
    @30
    @40
    @6
    @54
    @29
    @39
    cD
    @54
    vk
    vl
    cN
    cN
    @28
    @38
    @54
    @8
    @27
    @37
    @11
    @54
    @26
    @36
    @16
    @15
    @52
    @42
    @7
    eleq2
    ifbid
    ifeq2d
    mpt2eq3dv
    fveq2d
    eqeq2d
    @52
    @45
    wceq
    #
    @30
    @50
    @6
    @55
    @29
    @49
    cD
    @55
    vk
    vl
    cN
    cN
    @28
    @48
    @55
    @8
    @27
    @47
    @11
    @55
    @26
    @46
    @16
    @15
    @52
    @45
    @7
    eleq2
    ifbid
    ifeq2d
    mpt2eq3dv
    fveq2d
    eqeq2d
    @52
    @13
    wceq
    #
    @30
    @20
    @6
    @56
    @29
    @19
    cD
    @56
    vk
    vl
    cN
    cN
    @28
    @18
    @56
    @8
    @27
    @17
    @11
    @56
    @26
    @14
    @16
    @15
    @52
    @13
    @7
    eleq2
    ifbid
    ifeq2d
    mpt2eq3dv
    fveq2d
    eqeq2d
    @5
    @6
    vk
    vl
    cN
    cN
    @8
    @11
    @15
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    @35
    @1
    @3
    @4
    @6
    @59
    wceq
    @0
    cA
    cB
    cD
    cR
    c.1
    vk
    cH
    cI
    cJ
    cM
    cN
    c.0
    vl
    madufval.a
    madufval.d
    madufval.j
    madufval.b
    madufval.o
    madufval.z
    maducoeval
    3adant1l
    @34
    @58
    cD
    vk
    vl
    cN
    cN
    @33
    @57
    @7
    cN
    wcel
    #
    @9
    cN
    wcel
    #
    wa
    #
    @8
    @32
    @15
    @11
    @31
    wn
    @32
    @15
    wceq
    @62
    @7
    noel
    @31
    @16
    @15
    iffalse
    mp1i
    ifeq2d
    mpt2eq3ia
    fveq2i
    syl6eqr
    @5
    @42
    @13
    wss
    #
    @43
    @13
    @42
    cdif
    wcel
    #
    wa
    #
    wa
    #
    @41
    @51
    @66
    @40
    @50
    @6
    @66
    vk
    vl
    cN
    cN
    vk
    vr
    weq
    #
    @10
    c.0
    @43
    @9
    cM
    co
    #
    cif
    #
    @43
    cI
    cM
    co
    #
    @11
    cR
    cmulr
    cfv
    #
    co
    #
    cR
    cplusg
    cfv
    #
    co
    #
    @38
    cif
    #
    cmpt2
    #
    cD
    cfv
    vk
    vl
    cN
    cN
    @67
    @69
    @38
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    @40
    @50
    @66
    cD
    @73
    cR
    @71
    vk
    vl
    @43
    cH
    cR
    cbs
    cfv
    #
    cN
    @70
    @69
    @11
    @37
    madufval.d
    @80
    eqid
    #
    @73
    eqid
    #
    @71
    eqid
    #
    @0
    @1
    @3
    @4
    @65
    simpl1l
    @5
    cN
    cfn
    wcel
    #
    @65
    @5
    @1
    @84
    @0
    @1
    @3
    @4
    simp1r
    @1
    @84
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    madufval.a
    madufval.b
    matrcl
    simpld
    syl
    #
    adantr
    @66
    @61
    wa
    #
    @10
    c.0
    @68
    @80
    @86
    cR
    crg
    wcel
    #
    c.0
    @80
    wcel
    #
    @86
    @0
    @87
    @5
    @0
    @65
    @61
    @0
    @1
    @3
    @4
    simp1l
    ad2antrr
    cR
    crngring
    syl
    #
    @80
    cR
    c.0
    @81
    madufval.z
    ring0cl
    syl
    #
    @86
    @43
    @9
    @80
    cN
    cN
    cM
    @66
    cN
    cN
    cxp
    #
    @80
    cM
    wf
    #
    @61
    @66
    @1
    cM
    @80
    @91
    cmap
    co
    wcel
    @92
    @0
    @1
    @3
    @4
    @65
    simpl1r
    cA
    cB
    cR
    @80
    cM
    cN
    madufval.a
    @81
    madufval.b
    matbas2i
    cM
    @80
    @91
    elmapi
    3syl
    #
    adantr
    @66
    @43
    cN
    wcel
    @61
    @66
    @43
    cN
    @12
    @64
    @43
    @13
    wcel
    #
    @5
    @63
    @43
    @13
    @42
    eldifi
    ad2antll
    #
    eldifad
    #
    adantr
    @66
    @61
    simpr
    fovrnd
    #
    ifcld
    @86
    @10
    c.1
    c.0
    @80
    @86
    @87
    c.1
    @80
    wcel
    @89
    @80
    cR
    c.1
    @81
    madufval.o
    ringidcl
    syl
    @90
    ifcld
    @66
    @60
    @61
    w3a
    #
    @36
    @16
    @15
    @80
    @98
    @10
    c.0
    @15
    @80
    @66
    @61
    @88
    @60
    @90
    3adant2
    @66
    @60
    @61
    @15
    @80
    wcel
    @66
    @7
    @9
    @80
    cN
    cN
    cM
    @93
    fovrnda
    3impb
    #
    ifcld
    @99
    ifcld
    @66
    @43
    cI
    @80
    cN
    cN
    cM
    @93
    @96
    @2
    @3
    @4
    @65
    simpl2
    fovrnd
    #
    @96
    @2
    @3
    @4
    @65
    simpl3
    @66
    @94
    @43
    cH
    wne
    #
    @95
    @43
    cN
    cH
    eldifsni
    syl
    #
    mdetero
    @66
    @76
    @39
    cD
    @66
    vk
    vl
    cN
    cN
    @75
    @38
    @98
    @67
    @75
    @38
    wceq
    #
    @98
    @67
    wa
    #
    @74
    @15
    @75
    @38
    @98
    @67
    @74
    @15
    wceq
    #
    @98
    @105
    @67
    @74
    @68
    wceq
    #
    @66
    @61
    @106
    @60
    @86
    @74
    @10
    wn
    #
    @68
    c.0
    cif
    #
    @10
    @68
    c.0
    cif
    #
    @73
    co
    #
    @107
    @10
    wo
    #
    @68
    c.0
    cif
    #
    @68
    @86
    @69
    @108
    @72
    @109
    @73
    @69
    @108
    wceq
    @86
    @108
    @69
    @10
    @68
    c.0
    ifnot
    eqcomi
    a1i
    @86
    @72
    @10
    @70
    c.1
    @71
    co
    #
    @70
    c.0
    @71
    co
    #
    cif
    #
    @109
    @10
    @70
    c.1
    c.0
    @71
    ovif2
    @86
    @115
    @10
    @68
    @114
    cif
    @109
    @86
    @10
    @113
    @68
    @114
    @86
    @10
    wa
    @113
    @70
    @68
    @86
    @113
    @70
    wceq
    #
    @10
    @86
    @87
    @70
    @80
    wcel
    #
    @116
    @89
    @66
    @117
    @61
    @100
    adantr
    #
    @80
    cR
    @71
    c.1
    @70
    @81
    @83
    madufval.o
    ringridm
    syl2anc
    adantr
    @10
    @68
    @70
    wceq
    @86
    @9
    cI
    @43
    cM
    oveq2
    adantl
    eqtr4d
    ifeq1da
    @86
    @10
    @114
    c.0
    @68
    @86
    @87
    @117
    @114
    c.0
    wceq
    @89
    @118
    @80
    cR
    @71
    @70
    c.0
    @81
    @83
    madufval.z
    ringrz
    syl2anc
    ifeq2d
    eqtrd
    syl5eq
    oveq12d
    @86
    cR
    cmnd
    wcel
    #
    @68
    @80
    wcel
    @107
    @10
    wa
    wn
    #
    @112
    @110
    wceq
    @86
    @87
    @119
    @89
    cR
    ringmnd
    syl
    @97
    @120
    @86
    @107
    @107
    wi
    @120
    @107
    id
    @107
    @10
    imnan
    mpbi
    a1i
    @107
    @10
    @68
    @80
    @73
    cR
    c.0
    @81
    madufval.z
    @82
    mndifsplit
    syl3anc
    @111
    @112
    @68
    wceq
    @86
    @10
    pm2.1
    @111
    @68
    c.0
    iftrue
    mp1i
    3eqtr2d
    3adant2
    @67
    @15
    @68
    @74
    @7
    @43
    @9
    cM
    oveq1
    #
    eqeq2d
    syl5ibrcom
    imp
    @67
    @75
    @74
    wceq
    @98
    @67
    @74
    @38
    iftrue
    adantl
    @104
    @38
    @37
    @15
    @104
    @8
    @11
    @37
    @98
    @67
    @8
    wn
    #
    @98
    @122
    @67
    @43
    cH
    wceq
    #
    wn
    #
    @66
    @60
    @124
    @61
    @66
    @43
    cH
    @102
    neneqd
    3ad2ant1
    @67
    @8
    @123
    @7
    @43
    cH
    eqeq1
    notbid
    syl5ibrcom
    imp
    iffalsed
    @104
    @36
    @16
    @15
    @98
    @67
    @36
    wn
    #
    @98
    @125
    @67
    vr
    vn
    wel
    #
    wn
    #
    @66
    @60
    @127
    @61
    @64
    @127
    @5
    @63
    @43
    @13
    @42
    eldifn
    ad2antll
    3ad2ant1
    @67
    @36
    @126
    @7
    @43
    @42
    eleq1
    notbid
    syl5ibrcom
    imp
    iffalsed
    eqtrd
    3eqtr4d
    @67
    wn
    #
    @103
    @98
    @67
    @74
    @38
    iffalse
    adantl
    pm2.61dan
    mpt2eq3dva
    fveq2d
    @66
    @101
    @79
    @50
    wceq
    @102
    @101
    @78
    @49
    cD
    @101
    vk
    vl
    cN
    cN
    @77
    @48
    @101
    @8
    @77
    @48
    wceq
    @101
    @8
    wa
    #
    @67
    @69
    @11
    cif
    @11
    @77
    @48
    @129
    @67
    @69
    @11
    @129
    @7
    @43
    @129
    @43
    @7
    @8
    @43
    @7
    wne
    @101
    @7
    cH
    @43
    neeq2
    biimparc
    necomd
    neneqd
    iffalsed
    @129
    @67
    @38
    @11
    @69
    @8
    @38
    @11
    wceq
    @101
    @8
    @11
    @37
    iftrue
    adantl
    ifeq2d
    @8
    @48
    @11
    wceq
    @101
    @8
    @11
    @47
    iftrue
    adantl
    3eqtr4d
    @101
    @122
    wa
    #
    @67
    @69
    @37
    cif
    #
    @47
    @77
    @48
    @130
    @67
    @131
    @47
    wceq
    #
    @67
    @132
    @130
    @67
    @16
    @69
    @47
    @131
    @67
    @10
    @15
    @68
    c.0
    @121
    ifeq2d
    @67
    @46
    @16
    @15
    @67
    @46
    @43
    @45
    wcel
    #
    @43
    @44
    wcel
    @133
    vr
    vsnid
    @43
    @44
    @42
    elun2
    ax-mp
    @7
    @43
    @45
    eleq1
    mpbiri
    iftrued
    @67
    @69
    @37
    iftrue
    3eqtr4rd
    adantl
    @128
    @132
    @130
    @128
    @131
    @37
    @47
    @67
    @69
    @37
    iffalse
    @128
    @36
    @46
    @16
    @15
    @128
    @36
    @36
    @67
    wo
    #
    @46
    @128
    @36
    @134
    @36
    @67
    orc
    @67
    @36
    orel2
    impbid2
    @46
    @36
    @7
    @44
    wcel
    #
    wo
    @134
    @7
    @42
    @44
    elun
    @135
    @67
    @36
    vk
    @43
    velsn
    orbi2i
    bitr2i
    syl6bb
    ifbid
    eqtrd
    adantl
    pm2.61dan
    @122
    @77
    @131
    wceq
    @101
    @122
    @67
    @38
    @37
    @69
    @8
    @11
    @37
    iffalse
    ifeq2d
    adantl
    @122
    @48
    @47
    wceq
    @101
    @8
    @11
    @47
    iffalse
    adantl
    3eqtr4d
    pm2.61dan
    mpt2eq3dv
    fveq2d
    syl
    3eqtr3d
    eqeq2d
    biimpd
    @5
    @84
    @13
    cN
    wss
    @13
    cfn
    wcel
    @85
    cN
    @12
    difss
    cN
    @13
    ssfi
    sylancl
    findcard2d
    @19
    @25
    cD
    vk
    vl
    cN
    cN
    @18
    @24
    @62
    @8
    @18
    @24
    wceq
    #
    @8
    @136
    @62
    @8
    @11
    @23
    @18
    @24
    @8
    @10
    @22
    c.1
    c.0
    @8
    @10
    iba
    ifbid
    @8
    @11
    @17
    iftrue
    @8
    @10
    @24
    @23
    wceq
    @21
    @23
    @15
    iftrue
    orcs
    3eqtr4d
    adantl
    @62
    @122
    wa
    #
    @18
    @17
    @16
    @24
    @122
    @18
    @17
    wceq
    @62
    @8
    @11
    @17
    iffalse
    adantl
    @137
    @14
    @16
    @15
    @137
    @60
    @7
    cH
    wne
    #
    wa
    #
    @14
    @60
    @122
    @139
    @61
    @122
    @138
    @60
    @122
    @7
    cH
    @122
    id
    #
    neqned
    anim2i
    adantlr
    @7
    cN
    cH
    eldifsn
    sylibr
    iftrued
    @122
    @16
    @24
    wceq
    @62
    @122
    @10
    @21
    c.0
    @23
    @15
    @8
    @10
    biorf
    @122
    @23
    c.0
    @122
    @22
    c.1
    c.0
    @122
    @8
    @10
    @140
    intnand
    iffalsed
    eqcomd
    ifbieq1d
    adantl
    3eqtrd
    pm2.61dan
    mpt2eq3ia
    fveq2i
    syl6eq
end
