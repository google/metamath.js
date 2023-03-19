include "wcel.mm"
include "crn.mm"
include "wf.mm"
include "cv.mm"
include "cs1.mm"
include "cfv.mm"
include "wceq.mm"
include "cdif.mm"
include "wral.mm"
include "cconcat.mm"
include "co.mm"
include "w3a.mm"
include "mrsubf.mm"
include "mrsubcn.mm"
include "ralrimiva.mm"
include "mrsubccat.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "wa.mm"
include "cmpt.mm"
include "cun.mm"
include "cfrmd.mm"
include "cif.mm"
include "ccom.mm"
include "cgsu.mm"
include "cword.mm"
include "mrexval.mm"
include "adantr.mm"
include "s1eq.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "wn.mm"
include "difun2.mm"
include "eleq2i.mm"
include "eldif.mm"
include "bitr3i.mm"
include "simpr2.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "eqcomd.mm"
include "ifeqda.mm"
include "mpteq2dva.mm"
include "coeq1d.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "wss.mm"
include "elun2.mm"
include "simpr1.mm"
include "simpr.mm"
include "s1cld.mm"
include "ad2antrr.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "sylan2.mm"
include "cbvmptv.mm"
include "fmptd.mm"
include "ssid.mm"
include "mrsubfval.mm"
include "sylancl.mm"
include "cmnd.mm"
include "cvv.mm"
include "cmhm.mm"
include "cvrmd.mm"
include "cmcn.mm"
include "eqeltri.mm"
include "cmvar.mm"
include "unex.mm"
include "frmdmnd.mm"
include "ax-mp.mm"
include "a1i.mm"
include "eleqtrd.mm"
include "cplusg.mm"
include "c0.mm"
include "feq23d.mm"
include "mpbid.mm"
include "simpr3.mm"
include "wb.mm"
include "simprl.mm"
include "simprr.mm"
include "cbs.mm"
include "frmdbas.mm"
include "eqcomi.mm"
include "frmdadd.mm"
include "syl2anc.mm"
include "ffvelrn.mm"
include "ad2ant2lr.mm"
include "ad2ant2l.mm"
include "2ralbidva.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "bitr3d.mm"
include "3ad2antr1.mm"
include "chash.mm"
include "cc0.mm"
include "cn0.mm"
include "wrd0.mm"
include "lencl.mm"
include "syl.mm"
include "nn0cnd.mm"
include "0cnd.mm"
include "caddc.mm"
include "addid1d.mm"
include "syl5eleqr.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "ccatlid.mm"
include "syl6eq.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "ccatlen.mm"
include "3eqtrrd.mm"
include "addcanad.mm"
include "hasheq0.mm"
include "sylib.mm"
include "pm3.2i.mm"
include "frmd0.mm"
include "ismhm.mm"
include "mpbiran.mm"
include "syl3anbrc.mm"
include "vrmdf.mm"
include "fcompt.mm"
include "vrmdval.mm"
include "eqtrd.mm"
include "frmdup3lem.mm"
include "syl32anc.mm"
include "3eqtr4rd.mm"
include "cpm.mm"
include "wfn.mm"
include "cmap.mm"
include "mrsubff.mm"
include "ffn.mm"
include "cmrex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "fnfvelrn.mm"
include "eqeltrd.mm"
include "ex.mm"
include "impbid2.mm"

theorem elmrsubrn
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cV: class V
  let cW: class W
  let vc: setvar c
  let vf: setvar f
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let cX: class X
  let cY: class Y
  assume mrsubccat.s: |- S = ( mRSubst ` T )
  assume mrsubccat.r: |- R = ( mREx ` T )
  assume mrsubcn.v: |- V = ( mVR ` T )
  assume mrsubcn.c: |- C = ( mCN ` T )

  disjoint c x
  disjoint c y
  disjoint C c
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint R x
  disjoint R y
  disjoint S c
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint F c
  disjoint F x
  disjoint F y
  disjoint V c
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint c f
  disjoint c r
  disjoint c v
  disjoint f r
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint C f
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint C r
  disjoint v x
  disjoint v y
  disjoint C v
  disjoint R f
  disjoint R r
  disjoint R v
  disjoint S f
  disjoint T f
  disjoint T r
  disjoint T v
  disjoint c w
  disjoint f w
  disjoint F f
  disjoint r w
  disjoint F r
  disjoint v w
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint F w
  disjoint V f
  disjoint V r
  disjoint V v
  disjoint V w
  disjoint W r
  disjoint W v
  disjoint X f
  disjoint X v
  disjoint Y f
  disjoint Y v
  assert |- ( T e. W -> ( F e. ran S <-> ( F : R --> R /\ A. c e. ( C \ V ) ( F ` <" c "> ) = <" c "> /\ A. x e. R A. y e. R ( F ` ( x ++ y ) ) = ( ( F ` x ) ++ ( F ` y ) ) ) ) )

  proof
    cT
    cW
    wcel
    #
    cF
    cS
    crn
    #
    wcel
    #
    cR
    cR
    cF
    wf
    #
    vc
    cv
    #
    cs1
    #
    cF
    cfv
    #
    @5
    wceq
    #
    vc
    cC
    cV
    cdif
    #
    wral
    #
    vx
    cv
    #
    vy
    cv
    #
    cconcat
    co
    #
    cF
    cfv
    #
    @10
    cF
    cfv
    #
    @11
    cF
    cfv
    #
    cconcat
    co
    #
    wceq
    #
    vy
    cR
    wral
    vx
    cR
    wral
    #
    w3a
    #
    @2
    @3
    @9
    @18
    cR
    cS
    cT
    cF
    mrsubccat.s
    mrsubccat.r
    mrsubf
    @2
    @7
    vc
    @8
    cC
    cR
    cS
    cT
    cF
    cV
    @4
    mrsubccat.s
    mrsubccat.r
    mrsubcn.v
    mrsubcn.c
    mrsubcn
    ralrimiva
    @2
    @17
    vx
    vy
    cR
    cR
    @2
    @10
    cR
    wcel
    #
    @11
    cR
    wcel
    #
    @17
    cR
    cS
    cT
    cF
    @10
    @11
    mrsubccat.s
    mrsubccat.r
    mrsubccat
    3expb
    ralrimivva
    3jca
    @0
    @19
    @2
    @0
    @19
    wa
    #
    cF
    vw
    cV
    vw
    cv
    #
    cs1
    #
    cF
    cfv
    #
    cmpt
    #
    cS
    cfv
    #
    @1
    @22
    vr
    cR
    cC
    cV
    cun
    #
    cfrmd
    cfv
    #
    vv
    @28
    vv
    cv
    #
    cV
    wcel
    #
    @30
    @26
    cfv
    #
    @30
    cs1
    #
    cif
    #
    cmpt
    #
    vr
    cv
    #
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    vr
    @28
    cword
    #
    @29
    vv
    @28
    @33
    cF
    cfv
    #
    cmpt
    #
    @36
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    @27
    cF
    @22
    vr
    cR
    @38
    @40
    @44
    @0
    cR
    @40
    wceq
    #
    @19
    cC
    cR
    cT
    cV
    cW
    mrsubcn.c
    mrsubcn.v
    mrsubccat.r
    mrexval
    #
    adantr
    #
    @22
    @37
    @43
    @29
    cgsu
    @22
    @35
    @42
    @36
    @22
    vv
    @28
    @34
    @41
    @22
    @30
    @28
    wcel
    #
    wa
    #
    @31
    @32
    @33
    @41
    @31
    @32
    @41
    wceq
    @50
    vw
    @30
    @25
    @41
    cV
    @26
    @23
    @30
    wceq
    @24
    @33
    cF
    @23
    @30
    s1eq
    fveq2d
    #
    @26
    eqid
    @33
    cF
    fvex
    fvmpt
    adantl
    @50
    @31
    wn
    #
    wa
    @41
    @33
    @22
    @49
    @52
    @41
    @33
    wceq
    #
    @49
    @52
    wa
    #
    @22
    @30
    @8
    wcel
    #
    @53
    @55
    @30
    @28
    cV
    cdif
    #
    wcel
    @54
    @56
    @8
    @30
    cC
    cV
    difun2
    eleq2i
    @30
    @28
    cV
    eldif
    bitr3i
    @22
    @9
    @55
    @53
    @0
    @3
    @9
    @18
    simpr2
    @7
    @53
    vc
    @30
    @8
    @4
    @30
    wceq
    #
    @6
    @41
    @5
    @33
    @57
    @5
    @33
    cF
    @4
    @30
    s1eq
    #
    fveq2d
    @58
    eqeq12d
    rspccva
    sylan
    sylan2br
    anassrs
    eqcomd
    ifeqda
    mpteq2dva
    coeq1d
    oveq2d
    mpteq12dv
    @22
    cV
    cR
    @26
    wf
    #
    cV
    cV
    wss
    #
    @27
    @39
    wceq
    @22
    vv
    cV
    @41
    cR
    @26
    @31
    @22
    @49
    @41
    cR
    wcel
    @30
    cV
    cC
    elun2
    @50
    cR
    cR
    @33
    cF
    @22
    @3
    @49
    @0
    @3
    @9
    @18
    simpr1
    #
    adantr
    @50
    @33
    @40
    cR
    @50
    @30
    @28
    @22
    @49
    simpr
    s1cld
    @0
    @46
    @19
    @49
    @47
    ad2antrr
    #
    eleqtrrd
    ffvelrnd
    #
    sylan2
    vw
    vv
    cV
    @25
    @41
    @51
    cbvmptv
    fmptd
    #
    cV
    ssid
    #
    vv
    cV
    cC
    cR
    cS
    cT
    vr
    @26
    @29
    cV
    mrsubcn.c
    mrsubcn.v
    mrsubccat.r
    mrsubccat.s
    @29
    eqid
    #
    mrsubfval
    sylancl
    @22
    @29
    cmnd
    wcel
    #
    @28
    cvv
    wcel
    #
    @28
    @40
    @42
    wf
    cF
    @29
    @29
    cmhm
    co
    wcel
    #
    cF
    @28
    cvrmd
    cfv
    #
    ccom
    #
    @42
    wceq
    cF
    @45
    wceq
    @67
    @22
    @68
    @67
    cC
    cV
    cC
    cT
    cmcn
    cfv
    cvv
    mrsubcn.c
    cT
    cmcn
    fvex
    eqeltri
    cV
    cT
    cmvar
    cfv
    cvv
    mrsubcn.v
    cT
    cmvar
    fvex
    eqeltri
    #
    unex
    #
    @28
    @29
    cvv
    @66
    frmdmnd
    ax-mp
    #
    a1i
    @68
    @22
    @73
    a1i
    #
    @22
    vv
    @28
    @41
    @40
    @42
    @50
    @41
    cR
    @40
    @63
    @62
    eleqtrd
    @42
    eqid
    fmptd
    @22
    @40
    @40
    cF
    wf
    #
    @10
    @11
    @29
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @14
    @15
    @77
    co
    #
    wceq
    #
    vy
    @40
    wral
    #
    vx
    @40
    wral
    #
    c0
    cF
    cfv
    #
    c0
    wceq
    #
    @69
    @22
    @3
    @76
    @61
    @22
    cR
    cR
    @40
    @40
    cF
    @48
    @48
    feq23d
    mpbid
    #
    @22
    @18
    @83
    @0
    @3
    @9
    @18
    simpr3
    #
    @0
    @9
    @3
    @18
    @83
    wb
    @18
    @0
    @3
    wa
    #
    @81
    vy
    cR
    wral
    #
    vx
    cR
    wral
    @18
    @83
    @88
    @81
    @17
    vx
    vy
    cR
    cR
    @88
    @20
    @21
    wa
    #
    wa
    #
    @79
    @13
    @80
    @16
    @91
    @78
    @12
    cF
    @91
    @10
    @40
    wcel
    @11
    @40
    wcel
    @78
    @12
    wceq
    @91
    @10
    cR
    @40
    @88
    @20
    @21
    simprl
    @88
    @46
    @90
    @0
    @46
    @3
    @47
    adantr
    #
    adantr
    #
    eleqtrd
    @91
    @11
    cR
    @40
    @88
    @20
    @21
    simprr
    @93
    eleqtrd
    @40
    @77
    @28
    @29
    @10
    @11
    @66
    @29
    cbs
    cfv
    #
    @40
    @68
    @94
    @40
    wceq
    @73
    @94
    @28
    @29
    cvv
    @66
    @94
    eqid
    frmdbas
    ax-mp
    eqcomi
    #
    @77
    eqid
    #
    frmdadd
    syl2anc
    fveq2d
    @91
    @14
    @40
    wcel
    @15
    @40
    wcel
    @80
    @16
    wceq
    @91
    @14
    cR
    @40
    @3
    @20
    @14
    cR
    wcel
    @0
    @21
    cR
    cR
    @10
    cF
    ffvelrn
    ad2ant2lr
    @93
    eleqtrd
    @91
    @15
    cR
    @40
    @3
    @21
    @15
    cR
    wcel
    @0
    @20
    cR
    cR
    @11
    cF
    ffvelrn
    ad2ant2l
    @93
    eleqtrd
    @40
    @77
    @28
    @29
    @14
    @15
    @66
    @95
    @96
    frmdadd
    syl2anc
    eqeq12d
    2ralbidva
    @88
    @89
    @82
    vx
    cR
    @40
    @92
    @88
    @81
    vy
    cR
    @40
    @92
    raleqdv
    raleqbidv
    bitr3d
    3ad2antr1
    mpbid
    @22
    @84
    chash
    cfv
    #
    cc0
    wceq
    #
    @85
    @22
    @97
    @97
    cc0
    @22
    @97
    @22
    @84
    @40
    wcel
    #
    @97
    cn0
    wcel
    @22
    @76
    c0
    @40
    wcel
    #
    @99
    @86
    @28
    wrd0
    #
    @40
    @40
    c0
    cF
    ffvelrn
    sylancl
    #
    @28
    @84
    lencl
    syl
    nn0cnd
    #
    @103
    @22
    0cnd
    @22
    @97
    cc0
    caddc
    co
    @97
    @84
    @84
    cconcat
    co
    #
    chash
    cfv
    #
    @97
    @97
    caddc
    co
    #
    @22
    @97
    @103
    addid1d
    @22
    @84
    @104
    chash
    @22
    c0
    cR
    wcel
    #
    @107
    @18
    @84
    @104
    wceq
    #
    @22
    c0
    @40
    cR
    @101
    @48
    syl5eleqr
    #
    @109
    @87
    @17
    @108
    c0
    @11
    cconcat
    co
    #
    cF
    cfv
    #
    @84
    @15
    cconcat
    co
    #
    wceq
    vx
    vy
    c0
    c0
    cR
    cR
    @10
    c0
    wceq
    #
    @13
    @111
    @16
    @112
    @113
    @12
    @110
    cF
    @10
    c0
    @11
    cconcat
    oveq1
    fveq2d
    @113
    @14
    @84
    @15
    cconcat
    @10
    c0
    cF
    fveq2
    oveq1d
    eqeq12d
    @11
    c0
    wceq
    #
    @111
    @84
    @112
    @104
    @114
    @110
    c0
    cF
    @114
    @110
    c0
    c0
    cconcat
    co
    #
    c0
    @11
    c0
    c0
    cconcat
    oveq2
    @100
    @115
    c0
    wceq
    @101
    @28
    c0
    ccatlid
    ax-mp
    syl6eq
    fveq2d
    @114
    @15
    @84
    @84
    cconcat
    @11
    c0
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2va
    syl21anc
    fveq2d
    @22
    @99
    @99
    @105
    @106
    wceq
    @102
    @102
    @28
    @84
    @84
    ccatlen
    syl2anc
    3eqtrrd
    addcanad
    @84
    cvv
    wcel
    @98
    @85
    wb
    c0
    cF
    fvex
    @84
    cvv
    hasheq0
    ax-mp
    sylib
    @69
    @67
    @67
    wa
    @76
    @83
    @85
    w3a
    @67
    @67
    @74
    @74
    pm3.2i
    vx
    vy
    @40
    @40
    @77
    @77
    @29
    @29
    cF
    c0
    c0
    @95
    @95
    @96
    @96
    @28
    @29
    @66
    frmd0
    #
    @116
    ismhm
    mpbiran
    syl3anbrc
    @22
    @71
    vv
    @28
    @30
    @70
    cfv
    #
    cF
    cfv
    #
    cmpt
    #
    @42
    @22
    @76
    @28
    @40
    @70
    wf
    #
    @71
    @119
    wceq
    @86
    @68
    @120
    @73
    @70
    @28
    cvv
    @70
    eqid
    #
    vrmdf
    ax-mp
    vv
    cF
    @70
    @28
    @40
    @40
    fcompt
    sylancl
    @22
    vv
    @28
    @118
    @41
    @50
    @117
    @33
    cF
    @22
    @68
    @49
    @117
    @33
    wceq
    @75
    @30
    @70
    @28
    cvv
    @121
    vrmdval
    sylan
    fveq2d
    mpteq2dva
    eqtrd
    vr
    @42
    @40
    @70
    cF
    @29
    @28
    @29
    cvv
    @66
    @95
    @121
    frmdup3lem
    syl32anc
    3eqtr4rd
    @22
    cS
    cR
    cV
    cpm
    co
    #
    wfn
    #
    @26
    @122
    wcel
    #
    @27
    @1
    wcel
    @0
    @123
    @19
    @0
    @122
    cR
    cR
    cmap
    co
    #
    cS
    wf
    @123
    cR
    cS
    cT
    cV
    cW
    mrsubcn.v
    mrsubccat.r
    mrsubccat.s
    mrsubff
    @122
    @125
    cS
    ffn
    syl
    adantr
    @22
    @59
    @60
    @124
    @64
    @65
    cR
    cvv
    wcel
    cV
    cvv
    wcel
    @59
    @60
    wa
    @124
    cR
    cT
    cmrex
    cfv
    cvv
    mrsubccat.r
    cT
    cmrex
    fvex
    eqeltri
    @72
    cR
    cV
    cV
    @26
    cvv
    cvv
    elpm2r
    mpanl12
    sylancl
    @122
    @26
    cS
    fnfvelrn
    syl2anc
    eqeltrd
    ex
    impbid2
end
