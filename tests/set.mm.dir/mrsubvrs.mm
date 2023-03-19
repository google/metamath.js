include "crn.mm"
include "wcel.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "cs1.mm"
include "ciun.mm"
include "wceq.mm"
include "cmcn.mm"
include "cun.mm"
include "cword.mm"
include "cvv.mm"
include "c0.mm"
include "n0i.mm"
include "wn.mm"
include "cmrsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "eqid.mm"
include "mrexval.mm"
include "syl.mm"
include "eleq2d.mm"
include "wi.mm"
include "cconcat.mm"
include "co.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "rneq.mm"
include "0in.mm"
include "iuneq1d.mm"
include "0iun.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "mrsub0.mm"
include "wa.mm"
include "uneq1.mm"
include "simpl.mm"
include "simprl.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "s1cld.mm"
include "mrsubccat.mm"
include "syl3anc.mm"
include "wf.mm"
include "mrsubf.mm"
include "ffvelrnd.mm"
include "eleqtrd.mm"
include "ccatrn.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "indir.mm"
include "csn.mm"
include "s1rn.mm"
include "ad2antll.mm"
include "uneq2d.mm"
include "iunxun.mm"
include "wss.mm"
include "simpr.mm"
include "snssd.mm"
include "df-ss.mm"
include "sylib.mm"
include "vex.mm"
include "s1eq.mm"
include "fveq2d.mm"
include "iunxsn.mm"
include "incom.mm"
include "disjsn.mm"
include "sylibr.mm"
include "cdif.mm"
include "eldif.mm"
include "biimpri.mm"
include "sylan.mm"
include "difun2.mm"
include "syl6eleq.mm"
include "mrsubcn.mm"
include "3eqtr4a.mm"
include "pm2.61dan.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "wrdind.mm"
include "com12.mm"
include "sylbid.mm"
include "imp.mm"

theorem mrsubvrs
  let vx: setvar x
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cV: class V
  let cX: class X
  let vc: setvar c
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  assume mrsubco.s: |- S = ( mRSubst ` T )
  assume mrsubvrs.v: |- V = ( mVR ` T )
  assume mrsubvrs.r: |- R = ( mREx ` T )

  disjoint F x
  disjoint S x
  disjoint T x
  disjoint V x
  disjoint X x
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint S c
  disjoint S v
  disjoint S y
  disjoint S z
  disjoint T c
  disjoint T v
  disjoint T y
  disjoint T z
  disjoint V v
  disjoint V y
  disjoint V z
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint X v
  assert |- ( ( F e. ran S /\ X e. R ) -> ( ran ( F ` X ) i^i V ) = U_ x e. ( ran X i^i V ) ( ran ( F ` <" x "> ) i^i V ) )

  proof
    cF
    cS
    crn
    #
    wcel
    #
    cX
    cR
    wcel
    #
    cX
    cF
    cfv
    #
    crn
    #
    cV
    cin
    #
    vx
    cX
    crn
    #
    cV
    cin
    #
    vx
    cv
    #
    cs1
    #
    cF
    cfv
    #
    crn
    #
    cV
    cin
    #
    ciun
    #
    wceq
    #
    @1
    @2
    cX
    cT
    cmcn
    cfv
    #
    cV
    cun
    #
    cword
    #
    wcel
    #
    @14
    @1
    cR
    @17
    cX
    @1
    cT
    cvv
    wcel
    #
    cR
    @17
    wceq
    #
    @1
    @0
    c0
    wceq
    @19
    @0
    cF
    n0i
    @19
    wn
    #
    @0
    c0
    crn
    #
    c0
    @21
    cS
    c0
    @21
    cS
    cT
    cmrsub
    cfv
    c0
    mrsubco.s
    cT
    cmrsub
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    nsyl2
    @15
    cR
    cT
    cV
    cvv
    @15
    eqid
    #
    mrsubvrs.v
    mrsubvrs.r
    mrexval
    syl
    #
    eleq2d
    @18
    @1
    @14
    @1
    vv
    cv
    #
    cF
    cfv
    #
    crn
    #
    cV
    cin
    #
    vx
    @25
    crn
    #
    cV
    cin
    #
    @12
    ciun
    #
    wceq
    #
    wi
    @1
    c0
    cF
    cfv
    #
    crn
    #
    cV
    cin
    #
    c0
    wceq
    #
    wi
    @1
    vy
    cv
    #
    cF
    cfv
    #
    crn
    #
    cV
    cin
    #
    vx
    @37
    crn
    #
    cV
    cin
    #
    @12
    ciun
    #
    wceq
    #
    wi
    @1
    @37
    vz
    cv
    #
    cs1
    #
    cconcat
    co
    #
    cF
    cfv
    #
    crn
    #
    cV
    cin
    #
    vx
    @47
    crn
    #
    cV
    cin
    #
    @12
    ciun
    #
    wceq
    #
    wi
    @1
    @14
    wi
    vv
    vy
    vz
    cX
    @16
    @25
    c0
    wceq
    #
    @32
    @36
    @1
    @55
    @28
    @35
    @31
    c0
    @55
    @27
    @34
    cV
    @55
    @26
    @33
    @25
    c0
    cF
    fveq2
    rneqd
    ineq1d
    @55
    @31
    vx
    c0
    @12
    ciun
    #
    c0
    @55
    vx
    @30
    c0
    @12
    @55
    @30
    c0
    cV
    cin
    #
    c0
    @55
    @29
    c0
    cV
    @55
    @29
    @22
    c0
    @25
    c0
    rneq
    rn0
    syl6eq
    ineq1d
    cV
    0in
    #
    syl6eq
    iuneq1d
    vx
    @12
    0iun
    #
    syl6eq
    eqeq12d
    imbi2d
    @25
    @37
    wceq
    #
    @32
    @44
    @1
    @60
    @28
    @40
    @31
    @43
    @60
    @27
    @39
    cV
    @60
    @26
    @38
    @25
    @37
    cF
    fveq2
    rneqd
    ineq1d
    @60
    vx
    @30
    @42
    @12
    @60
    @29
    @41
    cV
    @25
    @37
    rneq
    ineq1d
    iuneq1d
    eqeq12d
    imbi2d
    @25
    @47
    wceq
    #
    @32
    @54
    @1
    @61
    @28
    @50
    @31
    @53
    @61
    @27
    @49
    cV
    @61
    @26
    @48
    @25
    @47
    cF
    fveq2
    rneqd
    ineq1d
    @61
    vx
    @30
    @52
    @12
    @61
    @29
    @51
    cV
    @25
    @47
    rneq
    ineq1d
    iuneq1d
    eqeq12d
    imbi2d
    @25
    cX
    wceq
    #
    @32
    @14
    @1
    @62
    @28
    @5
    @31
    @13
    @62
    @27
    @4
    cV
    @62
    @26
    @3
    @25
    cX
    cF
    fveq2
    rneqd
    ineq1d
    @62
    vx
    @30
    @7
    @12
    @62
    @29
    @6
    cV
    @25
    cX
    rneq
    ineq1d
    iuneq1d
    eqeq12d
    imbi2d
    @1
    @35
    @57
    c0
    @1
    @34
    c0
    cV
    @1
    @34
    @22
    c0
    @1
    @33
    c0
    cS
    cT
    cF
    mrsubco.s
    mrsub0
    rneqd
    rn0
    syl6eq
    ineq1d
    @58
    syl6eq
    @37
    @17
    wcel
    #
    @45
    @16
    wcel
    #
    wa
    #
    @1
    @44
    @54
    @1
    @65
    @44
    @54
    wi
    @44
    @54
    @1
    @65
    wa
    #
    @40
    @46
    cF
    cfv
    #
    crn
    #
    cV
    cin
    #
    cun
    #
    @43
    @69
    cun
    #
    wceq
    @40
    @43
    @69
    uneq1
    @66
    @50
    @70
    @53
    @71
    @66
    @50
    @39
    @68
    cun
    #
    cV
    cin
    @70
    @66
    @49
    @72
    cV
    @66
    @49
    @38
    @67
    cconcat
    co
    #
    crn
    #
    @72
    @66
    @48
    @73
    @66
    @1
    @37
    cR
    wcel
    @46
    cR
    wcel
    @48
    @73
    wceq
    @1
    @65
    simpl
    #
    @66
    @37
    @17
    cR
    @1
    @63
    @64
    simprl
    #
    @1
    @20
    @65
    @24
    adantr
    #
    eleqtrrd
    #
    @66
    @46
    @17
    cR
    @66
    @45
    @16
    @1
    @63
    @64
    simprr
    #
    s1cld
    #
    @77
    eleqtrrd
    #
    cR
    cS
    cT
    cF
    @37
    @46
    mrsubco.s
    mrsubvrs.r
    mrsubccat
    syl3anc
    rneqd
    @66
    @38
    @17
    wcel
    @67
    @17
    wcel
    @74
    @72
    wceq
    @66
    @38
    cR
    @17
    @66
    cR
    cR
    @37
    cF
    @1
    cR
    cR
    cF
    wf
    @65
    cR
    cS
    cT
    cF
    mrsubco.s
    mrsubvrs.r
    mrsubf
    adantr
    #
    @78
    ffvelrnd
    @77
    eleqtrd
    @66
    @67
    cR
    @17
    @66
    cR
    cR
    @46
    cF
    @82
    @81
    ffvelrnd
    @77
    eleqtrd
    @16
    @38
    @67
    ccatrn
    syl2anc
    eqtrd
    ineq1d
    @39
    @68
    cV
    indir
    syl6eq
    @66
    @53
    @43
    vx
    @45
    csn
    #
    cV
    cin
    #
    @12
    ciun
    #
    cun
    #
    @71
    @66
    @53
    vx
    @42
    @84
    cun
    #
    @12
    ciun
    @86
    @66
    vx
    @52
    @87
    @12
    @66
    @52
    @41
    @83
    cun
    #
    cV
    cin
    @87
    @66
    @51
    @88
    cV
    @66
    @51
    @41
    @46
    crn
    #
    cun
    #
    @88
    @66
    @63
    @46
    @17
    wcel
    @51
    @90
    wceq
    @76
    @80
    @16
    @37
    @46
    ccatrn
    syl2anc
    @66
    @89
    @83
    @41
    @64
    @89
    @83
    wceq
    #
    @1
    @63
    @45
    @16
    s1rn
    ad2antll
    #
    uneq2d
    eqtrd
    ineq1d
    @41
    @83
    cV
    indir
    syl6eq
    iuneq1d
    vx
    @42
    @84
    @12
    iunxun
    syl6eq
    @66
    @85
    @69
    @43
    @66
    @45
    cV
    wcel
    #
    @85
    @69
    wceq
    @66
    @93
    wa
    #
    @85
    vx
    @83
    @12
    ciun
    @69
    @94
    vx
    @84
    @83
    @12
    @94
    @83
    cV
    wss
    @84
    @83
    wceq
    @94
    @45
    cV
    @66
    @93
    simpr
    snssd
    @83
    cV
    df-ss
    sylib
    iuneq1d
    vx
    @45
    @12
    @69
    vz
    vex
    @8
    @45
    wceq
    #
    @11
    @68
    cV
    @95
    @10
    @67
    @95
    @9
    @46
    cF
    @8
    @45
    s1eq
    fveq2d
    rneqd
    ineq1d
    iunxsn
    syl6eq
    @66
    @93
    wn
    #
    wa
    #
    @56
    c0
    @85
    @69
    @59
    @97
    vx
    @84
    c0
    @12
    @97
    @84
    cV
    @83
    cin
    #
    c0
    @83
    cV
    incom
    @97
    @96
    @98
    c0
    wceq
    @66
    @96
    simpr
    cV
    @45
    disjsn
    sylibr
    syl5eq
    #
    iuneq1d
    @97
    @69
    @84
    c0
    @97
    @68
    @83
    cV
    @97
    @68
    @89
    @83
    @97
    @67
    @46
    @97
    @1
    @45
    @15
    cV
    cdif
    #
    wcel
    @67
    @46
    wceq
    @66
    @1
    @96
    @75
    adantr
    @97
    @45
    @16
    cV
    cdif
    #
    @100
    @66
    @64
    @96
    @45
    @101
    wcel
    #
    @79
    @102
    @64
    @96
    wa
    @45
    @16
    cV
    eldif
    biimpri
    sylan
    @15
    cV
    difun2
    syl6eleq
    @15
    cR
    cS
    cT
    cF
    cV
    @45
    mrsubco.s
    mrsubvrs.r
    mrsubvrs.v
    @23
    mrsubcn
    syl2anc
    rneqd
    @66
    @91
    @96
    @92
    adantr
    eqtrd
    ineq1d
    @99
    eqtrd
    3eqtr4a
    pm2.61dan
    uneq2d
    eqtrd
    eqeq12d
    syl5ibr
    expcom
    a2d
    wrdind
    com12
    sylbid
    imp
end
