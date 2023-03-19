include "cmfs.mm"
include "wcel.mm"
include "crn.mm"
include "cfv.mm"
include "cv.mm"
include "ciun.mm"
include "wceq.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "cmrsub.mm"
include "wrex.mm"
include "wi.mm"
include "eqid.mm"
include "elmsubrn.mm"
include "eleq2i.mm"
include "cmex.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "elrnmpti.mm"
include "bitri.mm"
include "wa.mm"
include "w3a.mm"
include "cmvar.mm"
include "cin.mm"
include "cs1.mm"
include "cmrex.mm"
include "simp2.mm"
include "cmtc.mm"
include "cxp.mm"
include "simp3.mm"
include "mexval.mm"
include "syl6eleq.mm"
include "xp2nd.mm"
include "syl.mm"
include "mrsubvrs.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt3i.mm"
include "xp1st.mm"
include "wf.mm"
include "mrsubf.mm"
include "eleq2s.mm"
include "ffvelrnd.mm"
include "opelxpi.mm"
include "syl6eleqr.mm"
include "mvrsval.mm"
include "op2nd.mm"
include "a1i.mm"
include "rneqd.mm"
include "ineq1d.mm"
include "3eqtrd.mm"
include "iuneq1d.mm"
include "cmty.mm"
include "mvhf.mm"
include "3ad2ant1.mm"
include "inss2.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "adantl.mm"
include "mvhval.mm"
include "cword.mm"
include "s1cli.mm"
include "elexi.mm"
include "op1std.mm"
include "op2ndd.mm"
include "eqtrd.mm"
include "simpl1.mm"
include "mtyf2.mm"
include "adantr.mm"
include "cmcn.mm"
include "cun.mm"
include "elun2.mm"
include "s1cld.mm"
include "mrexval.mm"
include "eleqtrrd.mm"
include "iuneq2dv.mm"
include "3eqtr4d.mm"
include "fveq1.mm"
include "iuneq2d.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "3expia.mm"
include "com23.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "3imp.mm"

theorem msubvrs
  let vx: setvar x
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cH: class H
  let cV: class V
  let cX: class X
  let ve: setvar e
  let vf: setvar f
  assume msubvrs.s: |- S = ( mSubst ` T )
  assume msubvrs.e: |- E = ( mEx ` T )
  assume msubvrs.v: |- V = ( mVars ` T )
  assume msubvrs.h: |- H = ( mVH ` T )

  disjoint E x
  disjoint F x
  disjoint T x
  disjoint X x
  disjoint V x
  disjoint e f
  disjoint e x
  disjoint E e
  disjoint f x
  disjoint E f
  disjoint F f
  disjoint H e
  disjoint H f
  disjoint T e
  disjoint T f
  disjoint X e
  disjoint X f
  disjoint V f
  assert |- ( ( T e. mFS /\ F e. ran S /\ X e. E ) -> ( V ` ( F ` X ) ) = U_ x e. ( V ` X ) ( V ` ( F ` ( H ` x ) ) ) )

  proof
    cT
    cmfs
    wcel
    #
    cF
    cS
    crn
    #
    wcel
    #
    cX
    cE
    wcel
    #
    cX
    cF
    cfv
    #
    cV
    cfv
    #
    vx
    cX
    cV
    cfv
    #
    vx
    cv
    #
    cH
    cfv
    #
    cF
    cfv
    #
    cV
    cfv
    #
    ciun
    #
    wceq
    #
    @2
    cF
    ve
    cE
    ve
    cv
    #
    c1st
    cfv
    #
    @13
    c2nd
    cfv
    #
    vf
    cv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    wceq
    #
    vf
    cT
    cmrsub
    cfv
    #
    crn
    #
    wrex
    #
    @0
    @3
    @12
    wi
    #
    @2
    cF
    vf
    @22
    @19
    cmpt
    #
    crn
    #
    wcel
    @23
    @1
    @26
    cF
    cS
    cT
    ve
    vf
    cE
    @21
    msubvrs.e
    @21
    eqid
    #
    msubvrs.s
    elmsubrn
    eleq2i
    vf
    @22
    @19
    cF
    @25
    @25
    eqid
    ve
    cE
    @18
    cE
    cT
    cmex
    cfv
    cvv
    msubvrs.e
    cT
    cmex
    fvex
    eqeltri
    mptex
    elrnmpti
    bitri
    @0
    @20
    @24
    vf
    @22
    @0
    @16
    @22
    wcel
    #
    wa
    @3
    @20
    @12
    @0
    @28
    @3
    @20
    @12
    wi
    @0
    @28
    @3
    w3a
    #
    @12
    @20
    cX
    @19
    cfv
    #
    cV
    cfv
    #
    vx
    @6
    @8
    @19
    cfv
    #
    cV
    cfv
    #
    ciun
    #
    wceq
    @29
    cX
    c2nd
    cfv
    #
    @16
    cfv
    #
    crn
    #
    cT
    cmvar
    cfv
    #
    cin
    #
    vx
    @35
    crn
    #
    @38
    cin
    #
    @7
    cs1
    #
    @16
    cfv
    #
    crn
    #
    @38
    cin
    #
    ciun
    #
    @31
    @34
    @29
    @28
    @35
    cT
    cmrex
    cfv
    #
    wcel
    #
    @39
    @46
    wceq
    @0
    @28
    @3
    simp2
    #
    @29
    cX
    cT
    cmtc
    cfv
    #
    @47
    cxp
    #
    wcel
    #
    @48
    @29
    cX
    cE
    @51
    @0
    @28
    @3
    simp3
    #
    @47
    cT
    cE
    @50
    @50
    eqid
    #
    msubvrs.e
    @47
    eqid
    #
    mexval
    #
    syl6eleq
    #
    cX
    @50
    @47
    xp2nd
    #
    syl
    vx
    @47
    @21
    cT
    @16
    @38
    @35
    @27
    @38
    eqid
    #
    @55
    mrsubvrs
    syl2anc
    @29
    @31
    cX
    c1st
    cfv
    #
    @36
    cop
    #
    cV
    cfv
    #
    @61
    c2nd
    cfv
    #
    crn
    #
    @38
    cin
    #
    @39
    @29
    @30
    @61
    cV
    @29
    @3
    @30
    @61
    wceq
    @53
    ve
    cX
    @18
    @61
    cE
    @19
    @13
    cX
    wceq
    #
    @14
    @60
    @17
    @36
    @13
    cX
    c1st
    fveq2
    @66
    @15
    @35
    @16
    @13
    cX
    c2nd
    fveq2
    fveq2d
    opeq12d
    @19
    eqid
    #
    @14
    @17
    opex
    #
    fvmpt3i
    syl
    fveq2d
    @29
    @61
    cE
    wcel
    @62
    @65
    wceq
    @29
    @61
    @51
    cE
    @29
    @60
    @50
    wcel
    #
    @36
    @47
    wcel
    @61
    @51
    wcel
    @29
    @52
    @69
    @57
    cX
    @50
    @47
    xp1st
    syl
    @29
    @47
    @47
    @35
    @16
    @29
    @28
    @47
    @47
    @16
    wf
    #
    @49
    @47
    @21
    cT
    @16
    @27
    @55
    mrsubf
    syl
    #
    @29
    @3
    @48
    @53
    @48
    cX
    @51
    cE
    @58
    @56
    eleq2s
    syl
    ffvelrnd
    @60
    @36
    @50
    @47
    opelxpi
    syl2anc
    @56
    syl6eleqr
    cT
    cE
    @38
    cV
    @61
    @59
    msubvrs.e
    msubvrs.v
    mvrsval
    syl
    @29
    @64
    @37
    @38
    @29
    @63
    @36
    @63
    @36
    wceq
    @29
    @60
    @36
    cX
    c1st
    fvex
    @35
    @16
    fvex
    op2nd
    a1i
    rneqd
    ineq1d
    3eqtrd
    @29
    @34
    vx
    @41
    @33
    ciun
    @46
    @29
    vx
    @6
    @41
    @33
    @29
    @3
    @6
    @41
    wceq
    @53
    cT
    cE
    @38
    cV
    cX
    @59
    msubvrs.e
    msubvrs.v
    mvrsval
    syl
    iuneq1d
    @29
    vx
    @41
    @33
    @45
    @29
    @7
    @41
    wcel
    #
    wa
    #
    @33
    @7
    cT
    cmty
    cfv
    #
    cfv
    #
    @43
    cop
    #
    cV
    cfv
    #
    @76
    c2nd
    cfv
    #
    crn
    #
    @38
    cin
    #
    @45
    @73
    @32
    @76
    cV
    @73
    @32
    @8
    c1st
    cfv
    #
    @8
    c2nd
    cfv
    #
    @16
    cfv
    #
    cop
    #
    @76
    @73
    @8
    cE
    wcel
    #
    @32
    @84
    wceq
    @29
    @38
    cE
    cH
    wf
    #
    @7
    @38
    wcel
    #
    @85
    @72
    @0
    @28
    @86
    @3
    cT
    cE
    cH
    @38
    @59
    msubvrs.e
    msubvrs.h
    mvhf
    3ad2ant1
    @41
    @38
    @7
    @40
    @38
    inss2
    sseli
    #
    @38
    cE
    @7
    cH
    ffvelrn
    syl2an
    ve
    @8
    @18
    @84
    cE
    @19
    @13
    @8
    wceq
    #
    @14
    @81
    @17
    @83
    @13
    @8
    c1st
    fveq2
    @89
    @15
    @82
    @16
    @13
    @8
    c2nd
    fveq2
    fveq2d
    opeq12d
    @67
    @68
    fvmpt3i
    syl
    @73
    @81
    @75
    @83
    @43
    @73
    @8
    @75
    @42
    cop
    wceq
    #
    @81
    @75
    wceq
    @73
    @87
    @90
    @72
    @87
    @29
    @88
    adantl
    #
    cT
    cH
    @38
    @7
    @74
    @59
    @74
    eqid
    #
    msubvrs.h
    mvhval
    syl
    #
    @75
    @42
    @8
    @7
    @74
    fvex
    #
    @42
    cvv
    cword
    @7
    s1cli
    elexi
    #
    op1std
    syl
    @73
    @82
    @42
    @16
    @73
    @90
    @82
    @42
    wceq
    @93
    @75
    @42
    @8
    @94
    @95
    op2ndd
    syl
    fveq2d
    opeq12d
    eqtrd
    fveq2d
    @73
    @76
    cE
    wcel
    @77
    @80
    wceq
    @73
    @76
    @51
    cE
    @73
    @75
    @50
    wcel
    @43
    @47
    wcel
    @76
    @51
    wcel
    @73
    @38
    @50
    @7
    @74
    @73
    @0
    @38
    @50
    @74
    wf
    @0
    @28
    @3
    @72
    simpl1
    #
    cT
    @50
    @38
    @74
    @59
    @54
    @92
    mtyf2
    syl
    @91
    ffvelrnd
    @73
    @47
    @47
    @42
    @16
    @29
    @70
    @72
    @71
    adantr
    @73
    @42
    cT
    cmcn
    cfv
    #
    @38
    cun
    #
    cword
    #
    @47
    @73
    @7
    @98
    @73
    @87
    @7
    @98
    wcel
    @91
    @7
    @38
    @97
    elun2
    syl
    s1cld
    @73
    @0
    @47
    @99
    wceq
    @96
    @97
    @47
    cT
    @38
    cmfs
    @97
    eqid
    @59
    @55
    mrexval
    syl
    eleqtrrd
    ffvelrnd
    @75
    @43
    @50
    @47
    opelxpi
    syl2anc
    @56
    syl6eleqr
    cT
    cE
    @38
    cV
    @76
    @59
    msubvrs.e
    msubvrs.v
    mvrsval
    syl
    @73
    @79
    @44
    @38
    @73
    @78
    @43
    @78
    @43
    wceq
    @73
    @75
    @43
    @94
    @42
    @16
    fvex
    op2nd
    a1i
    rneqd
    ineq1d
    3eqtrd
    iuneq2dv
    eqtrd
    3eqtr4d
    @20
    @5
    @31
    @11
    @34
    @20
    @4
    @30
    cV
    cX
    cF
    @19
    fveq1
    fveq2d
    @20
    vx
    @6
    @10
    @33
    @20
    @9
    @32
    cV
    @8
    cF
    @19
    fveq1
    fveq2d
    iuneq2d
    eqeq12d
    syl5ibrcom
    3expia
    com23
    rexlimdva
    syl5bi
    3imp
end
