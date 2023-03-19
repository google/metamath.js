include "cmfs.mm"
include "wcel.mm"
include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cmpst.mm"
include "cmcls.mm"
include "co.mm"
include "wss.mm"
include "ccnv.mm"
include "cmex.mm"
include "cfn.mm"
include "cxp.mm"
include "cdif.mm"
include "cun.mm"
include "w3a.mm"
include "eqid.mm"
include "mthmsta.mm"
include "simpr.mm"
include "sseldi.mm"
include "elmpst.mm"
include "sylib.mm"
include "simp1d.mm"
include "simpld.mm"
include "difssd.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "simprd.mm"
include "cnvdif.mm"
include "cmvar.mm"
include "cid.mm"
include "cnvxp.mm"
include "cnvi.mm"
include "difeq12i.mm"
include "eqtri.mm"
include "mdvval.mm"
include "cnveqi.mm"
include "3eqtr4i.mm"
include "a1i.mm"
include "uneq12d.mm"
include "cnvun.mm"
include "3eqtr4g.mm"
include "jca.mm"
include "simp2d.mm"
include "simp3d.mm"
include "syl3anbrc.mm"
include "cv.mm"
include "wrex.mm"
include "elmthm.mm"
include "c1st.mm"
include "simpll.mm"
include "adantr.mm"
include "cin.mm"
include "c2nd.mm"
include "csn.mm"
include "cima.mm"
include "cuni.mm"
include "mppspst.mm"
include "simprl.mm"
include "mpst123.mm"
include "syl.mm"
include "fveq2d.mm"
include "simprr.mm"
include "eqtr3d.mm"
include "eqeltrrd.mm"
include "msrval.mm"
include "3eqtr3d.mm"
include "fvex.mm"
include "inex1.mm"
include "otth.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "unieqd.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "ineq2d.mm"
include "inss1.mm"
include "syl6eqssr.mm"
include "eqidd.mm"
include "oteq123d.mm"
include "eqtrd.mm"
include "simp1bi.mm"
include "ssdifd.mm"
include "unss12.mm"
include "syl2anc.mm"
include "inundif.mm"
include "eqcomi.mm"
include "3sstr4g.mm"
include "ssid.mm"
include "ss2mcls.mm"
include "elmpps.mm"
include "simprbi.mm"
include "sseldd.mm"
include "rexlimddv.mm"
include "sylanbrc.mm"
include "ineq1i.mm"
include "indir.mm"
include "c0.mm"
include "incom.mm"
include "disjdif.mm"
include "0ss.mm"
include "eqsstri.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "3eqtri.mm"
include "oteq1d.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "mthmi.mm"
include "impbid1.mm"

theorem mthmpps
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let cT: class T
  let cU: class U
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vx: setvar x
  assume mthmpps.r: |- R = ( mStRed ` T )
  assume mthmpps.j: |- J = ( mPPSt ` T )
  assume mthmpps.u: |- U = ( mThm ` T )
  assume mthmpps.d: |- D = ( mDV ` T )
  assume mthmpps.v: |- V = ( mVars ` T )
  assume mthmpps.z: |- Z = U. ( V " ( H u. { A } ) )
  assume mthmpps.m: |- M = ( C u. ( D \ ( Z X. Z ) ) )


  assert |- ( T e. mFS -> ( <. C , H , A >. e. U <-> ( <. M , H , A >. e. J /\ ( R ` <. M , H , A >. ) = ( R ` <. C , H , A >. ) ) ) )

  proof
    cT
    cmfs
    wcel
    #
    cC
    cH
    cA
    cotp
    #
    cU
    wcel
    #
    cM
    cH
    cA
    cotp
    #
    cJ
    wcel
    #
    @3
    cR
    cfv
    #
    @1
    cR
    cfv
    #
    wceq
    #
    wa
    #
    @0
    @2
    @8
    @0
    @2
    wa
    #
    @4
    @7
    @9
    @3
    cT
    cmpst
    cfv
    #
    wcel
    #
    cA
    cM
    cH
    cT
    cmcls
    cfv
    #
    co
    #
    wcel
    #
    @4
    @9
    cM
    cD
    wss
    #
    cM
    ccnv
    #
    cM
    wceq
    #
    wa
    cH
    cT
    cmex
    cfv
    #
    wss
    #
    cH
    cfn
    wcel
    #
    wa
    #
    cA
    @18
    wcel
    #
    @11
    @9
    @15
    @17
    @9
    cM
    cC
    cD
    cZ
    cZ
    cxp
    #
    cdif
    #
    cun
    #
    cD
    mthmpps.m
    @9
    cC
    @24
    cD
    @9
    cC
    cD
    wss
    #
    cC
    ccnv
    #
    cC
    wceq
    #
    @9
    @26
    @28
    wa
    #
    @21
    @22
    @9
    @1
    @10
    wcel
    #
    @29
    @21
    @22
    w3a
    @9
    cU
    @10
    @1
    @10
    cT
    cU
    mthmpps.u
    @10
    eqid
    #
    mthmsta
    @0
    @2
    simpr
    #
    sseldi
    #
    cA
    cC
    @10
    cT
    @18
    cH
    cD
    mthmpps.d
    @18
    eqid
    #
    @31
    elmpst
    sylib
    #
    simp1d
    #
    simpld
    @9
    cD
    @23
    difssd
    unssd
    syl5eqss
    #
    @9
    @27
    @24
    ccnv
    #
    cun
    #
    @25
    @16
    cM
    @9
    @27
    cC
    @38
    @24
    @9
    @26
    @28
    @36
    simprd
    @38
    @24
    wceq
    @9
    @38
    cD
    ccnv
    #
    @23
    ccnv
    #
    cdif
    @24
    cD
    @23
    cnvdif
    @40
    cD
    @41
    @23
    cT
    cmvar
    cfv
    #
    @42
    cxp
    #
    cid
    cdif
    #
    ccnv
    #
    @44
    @40
    cD
    @45
    @43
    ccnv
    #
    cid
    ccnv
    #
    cdif
    @44
    @43
    cid
    cnvdif
    @46
    @43
    @47
    cid
    @42
    @42
    cnvxp
    cnvi
    difeq12i
    eqtri
    cD
    @44
    cD
    cT
    @42
    @42
    eqid
    mthmpps.d
    mdvval
    #
    cnveqi
    @48
    3eqtr4i
    cZ
    cZ
    cnvxp
    difeq12i
    eqtri
    a1i
    uneq12d
    @16
    @25
    ccnv
    @39
    cM
    @25
    mthmpps.m
    cnveqi
    cC
    @24
    cnvun
    eqtri
    mthmpps.m
    3eqtr4g
    jca
    @9
    @29
    @21
    @22
    @35
    simp2d
    #
    @9
    @29
    @21
    @22
    @35
    simp3d
    cA
    cM
    @10
    cT
    @18
    cH
    cD
    mthmpps.d
    @34
    @31
    elmpst
    syl3anbrc
    #
    @9
    vx
    cv
    #
    cR
    cfv
    #
    @6
    wceq
    #
    @14
    vx
    cJ
    @9
    @2
    @53
    vx
    cJ
    wrex
    @32
    vx
    cR
    cT
    cU
    cJ
    @1
    mthmpps.r
    mthmpps.j
    mthmpps.u
    elmthm
    sylib
    @9
    @51
    cJ
    wcel
    #
    @53
    wa
    #
    wa
    #
    @51
    c1st
    cfv
    #
    c1st
    cfv
    #
    cH
    @12
    co
    #
    @13
    cA
    @56
    cH
    @12
    cD
    cT
    @18
    cM
    @58
    cH
    mthmpps.d
    @34
    @12
    eqid
    #
    @0
    @2
    @55
    simpll
    @9
    @15
    @55
    @37
    adantr
    @9
    @19
    @55
    @9
    @19
    @20
    @49
    simpld
    adantr
    @56
    @58
    @23
    cin
    #
    @58
    @23
    cdif
    #
    cun
    #
    @25
    @58
    cM
    @56
    @61
    cC
    wss
    @62
    @24
    wss
    @63
    @25
    wss
    @56
    @61
    cC
    @23
    cin
    #
    cC
    @56
    @58
    cV
    @57
    c2nd
    cfv
    #
    @51
    c2nd
    cfv
    #
    csn
    #
    cun
    #
    cima
    #
    cuni
    #
    @70
    cxp
    #
    cin
    #
    @64
    @61
    @56
    @72
    @64
    wceq
    #
    @65
    cH
    wceq
    #
    @66
    cA
    wceq
    #
    @56
    @72
    @65
    @66
    cotp
    #
    @64
    cH
    cA
    cotp
    #
    wceq
    @73
    @74
    @75
    w3a
    @56
    @58
    @65
    @66
    cotp
    #
    cR
    cfv
    #
    @6
    @76
    @77
    @56
    @52
    @79
    @6
    @56
    @51
    @78
    cR
    @56
    @51
    @10
    wcel
    @51
    @78
    wceq
    @56
    cJ
    @10
    @51
    @10
    cT
    cJ
    @31
    mthmpps.j
    mppspst
    @9
    @54
    @53
    simprl
    #
    sseldi
    #
    @10
    cT
    @51
    @31
    mpst123
    syl
    #
    fveq2d
    @9
    @54
    @53
    simprr
    eqtr3d
    @56
    @78
    @10
    wcel
    @79
    @76
    wceq
    @56
    @51
    @78
    @10
    @82
    @81
    eqeltrrd
    @66
    @58
    @10
    cR
    cT
    @65
    cV
    @70
    mthmpps.v
    @31
    mthmpps.r
    @70
    eqid
    msrval
    syl
    @9
    @6
    @77
    wceq
    #
    @55
    @9
    @30
    @83
    @33
    cA
    cC
    @10
    cR
    cT
    cH
    cV
    cZ
    mthmpps.v
    @31
    mthmpps.r
    mthmpps.z
    msrval
    syl
    #
    adantr
    3eqtr3d
    @72
    @65
    @64
    cH
    @66
    cA
    @58
    @71
    @57
    c1st
    fvex
    inex1
    @57
    c2nd
    fvex
    @51
    c2nd
    fvex
    otth
    sylib
    #
    simp1d
    @56
    @71
    @23
    @58
    @56
    @70
    cZ
    @56
    @70
    cV
    cH
    cA
    csn
    #
    cun
    #
    cima
    #
    cuni
    cZ
    @56
    @69
    @88
    @56
    @68
    @87
    cV
    @56
    @65
    cH
    @67
    @86
    @56
    @73
    @74
    @75
    @85
    simp2d
    #
    @56
    @66
    cA
    @56
    @73
    @74
    @75
    @85
    simp3d
    #
    sneqd
    uneq12d
    imaeq2d
    unieqd
    mthmpps.z
    syl6eqr
    sqxpeqd
    ineq2d
    eqtr3d
    cC
    @23
    inss1
    syl6eqssr
    @56
    @58
    cD
    @23
    @56
    @58
    cH
    cA
    cotp
    #
    @10
    wcel
    #
    @58
    cD
    wss
    #
    @56
    @51
    @91
    @10
    @56
    @51
    @78
    @91
    @82
    @56
    @58
    @58
    @65
    cH
    @66
    cA
    @56
    @58
    eqidd
    @89
    @90
    oteq123d
    eqtrd
    #
    @81
    eqeltrrd
    @92
    @93
    @58
    ccnv
    @58
    wceq
    #
    @92
    @93
    @95
    wa
    @21
    @22
    cA
    @58
    @10
    cT
    @18
    cH
    cD
    mthmpps.d
    @34
    @31
    elmpst
    simp1bi
    simpld
    syl
    ssdifd
    @61
    cC
    @62
    @24
    unss12
    syl2anc
    @63
    @58
    @58
    @23
    inundif
    eqcomi
    mthmpps.m
    3sstr4g
    cH
    cH
    wss
    @56
    cH
    ssid
    a1i
    ss2mcls
    @56
    @91
    cJ
    wcel
    #
    cA
    @59
    wcel
    #
    @56
    @51
    @91
    cJ
    @94
    @80
    eqeltrrd
    @96
    @92
    @97
    cA
    @12
    @58
    @10
    cT
    cH
    cJ
    @31
    mthmpps.j
    @60
    elmpps
    simprbi
    syl
    sseldd
    rexlimddv
    cA
    @12
    cM
    @10
    cT
    cH
    cJ
    @31
    mthmpps.j
    @60
    elmpps
    sylanbrc
    @9
    cM
    @23
    cin
    #
    cH
    cA
    cotp
    #
    @77
    @5
    @6
    @9
    @98
    @64
    cH
    cA
    @98
    @64
    wceq
    @9
    @98
    @25
    @23
    cin
    @64
    @24
    @23
    cin
    #
    cun
    #
    @64
    cM
    @25
    @23
    mthmpps.m
    ineq1i
    cC
    @24
    @23
    indir
    @100
    @64
    wss
    @101
    @64
    wceq
    @100
    c0
    @64
    @100
    @23
    @24
    cin
    c0
    @24
    @23
    incom
    @23
    cD
    disjdif
    eqtri
    @64
    0ss
    eqsstri
    @100
    @64
    ssequn2
    mpbi
    3eqtri
    a1i
    oteq1d
    @9
    @11
    @5
    @99
    wceq
    @50
    cA
    cM
    @10
    cR
    cT
    cH
    cV
    cZ
    mthmpps.v
    @31
    mthmpps.r
    mthmpps.z
    msrval
    syl
    @84
    3eqtr4d
    jca
    ex
    cR
    cT
    cU
    cJ
    @3
    @1
    mthmpps.r
    mthmpps.j
    mthmpps.u
    mthmi
    impbid1
end
