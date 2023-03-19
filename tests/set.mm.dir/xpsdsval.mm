include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "cmpt2.mm"
include "cfv.mm"
include "csca.mm"
include "cprds.mm"
include "cds.mm"
include "cop.mm"
include "cpr.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "crn.mm"
include "cxp.mm"
include "cres.mm"
include "cvv.mm"
include "eqid.mm"
include "xpsval.mm"
include "xpslem.mm"
include "wf1o.mm"
include "xpsff1o2.mm"
include "f1ocnv.mm"
include "mp1i.mm"
include "ovexd.mm"
include "cxmt.mm"
include "wcel.mm"
include "wss.mm"
include "xpsxmetlem.mm"
include "ssid.mm"
include "xmetres2.mm"
include "sylancl.mm"
include "df-ov.mm"
include "wceq.mm"
include "xpsfval.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "opelxpi.mm"
include "wf.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "imasdsf1o.mm"
include "ovresd.mm"
include "eqtrd.mm"
include "wi.mm"
include "f1ocnvfv.mm"
include "sylancr.mm"
include "mpd.mm"
include "oveq12d.mm"
include "c2o.mm"
include "cmpt.mm"
include "cc0.mm"
include "cun.mm"
include "cbs.mm"
include "con0.mm"
include "fvexd.mm"
include "2on.mm"
include "a1i.mm"
include "wfn.mm"
include "xpscfn.mm"
include "eleqtrd.mm"
include "prdsdsval.mm"
include "wrex.mm"
include "wo.mm"
include "c0.mm"
include "c1o.mm"
include "df2o3.mm"
include "rexeqi.mm"
include "0ex.mm"
include "1on.mm"
include "elexi.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq123d.mm"
include "eqeq2d.mm"
include "rexpr.mm"
include "bitri.mm"
include "xpsc0.mm"
include "oveqi.mm"
include "syl5eq.mm"
include "eqtr4d.mm"
include "xpsc1.mm"
include "orbi12d.mm"
include "syl5bb.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "elpr.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "uneq1d.mm"
include "uncom.mm"
include "syl6eq.mm"
include "supeq1d.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "snssd.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "prssi.mm"
include "wor.mm"
include "xrltso.mm"
include "supsn.mm"
include "mp2an.mm"
include "supxrcl.mm"
include "xmetge0.mm"
include "ovex.mm"
include "prid1.mm"
include "supxrub.mm"
include "xrletrd.mm"
include "syl5eqbr.mm"
include "supxrun.mm"
include "3eqtrd.mm"
include "3eqtr3d.mm"

theorem xpsdsval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume xpsds.t: |- T = ( R Xs. S )
  assume xpsds.x: |- X = ( Base ` R )
  assume xpsds.y: |- Y = ( Base ` S )
  assume xpsds.1: |- ( ph -> R e. V )
  assume xpsds.2: |- ( ph -> S e. W )
  assume xpsds.p: |- P = ( dist ` T )
  assume xpsds.m: |- M = ( ( dist ` R ) |` ( X X. X ) )
  assume xpsds.n: |- N = ( ( dist ` S ) |` ( Y X. Y ) )
  assume xpsds.3: |- ( ph -> M e. ( *Met ` X ) )
  assume xpsds.4: |- ( ph -> N e. ( *Met ` Y ) )
  assume xpsds.a: |- ( ph -> A e. X )
  assume xpsds.b: |- ( ph -> B e. Y )
  assume xpsds.c: |- ( ph -> C e. X )
  assume xpsds.d: |- ( ph -> D e. Y )


  assert |- ( ph -> ( <. A , B >. P <. C , D >. ) = sup ( { ( A M C ) , ( B N D ) } , RR* , < ) )

  proof
    wph
    cA
    csn
    cB
    csn
    ccda
    co
    ccnv
    #
    vx
    vy
    cX
    cY
    vx
    cv
    #
    csn
    vy
    cv
    csn
    ccda
    co
    ccnv
    cmpt2
    #
    ccnv
    #
    cfv
    #
    cC
    csn
    cD
    csn
    ccda
    co
    ccnv
    #
    @3
    cfv
    #
    cP
    co
    #
    @0
    @5
    cR
    csca
    cfv
    #
    cR
    csn
    cS
    csn
    ccda
    co
    ccnv
    #
    cprds
    co
    #
    cds
    cfv
    #
    co
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cP
    co
    cA
    cC
    cM
    co
    #
    cB
    cD
    cN
    co
    #
    cpr
    #
    cxr
    clt
    csup
    #
    wph
    @7
    @0
    @5
    @11
    @2
    crn
    #
    @19
    cxp
    cres
    #
    co
    @12
    wph
    cX
    cY
    cxp
    #
    cP
    @10
    cT
    @20
    @3
    @19
    @0
    @5
    cvv
    wph
    vx
    vy
    cR
    cS
    cT
    @10
    @2
    @8
    cV
    cW
    cX
    cY
    xpsds.t
    xpsds.x
    xpsds.y
    xpsds.1
    xpsds.2
    @2
    eqid
    #
    @8
    eqid
    #
    @10
    eqid
    #
    xpsval
    wph
    vx
    vy
    cR
    cS
    cT
    @10
    @2
    @8
    cV
    cW
    cX
    cY
    xpsds.t
    xpsds.x
    xpsds.y
    xpsds.1
    xpsds.2
    @22
    @23
    @24
    xpslem
    #
    @21
    @19
    @2
    wf1o
    #
    @19
    @21
    @3
    wf1o
    wph
    vx
    vy
    cX
    cY
    @2
    @22
    xpsff1o2
    #
    @21
    @19
    @2
    f1ocnv
    mp1i
    wph
    @8
    @9
    cprds
    ovexd
    @20
    eqid
    xpsds.p
    wph
    @11
    @19
    cxmt
    cfv
    #
    wcel
    @19
    @19
    wss
    @20
    @28
    wcel
    wph
    vx
    vy
    cP
    cR
    cS
    cT
    cM
    cN
    cV
    cW
    cX
    cY
    xpsds.t
    xpsds.x
    xpsds.y
    xpsds.1
    xpsds.2
    xpsds.p
    xpsds.m
    xpsds.n
    xpsds.3
    xpsds.4
    xpsxmetlem
    @19
    ssid
    @11
    @19
    @19
    xmetres2
    sylancl
    wph
    @13
    @2
    cfv
    #
    @0
    @19
    wph
    @29
    cA
    cB
    @2
    co
    #
    @0
    cA
    cB
    @2
    df-ov
    wph
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    @30
    @0
    wceq
    xpsds.a
    xpsds.b
    vx
    vy
    cX
    cY
    @2
    cA
    cB
    @22
    xpsfval
    syl2anc
    syl5eqr
    #
    wph
    @13
    @21
    wcel
    #
    @29
    @19
    wcel
    wph
    @31
    @32
    @34
    xpsds.a
    xpsds.b
    cA
    cB
    cX
    cY
    opelxpi
    syl2anc
    #
    @21
    @19
    @13
    @2
    @26
    @21
    @19
    @2
    wf
    @27
    @21
    @19
    @2
    f1of
    ax-mp
    #
    ffvelrni
    syl
    eqeltrrd
    #
    wph
    @14
    @2
    cfv
    #
    @5
    @19
    wph
    @38
    cC
    cD
    @2
    co
    #
    @5
    cC
    cD
    @2
    df-ov
    wph
    cC
    cX
    wcel
    #
    cD
    cY
    wcel
    #
    @39
    @5
    wceq
    xpsds.c
    xpsds.d
    vx
    vy
    cX
    cY
    @2
    cC
    cD
    @22
    xpsfval
    syl2anc
    syl5eqr
    #
    wph
    @14
    @21
    wcel
    #
    @38
    @19
    wcel
    wph
    @40
    @41
    @43
    xpsds.c
    xpsds.d
    cC
    cD
    cX
    cY
    opelxpi
    syl2anc
    #
    @21
    @19
    @14
    @2
    @36
    ffvelrni
    syl
    eqeltrrd
    #
    imasdsf1o
    wph
    @0
    @5
    @11
    @19
    @37
    @45
    ovresd
    eqtrd
    wph
    @4
    @13
    @6
    @14
    cP
    wph
    @29
    @0
    wceq
    #
    @4
    @13
    wceq
    #
    @33
    wph
    @26
    @34
    @46
    @47
    wi
    @27
    @35
    @21
    @19
    @13
    @0
    @2
    f1ocnvfv
    sylancr
    mpd
    wph
    @38
    @5
    wceq
    #
    @6
    @14
    wceq
    #
    @42
    wph
    @26
    @43
    @48
    @49
    wi
    @27
    @44
    @21
    @19
    @14
    @5
    @2
    f1ocnvfv
    sylancr
    mpd
    oveq12d
    wph
    @12
    vk
    c2o
    vk
    cv
    #
    @0
    cfv
    #
    @50
    @5
    cfv
    #
    @50
    @9
    cfv
    #
    cds
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cc0
    csn
    #
    cun
    #
    cxr
    clt
    csup
    @58
    @17
    cun
    #
    cxr
    clt
    csup
    #
    @18
    wph
    vk
    @10
    cbs
    cfv
    #
    @11
    @9
    @8
    @0
    @5
    c2o
    cvv
    con0
    @10
    @24
    @62
    eqid
    wph
    cR
    csca
    fvexd
    c2o
    con0
    wcel
    wph
    2on
    a1i
    wph
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    @9
    c2o
    wfn
    xpsds.1
    xpsds.2
    cR
    cS
    cV
    cW
    xpscfn
    syl2anc
    wph
    @0
    @19
    @62
    @37
    @25
    eleqtrd
    wph
    @5
    @19
    @62
    @45
    @25
    eleqtrd
    @11
    eqid
    prdsdsval
    wph
    cxr
    @59
    @60
    clt
    wph
    @59
    @17
    @58
    cun
    @60
    wph
    @57
    @17
    @58
    wph
    vx
    @57
    @17
    wph
    @1
    @55
    wceq
    #
    vk
    c2o
    wrex
    #
    @1
    @15
    wceq
    #
    @1
    @16
    wceq
    #
    wo
    #
    @1
    @57
    wcel
    #
    @1
    @17
    wcel
    @66
    @1
    c0
    @0
    cfv
    #
    c0
    @5
    cfv
    #
    c0
    @9
    cfv
    #
    cds
    cfv
    #
    co
    #
    wceq
    #
    @1
    c1o
    @0
    cfv
    #
    c1o
    @5
    cfv
    #
    c1o
    @9
    cfv
    #
    cds
    cfv
    #
    co
    #
    wceq
    #
    wo
    #
    wph
    @69
    @66
    @65
    vk
    c0
    c1o
    cpr
    #
    wrex
    @83
    @65
    vk
    c2o
    @84
    df2o3
    rexeqi
    @65
    @76
    @82
    vk
    c0
    c1o
    0ex
    c1o
    con0
    1on
    elexi
    @50
    c0
    wceq
    #
    @55
    @75
    @1
    @85
    @51
    @71
    @52
    @72
    @54
    @74
    @85
    @53
    @73
    cds
    @50
    c0
    @9
    fveq2
    fveq2d
    @50
    c0
    @0
    fveq2
    @50
    c0
    @5
    fveq2
    oveq123d
    eqeq2d
    @50
    c1o
    wceq
    #
    @55
    @81
    @1
    @86
    @51
    @77
    @52
    @78
    @54
    @80
    @86
    @53
    @79
    cds
    @50
    c1o
    @9
    fveq2
    fveq2d
    @50
    c1o
    @0
    fveq2
    @50
    c1o
    @5
    fveq2
    oveq123d
    eqeq2d
    rexpr
    bitri
    wph
    @76
    @67
    @82
    @68
    wph
    @75
    @15
    @1
    wph
    @75
    cA
    cC
    cR
    cds
    cfv
    #
    co
    #
    @15
    wph
    @71
    cA
    @72
    cC
    @74
    @87
    wph
    @73
    cR
    cds
    wph
    @63
    @73
    cR
    wceq
    xpsds.1
    cR
    cS
    cV
    xpsc0
    syl
    fveq2d
    wph
    @31
    @71
    cA
    wceq
    xpsds.a
    cA
    cB
    cX
    xpsc0
    syl
    wph
    @40
    @72
    cC
    wceq
    xpsds.c
    cC
    cD
    cX
    xpsc0
    syl
    oveq123d
    wph
    @15
    cA
    cC
    @87
    cX
    cX
    cxp
    cres
    #
    co
    @88
    cM
    @89
    cA
    cC
    xpsds.m
    oveqi
    wph
    cA
    cC
    @87
    cX
    xpsds.a
    xpsds.c
    ovresd
    syl5eq
    eqtr4d
    eqeq2d
    wph
    @81
    @16
    @1
    wph
    @81
    cB
    cD
    cS
    cds
    cfv
    #
    co
    #
    @16
    wph
    @77
    cB
    @78
    cD
    @80
    @90
    wph
    @79
    cS
    cds
    wph
    @64
    @79
    cS
    wceq
    xpsds.2
    cR
    cS
    cW
    xpsc1
    syl
    fveq2d
    wph
    @32
    @77
    cB
    wceq
    xpsds.b
    cA
    cB
    cY
    xpsc1
    syl
    wph
    @41
    @78
    cD
    wceq
    xpsds.d
    cC
    cD
    cY
    xpsc1
    syl
    oveq123d
    wph
    @16
    cB
    cD
    @90
    cY
    cY
    cxp
    cres
    #
    co
    @91
    cN
    @92
    cB
    cD
    xpsds.n
    oveqi
    wph
    cB
    cD
    @90
    cY
    xpsds.b
    xpsds.d
    ovresd
    syl5eq
    eqtr4d
    eqeq2d
    orbi12d
    syl5bb
    @1
    cvv
    wcel
    @70
    @66
    wb
    vx
    vex
    #
    vk
    c2o
    @55
    @1
    @56
    cvv
    @56
    eqid
    elrnmpt
    ax-mp
    @1
    @15
    @16
    @93
    elpr
    3bitr4g
    eqrdv
    uneq1d
    @17
    @58
    uncom
    syl6eq
    supeq1d
    wph
    @58
    cxr
    wss
    @17
    cxr
    wss
    #
    @58
    cxr
    clt
    csup
    #
    @18
    cle
    wbr
    @61
    @18
    wceq
    wph
    cc0
    cxr
    cc0
    cxr
    wcel
    #
    wph
    0xr
    a1i
    #
    snssd
    wph
    @15
    cxr
    wcel
    #
    @16
    cxr
    wcel
    #
    @94
    wph
    cM
    cX
    cxmt
    cfv
    wcel
    #
    @31
    @40
    @98
    xpsds.3
    xpsds.a
    xpsds.c
    cA
    cC
    cM
    cX
    xmetcl
    syl3anc
    #
    wph
    cN
    cY
    cxmt
    cfv
    wcel
    @32
    @41
    @99
    xpsds.4
    xpsds.b
    xpsds.d
    cB
    cD
    cN
    cY
    xmetcl
    syl3anc
    @15
    @16
    cxr
    prssi
    syl2anc
    #
    wph
    @95
    cc0
    @18
    cle
    cxr
    clt
    wor
    @96
    @95
    cc0
    wceq
    xrltso
    0xr
    cxr
    cc0
    clt
    supsn
    mp2an
    wph
    cc0
    @15
    @18
    @97
    @101
    wph
    @94
    @18
    cxr
    wcel
    @102
    @17
    supxrcl
    syl
    wph
    @100
    @31
    @40
    cc0
    @15
    cle
    wbr
    xpsds.3
    xpsds.a
    xpsds.c
    cA
    cC
    cM
    cX
    xmetge0
    syl3anc
    wph
    @94
    @15
    @17
    wcel
    @15
    @18
    cle
    wbr
    @102
    @15
    @16
    cA
    cC
    cM
    ovex
    prid1
    @17
    @15
    supxrub
    sylancl
    xrletrd
    syl5eqbr
    @58
    @17
    supxrun
    syl3anc
    3eqtrd
    3eqtr3d
end
