include "cmpt.mm"
include "co.mm"
include "wbr.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "wral.mm"
include "chom.mm"
include "cixp.mm"
include "c2nd.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "cbs.mm"
include "eqid.mm"
include "ccat.mm"
include "cfunc.mm"
include "funcrcl.mm"
include "syl.mm"
include "simprd.mm"
include "adantr.mm"
include "wrel.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "ffvelrnda.mm"
include "invss.mm"
include "ssbrd.mm"
include "mpd.mm"
include "brxp.mm"
include "simprbi.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptelixpg.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "cbvixpv.mm"
include "syl6eleq.mm"
include "w3a.mm"
include "ccid.mm"
include "csect.mm"
include "simpr2.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfbr.mm"
include "breq123d.mm"
include "rspc.mm"
include "sylc.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "isinv.mm"
include "mpbid.mm"
include "simpld.mm"
include "issect.mm"
include "simp3d.mm"
include "oveq1d.mm"
include "simpr1.mm"
include "funcf2.mm"
include "simpr3.mm"
include "catlid.mm"
include "eqtr2d.mm"
include "nat1st2nd.mm"
include "natcl.mm"
include "simp2d.mm"
include "catass.mm"
include "nati.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "simp1d.mm"
include "catcocl.mm"
include "catrid.mm"
include "3eqtrrd.mm"
include "ralrimivvva.mm"
include "isnat2.mm"
include "mpbir2and.mm"
include "nfv.mm"
include "cbvral.mm"
include "sylib.mm"
include "fucinv.mm"
include "mpbir3and.mm"

theorem invfuc
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cU: class U
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vz: setvar z
  let cV: class V
  assume fuciso.q: |- Q = ( C FuncCat D )
  assume fuciso.b: |- B = ( Base ` C )
  assume fuciso.n: |- N = ( C Nat D )
  assume fuciso.f: |- ( ph -> F e. ( C Func D ) )
  assume fuciso.g: |- ( ph -> G e. ( C Func D ) )
  assume fucinv.i: |- I = ( Inv ` Q )
  assume fucinv.j: |- J = ( Inv ` D )
  assume invfuc.u: |- ( ph -> U e. ( F N G ) )
  assume invfuc.v: |- ( ( ph /\ x e. B ) -> ( U ` x ) ( ( ( 1st ` F ) ` x ) J ( ( 1st ` G ) ` x ) ) X )

  disjoint B x
  disjoint C x
  disjoint D x
  disjoint I x
  disjoint F x
  disjoint G x
  disjoint J x
  disjoint N x
  disjoint ph x
  disjoint Q x
  disjoint U x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C y
  disjoint C z
  disjoint D f
  disjoint D y
  disjoint D z
  disjoint I y
  disjoint F f
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G y
  disjoint G z
  disjoint J y
  disjoint N y
  disjoint V f
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint f ph
  disjoint ph y
  disjoint ph z
  disjoint Q y
  disjoint U y
  disjoint X f
  disjoint X y
  disjoint X z
  assert |- ( ph -> U ( F I G ) ( x e. B |-> X ) )

  proof
    wph
    cU
    vx
    cB
    cX
    cmpt
    #
    cF
    cG
    cI
    co
    wbr
    cU
    cF
    cG
    cN
    co
    wcel
    #
    @0
    cG
    cF
    cN
    co
    wcel
    #
    vy
    cv
    #
    cU
    cfv
    #
    @3
    @0
    cfv
    #
    @3
    cF
    c1st
    cfv
    #
    cfv
    #
    @3
    cG
    c1st
    cfv
    #
    cfv
    #
    cJ
    co
    #
    wbr
    #
    vy
    cB
    wral
    #
    invfuc.u
    wph
    @2
    @0
    vy
    cB
    @9
    @7
    cD
    chom
    cfv
    #
    co
    #
    cixp
    #
    wcel
    vz
    cv
    #
    @0
    cfv
    #
    vf
    cv
    #
    @3
    @16
    cG
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @9
    @16
    @8
    cfv
    #
    cop
    @16
    @6
    cfv
    #
    cD
    cco
    cfv
    #
    co
    #
    co
    #
    @18
    @3
    @16
    cF
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @5
    @9
    @7
    cop
    #
    @23
    @24
    co
    #
    co
    #
    wceq
    #
    vf
    @3
    @16
    cC
    chom
    cfv
    #
    co
    #
    wral
    vz
    cB
    wral
    vy
    cB
    wral
    wph
    @0
    vx
    cB
    vx
    cv
    #
    @8
    cfv
    #
    @36
    @6
    cfv
    #
    @13
    co
    #
    cixp
    #
    @15
    wph
    cX
    @39
    wcel
    #
    vx
    cB
    wral
    #
    @0
    @40
    wcel
    #
    wph
    @41
    vx
    cB
    wph
    @36
    cB
    wcel
    #
    wa
    #
    @36
    cU
    cfv
    #
    cX
    @38
    @37
    @13
    co
    #
    @39
    cxp
    #
    wbr
    #
    @41
    @45
    @46
    cX
    @38
    @37
    cJ
    co
    #
    wbr
    @49
    invfuc.v
    @45
    @50
    @48
    @46
    cX
    @45
    cD
    cbs
    cfv
    #
    cD
    @13
    cJ
    @38
    @37
    @51
    eqid
    #
    fucinv.j
    wph
    cD
    ccat
    wcel
    #
    @44
    wph
    cC
    ccat
    wcel
    #
    @53
    wph
    cF
    cC
    cD
    cfunc
    co
    #
    wcel
    #
    @54
    @53
    wa
    fuciso.f
    cC
    cD
    cF
    funcrcl
    syl
    simprd
    #
    adantr
    wph
    cB
    @51
    @36
    @6
    wph
    cB
    @51
    cC
    cD
    @6
    @27
    fuciso.b
    @52
    wph
    @55
    wrel
    #
    @56
    @6
    @27
    @55
    wbr
    #
    cC
    cD
    relfunc
    #
    fuciso.f
    cF
    @55
    1st2ndbr
    sylancr
    #
    funcf1
    #
    ffvelrnda
    wph
    cB
    @51
    @36
    @8
    wph
    cB
    @51
    cC
    cD
    @8
    @19
    fuciso.b
    @52
    wph
    @58
    cG
    @55
    wcel
    @8
    @19
    @55
    wbr
    #
    @60
    fuciso.g
    cG
    @55
    1st2ndbr
    sylancr
    #
    funcf1
    #
    ffvelrnda
    @13
    eqid
    #
    invss
    ssbrd
    mpd
    @49
    @46
    @47
    wcel
    @41
    @46
    cX
    @47
    @39
    brxp
    simprbi
    syl
    #
    ralrimiva
    cB
    cvv
    wcel
    @43
    @42
    wb
    cB
    cC
    cbs
    cfv
    cvv
    fuciso.b
    cC
    cbs
    fvex
    eqeltri
    vx
    cB
    cX
    @39
    cvv
    mptelixpg
    ax-mp
    sylibr
    vx
    vy
    cB
    @39
    @14
    vx
    vy
    weq
    #
    @37
    @9
    @38
    @7
    @13
    @36
    @3
    @8
    fveq2
    #
    @36
    @3
    @6
    fveq2
    #
    oveq12d
    cbvixpv
    syl6eleq
    wph
    @33
    vy
    vz
    vf
    cB
    cB
    @35
    wph
    @3
    cB
    wcel
    #
    @16
    cB
    wcel
    #
    @18
    @35
    wcel
    #
    w3a
    #
    wa
    #
    @32
    @17
    @21
    @4
    @7
    @9
    cop
    @22
    @24
    co
    co
    #
    @7
    @22
    cop
    @23
    @24
    co
    #
    co
    #
    @5
    @31
    co
    @17
    @76
    @5
    @30
    @22
    @24
    co
    co
    #
    @25
    co
    @26
    @75
    @29
    @78
    @5
    @31
    @75
    @29
    @17
    @16
    cU
    cfv
    #
    @23
    @22
    cop
    @23
    @24
    co
    co
    #
    @29
    @7
    @23
    cop
    #
    @23
    @24
    co
    #
    co
    #
    @17
    @80
    @29
    @82
    @22
    @24
    co
    co
    #
    @77
    co
    @78
    @75
    @84
    @23
    cD
    ccid
    cfv
    #
    cfv
    #
    @29
    @83
    co
    @29
    @75
    @81
    @87
    @29
    @83
    @75
    @80
    @23
    @22
    @13
    co
    wcel
    #
    @17
    @22
    @23
    @13
    co
    wcel
    #
    @81
    @87
    wceq
    #
    @75
    @80
    @17
    @23
    @22
    cD
    csect
    cfv
    #
    co
    wbr
    #
    @88
    @89
    @90
    w3a
    @75
    @92
    @17
    @80
    @22
    @23
    @91
    co
    wbr
    #
    @75
    @80
    @17
    @23
    @22
    cJ
    co
    #
    wbr
    #
    @92
    @93
    wa
    @75
    @72
    @46
    @36
    @0
    cfv
    #
    @50
    wbr
    #
    vx
    cB
    wral
    #
    @95
    wph
    @71
    @72
    @73
    simpr2
    #
    wph
    @98
    @74
    wph
    @97
    vx
    cB
    @45
    @46
    cX
    @96
    @50
    invfuc.v
    @45
    @44
    @41
    @96
    cX
    wceq
    wph
    @44
    simpr
    @67
    vx
    cB
    cX
    @39
    @0
    @0
    eqid
    fvmpt2
    syl2anc
    breqtrrd
    ralrimiva
    #
    adantr
    #
    @97
    @95
    vx
    @16
    cB
    vx
    @80
    @17
    @94
    vx
    @80
    nfcv
    vx
    @94
    nfcv
    vx
    cB
    cX
    @16
    nffvmpt1
    nfbr
    vx
    vz
    weq
    #
    @46
    @80
    @96
    @17
    @50
    @94
    @36
    @16
    cU
    fveq2
    @102
    @38
    @23
    @37
    @22
    cJ
    @36
    @16
    @6
    fveq2
    @36
    @16
    @8
    fveq2
    oveq12d
    @36
    @16
    @0
    fveq2
    breq123d
    rspc
    sylc
    @75
    @51
    cD
    @91
    @80
    @17
    cJ
    @23
    @22
    @52
    fucinv.j
    wph
    @53
    @74
    @57
    adantr
    #
    @75
    cB
    @51
    @16
    @6
    wph
    cB
    @51
    @6
    wf
    @74
    @62
    adantr
    #
    @99
    ffvelrnd
    #
    @75
    cB
    @51
    @16
    @8
    wph
    cB
    @51
    @8
    wf
    @74
    @65
    adantr
    #
    @99
    ffvelrnd
    #
    @91
    eqid
    #
    isinv
    mpbid
    simpld
    @75
    @51
    cD
    @91
    @24
    @86
    @80
    @17
    @13
    @23
    @22
    @52
    @66
    @24
    eqid
    #
    @86
    eqid
    #
    @108
    @103
    @105
    @107
    issect
    mpbid
    #
    simp3d
    oveq1d
    @75
    @51
    cD
    @24
    @86
    @29
    @13
    @7
    @23
    @52
    @66
    @110
    @103
    @75
    cB
    @51
    @3
    @6
    @104
    wph
    @71
    @72
    @73
    simpr1
    #
    ffvelrnd
    #
    @109
    @105
    @75
    @35
    @7
    @23
    @13
    co
    @18
    @28
    @75
    cB
    cC
    cD
    @6
    @27
    @34
    @13
    @3
    @16
    fuciso.b
    @34
    eqid
    #
    @66
    wph
    @59
    @74
    @61
    adantr
    @112
    @99
    funcf2
    wph
    @71
    @72
    @73
    simpr3
    #
    ffvelrnd
    #
    catlid
    eqtr2d
    @75
    @51
    cD
    @24
    @29
    @80
    @13
    @17
    @23
    @7
    @23
    @22
    @52
    @66
    @109
    @103
    @113
    @105
    @107
    @116
    @75
    cU
    cB
    cC
    cD
    @6
    @27
    @13
    @8
    @19
    cN
    @16
    fuciso.n
    @75
    cU
    cC
    cD
    cF
    cG
    cN
    fuciso.n
    wph
    @1
    @74
    invfuc.u
    adantr
    nat1st2nd
    #
    fuciso.b
    @66
    @99
    natcl
    @105
    @75
    @88
    @89
    @90
    @111
    simp2d
    #
    catass
    @75
    @85
    @76
    @17
    @77
    @75
    cU
    cB
    cC
    cD
    @18
    @24
    @6
    @27
    @34
    @8
    @19
    cN
    @3
    @16
    fuciso.n
    @117
    fuciso.b
    @114
    @109
    @112
    @99
    @115
    nati
    oveq2d
    3eqtrd
    oveq1d
    @75
    @51
    cD
    @24
    @5
    @76
    @13
    @17
    @23
    @9
    @7
    @22
    @52
    @66
    @109
    @103
    @75
    cB
    @51
    @3
    @8
    @106
    @112
    ffvelrnd
    #
    @113
    @107
    @75
    @5
    @14
    wcel
    #
    @4
    @7
    @9
    @13
    co
    wcel
    #
    @4
    @5
    @30
    @9
    @24
    co
    co
    #
    @9
    @86
    cfv
    #
    wceq
    #
    @75
    @5
    @4
    @9
    @7
    @91
    co
    wbr
    #
    @120
    @121
    @124
    w3a
    @75
    @4
    @5
    @7
    @9
    @91
    co
    wbr
    #
    @125
    @75
    @11
    @126
    @125
    wa
    @75
    @71
    @98
    @11
    @112
    @101
    @97
    @11
    vx
    @3
    cB
    vx
    @4
    @5
    @10
    vx
    @4
    nfcv
    vx
    @10
    nfcv
    vx
    cB
    cX
    @3
    nffvmpt1
    nfbr
    #
    @68
    @46
    @4
    @96
    @5
    @50
    @10
    @36
    @3
    cU
    fveq2
    @68
    @38
    @7
    @37
    @9
    cJ
    @70
    @69
    oveq12d
    @36
    @3
    @0
    fveq2
    breq123d
    #
    rspc
    sylc
    @75
    @51
    cD
    @91
    @4
    @5
    cJ
    @7
    @9
    @52
    fucinv.j
    @103
    @113
    @119
    @108
    isinv
    mpbid
    simprd
    @75
    @51
    cD
    @91
    @24
    @86
    @5
    @4
    @13
    @9
    @7
    @52
    @66
    @109
    @110
    @108
    @103
    @119
    @113
    issect
    mpbid
    #
    simp1d
    #
    @75
    @51
    cD
    @24
    @4
    @21
    @13
    @7
    @9
    @22
    @52
    @66
    @109
    @103
    @113
    @119
    @107
    @75
    @120
    @121
    @124
    @129
    simp2d
    @75
    @35
    @9
    @22
    @13
    co
    @18
    @20
    @75
    cB
    cC
    cD
    @8
    @19
    @34
    @13
    @3
    @16
    fuciso.b
    @114
    @66
    wph
    @63
    @74
    @64
    adantr
    @112
    @99
    funcf2
    @115
    ffvelrnd
    #
    catcocl
    @105
    @118
    catass
    @75
    @79
    @21
    @17
    @25
    @75
    @79
    @21
    @122
    @9
    @9
    cop
    @22
    @24
    co
    #
    co
    @21
    @123
    @132
    co
    @21
    @75
    @51
    cD
    @24
    @5
    @4
    @13
    @21
    @22
    @9
    @7
    @9
    @52
    @66
    @109
    @103
    @119
    @113
    @119
    @130
    @75
    cU
    cB
    cC
    cD
    @6
    @27
    @13
    @8
    @19
    cN
    @3
    fuciso.n
    @117
    fuciso.b
    @66
    @112
    natcl
    @107
    @131
    catass
    @75
    @122
    @123
    @21
    @132
    @75
    @120
    @121
    @124
    @129
    simp3d
    oveq2d
    @75
    @51
    cD
    @24
    @86
    @21
    @13
    @9
    @22
    @52
    @66
    @110
    @103
    @119
    @109
    @107
    @131
    catrid
    3eqtrd
    oveq2d
    3eqtrrd
    ralrimivvva
    wph
    vy
    vz
    @0
    cB
    cC
    cD
    @24
    vf
    cG
    cF
    @34
    @13
    cN
    fuciso.n
    fuciso.b
    @114
    @66
    @109
    fuciso.g
    fuciso.f
    isnat2
    mpbir2and
    wph
    @98
    @12
    @100
    @97
    @11
    vx
    vy
    cB
    @97
    vy
    nfv
    @127
    @128
    cbvral
    sylib
    wph
    vy
    cB
    cC
    cD
    cQ
    cU
    cF
    cG
    cI
    cJ
    cN
    @0
    fuciso.q
    fuciso.b
    fuciso.n
    fuciso.f
    fuciso.g
    fucinv.i
    fucinv.j
    fucinv
    mpbir3and
end
