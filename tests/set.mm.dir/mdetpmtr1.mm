include "ccrg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "ccom.mm"
include "cfv.mm"
include "cv.mm"
include "cmgp.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cbs.mm"
include "cplusg.mm"
include "cvv.mm"
include "c0g.mm"
include "eqid.mm"
include "crg.mm"
include "simpll.mm"
include "crngring.mm"
include "syl.mm"
include "csymg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "simplr.mm"
include "psgndmfi.mm"
include "fnfun.mm"
include "3syl.mm"
include "simprr.mm"
include "fndm.mm"
include "eleqtrrd.mm"
include "fvco.mm"
include "syl2anc.mm"
include "zrhpsgnelbas.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "zrhcofipsgn.mm"
include "sylan.mm"
include "simpr.mm"
include "mgpbas.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "ad3antrrr.mm"
include "symgfv.mm"
include "cmpt2.mm"
include "w3a.mm"
include "simp1rr.mm"
include "simp2.mm"
include "simp3.mm"
include "simp1rl.mm"
include "matecld.mm"
include "matbas2d.mm"
include "syl5eqel.mm"
include "ad2antrr.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "ringcl.mm"
include "symgbasfi.mm"
include "ovexd.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "gsummulc2.mm"
include "nfcv.mm"
include "fveq2.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ringcmn.mm"
include "wss.mm"
include "ssid.mm"
include "simpllr.mm"
include "simprl.mm"
include "symgov.mm"
include "symgcl.mm"
include "eqeltrrd.mm"
include "wreu.mm"
include "symgfcoeu.mm"
include "gsummptf1o.mm"
include "mdetleib.mm"
include "ad2antrl.mm"
include "ringass.mm"
include "syl13anc.mm"
include "cmul.mm"
include "psgnco.mm"
include "fveq2d.mm"
include "zring.mm"
include "crh.mm"
include "cz.mm"
include "zrhrhm.mm"
include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "1z.mm"
include "neg1z.mm"
include "prssi.mm"
include "mp2an.mm"
include "psgnran.mm"
include "sseldi.mm"
include "zringbas.mm"
include "zringmulr.mm"
include "rhmmul.mm"
include "3eqtrrd.mm"
include "eqtrd.mm"
include "wf.mm"
include "symgbasf.mm"
include "ffun.mm"
include "fdm.mm"
include "eqtr4d.mm"
include "ovmpt2d.mm"
include "mpteq2dva.mm"
include "eqtr3d.mm"
include "3eqtr4d.mm"

theorem mdetpmtr1
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vk: setvar k
  let vl: setvar l
  assume mdetpmtr.a: |- A = ( N Mat R )
  assume mdetpmtr.b: |- B = ( Base ` A )
  assume mdetpmtr.d: |- D = ( N maDet R )
  assume mdetpmtr.g: |- G = ( Base ` ( SymGrp ` N ) )
  assume mdetpmtr.s: |- S = ( pmSgn ` N )
  assume mdetpmtr.z: |- Z = ( ZRHom ` R )
  assume mdetpmtr.t: |- .x. = ( .r ` R )
  assume mdetpmtr1.e: |- E = ( i e. N , j e. N |-> ( ( P ` i ) M j ) )

  disjoint B i
  disjoint B j
  disjoint i j
  disjoint G i
  disjoint G j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint .x. p
  disjoint .x. q
  disjoint p q
  disjoint B p
  disjoint B x
  disjoint i p
  disjoint i x
  disjoint j p
  disjoint j x
  disjoint p x
  disjoint B q
  disjoint q x
  disjoint E p
  disjoint E x
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint i q
  disjoint j q
  disjoint M k
  disjoint M l
  disjoint M p
  disjoint M q
  disjoint M x
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint k p
  disjoint k q
  disjoint k x
  disjoint l p
  disjoint l q
  disjoint l x
  disjoint N k
  disjoint N l
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint P k
  disjoint P l
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint R k
  disjoint R l
  disjoint R p
  disjoint R q
  disjoint R x
  disjoint S p
  disjoint S q
  disjoint Z p
  disjoint Z q
  assert |- ( ( ( R e. CRing /\ N e. Fin ) /\ ( M e. B /\ P e. G ) ) -> ( D ` M ) = ( ( ( Z o. S ) ` P ) .x. ( D ` E ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    #
    cM
    cB
    wcel
    #
    cP
    cG
    wcel
    #
    wa
    #
    wa
    #
    cR
    vp
    cG
    cP
    cZ
    cS
    ccom
    #
    cfv
    #
    vp
    cv
    #
    @7
    cfv
    #
    cR
    cmgp
    cfv
    #
    vx
    cN
    vx
    cv
    #
    @9
    cfv
    #
    @12
    cE
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @8
    cR
    vp
    cG
    @17
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    cM
    cD
    cfv
    #
    @8
    cE
    cD
    cfv
    #
    c.x
    co
    @6
    cG
    cR
    cbs
    cfv
    #
    cR
    cplusg
    cfv
    #
    cR
    c.x
    vp
    cvv
    @17
    @8
    cR
    c0g
    cfv
    #
    @25
    eqid
    #
    @27
    eqid
    #
    @26
    eqid
    mdetpmtr.t
    @6
    @0
    cR
    crg
    wcel
    #
    @0
    @1
    @5
    simpll
    #
    cR
    crngring
    syl
    #
    cG
    cvv
    wcel
    @6
    cG
    cN
    csymg
    cfv
    #
    cbs
    cfv
    cvv
    mdetpmtr.g
    @33
    cbs
    fvex
    eqeltri
    a1i
    @6
    @8
    cP
    cS
    cfv
    #
    cZ
    cfv
    #
    @25
    @6
    cS
    wfun
    #
    cP
    cS
    cdm
    #
    wcel
    @8
    @35
    wceq
    #
    @6
    @1
    cS
    cG
    wfn
    #
    @36
    @0
    @1
    @5
    simplr
    #
    cN
    cS
    cG
    mdetpmtr.s
    mdetpmtr.g
    psgndmfi
    #
    cG
    cS
    fnfun
    3syl
    @6
    cP
    cG
    @37
    @2
    @3
    @4
    simprr
    #
    @6
    @1
    @39
    @37
    cG
    wceq
    @40
    @41
    cG
    cS
    fndm
    3syl
    eleqtrrd
    cP
    cZ
    cS
    fvco
    syl2anc
    #
    @6
    @30
    @1
    @4
    @35
    @25
    wcel
    @32
    @40
    @42
    cG
    cP
    cR
    cS
    cN
    cZ
    mdetpmtr.g
    mdetpmtr.s
    mdetpmtr.z
    zrhpsgnelbas
    syl3anc
    eqeltrd
    #
    @6
    @9
    cG
    wcel
    #
    wa
    #
    @30
    @10
    @25
    wcel
    #
    @16
    @25
    wcel
    #
    @17
    @25
    wcel
    @6
    @30
    @45
    @32
    adantr
    #
    @46
    @10
    @9
    cS
    cfv
    #
    cZ
    cfv
    #
    @25
    @6
    @1
    @45
    @10
    @51
    wceq
    @40
    cG
    @9
    cR
    cS
    cN
    cZ
    mdetpmtr.g
    mdetpmtr.z
    mdetpmtr.s
    zrhcofipsgn
    sylan
    #
    @46
    @30
    @1
    @45
    @51
    @25
    wcel
    @49
    @6
    @1
    @45
    @40
    adantr
    #
    @6
    @45
    simpr
    #
    cG
    @9
    cR
    cS
    cN
    cZ
    mdetpmtr.g
    mdetpmtr.s
    mdetpmtr.z
    zrhpsgnelbas
    syl3anc
    eqeltrd
    #
    @46
    @25
    vx
    @11
    cN
    @14
    @25
    cR
    @11
    @11
    eqid
    #
    @28
    mgpbas
    #
    @0
    @11
    ccmn
    wcel
    #
    @1
    @5
    @45
    cR
    @11
    @56
    crngmgp
    #
    ad3antrrr
    @53
    @46
    @14
    @25
    wcel
    vx
    cN
    @46
    @12
    cN
    wcel
    #
    wa
    #
    cA
    cB
    cR
    @13
    @12
    @25
    cE
    cN
    mdetpmtr.a
    @28
    mdetpmtr.b
    @61
    @45
    @60
    @13
    cN
    wcel
    @6
    @45
    @60
    simplr
    @46
    @60
    simpr
    #
    cN
    cG
    @9
    @33
    @12
    @33
    eqid
    #
    mdetpmtr.g
    symgfv
    syl2anc
    #
    @62
    @6
    cE
    cB
    wcel
    #
    @45
    @60
    @6
    cE
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cP
    cfv
    #
    vj
    cv
    #
    cM
    co
    #
    cmpt2
    #
    cB
    mdetpmtr1.e
    @6
    vi
    vj
    cA
    cB
    @69
    cR
    @25
    cN
    ccrg
    mdetpmtr.a
    @28
    mdetpmtr.b
    @40
    @31
    @6
    @66
    cN
    wcel
    #
    @68
    cN
    wcel
    #
    w3a
    #
    cA
    cB
    cR
    @67
    @68
    @25
    cM
    cN
    mdetpmtr.a
    @28
    mdetpmtr.b
    @73
    @4
    @71
    @67
    cN
    wcel
    @3
    @4
    @2
    @71
    @72
    simp1rr
    @6
    @71
    @72
    simp2
    cN
    cG
    cP
    @33
    @66
    @63
    mdetpmtr.g
    symgfv
    syl2anc
    @6
    @71
    @72
    simp3
    @3
    @4
    @2
    @71
    @72
    simp1rl
    matecld
    matbas2d
    syl5eqel
    #
    ad2antrr
    matecld
    ralrimiva
    gsummptcl
    #
    @25
    cR
    c.x
    @10
    @16
    @28
    mdetpmtr.t
    ringcl
    syl3anc
    @6
    vp
    cG
    @21
    cvv
    cvv
    @17
    @27
    @21
    eqid
    @6
    @1
    cG
    cfn
    wcel
    @40
    cN
    cG
    @33
    @63
    mdetpmtr.g
    symgbasfi
    syl
    #
    @46
    @10
    @16
    c.x
    ovexd
    @6
    cR
    c0g
    fvexd
    fsuppmptdm
    gsummulc2
    @6
    cR
    vq
    cG
    vq
    cv
    #
    @7
    cfv
    #
    @11
    vx
    cN
    @12
    @77
    cfv
    #
    @12
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    cgsu
    co
    #
    cR
    vp
    cG
    cP
    @9
    ccom
    #
    @7
    cfv
    #
    @11
    vx
    cN
    @12
    @85
    cfv
    #
    @12
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    @23
    @20
    @6
    vq
    vp
    cG
    @25
    @83
    cG
    @85
    @25
    cR
    @91
    @27
    vq
    @91
    nfcv
    @28
    @29
    @77
    @85
    wceq
    #
    @78
    @86
    @82
    @90
    c.x
    @77
    @85
    @7
    fveq2
    @93
    @81
    @89
    @11
    cgsu
    @93
    vx
    cN
    @80
    @88
    @93
    @79
    @87
    @12
    cM
    @12
    @77
    @85
    fveq1
    oveq1d
    mpteq2dv
    oveq2d
    oveq12d
    @6
    @30
    cR
    ccmn
    wcel
    @32
    cR
    ringcmn
    syl
    @76
    @25
    @25
    wss
    @6
    @25
    ssid
    a1i
    @6
    @77
    cG
    wcel
    #
    wa
    #
    @30
    @78
    @25
    wcel
    @82
    @25
    wcel
    @83
    @25
    wcel
    @6
    @30
    @94
    @32
    adantr
    #
    @95
    @78
    @77
    cS
    cfv
    cZ
    cfv
    #
    @25
    @95
    @1
    @94
    @78
    @97
    wceq
    @6
    @1
    @94
    @40
    adantr
    #
    @6
    @94
    simpr
    #
    cG
    @77
    cR
    cS
    cN
    cZ
    mdetpmtr.g
    mdetpmtr.z
    mdetpmtr.s
    zrhcofipsgn
    syl2anc
    @95
    @30
    @1
    @94
    @97
    @25
    wcel
    @96
    @98
    @99
    cG
    @77
    cR
    cS
    cN
    cZ
    mdetpmtr.g
    mdetpmtr.s
    mdetpmtr.z
    zrhpsgnelbas
    syl3anc
    eqeltrd
    @95
    @25
    vx
    @11
    cN
    @80
    @57
    @0
    @58
    @1
    @5
    @94
    @59
    ad3antrrr
    @0
    @1
    @5
    @94
    simpllr
    @95
    @80
    @25
    wcel
    vx
    cN
    @95
    @60
    wa
    #
    cA
    cB
    cR
    @79
    @12
    @25
    cM
    cN
    mdetpmtr.a
    @28
    mdetpmtr.b
    @100
    @94
    @60
    @79
    cN
    wcel
    @6
    @94
    @60
    simplr
    @95
    @60
    simpr
    #
    cN
    cG
    @77
    @33
    @12
    @63
    mdetpmtr.g
    symgfv
    syl2anc
    @101
    @6
    @3
    @94
    @60
    @2
    @3
    @4
    simprl
    ad2antrr
    matecld
    ralrimiva
    gsummptcl
    @25
    cR
    c.x
    @78
    @82
    @28
    mdetpmtr.t
    ringcl
    syl3anc
    @6
    @4
    @45
    @85
    cG
    wcel
    #
    @42
    @4
    @45
    wa
    cP
    @9
    @33
    cplusg
    cfv
    #
    co
    @85
    cG
    cN
    cG
    @103
    @33
    cP
    @9
    @63
    mdetpmtr.g
    @103
    eqid
    #
    symgov
    cN
    cG
    @103
    @33
    cP
    @9
    @63
    mdetpmtr.g
    @104
    symgcl
    eqeltrrd
    sylan
    #
    @95
    @1
    @4
    @94
    @93
    vp
    cG
    wreu
    @98
    @6
    @4
    @94
    @42
    adantr
    @99
    cN
    cP
    @77
    cG
    cfn
    vp
    mdetpmtr.g
    symgfcoeu
    syl3anc
    gsummptf1o
    @3
    @23
    @84
    wceq
    @2
    @4
    vx
    cA
    cB
    cD
    cG
    cR
    cS
    c.x
    @11
    cM
    cN
    cZ
    vq
    mdetpmtr.d
    mdetpmtr.a
    mdetpmtr.b
    mdetpmtr.g
    mdetpmtr.z
    mdetpmtr.s
    mdetpmtr.t
    @56
    mdetleib
    ad2antrl
    @6
    @19
    @92
    cR
    cgsu
    @6
    vp
    cG
    @18
    @91
    @46
    @8
    @10
    c.x
    co
    #
    @16
    c.x
    co
    #
    @18
    @91
    @46
    @30
    @8
    @25
    wcel
    #
    @47
    @48
    @107
    @18
    wceq
    @49
    @6
    @108
    @45
    @44
    adantr
    @55
    @75
    @25
    cR
    c.x
    @8
    @10
    @16
    @28
    mdetpmtr.t
    ringass
    syl13anc
    @46
    @106
    @86
    @16
    @90
    c.x
    @46
    @106
    @35
    @51
    c.x
    co
    #
    @86
    @46
    @8
    @35
    @10
    @51
    c.x
    @6
    @38
    @45
    @43
    adantr
    @52
    oveq12d
    @46
    @86
    @85
    cS
    cfv
    #
    cZ
    cfv
    #
    @34
    @50
    cmul
    co
    #
    cZ
    cfv
    #
    @109
    @46
    @1
    @102
    @86
    @111
    wceq
    @53
    @105
    cG
    @85
    cR
    cS
    cN
    cZ
    mdetpmtr.g
    mdetpmtr.z
    mdetpmtr.s
    zrhcofipsgn
    syl2anc
    @46
    @110
    @112
    cZ
    @46
    @1
    @4
    @45
    @110
    @112
    wceq
    @53
    @6
    @4
    @45
    @42
    adantr
    #
    @54
    cN
    cG
    @33
    cP
    @9
    cS
    @63
    mdetpmtr.s
    mdetpmtr.g
    psgnco
    syl3anc
    fveq2d
    @46
    cZ
    zring
    cR
    crh
    co
    wcel
    #
    @34
    cz
    wcel
    @50
    cz
    wcel
    @113
    @109
    wceq
    @6
    @115
    @45
    @6
    @30
    @115
    @32
    cR
    cZ
    mdetpmtr.z
    zrhrhm
    syl
    adantr
    @46
    c1
    c1
    cneg
    #
    cpr
    #
    cz
    @34
    c1
    cz
    wcel
    @116
    cz
    wcel
    @117
    cz
    wss
    1z
    neg1z
    c1
    @116
    cz
    prssi
    mp2an
    #
    @46
    @1
    @4
    @34
    @117
    wcel
    @53
    @114
    cG
    cP
    cS
    cN
    mdetpmtr.g
    mdetpmtr.s
    psgnran
    syl2anc
    sseldi
    @46
    @117
    cz
    @50
    @118
    @46
    @1
    @45
    @50
    @117
    wcel
    @53
    @54
    cG
    @9
    cS
    cN
    mdetpmtr.g
    mdetpmtr.s
    psgnran
    syl2anc
    sseldi
    @34
    @50
    zring
    cR
    cmul
    c.x
    cZ
    cz
    zringbas
    zringmulr
    mdetpmtr.t
    rhmmul
    syl3anc
    3eqtrrd
    eqtrd
    @46
    @15
    @89
    @11
    cgsu
    @46
    vx
    cN
    @14
    @88
    @61
    vi
    vj
    @13
    @12
    cN
    cN
    @69
    @88
    cE
    cvv
    cE
    @70
    wceq
    @61
    mdetpmtr1.e
    a1i
    @61
    @66
    @13
    wceq
    #
    @68
    @12
    wceq
    #
    wa
    #
    wa
    #
    @67
    @87
    @68
    @12
    cM
    @122
    @67
    @13
    cP
    cfv
    #
    @87
    @122
    @66
    @13
    cP
    @61
    @119
    @120
    simprl
    fveq2d
    @122
    @9
    wfun
    #
    @12
    @9
    cdm
    #
    wcel
    @87
    @123
    wceq
    @122
    @45
    cN
    cN
    @9
    wf
    #
    @124
    @6
    @45
    @60
    @121
    simpllr
    #
    cN
    cG
    @9
    @33
    @63
    mdetpmtr.g
    symgbasf
    #
    cN
    cN
    @9
    ffun
    3syl
    @122
    @12
    cN
    @125
    @46
    @60
    @121
    simplr
    @122
    @45
    @126
    @125
    cN
    wceq
    @127
    @128
    cN
    cN
    @9
    fdm
    3syl
    eleqtrrd
    @12
    cP
    @9
    fvco
    syl2anc
    eqtr4d
    @61
    @119
    @120
    simprr
    oveq12d
    @64
    @62
    @61
    @87
    @12
    cM
    ovexd
    ovmpt2d
    mpteq2dva
    oveq2d
    oveq12d
    eqtr3d
    mpteq2dva
    oveq2d
    3eqtr4d
    @6
    @24
    @22
    @8
    c.x
    @6
    @65
    @24
    @22
    wceq
    @74
    vx
    cA
    cB
    cD
    cG
    cR
    cS
    c.x
    @11
    cE
    cN
    cZ
    vp
    mdetpmtr.d
    mdetpmtr.a
    mdetpmtr.b
    mdetpmtr.g
    mdetpmtr.z
    mdetpmtr.s
    mdetpmtr.t
    @56
    mdetleib
    syl
    oveq2d
    3eqtr4d
end
