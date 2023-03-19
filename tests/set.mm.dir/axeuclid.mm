include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "wne.mm"
include "cc0.mm"
include "cicc.mm"
include "wrex.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "simpl21.mm"
include "simpl22.mm"
include "jca.mm"
include "simpl23.mm"
include "simpl3r.mm"
include "simprll.mm"
include "simprlr.mm"
include "cc.mm"
include "simp21.mm"
include "ad2antrr.mm"
include "fveecn.mm"
include "sylan.mm"
include "simp3r.mm"
include "mulid2.mm"
include "mul02.mm"
include "oveqan12d.mm"
include "addid1.mm"
include "adantr.mm"
include "eqtrd.mm"
include "syl2anc.mm"
include "wb.mm"
include "oveq2.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "eqeq2d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "adantrd.mm"
include "ralimdva.mm"
include "impancom.mm"
include "simp3l.mm"
include "eqeefv.mm"
include "sylibrd.mm"
include "necon3d.mm"
include "impr.mm"
include "anasss.mm"
include "eqtr2.mm"
include "ralimi.mm"
include "ad2antll.mm"
include "axeuclidlem.mm"
include "syl231anc.mm"
include "exp32.mm"
include "rexlimdvv.mm"
include "brbtwn.mm"
include "syl3anc.mm"
include "simp22.mm"
include "simp23.mm"
include "3anbi12d.mm"
include "r19.26.mm"
include "2rexbii.mm"
include "reeanv.mm"
include "bitri.mm"
include "anbi1i.mm"
include "r19.41vv.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "syl6bbr.mm"
include "simprl.mm"
include "simprr.mm"
include "3anbi123d.mm"
include "r19.26-3.mm"
include "rexbii.mm"
include "3reeanv.mm"
include "2rexbidva.mm"
include "3imtr4d.mm"

theorem axeuclid
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cN: class N
  let vi: setvar i
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint N x
  disjoint N y
  disjoint T x
  disjoint T y
  disjoint A i
  disjoint A p
  disjoint A q
  disjoint A r
  disjoint A s
  disjoint A u
  disjoint i p
  disjoint i q
  disjoint i r
  disjoint i s
  disjoint i u
  disjoint i x
  disjoint i y
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint p u
  disjoint p x
  disjoint p y
  disjoint q r
  disjoint q s
  disjoint q u
  disjoint q x
  disjoint q y
  disjoint r s
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint u x
  disjoint u y
  disjoint B i
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint C i
  disjoint C p
  disjoint C q
  disjoint C r
  disjoint C s
  disjoint C u
  disjoint D i
  disjoint D p
  disjoint D q
  disjoint N i
  disjoint N p
  disjoint N q
  disjoint N r
  disjoint N s
  disjoint N u
  disjoint T i
  disjoint T p
  disjoint T q
  disjoint T r
  disjoint T s
  disjoint T u
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ T e. ( EE ` N ) ) ) -> ( ( D Btwn <. A , T >. /\ D Btwn <. B , C >. /\ A =/= D ) -> E. x e. ( EE ` N ) E. y e. ( EE ` N ) ( B Btwn <. A , x >. /\ C Btwn <. A , y >. /\ T Btwn <. x , y >. ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    cD
    @1
    wcel
    #
    cT
    @1
    wcel
    #
    wa
    #
    w3a
    #
    vi
    cv
    #
    cD
    cfv
    #
    c1
    vp
    cv
    #
    cmin
    co
    #
    @10
    cA
    cfv
    #
    cmul
    co
    #
    @12
    @10
    cT
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @11
    c1
    vq
    cv
    #
    cmin
    co
    @10
    cB
    cfv
    #
    cmul
    co
    @20
    @10
    cC
    cfv
    #
    cmul
    co
    caddc
    co
    #
    wceq
    #
    wa
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    cA
    cD
    wne
    #
    wa
    #
    vq
    cc0
    c1
    cicc
    co
    #
    wrex
    vp
    @30
    wrex
    #
    @21
    c1
    vr
    cv
    #
    cmin
    co
    @14
    cmul
    co
    @32
    @10
    vx
    cv
    #
    cfv
    #
    cmul
    co
    caddc
    co
    wceq
    #
    @22
    c1
    vs
    cv
    #
    cmin
    co
    @14
    cmul
    co
    @36
    @10
    vy
    cv
    #
    cfv
    #
    cmul
    co
    caddc
    co
    wceq
    #
    @16
    c1
    vu
    cv
    #
    cmin
    co
    @34
    cmul
    co
    @40
    @38
    cmul
    co
    caddc
    co
    wceq
    #
    w3a
    vi
    @26
    wral
    #
    vu
    @30
    wrex
    #
    vs
    @30
    wrex
    vr
    @30
    wrex
    #
    vy
    @1
    wrex
    vx
    @1
    wrex
    #
    cD
    cA
    cT
    cop
    cbtwn
    wbr
    #
    cD
    cB
    cC
    cop
    cbtwn
    wbr
    #
    @28
    w3a
    #
    cB
    cA
    @33
    cop
    cbtwn
    wbr
    #
    cC
    cA
    @37
    cop
    cbtwn
    wbr
    #
    cT
    @33
    @37
    cop
    cbtwn
    wbr
    #
    w3a
    #
    vy
    @1
    wrex
    vx
    @1
    wrex
    @9
    @29
    @45
    vp
    vq
    @30
    @30
    @9
    @12
    @30
    wcel
    #
    @20
    @30
    wcel
    #
    wa
    #
    @29
    @45
    @9
    @55
    @29
    wa
    #
    wa
    #
    @2
    @3
    wa
    @4
    @7
    wa
    @53
    @54
    @12
    cc0
    wne
    #
    @18
    @23
    wceq
    #
    vi
    @26
    wral
    #
    @45
    @57
    @2
    @3
    @2
    @3
    @4
    @0
    @8
    @56
    simpl21
    @2
    @3
    @4
    @0
    @8
    @56
    simpl22
    jca
    @57
    @4
    @7
    @2
    @3
    @4
    @0
    @8
    @56
    simpl23
    @6
    @7
    @0
    @5
    @56
    simpl3r
    jca
    @9
    @53
    @54
    @29
    simprll
    @9
    @53
    @54
    @29
    simprlr
    @9
    @55
    @29
    @58
    @9
    @55
    wa
    #
    @27
    @28
    @58
    @61
    @27
    wa
    #
    @12
    cc0
    cA
    cD
    @62
    @12
    cc0
    wceq
    #
    @14
    @11
    wceq
    #
    vi
    @26
    wral
    #
    cA
    cD
    wceq
    #
    @61
    @63
    @27
    @65
    @61
    @63
    wa
    #
    @25
    @64
    vi
    @26
    @67
    @10
    @26
    wcel
    #
    wa
    #
    @19
    @64
    @24
    @69
    @19
    @64
    @69
    @19
    @11
    @14
    wceq
    @64
    @69
    @18
    @14
    @11
    @69
    @18
    @14
    wceq
    #
    c1
    @14
    cmul
    co
    #
    cc0
    @16
    cmul
    co
    #
    caddc
    co
    #
    @14
    wceq
    #
    @69
    @14
    cc
    wcel
    #
    @16
    cc
    wcel
    #
    @74
    @67
    @2
    @68
    @75
    @9
    @2
    @55
    @63
    @0
    @2
    @3
    @4
    @8
    simp21
    #
    ad2antrr
    cA
    @10
    cN
    fveecn
    sylan
    @67
    @7
    @68
    @76
    @9
    @7
    @55
    @63
    @0
    @5
    @6
    @7
    simp3r
    #
    ad2antrr
    cT
    @10
    cN
    fveecn
    sylan
    @75
    @76
    wa
    @73
    @14
    cc0
    caddc
    co
    #
    @14
    @75
    @76
    @71
    @14
    @72
    cc0
    caddc
    @14
    mulid2
    @16
    mul02
    oveqan12d
    @75
    @79
    @14
    wceq
    @76
    @14
    addid1
    adantr
    eqtrd
    syl2anc
    @63
    @70
    @74
    wb
    @61
    @68
    @63
    @18
    @73
    @14
    @63
    @15
    @71
    @17
    @72
    caddc
    @63
    @13
    c1
    @14
    cmul
    @63
    @13
    c1
    cc0
    cmin
    co
    c1
    @12
    cc0
    c1
    cmin
    oveq2
    1m0e1
    syl6eq
    oveq1d
    @12
    cc0
    @16
    cmul
    oveq1
    oveq12d
    eqeq1d
    ad2antlr
    mpbird
    eqeq2d
    @11
    @14
    eqcom
    syl6bb
    biimpd
    adantrd
    ralimdva
    impancom
    @62
    @2
    @6
    @66
    @65
    wb
    @9
    @2
    @55
    @27
    @77
    ad2antrr
    @9
    @6
    @55
    @27
    @0
    @5
    @6
    @7
    simp3l
    #
    ad2antrr
    cA
    cD
    vi
    cN
    eqeefv
    syl2anc
    sylibrd
    necon3d
    impr
    anasss
    @29
    @60
    @9
    @55
    @27
    @60
    @28
    @25
    @59
    vi
    @26
    @11
    @18
    @23
    eqtr2
    ralimi
    adantr
    ad2antll
    vx
    vy
    vu
    cA
    cB
    cC
    @12
    @20
    cT
    vi
    cN
    vs
    vr
    axeuclidlem
    syl231anc
    exp32
    rexlimdvv
    @9
    @48
    @19
    vi
    @26
    wral
    #
    vp
    @30
    wrex
    #
    @24
    vi
    @26
    wral
    #
    vq
    @30
    wrex
    #
    @28
    w3a
    #
    @31
    @9
    @46
    @82
    @47
    @84
    @28
    @9
    @6
    @2
    @7
    @46
    @82
    wb
    @80
    @77
    @78
    vp
    cD
    cA
    cT
    vi
    cN
    brbtwn
    syl3anc
    @9
    @6
    @3
    @4
    @47
    @84
    wb
    @80
    @0
    @2
    @3
    @4
    @8
    simp22
    @0
    @2
    @3
    @4
    @8
    simp23
    vq
    cD
    cB
    cC
    vi
    cN
    brbtwn
    syl3anc
    3anbi12d
    @27
    vq
    @30
    wrex
    vp
    @30
    wrex
    #
    @28
    wa
    @82
    @84
    wa
    #
    @28
    wa
    @31
    @85
    @86
    @87
    @28
    @86
    @81
    @83
    wa
    #
    vq
    @30
    wrex
    vp
    @30
    wrex
    @87
    @27
    @88
    vp
    vq
    @30
    @30
    @19
    @24
    vi
    @26
    r19.26
    2rexbii
    @81
    @83
    vp
    vq
    @30
    @30
    reeanv
    bitri
    anbi1i
    @27
    @28
    vp
    vq
    @30
    @30
    r19.41vv
    @82
    @84
    @28
    df-3an
    3bitr4i
    syl6bbr
    @9
    @52
    @44
    vx
    vy
    @1
    @1
    @9
    @33
    @1
    wcel
    #
    @37
    @1
    wcel
    #
    wa
    #
    wa
    #
    @52
    @35
    vi
    @26
    wral
    #
    vr
    @30
    wrex
    #
    @39
    vi
    @26
    wral
    #
    vs
    @30
    wrex
    #
    @41
    vi
    @26
    wral
    #
    vu
    @30
    wrex
    #
    w3a
    #
    @44
    @92
    @49
    @94
    @50
    @96
    @51
    @98
    @92
    @3
    @2
    @89
    @49
    @94
    wb
    @2
    @3
    @4
    @0
    @8
    @91
    simpl22
    @2
    @3
    @4
    @0
    @8
    @91
    simpl21
    #
    @9
    @89
    @90
    simprl
    #
    vr
    cB
    cA
    @33
    vi
    cN
    brbtwn
    syl3anc
    @92
    @4
    @2
    @90
    @50
    @96
    wb
    @2
    @3
    @4
    @0
    @8
    @91
    simpl23
    @100
    @9
    @89
    @90
    simprr
    #
    vs
    cC
    cA
    @37
    vi
    cN
    brbtwn
    syl3anc
    @92
    @7
    @89
    @90
    @51
    @98
    wb
    @6
    @7
    @0
    @5
    @91
    simpl3r
    @101
    @102
    vu
    cT
    @33
    @37
    vi
    cN
    brbtwn
    syl3anc
    3anbi123d
    @44
    @93
    @95
    @97
    w3a
    #
    vu
    @30
    wrex
    #
    vs
    @30
    wrex
    vr
    @30
    wrex
    @99
    @43
    @104
    vr
    vs
    @30
    @30
    @42
    @103
    vu
    @30
    @35
    @39
    @41
    vi
    @26
    r19.26-3
    rexbii
    2rexbii
    @93
    @95
    @97
    vr
    vs
    vu
    @30
    @30
    @30
    3reeanv
    bitri
    syl6bbr
    2rexbidva
    3imtr4d
end
