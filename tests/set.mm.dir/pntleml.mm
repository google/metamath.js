include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cc0.mm"
include "cicc.mm"
include "crab.mm"
include "eqid.mm"
include "wcel.mm"
include "pntlemd.mm"
include "simp3d.mm"
include "wa.mm"
include "c3.mm"
include "cexp.mm"
include "cmul.mm"
include "cmin.mm"
include "wceq.mm"
include "0m0e0.mm"
include "simpr.mm"
include "oveq1d.mm"
include "cn.mm"
include "3nn.mm"
include "0exp.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "rpcnd.mm"
include "mul01d.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtr4a.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "wi.mm"
include "weq.mm"
include "oveq1.mm"
include "raleqdv.mm"
include "cbvrexv.mm"
include "cr.mm"
include "w3a.mm"
include "simplrr.mm"
include "wb.mm"
include "0re.mm"
include "rpred.mm"
include "elicc2.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp1d.mm"
include "cz.mm"
include "simp2d.mm"
include "simplrl.mm"
include "ne0gt0d.mm"
include "elrpd.mm"
include "3z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "rpmulcld.mm"
include "resubcld.mm"
include "ce.mm"
include "c1.mm"
include "caddc.mm"
include "cioo.mm"
include "clt.mm"
include "simprl.mm"
include "1rp.mm"
include "rpaddcl.mm"
include "rpge0d.mm"
include "1re.mm"
include "addge02.mm"
include "jca.mm"
include "wss.mm"
include "cxr.mm"
include "rpxrd.mm"
include "lep1d.mm"
include "df-ico.mm"
include "xrletr.mm"
include "ixxss1.mm"
include "syl2anc.mm"
include "simprr.mm"
include "ssralv.mm"
include "sylc.mm"
include "pntlemp.mm"
include "rpre.mm"
include "adantl.mm"
include "leidd.mm"
include "elicopnf.mm"
include "syl.mm"
include "mpbir2and.mm"
include "fveq2.mm"
include "id.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "recnd.mm"
include "absge0d.mm"
include "0red.mm"
include "abscld.mm"
include "adantr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "syld.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "subge02d.mm"
include "letrd.mm"
include "mpbir3and.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "anassrs.mm"
include "expimpd.mm"
include "breq2.mm"
include "rexralbidv.mm"
include "elrab.mm"
include "cbvralv.mm"
include "syl5bb.mm"
include "syl6bbr.mm"
include "3imtr4g.mm"
include "imp.mm"
include "an32s.mm"
include "pm2.61dane.mm"
include "pntlem3.mm"

theorem pntleml
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let ve: setvar e
  let vk: setvar k
  let cF: class F
  let cL: class L
  let va: setvar a
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vc: setvar c
  let vp: setvar p
  let cC: class C
  let cK: class K
  let vn: setvar n
  let cE: class E
  let cT: class T
  let cY: class Y
  let cU: class U
  assume pntlem3.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntlem3.a: |- ( ph -> A e. RR+ )
  assume pntlem3.A: |- ( ph -> A. x e. RR+ ( abs ` ( ( R ` x ) / x ) ) <_ A )
  assume pntlemp.b: |- ( ph -> B e. RR+ )
  assume pntlemp.l: |- ( ph -> L e. ( 0 (,) 1 ) )
  assume pntlemp.d: |- D = ( A + 1 )
  assume pntlemp.f: |- F = ( ( 1 - ( 1 / D ) ) x. ( ( L / ( ; 3 2 x. B ) ) / ( D ^ 2 ) ) )
  assume pntlemp.K: |- ( ph -> A. e e. ( 0 (,) 1 ) E. x e. RR+ A. k e. ( ( exp ` ( B / e ) ) [,) +oo ) A. y e. ( x (,) +oo ) E. z e. RR+ ( ( y < z /\ ( ( 1 + ( L x. e ) ) x. z ) < ( k x. y ) ) /\ A. u e. ( z [,] ( ( 1 + ( L x. e ) ) x. z ) ) ( abs ` ( ( R ` u ) / u ) ) <_ e ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint a e
  disjoint a k
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint D a
  disjoint e k
  disjoint e u
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint D e
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint D u
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint F y
  disjoint F z
  disjoint R e
  disjoint R k
  disjoint R u
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint L e
  disjoint L k
  disjoint L u
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint ph x
  disjoint ph y
  disjoint B e
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph z
  disjoint r s
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint a v
  disjoint a w
  disjoint e v
  disjoint e w
  disjoint k v
  disjoint k w
  disjoint u v
  disjoint u w
  disjoint D v
  disjoint D w
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F v
  disjoint F w
  disjoint p s
  disjoint p u
  disjoint C p
  disjoint s u
  disjoint C s
  disjoint C u
  disjoint c e
  disjoint c k
  disjoint c x
  disjoint K c
  disjoint e t
  disjoint K e
  disjoint k t
  disjoint K k
  disjoint K t
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint c n
  disjoint c u
  disjoint R c
  disjoint e n
  disjoint e r
  disjoint e s
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint R n
  disjoint r u
  disjoint R r
  disjoint R s
  disjoint t u
  disjoint R t
  disjoint R v
  disjoint R w
  disjoint a c
  disjoint a t
  disjoint E a
  disjoint E c
  disjoint E e
  disjoint E k
  disjoint E t
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint p w
  disjoint p x
  disjoint T p
  disjoint T s
  disjoint T u
  disjoint T w
  disjoint T x
  disjoint a n
  disjoint Y a
  disjoint Y c
  disjoint Y k
  disjoint Y n
  disjoint Y t
  disjoint Y v
  disjoint Y w
  disjoint Y y
  disjoint Y z
  disjoint a r
  disjoint a s
  disjoint L c
  disjoint L t
  disjoint L v
  disjoint L w
  disjoint c p
  disjoint c ph
  disjoint p r
  disjoint p t
  disjoint p v
  disjoint p y
  disjoint p ph
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint B v
  disjoint B w
  disjoint U c
  disjoint U t
  disjoint U v
  disjoint U w
  disjoint U z
  assert |- ( ph -> ( x e. RR+ |-> ( ( psi ` x ) / x ) ) ~~>r 1 )

  proof
    wph
    vx
    vy
    vz
    vr
    vt
    cA
    cF
    cR
    vz
    cv
    #
    cR
    cfv
    #
    @0
    cdiv
    co
    #
    cabs
    cfv
    #
    vt
    cv
    #
    cle
    wbr
    #
    vz
    vy
    cv
    #
    cpnf
    cico
    co
    #
    wral
    vy
    crp
    wrex
    #
    vt
    cc0
    cA
    cicc
    co
    #
    crab
    #
    va
    pntlem3.r
    pntlem3.a
    pntlem3.A
    @10
    eqid
    wph
    cL
    crp
    wcel
    cD
    crp
    wcel
    cF
    crp
    wcel
    #
    wph
    cA
    cB
    cD
    cR
    cF
    cL
    va
    pntlem3.r
    pntlem3.a
    pntlemp.b
    pntlemp.l
    pntlemp.d
    pntlemp.f
    pntlemd
    simp3d
    #
    wph
    vr
    cv
    #
    @10
    wcel
    #
    wa
    #
    @13
    cF
    @13
    c3
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @10
    wcel
    #
    @13
    cc0
    @15
    @13
    cc0
    wceq
    #
    wa
    #
    @18
    @13
    @10
    @21
    cc0
    cc0
    cmin
    co
    cc0
    @18
    @13
    0m0e0
    @21
    @13
    cc0
    @17
    cc0
    cmin
    @15
    @20
    simpr
    #
    @21
    @17
    cF
    cc0
    cmul
    co
    #
    cc0
    @21
    @16
    cc0
    cF
    cmul
    @21
    @16
    cc0
    c3
    cexp
    co
    #
    cc0
    @21
    @13
    cc0
    c3
    cexp
    @22
    oveq1d
    c3
    cn
    wcel
    @24
    cc0
    wceq
    3nn
    c3
    0exp
    ax-mp
    syl6eq
    oveq2d
    wph
    @23
    cc0
    wceq
    @14
    @20
    wph
    cF
    wph
    cF
    @12
    rpcnd
    mul01d
    ad2antrr
    eqtrd
    oveq12d
    @22
    3eqtr4a
    wph
    @14
    @20
    simplr
    eqeltrd
    wph
    @13
    cc0
    wne
    #
    @14
    @19
    wph
    @25
    wa
    #
    @14
    @19
    @26
    @13
    @9
    wcel
    #
    @3
    @13
    cle
    wbr
    #
    vz
    @7
    wral
    #
    vy
    crp
    wrex
    #
    wa
    @18
    @9
    wcel
    #
    vv
    cv
    #
    cR
    cfv
    #
    @32
    cdiv
    co
    #
    cabs
    cfv
    #
    @18
    cle
    wbr
    #
    vv
    vw
    cv
    #
    cpnf
    cico
    co
    #
    wral
    #
    vw
    crp
    wrex
    #
    wa
    #
    @14
    @19
    @26
    @27
    @30
    @41
    wph
    @25
    @27
    @30
    @41
    wi
    @30
    @28
    vz
    vs
    cv
    #
    cpnf
    cico
    co
    #
    wral
    #
    vs
    crp
    wrex
    wph
    @25
    @27
    wa
    #
    wa
    #
    @41
    @29
    @44
    vy
    vs
    crp
    vy
    vs
    weq
    @28
    vz
    @7
    @43
    @6
    @42
    cpnf
    cico
    oveq1
    raleqdv
    cbvrexv
    @46
    @44
    @41
    vs
    crp
    @46
    @42
    crp
    wcel
    #
    @44
    wa
    #
    wa
    #
    @31
    @40
    @49
    @31
    @18
    cr
    wcel
    #
    cc0
    @18
    cle
    wbr
    #
    @18
    cA
    cle
    wbr
    #
    @49
    @13
    @17
    @49
    @13
    cr
    wcel
    #
    cc0
    @13
    cle
    wbr
    #
    @13
    cA
    cle
    wbr
    #
    @49
    @27
    @53
    @54
    @55
    w3a
    #
    wph
    @25
    @27
    @48
    simplrr
    @49
    cc0
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @27
    @56
    wb
    0re
    @49
    cA
    wph
    cA
    crp
    wcel
    @45
    @48
    pntlem3.a
    ad2antrr
    #
    rpred
    #
    cc0
    cA
    @13
    elicc2
    sylancr
    mpbid
    #
    simp1d
    #
    @49
    @17
    @49
    cF
    @16
    wph
    @11
    @45
    @48
    @12
    ad2antrr
    @49
    @13
    crp
    wcel
    c3
    cz
    wcel
    @16
    crp
    wcel
    @49
    @13
    @62
    @49
    @13
    @62
    @49
    @53
    @54
    @55
    @61
    simp2d
    wph
    @25
    @27
    @48
    simplrl
    ne0gt0d
    elrpd
    #
    3z
    @13
    c3
    rpexpcl
    sylancl
    rpmulcld
    #
    rpred
    #
    resubcld
    #
    @49
    @40
    @51
    @49
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cD
    cR
    @13
    ve
    vk
    @13
    cD
    cdiv
    co
    #
    cF
    cB
    @67
    cdiv
    co
    ce
    cfv
    #
    cL
    @42
    c1
    caddc
    co
    #
    va
    pntlem3.r
    @59
    wph
    vx
    cv
    #
    cR
    cfv
    @70
    cdiv
    co
    cabs
    cfv
    cA
    cle
    wbr
    vx
    crp
    wral
    @45
    @48
    pntlem3.A
    ad2antrr
    wph
    cB
    crp
    wcel
    @45
    @48
    pntlemp.b
    ad2antrr
    wph
    cL
    cc0
    c1
    cioo
    co
    #
    wcel
    @45
    @48
    pntlemp.l
    ad2antrr
    pntlemp.d
    pntlemp.f
    wph
    @6
    @0
    clt
    wbr
    c1
    cL
    ve
    cv
    #
    cmul
    co
    caddc
    co
    @0
    cmul
    co
    #
    vk
    cv
    @6
    cmul
    co
    clt
    wbr
    wa
    vu
    cv
    #
    cR
    cfv
    @74
    cdiv
    co
    cabs
    cfv
    @72
    cle
    wbr
    vu
    @0
    @73
    cicc
    co
    wral
    wa
    vz
    crp
    wrex
    vy
    @70
    cpnf
    cioo
    co
    wral
    vk
    cB
    @72
    cdiv
    co
    ce
    cfv
    cpnf
    cico
    co
    wral
    vx
    crp
    wrex
    ve
    @71
    wral
    @45
    @48
    pntlemp.K
    ad2antrr
    @63
    @49
    @53
    @54
    @55
    @61
    simp3d
    #
    @67
    eqid
    @68
    eqid
    @49
    @69
    crp
    wcel
    #
    c1
    @69
    cle
    wbr
    #
    @49
    @47
    c1
    crp
    wcel
    @76
    @46
    @47
    @44
    simprl
    #
    1rp
    @42
    c1
    rpaddcl
    sylancl
    @49
    cc0
    @42
    cle
    wbr
    #
    @77
    @49
    @42
    @78
    rpge0d
    @49
    c1
    cr
    wcel
    @42
    cr
    wcel
    @79
    @77
    wb
    1re
    @49
    @42
    @78
    rpred
    #
    c1
    @42
    addge02
    sylancr
    mpbid
    jca
    @49
    @69
    cpnf
    cico
    co
    #
    @43
    wss
    #
    @44
    @28
    vz
    @81
    wral
    @49
    @42
    cxr
    wcel
    @42
    @69
    cle
    wbr
    @82
    @49
    @42
    @78
    rpxrd
    @49
    @42
    @80
    lep1d
    vt
    vr
    vw
    vv
    @42
    @69
    cpnf
    cico
    cle
    clt
    cle
    cico
    cle
    vt
    vr
    vw
    df-ico
    #
    @83
    @42
    @69
    @32
    xrletr
    ixxss1
    syl2anc
    @46
    @47
    @44
    simprr
    @28
    vz
    @81
    @43
    ssralv
    sylc
    pntlemp
    #
    @49
    @39
    @51
    vw
    crp
    @49
    @37
    crp
    wcel
    #
    wa
    #
    @39
    @37
    cR
    cfv
    #
    @37
    cdiv
    co
    #
    cabs
    cfv
    #
    @18
    cle
    wbr
    #
    @51
    @86
    @37
    @38
    wcel
    #
    @39
    @90
    wi
    @86
    @91
    @37
    cr
    wcel
    #
    @37
    @37
    cle
    wbr
    #
    @85
    @92
    @49
    @37
    rpre
    adantl
    #
    @86
    @37
    @94
    leidd
    @86
    @92
    @91
    @92
    @93
    wa
    wb
    @94
    @37
    @37
    elicopnf
    syl
    mpbir2and
    @36
    @90
    vv
    @37
    @38
    vv
    vw
    weq
    #
    @35
    @89
    @18
    cle
    @95
    @34
    @88
    cabs
    @95
    @33
    @87
    @32
    @37
    cdiv
    @32
    @37
    cR
    fveq2
    @95
    id
    oveq12d
    fveq2d
    breq1d
    rspcv
    syl
    @86
    cc0
    @89
    cle
    wbr
    #
    @90
    @51
    @86
    @88
    @86
    @88
    @85
    @88
    cr
    wcel
    #
    @49
    @87
    cr
    wcel
    @85
    @97
    crp
    cr
    @37
    cR
    cR
    va
    pntlem3.r
    pntrf
    ffvelrni
    @87
    @37
    rerpdivcl
    mpancom
    adantl
    recnd
    #
    absge0d
    @86
    @57
    @89
    cr
    wcel
    @50
    @96
    @90
    wa
    @51
    wi
    @86
    0red
    @86
    @88
    @98
    abscld
    @49
    @50
    @85
    @66
    adantr
    cc0
    @89
    @18
    letr
    syl3anc
    mpand
    syld
    rexlimdva
    mpd
    @49
    @18
    @13
    cA
    @66
    @62
    @60
    @49
    cc0
    @17
    cle
    wbr
    @18
    @13
    cle
    wbr
    @49
    @17
    @64
    rpge0d
    @49
    @13
    @17
    @62
    @65
    subge02d
    mpbid
    @75
    letrd
    @49
    @57
    @58
    @31
    @50
    @51
    @52
    w3a
    wb
    0re
    @60
    cc0
    cA
    @18
    elicc2
    sylancr
    mpbir3and
    @84
    jca
    rexlimdvaa
    syl5bi
    anassrs
    expimpd
    @8
    @30
    vt
    @13
    @9
    vt
    vr
    weq
    @5
    @28
    vy
    vz
    crp
    @7
    @4
    @13
    @3
    cle
    breq2
    rexralbidv
    elrab
    @8
    @40
    vt
    @18
    @9
    @4
    @18
    wceq
    #
    @8
    @3
    @18
    cle
    wbr
    #
    vz
    @7
    wral
    #
    vy
    crp
    wrex
    @40
    @99
    @5
    @100
    vy
    vz
    crp
    @7
    @4
    @18
    @3
    cle
    breq2
    rexralbidv
    @39
    @101
    vw
    vy
    crp
    @39
    @100
    vz
    @38
    wral
    vw
    vy
    weq
    #
    @101
    @36
    @100
    vv
    vz
    @38
    vv
    vz
    weq
    #
    @35
    @3
    @18
    cle
    @103
    @34
    @2
    cabs
    @103
    @33
    @1
    @32
    @0
    cdiv
    @32
    @0
    cR
    fveq2
    @103
    id
    oveq12d
    fveq2d
    breq1d
    cbvralv
    @102
    @100
    vz
    @38
    @7
    @37
    @6
    cpnf
    cico
    oveq1
    raleqdv
    syl5bb
    cbvrexv
    syl6bbr
    elrab
    3imtr4g
    imp
    an32s
    pm2.61dane
    pntlem3
end
