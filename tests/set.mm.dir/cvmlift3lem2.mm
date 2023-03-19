include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "ccom.mm"
include "crio.mm"
include "w3a.mm"
include "wreu.mm"
include "cpconn.mm"
include "csconn.mm"
include "adantr.mm"
include "sconnpconn.mm"
include "syl.mm"
include "simpr.mm"
include "pconncn.mm"
include "syl3anc.mm"
include "wi.mm"
include "wral.mm"
include "cicc.mm"
include "wf.mm"
include "eqid.mm"
include "ccvm.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "cnco.mm"
include "syl2anc.mm"
include "simprrl.mm"
include "fveq2d.mm"
include "iiuni.mm"
include "cnf.mm"
include "0elunit.mm"
include "fvco3.mm"
include "sylancl.mm"
include "3eqtr4rd.mm"
include "cvmliftiota.mm"
include "simp1d.mm"
include "1elunit.mm"
include "ffvelrn.mm"
include "simprrr.mm"
include "eqidd.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "coeq2.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "riotabidv.mm"
include "fveq1d.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "ad4antr.mm"
include "cnlly.mm"
include "simprr1.mm"
include "simprr2.mm"
include "eqtr4d.mm"
include "cvmlift3lem1.mm"
include "simprr3.mm"
include "eqtrd.mm"
include "rexlimdvaa.mm"
include "ralrimiva.mm"
include "eqeq2.mm"
include "3anbi3d.mm"
include "rexbidv.mm"
include "eqeq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "cbvrexv.mm"
include "syl5bb.mm"
include "reu8.mm"
include "sylibr.mm"
include "mpd.mm"

theorem cvmlift3lem2
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cO: class O
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vs: setvar s
  let vw: setvar w
  let cA: class A
  let cI: class I
  let va: setvar a
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vt: setvar t
  let cH: class H
  let cQ: class Q
  let cS: class S
  let cR: class R
  let cT: class T
  let cZ: class Z
  let cW: class W
  assume cvmlift3.b: |- B = U. C
  assume cvmlift3.y: |- Y = U. K
  assume cvmlift3.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift3.k: |- ( ph -> K e. SConn )
  assume cvmlift3.l: |- ( ph -> K e. N-Locally PConn )
  assume cvmlift3.o: |- ( ph -> O e. Y )
  assume cvmlift3.g: |- ( ph -> G e. ( K Cn J ) )
  assume cvmlift3.p: |- ( ph -> P e. B )
  assume cvmlift3.e: |- ( ph -> ( F ` P ) = ( G ` O ) )

  disjoint f z
  disjoint f g
  disjoint g z
  disjoint J f
  disjoint J g
  disjoint F f
  disjoint F g
  disjoint F z
  disjoint B f
  disjoint B g
  disjoint B z
  disjoint X f
  disjoint X g
  disjoint X z
  disjoint G f
  disjoint G g
  disjoint G z
  disjoint C f
  disjoint C g
  disjoint C z
  disjoint f ph
  disjoint K f
  disjoint K g
  disjoint K z
  disjoint P f
  disjoint P g
  disjoint P z
  disjoint O f
  disjoint O g
  disjoint O z
  disjoint Y f
  disjoint Y g
  disjoint Y z
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b k
  disjoint b s
  disjoint b w
  disjoint b z
  disjoint A b
  disjoint c d
  disjoint c f
  disjoint c k
  disjoint c s
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d f
  disjoint d k
  disjoint d s
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint f k
  disjoint f s
  disjoint f w
  disjoint A f
  disjoint k s
  disjoint k w
  disjoint k z
  disjoint A k
  disjoint s w
  disjoint s z
  disjoint A s
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint I f
  disjoint g w
  disjoint I g
  disjoint I w
  disjoint I z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint J a
  disjoint b g
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint J b
  disjoint c g
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint J c
  disjoint d g
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint J d
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint g k
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint J s
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint a h
  disjoint a n
  disjoint a z
  disjoint F a
  disjoint b h
  disjoint b n
  disjoint F b
  disjoint c h
  disjoint c n
  disjoint F c
  disjoint d h
  disjoint d n
  disjoint F d
  disjoint f h
  disjoint f n
  disjoint g h
  disjoint g n
  disjoint h k
  disjoint h n
  disjoint h s
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint k n
  disjoint F k
  disjoint n s
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint F s
  disjoint u z
  disjoint F u
  disjoint v z
  disjoint F v
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint M f
  disjoint M g
  disjoint M h
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint N f
  disjoint N g
  disjoint N w
  disjoint a m
  disjoint a t
  disjoint H a
  disjoint b m
  disjoint b t
  disjoint H b
  disjoint c m
  disjoint c t
  disjoint H c
  disjoint d m
  disjoint d t
  disjoint H d
  disjoint f m
  disjoint f t
  disjoint H f
  disjoint g m
  disjoint g t
  disjoint H g
  disjoint h m
  disjoint h t
  disjoint H h
  disjoint m n
  disjoint m t
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint H m
  disjoint n t
  disjoint H n
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint H t
  disjoint H v
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint Q f
  disjoint Q g
  disjoint Q w
  disjoint S a
  disjoint S b
  disjoint S f
  disjoint S m
  disjoint S t
  disjoint S v
  disjoint S x
  disjoint B a
  disjoint B b
  disjoint B d
  disjoint B h
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint R g
  disjoint R w
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X h
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G d
  disjoint G h
  disjoint k m
  disjoint k t
  disjoint G k
  disjoint m u
  disjoint G m
  disjoint G n
  disjoint t u
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint T s
  disjoint Z f
  disjoint Z g
  disjoint Z x
  disjoint Z z
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C h
  disjoint C k
  disjoint m s
  disjoint C m
  disjoint C n
  disjoint s t
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint a ph
  disjoint h ph
  disjoint m ph
  disjoint n ph
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K h
  disjoint K m
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P h
  disjoint P n
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint O h
  disjoint O n
  disjoint O u
  disjoint O v
  disjoint O w
  disjoint O x
  disjoint Y a
  disjoint Y h
  disjoint Y m
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint W c
  disjoint W d
  disjoint W f
  disjoint W h
  disjoint W n
  disjoint W x
  disjoint W y
  assert |- ( ( ph /\ X e. Y ) -> E! z e. B E. f e. ( II Cn K ) ( ( f ` 0 ) = O /\ ( f ` 1 ) = X /\ ( ( iota_ g e. ( II Cn C ) ( ( F o. g ) = ( G o. f ) /\ ( g ` 0 ) = P ) ) ` 1 ) = z ) )

  proof
    wph
    cX
    cY
    wcel
    #
    wa
    #
    cc0
    va
    cv
    #
    cfv
    #
    cO
    wceq
    #
    c1
    @2
    cfv
    #
    cX
    wceq
    #
    wa
    #
    va
    cii
    cK
    ccn
    co
    #
    wrex
    #
    cc0
    vf
    cv
    #
    cfv
    #
    cO
    wceq
    #
    c1
    @10
    cfv
    #
    cX
    wceq
    #
    c1
    cF
    vg
    cv
    #
    ccom
    #
    cG
    @10
    ccom
    #
    wceq
    #
    cc0
    @15
    cfv
    cP
    wceq
    #
    wa
    #
    vg
    cii
    cC
    ccn
    co
    #
    crio
    #
    cfv
    #
    vz
    cv
    #
    wceq
    #
    w3a
    #
    vf
    @8
    wrex
    #
    vz
    cB
    wreu
    #
    @1
    cK
    cpconn
    wcel
    #
    cO
    cY
    wcel
    #
    @0
    @9
    @1
    cK
    csconn
    wcel
    #
    @29
    wph
    @31
    @0
    cvmlift3.k
    adantr
    cK
    sconnpconn
    syl
    wph
    @30
    @0
    cvmlift3.o
    adantr
    wph
    @0
    simpr
    cO
    cX
    va
    cK
    cY
    cvmlift3.y
    pconncn
    syl3anc
    @1
    @7
    @28
    va
    @8
    @1
    @2
    @8
    wcel
    #
    @7
    wa
    #
    wa
    #
    @27
    cc0
    vh
    cv
    #
    cfv
    #
    cO
    wceq
    #
    c1
    @35
    cfv
    #
    cX
    wceq
    #
    c1
    @16
    cG
    @35
    ccom
    #
    wceq
    #
    @19
    wa
    #
    vg
    @21
    crio
    #
    cfv
    #
    vw
    cv
    #
    wceq
    #
    w3a
    #
    vh
    @8
    wrex
    #
    @24
    @45
    wceq
    #
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    vz
    cB
    wrex
    #
    @28
    @34
    c1
    @16
    cG
    @2
    ccom
    #
    wceq
    #
    @19
    wa
    #
    vg
    @21
    crio
    #
    cfv
    #
    cB
    wcel
    #
    @12
    @14
    @23
    @58
    wceq
    #
    w3a
    #
    vf
    @8
    wrex
    #
    @48
    @58
    @45
    wceq
    #
    wi
    #
    vw
    cB
    wral
    #
    @53
    @34
    cc0
    c1
    cicc
    co
    #
    cB
    @57
    wf
    #
    c1
    @66
    wcel
    @59
    @34
    @57
    @21
    wcel
    #
    @67
    @34
    @68
    cF
    @57
    ccom
    @54
    wceq
    cc0
    @57
    cfv
    cP
    wceq
    @34
    cB
    cC
    cP
    vg
    cF
    @54
    @57
    cJ
    cvmlift3.b
    @57
    eqid
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @0
    @33
    cvmlift3.f
    ad2antrr
    @34
    @32
    cG
    cK
    cJ
    ccn
    co
    wcel
    #
    @54
    cii
    cJ
    ccn
    co
    wcel
    @1
    @32
    @7
    simprl
    #
    wph
    @70
    @0
    @33
    cvmlift3.g
    ad2antrr
    @2
    cG
    cii
    cK
    cJ
    cnco
    syl2anc
    wph
    cP
    cB
    wcel
    #
    @0
    @33
    cvmlift3.p
    ad2antrr
    @34
    @3
    cG
    cfv
    #
    cO
    cG
    cfv
    #
    cc0
    @54
    cfv
    #
    cP
    cF
    cfv
    #
    @34
    @3
    cO
    cG
    @1
    @32
    @4
    @6
    simprrl
    #
    fveq2d
    @34
    @66
    cY
    @2
    wf
    #
    cc0
    @66
    wcel
    @75
    @73
    wceq
    @34
    @32
    @78
    @71
    @2
    cii
    cK
    @66
    cY
    iiuni
    cvmlift3.y
    cnf
    syl
    0elunit
    @66
    cY
    cc0
    cG
    @2
    fvco3
    sylancl
    wph
    @76
    @74
    wceq
    #
    @0
    @33
    cvmlift3.e
    ad2antrr
    3eqtr4rd
    cvmliftiota
    simp1d
    @57
    cii
    cC
    @66
    cB
    iiuni
    cvmlift3.b
    cnf
    syl
    1elunit
    @66
    cB
    c1
    @57
    ffvelrn
    sylancl
    @34
    @32
    @4
    @6
    @58
    @58
    wceq
    #
    @62
    @71
    @77
    @1
    @32
    @4
    @6
    simprrr
    #
    @34
    @58
    eqidd
    @61
    @4
    @6
    @80
    w3a
    vf
    @2
    @8
    @10
    @2
    wceq
    #
    @12
    @4
    @14
    @6
    @60
    @80
    @82
    @11
    @3
    cO
    cc0
    @10
    @2
    fveq1
    eqeq1d
    @82
    @13
    @5
    cX
    c1
    @10
    @2
    fveq1
    eqeq1d
    @82
    @23
    @58
    @58
    @82
    c1
    @22
    @57
    @82
    @20
    @56
    vg
    @21
    @82
    @18
    @55
    @19
    @82
    @17
    @54
    @16
    @10
    @2
    cG
    coeq2
    eqeq2d
    anbi1d
    riotabidv
    fveq1d
    eqeq1d
    3anbi123d
    rspcev
    syl13anc
    @34
    @64
    vw
    cB
    @34
    @45
    cB
    wcel
    #
    wa
    #
    @47
    @63
    vh
    @8
    @84
    @35
    @8
    wcel
    #
    @47
    wa
    #
    wa
    #
    @58
    @44
    @45
    @87
    cB
    cC
    cP
    vg
    cF
    cG
    cJ
    cK
    @2
    @35
    cO
    cY
    cvmlift3.b
    cvmlift3.y
    wph
    @69
    @0
    @33
    @83
    @86
    cvmlift3.f
    ad4antr
    wph
    @31
    @0
    @33
    @83
    @86
    cvmlift3.k
    ad4antr
    wph
    cK
    cpconn
    cnlly
    wcel
    @0
    @33
    @83
    @86
    cvmlift3.l
    ad4antr
    wph
    @30
    @0
    @33
    @83
    @86
    cvmlift3.o
    ad4antr
    wph
    @70
    @0
    @33
    @83
    @86
    cvmlift3.g
    ad4antr
    wph
    @72
    @0
    @33
    @83
    @86
    cvmlift3.p
    ad4antr
    wph
    @79
    @0
    @33
    @83
    @86
    cvmlift3.e
    ad4antr
    @34
    @32
    @83
    @86
    @71
    ad2antrr
    @34
    @4
    @83
    @86
    @77
    ad2antrr
    @84
    @85
    @47
    simprl
    @37
    @39
    @46
    @85
    @84
    simprr1
    @87
    @5
    cX
    @38
    @34
    @6
    @83
    @86
    @81
    ad2antrr
    @37
    @39
    @46
    @85
    @84
    simprr2
    eqtr4d
    cvmlift3lem1
    @37
    @39
    @46
    @85
    @84
    simprr3
    eqtrd
    rexlimdvaa
    ralrimiva
    @52
    @62
    @65
    wa
    vz
    @58
    cB
    @24
    @58
    wceq
    #
    @27
    @62
    @51
    @65
    @88
    @26
    @61
    vf
    @8
    @88
    @25
    @60
    @12
    @14
    @24
    @58
    @23
    eqeq2
    3anbi3d
    rexbidv
    @88
    @50
    @64
    vw
    cB
    @88
    @49
    @63
    @48
    @24
    @58
    @45
    eqeq1
    imbi2d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    @27
    @48
    vz
    vw
    cB
    @27
    @37
    @39
    @44
    @24
    wceq
    #
    w3a
    #
    vh
    @8
    wrex
    @49
    @48
    @26
    @90
    vf
    vh
    @8
    @10
    @35
    wceq
    #
    @12
    @37
    @14
    @39
    @25
    @89
    @91
    @11
    @36
    cO
    cc0
    @10
    @35
    fveq1
    eqeq1d
    @91
    @13
    @38
    cX
    c1
    @10
    @35
    fveq1
    eqeq1d
    @91
    @23
    @44
    @24
    @91
    c1
    @22
    @43
    @91
    @20
    @42
    vg
    @21
    @91
    @18
    @41
    @19
    @91
    @17
    @40
    @16
    @10
    @35
    cG
    coeq2
    eqeq2d
    anbi1d
    riotabidv
    fveq1d
    eqeq1d
    3anbi123d
    cbvrexv
    @49
    @90
    @47
    vh
    @8
    @49
    @89
    @46
    @37
    @39
    @24
    @45
    @44
    eqeq2
    3anbi3d
    rexbidv
    syl5bb
    reu8
    sylibr
    rexlimdvaa
    mpd
end
