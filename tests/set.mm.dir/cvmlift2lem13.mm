include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "cc0.mm"
include "co.mm"
include "wa.mm"
include "cii.mm"
include "ctx.mm"
include "ccn.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "wcel.mm"
include "c1.mm"
include "cicc.mm"
include "csn.mm"
include "cxp.mm"
include "ccnp.mm"
include "cfv.mm"
include "crab.mm"
include "wss.mm"
include "wb.mm"
include "cnei.mm"
include "copab.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "cbvrabv.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "sseq1d.mm"
include "simpr.mm"
include "eleq1d.mm"
include "xpeq1.mm"
include "bibi12d.mm"
include "cbvrexv.mm"
include "simpl.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "bibi2d.mm"
include "rexeqbidv.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "cbvopabv.mm"
include "cvmlift2lem12.mm"
include "cvmlift2lem7.mm"
include "0elunit.mm"
include "cvmlift2lem8.mm"
include "mpan2.mm"
include "cmpt.mm"
include "cvmlift2lem2.mm"
include "simp3d.mm"
include "eqtrd.mm"
include "coeq2.mm"
include "eqeq1d.mm"
include "oveq.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "cop.mm"
include "iitop.mm"
include "iiuni.mm"
include "txunii.mm"
include "cconn.mm"
include "iiconn.mm"
include "txconn.mm"
include "mp2an.mm"
include "a1i.mm"
include "cnlly.mm"
include "iinllyconn.mm"
include "txnlly.mm"
include "opelxpi.mm"
include "df-ov.mm"
include "syl6eq.mm"
include "cvmliftmo.mm"
include "eqeq1i.mm"
include "anbi2i.mm"
include "rmobii.mm"
include "sylibr.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem cvmlift2lem13
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vh: setvar h
  let vk: setvar k
  let vs: setvar s
  let cA: class A
  let cM: class M
  let cS: class S
  let cT: class T
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z
  let cY: class Y
  assume cvmlift2.b: |- B = U. C
  assume cvmlift2.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift2.g: |- ( ph -> G e. ( ( II tX II ) Cn J ) )
  assume cvmlift2.p: |- ( ph -> P e. B )
  assume cvmlift2.i: |- ( ph -> ( F ` P ) = ( 0 G 0 ) )
  assume cvmlift2.h: |- H = ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( z G 0 ) ) /\ ( f ` 0 ) = P ) )
  assume cvmlift2.k: |- K = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> ( ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( x G z ) ) /\ ( f ` 0 ) = ( H ` x ) ) ) ` y ) )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint K f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint K g
  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint P f
  disjoint P g
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint K a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b g
  disjoint b m
  disjoint b n
  disjoint b r
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint K b
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint K c
  disjoint d f
  disjoint d g
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint K d
  disjoint f m
  disjoint f n
  disjoint f r
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g m
  disjoint g n
  disjoint g r
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint K m
  disjoint n r
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint K n
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint K r
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint K t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint K u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint K v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint K w
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b k
  disjoint b m
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c m
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d k
  disjoint d m
  disjoint d s
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f h
  disjoint f k
  disjoint f m
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g h
  disjoint g k
  disjoint g m
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint h k
  disjoint h m
  disjoint h s
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint k m
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b n
  disjoint b r
  disjoint b t
  disjoint b ph
  disjoint f n
  disjoint f r
  disjoint f t
  disjoint g n
  disjoint g r
  disjoint g t
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m ph
  disjoint n r
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint n ph
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint ph r
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint A a
  disjoint A t
  disjoint A v
  disjoint A x
  disjoint a c
  disjoint a d
  disjoint a k
  disjoint a s
  disjoint M a
  disjoint M b
  disjoint c r
  disjoint M c
  disjoint d r
  disjoint M d
  disjoint k r
  disjoint M k
  disjoint r s
  disjoint M r
  disjoint M s
  disjoint M u
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint S b
  disjoint S f
  disjoint S m
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint J b
  disjoint J c
  disjoint J d
  disjoint J k
  disjoint J m
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint U m
  disjoint U n
  disjoint U u
  disjoint U w
  disjoint U z
  disjoint a h
  disjoint G a
  disjoint G b
  disjoint c t
  disjoint G c
  disjoint h t
  disjoint G h
  disjoint k t
  disjoint G k
  disjoint G m
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint V m
  disjoint V n
  disjoint V u
  disjoint V w
  disjoint c n
  disjoint W c
  disjoint d n
  disjoint W d
  disjoint W m
  disjoint W n
  disjoint W u
  disjoint W v
  disjoint H b
  disjoint H c
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint d t
  disjoint X d
  disjoint X f
  disjoint X k
  disjoint X m
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Z z
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint h r
  disjoint C h
  disjoint C k
  disjoint C m
  disjoint C r
  disjoint s t
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint P h
  disjoint P k
  disjoint P u
  disjoint P v
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B v
  disjoint B w
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y f
  disjoint Y k
  disjoint Y m
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ph -> E! g e. ( ( II tX II ) Cn C ) ( ( F o. g ) = G /\ ( 0 g 0 ) = P ) )

  proof
    wph
    cF
    vg
    cv
    #
    ccom
    #
    cG
    wceq
    #
    cc0
    cc0
    @0
    co
    #
    cP
    wceq
    #
    wa
    #
    vg
    cii
    cii
    ctx
    co
    #
    cC
    ccn
    co
    #
    wrex
    #
    @5
    vg
    @7
    wrmo
    #
    @5
    vg
    @7
    wreu
    wph
    cK
    @7
    wcel
    cF
    cK
    ccom
    #
    cG
    wceq
    #
    cc0
    cc0
    cK
    co
    #
    cP
    wceq
    #
    @8
    wph
    vx
    vy
    vz
    vu
    vt
    cc0
    c1
    cicc
    co
    #
    vz
    cv
    #
    csn
    #
    cxp
    #
    cK
    va
    cv
    #
    @6
    cC
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    va
    @14
    @14
    cxp
    #
    crab
    #
    wss
    #
    vz
    @14
    crab
    cB
    cC
    cP
    vd
    cv
    #
    @14
    wcel
    #
    vv
    cv
    #
    vb
    cv
    #
    csn
    #
    cxp
    #
    @23
    wss
    #
    @27
    @25
    csn
    #
    cxp
    #
    @23
    wss
    #
    wb
    #
    vv
    vc
    cv
    #
    csn
    #
    cii
    cnei
    cfv
    #
    cfv
    #
    wrex
    #
    wa
    #
    vc
    vd
    copab
    vf
    cF
    cG
    cH
    cJ
    cK
    @23
    vr
    vb
    cvmlift2.b
    cvmlift2.f
    cvmlift2.g
    cvmlift2.p
    cvmlift2.i
    cvmlift2.h
    cvmlift2.k
    @21
    cK
    @15
    @19
    cfv
    #
    wcel
    va
    vz
    @22
    va
    vz
    weq
    @20
    @42
    cK
    @18
    @15
    @19
    fveq2
    eleq2d
    cbvrabv
    @24
    @14
    @29
    cxp
    #
    @23
    wss
    vz
    vb
    @14
    vz
    vb
    weq
    #
    @17
    @43
    @23
    @44
    @16
    @29
    @14
    @15
    @28
    sneq
    xpeq2d
    sseq1d
    cbvrabv
    @41
    vt
    cv
    #
    @14
    wcel
    #
    vu
    cv
    #
    @29
    cxp
    #
    @23
    wss
    #
    @47
    @45
    csn
    #
    cxp
    #
    @23
    wss
    #
    wb
    #
    vu
    vr
    cv
    #
    csn
    #
    @38
    cfv
    #
    wrex
    #
    wa
    vc
    vd
    vr
    vt
    vc
    vr
    weq
    #
    vd
    vt
    weq
    #
    wa
    #
    @26
    @46
    @40
    @57
    @60
    @25
    @45
    @14
    @58
    @59
    simpr
    #
    eleq1d
    @40
    @49
    @47
    @32
    cxp
    #
    @23
    wss
    #
    wb
    #
    vu
    @39
    wrex
    @60
    @57
    @35
    @64
    vv
    vu
    @39
    vv
    vu
    weq
    #
    @31
    @49
    @34
    @63
    @65
    @30
    @48
    @23
    @27
    @47
    @29
    xpeq1
    sseq1d
    @65
    @33
    @62
    @23
    @27
    @47
    @32
    xpeq1
    sseq1d
    bibi12d
    cbvrexv
    @60
    @64
    @53
    vu
    @39
    @56
    @60
    @37
    @55
    @38
    @60
    @36
    @54
    @58
    @59
    simpl
    sneqd
    fveq2d
    @60
    @63
    @52
    @49
    @60
    @62
    @51
    @23
    @60
    @32
    @50
    @47
    @60
    @25
    @45
    @61
    sneqd
    xpeq2d
    sseq1d
    bibi2d
    rexeqbidv
    syl5bb
    anbi12d
    cbvopabv
    cvmlift2lem12
    wph
    vx
    vy
    vz
    cB
    cC
    cP
    vf
    cF
    cG
    cH
    cJ
    cK
    cvmlift2.b
    cvmlift2.f
    cvmlift2.g
    cvmlift2.p
    cvmlift2.i
    cvmlift2.h
    cvmlift2.k
    cvmlift2lem7
    wph
    @12
    cc0
    cH
    cfv
    #
    cP
    wph
    cc0
    @14
    wcel
    #
    @12
    @66
    wceq
    0elunit
    wph
    vx
    vy
    vz
    cB
    cC
    cP
    vf
    cF
    cG
    cH
    cJ
    cK
    cc0
    cvmlift2.b
    cvmlift2.f
    cvmlift2.g
    cvmlift2.p
    cvmlift2.i
    cvmlift2.h
    cvmlift2.k
    cvmlift2lem8
    mpan2
    wph
    cH
    cii
    cC
    ccn
    co
    wcel
    cF
    cH
    ccom
    vz
    @14
    @15
    cc0
    cG
    co
    cmpt
    wceq
    @66
    cP
    wceq
    wph
    vz
    cB
    cC
    cP
    vf
    cF
    cG
    cH
    cJ
    cvmlift2.b
    cvmlift2.f
    cvmlift2.g
    cvmlift2.p
    cvmlift2.i
    cvmlift2.h
    cvmlift2lem2
    simp3d
    eqtrd
    @5
    @11
    @13
    wa
    vg
    cK
    @7
    @0
    cK
    wceq
    #
    @2
    @11
    @4
    @13
    @68
    @1
    @10
    cG
    @0
    cK
    cF
    coeq2
    eqeq1d
    @68
    @3
    @12
    cP
    cc0
    cc0
    @0
    cK
    oveq
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    wph
    @2
    cc0
    cc0
    cop
    #
    @0
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vg
    @7
    wrmo
    @9
    wph
    cB
    cC
    cP
    vg
    cF
    cG
    cJ
    @6
    @69
    @22
    cvmlift2.b
    cii
    cii
    @14
    @14
    iitop
    iitop
    iiuni
    iiuni
    txunii
    cvmlift2.f
    @6
    cconn
    wcel
    #
    wph
    cii
    cconn
    wcel
    #
    @74
    @73
    iiconn
    iiconn
    cii
    cii
    txconn
    mp2an
    a1i
    @6
    cconn
    cnlly
    #
    wcel
    #
    wph
    cii
    @75
    wcel
    #
    @77
    @76
    iinllyconn
    iinllyconn
    cconn
    cii
    cii
    vx
    vy
    vx
    cv
    vy
    cv
    txconn
    txnlly
    mp2an
    a1i
    @69
    @22
    wcel
    #
    wph
    @67
    @67
    @78
    0elunit
    0elunit
    cc0
    cc0
    @14
    @14
    opelxpi
    mp2an
    a1i
    cvmlift2.g
    cvmlift2.p
    wph
    cP
    cF
    cfv
    cc0
    cc0
    cG
    co
    @69
    cG
    cfv
    cvmlift2.i
    cc0
    cc0
    cG
    df-ov
    syl6eq
    cvmliftmo
    @5
    @72
    vg
    @7
    @4
    @71
    @2
    @3
    @70
    cP
    cc0
    cc0
    @0
    df-ov
    eqeq1i
    anbi2i
    rmobii
    sylibr
    @5
    vg
    @7
    reu5
    sylanbrc
end
