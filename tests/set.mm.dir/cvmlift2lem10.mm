include "cop.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wrex.mm"
include "csn.mm"
include "cxp.mm"
include "cres.mm"
include "cii.mm"
include "ctx.mm"
include "co.mm"
include "crest.mm"
include "ccn.mm"
include "wi.mm"
include "w3a.mm"
include "ccvm.mm"
include "cuni.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "wf.mm"
include "iitop.mm"
include "iiuni.mm"
include "txunii.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "opelxpd.mm"
include "ffvelrnd.mm"
include "cvmcov.mm"
include "syl2anc.mm"
include "wex.mm"
include "n0.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "csconn.mm"
include "wceq.mm"
include "eleq1.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "wral.mm"
include "adantr.mm"
include "cvmsrcl.mm"
include "ad2antll.mm"
include "cnima.mm"
include "ctop.mm"
include "wb.mm"
include "eltx.mm"
include "mp2an.mm"
include "sylib.mm"
include "simprl.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "rspcdva.mm"
include "clly.mm"
include "iillysconn.mm"
include "simplrl.mm"
include "simprll.mm"
include "llyi.mm"
include "mp3an2i.mm"
include "simplrr.mm"
include "simprlr.mm"
include "reeanv.mm"
include "simpl2.mm"
include "a1i.mm"
include "simpr2.mm"
include "simprl1.mm"
include "simprr1.mm"
include "xpss12.mm"
include "sstrd.mm"
include "ex.mm"
include "3jcad.mm"
include "simp3.mm"
include "anim12i.mm"
include "jca2.mm"
include "reximdv.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "simp3l1.mm"
include "simp3l2.mm"
include "crio.mm"
include "simpl1l.mm"
include "df-ov.mm"
include "simpl1r.mm"
include "simpld.mm"
include "syl5eqel.mm"
include "simprd.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "cpconn.mm"
include "cconn.mm"
include "simp3rl.mm"
include "sconnpconn.mm"
include "pconnconn.mm"
include "simp3rr.mm"
include "simp3l3.mm"
include "simprr.mm"
include "cvmlift2lem9.mm"
include "rexlimdvaa.mm"
include "3jca.mm"
include "3expia.mm"
include "reximdvva.mm"
include "expr.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "rexlimdvw.mm"

theorem cvmlift2lem10
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vc: setvar c
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vt: setvar t
  let vh: setvar h
  let cA: class A
  let cM: class M
  let cT: class T
  let cU: class U
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume cvmlift2.b: |- B = U. C
  assume cvmlift2.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift2.g: |- ( ph -> G e. ( ( II tX II ) Cn J ) )
  assume cvmlift2.p: |- ( ph -> P e. B )
  assume cvmlift2.i: |- ( ph -> ( F ` P ) = ( 0 G 0 ) )
  assume cvmlift2.h: |- H = ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( z G 0 ) ) /\ ( f ` 0 ) = P ) )
  assume cvmlift2.k: |- K = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> ( ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( x G z ) ) /\ ( f ` 0 ) = ( H ` x ) ) ) ` y ) )
  assume cvmlift2lem10.s: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. c e. s ( A. d e. ( s \ { c } ) ( c i^i d ) = (/) /\ ( F |` c ) e. ( ( C |`t c ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmlift2lem10.1: |- ( ph -> X e. ( 0 [,] 1 ) )
  assume cvmlift2lem10.2: |- ( ph -> Y e. ( 0 [,] 1 ) )

  disjoint c d
  disjoint c f
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint K c
  disjoint d f
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint K d
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint K f
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
  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint c d
  disjoint c f
  disjoint c k
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint d f
  disjoint d k
  disjoint d s
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f k
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
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
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint f ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S f
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint J c
  disjoint J d
  disjoint J f
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint G c
  disjoint G f
  disjoint G k
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H c
  disjoint H f
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint X c
  disjoint X d
  disjoint X f
  disjoint X k
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint C c
  disjoint C d
  disjoint C f
  disjoint C k
  disjoint C s
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint P f
  disjoint P k
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint B c
  disjoint B d
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint Y c
  disjoint Y d
  disjoint Y f
  disjoint Y k
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint S a
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
  disjoint c g
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint d g
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint f r
  disjoint f t
  disjoint g m
  disjoint g n
  disjoint g r
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint K g
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
  disjoint c g
  disjoint c h
  disjoint c m
  disjoint d g
  disjoint d h
  disjoint d m
  disjoint f g
  disjoint f h
  disjoint f m
  disjoint g h
  disjoint g k
  disjoint g m
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
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
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
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
  disjoint g ph
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
  disjoint S m
  disjoint S t
  disjoint J b
  disjoint J g
  disjoint J m
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
  disjoint G g
  disjoint h t
  disjoint G h
  disjoint k t
  disjoint G m
  disjoint G t
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
  disjoint X a
  disjoint X b
  disjoint d t
  disjoint X m
  disjoint X t
  disjoint Z z
  disjoint C a
  disjoint C b
  disjoint C g
  disjoint h r
  disjoint C h
  disjoint C m
  disjoint C r
  disjoint s t
  disjoint C t
  disjoint P g
  disjoint P h
  disjoint B b
  disjoint Y a
  disjoint Y b
  disjoint Y m
  disjoint Y t
  assert |- ( ph -> E. u e. II E. v e. II ( X e. u /\ Y e. v /\ ( E. w e. v ( K |` ( u X. { w } ) ) e. ( ( ( II tX II ) |`t ( u X. { w } ) ) Cn C ) -> ( K |` ( u X. v ) ) e. ( ( ( II tX II ) |`t ( u X. v ) ) Cn C ) ) ) )

  proof
    wph
    cX
    cY
    cop
    #
    cG
    cfv
    #
    vm
    cv
    #
    wcel
    #
    @2
    cS
    cfv
    #
    c0
    wne
    #
    wa
    #
    vm
    cJ
    wrex
    #
    cX
    vu
    cv
    #
    wcel
    #
    cY
    vv
    cv
    #
    wcel
    #
    cK
    @8
    vw
    cv
    #
    csn
    cxp
    #
    cres
    cii
    cii
    ctx
    co
    #
    @13
    crest
    co
    cC
    ccn
    co
    wcel
    #
    vw
    @10
    wrex
    cK
    @8
    @10
    cxp
    #
    cres
    @14
    @16
    crest
    co
    cC
    ccn
    co
    wcel
    #
    wi
    #
    w3a
    #
    vv
    cii
    wrex
    vu
    cii
    wrex
    #
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @1
    cJ
    cuni
    #
    wcel
    @7
    cvmlift2.f
    wph
    cc0
    c1
    cicc
    co
    #
    @23
    cxp
    #
    @22
    @0
    cG
    wph
    cG
    @14
    cJ
    ccn
    co
    wcel
    #
    @24
    @22
    cG
    wf
    #
    cvmlift2.g
    cG
    @14
    cJ
    @24
    @22
    cii
    cii
    @23
    @23
    iitop
    iitop
    iiuni
    iiuni
    txunii
    @22
    eqid
    #
    cnf
    syl
    #
    wph
    cX
    cY
    @23
    @23
    cvmlift2lem10.1
    cvmlift2lem10.2
    opelxpd
    #
    ffvelrnd
    vm
    vd
    vc
    cC
    @1
    cS
    vk
    cF
    cJ
    @22
    vs
    cvmlift2lem10.s
    @27
    cvmcov
    syl2anc
    wph
    @6
    @20
    vm
    cJ
    wph
    @3
    @5
    @20
    @5
    vt
    cv
    #
    @4
    wcel
    #
    vt
    wex
    wph
    @3
    wa
    #
    @20
    vt
    @4
    n0
    @32
    @31
    @20
    vt
    wph
    @3
    @31
    @20
    wph
    @3
    @31
    wa
    #
    wa
    #
    @9
    @11
    @16
    cG
    ccnv
    @2
    cima
    #
    wss
    #
    w3a
    #
    cii
    @8
    crest
    co
    #
    csconn
    wcel
    #
    cii
    @10
    crest
    co
    #
    csconn
    wcel
    #
    wa
    #
    wa
    #
    vv
    cii
    wrex
    #
    vu
    cii
    wrex
    #
    @20
    @34
    cX
    va
    cv
    #
    wcel
    #
    cY
    vb
    cv
    #
    wcel
    #
    wa
    #
    @46
    @48
    cxp
    #
    @35
    wss
    #
    wa
    #
    vb
    cii
    wrex
    va
    cii
    wrex
    #
    @45
    @34
    vz
    cv
    #
    @51
    wcel
    #
    @52
    wa
    #
    vb
    cii
    wrex
    va
    cii
    wrex
    #
    @54
    vz
    @35
    @0
    @55
    @0
    wceq
    #
    @57
    @53
    va
    vb
    cii
    cii
    @59
    @56
    @50
    @52
    @59
    @56
    @0
    @51
    wcel
    @50
    @55
    @0
    @51
    eleq1
    cX
    cY
    @46
    @48
    opelxp
    syl6bb
    anbi1d
    2rexbidv
    @34
    @35
    @14
    wcel
    #
    @58
    vz
    @35
    wral
    #
    @34
    @25
    @2
    cJ
    wcel
    #
    @60
    wph
    @25
    @33
    cvmlift2.g
    adantr
    @31
    @62
    wph
    @3
    vd
    vc
    cC
    cS
    @30
    @2
    vk
    cF
    cJ
    vs
    cvmlift2lem10.s
    cvmsrcl
    ad2antll
    @2
    cG
    @14
    cJ
    cnima
    syl2anc
    cii
    ctop
    wcel
    #
    @63
    @60
    @61
    wb
    iitop
    iitop
    va
    vb
    @35
    cii
    cii
    ctop
    ctop
    vz
    eltx
    mp2an
    sylib
    @34
    @0
    @35
    wcel
    #
    @0
    @24
    wcel
    #
    @3
    wph
    @65
    @33
    @29
    adantr
    wph
    @3
    @31
    simprl
    @34
    @26
    cG
    @24
    wfn
    @64
    @65
    @3
    wa
    wb
    wph
    @26
    @33
    @28
    adantr
    @24
    @22
    cG
    ffn
    @24
    @0
    @2
    cG
    elpreima
    3syl
    mpbir2and
    rspcdva
    @34
    @53
    @45
    va
    vb
    cii
    cii
    @34
    @46
    cii
    wcel
    #
    @48
    cii
    wcel
    #
    wa
    wa
    #
    @53
    @45
    @68
    @53
    wa
    #
    @8
    @46
    wss
    #
    @9
    @39
    w3a
    #
    vu
    cii
    wrex
    #
    @10
    @48
    wss
    #
    @11
    @41
    w3a
    #
    vv
    cii
    wrex
    #
    @45
    cii
    csconn
    clly
    wcel
    #
    @69
    @66
    @47
    @72
    iillysconn
    @34
    @66
    @67
    @53
    simplrl
    @68
    @47
    @49
    @52
    simprll
    vu
    csconn
    cX
    @46
    cii
    llyi
    mp3an2i
    @76
    @69
    @67
    @49
    @75
    iillysconn
    @34
    @66
    @67
    @53
    simplrr
    @68
    @47
    @49
    @52
    simprlr
    vv
    csconn
    cY
    @48
    cii
    llyi
    mp3an2i
    @72
    @75
    wa
    @71
    @74
    wa
    #
    vv
    cii
    wrex
    #
    vu
    cii
    wrex
    @69
    @45
    @71
    @74
    vu
    vv
    cii
    cii
    reeanv
    @69
    @78
    @44
    vu
    cii
    @69
    @77
    @43
    vv
    cii
    @69
    @77
    @37
    @42
    @69
    @77
    @9
    @11
    @36
    @77
    @9
    wi
    @69
    @70
    @9
    @39
    @74
    simpl2
    a1i
    @77
    @11
    wi
    @69
    @71
    @73
    @11
    @41
    simpr2
    a1i
    @69
    @77
    @36
    @69
    @77
    wa
    #
    @16
    @51
    @35
    @79
    @70
    @73
    @16
    @51
    wss
    @70
    @9
    @39
    @74
    @69
    simprl1
    @73
    @11
    @41
    @71
    @69
    simprr1
    @8
    @46
    @10
    @48
    xpss12
    syl2anc
    @68
    @50
    @52
    @77
    simplrr
    sstrd
    ex
    3jcad
    @71
    @39
    @74
    @41
    @70
    @9
    @39
    simp3
    @73
    @11
    @41
    simp3
    anim12i
    jca2
    reximdv
    reximdv
    syl5bir
    mp2and
    ex
    rexlimdvva
    mpd
    @34
    @43
    @19
    vu
    vv
    cii
    cii
    @34
    @8
    cii
    wcel
    #
    @10
    cii
    wcel
    #
    wa
    #
    @43
    @19
    @34
    @82
    @43
    w3a
    #
    @9
    @11
    @18
    @9
    @11
    @36
    @42
    @34
    @82
    simp3l1
    #
    @9
    @11
    @36
    @42
    @34
    @82
    simp3l2
    #
    @83
    @15
    @17
    vw
    @10
    @83
    @12
    @10
    wcel
    #
    @15
    wa
    #
    wa
    #
    vx
    vy
    vz
    cB
    cC
    cP
    cS
    @30
    @8
    vf
    vk
    cF
    cG
    cH
    cJ
    cK
    @2
    @10
    cX
    cY
    cK
    co
    @48
    wcel
    vb
    @30
    crio
    #
    cX
    cY
    @12
    vs
    vb
    vc
    vd
    cvmlift2.b
    @88
    wph
    @21
    wph
    @33
    @82
    @43
    @87
    simpl1l
    #
    cvmlift2.f
    syl
    @88
    wph
    @25
    @90
    cvmlift2.g
    syl
    @88
    wph
    cP
    cB
    wcel
    @90
    cvmlift2.p
    syl
    @88
    wph
    cP
    cF
    cfv
    cc0
    cc0
    cG
    co
    wceq
    @90
    cvmlift2.i
    syl
    cvmlift2.h
    cvmlift2.k
    cvmlift2lem10.s
    @88
    cX
    cY
    cG
    co
    @1
    @2
    cX
    cY
    cG
    df-ov
    @88
    @3
    @31
    wph
    @33
    @82
    @43
    @87
    simpl1r
    #
    simpld
    syl5eqel
    @88
    @3
    @31
    @91
    simprd
    @80
    @81
    @34
    @43
    @87
    simpl2l
    @80
    @81
    @34
    @43
    @87
    simpl2r
    @88
    @39
    @38
    cpconn
    wcel
    @38
    cconn
    wcel
    @83
    @39
    @87
    @39
    @41
    @37
    @34
    @82
    simp3rl
    adantr
    @38
    sconnpconn
    @38
    pconnconn
    3syl
    @88
    @41
    @40
    cpconn
    wcel
    @40
    cconn
    wcel
    @83
    @41
    @87
    @39
    @41
    @37
    @34
    @82
    simp3rr
    adantr
    @40
    sconnpconn
    @40
    pconnconn
    3syl
    @83
    @9
    @87
    @84
    adantr
    @83
    @11
    @87
    @85
    adantr
    @83
    @36
    @87
    @9
    @11
    @36
    @42
    @34
    @82
    simp3l3
    adantr
    @83
    @86
    @15
    simprl
    @83
    @86
    @15
    simprr
    @89
    eqid
    cvmlift2lem9
    rexlimdvaa
    3jca
    3expia
    reximdvva
    mpd
    expr
    exlimdv
    syl5bi
    expimpd
    rexlimdvw
    mpd
end
