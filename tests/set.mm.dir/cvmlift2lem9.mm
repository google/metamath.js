include "cii.mm"
include "ctx.mm"
include "co.mm"
include "cxp.mm"
include "cop.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "iitop.mm"
include "iiuni.mm"
include "txunii.mm"
include "cvmlift2lem5.mm"
include "ccom.mm"
include "ccn.mm"
include "cvmlift2lem7.mm"
include "eqeltrd.mm"
include "ctop.mm"
include "wcel.mm"
include "txtopi.mm"
include "a1i.mm"
include "wss.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "syl.mm"
include "sseldd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "wa.mm"
include "cfv.mm"
include "ccvm.mm"
include "fovrnd.mm"
include "wf.mm"
include "wceq.mm"
include "fvco3.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "cvmsiota.mm"
include "syl13anc.mm"
include "eleq1i.mm"
include "anbi2i.mm"
include "sylib.mm"
include "xpss12.mm"
include "cima.mm"
include "cv.mm"
include "wral.mm"
include "csn.mm"
include "cres.mm"
include "snidg.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "ovres.mm"
include "crest.mm"
include "ccnv.mm"
include "eqid.mm"
include "cconn.mm"
include "cvv.mm"
include "snex.mm"
include "adantr.mm"
include "txrest.mm"
include "syl22anc.mm"
include "cpw.mm"
include "ctopon.mm"
include "iitopon.mm"
include "sselda.mm"
include "adantrr.mm"
include "restsn2.mm"
include "sylancr.mm"
include "c0.mm"
include "cpr.mm"
include "pwsn.mm"
include "indisconn.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "txconn.mm"
include "cvmlift2lem6.mm"
include "syldan.mm"
include "xpss2.mm"
include "snssd.mm"
include "xpss1.mm"
include "restuni.mm"
include "sseqtrd.mm"
include "cnrest.mm"
include "resabs1d.mm"
include "ovex.mm"
include "xpex.mm"
include "restabs.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "3eltr3d.mm"
include "crn.mm"
include "wb.mm"
include "cvmtop1.mm"
include "toptopon.mm"
include "df-ima.mm"
include "simprl.mm"
include "imass2.mm"
include "3syl.mm"
include "imaco.mm"
include "cnvco.mm"
include "cnveqd.mm"
include "syl5eqr.mm"
include "imaeq1d.mm"
include "sseqtr4d.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "fdm.mm"
include "funimass3.mm"
include "mpbird.mm"
include "sstrd.mm"
include "syl5eqssr.mm"
include "cnvimass.mm"
include "cvmcn.mm"
include "cnf.mm"
include "syl5sseq.mm"
include "cnrest2.mm"
include "mpbid.mm"
include "cvmsss.mm"
include "simpld.mm"
include "cvmsuni.mm"
include "cvmsrcl.mm"
include "cnima.mm"
include "restopn2.mm"
include "mpbir2and.mm"
include "ccld.mm"
include "cvmscld.mm"
include "eleqtrd.mm"
include "eqtr4d.mm"
include "mpdan.mm"
include "simprd.mm"
include "conncn.mm"
include "feq2d.mm"
include "eqeltrrd.mm"
include "ralrimivva.mm"
include "funimassov.mm"
include "cvmlift2lem9a.mm"

theorem cvmlift2lem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let va: setvar a
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vh: setvar h
  let cA: class A
  assume cvmlift2.b: |- B = U. C
  assume cvmlift2.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift2.g: |- ( ph -> G e. ( ( II tX II ) Cn J ) )
  assume cvmlift2.p: |- ( ph -> P e. B )
  assume cvmlift2.i: |- ( ph -> ( F ` P ) = ( 0 G 0 ) )
  assume cvmlift2.h: |- H = ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( z G 0 ) ) /\ ( f ` 0 ) = P ) )
  assume cvmlift2.k: |- K = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> ( ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( x G z ) ) /\ ( f ` 0 ) = ( H ` x ) ) ) ` y ) )
  assume cvmlift2lem10.s: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. c e. s ( A. d e. ( s \ { c } ) ( c i^i d ) = (/) /\ ( F |` c ) e. ( ( C |`t c ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmlift2lem9.1: |- ( ph -> ( X G Y ) e. M )
  assume cvmlift2lem9.2: |- ( ph -> T e. ( S ` M ) )
  assume cvmlift2lem9.3: |- ( ph -> U e. II )
  assume cvmlift2lem9.4: |- ( ph -> V e. II )
  assume cvmlift2lem9.5: |- ( ph -> ( II |`t U ) e. Conn )
  assume cvmlift2lem9.6: |- ( ph -> ( II |`t V ) e. Conn )
  assume cvmlift2lem9.7: |- ( ph -> X e. U )
  assume cvmlift2lem9.8: |- ( ph -> Y e. V )
  assume cvmlift2lem9.9: |- ( ph -> ( U X. V ) C_ ( `' G " M ) )
  assume cvmlift2lem9.10: |- ( ph -> Z e. V )
  assume cvmlift2lem9.11: |- ( ph -> ( K |` ( U X. { Z } ) ) e. ( ( ( II tX II ) |`t ( U X. { Z } ) ) Cn C ) )
  assume cvmlift2lem9.w: |- W = ( iota_ b e. T ( X K Y ) e. b )

  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint K b
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint K c
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint K d
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint K f
  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b k
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint c d
  disjoint c f
  disjoint c k
  disjoint c s
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint d f
  disjoint d k
  disjoint d s
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f k
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint b ph
  disjoint f ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint M b
  disjoint M c
  disjoint M d
  disjoint M k
  disjoint M s
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint S b
  disjoint S f
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint J b
  disjoint J c
  disjoint J d
  disjoint J f
  disjoint J k
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint T s
  disjoint U z
  disjoint G b
  disjoint G c
  disjoint G f
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint W c
  disjoint W d
  disjoint H b
  disjoint H c
  disjoint H f
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X f
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Z z
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C f
  disjoint C k
  disjoint C s
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint P f
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y f
  disjoint Y k
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
  disjoint b g
  disjoint b m
  disjoint b n
  disjoint b r
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint c g
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint d g
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint f g
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
  disjoint b g
  disjoint b h
  disjoint b m
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint c g
  disjoint c h
  disjoint c m
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint d g
  disjoint d h
  disjoint d m
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint f g
  disjoint f h
  disjoint f m
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
  disjoint k u
  disjoint k v
  disjoint k w
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
  disjoint c r
  disjoint d r
  disjoint k r
  disjoint r s
  disjoint M r
  disjoint M u
  disjoint S m
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint J g
  disjoint J m
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint T u
  disjoint T v
  disjoint U m
  disjoint U n
  disjoint U u
  disjoint U w
  disjoint a h
  disjoint G a
  disjoint c t
  disjoint G g
  disjoint h t
  disjoint G h
  disjoint k t
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
  disjoint d n
  disjoint W m
  disjoint W n
  disjoint W u
  disjoint W v
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint X a
  disjoint d t
  disjoint X m
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint C a
  disjoint C g
  disjoint h r
  disjoint C h
  disjoint C m
  disjoint C r
  disjoint s t
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint P g
  disjoint P h
  disjoint P u
  disjoint P v
  disjoint B v
  disjoint B w
  disjoint Y a
  disjoint Y m
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  assert |- ( ph -> ( K |` ( U X. V ) ) e. ( ( ( II tX II ) |`t ( U X. V ) ) Cn C ) )

  proof
    wph
    cM
    cB
    cC
    cS
    cT
    vk
    cF
    cK
    cJ
    cii
    cii
    ctx
    co
    #
    cU
    cV
    cxp
    #
    cW
    cX
    cY
    cop
    #
    cc0
    c1
    cicc
    co
    #
    @3
    cxp
    #
    vs
    vc
    vd
    cvmlift2.b
    cii
    cii
    @3
    @3
    iitop
    iitop
    iiuni
    iiuni
    txunii
    #
    cvmlift2lem10.s
    cvmlift2.f
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
    cvmlift2lem5
    #
    wph
    cF
    cK
    ccom
    #
    cG
    @0
    cJ
    ccn
    co
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
    #
    cvmlift2.g
    eqeltrd
    @0
    ctop
    wcel
    #
    wph
    cii
    cii
    iitop
    iitop
    txtopi
    #
    a1i
    #
    wph
    cX
    @3
    wcel
    #
    cY
    @3
    wcel
    @2
    @4
    wcel
    #
    wph
    cU
    @3
    cX
    wph
    cU
    cii
    wcel
    #
    cU
    @3
    wss
    #
    cvmlift2lem9.3
    @14
    cU
    cii
    cuni
    #
    @3
    cU
    cii
    elssuni
    iiuni
    syl6sseqr
    syl
    #
    cvmlift2lem9.7
    sseldd
    #
    wph
    cV
    @3
    cY
    wph
    cV
    cii
    wcel
    #
    cV
    @3
    wss
    #
    cvmlift2lem9.4
    @19
    cV
    @16
    @3
    cV
    cii
    elssuni
    iiuni
    syl6sseqr
    #
    syl
    #
    cvmlift2lem9.8
    sseldd
    #
    cX
    cY
    @3
    @3
    opelxpi
    syl2anc
    #
    cvmlift2lem9.2
    wph
    cW
    cT
    wcel
    #
    cX
    cY
    cK
    co
    #
    cW
    wcel
    #
    wa
    #
    @25
    @2
    cK
    cfv
    #
    cW
    wcel
    #
    wa
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cT
    cM
    cS
    cfv
    wcel
    #
    @26
    cB
    wcel
    @26
    cF
    cfv
    #
    cM
    wcel
    @28
    cvmlift2.f
    cvmlift2lem9.2
    wph
    cX
    cY
    cB
    @3
    @3
    cK
    @6
    @18
    @23
    fovrnd
    wph
    @33
    cX
    cY
    cG
    co
    #
    cM
    wph
    @29
    cF
    cfv
    #
    @2
    cG
    cfv
    #
    @33
    @34
    wph
    @2
    @7
    cfv
    #
    @35
    @36
    wph
    @4
    cB
    cK
    wf
    #
    @13
    @37
    @35
    wceq
    @6
    @24
    @4
    cB
    @2
    cF
    cK
    fvco3
    syl2anc
    wph
    @2
    @7
    cG
    @8
    fveq1d
    eqtr3d
    @26
    @29
    cF
    cX
    cY
    cK
    df-ov
    #
    fveq2i
    cX
    cY
    cG
    df-ov
    3eqtr4g
    cvmlift2lem9.1
    eqeltrd
    vb
    vd
    vc
    @26
    cB
    cC
    cS
    cT
    cM
    vk
    cF
    cJ
    cW
    vs
    cvmlift2lem10.s
    cvmlift2.b
    cvmlift2lem9.w
    cvmsiota
    syl13anc
    #
    @27
    @30
    @25
    @26
    @29
    cW
    @39
    eleq1i
    anbi2i
    sylib
    wph
    @15
    @20
    @1
    @4
    wss
    @17
    @22
    cU
    @3
    cV
    @3
    xpss12
    syl2anc
    #
    wph
    cK
    @1
    cima
    #
    cW
    wss
    #
    vm
    cv
    #
    vn
    cv
    #
    cK
    co
    #
    cW
    wcel
    #
    vn
    cV
    wral
    vm
    cU
    wral
    #
    wph
    @47
    vm
    vn
    cU
    cV
    wph
    @44
    cU
    wcel
    #
    @45
    cV
    wcel
    #
    wa
    #
    wa
    #
    @44
    @45
    cK
    @44
    csn
    #
    cV
    cxp
    #
    cres
    #
    co
    #
    @46
    cW
    @52
    @44
    @53
    wcel
    #
    @50
    @56
    @46
    wceq
    @49
    @57
    wph
    @50
    @44
    cU
    snidg
    ad2antrl
    #
    wph
    @49
    @50
    simprr
    #
    @44
    @45
    @53
    cV
    cK
    ovres
    syl2anc
    @52
    @44
    @45
    cW
    @53
    cV
    @55
    @52
    @54
    cW
    @55
    wf
    @0
    @54
    crest
    co
    #
    cuni
    #
    cW
    @55
    wf
    @52
    @44
    cZ
    cop
    #
    cW
    @55
    @60
    cC
    cF
    ccnv
    #
    cM
    cima
    #
    crest
    co
    #
    @61
    @61
    eqid
    @52
    @60
    cii
    @53
    crest
    co
    #
    cii
    cV
    crest
    co
    #
    ctx
    co
    #
    cconn
    @52
    cii
    ctop
    wcel
    #
    @69
    @53
    cvv
    wcel
    #
    @19
    @60
    @68
    wceq
    @69
    @52
    iitop
    a1i
    #
    @71
    @70
    @52
    @44
    snex
    #
    a1i
    wph
    @19
    @51
    cvmlift2lem9.4
    adantr
    @53
    cV
    cii
    cii
    ctop
    ctop
    cvv
    cii
    txrest
    syl22anc
    @52
    @66
    cconn
    wcel
    @67
    cconn
    wcel
    #
    @68
    cconn
    wcel
    @52
    @66
    @53
    cpw
    #
    cconn
    @52
    cii
    @3
    ctopon
    cfv
    wcel
    #
    @44
    @3
    wcel
    #
    @66
    @74
    wceq
    iitopon
    wph
    @49
    @76
    @50
    wph
    cU
    @3
    @44
    @17
    sselda
    adantrr
    #
    @44
    cii
    @3
    restsn2
    sylancr
    @74
    c0
    @53
    cpr
    cconn
    @44
    pwsn
    @53
    indisconn
    eqeltri
    syl6eqel
    wph
    @73
    @51
    cvmlift2lem9.6
    adantr
    @66
    @67
    txconn
    syl2anc
    eqeltrd
    @52
    @55
    @60
    cC
    ccn
    co
    #
    wcel
    #
    @55
    @60
    @65
    ccn
    co
    wcel
    #
    @52
    cK
    @53
    @3
    cxp
    #
    cres
    #
    @54
    cres
    #
    @0
    @81
    crest
    co
    #
    @54
    crest
    co
    #
    cC
    ccn
    co
    #
    @55
    @78
    @52
    @82
    @84
    cC
    ccn
    co
    wcel
    #
    @54
    @84
    cuni
    #
    wss
    @83
    @86
    wcel
    wph
    @51
    @76
    @87
    @77
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
    @44
    cvmlift2.b
    cvmlift2.f
    cvmlift2.g
    cvmlift2.p
    cvmlift2.i
    cvmlift2.h
    cvmlift2.k
    cvmlift2lem6
    syldan
    @52
    @54
    @81
    @88
    @52
    @20
    @54
    @81
    wss
    #
    wph
    @20
    @51
    @22
    adantr
    cV
    @3
    @53
    xpss2
    syl
    #
    @52
    @9
    @81
    @4
    wss
    #
    @81
    @88
    wceq
    @10
    @52
    @53
    @3
    wss
    @91
    @52
    @44
    @3
    @77
    snssd
    @53
    @3
    @3
    xpss1
    syl
    #
    @81
    @0
    @4
    @5
    restuni
    sylancr
    sseqtrd
    @54
    @82
    @84
    cC
    @88
    @88
    eqid
    cnrest
    syl2anc
    @52
    cK
    @54
    @81
    @90
    resabs1d
    @52
    @85
    @60
    cC
    ccn
    @52
    @9
    @89
    @81
    cvv
    wcel
    #
    @85
    @60
    wceq
    @9
    @52
    @10
    a1i
    @90
    @93
    @52
    @53
    @3
    @72
    cc0
    c1
    cicc
    ovex
    #
    xpex
    a1i
    @54
    @81
    @0
    ctop
    cvv
    restabs
    syl3anc
    oveq1d
    3eltr3d
    @52
    cC
    cB
    ctopon
    cfv
    wcel
    #
    @55
    crn
    #
    @64
    wss
    @64
    cB
    wss
    #
    @79
    @80
    wb
    @52
    cC
    ctop
    wcel
    #
    @95
    wph
    @98
    @51
    wph
    @31
    @98
    cvmlift2.f
    cC
    cF
    cJ
    cvmtop1
    syl
    #
    adantr
    cC
    cB
    cvmlift2.b
    toptopon
    #
    sylib
    @52
    @96
    cK
    @54
    cima
    #
    @64
    cK
    @54
    df-ima
    @52
    @101
    @42
    @64
    @52
    @53
    cU
    wss
    @54
    @1
    wss
    @101
    @42
    wss
    @52
    @44
    cU
    wph
    @49
    @50
    simprl
    #
    snssd
    @53
    cU
    cV
    xpss1
    @54
    @1
    cK
    imass2
    3syl
    wph
    @42
    @64
    wss
    #
    @51
    wph
    @103
    @1
    cK
    ccnv
    #
    @64
    cima
    #
    wss
    #
    wph
    @1
    cG
    ccnv
    #
    cM
    cima
    #
    @105
    cvmlift2lem9.9
    wph
    @105
    @104
    @63
    ccom
    #
    cM
    cima
    @108
    @104
    @63
    cM
    imaco
    wph
    @109
    @107
    cM
    wph
    @109
    @7
    ccnv
    @107
    cF
    cK
    cnvco
    wph
    @7
    cG
    @8
    cnveqd
    syl5eqr
    imaeq1d
    syl5eqr
    sseqtr4d
    wph
    cK
    wfun
    #
    @1
    cK
    cdm
    #
    wss
    #
    @103
    @106
    wb
    wph
    @38
    @110
    @6
    @4
    cB
    cK
    ffun
    syl
    #
    wph
    @1
    @4
    @111
    @41
    wph
    @38
    @111
    @4
    wceq
    @6
    @4
    cB
    cK
    fdm
    syl
    sseqtr4d
    #
    @1
    @64
    cK
    funimass3
    syl2anc
    mpbird
    #
    adantr
    sstrd
    syl5eqssr
    wph
    @97
    @51
    wph
    cF
    cdm
    #
    @64
    cB
    cF
    cM
    cnvimass
    wph
    cF
    cC
    cJ
    ccn
    co
    wcel
    #
    cB
    cJ
    cuni
    #
    cF
    wf
    @116
    cB
    wceq
    wph
    @31
    @117
    cvmlift2.f
    cC
    cF
    cJ
    cvmcn
    syl
    #
    cF
    cC
    cJ
    cB
    @118
    cvmlift2.b
    @118
    eqid
    cnf
    cB
    @118
    cF
    fdm
    3syl
    syl5sseq
    #
    adantr
    @64
    @55
    @60
    cC
    cB
    cnrest2
    syl3anc
    mpbid
    wph
    cW
    @65
    wcel
    #
    @51
    wph
    @121
    cW
    cC
    wcel
    #
    cW
    @64
    wss
    #
    wph
    cT
    cC
    cW
    wph
    @32
    cT
    cC
    wss
    cvmlift2lem9.2
    vd
    vc
    cC
    cS
    cT
    cM
    vk
    cF
    cJ
    vs
    cvmlift2lem10.s
    cvmsss
    syl
    wph
    @25
    @27
    @40
    simpld
    #
    sseldd
    wph
    cW
    cT
    cuni
    #
    @64
    wph
    @25
    cW
    @125
    wss
    @124
    cW
    cT
    elssuni
    syl
    wph
    @32
    @125
    @64
    wceq
    cvmlift2lem9.2
    vd
    vc
    cC
    cS
    cT
    cM
    vk
    cF
    cJ
    vs
    cvmlift2lem10.s
    cvmsuni
    syl
    sseqtrd
    wph
    @98
    @64
    cC
    wcel
    #
    @121
    @122
    @123
    wa
    wb
    @99
    wph
    @117
    cM
    cJ
    wcel
    #
    @126
    @119
    wph
    @32
    @127
    cvmlift2lem9.2
    vd
    vc
    cC
    cS
    cT
    cM
    vk
    cF
    cJ
    vs
    cvmlift2lem10.s
    cvmsrcl
    syl
    cM
    cF
    cC
    cJ
    cnima
    syl2anc
    @64
    cW
    cC
    restopn2
    syl2anc
    mpbir2and
    #
    adantr
    wph
    cW
    @65
    ccld
    cfv
    wcel
    #
    @51
    wph
    @31
    @32
    @25
    @129
    cvmlift2.f
    cvmlift2lem9.2
    @124
    vd
    vc
    cW
    cC
    cS
    cT
    cM
    vk
    cF
    cJ
    vs
    cvmlift2lem10.s
    cvmscld
    syl3anc
    #
    adantr
    @52
    @62
    @54
    @61
    @52
    @57
    cZ
    cV
    wcel
    #
    @62
    @54
    wcel
    @58
    wph
    @131
    @51
    cvmlift2lem9.10
    adantr
    #
    @44
    cZ
    @53
    cV
    opelxpi
    syl2anc
    @52
    @9
    @54
    @4
    wss
    @54
    @61
    wceq
    @10
    @52
    @54
    @81
    @4
    @90
    @92
    sstrd
    @54
    @0
    @4
    @5
    restuni
    sylancr
    #
    eleqtrd
    @52
    @62
    @55
    cfv
    #
    @44
    cZ
    cK
    cU
    cZ
    csn
    #
    cxp
    #
    cres
    #
    co
    #
    cW
    @52
    @134
    @44
    cZ
    @55
    co
    #
    @138
    @44
    cZ
    @55
    df-ov
    @52
    @139
    @44
    cZ
    cK
    co
    #
    @138
    @52
    @57
    @131
    @139
    @140
    wceq
    @58
    @132
    @44
    cZ
    @53
    cV
    cK
    ovres
    syl2anc
    @52
    @49
    cZ
    @135
    wcel
    #
    @138
    @140
    wceq
    @102
    wph
    @141
    @51
    wph
    @131
    @141
    cvmlift2lem9.10
    cZ
    cV
    snidg
    syl
    #
    adantr
    #
    @44
    cZ
    cU
    @135
    cK
    ovres
    syl2anc
    eqtr4d
    syl5eqr
    @52
    @44
    cZ
    cW
    cU
    @135
    @137
    wph
    @136
    cW
    @137
    wf
    #
    @51
    wph
    @144
    @0
    @136
    crest
    co
    #
    cuni
    #
    cW
    @137
    wf
    wph
    cX
    cZ
    cop
    #
    cW
    @137
    @145
    @65
    @146
    @146
    eqid
    wph
    @145
    cii
    cU
    crest
    co
    #
    cii
    @135
    crest
    co
    #
    ctx
    co
    #
    cconn
    wph
    @69
    @69
    @14
    @135
    cvv
    wcel
    #
    @145
    @150
    wceq
    @69
    wph
    iitop
    a1i
    #
    @152
    cvmlift2lem9.3
    @151
    wph
    cZ
    snex
    a1i
    cU
    @135
    cii
    cii
    ctop
    ctop
    cii
    cvv
    txrest
    syl22anc
    wph
    @148
    cconn
    wcel
    @149
    cconn
    wcel
    @150
    cconn
    wcel
    cvmlift2lem9.5
    wph
    @149
    @135
    cpw
    #
    cconn
    wph
    @75
    cZ
    @3
    wcel
    @149
    @153
    wceq
    iitopon
    wph
    cV
    @3
    cZ
    @22
    cvmlift2lem9.10
    sseldd
    #
    cZ
    cii
    @3
    restsn2
    sylancr
    @153
    c0
    @135
    cpr
    cconn
    cZ
    pwsn
    @135
    indisconn
    eqeltri
    syl6eqel
    @148
    @149
    txconn
    syl2anc
    eqeltrd
    wph
    @137
    @145
    cC
    ccn
    co
    wcel
    #
    @137
    @145
    @65
    ccn
    co
    wcel
    #
    cvmlift2lem9.11
    wph
    @95
    @137
    crn
    #
    @64
    wss
    @97
    @155
    @156
    wb
    wph
    @98
    @95
    @99
    @100
    sylib
    #
    wph
    @157
    cK
    @136
    cima
    #
    @64
    cK
    @136
    df-ima
    wph
    @159
    @42
    @64
    wph
    @135
    cV
    wss
    @136
    @1
    wss
    @159
    @42
    wss
    wph
    cZ
    cV
    cvmlift2lem9.10
    snssd
    @135
    cV
    cU
    xpss2
    @136
    @1
    cK
    imass2
    3syl
    @115
    sstrd
    syl5eqssr
    @120
    @64
    @137
    @145
    cC
    cB
    cnrest2
    syl3anc
    mpbid
    @128
    @130
    wph
    @147
    @136
    @146
    wph
    cX
    cU
    wcel
    #
    @141
    @147
    @136
    wcel
    cvmlift2lem9.7
    @142
    cX
    cZ
    cU
    @135
    opelxpi
    syl2anc
    wph
    @9
    @136
    @4
    wss
    #
    @136
    @146
    wceq
    @10
    wph
    @15
    @135
    @3
    wss
    @161
    @17
    wph
    cZ
    @3
    @154
    snssd
    cU
    @3
    @135
    @3
    xpss12
    syl2anc
    @136
    @0
    @4
    @5
    restuni
    sylancr
    #
    eleqtrd
    wph
    @147
    @137
    cfv
    #
    cX
    cZ
    cK
    cX
    csn
    #
    cV
    cxp
    #
    cres
    #
    co
    #
    cW
    wph
    @163
    cX
    cZ
    @137
    co
    #
    @167
    cX
    cZ
    @137
    df-ov
    wph
    @168
    cX
    cZ
    cK
    co
    #
    @167
    wph
    @160
    @141
    @168
    @169
    wceq
    cvmlift2lem9.7
    @142
    cX
    cZ
    cU
    @135
    cK
    ovres
    syl2anc
    wph
    cX
    @164
    wcel
    #
    @131
    @167
    @169
    wceq
    wph
    @160
    @170
    cvmlift2lem9.7
    cX
    cU
    snidg
    syl
    #
    cvmlift2lem9.10
    cX
    cZ
    @164
    cV
    cK
    ovres
    syl2anc
    eqtr4d
    syl5eqr
    wph
    cX
    cZ
    cW
    @164
    cV
    @166
    wph
    @165
    cW
    @166
    wf
    @0
    @165
    crest
    co
    #
    cuni
    #
    cW
    @166
    wf
    wph
    @2
    cW
    @166
    @172
    @65
    @173
    @173
    eqid
    wph
    @172
    cii
    @164
    crest
    co
    #
    @67
    ctx
    co
    #
    cconn
    wph
    @69
    @69
    @164
    cvv
    wcel
    #
    @19
    @172
    @175
    wceq
    @152
    @152
    @176
    wph
    cX
    snex
    #
    a1i
    cvmlift2lem9.4
    @164
    cV
    cii
    cii
    ctop
    ctop
    cvv
    cii
    txrest
    syl22anc
    wph
    @174
    cconn
    wcel
    @73
    @175
    cconn
    wcel
    wph
    @174
    @164
    cpw
    #
    cconn
    wph
    @75
    @12
    @174
    @178
    wceq
    iitopon
    @18
    cX
    cii
    @3
    restsn2
    sylancr
    @178
    c0
    @164
    cpr
    cconn
    cX
    pwsn
    @164
    indisconn
    eqeltri
    syl6eqel
    cvmlift2lem9.6
    @174
    @67
    txconn
    syl2anc
    eqeltrd
    wph
    @166
    @172
    cC
    ccn
    co
    #
    wcel
    #
    @166
    @172
    @65
    ccn
    co
    wcel
    #
    wph
    cK
    @164
    @3
    cxp
    #
    cres
    #
    @165
    cres
    #
    @0
    @182
    crest
    co
    #
    @165
    crest
    co
    #
    cC
    ccn
    co
    #
    @166
    @179
    wph
    @183
    @185
    cC
    ccn
    co
    wcel
    #
    @165
    @185
    cuni
    #
    wss
    @184
    @187
    wcel
    wph
    @12
    @188
    @18
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
    cX
    cvmlift2.b
    cvmlift2.f
    cvmlift2.g
    cvmlift2.p
    cvmlift2.i
    cvmlift2.h
    cvmlift2.k
    cvmlift2lem6
    mpdan
    wph
    @165
    @182
    @189
    wph
    @19
    @20
    @165
    @182
    wss
    #
    cvmlift2lem9.4
    @21
    cV
    @3
    @164
    xpss2
    3syl
    #
    wph
    @9
    @182
    @4
    wss
    #
    @182
    @189
    wceq
    @10
    wph
    @164
    @3
    wss
    @192
    wph
    cX
    @3
    @18
    snssd
    @164
    @3
    @3
    xpss1
    syl
    @182
    @0
    @4
    @5
    restuni
    sylancr
    sseqtrd
    @165
    @183
    @185
    cC
    @189
    @189
    eqid
    cnrest
    syl2anc
    wph
    cK
    @165
    @182
    @191
    resabs1d
    wph
    @186
    @172
    cC
    ccn
    wph
    @9
    @190
    @182
    cvv
    wcel
    #
    @186
    @172
    wceq
    @11
    @191
    @193
    wph
    @164
    @3
    @177
    @94
    xpex
    a1i
    @165
    @182
    @0
    ctop
    cvv
    restabs
    syl3anc
    oveq1d
    3eltr3d
    wph
    @95
    @166
    crn
    #
    @64
    wss
    @97
    @180
    @181
    wb
    @158
    wph
    @194
    cK
    @165
    cima
    #
    @64
    cK
    @165
    df-ima
    wph
    @195
    @42
    @64
    wph
    @164
    cU
    wss
    #
    @165
    @1
    wss
    #
    @195
    @42
    wss
    wph
    cX
    cU
    cvmlift2lem9.7
    snssd
    #
    @164
    cU
    cV
    xpss1
    #
    @165
    @1
    cK
    imass2
    3syl
    @115
    sstrd
    syl5eqssr
    @120
    @64
    @166
    @172
    cC
    cB
    cnrest2
    syl3anc
    mpbid
    @128
    @130
    wph
    @2
    @165
    @173
    wph
    @170
    cY
    cV
    wcel
    #
    @2
    @165
    wcel
    @171
    cvmlift2lem9.8
    cX
    cY
    @164
    cV
    opelxpi
    syl2anc
    wph
    @9
    @165
    @4
    wss
    @165
    @173
    wceq
    @10
    wph
    @165
    @1
    @4
    wph
    @196
    @197
    @198
    @199
    syl
    @41
    sstrd
    @165
    @0
    @4
    @5
    restuni
    sylancr
    #
    eleqtrd
    wph
    @2
    @166
    cfv
    #
    @26
    cW
    wph
    @202
    cX
    cY
    @166
    co
    #
    @26
    cX
    cY
    @166
    df-ov
    wph
    @170
    @200
    @203
    @26
    wceq
    @171
    cvmlift2lem9.8
    cX
    cY
    @164
    cV
    cK
    ovres
    syl2anc
    syl5eqr
    wph
    @25
    @27
    @40
    simprd
    eqeltrd
    conncn
    wph
    @165
    @173
    cW
    @166
    @201
    feq2d
    mpbird
    @171
    cvmlift2lem9.10
    fovrnd
    eqeltrd
    conncn
    wph
    @136
    @146
    cW
    @137
    @162
    feq2d
    mpbird
    adantr
    @102
    @143
    fovrnd
    eqeltrd
    conncn
    @52
    @54
    @61
    cW
    @55
    @133
    feq2d
    mpbird
    @58
    @59
    fovrnd
    eqeltrrd
    ralrimivva
    wph
    @110
    @112
    @43
    @48
    wb
    @113
    @114
    vm
    vn
    cU
    cV
    cW
    cK
    funimassov
    syl2anc
    mpbird
    cvmlift2lem9a
end
