include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cii.mm"
include "ctx.mm"
include "co.mm"
include "ccnp.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "crab.mm"
include "adantr.mm"
include "cuni.mm"
include "elssuni.mm"
include "iiuni.mm"
include "syl6sseqr.mm"
include "syl.mm"
include "elunii.mm"
include "syl6eleqr.mm"
include "syl2anc.mm"
include "snssd.mm"
include "xpss12.mm"
include "cres.mm"
include "crest.mm"
include "ccn.mm"
include "wrex.mm"
include "wf.mm"
include "wral.mm"
include "cvmlift2lem5.mm"
include "sseldd.mm"
include "fssresd.mm"
include "simpr.mm"
include "syl6sseq.mm"
include "ssrab.mm"
include "simprbi.mm"
include "r19.21bi.mm"
include "ctopon.mm"
include "iitopon.mm"
include "txtopon.mm"
include "mp2an.mm"
include "toponunii.mm"
include "cnpresti.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "resttopon.mm"
include "sylancr.mm"
include "ctop.mm"
include "ccvm.mm"
include "cvmtop1.mm"
include "toptopon.mm"
include "sylib.mm"
include "cncnp.mm"
include "mpbir2and.mm"
include "wceq.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "reseq2d.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eleq12d.mm"
include "rspcev.mm"
include "imp.mm"
include "syldan.mm"
include "xpss2.mm"
include "iitop.mm"
include "txtopi.mm"
include "restuni.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "eqid.mm"
include "cncnpi.mm"
include "cnt.mm"
include "a1i.mm"
include "txopn.mm"
include "syl22anc.mm"
include "isopn3i.mm"
include "sseqtr4d.mm"
include "ad2antrr.mm"
include "cnprest.mm"
include "mpbird.mm"
include "ssrabdv.mm"
include "ex.mm"

theorem cvmlift2lem11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cP: class P
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cV: class V
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vh: setvar h
  let vk: setvar k
  let vs: setvar s
  let cA: class A
  let cS: class S
  let cT: class T
  let cW: class W
  let cX: class X
  assume cvmlift2.b: |- B = U. C
  assume cvmlift2.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift2.g: |- ( ph -> G e. ( ( II tX II ) Cn J ) )
  assume cvmlift2.p: |- ( ph -> P e. B )
  assume cvmlift2.i: |- ( ph -> ( F ` P ) = ( 0 G 0 ) )
  assume cvmlift2.h: |- H = ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( z G 0 ) ) /\ ( f ` 0 ) = P ) )
  assume cvmlift2.k: |- K = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> ( ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( x G z ) ) /\ ( f ` 0 ) = ( H ` x ) ) ) ` y ) )
  assume cvmlift2.m: |- M = { z e. ( ( 0 [,] 1 ) X. ( 0 [,] 1 ) ) | K e. ( ( ( II tX II ) CnP C ) ` z ) }
  assume cvmlift2lem11.1: |- ( ph -> U e. II )
  assume cvmlift2lem11.2: |- ( ph -> V e. II )
  assume cvmlift2lem11.3: |- ( ph -> Y e. V )
  assume cvmlift2lem11.4: |- ( ph -> Z e. V )
  assume cvmlift2lem11.5: |- ( ph -> ( E. w e. V ( K |` ( U X. { w } ) ) e. ( ( ( II tX II ) |`t ( U X. { w } ) ) Cn C ) -> ( K |` ( U X. V ) ) e. ( ( ( II tX II ) |`t ( U X. V ) ) Cn C ) ) )

  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint K f
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
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
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
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint J f
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint U w
  disjoint U z
  disjoint G f
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint V w
  disjoint H f
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint Z z
  disjoint C f
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint P f
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint Y f
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
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
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint f r
  disjoint f t
  disjoint f u
  disjoint f v
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
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f m
  disjoint f s
  disjoint f u
  disjoint f v
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
  disjoint ph u
  disjoint ph v
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
  disjoint J g
  disjoint J k
  disjoint J m
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint U m
  disjoint U n
  disjoint U u
  disjoint a h
  disjoint G a
  disjoint G b
  disjoint c t
  disjoint G c
  disjoint G g
  disjoint h t
  disjoint G h
  disjoint k t
  disjoint G k
  disjoint G m
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint V m
  disjoint V n
  disjoint V u
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
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C g
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
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P u
  disjoint P v
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B v
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y k
  disjoint Y m
  disjoint Y t
  disjoint Y u
  disjoint Y v
  assert |- ( ph -> ( ( U X. { Y } ) C_ M -> ( U X. { Z } ) C_ M ) )

  proof
    wph
    cU
    cY
    csn
    #
    cxp
    #
    cM
    wss
    #
    cU
    cZ
    csn
    #
    cxp
    #
    cM
    wss
    wph
    @2
    wa
    #
    @4
    cK
    vz
    cv
    #
    cii
    cii
    ctx
    co
    #
    cC
    ccnp
    co
    cfv
    wcel
    #
    vz
    cc0
    c1
    cicc
    co
    #
    @9
    cxp
    #
    crab
    #
    cM
    @5
    @8
    vz
    @10
    @4
    @5
    cU
    @9
    wss
    #
    @3
    @9
    wss
    @4
    @10
    wss
    @5
    cU
    cii
    wcel
    #
    @12
    wph
    @13
    @2
    cvmlift2lem11.1
    adantr
    #
    @13
    cU
    cii
    cuni
    #
    @9
    cU
    cii
    elssuni
    iiuni
    syl6sseqr
    syl
    #
    @5
    cZ
    @9
    wph
    cZ
    @9
    wcel
    #
    @2
    wph
    cZ
    cV
    wcel
    #
    cV
    cii
    wcel
    #
    @17
    cvmlift2lem11.4
    cvmlift2lem11.2
    @18
    @19
    wa
    cZ
    @15
    @9
    cZ
    cV
    cii
    elunii
    iiuni
    syl6eleqr
    syl2anc
    adantr
    snssd
    cU
    @9
    @3
    @9
    xpss12
    syl2anc
    @5
    @6
    @4
    wcel
    #
    wa
    #
    @8
    cK
    cU
    cV
    cxp
    #
    cres
    #
    @6
    @7
    @22
    crest
    co
    #
    cC
    ccnp
    co
    cfv
    wcel
    #
    @21
    @23
    @24
    cC
    ccn
    co
    wcel
    #
    @6
    @24
    cuni
    #
    wcel
    @25
    @5
    @26
    @20
    wph
    @2
    cK
    cU
    vw
    cv
    #
    csn
    #
    cxp
    #
    cres
    #
    @7
    @30
    crest
    co
    #
    cC
    ccn
    co
    #
    wcel
    #
    vw
    cV
    wrex
    #
    @26
    @5
    cY
    cV
    wcel
    #
    cK
    @1
    cres
    #
    @7
    @1
    crest
    co
    #
    cC
    ccn
    co
    #
    wcel
    #
    @35
    wph
    @36
    @2
    cvmlift2lem11.3
    adantr
    #
    @5
    @40
    @1
    cB
    @37
    wf
    #
    @37
    @6
    @38
    cC
    ccnp
    co
    cfv
    wcel
    #
    vz
    @1
    wral
    #
    @5
    @10
    cB
    @1
    cK
    wph
    @10
    cB
    cK
    wf
    #
    @2
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
    adantr
    @5
    @12
    @0
    @9
    wss
    @1
    @10
    wss
    #
    @16
    @5
    cY
    @9
    @5
    cV
    @9
    cY
    @5
    @19
    cV
    @9
    wss
    #
    wph
    @19
    @2
    cvmlift2lem11.2
    adantr
    #
    @19
    cV
    @15
    @9
    cV
    cii
    elssuni
    iiuni
    syl6sseqr
    syl
    #
    @41
    sseldd
    snssd
    cU
    @9
    @0
    @9
    xpss12
    syl2anc
    #
    fssresd
    @5
    @43
    vz
    @1
    @5
    @6
    @1
    wcel
    #
    wa
    @47
    @52
    @8
    @43
    @5
    @47
    @52
    @51
    adantr
    @5
    @52
    simpr
    @5
    @8
    vz
    @1
    @5
    @1
    @11
    wss
    #
    @8
    vz
    @1
    wral
    #
    @5
    @1
    cM
    @11
    wph
    @2
    simpr
    cvmlift2.m
    syl6sseq
    @53
    @47
    @54
    @8
    vz
    @10
    @1
    ssrab
    simprbi
    syl
    r19.21bi
    @1
    @6
    cK
    @7
    cC
    @10
    @10
    @7
    cii
    @9
    ctopon
    cfv
    wcel
    #
    @55
    @7
    @10
    ctopon
    cfv
    wcel
    #
    iitopon
    iitopon
    cii
    cii
    @9
    @9
    txtopon
    mp2an
    #
    toponunii
    #
    cnpresti
    syl3anc
    ralrimiva
    @5
    @38
    @1
    ctopon
    cfv
    wcel
    #
    cC
    cB
    ctopon
    cfv
    wcel
    #
    @40
    @42
    @44
    wa
    wb
    @5
    @56
    @47
    @59
    @57
    @51
    @1
    @7
    @10
    resttopon
    sylancr
    @5
    cC
    ctop
    wcel
    #
    @60
    wph
    @61
    @2
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    @61
    cvmlift2.f
    cC
    cF
    cJ
    cvmtop1
    syl
    adantr
    cC
    cB
    cvmlift2.b
    toptopon
    sylib
    vz
    @37
    @38
    cC
    @1
    cB
    cncnp
    syl2anc
    mpbir2and
    @34
    @40
    vw
    cY
    cV
    @28
    cY
    wceq
    #
    @31
    @37
    @33
    @39
    @62
    @30
    @1
    cK
    @62
    @29
    @0
    cU
    @28
    cY
    sneq
    xpeq2d
    #
    reseq2d
    @62
    @32
    @38
    cC
    ccn
    @62
    @30
    @1
    @7
    crest
    @63
    oveq2d
    oveq1d
    eleq12d
    rspcev
    syl2anc
    wph
    @35
    @26
    cvmlift2lem11.5
    imp
    syldan
    adantr
    @5
    @4
    @27
    @6
    @5
    @4
    @22
    @27
    @5
    @3
    cV
    wss
    @4
    @22
    wss
    @5
    cZ
    cV
    wph
    @18
    @2
    cvmlift2lem11.4
    adantr
    snssd
    @3
    cV
    cU
    xpss2
    syl
    #
    @5
    @7
    ctop
    wcel
    #
    @22
    @10
    wss
    #
    @22
    @27
    wceq
    cii
    cii
    iitop
    iitop
    txtopi
    #
    @5
    @12
    @48
    @66
    @16
    @50
    cU
    @9
    cV
    @9
    xpss12
    syl2anc
    #
    @22
    @7
    @10
    @58
    restuni
    sylancr
    sseqtrd
    sselda
    @6
    @23
    @24
    cC
    @27
    @27
    eqid
    cncnpi
    syl2anc
    @21
    @65
    @66
    @6
    @22
    @7
    cnt
    cfv
    cfv
    #
    wcel
    @45
    @8
    @25
    wb
    @65
    @21
    @67
    a1i
    @5
    @66
    @20
    @68
    adantr
    @5
    @4
    @69
    @6
    @5
    @4
    @22
    @69
    @64
    @5
    @65
    @22
    @7
    wcel
    #
    @69
    @22
    wceq
    @67
    @5
    cii
    ctop
    wcel
    #
    @71
    @13
    @19
    @70
    @71
    @5
    iitop
    a1i
    #
    @72
    @14
    @49
    cU
    cV
    cii
    cii
    ctop
    ctop
    txopn
    syl22anc
    @22
    @7
    isopn3i
    sylancr
    sseqtr4d
    sselda
    wph
    @45
    @2
    @20
    @46
    ad2antrr
    @22
    @6
    cK
    @7
    cC
    @10
    cB
    @58
    cvmlift2.b
    cnprest
    syl22anc
    mpbird
    ssrabdv
    cvmlift2.m
    syl6sseqr
    ex
end
