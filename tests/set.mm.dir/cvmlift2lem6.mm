include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cres.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "wceq.mm"
include "cfv.mm"
include "cii.mm"
include "ccn.mm"
include "crio.mm"
include "cmpt2.mm"
include "ctx.mm"
include "crest.mm"
include "wfn.mm"
include "wf.mm"
include "cvmlift2lem5.mm"
include "adantr.mm"
include "ffn.mm"
include "syl.mm"
include "fnov.mm"
include "sylib.mm"
include "reseq1d.mm"
include "wss.mm"
include "simpr.mm"
include "snssd.mm"
include "ssid.mm"
include "resmpt2.mm"
include "sylancl.mm"
include "w3a.mm"
include "elsni.mm"
include "3ad2ant2.mm"
include "oveq1d.mm"
include "simp1r.mm"
include "simp3.mm"
include "cvmlift2lem4.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "mpt2eq3dva.mm"
include "eqid.mm"
include "ctopon.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnmpt2nd.mm"
include "cvmlift2lem3.mm"
include "simp1d.mm"
include "cnmpt21f.mm"
include "cnmpt2res.mm"
include "ctop.mm"
include "cvv.mm"
include "iitop.mm"
include "snex.mm"
include "ovex.mm"
include "txrest.mm"
include "mp4an.mm"
include "oveq1i.mm"
include "syl6eleqr.mm"
include "eqeltrd.mm"

theorem cvmlift2lem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cX: class X
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
  let cZ: class Z
  let cY: class Y
  assume cvmlift2.b: |- B = U. C
  assume cvmlift2.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift2.g: |- ( ph -> G e. ( ( II tX II ) Cn J ) )
  assume cvmlift2.p: |- ( ph -> P e. B )
  assume cvmlift2.i: |- ( ph -> ( F ` P ) = ( 0 G 0 ) )
  assume cvmlift2.h: |- H = ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( z G 0 ) ) /\ ( f ` 0 ) = P ) )
  assume cvmlift2.k: |- K = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> ( ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( x G z ) ) /\ ( f ` 0 ) = ( H ` x ) ) ) ` y ) )

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
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint f ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint J f
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint P f
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
  disjoint J g
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
  disjoint G g
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
  disjoint X k
  disjoint X m
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint Z z
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
  disjoint C w
  disjoint P g
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
  assert |- ( ( ph /\ X e. ( 0 [,] 1 ) ) -> ( K |` ( { X } X. ( 0 [,] 1 ) ) ) e. ( ( ( II tX II ) |`t ( { X } X. ( 0 [,] 1 ) ) ) Cn C ) )

  proof
    wph
    cX
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    wa
    #
    cK
    cX
    csn
    #
    @0
    cxp
    #
    cres
    #
    vu
    vv
    @3
    @0
    vv
    cv
    #
    cF
    vf
    cv
    #
    ccom
    vz
    @0
    cX
    vz
    cv
    cG
    co
    cmpt
    #
    wceq
    cc0
    @7
    cfv
    cX
    cH
    cfv
    #
    wceq
    wa
    vf
    cii
    cC
    ccn
    co
    #
    crio
    #
    cfv
    #
    cmpt2
    #
    cii
    cii
    ctx
    co
    @4
    crest
    co
    #
    cC
    ccn
    co
    #
    @2
    @5
    vu
    vv
    @0
    @0
    vu
    cv
    #
    @6
    cK
    co
    #
    cmpt2
    #
    @4
    cres
    #
    @13
    @2
    cK
    @18
    @4
    @2
    cK
    @0
    @0
    cxp
    #
    wfn
    #
    cK
    @18
    wceq
    @2
    @20
    cB
    cK
    wf
    #
    @21
    wph
    @22
    @1
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
    adantr
    @20
    cB
    cK
    ffn
    syl
    vu
    vv
    @0
    @0
    cK
    fnov
    sylib
    reseq1d
    @2
    @19
    vu
    vv
    @3
    @0
    @17
    cmpt2
    #
    @13
    @2
    @3
    @0
    wss
    @0
    @0
    wss
    #
    @19
    @23
    wceq
    @2
    cX
    @0
    wph
    @1
    simpr
    snssd
    #
    @0
    ssid
    #
    vu
    vv
    @0
    @0
    @3
    @0
    @17
    resmpt2
    sylancl
    @2
    vu
    vv
    @3
    @0
    @17
    @12
    @2
    @16
    @3
    wcel
    #
    @6
    @0
    wcel
    #
    w3a
    #
    @17
    cX
    @6
    cK
    co
    #
    @12
    @29
    @16
    cX
    @6
    cK
    @27
    @2
    @16
    cX
    wceq
    @28
    @16
    cX
    elsni
    3ad2ant2
    oveq1d
    @29
    @1
    @28
    @30
    @12
    wceq
    wph
    @1
    @27
    @28
    simp1r
    @2
    @27
    @28
    simp3
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
    @6
    cvmlift2.b
    cvmlift2.f
    cvmlift2.g
    cvmlift2.p
    cvmlift2.i
    cvmlift2.h
    cvmlift2.k
    cvmlift2lem4
    syl2anc
    eqtrd
    mpt2eq3dva
    eqtrd
    eqtrd
    @2
    @13
    cii
    @3
    crest
    co
    #
    cii
    @0
    crest
    co
    #
    ctx
    co
    #
    cC
    ccn
    co
    @15
    @2
    vu
    vv
    @12
    cii
    @31
    cC
    cii
    @32
    @0
    @0
    @3
    @0
    @31
    eqid
    cii
    @0
    ctopon
    cfv
    wcel
    @2
    iitopon
    a1i
    #
    @25
    @32
    eqid
    @34
    @24
    @2
    @26
    a1i
    @2
    vu
    vv
    @6
    @11
    cii
    cii
    cii
    cC
    @0
    @0
    @34
    @34
    @2
    vu
    vv
    cii
    cii
    @0
    @0
    @34
    @34
    cnmpt2nd
    @2
    @11
    @10
    wcel
    cF
    @11
    ccom
    @8
    wceq
    cc0
    @11
    cfv
    @9
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
    @11
    cX
    cvmlift2.b
    cvmlift2.f
    cvmlift2.g
    cvmlift2.p
    cvmlift2.i
    cvmlift2.h
    @11
    eqid
    cvmlift2lem3
    simp1d
    cnmpt21f
    cnmpt2res
    @14
    @33
    cC
    ccn
    cii
    ctop
    wcel
    #
    @35
    @3
    cvv
    wcel
    @0
    cvv
    wcel
    @14
    @33
    wceq
    iitop
    iitop
    cX
    snex
    cc0
    c1
    cicc
    ovex
    @3
    @0
    cii
    cii
    ctop
    ctop
    cvv
    cvv
    txrest
    mp4an
    oveq1i
    syl6eleqr
    eqeltrd
end
