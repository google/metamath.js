include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "wceq.mm"
include "cfv.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "crio.mm"
include "cmpt2.mm"
include "wcel.mm"
include "w3a.mm"
include "eqid.mm"
include "cvmlift2lem3.mm"
include "adantrr.mm"
include "simp2d.mm"
include "fveq1d.mm"
include "wf.mm"
include "simp1d.mm"
include "iiuni.mm"
include "cnf.mm"
include "syl.mm"
include "simprr.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "3eqtr3d.mm"
include "3impb.mm"
include "mpt2eq3dva.mm"
include "ffvelrnd.mm"
include "a1i.mm"
include "cuni.mm"
include "ccvm.mm"
include "cvmcn.mm"
include "3syl.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmpt2co.mm"
include "cxp.mm"
include "wfn.mm"
include "ctx.mm"
include "iitop.mm"
include "txunii.mm"
include "ffn.mm"
include "fnov.mm"
include "sylib.mm"
include "3eqtr4d.mm"

theorem cvmlift2lem7
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
  assert |- ( ph -> ( F o. K ) = G )

  proof
    wph
    vx
    vy
    cc0
    c1
    cicc
    co
    #
    @0
    vy
    cv
    #
    cF
    vf
    cv
    #
    ccom
    vz
    @0
    vx
    cv
    #
    vz
    cv
    #
    cG
    co
    #
    cmpt
    #
    wceq
    cc0
    @2
    cfv
    @3
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
    cF
    cfv
    #
    cmpt2
    vx
    vy
    @0
    @0
    @3
    @1
    cG
    co
    #
    cmpt2
    #
    cF
    cK
    ccom
    cG
    wph
    vx
    vy
    @0
    @0
    @11
    @12
    wph
    @3
    @0
    wcel
    #
    @1
    @0
    wcel
    #
    @11
    @12
    wceq
    wph
    @14
    @15
    wa
    wa
    #
    @1
    cF
    @9
    ccom
    #
    cfv
    #
    @1
    @6
    cfv
    #
    @11
    @12
    @16
    @1
    @17
    @6
    @16
    @9
    @8
    wcel
    #
    @17
    @6
    wceq
    #
    cc0
    @9
    cfv
    @7
    wceq
    #
    wph
    @14
    @20
    @21
    @22
    w3a
    @15
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
    @9
    @3
    cvmlift2.b
    cvmlift2.f
    cvmlift2.g
    cvmlift2.p
    cvmlift2.i
    cvmlift2.h
    @9
    eqid
    cvmlift2lem3
    adantrr
    #
    simp2d
    fveq1d
    @16
    @0
    cB
    @9
    wf
    #
    @15
    @18
    @11
    wceq
    @16
    @20
    @24
    @16
    @20
    @21
    @22
    @23
    simp1d
    @9
    cii
    cC
    @0
    cB
    iiuni
    cvmlift2.b
    cnf
    syl
    #
    wph
    @14
    @15
    simprr
    #
    @0
    cB
    @1
    cF
    @9
    fvco3
    syl2anc
    @16
    @15
    @19
    @12
    wceq
    @26
    vz
    @1
    @5
    @12
    @0
    @6
    @4
    @1
    @3
    cG
    oveq2
    @6
    eqid
    @3
    @1
    cG
    ovex
    fvmpt
    syl
    3eqtr3d
    3impb
    mpt2eq3dva
    wph
    vx
    vy
    vw
    @0
    @0
    cB
    @10
    vw
    cv
    #
    cF
    cfv
    @11
    cK
    cF
    @16
    @0
    cB
    @1
    @9
    @25
    @26
    ffvelrnd
    cK
    vx
    vy
    @0
    @0
    @10
    cmpt2
    wceq
    wph
    cvmlift2.k
    a1i
    wph
    vw
    cB
    cJ
    cuni
    #
    cF
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    cF
    cC
    cJ
    ccn
    co
    wcel
    cB
    @28
    cF
    wf
    cvmlift2.f
    cC
    cF
    cJ
    cvmcn
    cF
    cC
    cJ
    cB
    @28
    cvmlift2.b
    @28
    eqid
    #
    cnf
    3syl
    feqmptd
    @27
    @10
    cF
    fveq2
    fmpt2co
    wph
    cG
    @0
    @0
    cxp
    #
    wfn
    #
    cG
    @13
    wceq
    wph
    cG
    cii
    cii
    ctx
    co
    #
    cJ
    ccn
    co
    wcel
    @30
    @28
    cG
    wf
    @31
    cvmlift2.g
    cG
    @32
    cJ
    @30
    @28
    cii
    cii
    @0
    @0
    iitop
    iitop
    iiuni
    iiuni
    txunii
    @29
    cnf
    @30
    @28
    cG
    ffn
    3syl
    vx
    vy
    @0
    @0
    cG
    fnov
    sylib
    3eqtr4d
end
