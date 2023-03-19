include "cv.mm"
include "ccom.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cmpt.mm"
include "wceq.mm"
include "cfv.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "crio.mm"
include "cmpt2.mm"
include "coeq2.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "a1i.mm"
include "eqeq12d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "cbvriotav.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "fveq2.mm"
include "riotabidv.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "cbvmpt2v.mm"
include "cvmlift2lem13.mm"

theorem cvmlift2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cJ: class J
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vn: setvar n
  let vr: setvar r
  let vt: setvar t
  let cA: class A
  let cM: class M
  let cS: class S
  let cT: class T
  let cU: class U
  let cV: class V
  let cW: class W
  let cH: class H
  let cX: class X
  let cZ: class Z
  let cY: class Y
  assume cvmlift2.b: |- B = U. C
  assume cvmlift2.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift2.g: |- ( ph -> G e. ( ( II tX II ) Cn J ) )
  assume cvmlift2.p: |- ( ph -> P e. B )
  assume cvmlift2.i: |- ( ph -> ( F ` P ) = ( 0 G 0 ) )

  disjoint F f
  disjoint f ph
  disjoint J f
  disjoint G f
  disjoint C f
  disjoint P f
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
  disjoint f x
  disjoint f y
  disjoint f z
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
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
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
  disjoint ph x
  disjoint ph y
  disjoint ph z
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
  disjoint J x
  disjoint J y
  disjoint J z
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
  disjoint G x
  disjoint G y
  disjoint G z
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
  disjoint H f
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
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
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
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
  assert |- ( ph -> E! f e. ( ( II tX II ) Cn C ) ( ( F o. f ) = G /\ ( 0 f 0 ) = P ) )

  proof
    wph
    vx
    vy
    vz
    cB
    cC
    cP
    vg
    vf
    cF
    cG
    cF
    vh
    cv
    #
    ccom
    #
    vw
    cc0
    c1
    cicc
    co
    #
    vw
    cv
    #
    cc0
    cG
    co
    #
    cmpt
    #
    wceq
    #
    cc0
    @0
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vh
    cii
    cC
    ccn
    co
    #
    crio
    #
    cJ
    vu
    vv
    @2
    @2
    vv
    cv
    #
    cF
    vk
    cv
    #
    ccom
    #
    vw
    @2
    vu
    cv
    #
    @3
    cG
    co
    #
    cmpt
    #
    wceq
    #
    cc0
    @13
    cfv
    #
    @15
    @11
    cfv
    #
    wceq
    #
    wa
    #
    vk
    @10
    crio
    #
    cfv
    #
    cmpt2
    cvmlift2.b
    cvmlift2.f
    cvmlift2.g
    cvmlift2.p
    cvmlift2.i
    @9
    cF
    vg
    cv
    #
    ccom
    #
    vz
    @2
    vz
    cv
    #
    cc0
    cG
    co
    #
    cmpt
    #
    wceq
    #
    cc0
    @25
    cfv
    #
    cP
    wceq
    #
    wa
    vh
    vg
    @10
    @0
    @25
    wceq
    #
    @6
    @30
    @8
    @32
    @33
    @1
    @26
    @5
    @29
    @0
    @25
    cF
    coeq2
    @5
    @29
    wceq
    @33
    vw
    vz
    @2
    @4
    @28
    @3
    @27
    cc0
    cG
    oveq1
    cbvmptv
    a1i
    eqeq12d
    @33
    @7
    @31
    cP
    cc0
    @0
    @25
    fveq1
    eqeq1d
    anbi12d
    cbvriotav
    vu
    vv
    vx
    vy
    @2
    @2
    @24
    vy
    cv
    #
    @26
    vz
    @2
    vx
    cv
    #
    @27
    cG
    co
    #
    cmpt
    #
    wceq
    #
    @31
    @35
    @11
    cfv
    #
    wceq
    #
    wa
    #
    vg
    @10
    crio
    #
    cfv
    @12
    @42
    cfv
    @15
    @35
    wceq
    #
    @12
    @23
    @42
    @43
    @23
    @26
    vz
    @2
    @15
    @27
    cG
    co
    #
    cmpt
    #
    wceq
    #
    @31
    @20
    wceq
    #
    wa
    #
    vg
    @10
    crio
    @42
    @22
    @48
    vk
    vg
    @10
    @13
    @25
    wceq
    #
    @18
    @46
    @21
    @47
    @49
    @14
    @26
    @17
    @45
    @13
    @25
    cF
    coeq2
    @17
    @45
    wceq
    @49
    vw
    vz
    @2
    @16
    @44
    @3
    @27
    @15
    cG
    oveq2
    cbvmptv
    a1i
    eqeq12d
    @49
    @19
    @31
    @20
    cc0
    @13
    @25
    fveq1
    eqeq1d
    anbi12d
    cbvriotav
    @43
    @48
    @41
    vg
    @10
    @43
    @46
    @38
    @47
    @40
    @43
    @45
    @37
    @26
    @43
    vz
    @2
    @44
    @36
    @15
    @35
    @27
    cG
    oveq1
    mpteq2dv
    eqeq2d
    @43
    @20
    @39
    @31
    @15
    @35
    @11
    fveq2
    eqeq2d
    anbi12d
    riotabidv
    syl5eq
    fveq1d
    @12
    @34
    @42
    fveq2
    cbvmpt2v
    cvmlift2lem13
end
