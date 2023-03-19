include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cii.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnmptid.mm"
include "0elunit.mm"
include "cnmptc.mm"
include "cnmpt12f.mm"
include "wceq.mm"
include "oveq1.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "cvmliftiota.mm"

theorem cvmlift2lem2
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
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
  let cX: class X
  let cZ: class Z
  let cY: class Y
  assume cvmlift2.b: |- B = U. C
  assume cvmlift2.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift2.g: |- ( ph -> G e. ( ( II tX II ) Cn J ) )
  assume cvmlift2.p: |- ( ph -> P e. B )
  assume cvmlift2.i: |- ( ph -> ( F ` P ) = ( 0 G 0 ) )
  assume cvmlift2.h: |- H = ( iota_ f e. ( II Cn C ) ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( z G 0 ) ) /\ ( f ` 0 ) = P ) )

  disjoint f z
  disjoint F f
  disjoint F z
  disjoint f ph
  disjoint ph z
  disjoint J f
  disjoint J z
  disjoint G f
  disjoint G z
  disjoint H f
  disjoint H z
  disjoint C f
  disjoint C z
  disjoint P f
  disjoint P z
  disjoint B z
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
  disjoint H x
  disjoint H y
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
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
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
  assert |- ( ph -> ( H e. ( II Cn C ) /\ ( F o. H ) = ( z e. ( 0 [,] 1 ) |-> ( z G 0 ) ) /\ ( H ` 0 ) = P ) )

  proof
    wph
    cB
    cC
    cP
    vf
    cF
    vz
    cc0
    c1
    cicc
    co
    #
    vz
    cv
    #
    cc0
    cG
    co
    #
    cmpt
    #
    cH
    cJ
    cvmlift2.b
    cvmlift2.h
    cvmlift2.f
    wph
    vz
    @1
    cc0
    cG
    cii
    cii
    cii
    cJ
    @0
    cii
    @0
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    #
    wph
    vz
    cii
    @0
    @4
    cnmptid
    wph
    vz
    cc0
    cii
    cii
    @0
    @0
    @4
    @4
    cc0
    @0
    wcel
    #
    wph
    0elunit
    a1i
    cnmptc
    cvmlift2.g
    cnmpt12f
    cvmlift2.p
    wph
    cP
    cF
    cfv
    cc0
    cc0
    cG
    co
    #
    cc0
    @3
    cfv
    #
    cvmlift2.i
    @5
    @7
    @6
    wceq
    0elunit
    vz
    cc0
    @2
    @6
    @0
    @3
    @1
    cc0
    cc0
    cG
    oveq1
    @3
    eqid
    cc0
    cc0
    cG
    ovex
    fvmpt
    ax-mp
    syl6eqr
    cvmliftiota
end
