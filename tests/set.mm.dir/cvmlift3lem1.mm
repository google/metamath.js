include "cc0.mm"
include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "cfv.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "crio.mm"
include "c1.mm"
include "cphtpc.mm"
include "wbr.mm"
include "eqid.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "cicc.mm"
include "wf.mm"
include "wcel.mm"
include "iiuni.mm"
include "cnf.mm"
include "syl.mm"
include "0elunit.mm"
include "fvco3.mm"
include "sylancl.mm"
include "sconnpht2.mm"
include "phtpcco2.mm"
include "cvmliftpht.mm"
include "phtpc01.mm"
include "simprd.mm"

theorem cvmlift3lem1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cY: class Y
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vk: setvar k
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cI: class I
  let va: setvar a
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let vn: setvar n
  let vm: setvar m
  let vt: setvar t
  let cH: class H
  let cQ: class Q
  let cS: class S
  let cR: class R
  let cX: class X
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
  assume cvmlift3lem1.1: |- ( ph -> M e. ( II Cn K ) )
  assume cvmlift3lem1.2: |- ( ph -> ( M ` 0 ) = O )
  assume cvmlift3lem1.3: |- ( ph -> N e. ( II Cn K ) )
  assume cvmlift3lem1.4: |- ( ph -> ( N ` 0 ) = O )
  assume cvmlift3lem1.5: |- ( ph -> ( M ` 1 ) = ( N ` 1 ) )

  disjoint J g
  disjoint F g
  disjoint M g
  disjoint N g
  disjoint B g
  disjoint G g
  disjoint C g
  disjoint K g
  disjoint P g
  disjoint O g
  disjoint Y g
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
  disjoint f z
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
  disjoint f g
  disjoint I f
  disjoint g w
  disjoint g z
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
  disjoint J f
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
  disjoint F f
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
  disjoint F z
  disjoint M f
  disjoint M h
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint N f
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
  disjoint B f
  disjoint B h
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R g
  disjoint R w
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G d
  disjoint G f
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
  disjoint G z
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
  disjoint C f
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
  disjoint C z
  disjoint a ph
  disjoint f ph
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
  disjoint K f
  disjoint K h
  disjoint K m
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P f
  disjoint P h
  disjoint P n
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P z
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint O f
  disjoint O h
  disjoint O n
  disjoint O u
  disjoint O v
  disjoint O w
  disjoint O x
  disjoint O z
  disjoint Y a
  disjoint Y f
  disjoint Y h
  disjoint Y m
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint W c
  disjoint W d
  disjoint W f
  disjoint W h
  disjoint W n
  disjoint W x
  disjoint W y
  assert |- ( ph -> ( ( iota_ g e. ( II Cn C ) ( ( F o. g ) = ( G o. M ) /\ ( g ` 0 ) = P ) ) ` 1 ) = ( ( iota_ g e. ( II Cn C ) ( ( F o. g ) = ( G o. N ) /\ ( g ` 0 ) = P ) ) ` 1 ) )

  proof
    wph
    cc0
    cF
    vg
    cv
    #
    ccom
    #
    cG
    cM
    ccom
    #
    wceq
    cc0
    @0
    cfv
    cP
    wceq
    #
    wa
    vg
    cii
    cC
    ccn
    co
    #
    crio
    #
    cfv
    cc0
    @1
    cG
    cN
    ccom
    #
    wceq
    @3
    wa
    vg
    @4
    crio
    #
    cfv
    wceq
    #
    c1
    @5
    cfv
    c1
    @7
    cfv
    wceq
    #
    wph
    @5
    @7
    cC
    cphtpc
    cfv
    wbr
    @8
    @9
    wa
    wph
    cB
    cC
    cP
    vg
    cF
    @2
    @6
    cJ
    @5
    @7
    cvmlift3.b
    @5
    eqid
    @7
    eqid
    cvmlift3.f
    cvmlift3.p
    wph
    cP
    cF
    cfv
    #
    cc0
    cM
    cfv
    #
    cG
    cfv
    #
    cc0
    @2
    cfv
    #
    wph
    @10
    cO
    cG
    cfv
    @12
    cvmlift3.e
    wph
    @11
    cO
    cG
    cvmlift3lem1.2
    fveq2d
    eqtr4d
    wph
    cc0
    c1
    cicc
    co
    #
    cY
    cM
    wf
    #
    cc0
    @14
    wcel
    @13
    @12
    wceq
    wph
    cM
    cii
    cK
    ccn
    co
    wcel
    @15
    cvmlift3lem1.1
    cM
    cii
    cK
    @14
    cY
    iiuni
    cvmlift3.y
    cnf
    syl
    0elunit
    @14
    cY
    cc0
    cG
    cM
    fvco3
    sylancl
    eqtr4d
    wph
    cG
    cM
    cN
    cK
    cJ
    wph
    cM
    cN
    cK
    cvmlift3.k
    cvmlift3lem1.1
    cvmlift3lem1.3
    wph
    @11
    cO
    cc0
    cN
    cfv
    cvmlift3lem1.2
    cvmlift3lem1.4
    eqtr4d
    cvmlift3lem1.5
    sconnpht2
    cvmlift3.g
    phtpcco2
    cvmliftpht
    @5
    @7
    cC
    phtpc01
    syl
    simprd
end
