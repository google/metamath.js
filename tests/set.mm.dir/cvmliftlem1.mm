include "wa.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wcel.mm"
include "wrel.mm"
include "wceq.mm"
include "wral.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "fveq2.mm"
include "opeliunxp2.mm"
include "simprbi.mm"
include "syl.mm"

theorem cvmliftlem1
  let wph: wff ph
  let wps: wff ps
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cT: class T
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cJ: class J
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vb: setvar b
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let cK: class K
  let cQ: class Q
  let cW: class W
  assume cvmliftlem.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmliftlem.b: |- B = U. C
  assume cvmliftlem.x: |- X = U. J
  assume cvmliftlem.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmliftlem.g: |- ( ph -> G e. ( II Cn J ) )
  assume cvmliftlem.p: |- ( ph -> P e. B )
  assume cvmliftlem.e: |- ( ph -> ( F ` P ) = ( G ` 0 ) )
  assume cvmliftlem.n: |- ( ph -> N e. NN )
  assume cvmliftlem.t: |- ( ph -> T : ( 1 ... N ) --> U_ j e. J ( { j } X. ( S ` j ) ) )
  assume cvmliftlem.a: |- ( ph -> A. k e. ( 1 ... N ) ( G " ( ( ( k - 1 ) / N ) [,] ( k / N ) ) ) C_ ( 1st ` ( T ` k ) ) )
  assume cvmliftlem.l: |- L = ( topGen ` ran (,) )
  assume cvmliftlem1.m: |- ( ( ph /\ ps ) -> M e. ( 1 ... N ) )

  disjoint B v
  disjoint j k
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint F j
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint F k
  disjoint s u
  disjoint s v
  disjoint F s
  disjoint u v
  disjoint F u
  disjoint F v
  disjoint M j
  disjoint M k
  disjoint M s
  disjoint M u
  disjoint M v
  disjoint P k
  disjoint P u
  disjoint P v
  disjoint C j
  disjoint C k
  disjoint C s
  disjoint C u
  disjoint C v
  disjoint j ph
  disjoint ph s
  disjoint N k
  disjoint N u
  disjoint N v
  disjoint S j
  disjoint S k
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint X j
  disjoint G j
  disjoint G k
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint T j
  disjoint T k
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint J j
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint b v
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint v y
  disjoint v z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b w
  disjoint b x
  disjoint F b
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j m
  disjoint j n
  disjoint j t
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint L n
  disjoint L y
  disjoint L z
  disjoint K f
  disjoint K y
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint M m
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint P b
  disjoint P f
  disjoint P g
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint P z
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C f
  disjoint C g
  disjoint C n
  disjoint C y
  disjoint C z
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ps z
  disjoint N b
  disjoint N c
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint S a
  disjoint S b
  disjoint S f
  disjoint S g
  disjoint S n
  disjoint S x
  disjoint S z
  disjoint X a
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G g
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T m
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint J a
  disjoint J b
  disjoint J c
  disjoint J f
  disjoint J g
  disjoint J n
  disjoint J x
  disjoint J z
  disjoint Q b
  disjoint Q c
  disjoint Q k
  disjoint Q m
  disjoint Q n
  disjoint Q u
  disjoint Q v
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint W k
  disjoint W m
  disjoint W x
  disjoint W z
  assert |- ( ( ph /\ ps ) -> ( 2nd ` ( T ` M ) ) e. ( S ` ( 1st ` ( T ` M ) ) ) )

  proof
    wph
    wps
    wa
    #
    cM
    cT
    cfv
    #
    c1st
    cfv
    #
    @1
    c2nd
    cfv
    #
    cop
    #
    vj
    cJ
    vj
    cv
    #
    csn
    #
    @5
    cS
    cfv
    #
    cxp
    #
    ciun
    #
    wcel
    #
    @3
    @2
    cS
    cfv
    #
    wcel
    #
    @0
    @1
    @4
    @9
    @0
    @9
    wrel
    #
    @1
    @9
    wcel
    @1
    @4
    wceq
    @13
    @8
    wrel
    #
    vj
    cJ
    wral
    @14
    vj
    cJ
    @6
    @7
    relxp
    rgenw
    vj
    cJ
    @8
    reliun
    mpbir
    @0
    c1
    cN
    cfz
    co
    #
    @9
    cM
    cT
    wph
    @15
    @9
    cT
    wf
    wps
    cvmliftlem.t
    adantr
    cvmliftlem1.m
    ffvelrnd
    #
    @1
    @9
    1st2nd
    sylancr
    @16
    eqeltrrd
    @10
    @2
    cJ
    wcel
    @12
    vj
    cJ
    @7
    @2
    @3
    @11
    @5
    @2
    cS
    fveq2
    opeliunxp2
    simprbi
    syl
end
