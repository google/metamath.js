include "wa.mm"
include "cima.mm"
include "cfv.mm"
include "c1st.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cicc.mm"
include "wss.mm"
include "wral.mm"
include "adantr.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "syl6eqr.mm"
include "imaeq2d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "wfun.mm"
include "cdm.mm"
include "wi.mm"
include "cc0.mm"
include "wf.mm"
include "cii.mm"
include "ccn.mm"
include "iiuni.mm"
include "cnf.mm"
include "syl.mm"
include "ffun.mm"
include "cvmliftlem2.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funfvima2.mm"
include "syl2anc.mm"
include "mpd.mm"
include "sseldd.mm"

theorem cvmliftlem3
  let wph: wff ph
  let wps: wff ps
  let vv: setvar v
  let vu: setvar u
  let cA: class A
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
  let cW: class W
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
  assume cvmliftlem3.3: |- W = ( ( ( M - 1 ) / N ) [,] ( M / N ) )
  assume cvmliftlem3.m: |- ( ( ph /\ ps ) -> A e. W )

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
  disjoint W k
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
  disjoint W m
  disjoint W x
  disjoint W z
  assert |- ( ( ph /\ ps ) -> ( G ` A ) e. ( 1st ` ( T ` M ) ) )

  proof
    wph
    wps
    wa
    #
    cG
    cW
    cima
    #
    cM
    cT
    cfv
    #
    c1st
    cfv
    #
    cA
    cG
    cfv
    #
    @0
    cM
    c1
    cN
    cfz
    co
    #
    wcel
    cG
    vk
    cv
    #
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    @6
    cN
    cdiv
    co
    #
    cicc
    co
    #
    cima
    #
    @6
    cT
    cfv
    #
    c1st
    cfv
    #
    wss
    #
    vk
    @5
    wral
    #
    @1
    @3
    wss
    #
    cvmliftlem1.m
    wph
    @15
    wps
    cvmliftlem.a
    adantr
    @14
    @16
    vk
    cM
    @5
    @6
    cM
    wceq
    #
    @11
    @1
    @13
    @3
    @17
    @10
    cW
    cG
    @17
    @10
    cM
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    cM
    cN
    cdiv
    co
    #
    cicc
    co
    cW
    @17
    @8
    @19
    @9
    @20
    cicc
    @17
    @7
    @18
    cN
    cdiv
    @6
    cM
    c1
    cmin
    oveq1
    oveq1d
    @6
    cM
    cN
    cdiv
    oveq1
    oveq12d
    cvmliftlem3.3
    syl6eqr
    imaeq2d
    @17
    @12
    @2
    c1st
    @6
    cM
    cT
    fveq2
    fveq2d
    sseq12d
    rspcv
    sylc
    @0
    cA
    cW
    wcel
    #
    @4
    @1
    wcel
    #
    cvmliftlem3.m
    @0
    cG
    wfun
    #
    cW
    cG
    cdm
    #
    wss
    @21
    @22
    wi
    @0
    cc0
    c1
    cicc
    co
    #
    cX
    cG
    wf
    #
    @23
    wph
    @26
    wps
    wph
    cG
    cii
    cJ
    ccn
    co
    wcel
    @26
    cvmliftlem.g
    cG
    cii
    cJ
    @25
    cX
    iiuni
    cvmliftlem.x
    cnf
    syl
    adantr
    #
    @25
    cX
    cG
    ffun
    syl
    @0
    cW
    @25
    @24
    wph
    wps
    vv
    vu
    cB
    cC
    cP
    cS
    cT
    vj
    vk
    cF
    cG
    cJ
    cL
    cM
    cN
    cW
    cX
    vs
    cvmliftlem.1
    cvmliftlem.b
    cvmliftlem.x
    cvmliftlem.f
    cvmliftlem.g
    cvmliftlem.p
    cvmliftlem.e
    cvmliftlem.n
    cvmliftlem.t
    cvmliftlem.a
    cvmliftlem.l
    cvmliftlem1.m
    cvmliftlem3.3
    cvmliftlem2
    @0
    @26
    @24
    @25
    wceq
    @27
    @25
    cX
    cG
    fdm
    syl
    sseqtr4d
    cW
    cA
    cG
    funfvima2
    syl2anc
    mpd
    sseldd
end
