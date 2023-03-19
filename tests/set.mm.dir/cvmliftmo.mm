include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "cfv.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "ccn.mm"
include "co.mm"
include "wral.mm"
include "wrmo.mm"
include "wcel.mm"
include "ccvm.mm"
include "ad2antrr.mm"
include "cconn.mm"
include "cnlly.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprll.mm"
include "simprrl.mm"
include "eqtr4d.mm"
include "simprlr.mm"
include "simprrr.mm"
include "cvmliftmoi.mm"
include "ex.mm"
include "ralrimivva.mm"
include "coeq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "anbi12d.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem cvmliftmo
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cO: class O
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  let cM: class M
  let cN: class N
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cR: class R
  let cT: class T
  let cW: class W
  assume cvmliftmo.b: |- B = U. C
  assume cvmliftmo.y: |- Y = U. K
  assume cvmliftmo.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmliftmo.k: |- ( ph -> K e. Conn )
  assume cvmliftmo.l: |- ( ph -> K e. N-Locally Conn )
  assume cvmliftmo.o: |- ( ph -> O e. Y )
  assume cvmliftmo.g: |- ( ph -> G e. ( K Cn J ) )
  assume cvmliftmo.p: |- ( ph -> P e. B )
  assume cvmliftmo.e: |- ( ph -> ( F ` P ) = ( G ` O ) )

  disjoint C f
  disjoint G f
  disjoint K f
  disjoint O f
  disjoint f ph
  disjoint F f
  disjoint P f
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a m
  disjoint a r
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint C a
  disjoint b f
  disjoint b g
  disjoint b k
  disjoint b m
  disjoint b r
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint C b
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f r
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g k
  disjoint g m
  disjoint g r
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint C g
  disjoint k m
  disjoint k r
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint C k
  disjoint m r
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint C m
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint C r
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint C s
  disjoint u v
  disjoint u w
  disjoint C u
  disjoint v w
  disjoint C v
  disjoint C w
  disjoint G g
  disjoint a t
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b t
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint k t
  disjoint k y
  disjoint k z
  disjoint J k
  disjoint m t
  disjoint m y
  disjoint m z
  disjoint J m
  disjoint r t
  disjoint r y
  disjoint r z
  disjoint J r
  disjoint s t
  disjoint s y
  disjoint s z
  disjoint J s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint B b
  disjoint B v
  disjoint B w
  disjoint a x
  disjoint K a
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g t
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint K g
  disjoint m x
  disjoint K m
  disjoint s x
  disjoint K s
  disjoint t x
  disjoint K t
  disjoint x y
  disjoint x z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M a
  disjoint b x
  disjoint M b
  disjoint k x
  disjoint M k
  disjoint M m
  disjoint r x
  disjoint M r
  disjoint M s
  disjoint M t
  disjoint u x
  disjoint M u
  disjoint v x
  disjoint M v
  disjoint w x
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N a
  disjoint N m
  disjoint N s
  disjoint N t
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint O g
  disjoint O x
  disjoint a ph
  disjoint g ph
  disjoint m ph
  disjoint ph s
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Q x
  disjoint F a
  disjoint F b
  disjoint F g
  disjoint F k
  disjoint F m
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint S a
  disjoint S b
  disjoint S m
  disjoint S s
  disjoint S t
  disjoint S y
  disjoint S z
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint P g
  disjoint R x
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint W u
  disjoint W v
  disjoint Y a
  disjoint Y m
  disjoint Y s
  disjoint Y t
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ph -> E* f e. ( K Cn C ) ( ( F o. f ) = G /\ ( f ` O ) = P ) )

  proof
    wph
    cF
    vf
    cv
    #
    ccom
    #
    cG
    wceq
    #
    cO
    @0
    cfv
    #
    cP
    wceq
    #
    wa
    #
    cF
    vg
    cv
    #
    ccom
    #
    cG
    wceq
    #
    cO
    @6
    cfv
    #
    cP
    wceq
    #
    wa
    #
    wa
    #
    vf
    vg
    weq
    #
    wi
    #
    vg
    cK
    cC
    ccn
    co
    #
    wral
    vf
    @15
    wral
    @5
    vf
    @15
    wrmo
    wph
    @14
    vf
    vg
    @15
    @15
    wph
    @0
    @15
    wcel
    #
    @6
    @15
    wcel
    #
    wa
    #
    wa
    #
    @12
    @13
    @19
    @12
    wa
    #
    cB
    cC
    cF
    cJ
    cK
    @0
    @6
    cO
    cY
    cvmliftmo.b
    cvmliftmo.y
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    @18
    @12
    cvmliftmo.f
    ad2antrr
    wph
    cK
    cconn
    wcel
    @18
    @12
    cvmliftmo.k
    ad2antrr
    wph
    cK
    cconn
    cnlly
    wcel
    @18
    @12
    cvmliftmo.l
    ad2antrr
    wph
    cO
    cY
    wcel
    @18
    @12
    cvmliftmo.o
    ad2antrr
    wph
    @16
    @17
    @12
    simplrl
    wph
    @16
    @17
    @12
    simplrr
    @20
    @1
    cG
    @7
    @19
    @2
    @4
    @11
    simprll
    @19
    @5
    @8
    @10
    simprrl
    eqtr4d
    @20
    @3
    cP
    @9
    @19
    @2
    @4
    @11
    simprlr
    @19
    @5
    @8
    @10
    simprrr
    eqtr4d
    cvmliftmoi
    ex
    ralrimivva
    @5
    @11
    vf
    vg
    @15
    @13
    @2
    @8
    @4
    @10
    @13
    @1
    @7
    cG
    @0
    @6
    cF
    coeq2
    eqeq1d
    @13
    @3
    @9
    cP
    cO
    @0
    @6
    fveq1
    eqeq1d
    anbi12d
    rmo4
    sylibr
end
