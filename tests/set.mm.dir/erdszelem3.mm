include "chash.mm"
include "cv.mm"
include "cima.mm"
include "clt.mm"
include "cres.mm"
include "wiso.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cpw.mm"
include "crab.mm"
include "cr.mm"
include "csup.mm"
include "wceq.mm"
include "oveq2.mm"
include "pweqd.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "rabeqbidv.mm"
include "imaeq2d.mm"
include "supeq1d.mm"
include "ltso.mm"
include "supex.mm"
include "fvmpt.mm"

theorem erdszelem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cK: class K
  let cN: class N
  let cO: class O
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let cI: class I
  let cJ: class J
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let cS: class S
  let cT: class T
  assume erdsze.n: |- ( ph -> N e. NN )
  assume erdsze.f: |- ( ph -> F : ( 1 ... N ) -1-1-> RR )
  assume erdszelem.k: |- K = ( x e. ( 1 ... N ) |-> sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y ) Isom < , O ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint A x
  disjoint A y
  disjoint O x
  disjoint O y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint F f
  disjoint m n
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n s
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint F w
  disjoint F z
  disjoint I n
  disjoint I s
  disjoint I x
  disjoint I y
  disjoint K f
  disjoint K s
  disjoint K z
  disjoint A f
  disjoint A s
  disjoint A w
  disjoint A z
  disjoint J n
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint O f
  disjoint O s
  disjoint O w
  disjoint O z
  disjoint R m
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint N a
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint N b
  disjoint N m
  disjoint N n
  disjoint N s
  disjoint N w
  disjoint N z
  disjoint a f
  disjoint a ph
  disjoint b f
  disjoint b ph
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph s
  disjoint ph w
  disjoint ph z
  disjoint S m
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T a
  disjoint T b
  disjoint T m
  disjoint T s
  disjoint T w
  disjoint T z
  assert |- ( A e. ( 1 ... N ) -> ( K ` A ) = sup ( ( # " { y e. ~P ( 1 ... A ) | ( ( F |` y ) Isom < , O ( y , ( F " y ) ) /\ A e. y ) } ) , RR , < ) )

  proof
    vx
    cA
    chash
    vy
    cv
    #
    cF
    @0
    cima
    clt
    cO
    cF
    @0
    cres
    wiso
    #
    vx
    cv
    #
    @0
    wcel
    #
    wa
    #
    vy
    c1
    @2
    cfz
    co
    #
    cpw
    #
    crab
    #
    cima
    #
    cr
    clt
    csup
    chash
    @1
    cA
    @0
    wcel
    #
    wa
    #
    vy
    c1
    cA
    cfz
    co
    #
    cpw
    #
    crab
    #
    cima
    #
    cr
    clt
    csup
    c1
    cN
    cfz
    co
    cK
    @2
    cA
    wceq
    #
    cr
    @8
    @14
    clt
    @15
    @7
    @13
    chash
    @15
    @4
    @10
    vy
    @6
    @12
    @15
    @5
    @11
    @2
    cA
    c1
    cfz
    oveq2
    pweqd
    @15
    @3
    @9
    @1
    @2
    cA
    @0
    eleq1
    anbi2d
    rabeqbidv
    imaeq2d
    supeq1d
    erdszelem.k
    cr
    @14
    clt
    ltso
    supex
    fvmpt
end
