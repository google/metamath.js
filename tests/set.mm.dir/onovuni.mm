include "wcel.mm"
include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cuni.mm"
include "cvv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cfv.mm"
include "ciun.mm"
include "wlim.mm"
include "wceq.mm"
include "vex.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "3eqtr4g.mm"
include "3sstr4g.mm"
include "onfununi.mm"
include "uniexg.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "3eqtr3d.mm"

theorem onovuni
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cT: class T
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  let cK: class K
  let cL: class L
  assume onovuni.1: |- ( Lim y -> ( A F y ) = U_ x e. y ( A F x ) )
  assume onovuni.2: |- ( ( x e. On /\ y e. On /\ x C_ y ) -> ( A F x ) C_ ( A F y ) )

  disjoint T x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint S x
  disjoint S y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F w
  disjoint F z
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint S w
  disjoint S z
  disjoint T w
  assert |- ( ( S e. T /\ S C_ On /\ S =/= (/) ) -> ( A F U. S ) = U_ x e. S ( A F x ) )

  proof
    cS
    cT
    wcel
    #
    cS
    con0
    wss
    #
    cS
    c0
    wne
    #
    w3a
    #
    cS
    cuni
    #
    vz
    cvv
    cA
    vz
    cv
    #
    cF
    co
    #
    cmpt
    #
    cfv
    #
    vx
    cS
    vx
    cv
    #
    @7
    cfv
    #
    ciun
    #
    cA
    @4
    cF
    co
    #
    vx
    cS
    cA
    @9
    cF
    co
    #
    ciun
    #
    vx
    vy
    cS
    cT
    @7
    vy
    cv
    #
    wlim
    cA
    @15
    cF
    co
    #
    vx
    @15
    @13
    ciun
    @15
    @7
    cfv
    #
    vx
    @15
    @10
    ciun
    onovuni.1
    @15
    cvv
    wcel
    @17
    @16
    wceq
    vy
    vex
    vz
    @15
    @6
    @16
    cvv
    @7
    @5
    @15
    cA
    cF
    oveq2
    @7
    eqid
    #
    cA
    @15
    cF
    ovex
    fvmpt
    ax-mp
    #
    vx
    @15
    @10
    @13
    @10
    @13
    wceq
    #
    @9
    @15
    wcel
    @9
    cvv
    wcel
    @20
    vx
    vex
    vz
    @9
    @6
    @13
    cvv
    @7
    @5
    @9
    cA
    cF
    oveq2
    @18
    cA
    @9
    cF
    ovex
    fvmpt
    ax-mp
    #
    a1i
    iuneq2i
    3eqtr4g
    @9
    con0
    wcel
    @15
    con0
    wcel
    @9
    @15
    wss
    w3a
    @13
    @16
    @10
    @17
    onovuni.2
    @21
    @19
    3sstr4g
    onfununi
    @0
    @1
    @8
    @12
    wceq
    #
    @2
    @0
    @4
    cvv
    wcel
    @22
    cS
    cT
    uniexg
    vz
    @4
    @6
    @12
    cvv
    @7
    @5
    @4
    cA
    cF
    oveq2
    @18
    cA
    @4
    cF
    ovex
    fvmpt
    syl
    3ad2ant1
    @11
    @14
    wceq
    @3
    vx
    cS
    @10
    @13
    @20
    @9
    cS
    wcel
    @21
    a1i
    iuneq2i
    a1i
    3eqtr3d
end
