include "c0.mm"
include "wne.mm"
include "cin.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wceq.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "crab.mm"
include "scott0.mm"
include "eqeq1i.mm"
include "bitr4i.mm"
include "necon3bii.mm"
include "n0.mm"
include "bitri.mm"
include "wa.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "a1i.mm"
include "ciun.mm"
include "ssiun2.mm"
include "syl6sseqr.mm"
include "sseld.mm"
include "jcad.mm"
include "inelcm.mm"
include "syl6.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "rgen.mm"

theorem cplem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  assume cplem1.1: |- C = { y e. B | A. z e. B ( rank ` y ) C_ ( rank ` z ) }
  assume cplem1.2: |- D = U_ x e. A C

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint D w
  assert |- A. x e. A ( B =/= (/) -> ( B i^i D ) =/= (/) )

  proof
    cB
    c0
    wne
    #
    cB
    cD
    cin
    c0
    wne
    #
    wi
    vx
    cA
    @0
    vw
    cv
    #
    cC
    wcel
    #
    vw
    wex
    #
    vx
    cv
    cA
    wcel
    #
    @1
    @0
    cC
    c0
    wne
    @4
    cB
    c0
    cC
    c0
    cB
    c0
    wceq
    vy
    cv
    crnk
    cfv
    vz
    cv
    crnk
    cfv
    wss
    vz
    cB
    wral
    #
    vy
    cB
    crab
    #
    c0
    wceq
    cC
    c0
    wceq
    vy
    vz
    cB
    scott0
    cC
    @7
    c0
    cplem1.1
    eqeq1i
    bitr4i
    necon3bii
    vw
    cC
    n0
    bitri
    @5
    @3
    @1
    vw
    @5
    @3
    @2
    cB
    wcel
    #
    @2
    cD
    wcel
    #
    wa
    @1
    @5
    @3
    @8
    @9
    @3
    @8
    wi
    @5
    cC
    cB
    @2
    cC
    @7
    cB
    cplem1.1
    @6
    vy
    cB
    ssrab2
    eqsstri
    sseli
    a1i
    @5
    cC
    cD
    @2
    @5
    cC
    vx
    cA
    cC
    ciun
    cD
    vx
    cA
    cC
    ssiun2
    cplem1.2
    syl6sseqr
    sseld
    jcad
    @2
    cB
    cD
    inelcm
    syl6
    exlimdv
    syl5bi
    rgen
end
