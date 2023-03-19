include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "chil.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "csp.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cio.mm"
include "wf.mm"
include "w3a.mm"
include "crio.mm"
include "dmadjop.mm"
include "biantrurd.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "3anass.mm"
include "3bitr4g.mm"
include "iotabidv.mm"
include "df-riota.mm"
include "a1i.mm"
include "dfadj2.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "3anbi13d.mm"
include "fvopab5.mm"
include "3eqtr4rd.mm"

theorem adjval
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cT: class T
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z

  disjoint u x
  disjoint u y
  disjoint T u
  disjoint x y
  disjoint T x
  disjoint T y
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint T t
  disjoint u w
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- ( T e. dom adjh -> ( adjh ` T ) = ( iota_ u e. ( ~H ^m ~H ) A. x e. ~H A. y e. ~H ( x .ih ( T ` y ) ) = ( ( u ` x ) .ih y ) ) )

  proof
    cT
    cado
    cdm
    #
    wcel
    #
    vu
    cv
    #
    chil
    chil
    cmap
    co
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    #
    csp
    co
    #
    @5
    @2
    cfv
    @6
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    wa
    #
    vu
    cio
    #
    chil
    chil
    cT
    wf
    #
    chil
    chil
    @2
    wf
    #
    @11
    w3a
    #
    vu
    cio
    @11
    vu
    @3
    crio
    #
    cT
    cado
    cfv
    @1
    @12
    @16
    vu
    @1
    @15
    @11
    wa
    #
    @14
    @18
    wa
    @12
    @16
    @1
    @14
    @18
    cT
    dmadjop
    biantrurd
    @4
    @15
    @11
    chil
    chil
    @2
    ax-hilex
    ax-hilex
    elmap
    anbi1i
    @14
    @15
    @11
    3anass
    3bitr4g
    iotabidv
    @17
    @13
    wceq
    @1
    @11
    vu
    @3
    df-riota
    a1i
    chil
    chil
    vt
    cv
    #
    wf
    #
    @15
    @5
    @6
    @19
    cfv
    #
    csp
    co
    #
    @9
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    @16
    vt
    vu
    cT
    cado
    @0
    vx
    vy
    vu
    vt
    dfadj2
    @19
    cT
    wceq
    #
    @20
    @14
    @24
    @11
    @15
    chil
    chil
    @19
    cT
    feq1
    @25
    @23
    @10
    vx
    vy
    chil
    chil
    @25
    @22
    @8
    @9
    @25
    @21
    @7
    @5
    csp
    @6
    @19
    cT
    fveq1
    oveq2d
    eqeq1d
    2ralbidv
    3anbi13d
    fvopab5
    3eqtr4rd
end
