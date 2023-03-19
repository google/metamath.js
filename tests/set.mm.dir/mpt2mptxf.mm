include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cmpt.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cmpt2.mm"
include "df-mpt.mm"
include "coprab.mm"
include "df-mpt2.mm"
include "cop.mm"
include "wex.mm"
include "eliunxp.mm"
include "anbi1i.mm"
include "nfeq2.mm"
include "19.41.mm"
include "exbii.mm"
include "bitri.mm"
include "anass.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "pm5.32i.mm"
include "2exbii.mm"
include "3bitr2i.mm"
include "opabbii.mm"
include "dfoprab2.mm"
include "eqtr4i.mm"

theorem mpt2mptxf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  assume mpt2mptxf.0: |- F/_ x C
  assume mpt2mptxf.1: |- F/_ y C
  assume mpt2mptxf.2: |- ( z = <. x , y >. -> C = D )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint D z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint D w
  assert |- ( z e. U_ x e. A ( { x } X. B ) |-> C ) = ( x e. A , y e. B |-> D )

  proof
    vz
    vx
    cA
    vx
    cv
    #
    csn
    cB
    cxp
    ciun
    #
    cC
    cmpt
    vz
    cv
    #
    @1
    wcel
    #
    vw
    cv
    #
    cC
    wceq
    #
    wa
    #
    vz
    vw
    copab
    #
    vx
    vy
    cA
    cB
    cD
    cmpt2
    #
    vz
    vw
    @1
    cC
    df-mpt
    @8
    @0
    cA
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    #
    @4
    cD
    wceq
    #
    wa
    #
    vx
    vy
    vw
    coprab
    #
    @7
    vx
    vy
    vw
    cA
    cB
    cD
    df-mpt2
    @7
    @2
    @0
    @9
    cop
    wceq
    #
    @12
    wa
    #
    vy
    wex
    vx
    wex
    #
    vz
    vw
    copab
    @13
    @6
    @16
    vz
    vw
    @6
    @14
    @10
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    @5
    wa
    #
    @17
    @5
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    @16
    @3
    @19
    @5
    vx
    vy
    cA
    cB
    @2
    eliunxp
    anbi1i
    @23
    @18
    @5
    wa
    #
    vx
    wex
    @20
    @22
    @24
    vx
    @17
    @5
    vy
    vy
    @4
    cC
    mpt2mptxf.1
    nfeq2
    19.41
    exbii
    @18
    @5
    vx
    vx
    @4
    cC
    mpt2mptxf.0
    nfeq2
    19.41
    bitri
    @21
    @15
    vx
    vy
    @21
    @14
    @10
    @5
    wa
    #
    wa
    @15
    @14
    @10
    @5
    anass
    @14
    @25
    @12
    @14
    @5
    @11
    @10
    @14
    cC
    cD
    @4
    mpt2mptxf.2
    eqeq2d
    anbi2d
    pm5.32i
    bitri
    2exbii
    3bitr2i
    opabbii
    @12
    vx
    vy
    vw
    vz
    dfoprab2
    eqtr4i
    eqtr4i
    eqtr4i
end
