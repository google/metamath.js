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
include "eliunxp2.mm"
include "anbi1i.mm"
include "19.41vv.mm"
include "anass.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "2exbii.mm"
include "3bitr2i.mm"
include "opabbii.mm"
include "dfoprab2.mm"
include "eqtr4i.mm"

theorem mpt2mptx2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vk: setvar k
  assume mpt2mptx2.1: |- ( z = <. x , y >. -> C = D )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint D z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint D w
  disjoint k x
  assert |- ( z e. U_ y e. B ( A X. { y } ) |-> C ) = ( x e. A , y e. B |-> D )

  proof
    vz
    vy
    cB
    cA
    vy
    cv
    #
    csn
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
    vx
    cv
    #
    cA
    wcel
    @0
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
    @9
    @0
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
    vx
    wex
    #
    @5
    wa
    @17
    @5
    wa
    #
    vy
    wex
    vx
    wex
    @16
    @3
    @18
    @5
    vx
    vy
    cA
    cB
    @2
    eliunxp2
    anbi1i
    @17
    @5
    vx
    vy
    19.41vv
    @19
    @15
    vx
    vy
    @19
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
    @20
    @12
    @14
    @5
    @11
    @10
    @14
    cC
    cD
    @4
    mpt2mptx2.1
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
