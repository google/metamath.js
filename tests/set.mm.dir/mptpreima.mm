include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "crab.mm"
include "cmpt.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "cnveqi.mm"
include "cnvopab.mm"
include "imaeq1i.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "resopab.mm"
include "rneqi.mm"
include "wex.mm"
include "cab.mm"
include "ancom.mm"
include "anass.mm"
include "bitri.mm"
include "exbii.mm"
include "19.42v.mm"
include "df-clel.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "abbii.mm"
include "rnopab.mm"
include "df-rab.mm"
include "3eqtr4i.mm"

theorem mptpreima
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  let cV: class V
  assume dmmpt.1: |- F = ( x e. A |-> B )

  disjoint C x
  disjoint x y
  disjoint C y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint V x
  assert |- ( `' F " C ) = { x e. A | B e. C }

  proof
    cF
    ccnv
    #
    cC
    cima
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wceq
    #
    wa
    #
    vy
    vx
    copab
    #
    cC
    cima
    #
    cB
    cC
    wcel
    #
    vx
    cA
    crab
    #
    @0
    @5
    cC
    @0
    @4
    vx
    vy
    copab
    #
    ccnv
    @5
    cF
    @9
    cF
    vx
    cA
    cB
    cmpt
    @9
    dmmpt.1
    vx
    vy
    cA
    cB
    df-mpt
    eqtri
    cnveqi
    @4
    vx
    vy
    cnvopab
    eqtri
    imaeq1i
    @6
    @5
    cC
    cres
    #
    crn
    #
    @8
    @5
    cC
    df-ima
    @11
    @2
    cC
    wcel
    #
    @4
    wa
    #
    vy
    vx
    copab
    #
    crn
    #
    @8
    @10
    @14
    @4
    vy
    vx
    cC
    resopab
    rneqi
    @13
    vy
    wex
    #
    vx
    cab
    @1
    @7
    wa
    #
    vx
    cab
    @15
    @8
    @16
    @17
    vx
    @16
    @1
    @3
    @12
    wa
    #
    wa
    #
    vy
    wex
    #
    @17
    @13
    @19
    vy
    @13
    @4
    @12
    wa
    @19
    @12
    @4
    ancom
    @1
    @3
    @12
    anass
    bitri
    exbii
    @20
    @1
    @18
    vy
    wex
    #
    wa
    @17
    @1
    @18
    vy
    19.42v
    @21
    @7
    @1
    @7
    @21
    vy
    cB
    cC
    df-clel
    bicomi
    anbi2i
    bitri
    bitri
    abbii
    @13
    vy
    vx
    rnopab
    @7
    vx
    cA
    df-rab
    3eqtr4i
    eqtri
    eqtri
    eqtri
end
