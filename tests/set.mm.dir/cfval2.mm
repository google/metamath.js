include "con0.mm"
include "wcel.mm"
include "ccf.mm"
include "cfv.mm"
include "cv.mm"
include "ccrd.mm"
include "wceq.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "cpw.mm"
include "crab.mm"
include "ciin.mm"
include "cfval.mm"
include "fvex.mm"
include "dfiin2.mm"
include "df-rex.mm"
include "rabid.mm"
include "selpw.mm"
include "anbi1i.mm"
include "bitri.mm"
include "anbi2ci.mm"
include "exbii.mm"
include "abbii.mm"
include "inteqi.mm"
include "eqtr2i.mm"
include "syl6eq.mm"

theorem cfval2
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vy: setvar y

  disjoint A w
  disjoint A x
  disjoint A z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint A y
  disjoint w y
  disjoint x y
  disjoint y z
  assert |- ( A e. On -> ( cf ` A ) = |^|_ x e. { x e. ~P A | A. z e. A E. w e. x z C_ w } ( card ` x ) )

  proof
    cA
    con0
    wcel
    cA
    ccf
    cfv
    vy
    cv
    vx
    cv
    #
    ccrd
    cfv
    #
    wceq
    #
    @0
    cA
    wss
    #
    vz
    cv
    vw
    cv
    wss
    vw
    @0
    wrex
    vz
    cA
    wral
    #
    wa
    #
    wa
    #
    vx
    wex
    #
    vy
    cab
    #
    cint
    #
    vx
    @4
    vx
    cA
    cpw
    #
    crab
    #
    @1
    ciin
    #
    vy
    vx
    vz
    vw
    cA
    cfval
    @12
    @2
    vx
    @11
    wrex
    #
    vy
    cab
    #
    cint
    @9
    vx
    vy
    @11
    @1
    @0
    ccrd
    fvex
    dfiin2
    @14
    @8
    @13
    @7
    vy
    @13
    @0
    @11
    wcel
    #
    @2
    wa
    #
    vx
    wex
    @7
    @2
    vx
    @11
    df-rex
    @16
    @6
    vx
    @15
    @5
    @2
    @15
    @0
    @10
    wcel
    #
    @4
    wa
    @5
    @4
    vx
    @10
    rabid
    @17
    @3
    @4
    vx
    cA
    selpw
    anbi1i
    bitri
    anbi2ci
    exbii
    bitri
    abbii
    inteqi
    eqtr2i
    syl6eq
end
