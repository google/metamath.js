include "wlim.mm"
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
include "cuni.mm"
include "cpw.mm"
include "crab.mm"
include "ciin.mm"
include "con0.mm"
include "wcel.mm"
include "word.mm"
include "limord.mm"
include "elon.mm"
include "sylibr.mm"
include "cfval.mm"
include "syl.mm"
include "fvex.mm"
include "dfiin2.mm"
include "df-rex.mm"
include "ancom.mm"
include "rabid.mm"
include "selpw.mm"
include "anbi1i.mm"
include "coflim.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "abbidv.mm"
include "inteqd.mm"
include "syl5req.mm"
include "eqtrd.mm"

theorem cflim3
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume cflim3.1: |- A e. _V

  disjoint A x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( Lim A -> ( cf ` A ) = |^|_ x e. { x e. ~P A | U. x = A } ( card ` x ) )

  proof
    cA
    wlim
    #
    cA
    ccf
    cfv
    #
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
    @2
    cA
    wss
    #
    vz
    cv
    vw
    cv
    wss
    vw
    @2
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
    @2
    cuni
    cA
    wceq
    #
    vx
    cA
    cpw
    #
    crab
    #
    @3
    ciin
    #
    @0
    cA
    con0
    wcel
    #
    @1
    @11
    wceq
    @0
    cA
    word
    @16
    cA
    limord
    cA
    cflim3.1
    elon
    sylibr
    vy
    vx
    vz
    vw
    cA
    cfval
    syl
    @0
    @15
    @4
    vx
    @14
    wrex
    #
    vy
    cab
    #
    cint
    @11
    vx
    vy
    @14
    @3
    @2
    ccrd
    fvex
    dfiin2
    @0
    @18
    @10
    @0
    @17
    @9
    vy
    @17
    @2
    @14
    wcel
    #
    @4
    wa
    #
    vx
    wex
    @0
    @9
    @4
    vx
    @14
    df-rex
    @0
    @20
    @8
    vx
    @20
    @4
    @19
    wa
    @0
    @8
    @19
    @4
    ancom
    @0
    @19
    @7
    @4
    @19
    @2
    @13
    wcel
    #
    @12
    wa
    #
    @0
    @7
    @12
    vx
    @13
    rabid
    @22
    @5
    @12
    wa
    @0
    @7
    @21
    @5
    @12
    vx
    cA
    selpw
    anbi1i
    @0
    @5
    @12
    @6
    vz
    vw
    cA
    @2
    coflim
    pm5.32da
    syl5bb
    syl5bb
    anbi2d
    syl5bb
    exbidv
    syl5bb
    abbidv
    inteqd
    syl5req
    eqtrd
end
