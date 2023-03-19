include "ctsk.mm"
include "cuni.mm"
include "cvv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cpw.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "w3a.mm"
include "axgroth5.mm"
include "wb.mm"
include "vex.mm"
include "eltskg.mm"
include "ax-mp.mm"
include "anbi2i.mm"
include "3anass.mm"
include "bitr4i.mm"
include "exbii.mm"
include "mpbir.mm"
include "eluni.mm"
include "2th.mm"
include "eqriv.mm"

theorem grothtsk
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- U. Tarski = _V

  proof
    vw
    ctsk
    cuni
    #
    cvv
    vw
    cv
    #
    @0
    wcel
    #
    @1
    cvv
    wcel
    @2
    @1
    vx
    cv
    #
    wcel
    #
    @3
    ctsk
    wcel
    #
    wa
    #
    vx
    wex
    #
    @7
    @4
    vy
    cv
    #
    cpw
    #
    @3
    wss
    @9
    vz
    cv
    wss
    vz
    @3
    wrex
    wa
    vy
    @3
    wral
    #
    @8
    @3
    cen
    wbr
    @8
    @3
    wcel
    wo
    vy
    @3
    cpw
    wral
    #
    w3a
    #
    vx
    wex
    vw
    vx
    vy
    vz
    axgroth5
    @6
    @12
    vx
    @6
    @4
    @10
    @11
    wa
    #
    wa
    @12
    @5
    @13
    @4
    @3
    cvv
    wcel
    @5
    @13
    wb
    vx
    vex
    vy
    vz
    @3
    cvv
    eltskg
    ax-mp
    anbi2i
    @4
    @10
    @11
    3anass
    bitr4i
    exbii
    mpbir
    vx
    @1
    ctsk
    eluni
    mpbir
    vw
    vex
    2th
    eqriv
end
