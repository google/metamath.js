include "cv.mm"
include "c0.mm"
include "csn.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "wss.mm"
include "cuni.mm"
include "velsn.mm"
include "ralbii.mm"
include "dfss3.mm"
include "wn.mm"
include "wex.mm"
include "wrex.mm"
include "neq0.mm"
include "rexcom4.mm"
include "rexbii.mm"
include "eluni2.mm"
include "exbii.mm"
include "3bitr4ri.mm"
include "rexnal.mm"
include "3bitri.mm"
include "con4bii.mm"

theorem uni0b
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( U. A = (/) <-> A C_ { (/) } )

  proof
    vx
    cv
    #
    c0
    csn
    #
    wcel
    #
    vx
    cA
    wral
    @0
    c0
    wceq
    #
    vx
    cA
    wral
    #
    cA
    @1
    wss
    cA
    cuni
    #
    c0
    wceq
    #
    @2
    @3
    vx
    cA
    vx
    c0
    velsn
    ralbii
    vx
    cA
    @1
    dfss3
    @6
    @4
    @6
    wn
    vy
    cv
    #
    @5
    wcel
    #
    vy
    wex
    #
    @3
    wn
    #
    vx
    cA
    wrex
    #
    @4
    wn
    vy
    @5
    neq0
    @7
    @0
    wcel
    #
    vy
    wex
    #
    vx
    cA
    wrex
    @12
    vx
    cA
    wrex
    #
    vy
    wex
    @11
    @9
    @12
    vx
    vy
    cA
    rexcom4
    @10
    @13
    vx
    cA
    vy
    @0
    neq0
    rexbii
    @8
    @14
    vy
    vx
    @7
    cA
    eluni2
    exbii
    3bitr4ri
    @3
    vx
    cA
    rexnal
    3bitri
    con4bii
    3bitr4ri
end
