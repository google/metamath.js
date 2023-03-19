include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wex.mm"
include "wa.mm"
include "vex.mm"
include "eldm2.mm"
include "19.41v.mm"
include "opelres.mm"
include "exbii.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "bitr2i.mm"
include "ineqri.mm"
include "incom.mm"
include "eqtr3i.mm"

theorem dmres
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- dom ( A |` B ) = ( B i^i dom A )

  proof
    cA
    cdm
    #
    cB
    cin
    cA
    cB
    cres
    #
    cdm
    #
    cB
    @0
    cin
    vx
    @0
    cB
    @2
    vx
    cv
    #
    @2
    wcel
    @3
    vy
    cv
    #
    cop
    #
    @1
    wcel
    #
    vy
    wex
    #
    @3
    @0
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    #
    vy
    @3
    @1
    vx
    vex
    #
    eldm2
    @5
    cA
    wcel
    #
    @9
    wa
    #
    vy
    wex
    @12
    vy
    wex
    #
    @9
    wa
    @7
    @10
    @12
    @9
    vy
    19.41v
    @6
    @13
    vy
    @3
    @4
    cA
    cB
    vy
    vex
    opelres
    exbii
    @8
    @14
    @9
    vy
    @3
    cA
    @11
    eldm2
    anbi1i
    3bitr4i
    bitr2i
    ineqri
    @0
    cB
    incom
    eqtr3i
end
