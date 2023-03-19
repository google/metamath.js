include "cxp.mm"
include "c0.mm"
include "wceq.mm"
include "cuni.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "cop.mm"
include "wa.mm"
include "elxp3.mm"
include "wss.mm"
include "elssuni.mm"
include "vex.mm"
include "opnzi.mm"
include "ssn0.mm"
include "sylancl.mm"
include "adantl.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "exlimiv.mm"
include "necon4i.mm"
include "impbii.mm"

theorem unixp0
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A X. B ) = (/) <-> U. ( A X. B ) = (/) )

  proof
    cA
    cB
    cxp
    #
    c0
    wceq
    #
    @0
    cuni
    #
    c0
    wceq
    @1
    @2
    c0
    cuni
    c0
    @0
    c0
    unieq
    uni0
    syl6eq
    @0
    c0
    @2
    c0
    @0
    c0
    wne
    vz
    cv
    #
    @0
    wcel
    #
    vz
    wex
    @2
    c0
    wne
    #
    vz
    @0
    n0
    @4
    @5
    vz
    @4
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @3
    wceq
    #
    @8
    @0
    wcel
    #
    wa
    #
    vy
    wex
    vx
    wex
    @5
    vx
    vy
    @3
    cA
    cB
    elxp3
    @11
    @5
    vx
    vy
    @10
    @5
    @9
    @10
    @8
    @2
    wss
    @8
    c0
    wne
    @5
    @8
    @0
    elssuni
    @6
    @7
    vx
    vex
    vy
    vex
    opnzi
    @8
    @2
    ssn0
    sylancl
    adantl
    exlimivv
    sylbi
    exlimiv
    sylbi
    necon4i
    impbii
end
