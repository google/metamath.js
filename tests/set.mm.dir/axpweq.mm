include "cpw.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "pwidg.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq2d.mm"
include "spcegv.mm"
include "mpd.mm"
include "elex.mm"
include "exlimiv.mm"
include "impbii.mm"
include "wss.mm"
include "vex.mm"
include "elpw2.mm"
include "pwss.mm"
include "dfss2.mm"
include "imbi1i.mm"
include "albii.mm"
include "bitri.mm"
include "exbii.mm"

theorem axpweq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume axpweq.1: |- A e. _V

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ~P A e. _V <-> E. x A. y ( A. z ( z e. y -> z e. A ) -> y e. x ) )

  proof
    cA
    cpw
    #
    cvv
    wcel
    #
    @0
    vx
    cv
    #
    cpw
    #
    wcel
    #
    vx
    wex
    #
    vz
    vy
    wel
    vz
    cv
    cA
    wcel
    wi
    vz
    wal
    #
    vy
    vx
    wel
    #
    wi
    #
    vy
    wal
    #
    vx
    wex
    @1
    @5
    @1
    @0
    @0
    cpw
    #
    wcel
    #
    @5
    @0
    cvv
    pwidg
    @4
    @11
    vx
    @0
    cvv
    @2
    @0
    wceq
    @3
    @10
    @0
    @2
    @0
    pweq
    eleq2d
    spcegv
    mpd
    @4
    @1
    vx
    @0
    @3
    elex
    exlimiv
    impbii
    @4
    @9
    vx
    @4
    @0
    @2
    wss
    #
    @9
    @0
    @2
    vx
    vex
    elpw2
    @12
    vy
    cv
    #
    cA
    wss
    #
    @7
    wi
    #
    vy
    wal
    @9
    vy
    cA
    @2
    pwss
    @15
    @8
    vy
    @14
    @6
    @7
    vz
    @13
    cA
    dfss2
    imbi1i
    albii
    bitri
    bitri
    exbii
    bitri
end
