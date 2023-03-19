include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "inf1.mm"
include "wcel.mm"
include "dfss2.mm"
include "eluni.mm"
include "imbi2i.mm"
include "albii.mm"
include "bitri.mm"
include "anbi2i.mm"
include "exbii.mm"
include "mpbir.mm"

theorem inf2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume inf1.1: |- E. x ( y e. x /\ A. y ( y e. x -> E. z ( y e. z /\ z e. x ) ) )

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- E. x ( x =/= (/) /\ x C_ U. x )

  proof
    vx
    cv
    #
    c0
    wne
    #
    @0
    @0
    cuni
    #
    wss
    #
    wa
    #
    vx
    wex
    @1
    vy
    vx
    wel
    #
    vy
    vz
    wel
    vz
    vx
    wel
    wa
    vz
    wex
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    vx
    wex
    vx
    vy
    vz
    inf1.1
    inf1
    @4
    @9
    vx
    @3
    @8
    @1
    @3
    @5
    vy
    cv
    #
    @2
    wcel
    #
    wi
    #
    vy
    wal
    @8
    vy
    @0
    @2
    dfss2
    @12
    @7
    vy
    @11
    @6
    @5
    vz
    @10
    @0
    eluni
    imbi2i
    albii
    bitri
    anbi2i
    exbii
    mpbir
end
