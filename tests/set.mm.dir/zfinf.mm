include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "ax-inf.mm"
include "weq.mm"
include "elequ1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "cbvalv.mm"
include "anbi2i.mm"
include "exbii.mm"
include "mpbi.mm"

theorem zfinf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- E. x ( y e. x /\ A. y ( y e. x -> E. z ( y e. z /\ z e. x ) ) )

  proof
    vy
    vx
    wel
    #
    vw
    vx
    wel
    #
    vw
    vz
    wel
    #
    vz
    vx
    wel
    #
    wa
    #
    vz
    wex
    #
    wi
    #
    vw
    wal
    #
    wa
    #
    vx
    wex
    @0
    @0
    vy
    vz
    wel
    #
    @3
    wa
    #
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
    vy
    vx
    vw
    vz
    ax-inf
    @8
    @14
    vx
    @7
    @13
    @0
    @6
    @12
    vw
    vy
    vw
    vy
    weq
    #
    @1
    @0
    @5
    @11
    vw
    vy
    vx
    elequ1
    @15
    @4
    @10
    vz
    @15
    @2
    @9
    @3
    vw
    vy
    vz
    elequ1
    anbi1d
    exbidv
    imbi12d
    cbvalv
    anbi2i
    exbii
    mpbi
end
