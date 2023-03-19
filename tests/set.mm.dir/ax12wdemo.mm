include "wel.mm"
include "wal.mm"
include "w3a.mm"
include "weq.mm"
include "elequ1.mm"
include "wb.mm"
include "elequ2.mm"
include "cbvalvw.mm"
include "a1i.mm"
include "albidv.mm"
include "syl5bb.mm"
include "3anbi123d.mm"
include "3anbi13d.mm"
include "ax12w.mm"

theorem ax12wdemo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint v x
  disjoint w y
  disjoint v y
  disjoint w z
  disjoint v z
  disjoint v w
  assert |- ( x = y -> ( A. y ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) -> A. x ( x = y -> ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ) ) )

  proof
    vx
    vy
    wel
    #
    vz
    vx
    wel
    #
    vx
    wal
    #
    vy
    vx
    wel
    #
    vz
    wal
    #
    vy
    wal
    #
    w3a
    vy
    vy
    wel
    #
    vz
    vw
    wel
    #
    vw
    wal
    #
    vv
    vy
    wel
    #
    vz
    wal
    #
    vv
    wal
    #
    w3a
    vx
    vv
    wel
    #
    @2
    vv
    vx
    wel
    #
    vz
    wal
    #
    vv
    wal
    #
    w3a
    vx
    vy
    vv
    vx
    vy
    weq
    #
    @0
    @6
    @2
    @8
    @5
    @11
    vx
    vy
    vy
    elequ1
    @2
    @8
    wb
    @16
    @1
    @7
    vx
    vw
    vx
    vw
    vz
    elequ2
    cbvalvw
    a1i
    @5
    @15
    @16
    @11
    @4
    @14
    vy
    vv
    vy
    vv
    weq
    #
    @3
    @13
    vz
    vy
    vv
    vx
    elequ1
    albidv
    cbvalvw
    #
    @16
    @14
    @10
    vv
    @16
    @13
    @9
    vz
    vx
    vy
    vv
    elequ2
    albidv
    albidv
    syl5bb
    3anbi123d
    @17
    @0
    @12
    @5
    @15
    @2
    vy
    vv
    vx
    elequ2
    @5
    @15
    wb
    @17
    @18
    a1i
    3anbi13d
    ax12w
end
