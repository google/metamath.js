include "c0.mm"
include "wel.mm"
include "wn.mm"
include "wal.mm"
include "cio.mm"
include "0ss.mm"
include "cab.mm"
include "cuni.mm"
include "iotassuni.mm"
include "cv.mm"
include "wceq.mm"
include "csn.mm"
include "eq0.mm"
include "bicomi.mm"
include "abbii.mm"
include "unieqi.mm"
include "df-sn.mm"
include "eqcomi.mm"
include "0ex.mm"
include "unisn.mm"
include "3eqtri.mm"
include "sseqtri.mm"
include "eqssi.mm"

theorem bj-nuliotaALT
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- (/) = ( iota x A. y -. y e. x )

  proof
    c0
    vy
    vx
    wel
    wn
    vy
    wal
    #
    vx
    cio
    #
    @1
    0ss
    @1
    @0
    vx
    cab
    #
    cuni
    #
    c0
    @0
    vx
    iotassuni
    @3
    vx
    cv
    #
    c0
    wceq
    #
    vx
    cab
    #
    cuni
    c0
    csn
    #
    cuni
    c0
    @2
    @6
    @0
    @5
    vx
    @5
    @0
    vy
    @4
    eq0
    bicomi
    abbii
    unieqi
    @6
    @7
    @7
    @6
    vx
    c0
    df-sn
    eqcomi
    unieqi
    c0
    0ex
    unisn
    3eqtri
    sseqtri
    eqssi
end
