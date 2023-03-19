include "weq.mm"
include "wal.mm"
include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "wnfc.mm"
include "eleq2d.mm"
include "drnf1.mm"
include "dral2.mm"
include "df-nfc.mm"
include "3bitr4g.mm"

theorem drnfc1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  assume drnfc1.1: |- ( A. x x = y -> A = B )


  assert |- ( A. x x = y -> ( F/_ x A <-> F/_ y B ) )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    vw
    cv
    #
    cA
    wcel
    #
    vx
    wnf
    #
    vw
    wal
    @1
    cB
    wcel
    #
    vy
    wnf
    #
    vw
    wal
    vx
    cA
    wnfc
    vy
    cB
    wnfc
    @3
    @5
    vx
    vy
    vw
    @2
    @4
    vx
    vy
    @0
    cA
    cB
    @1
    drnfc1.1
    eleq2d
    drnf1
    dral2
    vx
    vw
    cA
    df-nfc
    vy
    vw
    cB
    df-nfc
    3bitr4g
end
