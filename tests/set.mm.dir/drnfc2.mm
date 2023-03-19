include "weq.mm"
include "wal.mm"
include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "wnfc.mm"
include "eleq2d.mm"
include "drnf2.mm"
include "dral2.mm"
include "df-nfc.mm"
include "3bitr4g.mm"

theorem drnfc2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  assume drnfc1.1: |- ( A. x x = y -> A = B )


  assert |- ( A. x x = y -> ( F/_ z A <-> F/_ z B ) )

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
    vz
    wnf
    #
    vw
    wal
    @1
    cB
    wcel
    #
    vz
    wnf
    #
    vw
    wal
    vz
    cA
    wnfc
    vz
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
    vz
    @0
    cA
    cB
    @1
    drnfc1.1
    eleq2d
    drnf2
    dral2
    vz
    vw
    cA
    df-nfc
    vz
    vw
    cB
    df-nfc
    3bitr4g
end
